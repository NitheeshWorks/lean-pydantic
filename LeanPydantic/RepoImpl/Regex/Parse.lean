import Keel.Parse
import Keel.DataTypes.Refine
import LeanPydantic.RepoImpl.Regex.Match

/-!
# RepoImpl: compiling a pattern

`Regex.compile` reads a pattern in Rust `regex` syntax, the syntax pydantic's
default engine accepts, with Keel's parser combinators. It follows Rust's
parser (`regex-syntax`) step by step, so that it accepts the same patterns and
gives them the same meaning. Groups, flag directives and nested classes
recurse at most `maxDepth` deep (Rust's own nesting limit, 250), so the
parser's depth is bounded whatever the pattern.

Supported: literals and escapes (`\n`, `\t`, `\x41`, `\x{..}`, `\u{..}`,
`\U0001F600`, any escaped ASCII punctuation), `.`, classes with ranges,
negation, nesting, the POSIX classes `[[:alpha:]]` (and their negations
`[[:^alpha:]]`) and the operators `&&`, `--` and `~~`, the Unicode shorthands
`\d \w \s` and their negations, the assertions `^ $ \A \z \b \B \< \>
\b{start} \b{end}`, groups `( )`, `(?: )`, `(?P<name> )` and `(?<name> )`,
alternation, the repetitions `* + ? {n} {n,} {n,m}` (greedy or lazy, which a
yes/no match cannot tell apart), and the inline flags `i m s x R u U`, set
for the rest of the group by `(?flags)` or for a group by `(?flags: )`, with
`-` clearing: `i` folds case by Rust's simple case folding, `s` lets `.`
match `\n`, `x` ignores white space and `#` comments, `R` keeps `.` off `\r`,
`-u` makes the classes ASCII (refusing, as Rust does, anything that could
match a byte above 0x7F), and `U` only changes which match is reported.
What Rust rejects is rejected with an error. Three things Rust accepts are
also rejected, because Keel's assertions cannot express them yet: `^` and `$`
under `(?m)`, the word assertions under `(?-u)`, and `\b{start-half}` and
`\b{end-half}`; so is `\p{..}`.
-/

namespace LeanPydantic.Regex

/-- A parsed pattern, before repetitions are expanded. -/
inductive Ast where
  | eps
  | cls (k : Cls)
  | assert (a : Assertion)
  | alt (a b : Ast)
  | cat (a b : Ast)
  | group (name : Option String) (a : Ast)
  | rep (a : Ast) (lo : Nat) (hi : Option Nat)
  deriving Inhabited, Repr

namespace Ast

/-- A sequence of items. -/
def ofSeq : List Ast → Ast
  | [] => .eps
  | x :: xs => xs.foldl .cat x

/-- Alternatives, each a sequence of items. -/
def ofAlts : List (List Ast) → Ast
  | [] => .eps
  | s :: ss => ss.foldl (fun a s => .alt a (ofSeq s)) (ofSeq s)

end Ast

/-- The inline flags in force. -/
structure Flags where
  /-- `i`: case-insensitive, by Rust's simple case folding. -/
  caseless : Bool := false
  /-- `m`: `^` and `$` also at line ends. -/
  multiLine : Bool := false
  /-- `s`: `.` also matches `\n`. -/
  dotAll : Bool := false
  /-- `x`: white space and `#` comments between tokens are ignored. -/
  verbose : Bool := false
  /-- `R`: lines end at `\r` as well as `\n`. -/
  crlf : Bool := false
  /-- `u` (on by default): Unicode classes; off, ASCII ones. -/
  unicode : Bool := true
  deriving Inhabited

namespace Flags

/-- Apply a flag string (`i`, `is-x`, ...) as Rust does: each flag at most
once, at most one `-`, and not last. `U` swaps greed, which a yes/no match
cannot see. -/
def set (fl : Flags) (cs : List Char) : Except String Flags :=
  go fl cs [] false false
where
  /-- `seen`: the flags so far; `neg`: after the `-`; `dangling`: the last was `-`. -/
  go (fl : Flags) : List Char → List Char → Bool → Bool → Except String Flags
    | [], _, _, dangling => if dangling then .error "dangling flag negation operator" else .ok fl
    | '-' :: cs, seen, neg, _ =>
      if neg then .error "flag negation operator repeated" else go fl cs seen true true
    | c :: cs, seen, neg, _ =>
      if c ∈ seen then .error "duplicate flag" else
      let v := !neg
      match c with
      | 'i' => go { fl with caseless := v } cs (c :: seen) neg false
      | 'm' => go { fl with multiLine := v } cs (c :: seen) neg false
      | 's' => go { fl with dotAll := v } cs (c :: seen) neg false
      | 'x' => go { fl with verbose := v } cs (c :: seen) neg false
      | 'R' => go { fl with crlf := v } cs (c :: seen) neg false
      | 'u' => go { fl with unicode := v } cs (c :: seen) neg false
      | 'U' => go fl cs (c :: seen) neg false
      | _ => .error "unrecognized flag"

end Flags

namespace Parse

open Keel Parser

/-- Parsers of pattern characters, failing with a message. -/
abbrev P := Keel.Parser Char String

/-- The nesting bound for groups, flag directives and classes (Rust's
default). -/
def maxDepth : Nat := 250

/-! ## White space under `(?x)` -/

/-- One white space character (Rust's `char::is_whitespace`, the `\s` table)
or a `#` comment up to and including the end of its line. -/
def spaceOrComment : P Unit := do
  let c ← satisfy fun c => isSpace c || c == '#'
  if c = '#' then
    let _ ← many (satisfy (· != '\n'))
    let _ ← optional (token '\n')
    pure ()
  else pure ()

/-- Under `(?x)`, skip white space and comments (Rust's `bump_space`). -/
def skipSpace (fl : Flags) : P Unit :=
  if fl.verbose then do let _ ← many spaceOrComment; pure () else pure ()

/-- The character after the next one, skipping white space under `(?x)`,
without consuming anything (Rust's `peek_space`). -/
def peekSpace (fl : Flags) : P (Option Char) := lookahead do
  let _ ← next?
  skipSpace fl
  peek?

/-- The next two characters, without consuming them. -/
def peek2 : P (Option Char × Option Char) := lookahead do
  let a ← next?
  let b ← next?
  pure (a, b)

/-! ## Escapes -/

/-- What an escape stands for. -/
inductive Esc where
  /-- A character; `byte` when written `\xNN`, which under `(?-u)` is a byte. -/
  | char (c : Char) (byte : Bool)
  /-- A Perl class: `d`, `D`, `w`, `W`, `s` or `S`. -/
  | perl (k : Char)
  | assert (a : Assertion)

def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexNumber (ds : List Char) : Nat := ds.foldl (fun n d => 16 * n + hexValue d) 0

def decNumber (ds : List Char) : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

/-- The scalar value `n` as a character. -/
def scalar (n : Nat) : P Char :=
  if h : n.isValidChar then pure (Char.ofNatAux n h) else fail "invalid Unicode scalar value"

/-- `n` hex digits, white space between them skipped under `(?x)`. -/
def hexDigits (fl : Flags) : Nat → P (List Char)
  | 0 => pure []
  | 1 => do
    let d ← satisfy isHex |>.withError "invalid hexadecimal escape"
    pure [d]
  | n + 2 => do
    let d ← satisfy isHex |>.withError "invalid hexadecimal escape"
    skipSpace fl
    let ds ← hexDigits fl (n + 1)
    pure (d :: ds)

/-- The digits of `\x`, `\u` or `\U`: `{` hex digits `}` (a 32-bit value), or
exactly `width` hex digits. Also whether it is the two-digit `\xNN`. -/
def hexEscape (fl : Flags) (width : Nat) : P (Char × Bool) := do
  skipSpace fl
  if (← peek?) = some '{' then
    let _ ← next
    skipSpace fl
    let ds ← many (do let d ← satisfy isHex; skipSpace fl; pure d)
    let _ ← token '}' |>.withError "invalid or unclosed hexadecimal escape"
    if ds.isEmpty then fail "empty hexadecimal escape"
    else if hexNumber ds ≥ 2 ^ 32 then fail "invalid hexadecimal escape"
    else do let c ← scalar (hexNumber ds); pure (c, false)
  else
    let ds ← hexDigits fl width
    let c ← scalar (hexNumber ds)
    pure (c, width == 2)

def isBoundaryNameChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '-'

/-- `\b`, or `\b{start}` and the other special word boundaries. A `{` not
followed by a letter or `-` starts a repetition of `\b` instead. -/
def wordBoundary (fl : Flags) : P Esc := do
  if (← peek?) ≠ some '{' then return .assert .wordBoundary
  match ← lookahead (do let _ ← next; skipSpace fl; peek?) with
  | none => fail "unclosed special word boundary"
  | some c =>
    if !isBoundaryNameChar c then return .assert .wordBoundary
    let _ ← next
    skipSpace fl
    let name ← many (do let c ← satisfy isBoundaryNameChar; skipSpace fl; pure c)
    let _ ← token '}' |>.withError "unclosed special word boundary"
    match String.ofList name with
    | "start" => pure (.assert .wordStart)
    | "end" => pure (.assert .wordEnd)
    | "start-half" | "end-half" => fail "unsupported: \\b{start-half} and \\b{end-half}"
    | _ => fail "unrecognized special word boundary"

/-- The escape after a backslash. -/
def escape (fl : Flags) : P Esc := do
  let e ← next |>.withError "incomplete escape sequence"
  match e with
  | 'n' => pure (.char '\n' false)
  | 't' => pure (.char '\t' false)
  | 'r' => pure (.char '\r' false)
  | 'f' => pure (.char '\x0c' false)
  | 'v' => pure (.char '\x0b' false)
  | 'a' => pure (.char '\x07' false)
  | 'x' => do let (c, b) ← hexEscape fl 2; pure (.char c b)
  | 'u' => do let (c, _) ← hexEscape fl 4; pure (.char c false)
  | 'U' => do let (c, _) ← hexEscape fl 8; pure (.char c false)
  | 'd' | 'D' | 'w' | 'W' | 's' | 'S' => pure (.perl e)
  | 'p' | 'P' => fail "unsupported: Unicode classes \\p{..}"
  | 'A' => pure (.assert .start)
  | 'z' => pure (.assert .finish)
  | 'B' => pure (.assert .notWordBoundary)
  | '<' => pure (.assert .wordStart)
  | '>' => pure (.assert .wordEnd)
  | 'b' => wordBoundary fl
  | c =>
    if c.toNat < 128 && !c.isAlphanum then pure (.char c false)
    else fail s!"unsupported escape sequence \\{c}"

/-! ## Classes -/

def emptyCls : Cls := .diff (.atom .any) (.atom .any)

/-- The union of some classes (the empty class for none). -/
def unionOf : List Cls → Cls
  | [] => emptyCls
  | k :: ks => ks.foldl .union k

/-- The union of some ranges. -/
def ofRanges (rs : List (Char × Char)) : Cls := unionOf (rs.map fun (a, b) => .atom (.range a b))

/-- The ASCII class `[:name:]`, as ranges. -/
def posix : String → Option (List (Char × Char))
  | "alnum" => some [('0', '9'), ('A', 'Z'), ('a', 'z')]
  | "alpha" => some [('A', 'Z'), ('a', 'z')]
  | "ascii" => some [('\x00', '\x7f')]
  | "blank" => some [('\t', '\t'), (' ', ' ')]
  | "cntrl" => some [('\x00', '\x1f'), ('\x7f', '\x7f')]
  | "digit" => some [('0', '9')]
  | "graph" => some [('!', '~')]
  | "lower" => some [('a', 'z')]
  | "print" => some [(' ', '~')]
  | "punct" => some [('!', '/'), (':', '@'), ('[', '`'), ('{', '~')]
  | "space" => some [('\t', '\r'), (' ', ' ')]
  | "upper" => some [('A', 'Z')]
  | "word" => some [('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')]
  | "xdigit" => some [('0', '9'), ('A', 'F'), ('a', 'f')]
  | _ => none

/-- `(?i)` on a class: the characters with a simple case variant in it.
Folding commutes with every class operation here, because a folded class
holds whole orbits; `\d \w \s` and `.` hold whole orbits already (checked by
`scripts/regex/unicode_tables.py`), so they are left as they are, as Rust
leaves them. -/
def foldCase : Cls → Cls
  | .atom (.char c) => if (caseVariants c).isEmpty then .atom (.char c) else .atom (.caseless c c)
  | .atom (.range lo hi) => .atom (.caseless lo hi)
  | .atom a => .atom a
  | .union k l => .union (foldCase k) (foldCase l)
  | .inter k l => .inter (foldCase k) (foldCase l)
  | .diff k l => .diff (foldCase k) (foldCase l)
  | .sym k l => .sym (foldCase k) (foldCase l)
  | .neg k => .neg (foldCase k)

/-- The other ASCII case of an ASCII letter. -/
def swapCase (c : Char) : Char := if c.isUpper then c.toLower else c.toUpper

/-- A class under `(?-u)`, which Rust builds over bytes: the bytes of `k`
(whose literals are ASCII), folded on ASCII letters under `(?i)`, negated
within the bytes if `neg`. A set with a byte above 0x7F could match invalid
UTF-8 and is refused, as Rust refuses it; otherwise it is ASCII and is
returned as its characters. -/
def byteClass (fl : Flags) (neg : Bool) (k : Cls) : P Cls :=
  let has (b : Nat) := Cls.test k (Char.ofNat b)
  let mem (b : Nat) :=
    let x := has b || (fl.caseless && b < 128 && (Char.ofNat b).isAlpha && has (swapCase (Char.ofNat b)).toNat)
    if neg then !x else x
  if (List.range' 128 128).any mem then fail "pattern can match invalid UTF-8"
  else pure (unionOf (((List.range 128).filter mem).map fun b => .atom (.char (Char.ofNat b))))

/-- A Perl class: Unicode, or ASCII under `(?-u)`, where a negated one is
refused (it holds bytes above 0x7F). -/
def perl (fl : Flags) (k : Char) : P Cls :=
  let (a, rs, neg) : Atom × List (Char × Char) × Bool := match k with
    | 'd' => (.digit, [('0', '9')], false)
    | 'D' => (.digit, [('0', '9')], true)
    | 'w' => (.word, [('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')], false)
    | 'W' => (.word, [('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')], true)
    | 's' => (.space, [('\t', '\r'), (' ', ' ')], false)
    | _ => (.space, [('\t', '\r'), (' ', ' ')], true)
  if fl.unicode then pure (if neg then .neg (.atom a) else .atom a)
  else if neg then fail "pattern can match invalid UTF-8"
  else pure (ofRanges rs)

/-- A class closed by its `]`: folded under `(?i)`, then negated if `neg`;
under `(?-u)` a set of ASCII bytes. -/
def finish (fl : Flags) (neg : Bool) (k : Cls) : P Cls :=
  if fl.unicode then
    let k := if fl.caseless then foldCase k else k
    pure (if neg then .neg k else k)
  else byteClass fl neg k

/-- A literal in a class: under `(?-u)` it must be ASCII (a byte above 0x7F,
`\xNN`, could match invalid UTF-8, and any other character is Unicode). -/
def classLit (fl : Flags) (c : Char) : P Char :=
  if !fl.unicode && c.toNat > 0x7f then fail "Unicode not allowed here" else pure c

/-- A class item's first part: a character, or a Perl class. -/
inductive Prim where
  | lit (c : Char)
  | cls (k : Cls)

/-- A character, an escape or a Perl class inside a class. -/
def classPrim (fl : Flags) : P Prim := do
  match ← next? with
  | some '\\' =>
    match ← escape fl with
    | .char c _ => .lit <$> classLit fl c
    | .perl k => .cls <$> perl fl k
    | .assert _ => fail "assertions are not allowed in a class"
  | some c => .lit <$> classLit fl c
  | none => fail "unclosed character class"

/-- A character, a Perl class, or a range `c-d`. A `-` before `]` or `-` is
not a range. -/
def rangeItem (fl : Flags) : P Cls := do
  let p ← classPrim fl
  skipSpace fl
  let c ← peek?
  if c.isNone then fail "unclosed character class"
  let after ← peekSpace fl
  if c ≠ some '-' || after = some ']' || after = some '-' then
    match p with
    | .lit c => pure (.atom (.char c))
    | .cls k => pure k
  else
    let _ ← next
    skipSpace fl
    let q ← classPrim fl
    match p, q with
    | .lit lo, .lit hi =>
      if hi < lo then fail "invalid range: its end is below its start" else pure (.atom (.range lo hi))
    | _, _ => fail "invalid range boundary: a class cannot be one"

/-- `[:name:]` or `[:^name:]` after its `[`; fails consuming nothing if what
follows is not one (it is then a nested class). -/
def asciiClass (fl : Flags) : P Cls := do
  let (neg, rs) ← attempt do
    let _ ← token ':'
    let neg ← optional (token '^')
    let name ← many (satisfy (· != ':'))
    let _ ← token ':'
    let _ ← token ']'
    match posix (String.ofList name) with
    | some rs => pure (neg.isSome, rs)
    | none => fail "not an ASCII class"
  if fl.unicode then pure (if neg then .neg (ofRanges rs) else ofRanges rs)
  else if neg then fail "pattern can match invalid UTF-8"
  else pure (ofRanges rs)

/-- One item of a union, white space after it skipped; fails without
consuming at the union's end (`]` or an operator) or at the end of input.
`nested` parses a class after its `[`. -/
def classItem (fl : Flags) (nested : P Cls) : P Cls := do
  match ← peek2 with
  | (none, _) | (some ']', _) | (some '&', some '&') | (some '-', some '-') | (some '~', some '~') =>
    fail "end of union"
  | (some '[', _) =>
    let _ ← next
    let k ← asciiClass fl <|> nested
    skipSpace fl
    pure k
  | _ =>
    let k ← rangeItem fl
    skipSpace fl
    pure k

/-- A set operator, if one is next. -/
def classOp : P (Option (Cls → Cls → Cls)) := do
  match ← peek2 with
  | (some '&', some '&') => let _ ← take 2; pure (some .inter)
  | (some '-', some '-') => let _ ← take 2; pure (some .diff)
  | (some '~', some '~') => let _ ← take 2; pure (some .sym)
  | _ => pure none

/-- The operators of a class, left to right, until its `]`. An operand may
be empty. -/
def classOps (fl : Flags) (nested : P Cls) (acc : Cls) : Nat → P Cls
  | 0 => fail "character class too long"
  | fuel + 1 => do
    match ← classOp with
    | some op => do
      skipSpace fl
      let ks ← many (classItem fl nested)
      classOps fl nested (op acc (unionOf ks)) fuel
    | none => do
      let _ ← token ']' |>.withError "unclosed character class"
      pure acc

/-- A class after its `[`; `nested` parses an inner one. Any `-` first are
literal, and so is a `]` first after none. -/
def classBody (fl : Flags) (nested : P Cls) : P Cls := do
  skipSpace fl
  let neg ← if (← peek?) = some '^' then do let _ ← next; skipSpace fl; pure true else pure false
  let dashes ← many (do let _ ← token '-'; skipSpace fl; pure (Keel.Regex.Cls.atom (.char '-')))
  let bracket ← if dashes.isEmpty && (← peek?) = some ']' then do
      let _ ← next
      skipSpace fl
      pure [Keel.Regex.Cls.atom (.char ']')]
    else pure []
  let ks ← many (classItem fl nested)
  let k ← classOps fl nested (unionOf (dashes ++ bracket ++ ks)) 4096
  finish fl neg k

/-- A class after its `[`, nested at most `maxDepth` deep. -/
def charClass (fl : Flags) : P Cls := fixDepth maxDepth (classBody fl)

/-! ## Groups and sequences -/

def isNameChar (c : Char) : Bool := c.isAlphanum || c = '_' || c = '.' || c = '[' || c = ']'

/-- A group name and its closing `>`. -/
def groupName : P String := do
  let cs ← many (satisfy isNameChar)
  let _ ← token '>' |>.withError "invalid capture group name"
  match cs with
  | c :: _ => if c.isAlpha || c = '_' then pure (String.ofList cs) else fail "invalid capture group name"
  | [] => fail "empty capture group name"

def isFlagChar (c : Char) : Bool := "imsxRuU-".contains c

/-- A flag directive `(?flags)` next: the flags in force after it, consumed.
Otherwise `none`, consuming nothing. -/
def directive (fl : Flags) : P (Option Flags) :=
  (some <$> attempt do
    let _ ← token '('
    skipSpace fl
    let _ ← token '?'
    let cs ← many (satisfy isFlagChar)
    let _ ← token ')'
    match fl.set cs with
    | .ok fl' => if cs.isEmpty then fail "empty flags" else pure fl'
    | .error e => fail e) <|> pure none

/-- What opens a group after its `(` (and any white space under `(?x)`): its
name, and the flags of its body. -/
def groupOpen (fl : Flags) : P (Option String × Flags) := do
  if ← startsWith ['?', 'P', '<'] then
    let _ ← take 3
    let n ← groupName
    pure (some n, fl)
  else if ← startsWith ['?', '<'] then
    let _ ← take 2
    let n ← groupName
    pure (some n, fl)
  else if (← peek?) = some '?' then
    let _ ← next
    let cs ← many (satisfy fun c => c != ':' && c != ')')
    match ← next?, fl.set cs with
    | some ':', .ok fl' => pure (none, fl')
    | _, .error e => fail e
    | some ')', .ok _ => fail "repetition operator missing expression"
    | _, .ok _ => fail "unclosed group"
  else pure (none, fl)

/-- A group after its `(`; `sub` parses a body under the given flags. -/
def group (fl : Flags) (sub : Flags → P (List (List Ast))) : P Ast := do
  skipSpace fl
  if (← startsWith ['?', '=']) || (← startsWith ['?', '!']) || (← startsWith ['?', '<', '='])
      || (← startsWith ['?', '<', '!']) then
    fail "look-around is not supported"
  let (name, fl') ← groupOpen fl
  let body ← sub fl'
  let _ ← token ')' |>.withError "unclosed group"
  pure (.group name (Ast.ofAlts body))

/-- `.`: without `\n` (and `\r` under `(?R)`), or anything under `(?s)`;
refused under `(?-u)`, where it could match a byte above 0x7F. -/
def dot (fl : Flags) : P Cls :=
  if !fl.unicode then fail "pattern can match invalid UTF-8"
  else pure (.atom (if fl.dotAll then .any else if fl.crlf then .dotCRLF else .dot))

/-- A literal: under `(?i)` its case variants too (ASCII ones only under
`(?-u)`, where a `\xNN` above 0x7F is a byte and refused). -/
def literal (fl : Flags) (c : Char) (byte : Bool) : P Ast :=
  if !fl.unicode && byte && c.toNat > 0x7f then fail "pattern can match invalid UTF-8"
  else if !fl.caseless then pure (.cls (.atom (.char c)))
  else if fl.unicode then pure (.cls (foldCase (.atom (.char c))))
  else if c.toNat < 128 && c.isAlpha then pure (.cls (.union (.atom (.char c)) (.atom (.char (swapCase c)))))
  else pure (.cls (.atom (.char c)))

/-- `^` or `$`. Under `(?m)` they would also hold at line ends, which Keel's
assertions cannot say yet. -/
def anchor (fl : Flags) (a : Assertion) : P Ast :=
  if fl.multiLine then fail "unsupported: ^ and $ under (?m)" else pure (.assert a)

/-- An escaped assertion. Under `(?-u)` the word assertions would use ASCII
word characters, which Keel's assertions cannot say yet. -/
def assertion (fl : Flags) (a : Assertion) : P Ast :=
  match a with
  | .start | .finish => pure (.assert a)
  | _ => if fl.unicode then pure (.assert a) else fail "unsupported: word assertions under (?-u)"

/-- One element of a sequence, before any repetition, white space after it
skipped. Fails without consuming at `|`, `)`, a flag directive and the end. -/
def atom (fl : Flags) (sub : Flags → P (List (List Ast))) : P Ast := do
  let a ← match ← peek? with
    | none | some '|' | some ')' => fail "end of sequence"
    | some '*' | some '+' | some '?' | some '{' => failAhead "repetition operator missing expression"
    | some '(' =>
      if (← lookahead (directive fl)).isSome then fail "a flag directive"
      else do let _ ← next; group fl sub
    | some c => do
      let _ ← next
      match c with
      | '[' => .cls <$> charClass fl
      | '.' => .cls <$> dot fl
      | '^' => anchor fl .start
      | '$' => anchor fl .finish
      | '\\' =>
        match ← escape fl with
        | .char d byte => literal fl d byte
        | .perl k => .cls <$> perl fl k
        | .assert a => assertion fl a
      | _ => literal fl c false
  skipSpace fl
  pure a

/-- A count in `{..}`: white space around it skipped (any, as Rust does),
and between its digits under `(?x)`; `none` if it has no digits. -/
def count (fl : Flags) : P (Option Nat) := do
  let _ ← many (satisfy isSpace)
  let ds ← many (do let d ← satisfy Char.isDigit; skipSpace fl; pure d)
  let _ ← many (do let _ ← satisfy isSpace; skipSpace fl; pure ())
  if ds.isEmpty then pure none
  else
    let n := decNumber ds
    if n ≥ 2 ^ 32 then fail "repetition count too large" else pure (some n)

/-- `{n}`, `{n,}` or `{n,m}` after its `{`: its bounds. -/
def counted (fl : Flags) : P (Nat × Option Nat) := do
  skipSpace fl
  let lo ← count fl
  let q ← if (← peek?) = some ',' then do
      let _ ← next
      skipSpace fl
      if (← peek?) = some '}' then
        match lo with
        | some n => pure (n, none)
        | none => fail "invalid repetition count"
      else
        match lo, ← count fl with
        | some n, some m => pure (n, some m)
        | _, _ => fail "invalid repetition count"
    else
      match lo with
      | some n => pure (n, some n)
      | none => fail "invalid repetition count"
  let _ ← token '}' |>.withError "unclosed counted repetition"
  match q with
  | (lo, some hi) => if hi < lo then fail "invalid repetition range" else pure q
  | _ => pure q

/-- One repetition operator, greedy or lazy: its bounds, white space after
it skipped. Fails without consuming when none is next. -/
def quantifier (fl : Flags) : P (Nat × Option Nat) := do
  let q ← match ← peek? with
    | some '*' => do let _ ← next; let _ ← optional (token '?'); pure (0, none)
    | some '+' => do let _ ← next; let _ ← optional (token '?'); pure (1, none)
    | some '?' => do let _ ← next; let _ ← optional (token '?'); pure (0, some 1)
    | some '{' => do
      let _ ← next
      let q ← counted fl
      skipSpace fl
      let _ ← optional (token '?')
      pure q
    | _ => fail "no repetition"
  skipSpace fl
  pure q

/-- An atom and its repetitions. -/
def repeated (fl : Flags) (sub : Flags → P (List (List Ast))) : P Ast := do
  let a ← atom fl sub
  let qs ← many (quantifier fl)
  pure (qs.foldl (fun a (lo, hi) => .rep a lo hi) a)

/-- A sequence of items, possibly empty. -/
def sequence (fl : Flags) (sub : Flags → P (List (List Ast))) : P (List Ast) := do
  skipSpace fl
  many (repeated fl sub)

/-- Join what follows a flag directive to the alternatives before it: its
first alternative continues the last one. -/
def joinRest : List (List Ast) → List (List Ast) → List (List Ast)
  | [a], r :: rs => (a ++ r) :: rs
  | a :: as, rs => a :: joinRest as rs
  | [], rs => rs

/-- The alternatives of a group's body (or the pattern), up to its `)` or the
end, as sequences of items. A flag directive `(?flags)` sets flags for the
rest of the body, which is parsed under them; groups and directives recurse
at most `d` deep. -/
def alts (fl : Flags) : Nat → P (List (List Ast))
  | 0 => failAhead "nest limit exceeded"
  | d + 1 => do
    let first ← sequence fl (alts · d)
    let more ← many (do let _ ← token '|'; sequence fl (alts · d))
    match ← directive fl with
    | none => pure (first :: more)
    | some fl' => do
      let rest ← alts fl' d
      pure (joinRest (first :: more) rest)

/-- A pattern, nested at most `maxDepth` deep. -/
def pattern : P Ast := Ast.ofAlts <$> alts {} maxDepth

end Parse

namespace Ast

/-- The character classes `a` expands to. -/
def leaves : Ast → Nat
  | eps | assert _ => 0
  | cls _ => 1
  | alt a b | cat a b => a.leaves + b.leaves
  | group _ a => a.leaves
  | rep a lo hi => a.leaves * (hi.getD (lo + 1))

/-- The capture group names, in order. -/
def names : Ast → List String
  | eps | assert _ | cls _ => []
  | alt a b | cat a b => a.names ++ b.names
  | group n a => n.toList ++ a.names
  | rep a _ _ => a.names

/-- `r` `n` times. -/
def power (r : Regex) : Nat → Regex
  | 0 => .eps
  | 1 => r
  | n + 1 => .cat r (power r n)

/-- `r` at most `n` times. -/
def upto (r : Regex) : Nat → Regex
  | 0 => .eps
  | n + 1 => .alt (.cat r (upto r n)) .eps

/-- The regular expression, repetitions expanded. -/
def lower : Ast → Regex
  | eps => .eps
  | cls k => .cls k
  | assert a => .assert a
  | alt a b => .alt a.lower b.lower
  | cat a b => .cat a.lower b.lower
  | group _ a => a.lower
  | rep a lo none => .cat (power a.lower lo) (.star a.lower)
  | rep a lo (some hi) => .cat (power a.lower lo) (upto a.lower (hi - lo))

end Ast

/-- The most character classes a pattern may expand to. Each is at most one
term of the matcher's state, so this bounds the work per input character. -/
def maxLeaves : Nat := 10000

/-- The first name that occurs twice, if any. -/
def duplicate? : List String → Option String
  | [] => none
  | n :: ns => if n ∈ ns then some n else duplicate? ns

/-- Compile a pattern in Rust `regex` syntax, or say why it is invalid. -/
def compile (src : String) : Except String Regex :=
  let cs := src.toList
  let at_ (rest : List Char) := s!" at position {cs.length - rest.length}"
  match Parse.pattern.parse cs with
  | .error e rest => .error (e ++ at_ rest)
  | .ok ast rest =>
    if !rest.isEmpty then .error ("unopened group" ++ at_ rest)
    else match duplicate? ast.names with
      | some n => .error s!"duplicate capture group name {n}"
      | none =>
        if ast.leaves > maxLeaves then .error s!"pattern too large (over {maxLeaves} classes once repetitions are expanded)"
        else .ok ast.lower

/-- A Keel pattern from its source: the source, and the compiled matcher.
`pattern "…"` in a refinement checks at elaboration time that the source
compiles, so the fallback is never taken there. The pattern is compiled
(`Keel.Regex.compile`: numbered terms and tables) once, when the pattern
value is made, not per test. -/
def ofSource (src : String) : Keel.Pattern :=
  match compile src with
  | .ok r => ⟨src, (Keel.Regex.compile r .search).test⟩
  | .error _ => ⟨src, fun _ => false⟩

end LeanPydantic.Regex
