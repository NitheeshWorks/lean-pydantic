import Keel
import LeanPydantic.RepoImpl.Regex.Nfa

/-!
# RepoImpl: compiling a pattern

`Regex.compile` reads a pattern in Rust `regex` syntax, the syntax pydantic's
default engine accepts, with Keel's parser combinators. Groups and nested
character classes recurse through `Keel.Parser.fixDepth`, so the parser's
depth is bounded (by Rust's own nesting limit, 250) whatever the pattern.

Supported: literals and escapes (`\n`, `\t`, `\x41`, `\x{..}`, `A`,
`\u{..}`, `\U0001F600`, any escaped ASCII punctuation), `.`, classes with
ranges, negation, nesting and the operators `&&`, `--` and `~~`, the Unicode
shorthands `\d \w \s` and their negations, the assertions `^ $ \A \z \b \B
\< \>`, groups `( )`, `(?: )`, `(?P<name> )` and `(?<name> )`, alternation,
and the repetitions `* + ? {n} {n,} {n,m}` (greedy or lazy, which a yes/no
match cannot tell apart). A pattern outside this, such as inline flags,
`\p{..}` or a POSIX class, is rejected with an error, as one Rust rejects is.
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

namespace Parse

open Keel Parser

/-- Parsers of pattern characters, failing with a message. -/
abbrev P := Keel.Parser Char String

/-- The nesting bound for groups and classes (Rust's default). -/
def maxDepth : Nat := 250

/-- What an escape stands for. -/
inductive Esc where
  | char (c : Char)
  | cls (k : Cls)
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

/-- The digits of `\x`, `\u` or `\U`: `{` up to eight hex digits `}`, or
exactly `width` hex digits. -/
def hexEscape (width : Nat) : P Char := do
  if (← peek?) = some '{' then
    let _ ← next
    let ds ← many (satisfy isHex)
    let _ ← token '}' |>.withError "unclosed hexadecimal escape"
    if ds.isEmpty || ds.length > 8 then fail "invalid hexadecimal escape" else scalar (hexNumber ds)
  else
    let ds ← take width |>.withError "incomplete hexadecimal escape"
    if ds.all isHex then scalar (hexNumber ds) else fail "invalid hexadecimal escape"

/-- The escape after a backslash. -/
def escape : P Esc := do
  let e ← next |>.withError "incomplete escape sequence"
  match e with
  | 'n' => pure (.char '\n')
  | 't' => pure (.char '\t')
  | 'r' => pure (.char '\r')
  | 'f' => pure (.char '\x0c')
  | 'v' => pure (.char '\x0b')
  | 'a' => pure (.char '\x07')
  | 'x' => .char <$> hexEscape 2
  | 'u' => .char <$> hexEscape 4
  | 'U' => .char <$> hexEscape 8
  | 'd' => pure (.cls (.atom .digit))
  | 'D' => pure (.cls (.neg (.atom .digit)))
  | 'w' => pure (.cls (.atom .word))
  | 'W' => pure (.cls (.neg (.atom .word)))
  | 's' => pure (.cls (.atom .space))
  | 'S' => pure (.cls (.neg (.atom .space)))
  | 'A' => pure (.assert .start)
  | 'z' => pure (.assert .finish)
  | 'B' => pure (.assert .notWordBoundary)
  | '<' => pure (.assert .wordStart)
  | '>' => pure (.assert .wordEnd)
  | 'b' =>
    if (← peek?) = some '{' then fail "unsupported: \\b{...}" else pure (.assert .wordBoundary)
  | c =>
    if c.toNat < 128 && !c.isAlphanum then pure (.char c)
    else fail s!"unsupported escape sequence \\{c}"

/-- The next two characters, without consuming them. -/
def peek2 : P (Option Char × Option Char) := lookahead do
  let a ← next?
  let b ← next?
  pure (a, b)

/-- A single character inside a class: a literal or an escape for one. -/
def classChar : P Char := do
  match ← next? with
  | some '\\' =>
    match ← escape with
    | .char c => pure c
    | _ => fail "a class or assertion cannot end a range"
  | some '[' => fail "a class cannot end a range"
  | some c => pure c
  | none => fail "unclosed character class"

/-- `c`, or the range `c-d` if a `-` and a character follow. -/
def rangeFrom (lo : Char) : P Cls := do
  match ← peek2 with
  | (some '-', some b) =>
    if b = ']' || b = '-' then pure (.atom (.char lo))
    else
      let _ ← next
      let hi ← classChar
      if hi < lo then fail "invalid range: its end is below its start" else pure (.atom (.range lo hi))
  | _ => pure (.atom (.char lo))

/-- One item of a class. `nested` parses a class after its `[`. -/
def classItem (nested : P Cls) : P Cls := do
  match ← peek? with
  | some '[' =>
    let _ ← next
    if (← peek?) = some ':' then fail "unsupported: POSIX character classes" else nested
  | some '\\' =>
    let _ ← next
    match ← escape with
    | .char c => rangeFrom c
    | .cls k =>
      match ← peek2 with
      | (some '-', some b) =>
        if b = ']' || b = '-' then pure k else fail "a class cannot start a range"
      | _ => pure k
    | .assert _ => fail "assertions are not allowed in a class"
  | some c => let _ ← next; rangeFrom c
  | none => fail "unclosed character class"

/-- A set operator, if one is next. -/
def classOp : P (Option (Cls → Cls → Cls)) := do
  match ← peek2 with
  | (some '&', some '&') => let _ ← take 2; pure (some .inter)
  | (some '-', some '-') => let _ ← take 2; pure (some .diff)
  | (some '~', some '~') => let _ ← take 2; pure (some .sym)
  | _ => pure none

/-- Items up to an operator or the closing `]`, as their union. A `]`
first is a literal. -/
def classUnion (nested : P Cls) (first : Bool) : P Cls := do
  let k ← if first && (← peek?) = some ']' then do let _ ← next; rangeFrom ']' else classItem nested
  let ks ← many (attempt do
    match ← peek2 with
    | (some ']', _) | (some '&', some '&') | (some '-', some '-') | (some '~', some '~') =>
      fail "end of union"
    | _ => classItem nested)
  pure (ks.foldl .union k)

/-- The operators of a class, left to right, until its `]`. -/
def classOps (nested : P Cls) (acc : Cls) : Nat → P Cls
  | 0 => fail "character class too long"
  | fuel + 1 => do
    match ← classOp with
    | some op => do
      let k ← classUnion nested false
      classOps nested (op acc k) fuel
    | none => do
      let _ ← token ']' |>.withError "unclosed character class"
      pure acc

/-- A class after its `[`; `nested` parses an inner one. -/
def classBody (nested : P Cls) : P Cls := do
  let neg ← (some <$> token '^') <|> pure none
  let k ← classUnion nested true
  let k ← classOps nested k 4096
  pure (if neg.isSome then .neg k else k)

/-- A class after its `[`, nested at most `maxDepth` deep. -/
def charClass : P Cls := fixDepth maxDepth classBody

def isNameChar (c : Char) : Bool := c.isAlphanum || c = '_' || c = '.' || c = '[' || c = ']'

/-- A group name and its closing `>`. -/
def groupName : P String := do
  let cs ← many (satisfy isNameChar)
  let _ ← token '>' |>.withError "invalid capture group name"
  match cs with
  | c :: _ => if c.isAlpha || c = '_' then pure (String.ofList cs) else fail "invalid capture group name"
  | [] => fail "empty capture group name"

/-- A group after its `(`; `alts` parses its body. -/
def group (alts : P Ast) : P Ast := do
  let name ← if (← peek?) = some '?' then do
      let _ ← next
      match ← next? with
      | some ':' => pure none
      | some 'P' => let _ ← token '<' |>.withError "unsupported group syntax"; some <$> groupName
      | some '<' => some <$> groupName
      | _ => fail "unsupported: inline flags and lookaround"
    else pure none
  let body ← alts
  let _ ← token ')' |>.withError "unclosed group"
  pure (.group name body)

/-- One element of a sequence, before any repetition. Fails without
consuming at `|`, `)` and the end. -/
def atom (alts : P Ast) : P Ast := do
  match ← peek? with
  | none | some '|' | some ')' => fail "end of sequence"
  | some '*' | some '+' | some '?' | some '{' => failAhead "repetition operator missing expression"
  | some c =>
    let _ ← next
    match c with
    | '(' => group alts
    | '[' => .cls <$> charClass
    | '.' => pure (.cls (.atom .dot))
    | '^' => pure (.assert .start)
    | '$' => pure (.assert .finish)
    | '\\' =>
      match ← escape with
      | .char d => pure (.cls (.atom (.char d)))
      | .cls k => pure (.cls k)
      | .assert a => pure (.assert a)
    | _ => pure (.cls (.atom (.char c)))

def spaces : P Unit := do let _ ← many (token ' '); pure ()

/-- A decimal count in `{..}`. -/
def count : P Nat := do
  let ds ← many (satisfy Char.isDigit)
  if ds.isEmpty then fail "invalid repetition count"
  else
    let n := decNumber ds
    if n ≥ 2 ^ 32 then fail "repetition count too large" else pure n

/-- One repetition operator, greedy or lazy: its bounds. Fails without
consuming when none is next. -/
def quantifier : P (Nat × Option Nat) := do
  let q ← match ← peek? with
    | some '*' => do let _ ← next; pure (0, none)
    | some '+' => do let _ ← next; pure (1, none)
    | some '?' => do let _ ← next; pure (0, some 1)
    | some '{' => do
      let _ ← next
      spaces
      let lo ← count
      spaces
      let hi ← if (← peek?) = some ',' then do
          let _ ← next
          spaces
          if (← peek?) = some '}' then pure none else do
            let m ← count
            spaces
            pure (some m)
        else pure (some lo)
      let _ ← token '}' |>.withError "unclosed repetition"
      match hi with
      | some m => if m < lo then fail "invalid repetition range" else pure (lo, hi)
      | none => pure (lo, hi)
    | _ => fail "no repetition"
  let _ ← (some <$> token '?') <|> pure none
  pure q

/-- An atom and its repetitions. -/
def repeated (alts : P Ast) : P Ast := do
  let a ← atom alts
  let qs ← many quantifier
  pure (qs.foldl (fun a (lo, hi) => .rep a lo hi) a)

/-- A sequence, possibly empty. -/
def sequence (alts : P Ast) : P Ast := do
  let xs ← many (repeated alts)
  pure (match xs with
    | [] => .eps
    | x :: xs => xs.foldl .cat x)

/-- Alternatives `a|b|..`; `alts` parses a group's body. -/
def alternation (alts : P Ast) : P Ast := do
  let a ← sequence alts
  let bs ← many (do let _ ← token '|'; sequence alts)
  pure (bs.foldl .alt a)

/-- A pattern, with groups nested at most `maxDepth` deep. -/
def pattern : P Ast := fixDepth maxDepth alternation

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
(`Nfa.build`) once, when the pattern value is made, not per test. -/
def ofSource (src : String) : Keel.Pattern :=
  match compile src with
  | .ok r =>
    match Regex.Nfa.build r with
    | some N => ⟨src, N.search⟩
    | none => ⟨src, r.search⟩
  | .error _ => ⟨src, fun _ => false⟩

end LeanPydantic.Regex
