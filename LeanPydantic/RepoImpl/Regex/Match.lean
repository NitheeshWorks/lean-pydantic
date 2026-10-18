import LeanPydantic.DataTypes.Regex
import LeanPydantic.RepoImpl.Regex.Unicode

/-!
# RepoImpl: matching by partial derivatives

`Regex.search r s` decides whether `r` matches somewhere in `s`, as Rust's
`Regex::is_match` does. The scan reads `s` once, left to right, keeping a
set of terms: Antimirov's partial derivatives of `r` by the text read so far,
started at every position, with duplicates removed. A term is nullable at
the next position exactly when a match ends there.

There is no backtracking. Every term of the set is `r` or one of its partial
derivatives `PD r`, of which there are at most as many as `r` has character
classes (`Proofs/Regex.lean`, `reach_length_le`), so the work per character
is bounded by the pattern, and the scan is linear in the input. It is a tail
loop over the input; the only other recursion is on the pattern's terms.
-/

namespace LeanPydantic.Regex

/-- Binary search for `n` among sorted, disjoint inclusive ranges. -/
def inRanges (t : Array (Nat × Nat)) (n : Nat) : Bool :=
  go 0 t.size 32
where
  /-- At most 32 halvings, more than any table here needs (2^32 entries). -/
  go (lo hi : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match t[mid]? with
        | some (a, b) =>
          if n < a then go lo mid fuel
          else if b < n then go (mid + 1) hi fuel
          else true
        | none => false
      else false

/-- `\w` -/
def isWord (c : Char) : Bool :=
  if c.toNat < 128 then c.isAlphanum || c == '_' else inRanges Unicode.word c.toNat

/-- `\d` -/
def isDigit (c : Char) : Bool :=
  if c.toNat < 128 then c.isDigit else inRanges Unicode.digit c.toNat

/-- `\s` -/
def isSpace (c : Char) : Bool := inRanges Unicode.space c.toNat

/-- Whether a character is in an atom. -/
def Atom.test : Atom → Char → Bool
  | .char a, c => c == a
  | .range lo hi, c => lo ≤ c && c ≤ hi
  | .dot, c => c != '\n'
  | .digit, c => isDigit c
  | .word, c => isWord c
  | .space, c => isSpace c

/-- Whether a character is in a class. -/
def Cls.test : Cls → Char → Bool
  | .atom a, c => a.test c
  | .union k l, c => k.test c || l.test c
  | .inter k l, c => k.test c && l.test c
  | .diff k l, c => k.test c && !l.test c
  | .sym k l, c => k.test c != l.test c
  | .neg k, c => !k.test c

/-- Is the character next to a position a word character? None at the ends. -/
def wordAt : Option Char → Bool
  | some c => isWord c
  | none => false

/-- Whether an assertion holds between the character before (`p`) and the
character after (`n`); `none` is an end of the text. -/
def Assertion.holds : Assertion → Option Char → Option Char → Bool
  | .start, p, _ => p.isNone
  | .finish, _, n => n.isNone
  | .wordBoundary, p, n => wordAt p != wordAt n
  | .notWordBoundary, p, n => wordAt p == wordAt n
  | .wordStart, p, n => !wordAt p && wordAt n
  | .wordEnd, p, n => wordAt p && !wordAt n

namespace Regex

/-- Whether `r` matches the empty string between `p` and `n`. -/
def nullable (p n : Option Char) : Regex → Bool
  | empty => false
  | eps => true
  | cls _ => false
  | assert a => a.holds p n
  | alt r s => nullable p n r || nullable p n s
  | cat r s => nullable p n r && nullable p n s
  | star _ => true

/-- Concatenation, dropping a leading `eps`. -/
def seq (r s : Regex) : Regex := if r = eps then s else cat r s

/-- Partial derivatives of `r` by `c`, read just after the character `p`:
the terms that, matched after `c`, make up a match of `r` that starts
with `c`. -/
def pd (p : Option Char) (c : Char) : Regex → List Regex
  | empty => []
  | eps => []
  | cls k => if k.test c then [eps] else []
  | assert _ => []
  | alt r s => pd p c r ++ pd p c s
  | cat r s =>
    (pd p c r).map (seq · s) ++ (if nullable p (some c) r then pd p c s else [])
  | star r => (pd p c r).map (seq · (star r))

/-- The list without duplicates (first occurrences kept, in reverse). -/
def uniq (l : List Regex) : List Regex := l.foldl (fun acc q => acc.insert q) []

/-- One step of the scan: the derivatives of the set by `c` read after `p`,
and `r` again, for a match starting after `c`. -/
def next (r : Regex) (p : Option Char) (c : Char) (T : List Regex) : List Regex :=
  (uniq (T.flatMap (pd p c))).insert r

/-- The scan, after the character `p`, on the rest of the text. -/
def scan (r : Regex) (p : Option Char) : List Char → List Regex → Bool
  | [], T => T.any (nullable p none)
  | c :: cs, T => if T.any (nullable p (some c)) then true else scan r (some c) cs (next r p c T)

/-- Whether `r` matches somewhere in `s` (Rust's `is_match`). -/
def search (r : Regex) (s : String) : Bool := scan r none s.toList [r]

end Regex

end LeanPydantic.Regex
