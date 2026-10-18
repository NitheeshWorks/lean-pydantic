import LeanPydantic.DataTypes.Regex
import LeanPydantic.RepoImpl.Regex.Unicode
import Keel.Regex

/-!
# RepoImpl: the Rust dialect's classes, and matching through Keel

The atoms read Rust's Unicode tables; `CharClass Atom` hands them, and `\w`
as the word test, to `Keel.Regex`, whose matcher (Antimirov's partial
derivatives, compiled to numbered tables with a per-call cache) does the
rest. `Regex.search r s` is Rust's `Regex::is_match`: Keel's scan in
`Mode.search`. It reads `s` once with no backtracking; the work per
character is bounded by the pattern (`Keel.Regex.reach_length_le`).
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

/-- The Rust dialect: its atoms, and `\w` for the word assertions. -/
instance : Keel.CharClass Atom where
  test := Atom.test
  word := isWord

/-- Whether a character is in a class. -/
def Cls.test (k : Cls) (c : Char) : Bool := Keel.CharClass.test k c

/-- Is the character next to a position a word character? None at the ends. -/
def wordAt : Option Char → Bool := Keel.Regex.wordAt isWord

/-- Whether an assertion holds between the character before (`p`) and the
character after (`n`); `none` is an end of the text. -/
def Assertion.holds (a : Assertion) (p n : Option Char) : Bool := Keel.Regex.Assertion.holds isWord a p n

namespace Regex

/-- `nullable p n r`: `r` matches the empty string between `p` and `n`. -/
def nullable (p n : Option Char) (r : Regex) : Bool := Keel.Regex.nullable p n r

/-- Antimirov's partial derivatives of `r` by `c`, after `p`. -/
def pd (p : Option Char) (c : Char) (r : Regex) : List Regex := Keel.Regex.pd p c r

/-- One step of the unanchored scan. -/
def next (r : Regex) (p : Option Char) (c : Char) (T : List Regex) : List Regex :=
  Keel.Regex.next .search r p c T

/-- **Rust's `is_match`**: `r` matches somewhere in `s` (Keel's scan). -/
def search (r : Regex) (s : String) : Bool := Keel.Regex.accepts .search r s.toList

/-- A compiled pattern: Keel's numbered tables for `r`. -/
abbrev Nfa (r : Regex) := Keel.Regex.Nfa r

/-- Number the derivative terms of `r` and build the tables, once. -/
def Nfa.build (r : Regex) : Option (Nfa r) := Keel.Regex.Nfa.build r

/-- The compiled search. -/
def Nfa.search {r : Regex} (N : Nfa r) (s : String) : Bool := Keel.Regex.Nfa.accepts N .search s.toList

end Regex

end LeanPydantic.Regex
