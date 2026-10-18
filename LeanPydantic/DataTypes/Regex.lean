/-!
# DataTypes: regular expressions for `pattern`

pydantic checks `pattern` with Rust's `regex` crate (its default
`regex_engine='rust-regex'`), as an unanchored search. These are the terms
lean-pydantic compiles a pattern to. Matching is by partial derivatives
(`RepoImpl/Regex.lean`), which needs no backtracking and does work per input
character bounded by the pattern alone (`Proofs/Regex.lean`, `reach_length_le`).

Zero-width assertions (`^`, `$`, `\b`, ...) are terms too. Whether one holds
depends only on the characters on either side of the position, so the
semantics (`Specifications/Regex.lean`) carries the character before and the
character after each matched segment.
-/

namespace LeanPydantic.Regex

/-- A primitive set of characters. -/
inductive Atom where
  /-- One character. -/
  | char (c : Char)
  /-- An inclusive range, `a-z`. -/
  | range (lo hi : Char)
  /-- `.`: any character but `\n`. -/
  | dot
  /-- `\d`: a Unicode decimal digit. -/
  | digit
  /-- `\w`: a Unicode word character. -/
  | word
  /-- `\s`: Unicode white space. -/
  | space
  deriving DecidableEq, Repr, Inhabited

/-- A character class: atoms closed under Rust's class operations. -/
inductive Cls where
  | atom (a : Atom)
  /-- `[ab]` -/
  | union (k l : Cls)
  /-- `[a&&b]` -/
  | inter (k l : Cls)
  /-- `[a--b]` -/
  | diff (k l : Cls)
  /-- `[a~~b]` -/
  | sym (k l : Cls)
  /-- `[^a]`, `\D`, `\W`, `\S` -/
  | neg (k : Cls)
  deriving DecidableEq, Repr, Inhabited

/-- A zero-width assertion. -/
inductive Assertion where
  /-- `^`, `\A`: the start of the text. -/
  | start
  /-- `$`, `\z`: the end of the text (Rust's `$` does not match before a final `\n`). -/
  | finish
  /-- `\b` -/
  | wordBoundary
  /-- `\B` -/
  | notWordBoundary
  /-- `\<` -/
  | wordStart
  /-- `\>` -/
  | wordEnd
  deriving DecidableEq, Repr, Inhabited

/-- A regular expression. -/
inductive Regex where
  /-- Matches nothing. -/
  | empty
  /-- Matches the empty string. -/
  | eps
  /-- One character of a class. -/
  | cls (k : Cls)
  /-- The empty string, where the assertion holds. -/
  | assert (a : Assertion)
  | alt (r s : Regex)
  | cat (r s : Regex)
  | star (r : Regex)
  deriving DecidableEq, Repr, Inhabited

end LeanPydantic.Regex
