import Keel.DataTypes.Regex

/-!
# DataTypes: regular expressions for `pattern`

pydantic checks `pattern` with Rust's `regex` crate (its default
`regex_engine='rust-regex'`), as an unanchored search. A pattern compiles
to a `Keel.Regex` over this dialect's character classes: Keel supplies the
terms, their meaning and the linear-time matcher (`Keel.Regex`), and this
repository keeps the Rust dialect: its atoms (`\d`, `\w`, `\s` with Rust's
Unicode tables, `.` without `\n`, Rust's simple case folding for `(?i)`), its
word characters, and its parser (`RepoImpl/Regex/Parse.lean`).
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
  /-- `.` under `(?s)`: any character. -/
  | any
  /-- `.` under `(?R)`: any character but `\n` and `\r`. -/
  | dotCRLF
  /-- A range under `(?i)`: a character with a simple case variant (itself
  included) in `lo-hi`. -/
  | caseless (lo hi : Char)
  /-- `\d`: a Unicode decimal digit. -/
  | digit
  /-- `\w`: a Unicode word character. -/
  | word
  /-- `\s`: Unicode white space. -/
  | space
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A character class: atoms closed under Rust's class operations (`[ab]`,
`[a&&b]`, `[a--b]`, `[a~~b]`, `[^a]`). -/
abbrev Cls := Keel.Regex.Cls Atom

/-- A zero-width assertion (`^`, `$`, `\b`, `\B`, `\<`, `\>`). -/
abbrev Assertion := Keel.Regex.Assertion

/-- A regular expression in the Rust dialect. -/
abbrev Regex := Keel.Regex Cls

end LeanPydantic.Regex
