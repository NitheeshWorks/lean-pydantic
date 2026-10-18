import LeanPydantic.RepoImpl.Regex.Match

/-!
# Specifications: what a pattern matches

`Matches r p u n` (Keel's): `r` matches exactly the characters `u`, where
`p` is the character before `u` and `n` the character after it (`none` at
an end of the text). Classes and assertions read the Rust dialect's tables.

`Search r t`: `r` matches some segment of `t`, as Rust's `is_match`. It is
Keel's `Accepts` in `Mode.search` (`search_iff_accepts`).

`PD r`: Antimirov's set of partial derivatives of `r`, one per character
class, which bounds the matcher's state; `Reach r T` is a state the scan can
reach.
-/

namespace LeanPydantic.Regex

namespace Regex

/-- `r` matches `u`, between the characters `p` and `n`. -/
abbrev Matches (r : Regex) (p : Option Char) (u : List Char) (n : Option Char) : Prop :=
  Keel.Regex.Matches r p u n

/-- `r` matches somewhere in `t`: `t = x ++ y` and `x = u ++ v`, with `v`
matched between the last character of `u` and the first of `y`. -/
def Search (r : Regex) (t : List Char) : Prop :=
  ∃ x y, t = x ++ y ∧ ∃ u v, x = u ++ v ∧ Matches r u.getLast? v y.head?

/-- Antimirov's partial derivatives of `r`, over every character. -/
abbrev PD (r : Regex) : List Regex := Keel.Regex.PD r

/-- The number of character classes in `r`. -/
abbrev leaves (r : Regex) : Nat := Keel.Regex.leaves r

/-- A state the scan for `r` can reach: no duplicates, and only `r` and its
partial derivatives. -/
abbrev Reach (r : Regex) (T : List Regex) : Prop := Keel.Regex.Reach r T

end Regex

end LeanPydantic.Regex
