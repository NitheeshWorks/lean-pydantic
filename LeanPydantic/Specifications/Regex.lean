import LeanPydantic.RepoImpl.Regex.Match

/-!
# Specifications: what a pattern matches

`Matches r p u n`: `r` matches exactly the characters `u`, where `p` is the
character before `u` and `n` the character after it (`none` at an end of
the text). Classes and assertions read their characters with `Cls.test` and
`Assertion.holds`; everything else is the textbook language of a regular
expression. A star's iterations are non-empty, which loses nothing: an
empty iteration matches only where the star already matches.

`Search r t`: `r` matches some segment of `t`, as Rust's `is_match`.

`PD r`: Antimirov's set of partial derivatives of `r`, one per character
class, which bounds the matcher's state.
-/

namespace LeanPydantic.Regex

namespace Regex

/-- `r` matches `u`, between the characters `p` and `n`. -/
inductive Matches : Regex → Option Char → List Char → Option Char → Prop where
  | eps {p n} : Matches eps p [] n
  | cls {k c p n} : k.test c = true → Matches (cls k) p [c] n
  | assert {a p n} : a.holds p n = true → Matches (assert a) p [] n
  | altL {r s p u n} : Matches r p u n → Matches (alt r s) p u n
  | altR {r s p u n} : Matches s p u n → Matches (alt r s) p u n
  | cat {r s p u v n} : Matches r p u (v.head?.or n) → Matches s (u.getLast?.or p) v n →
      Matches (cat r s) p (u ++ v) n
  | starNil {r p n} : Matches (star r) p [] n
  | starCons {r p u v n} : u ≠ [] → Matches r p u (v.head?.or n) →
      Matches (star r) (u.getLast?.or p) v n → Matches (star r) p (u ++ v) n

/-- `r` matches somewhere in `t`: `t = x ++ y` and `x = u ++ v`, with `v`
matched between the last character of `u` and the first of `y`. -/
def Search (r : Regex) (t : List Char) : Prop :=
  ∃ x y, t = x ++ y ∧ ∃ u v, x = u ++ v ∧ Matches r u.getLast? v y.head?

/-- Antimirov's partial derivatives of `r`, over every character. -/
def PD : Regex → List Regex
  | empty | eps | assert _ => []
  | cls _ => [eps]
  | alt r s => PD r ++ PD s
  | cat r s => (PD r).map (seq · s) ++ PD s
  | star r => (PD r).map (seq · (star r))

/-- The number of character classes in `r`. -/
def leaves : Regex → Nat
  | empty | eps | assert _ => 0
  | cls _ => 1
  | alt r s | cat r s => r.leaves + s.leaves
  | star r => r.leaves

/-- A state the scan for `r` can reach: no duplicates, and only `r` and its
partial derivatives. -/
def Reach (r : Regex) (T : List Regex) : Prop := T.Nodup ∧ ∀ q ∈ T, q ∈ r :: PD r

end Regex

end LeanPydantic.Regex
