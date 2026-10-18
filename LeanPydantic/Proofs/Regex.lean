import LeanPydantic.Specifications.Regex
import LeanPydantic.RepoImpl.Regex.Parse

/-!
# Proofs: the pattern matcher

The matcher is Keel's (`Keel.Regex`); these are its laws for the Rust
dialect.

* `derive_correct`: the partial derivatives by `c` are exactly the ways to
  finish a match that starts with `c` (Antimirov's theorem, with context).
* `search_correct`: the scan decides `Search`, Rust's `is_match`.
* `Nfa.search_eq`: the compiled matcher patterns run is the scan.
* `reach_length_le`: every state of the scan has at most `leaves r + 1`
  terms, so the work per character is bounded by the pattern and the scan is
  linear in the text. No input makes it backtrack.
-/

namespace LeanPydantic.Regex.Regex

theorem nullable_iff (r : Regex) (p n : Option Char) : nullable p n r = true ↔ Matches r p [] n :=
  Keel.Regex.nullable_iff r p n

/-- **Antimirov's theorem, in context.** -/
theorem derive_correct (p : Option Char) (c : Char) (r : Regex) (u : List Char) (n : Option Char) :
    Matches r p (c :: u) n ↔ ∃ q ∈ pd p c r, Matches q (some c) u n :=
  Keel.Regex.derive_correct p c r u n

/-- The partial derivatives by `c` are a pick from the linear form of `r`. -/
theorem pd_eq_lin (p : Option Char) (c : Char) (r : Regex) :
    pd p c r = Keel.Regex.pick c (Keel.Regex.lin (Keel.Regex.ctx Cls p) (isWord c) r) :=
  Keel.Regex.pd_eq_lin p c r

/-- `Search` is Keel's `Accepts` in `Mode.search`. -/
theorem search_iff_accepts (r : Regex) (t : List Char) :
    Search r t ↔ Keel.Regex.Accepts .search r t := by
  unfold Search Keel.Regex.Accepts
  constructor
  · rintro ⟨x, y, rfl, u, v, rfl, h⟩
    exact ⟨u ++ v, y, rfl, fun h => absurd h (by decide), u, v, rfl, fun h => absurd h (by decide), h⟩
  · rintro ⟨x, y, rfl, -, u, v, rfl, -, h⟩
    exact ⟨u ++ v, y, rfl, u, v, rfl, h⟩

/-- **The scan decides the search** (Rust's `is_match`). -/
theorem search_correct (r : Regex) (s : String) : r.search s = true ↔ Search r s.toList := by
  rw [search, Keel.Regex.accepts_iff, search_iff_accepts]

/-- **The compiled matcher is the scan.** -/
theorem Nfa.search_eq {r : Regex} (N : Nfa r) (s : String) : N.search s = r.search s :=
  Keel.Regex.Nfa.accepts_eq N .search s.toList

theorem reach_next {r : Regex} {T : List Regex} (p : Option Char) (c : Char) (h : Reach r T) :
    Reach r (next r p c T) :=
  Keel.Regex.reach_next p c h

/-- **The scan's state is bounded by the pattern**: a reachable state has at
most one term per character class of `r`, plus `r`. -/
theorem reach_length_le {r : Regex} {T : List Regex} (h : Reach r T) : T.length ≤ r.leaves + 1 :=
  Keel.Regex.reach_length_le h

end LeanPydantic.Regex.Regex

namespace LeanPydantic.Regex

/-- **A compiled pattern tests the search**: the Keel pattern built from a
source that compiles to `r` accepts a string exactly when `r` matches some
segment of it. -/
theorem ofSource_test {src : String} {r : Regex} (h : compile src = .ok r) (s : String) :
    (ofSource src).test s = true ↔ r.Search s.toList := by
  simp only [ofSource, h]
  rw [Keel.Regex.compile_test_iff, Regex.search_iff_accepts]

/-- A compiled pattern's source is the one given (it is the schema's
`pattern` and the error's `ctx.pattern`). -/
theorem ofSource_source (src : String) : (ofSource src).source = src := by
  unfold ofSource; split <;> rfl

end LeanPydantic.Regex
