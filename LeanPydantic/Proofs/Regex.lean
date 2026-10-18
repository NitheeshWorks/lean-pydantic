import LeanPydantic.Specifications.Regex
import LeanPydantic.RepoImpl.Regex.Parse

/-!
# Proofs: the pattern matcher

* `nullable_iff`: `nullable` decides the empty match, assertions included.
* `derive_correct`: the partial derivatives by `c` are exactly the ways to
  finish a match that starts with `c` (Antimirov's theorem, with context).
* `search_correct`: the scan decides `Search`, Rust's `is_match`.
* `reach_length_le`: every state of the scan has at most `leaves r + 1`
  terms, so the work per character is bounded by the pattern and the scan is
  linear in the text. No input makes it backtrack.
-/

namespace LeanPydantic.Regex.Regex

variable {r s : Regex} {p n : Option Char}

/-! ## Inversion -/

theorem matches_empty_iff {u : List Char} : Matches empty p u n ↔ False :=
  ⟨fun h => (by cases h), False.elim⟩

theorem matches_eps_iff {u : List Char} : Matches eps p u n ↔ u = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .eps⟩

theorem matches_cls_iff {k : Cls} {u : List Char} :
    Matches (cls k) p u n ↔ ∃ c, u = [c] ∧ k.test c = true :=
  ⟨fun h => by cases h with | cls h => exact ⟨_, rfl, h⟩, fun ⟨_, h, hc⟩ => h ▸ .cls hc⟩

theorem matches_assert_iff {a : Assertion} {u : List Char} :
    Matches (assert a) p u n ↔ u = [] ∧ a.holds p n = true :=
  ⟨fun h => by cases h with | assert h => exact ⟨rfl, h⟩, fun ⟨h, ha⟩ => h ▸ .assert ha⟩

theorem matches_alt_iff {u : List Char} :
    Matches (alt r s) p u n ↔ Matches r p u n ∨ Matches s p u n :=
  ⟨fun h => by cases h with | altL h => exact .inl h | altR h => exact .inr h,
   fun h => h.elim .altL .altR⟩

theorem matches_cat_iff {w : List Char} :
    Matches (cat r s) p w n ↔
      ∃ u v, w = u ++ v ∧ Matches r p u (v.head?.or n) ∧ Matches s (u.getLast?.or p) v n :=
  ⟨fun h => by cases h with | cat h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩,
   fun ⟨_, _, hw, h₁, h₂⟩ => hw ▸ .cat h₁ h₂⟩

theorem matches_star_iff {w : List Char} :
    Matches (star r) p w n ↔ w = [] ∨
      ∃ u v, u ≠ [] ∧ w = u ++ v ∧ Matches r p u (v.head?.or n) ∧
        Matches (star r) (u.getLast?.or p) v n := by
  constructor
  · intro h
    cases h with
    | starNil => exact .inl rfl
    | starCons hu h₁ h₂ => exact .inr ⟨_, _, hu, rfl, h₁, h₂⟩
  · rintro (h | ⟨_, _, hu, hw, h₁, h₂⟩)
    · exact h ▸ .starNil
    · exact hw ▸ .starCons hu h₁ h₂

theorem matches_seq_iff {w : List Char} : Matches (seq r s) p w n ↔ Matches (cat r s) p w n := by
  unfold seq
  split
  · subst_vars
    rw [matches_cat_iff]
    constructor
    · intro h; exact ⟨[], w, rfl, .eps, h⟩
    · rintro ⟨u, v, rfl, h₁, h₂⟩
      rw [matches_eps_iff] at h₁
      subst h₁
      exact h₂
  · exact Iff.rfl

theorem getLast?_or_cons (c : Char) (l : List Char) (p : Option Char) :
    (c :: l).getLast?.or p = l.getLast?.or (some c) := by
  cases l <;> simp [List.getLast?_cons]

/-! ## The empty match -/

/-- `nullable` decides whether `r` matches the empty string in context. -/
theorem nullable_iff (r : Regex) (p n : Option Char) : nullable p n r = true ↔ Matches r p [] n := by
  induction r with
  | empty => simp [nullable, matches_empty_iff]
  | eps => simp [nullable, matches_eps_iff]
  | cls k => simp [nullable, matches_cls_iff]
  | assert a => simp [nullable, matches_assert_iff]
  | alt r s ihr ihs => simp [nullable, matches_alt_iff, ihr, ihs]
  | cat r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true, ihr, ihs, matches_cat_iff]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨[], [], rfl, h₁, h₂⟩
    · rintro ⟨u, v, huv, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
      exact ⟨h₁, h₂⟩
  | star r => simp [nullable, Matches.starNil]

/-! ## Partial derivatives -/

/-- **Antimirov's theorem, in context**: `r` matches `c :: u` after `p`
exactly when one of its partial derivatives by `c` matches `u` after `c`. -/
theorem derive_correct (p : Option Char) (c : Char) (r : Regex) (u : List Char) (n : Option Char) :
    Matches r p (c :: u) n ↔ ∃ q ∈ pd p c r, Matches q (some c) u n := by
  induction r generalizing u n with
  | empty => simp [pd, matches_empty_iff]
  | eps => simp [pd, matches_eps_iff]
  | assert a => simp [pd, matches_assert_iff]
  | cls k =>
    rw [matches_cls_iff]
    by_cases hk : k.test c = true
    · simp only [pd, hk, ite_true, List.mem_singleton, exists_eq_left, matches_eps_iff]
      constructor
      · rintro ⟨d, hd, _⟩
        simp only [List.cons.injEq] at hd
        exact hd.2
      · intro h; exact ⟨c, by simp [h], hk⟩
    · constructor
      · rintro ⟨d, hd, hdk⟩
        simp only [List.cons.injEq] at hd
        exact absurd (hd.1 ▸ hdk) hk
      · rintro ⟨q, hq, _⟩
        simp [pd, hk] at hq
  | alt r s ihr ihs =>
    simp only [matches_alt_iff, ihr, ihs, pd, List.mem_append]
    constructor
    · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
      · exact ⟨q, .inl hq, h⟩
      · exact ⟨q, .inr hq, h⟩
    · rintro ⟨q, hq | hq, h⟩
      · exact .inl ⟨q, hq, h⟩
      · exact .inr ⟨q, hq, h⟩
  | cat r s ihr ihs =>
    rw [matches_cat_iff]
    simp only [pd, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨u₁, v, hw, h₁, h₂⟩
      cases u₁ with
      | nil =>
        simp only [List.nil_append] at hw
        subst hw
        have hn : nullable p (some c) r = true := (nullable_iff r p (some c)).2 h₁
        obtain ⟨q, hq, hm⟩ := (ihs u n).1 h₂
        exact ⟨q, .inr (by simpa [hn] using hq), hm⟩
      | cons d u₁ =>
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨q, hq, hm⟩ := (ihr u₁ _).1 h₁
        refine ⟨seq q s, .inl ⟨q, hq, rfl⟩, ?_⟩
        rw [matches_seq_iff, matches_cat_iff]
        exact ⟨u₁, v, rfl, hm, by rwa [getLast?_or_cons] at h₂⟩
    · rintro ⟨q', h | h, hm⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rw [matches_seq_iff, matches_cat_iff] at hm
        obtain ⟨u₁, v, rfl, h₁, h₂⟩ := hm
        exact ⟨c :: u₁, v, rfl, (ihr u₁ _).2 ⟨q, hq, h₁⟩, by rwa [getLast?_or_cons]⟩
      · split at h
        · rename_i hn
          exact ⟨[], c :: u, rfl, (nullable_iff r p (some c)).1 hn, (ihs u n).2 ⟨q', h, hm⟩⟩
        · simp at h
  | star r ih =>
    rw [matches_star_iff]
    simp only [pd, List.mem_map]
    constructor
    · rintro (h | ⟨u₁, v, hne, hw, h₁, h₂⟩)
      · simp at h
      · cases u₁ with
        | nil => exact absurd rfl hne
        | cons d u₁ =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨q, hq, hm⟩ := (ih u₁ _).1 h₁
          refine ⟨seq q (star r), ⟨q, hq, rfl⟩, ?_⟩
          rw [matches_seq_iff, matches_cat_iff]
          exact ⟨u₁, v, rfl, hm, by rwa [getLast?_or_cons] at h₂⟩
    · rintro ⟨q', ⟨q, hq, rfl⟩, hm⟩
      rw [matches_seq_iff, matches_cat_iff] at hm
      obtain ⟨u₁, v, rfl, h₁, h₂⟩ := hm
      exact .inr ⟨c :: u₁, v, List.cons_ne_nil _ _, rfl, (ih u₁ _).2 ⟨q, hq, h₁⟩,
        by rwa [getLast?_or_cons]⟩

/-! ## The scan -/

theorem mem_foldl_insert (l acc : List Regex) (q : Regex) :
    q ∈ l.foldl (fun acc q => acc.insert q) acc ↔ q ∈ acc ∨ q ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_insert_iff, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

theorem nodup_insert {l : List Regex} (q : Regex) (h : l.Nodup) : (l.insert q).Nodup := by
  unfold List.insert
  split
  · exact h
  · rename_i hq
    exact List.nodup_cons.2 ⟨by simpa using hq, h⟩

theorem nodup_foldl_insert (l acc : List Regex) (h : acc.Nodup) :
    (l.foldl (fun acc q => acc.insert q) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons a l ih => exact ih _ (nodup_insert a h)

theorem mem_next {r q : Regex} {c : Char} {T : List Regex} :
    q ∈ next r p c T ↔ q = r ∨ ∃ t ∈ T, q ∈ pd p c t := by
  simp [next, uniq, List.mem_insert_iff, mem_foldl_insert, List.mem_flatMap]

/-- What the scan's state means after the text `pre`: a term of it matches
`v` exactly when `r` matches from a position in `pre` through `v`. -/
def Inv (r : Regex) (pre : List Char) (T : List Regex) : Prop :=
  ∀ v n, (∃ q ∈ T, Matches q pre.getLast? v n) ↔
    ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ Matches r u₁.getLast? (u₂ ++ v) n

theorem inv_init (r : Regex) : Inv r [] [r] := by
  intro v n
  constructor
  · rintro ⟨q, hq, h⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨[], [], rfl, h⟩
  · rintro ⟨u₁, u₂, h, hm⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm
    exact ⟨r, List.mem_singleton_self r, hm⟩

theorem inv_next {r : Regex} {pre : List Char} {T : List Regex} (c : Char) (h : Inv r pre T) :
    Inv r (pre ++ [c]) (next r pre.getLast? c T) := by
  intro v n
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  have step : (∃ q ∈ next r pre.getLast? c T, Matches q (some c) v n) ↔
      Matches r (some c) v n ∨ ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ Matches r u₁.getLast? (u₂ ++ c :: v) n := by
    rw [← h (c :: v) n]
    simp only [mem_next]
    constructor
    · rintro ⟨q, rfl | ⟨t, ht, hq⟩, hm⟩
      · exact .inl hm
      · exact .inr ⟨t, ht, (derive_correct _ c t v n).2 ⟨q, hq, hm⟩⟩
    · rintro (hm | ⟨t, ht, hm⟩)
      · exact ⟨r, .inl rfl, hm⟩
      · obtain ⟨q, hq, hm⟩ := (derive_correct _ c t v n).1 hm
        exact ⟨q, .inr ⟨t, ht, hq⟩, hm⟩
  rw [step]
  constructor
  · rintro (hm | ⟨u₁, u₂, rfl, hm⟩)
    · exact ⟨pre ++ [c], [], by simp, by simpa using hm⟩
    · exact ⟨u₁, u₂ ++ [c], by simp, by simpa using hm⟩
  · rintro ⟨u₁, u₂, hpre, hm⟩
    rcases List.eq_nil_or_concat u₂ with rfl | ⟨L, b, rfl⟩
    · simp only [List.append_nil] at hpre
      subst hpre
      exact .inl (by simpa using hm)
    · simp only [List.concat_eq_append, ← List.append_assoc] at hpre
      obtain ⟨rfl, hcb⟩ := List.append_inj' hpre rfl
      simp only [List.cons.injEq, and_true] at hcb
      subst hcb
      exact .inr ⟨u₁, L, rfl, by simpa using hm⟩

theorem scan_spec (r : Regex) (rest : List Char) :
    ∀ (pre : List Char) (T : List Regex), Inv r pre T →
      (scan r pre.getLast? rest T = true ↔
        ∃ x y, rest = x ++ y ∧ ∃ u₁ u₂, pre ++ x = u₁ ++ u₂ ∧ Matches r u₁.getLast? u₂ y.head?) := by
  induction rest with
  | nil =>
    intro pre T h
    simp only [scan, List.any_eq_true, nullable_iff]
    rw [show (∃ q ∈ T, Matches q pre.getLast? [] none) ↔ _ from h [] none]
    constructor
    · rintro ⟨u₁, u₂, hpre, hm⟩
      exact ⟨[], [], rfl, u₁, u₂, by simpa using hpre, by simpa using hm⟩
    · rintro ⟨x, y, hxy, u₁, u₂, hpre, hm⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hxy.symm
      exact ⟨u₁, u₂, by simpa using hpre, by simpa using hm⟩
  | cons c cs ih =>
    intro pre T h
    have ih' := ih (pre ++ [c]) _ (inv_next c h)
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at ih'
    have first : (T.any (nullable pre.getLast? (some c)) = true) ↔
        ∃ u₁ u₂, pre = u₁ ++ u₂ ∧ Matches r u₁.getLast? u₂ (some c) := by
      simp only [List.any_eq_true, nullable_iff]
      rw [show (∃ q ∈ T, Matches q pre.getLast? [] (some c)) ↔ _ from h [] (some c)]
      simp
    have hscan : scan r pre.getLast? (c :: cs) T = true ↔
        T.any (nullable pre.getLast? (some c)) = true ∨ scan r (some c) cs (next r pre.getLast? c T) = true := by
      simp only [scan]
      split <;> simp_all
    rw [hscan, first, ih']
    constructor
    · rintro (⟨u₁, u₂, hpre, hm⟩ | ⟨x, y, rfl, u₁, u₂, hpre, hm⟩)
      · exact ⟨[], c :: cs, rfl, u₁, u₂, by simpa using hpre, hm⟩
      · exact ⟨c :: x, y, rfl, u₁, u₂, by simpa using hpre, hm⟩
    · rintro ⟨x, y, hxy, u₁, u₂, hpre, hm⟩
      cases x with
      | nil =>
        simp only [List.nil_append] at hxy
        subst hxy
        exact .inl ⟨u₁, u₂, by simpa using hpre, hm⟩
      | cons d x =>
        simp only [List.cons_append, List.cons.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        exact .inr ⟨x, y, rfl, u₁, u₂, by simpa using hpre, hm⟩

/-- **The matcher decides the search**: `search r s` holds exactly when `r`
matches some segment of `s`, with the assertions read in context. -/
theorem search_correct (r : Regex) (s : String) : r.search s = true ↔ Search r s.toList := by
  unfold search Search
  rw [show (none : Option Char) = ([] : List Char).getLast? from rfl,
    scan_spec r s.toList [] [r] (inv_init r)]
  simp

/-! ## The state is bounded by the pattern -/

theorem pd_mem_PD {p : Option Char} {c : Char} {q : Regex} :
    ∀ {r : Regex}, q ∈ pd p c r → q ∈ PD r
  | empty, h | eps, h | assert _, h => by simp [pd] at h
  | cls k, h => by
    simp only [pd] at h
    split at h <;> simp_all [PD]
  | alt r s, h => by
    simp only [pd, List.mem_append] at h
    simp only [PD, List.mem_append]
    exact h.imp pd_mem_PD pd_mem_PD
  | cat r s, h => by
    simp only [pd, List.mem_append, List.mem_map] at h
    simp only [PD, List.mem_append, List.mem_map]
    rcases h with ⟨q', hq', rfl⟩ | h
    · exact .inl ⟨q', pd_mem_PD hq', rfl⟩
    · split at h
      · exact .inr (pd_mem_PD h)
      · simp at h
  | star r, h => by
    simp only [pd, List.mem_map] at h
    simp only [PD, List.mem_map]
    obtain ⟨q', hq', rfl⟩ := h
    exact ⟨q', pd_mem_PD hq', rfl⟩

/-- **The partial derivatives are closed under derivation** (Antimirov). -/
theorem PD_closed {p : Option Char} {c : Char} :
    ∀ {r q q' : Regex}, q ∈ PD r → q' ∈ pd p c q → q' ∈ PD r
  | empty, _, _, h, _ | eps, _, _, h, _ | assert _, _, _, h, _ => by simp [PD] at h
  | cls k, q, q', h, h' => by
    simp only [PD, List.mem_singleton] at h
    subst h
    simp [pd] at h'
  | alt r s, q, q', h, h' => by
    simp only [PD, List.mem_append] at h ⊢
    exact h.imp (PD_closed · h') (PD_closed · h')
  | cat r s, q, q', h, h' => by
    simp only [PD, List.mem_append, List.mem_map] at h ⊢
    rcases h with ⟨q₁, hq₁, rfl⟩ | h
    · unfold seq at h'
      split at h'
      · exact .inr (pd_mem_PD h')
      · simp only [pd, List.mem_append, List.mem_map] at h'
        rcases h' with ⟨q₂, hq₂, rfl⟩ | h'
        · exact .inl ⟨q₂, PD_closed hq₁ hq₂, rfl⟩
        · split at h'
          · exact .inr (pd_mem_PD h')
          · simp at h'
    · exact .inr (PD_closed h h')
  | star r, q, q', h, h' => by
    simp only [PD, List.mem_map] at h
    obtain ⟨q₁, hq₁, rfl⟩ := h
    have hstar : ∀ {x}, x ∈ pd p c (star r) → x ∈ PD (star r) := pd_mem_PD
    unfold seq at h'
    split at h'
    · exact hstar h'
    · simp only [pd, List.mem_append, List.mem_map] at h'
      rcases h' with ⟨q₂, hq₂, rfl⟩ | h'
      · simp only [PD, List.mem_map]
        exact ⟨q₂, PD_closed hq₁ hq₂, rfl⟩
      · split at h'
        · exact hstar h'
        · simp at h'

theorem length_PD : ∀ r : Regex, (PD r).length = r.leaves
  | empty | eps | assert _ | cls _ => rfl
  | alt r s | cat r s => by simp [PD, leaves, length_PD r, length_PD s]
  | star r => by simp [PD, leaves, length_PD r]

theorem reach_init (r : Regex) : Reach r [r] :=
  ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun q hq => by simp_all⟩

theorem reach_next {r : Regex} {T : List Regex} (p : Option Char) (c : Char) (h : Reach r T) :
    Reach r (next r p c T) := by
  refine ⟨nodup_insert r (nodup_foldl_insert _ [] List.nodup_nil), fun q hq => ?_⟩
  rcases mem_next.1 hq with rfl | ⟨t, ht, hqt⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    rcases List.mem_cons.1 (h.2 t ht) with htr | htp
    · exact pd_mem_PD (htr ▸ hqt)
    · exact PD_closed htp hqt

/-- **The scan's state is bounded by the pattern**: a reachable state has at
most one term per character class of `r`, plus `r`. -/
theorem reach_length_le {r : Regex} {T : List Regex} (h : Reach r T) : T.length ≤ r.leaves + 1 := by
  have := List.Nodup.length_le_of_subset h.1 (fun q hq => h.2 q hq)
  simpa [length_PD] using this

end LeanPydantic.Regex.Regex

namespace LeanPydantic.Regex

/-- **A compiled pattern tests the search**: the Keel pattern built from a
source that compiles to `r` accepts a string exactly when `r` matches some
segment of it. -/
theorem ofSource_test {src : String} {r : Regex} (h : compile src = .ok r) (s : String) :
    (ofSource src).test s = true ↔ r.Search s.toList := by
  simp only [ofSource, h, Regex.searchDfa_eq]
  exact Regex.search_correct r s

/-- A compiled pattern's source is the one given (it is the schema's
`pattern` and the error's `ctx.pattern`). -/
theorem ofSource_source (src : String) : (ofSource src).source = src := by
  unfold ofSource; split <;> rfl

end LeanPydantic.Regex
