import LeanPydantic.Specifications

/-!
# Proofs: pydantic-order validation is sound and complete

`validatePy` reorders the conjunction and stops at the first failing
conjunct; reordering a conjunction does not change what it means, so it
inherits Keel's `validate_iff`. And a constraint's JSON Schema keywords are
sound for every carrier type with a `LawfulConstrained` instance, by one
induction.
-/

namespace Keel.Constraint

open LeanPydantic
open LeanJson (Json)

variable {α : Type}

theorem conjuncts_holds (c : Constraint α) (x : α) :
    (∀ a ∈ c.conjuncts, a.holds x) ↔ c.holds x := by
  induction c with
  | and c d ihc ihd =>
    simp only [conjuncts, List.mem_append, holds]
    constructor
    · intro h; exact ⟨ihc.1 fun a ha => h a (.inl ha), ihd.1 fun a ha => h a (.inr ha)⟩
    · rintro ⟨h1, h2⟩ a (ha | ha)
      · exact ihc.2 h1 a ha
      · exact ihd.2 h2 a ha
  | _ => simp [conjuncts]

theorem ordered_holds (c : Constraint α) (x : α) :
    (∀ a ∈ c.ordered, a.holds x) ↔ c.holds x := by
  rw [← conjuncts_holds]
  have hp := List.mergeSort_perm c.conjuncts (fun a b => decide (rank a ≤ rank b))
  exact ⟨fun h a ha => h a (hp.mem_iff.2 ha), fun h a ha => h a (hp.mem_iff.1 ha)⟩

theorem firstFailure_none (x : α) :
    ∀ l : List (Constraint α), firstFailure x l = none ↔ ∀ a ∈ l, a.holds x
  | [] => by simp [firstFailure]
  | a :: as => by
    unfold firstFailure
    split
    · rename_i es h
      simp only [reduceCtorEq, false_iff, List.mem_cons, forall_eq_or_imp, not_and]
      intro ha; rw [(validate_iff a x).2 ha] at h; cases h
    · rename_i y h
      rw [firstFailure_none x as]
      have := ((validate_eq_ok_iff a x y).1 h).2
      simp [this]

theorem firstFailure_ne_nil (x : α) :
    ∀ (l : List (Constraint α)) (es : List (Keel.Refine.Error α)), firstFailure x l = some es → es ≠ []
  | [], _, h => by simp [firstFailure] at h
  | a :: as, es, h => by
    unfold firstFailure at h
    split at h
    · rename_i es' he; cases h; exact validate_error_ne_nil a he
    · exact firstFailure_ne_nil x as es h

/-- **Sound and complete**: validation in pydantic's order succeeds, giving
its input back, exactly when the constraint holds. -/
theorem validatePy_iff (c : Constraint α) (x : α) : c.validatePy x = .ok x ↔ c.holds x := by
  rw [← ordered_holds, ← firstFailure_none]
  unfold validatePy
  split <;> simp_all

/-- Soundness: a validated value is the input, and satisfies the constraint. -/
theorem validate_sound (c : Constraint α) {x y : α} (h : c.validatePy x = .ok y) :
    y = x ∧ c.holds x := by
  unfold validatePy at h
  split at h
  · cases h
  · rename_i hn; cases h
    exact ⟨rfl, (ordered_holds c x).1 ((firstFailure_none x _).1 hn)⟩

/-- Completeness: a value satisfying the constraint validates. -/
theorem validate_complete (c : Constraint α) {x : α} (h : c.holds x) : c.validatePy x = .ok x :=
  (validatePy_iff c x).2 h

/-- A failed validation reports at least one error. -/
theorem validate_errors_nonempty (c : Constraint α) {x : α} {es : List (Keel.Refine.Error α)}
    (h : c.validatePy x = .error es) : es ≠ [] := by
  unfold validatePy at h
  split at h
  · rename_i es' he; cases h; exact firstFailure_ne_nil x _ _ he
  · cases h

/-- Validation fails exactly when the constraint does not hold. -/
theorem validatePy_error_iff (c : Constraint α) (x : α) :
    (∃ es, c.validatePy x = .error es) ↔ ¬ c.holds x := by
  rw [← validatePy_iff]
  unfold validatePy
  split <;> simp

/-- A constraint's keywords hold on strictly validated input satisfying it. -/
theorem keywordsOf_sound [FromJson α] [Constrained α] [LawfulConstrained α] {cfg : Cfg} {j : Json}
    {x : α} (hs : cfg.strict = true) (hv : fromJson cfg j = .ok x) (c : Constraint α) :
    c.AllStd → c.holds x → ∀ k ∈ c.keywordsOf, k.check j = true := by
  induction c with
  | and c d ihc ihd =>
    rintro ⟨s1, s2⟩ ⟨h1, h2⟩ k hk
    simp only [keywordsOf, List.mem_append] at hk
    exact hk.elim (ihc s1 h1 k) (ihd s2 h2 k)
  | or | not | oneOf => intro _ _ k hk; simp [keywordsOf] at hk
  | _ =>
    intro hstd h k hk
    exact LawfulConstrained.keywords_sound cfg j x _ (by simpa [AllStd] using hstd) hs hv h k
      (by simpa [keywordsOf] using hk)

end Keel.Constraint
