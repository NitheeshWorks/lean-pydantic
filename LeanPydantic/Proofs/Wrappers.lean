import LeanPydantic.Proofs.Scalars

/-!
# Proofs: `Option α` and `α ∣ c` inherit the laws of `α`

* `Option α` is lawful when `α` is and never dumps to `null`, and its schema
  means "null, or `α`" (`nullable_anyOf`).
* `α ∣ c` validates exactly the `α` values satisfying `c`
  (`fromJson_refined_iff`), and is lawful when `α` is and `c` is built with
  `α`'s own instances (`Canonical c`, found automatically).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

variable {α : Type}

/-! ## `Option α` -/

theorem fromJson_option_null [FromJson α] (cfg : Cfg) :
    fromJson (α := Option α) cfg .null = .ok none := rfl

theorem fromJson_option_of_ne_null [FromJson α] (cfg : Cfg) {j : Json} (h : j ≠ .null) :
    fromJson (α := Option α) cfg j = (fromJson cfg j).map some := by
  cases j <;> first | exact absurd rfl h | rfl

/-- The schema of `α | None`: `α`'s with `null` as one more alternative. -/
theorem schema_option [JsonSchema α] :
    JsonSchema.schema (Option α) = (JsonSchema.schema α).nullable := rfl

theorem checkAny_iff : ∀ (alts : List Schema) (j : Json),
    Schema.checkAny alts j = true ↔ ∃ s ∈ alts, s.check j = true
  | [], _ => by simp [Schema.checkAny]
  | s :: ss, j => by simp [Schema.checkAny, checkAny_iff ss j]

theorem check_null (j : Json) : Schema.null.check j = true ↔ j = .null := by
  cases j <;> simp [Schema.check, LeanJson.Json.isNull]

/-- **Nullable schemas**: a value conforms to `α | None`'s schema exactly
when it is `null` or conforms to `α`'s. -/
theorem nullable_anyOf [JsonSchema α] (j : Json) :
    Conforms (JsonSchema.schema (Option α)) j ↔ j = .null ∨ Conforms (JsonSchema.schema α) j := by
  rw [schema_option]
  unfold Conforms Schema.nullable
  split
  · rename_i alts h
    rw [h]
    simp only [Schema.check, checkAny_iff, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨s, hs | rfl, hc⟩
      · exact .inr ⟨s, hs, hc⟩
      · exact .inl ((check_null j).1 hc)
    · rintro (rfl | ⟨s, hs, hc⟩)
      · exact ⟨.null, .inr rfl, (check_null _).2 rfl⟩
      · exact ⟨s, .inl hs, hc⟩
  · simp only [Schema.check, checkAny_iff, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨s, rfl | rfl, hc⟩
      · exact .inr hc
      · exact .inl ((check_null j).1 hc)
    · rintro (rfl | hc)
      · exact ⟨.null, .inr rfl, (check_null _).2 rfl⟩
      · exact ⟨_, .inl rfl, hc⟩

instance [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [NonNull α] :
    LawfulJson (Option α) where
  fromJson_toJson cfg
    | none => rfl
    | some a => by
      show fromJson cfg (toJson DumpOpts.roundTrip a) = _
      rw [fromJson_option_of_ne_null cfg (NonNull.toJson_ne_null _ a), LawfulJson.fromJson_toJson]
      rfl
  schema_sound cfg j a hs h := by
    rw [nullable_anyOf]
    by_cases hj : j = .null
    · exact .inl hj
    · rw [fromJson_option_of_ne_null cfg hj] at h
      cases hv : fromJson (α := α) cfg j with
      | error e => rw [hv] at h; cases h
      | ok v => exact .inr (LawfulJson.schema_sound cfg j v hs hv)
  errors_ne_nil cfg j := by
    by_cases hj : j = .null
    · subst hj; rw [fromJson_option_null]; nofun
    · rw [fromJson_option_of_ne_null cfg hj]
      have := LawfulJson.errors_ne_nil (α := α) cfg j
      cases hv : fromJson (α := α) cfg j <;> simp_all [Except.map]

/-! ## `α ∣ c` -/

section Refined

variable [FromJson α] [Constrained α] (c : Constraint α)

/-- **Refinement**: `α ∣ c` accepts a JSON value exactly when `α` does and
the result satisfies `c`. -/
theorem fromJson_refined_iff (cfg : Cfg) (j : Json) (y : {x : α // c.holds x}) :
    fromJson cfg j = .ok y ↔ fromJson (α := α) cfg j = .ok y.val := by
  show (fromJsonRefined c).fromJson cfg j = _ ↔ _
  unfold fromJsonRefined
  simp only
  split
  · rename_i es h; simp [h]
  · rename_i x h
    rw [h]
    split
    · rename_i hx; constructor
      · intro e; cases e; rfl
      · intro e; cases e; rfl
    · rename_i hx
      split <;> simp <;> (rintro rfl; exact hx y.property)

/-- A refinement's errors are the base type's, or the first failed
constraint's in pydantic's order. -/
theorem fromJson_refined_error (cfg : Cfg) (j : Json) (x : α) (hb : fromJson cfg j = .ok x)
    (hx : ¬ c.holds x) :
    ∃ es, c.validatePy x = .error es ∧
      fromJson (α := {x : α // c.holds x}) cfg j = .error (Constraint.toDetails j cfg.mode es) := by
  obtain ⟨es, he⟩ := (Constraint.validatePy_error_iff c x).2 hx
  refine ⟨es, he, ?_⟩
  show (fromJsonRefined c).fromJson cfg j = _
  unfold fromJsonRefined
  simp only [hb, hx, dite_false, he]

/-- The schema of a refinement is sound for strict validation: `α`'s schema
plus `c`'s keywords. -/
theorem check_withKeywords (s : Schema) (kws : List Keyword) (j : Json) (h : s.check j = true)
    (hk : ∀ k ∈ kws, k.check j = true) : (s.withKeywords kws).check j = true := by
  cases s <;> simp_all [Schema.withKeywords, Schema.check, List.all_eq_true]
  case anyOf ss =>
    rw [checkAny_iff] at h ⊢
    obtain ⟨s, hs, hc⟩ := h
    refine ⟨s.numberWith kws, List.mem_map_of_mem hs, ?_⟩
    cases s <;> simp_all [Schema.numberWith, Schema.check, List.all_eq_true]
  case array =>
    cases j with
    | arr xs => cases xs; simp_all [Schema.check, List.all_eq_true]
    | _ => simp [Schema.check] at h

instance [ToJson α] [JsonSchema α] [LawfulJson α] [LawfulConstrained α] [hc : Canonical c] :
    LawfulJson {x : α // c.holds x} where
  fromJson_toJson cfg y := (fromJson_refined_iff c cfg _ y).2 (LawfulJson.fromJson_toJson cfg y.val)
  schema_sound cfg j y hs h := by
    have hb := (fromJson_refined_iff c cfg j y).1 h
    exact check_withKeywords _ _ j (LawfulJson.schema_sound cfg j y.val hs hb)
      (Constraint.keywordsOf_sound hs hb c hc.std y.property)
  errors_ne_nil cfg j := by
    cases hb : fromJson (α := α) cfg j with
    | error es =>
      show (fromJsonRefined c).fromJson cfg j ≠ _
      unfold fromJsonRefined
      simp only [hb]
      intro e; cases e; exact LawfulJson.errors_ne_nil (α := α) cfg j hb
    | ok x =>
      by_cases hx : c.holds x
      · intro e
        have := (fromJson_refined_iff c cfg j ⟨x, hx⟩).2 hb
        rw [this] at e; cases e
      · obtain ⟨es, he, h⟩ := fromJson_refined_error c cfg j x hb hx
        rw [h]; intro e
        have := Constraint.validate_errors_nonempty c he
        injection e with e
        simp_all [Constraint.toDetails]

end Refined

instance [ToJson α] [NonNull α] (p : α → Prop) : NonNull {x : α // p x} :=
  ⟨fun o x => NonNull.toJson_ne_null o x.val⟩

end LeanPydantic
