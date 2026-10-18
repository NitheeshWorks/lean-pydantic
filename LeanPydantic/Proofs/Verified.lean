import LeanPydantic.APIs.Model
import LeanPydantic.Proofs.Error

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` states a layer's headline properties as fields and
`theVerified<Layer>` fills every one with its proof. A property with no
proof is a compile error the moment it has a field here, so this file is an
honest map of what is verified. `scripts/Axioms.lean` checks every
declaration of the library, these included.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-- Constraints, validated in pydantic's order. -/
structure VerifiedConstraint : Prop where
  /-- Sound and complete: validation returns its input exactly when the
  constraint holds. -/
  validateIff : ∀ (α : Type) (c : Constraint α) (x : α), c.validatePy x = .ok x ↔ c.holds x
  /-- A validated value is the input and satisfies the constraint. -/
  validateSound : ∀ (α : Type) (c : Constraint α) (x y : α), c.validatePy x = .ok y → y = x ∧ c.holds x
  /-- A value satisfying the constraint validates. -/
  validateComplete : ∀ (α : Type) (c : Constraint α) (x : α), c.holds x → c.validatePy x = .ok x
  /-- A failed validation reports an error. -/
  validateErrorsNonempty : ∀ (α : Type) (c : Constraint α) (x : α) es,
    c.validatePy x = .error es → es ≠ []
  /-- A constraint's JSON Schema keywords hold on strictly validated input. -/
  keywordsSound : ∀ (α : Type) [FromJson α] [Constrained α] [LawfulConstrained α] (cfg : Cfg)
    (j : Json) (x : α) (c : Constraint α), cfg.strict = true → fromJson cfg j = .ok x →
      c.AllStd → c.holds x → ∀ k ∈ c.keywordsOf, k.check j = true

/-- Errors: `type`, `ctx` and `msg` agree. -/
structure VerifiedErrors : Prop where
  /-- The message is the type's template rendered from the context. -/
  typeCtxCoherent : ∀ e : ErrorDetails, e.msg = render e.ctx (template e.mode e.type)

/-- Exact numbers. -/
structure VerifiedNumber : Prop where
  /-- A scale-invariant relation reads the same at any common lower exponent. -/
  relAt : ∀ (R : Int → Int → Prop), ScaleInvariant R → ∀ (a b : Number) (E : Int),
    E ≤ min (Num.exp a) (Num.exp b) → (Num.rel R a b ↔ R (Num.keyAt a E) (Num.keyAt b E))
  /-- Numbers relate as the decimals they denote. -/
  relDenotes : ∀ (R : Int → Int → Prop), ScaleInvariant R → ∀ (a b : Number) (d e : Decimal),
    Num.Denotes a d → Num.Denotes b e → (Num.rel R a b ↔ Dec.rel R d e)

/-- `Option α` and `α ∣ c`. -/
structure VerifiedWrappers : Prop where
  /-- The schema of `α | None` means "null, or α". -/
  nullableAnyOf : ∀ (α : Type) [JsonSchema α] (j : Json),
    Conforms (JsonSchema.schema (Option α)) j ↔ j = .null ∨ Conforms (JsonSchema.schema α) j
  /-- A refinement accepts exactly the base type's values satisfying it. -/
  refinedIff : ∀ (α : Type) [FromJson α] [Constrained α] (c : Constraint α) (cfg : Cfg) (j : Json)
    (y : {x : α // c.holds x}), fromJson cfg j = .ok y ↔ fromJson (α := α) cfg j = .ok y.val

/-- Models. -/
structure VerifiedModel : Prop where
  /-- The field combinator preserves the laws. -/
  fieldLawful : ∀ (α β : Type) [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] (name : String)
    (d : Option α) (rest : Fields β), name ∉ rest.keys → rest.Lawful → (Fields.field name d rest).Lawful
  /-- Validating a dump gives the model back. -/
  validateDump : ∀ (α : Type) [Model α] (a : α) (strict : Bool),
    (Model.model_validate α (Model.model_dump a) strict).map (·.val) = .ok a
  /-- Strict validation accepts only what the schema allows. -/
  schemaSound : ∀ (α : Type) [Model α] (obj : Json) (a : α),
    (Model.model_validate α obj (strict := true)).map (·.val) = .ok a → Conforms (JsonSchema.schema α) obj
  /-- Dumps conform to the schema. -/
  dumpConforms : ∀ (α : Type) [Model α] (a : α), Conforms (JsonSchema.schema α) (Model.model_dump a)
  /-- Every error of an object's validation is located under a field. -/
  locPrefix : ∀ (α : Type) [m : Model α] (cfg : Cfg) (kvs : List (String × Json)) es,
    fromJson (α := α) cfg (.obj kvs) = .error es → ∀ e ∈ es, ∃ k ∈ m.fields.keys, ∃ l, e.loc = .key k :: l

theorem theVerifiedConstraint : VerifiedConstraint where
  validateIff _ c x := Keel.Constraint.validatePy_iff c x
  validateSound _ c _ _ h := Keel.Constraint.validate_sound c h
  validateComplete _ c _ h := Keel.Constraint.validate_complete c h
  validateErrorsNonempty _ c _ _ h := Keel.Constraint.validate_errors_nonempty c h
  keywordsSound _ _ _ _ _ _ _ c hs hv hstd h := Keel.Constraint.keywordsOf_sound hs hv c hstd h

theorem theVerifiedErrors : VerifiedErrors where
  typeCtxCoherent := error_type_ctx_coherent

theorem theVerifiedNumber : VerifiedNumber where
  relAt _ hR a b _ hE := Num.rel_at hR a b hE
  relDenotes _ hR _ _ _ _ ha hb := Num.rel_denotes hR ha hb

theorem theVerifiedWrappers : VerifiedWrappers where
  nullableAnyOf _ _ j := nullable_anyOf j
  refinedIff _ _ _ c cfg j y := fromJson_refined_iff c cfg j y

theorem theVerifiedModel : VerifiedModel where
  fieldLawful _ _ _ _ _ _ _ _ _ h hr := Fields.field_lawful h hr
  validateDump _ _ a strict := Model.model_validate_model_dump a strict
  schemaSound _ _ _ _ h := Model.schema_sound h
  dumpConforms _ _ a := Model.model_dump_conforms a
  locPrefix _ _ cfg kvs es h := Model.validate_loc_prefix cfg kvs es h

end LeanPydantic
