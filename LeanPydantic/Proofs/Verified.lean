import LeanPydantic.APIs.Model
import LeanPydantic.Proofs.Error
import LeanPydantic.Proofs.Regex
import LeanPydantic.Proofs.Complete
import LeanPydantic.Proofs.Choice
import LeanPydantic.Proofs.Containers

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
    (alias : Option String) (d : Option α) (rest : Fields β), alias.getD name ∉ rest.keys →
      rest.Lawful → (Fields.field name alias d rest).Lawful
  /-- Validating a dump by alias gives the model back (`alias_roundtrip`). -/
  validateDump : ∀ (α : Type) [Model α] [LawfulModel α] (a : α) (strict : Bool),
    (Model.model_validate α (Model.model_dump a (by_alias := true)) strict).map (·.val) = .ok a
  /-- Strict validation accepts only what the schema allows. -/
  schemaSound : ∀ (α : Type) [Model α] [LawfulModel α] (obj : Json) (a : α),
    (Model.model_validate α obj (strict := true)).map (·.val) = .ok a → Conforms (JsonSchema.schema α) obj
  /-- Dumps conform to the schema. -/
  dumpConforms : ∀ (α : Type) [Model α] [LawfulModel α] (a : α),
    Conforms (JsonSchema.schema α) (Model.model_dump a (by_alias := true))
  /-- Every error of an object's validation is located under a field. -/
  locPrefix : ∀ (α : Type) [m : Model α] [LawfulModel α] (cfg : Cfg) (kvs : List (String × Json)) es,
    fromJson (α := α) cfg (.obj ⟨kvs⟩) = .error es → ∀ e ∈ es, ∃ k ∈ m.fields.keys, ∃ l, e.loc = .key k :: l

/-- `pattern`: the matcher, its correctness and its bound. -/
structure VerifiedRegex : Prop where
  /-- `derive_correct`: partial derivatives finish exactly the matches that
  start with the character read. -/
  deriveCorrect : ∀ (r : Regex.Regex) (p : Option Char) (c : Char) (u : List Char) (n : Option Char),
    r.Matches p (c :: u) n ↔ ∃ q ∈ Regex.Regex.pd p c r, q.Matches (some c) u n
  /-- The scan decides the unanchored search (Rust's `is_match`). -/
  searchCorrect : ∀ (r : Regex.Regex) (s : String), r.search s = true ↔ r.Search s.toList
  /-- The lazy DFA that patterns run is the scan, transition caching and all. -/
  dfaEq : ∀ (r : Regex.Regex) (s : String), r.searchDfa s = r.search s
  /-- A compiled pattern tests exactly that search. -/
  patternTest : ∀ (src : String) (r : Regex.Regex), Regex.compile src = .ok r →
    ∀ s, (Regex.ofSource src).test s = true ↔ r.Search s.toList
  /-- Linear time: every state the scan reaches has at most one term per
  character class of the pattern, plus one. -/
  stateBound : ∀ (r : Regex.Regex) (T : List Regex.Regex) (p : Option Char) (c : Char),
    r.Reach T → r.Reach (Regex.Regex.next r p c T) ∧ T.length ≤ r.leaves + 1

/-- The m2 surface: containers, choices, `exclude_unset`, completeness. -/
structure VerifiedSurface : Prop where
  /-- Lists, dicts and tuples of lawful types are lawful (round trip,
  strict soundness against the schema, non-empty errors). -/
  listLawful : ∀ (α : Type) [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α], LawfulJson (List α)
  dictLawful : ∀ (α : Type) [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α], LawfulJson (Dict α)
  tupleLawful : ∀ (α β : Type) [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [TupleItems β]
    [LawfulTupleItems β], LawfulJson (α × β)
  /-- `Literal[...]` of a lawful type is lawful. -/
  literalLawful : ∀ (α : Type) [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [DecidableEq α]
    (cs : List α), LawfulJson {x : α // (Constraint.oneOf cs).holds x}
  /-- A derived enumeration is lawful. -/
  enumLawful : ∀ (α : Type) [Enumeration α] [LawfulEnumeration α], LawfulJson α
  /-- `union_smart_leftmost`: an exact strict match of the leftmost choice wins. -/
  unionSmartLeftmost : ∀ (α β : Type) [FromJson α] [ToJson α] [JsonSchema α] [Choices β] (cfg : Cfg)
    (j : Json) (a : α), fromJson (α := α) cfg.strictly j = .ok a → FromJson.exact α j = true →
      fromJson (α := α ⊕ β) cfg j = .ok (.inl a)
  /-- With no exact match, the leftmost strict match wins. -/
  unionSmartStrict : ∀ (α β : Type) [FromJson α] [ToJson α] [JsonSchema α] [Choices β] (cfg : Cfg)
    (j : Json) (a : α), Choices.exactly (τ := α ⊕ β) cfg j = none →
      fromJson (α := α) cfg.strictly j = .ok a → fromJson (α := α ⊕ β) cfg j = .ok (.inl a)
  /-- `exclude_unset_subset`: an `exclude_unset` dump writes only fields set in the input. -/
  excludeUnsetSubset : ∀ (α : Type) [Model α] [LawfulModel α] (a : α) (j : Json),
    ∃ kvs, Model.model_dump a (by_alias := true) (exclude_unset := true) (set_from := some j) = .obj ⟨kvs⟩ ∧
      ∀ p ∈ kvs, Fields.wasSet (some j) p.1 = true
  /-- The same, in the form users call: a validated model remembers its
  input, so no `set_from` is passed (`Valid.exclude_unset_subset`). -/
  validExcludeUnsetSubset : ∀ (α : Type) [Model α] [LawfulModel α] (cfg : Cfg) (obj : Json) (v : Valid α cfg obj),
    ∃ kvs, v.model_dump (by_alias := true) (exclude_unset := true) = .obj ⟨kvs⟩ ∧
      ∀ p ∈ kvs, Fields.wasSet (some obj) p.1 = true
  /-- `schema_complete` for scalars: every input their schema allows validates. -/
  completeBool : ∀ cfg, SchemaComplete Bool cfg
  completeString : ∀ cfg, SchemaComplete String cfg
  completeFloat : ∀ cfg : Cfg, cfg.mode = .json → SchemaComplete Float cfg
  completeOption : ∀ (α : Type) [FromJson α] [JsonSchema α] (cfg : Cfg),
    SchemaComplete α cfg → SchemaComplete (Option α) cfg

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
  fieldLawful _ _ _ _ _ _ _ _ _ _ h hr := Fields.field_lawful h hr
  validateDump _ _ _ a strict := Model.model_validate_model_dump a strict
  schemaSound _ _ _ _ _ h := Model.schema_sound h
  dumpConforms _ _ _ a := Model.model_dump_conforms a
  locPrefix _ _ _ cfg kvs es h := Model.validate_loc_prefix cfg kvs es h

theorem theVerifiedSurface : VerifiedSurface where
  listLawful _ _ _ _ _ := inferInstance
  dictLawful _ _ _ _ _ := inferInstance
  tupleLawful _ _ _ _ _ _ _ _ := inferInstance
  literalLawful _ _ _ _ _ _ _ := inferInstance
  enumLawful _ _ _ := inferInstance
  unionSmartLeftmost _ _ _ _ _ _ cfg j a h hx := union_smart_leftmost cfg j a h hx
  unionSmartStrict _ _ _ _ _ _ cfg j a hn h := union_smart_strict cfg j a hn h
  excludeUnsetSubset _ _ _ a j := Model.exclude_unset_subset a j
  validExcludeUnsetSubset _ _ _ _ _ v := Valid.exclude_unset_subset v
  completeBool := schema_complete_bool
  completeString := schema_complete_string
  completeFloat := schema_complete_float
  completeOption _ _ _ cfg h := schema_complete_option cfg h

theorem theVerifiedRegex : VerifiedRegex where
  deriveCorrect r p c u n := Regex.Regex.derive_correct p c r u n
  searchCorrect := Regex.Regex.search_correct
  dfaEq := Regex.Regex.searchDfa_eq
  patternTest _ _ h s := Regex.ofSource_test h s
  stateBound _ _ p c h := ⟨Regex.Regex.reach_next p c h, Regex.Regex.reach_length_le h⟩

end LeanPydantic
