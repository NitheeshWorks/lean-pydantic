import LeanPydantic.RepoImpl

/-!
# Specifications: what a schema means, and the laws of a type

* `Conforms s j`: `j` is valid under the JSON Schema `s`.
* `LawfulJson α`: the three laws every supported type satisfies, and that
  `deriving Model` establishes for a structure from its fields' laws:
  validating a dump gives the value back (in either mode, strict or lax); a
  strict validation only accepts input the schema allows; a failed validation
  reports at least one error.
* `NonNull α`: a dump is never `null` (what `Option α` needs to tell `none`
  from `some a`).
* `LawfulConstrained α`: on strictly validated input, the JSON Schema
  keywords of a satisfied atom hold. This is the per-type fact that makes a
  refinement's schema sound.
* `Fields.Lawful F`: the same laws for a product of fields, which the field
  combinators preserve.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-- `j` is valid under the JSON Schema `s`. -/
def Conforms (s : Schema) (j : Json) : Prop := s.check j = true

instance (s : Schema) (j : Json) : Decidable (Conforms s j) :=
  inferInstanceAs (Decidable (_ = true))

/-- The laws of a type's validator, serialiser and schema. -/
class LawfulJson (α : Type) [FromJson α] [ToJson α] [JsonSchema α] : Prop where
  /-- Validating a dump (every field, under its alias) gives the value
  back. -/
  fromJson_toJson : ∀ (cfg : Cfg) (a : α), fromJson cfg (toJson DumpOpts.roundTrip a) = .ok a
  /-- Strict validation accepts only what the schema allows. -/
  schema_sound : ∀ (cfg : Cfg) (j : Json) (a : α),
    cfg.strict = true → fromJson cfg j = .ok a → Conforms (JsonSchema.schema α) j
  /-- A failed validation names at least one error. -/
  errors_ne_nil : ∀ (cfg : Cfg) (j : Json), fromJson (α := α) cfg j ≠ .error []

/-- A dump is never `null`. -/
class NonNull (α : Type) [ToJson α] : Prop where
  toJson_ne_null : ∀ (o : DumpOpts) (a : α), toJson o a ≠ .null

/-- On strictly validated input, a satisfied atom's keywords hold (for atoms
built with the type's own instances). -/
class LawfulConstrained (α : Type) [FromJson α] [Constrained α] : Prop where
  keywords_sound : ∀ (cfg : Cfg) (j : Json) (x : α) (a : Constraint α),
    Constrained.Std a → cfg.strict = true → fromJson cfg j = .ok x → a.holds x →
      ∀ k ∈ Constrained.keywords a, k.check j = true

/-- The laws of a product of fields. -/
structure Fields.Lawful {β : Type} (F : Fields β) : Prop where
  /-- Members that agree with a dump on every field name decode to it. -/
  decode_encode : ∀ (cfg : Cfg) (j : Json) (b : β) (kvs : List (String × Json)),
    (∀ k ∈ F.keys, LeanJson.Json.lookupLast k kvs = LeanJson.Json.lookupLast k (F.encode DumpOpts.roundTrip b)) →
      F.decode cfg j kvs = .ok b
  /-- Every field is read by its key first (then, under `populate_by_name`,
  by its name). -/
  lookups_head : F.lookups.map List.head? = F.keys.map some
  /-- The schema's properties are the fields' keys. -/
  props_keys : F.props.map Prod.fst = F.keys
  /-- A default dump writes every field, in order. -/
  encode_keys : ∀ b : β, (F.encode DumpOpts.roundTrip b).map Prod.fst = F.keys
  /-- A failed decode names at least one error. -/
  ne_nil : ∀ (cfg : Cfg) (j : Json) (kvs : List (String × Json)), F.decode cfg j kvs ≠ .error []
  /-- Every error is located under a field's key (or, for a field read by
  its name under `populate_by_name`, its name). -/
  loc_key : ∀ (cfg : Cfg) (j : Json) (kvs : List (String × Json)) (es : List ErrorDetails),
    F.decode cfg j kvs = .error es → ∀ e ∈ es, ∃ k, (k ∈ F.keys ∨ k ∈ F.names) ∧ ∃ l, e.loc = .key k :: l
  /-- `exclude_unset`: a dump writes only fields counted as set
  (`setFields`, whose names are pydantic's `model_fields_set`), each under
  its name or, by alias, its key. -/
  unset_subset : ∀ (o : DumpOpts) (b : β), o.exclude_unset = true →
    ∀ p ∈ F.encode o b, ∃ q ∈ F.setFields o.set_from o.set_names, p.1 = Fields.dumpKey o.by_alias q
  /-- The fields' names are distinct. -/
  names_nodup : F.names.Nodup
  /-- The fields counted as set are fields, as (name, key). -/
  setFields_sub : ∀ sf ns, ∀ q ∈ F.setFields sf ns, q ∈ F.names.zip F.keys
  /-- A field named like an extra counts as set (pydantic's
  `model_fields_set` holds the extras' keys). -/
  names_set : ∀ sf ns, ∀ q ∈ F.names.zip F.keys, q.1 ∈ ns → q ∈ F.setFields sf ns
  /-- And it writes every field counted as set, when no other option leaves
  one out. -/
  unset_complete : ∀ (o : DumpOpts) (b : β), o.exclude_unset = true → o.«include» = none → o.exclude = [] →
    o.exclude_none = false → o.exclude_defaults = false →
    ∀ q ∈ F.setFields o.set_from o.set_names, ∃ p ∈ F.encode o b, p.1 = Fields.dumpKey o.by_alias q

/-- Every field is read by its key alone (no `populate_by_name`). -/
def Fields.ByKey {β : Type} (F : Fields β) : Prop := F.lookups = F.keys.map ([·])

/-- The schema law of a product of fields, which a field read by its name
(`populate_by_name`) breaks: pydantic's schema lists only its alias. -/
structure Fields.Sound {β : Type} (F : Fields β) : Prop where
  by_key : F.ByKey
  /-- Strictly decoded members satisfy the properties and the required list. -/
  sound : ∀ (cfg : Cfg) (j : Json) (kvs : List (String × Json)) (b : β),
    cfg.strict = true → F.decode cfg j kvs = .ok b →
      Schema.checkProps F.props kvs = true ∧
        ∀ r ∈ F.required, (LeanJson.Json.lookupLast r kvs).isSome = true

end LeanPydantic
