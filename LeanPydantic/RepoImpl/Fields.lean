import LeanPydantic.RepoImpl.Scalars

/-!
# RepoImpl: models as a product of fields

A model with fields `f₁ : α₁, …, fₙ : αₙ` is handled through the product
`α₁ × (α₂ × (… × Unit))`. `Fields β` describes how to read a `β` from an
object's members, write it back, and describe it in JSON Schema; it is built
from `Fields.nil` and `Fields.field`, one combinator per field, and the laws
are proved once for each combinator (`Proofs/Fields.lean`). The `deriving
Model` handler only lists the fields; it never writes a proof about one.

Reading follows pydantic's model validator: each field is looked up (the last
member with its name wins, as in a Python `dict`), validated, and its errors
placed under the field's name (Keel's `Validator.at`); a missing field takes
its default or is `missing` (with the whole object as input); every field is
validated and all their errors are reported, in field order
(`Validator.both`); members that name no field are ignored (`extra='ignore'`).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

/-- Python's `str.title()` applied after `replace('_', ' ')`: pydantic's
default field title (`item_id` becomes `Item Id`). Case mapping is ASCII. -/
def fieldTitle (name : String) : String :=
  String.ofList (go false (name.toList.map fun c => if c = '_' then ' ' else c))
where
  go (prevCased : Bool) : List Char → List Char
    | [] => []
    | c :: cs =>
      if c.isAlpha then (if prevCased then c.toLower else c.toUpper) :: go true cs
      else c :: go false cs

/-- How to read, write and describe a product of fields. -/
structure Fields (β : Type) where
  /-- Validate from the members `kvs` of the object `j`. -/
  decode : Cfg → Json → Keel.Validator ErrorDetails (List (String × Json)) β
  encode : DumpOpts → β → List (String × Json)
  keys : List String
  props : List (String × Schema)
  required : List String

namespace Fields

/-- No fields. -/
def nil : Fields Unit where
  decode _ _ _ := .ok ()
  encode _ _ := []
  keys := []
  props := []
  required := []

/-- The validator of one field: its member's value, else its default, else
`missing` (whose input is the whole object `j`). Errors are placed under the
field's name. -/
def member {α : Type} [FromJson α] (cfg : Cfg) (j : Json) (name : String) (default : Option α) :
    Keel.Validator ErrorDetails (List (String × Json)) α :=
  Keel.Validator.at (.key name) fun kvs =>
    match LeanJson.Json.lookupLast name kvs with
    | some v => fromJson cfg v
    | none =>
      match default with
      | some d => .ok d
      | none => .error [{ kind := .missing, input := j, mode := cfg.mode }]

/-- Whether `model_dump` keeps a field whose dumped value is `v`. -/
def keep (opts : DumpOpts) (name : String) (v : Json) (isDefault : Bool) : Bool :=
  !(opts.exclude_none && decide (v = .null)) && !(opts.exclude_defaults && isDefault) &&
    !(decide (name ∈ opts.exclude)) && (match opts.«include» with
      | some ks => decide (name ∈ ks)
      | none => true)

/-- A field `name : α` with an optional default, before the fields `rest`. -/
@[noinline]
def field {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] (name : String) (default : Option α)
    (rest : Fields β) : Fields (α × β) where
  decode cfg j := Keel.Validator.both (member cfg j name default) (rest.decode cfg j)
  encode opts p :=
    let v := toJson opts.nested p.1
    let isDefault := match default with
      | some d => decide (toJson {} p.1 = toJson {} d)
      | none => false
    if keep opts name v isDefault then (name, v) :: rest.encode opts p.2 else rest.encode opts p.2
  keys := name :: rest.keys
  props := (name, .annotated (JsonSchema.schema α) (some (fieldTitle name))
    (default.map (toJson {}))) :: rest.props
  required := if default.isSome then rest.required else name :: rest.required

variable {α β : Type}

/-- The model validator: an object's fields, or `model_type`. -/
def validate (title : String) (F : Fields β) (back : β → α) (cfg : Cfg) (j : Json) :
    Except (List ErrorDetails) α :=
  match j with
  | .obj kvs => (F.decode cfg j kvs).map back
  | _ => .error [{ kind := .modelType title, input := j, mode := cfg.mode }]

/-- The model serialiser. -/
def dump (F : Fields β) (into : α → β) (opts : DumpOpts) (a : α) : Json :=
  .obj (F.encode opts (into a))

/-- The model schema. -/
def schema (title : String) (F : Fields β) : Schema := .object title F.props F.required

end Fields

end LeanPydantic
