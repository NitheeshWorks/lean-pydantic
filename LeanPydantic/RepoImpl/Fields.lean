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
(`Validator.both`). Members that no field reads follow the model's `extra`
policy (`model_config['extra']`): ignored (`'ignore'`, the default), each an
`extra_forbidden` error after the fields' errors (`'forbid'`), or kept and
dumped after the fields (`'allow'`; a validated value finds them in the input
it remembers, as `exclude_unset` does). Under `populate_by_name` a field with
an alias is read by its alias, else by its name.
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
  /-- Each field's key: its alias, or its name. -/
  keys : List String
  /-- Each field's input keys, in the order they are tried: its key, then,
  under `populate_by_name`, its name. -/
  lookups : List (List String)
  /-- The fields' own names. -/
  names : List String
  props : List (String × Schema)
  required : List String
  /-- The fields counted as set, as (name, key), given the input the value
  was validated from and that input's extras' keys. Their names are
  pydantic's `model_fields_set`. -/
  setFields : Option Json → List String → List (String × String)

namespace Fields

/-- No fields. -/
def nil : Fields Unit where
  decode _ _ _ := .ok ()
  encode _ _ := []
  keys := []
  lookups := []
  names := []
  props := []
  required := []
  setFields _ _ := []

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

/-- The first of `cands` the members have, with its value (the last member
with that key). -/
def lookupFirst (cands : List String) (kvs : List (String × Json)) : Option (String × Json) :=
  match cands with
  | [] => none
  | k :: ks =>
    match LeanJson.Json.lookupLast k kvs with
    | some v => some (k, v)
    | none => lookupFirst ks kvs

/-- One field under `populate_by_name`: read by its alias `key` if the input
has it, else by its `name`; its errors are under the key it was read by, and
`missing` is under the alias. -/
def memberBy {α : Type} [FromJson α] (cfg : Cfg) (j : Json) (key name : String) (default : Option α) :
    Keel.Validator ErrorDetails (List (String × Json)) α := fun kvs =>
  match LeanJson.Json.lookupLast key kvs with
  | some _ => member cfg j key default kvs
  | none =>
    match LeanJson.Json.lookupLast name kvs with
    | some _ => member cfg j name default kvs
    | none => member cfg j key default kvs

/-- Whether `model_dump` keeps the field `name` whose dumped value is `v`. -/
def keep (opts : DumpOpts) (name : String) (v : Json) (isDefault isSet : Bool) : Bool :=
  !(opts.exclude_none && decide (v = .null)) && !(opts.exclude_defaults && isDefault) &&
    !(opts.exclude_unset && !isSet) &&
    !(decide (name ∈ opts.exclude)) && (match opts.«include» with
      | some ks => decide (name ∈ ks)
      | none => true)

/-- The member named `key` of the input a value was validated from. -/
def setMember (set_from : Option Json) (key : String) : Option Json :=
  match set_from with
  | some (.obj ⟨kvs⟩) => LeanJson.Json.lookupLast key kvs
  | _ => none

/-- Whether the field under `key` was set in that input (every field is, when
the input is unknown). -/
def wasSet (set_from : Option Json) (key : String) : Bool :=
  match set_from with
  | some (.obj ⟨kvs⟩) => (LeanJson.Json.lookupLast key kvs).isSome
  | _ => true

/-- Whether a field counts as set (in pydantic's `model_fields_set`): the
input had one of its keys `cs`, or an extra named `name`. Every field is set
when the input is unknown. -/
def isSet (set_from : Option Json) (set_names : List String) (cs : List String) (name : String) : Bool :=
  cs.any (wasSet set_from) || decide (name ∈ set_names)

/-- A field `name : α`, validated under `alias` when it has one (pydantic's
`Field(alias=…)`), and also under `name` when `byName` (`populate_by_name`),
with an optional default, before the fields `rest`. -/
@[noinline]
def field {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (default : Option α) (rest : Fields β) (factory : Bool := false) (byName : Bool := false) :
    Fields (α × β) :=
  let key := alias.getD name
  { decode := fun cfg j => Keel.Validator.both
      (if byName then memberBy cfg j key name default else member cfg j key default) (rest.decode cfg j)
    encode := fun opts p =>
      let setKey := if byName && (setMember opts.set_from key).isNone then name else key
      let v := toJson (opts.nested (setMember opts.set_from setKey)) p.1
      let isDefault := match default with
        | some d => decide (toJson { serializers := false } p.1 = toJson { serializers := false } d)
        | none => false
      let rest' := rest.encode opts p.2
      if keep opts name v isDefault (isSet opts.set_from opts.set_names (if byName then [key, name] else [key]) name) then
        ((if opts.by_alias then key else name), v) :: rest'
      else rest'
    keys := key :: rest.keys
    lookups := (if byName then [key, name] else [key]) :: rest.lookups
    names := name :: rest.names
    props := (key, .annotated (JsonSchema.schema α)
      (if (JsonSchema.schema α).wantsTitle then some (fieldTitle key) else none)
      (if factory then none else default.map (toJson { serializers := false }))) :: rest.props
    required := if default.isSome then rest.required else key :: rest.required
    setFields := fun sf ns =>
      (if isSet sf ns (if byName then [key, name] else [key]) name then [(name, key)] else []) ++ rest.setFields sf ns }

variable {α β : Type}

/-- The input keys the fields read: for each field, the first of its keys the
members have. -/
def consumed (F : Fields β) (kvs : List (String × Json)) : List String :=
  F.lookups.filterMap fun cs => (lookupFirst cs kvs).map Prod.fst

/-- The input keys that are not extras. pydantic-core differs by input mode:
from Python objects, the keys the fields read; from JSON text, every field's
key and every field's name, read or not (so there a field's name is never an
extra, even when the field is read only by its alias). -/
def accepted (F : Fields β) : InputMode → List (String × Json) → List String
  | .python, kvs => F.consumed kvs
  | .json, _ => F.keys ++ F.names

/-- The keys accepted whenever the input has them: the fields' keys from
Python objects (without `populate_by_name`), and also their names from JSON
text. -/
def acceptedNames (F : Fields β) : InputMode → List String
  | .python => F.keys
  | .json => F.keys ++ F.names

/-- The members that are extras, in input order. -/
def extras (F : Fields β) (mode : InputMode) (kvs : List (String × Json)) : List (String × Json) :=
  kvs.filter fun kv => !decide (kv.1 ∈ F.accepted mode kvs)

/-- `extra='forbid'`: an `extra_forbidden` error for each extra, under its
key, with its value as input. -/
def forbidExtras (cfg : Cfg) (F : Fields β) : Keel.Validator ErrorDetails (List (String × Json)) Unit :=
  fun kvs =>
    match F.extras cfg.mode kvs with
    | [] => .ok ()
    | es => .error (es.map fun kv => { kind := .extraForbidden, loc := [.key kv.1], input := kv.2, mode := cfg.mode })

/-- The model validator: an object's fields (and, under `forbid`, no extras),
or `model_type`. pydantic-core reports the extras after the fields' errors
for Python input, and before them for JSON input. -/
def validate (title : String) (extra : Extra) (F : Fields β) (back : β → α) (cfg : Cfg) (j : Json) :
    Except (List ErrorDetails) α :=
  match j with
  | .obj ⟨kvs⟩ =>
    match extra with
    | .forbid =>
      match cfg.mode with
      | .python => (Keel.Validator.both (F.decode cfg j) (forbidExtras cfg F) kvs).map (fun p => back p.1)
      | .json => (Keel.Validator.both (forbidExtras cfg F) (F.decode cfg j) kvs).map (fun p => back p.2)
    | _ => (F.decode cfg j kvs).map back
  | _ =>
    let kind := if cfg.from_attributes && cfg.mode = .python then .modelAttributesType else .modelType title
    .error [{ kind, input := j, mode := cfg.mode }]

/-- Whether `model_dump` keeps an extra member: `include`, `exclude` and
`exclude_none` apply to it, `exclude_defaults` and `exclude_unset` do not (it
has no default, and it was set). -/
def keepExtra (opts : DumpOpts) (kv : String × Json) : Bool :=
  !(opts.exclude_none && decide (kv.2 = .null)) && !(decide (kv.1 ∈ opts.exclude)) &&
    (match opts.«include» with
      | some ks => decide (kv.1 ∈ ks)
      | none => true)

/-- The extras a dump writes under `extra='allow'`: those of the input the
value was validated from, as a Python `dict` holds them (first position, last
value), as they came. A value with no input has none. -/
def extraDump (F : Fields β) (opts : DumpOpts) : List (String × Json) :=
  match opts.set_from with
  | some (.obj ⟨kvs⟩) => (dedup (F.extras opts.set_mode kvs)).filter (keepExtra opts)
  | _ => []

/-- The extras' keys of the input `set_from` (each once), under `allow`. -/
def extraKeys (extra : Extra) (F : Fields β) (set_from : Option Json) (mode : InputMode) : List String :=
  if extra = .allow then
    match set_from with
    | some (.obj ⟨kvs⟩) => (dedup (F.extras mode kvs)).map Prod.fst
    | _ => []
  else []

/-- pydantic's `model_fields_set`: the names of the fields counted as set,
then (under `allow`) the extras' keys, each once. -/
def fieldsSet (extra : Extra) (F : Fields β) (set_from : Option Json) (mode : InputMode) : List String :=
  let ex := F.extraKeys extra set_from mode
  let ns := (F.setFields set_from ex).map Prod.fst
  ns ++ ex.filter (fun k => !ns.contains k)

/-- The key a field (name, key) is dumped under. -/
def dumpKey (by_alias : Bool) (q : String × String) : String := if by_alias then q.2 else q.1

/-- The model serialiser: the fields, then (under `allow`) the extras. An
extra named like a field marks that field as set. -/
def dump (extra : Extra) (F : Fields β) (into : α → β) (opts : DumpOpts) (a : α) : Json :=
  .obj ⟨F.encode { opts with set_names := F.extraKeys extra opts.set_from opts.set_mode } (into a) ++
    (if extra = .allow then F.extraDump opts else [])⟩

/-- The model schema: a reference, named by the model's title, to its object
schema (pydantic puts every model under `$defs`; a document for the model
itself is the object, with the others under `$defs`). -/
def schema (title : String) (extra : Extra) (F : Fields β) : Schema :=
  .ref title (.object title F.props F.required extra)

end Fields

end LeanPydantic
