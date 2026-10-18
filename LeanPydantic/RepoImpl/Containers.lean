import LeanPydantic.RepoImpl.Fields

/-!
# RepoImpl: containers

| Lean | pydantic | schema |
|---|---|---|
| `List α` | `list[α]` | `{"items": α, "type": "array"}` |
| `Dict α` | `dict[str, α]` | `{"additionalProperties": α, "type": "object"}` |
| `List α ∣ minLength n` | `Annotated[list[α], Field(min_length=n)]` | `minItems` |

A list validates every element, each under its index (Keel's
`Validator.each`), and reports every element's errors; a dict validates
every value under its key. Object members are first collapsed as a Python
`dict` collapses them (`dedup`: one entry per key, at the key's first
position, with its last value).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-! ## `list[α]` -/

/-- The element of a list input at index `i`. -/
def elemFrom (set_from : Option Json) (i : Nat) : Option Json :=
  match set_from with
  | some (.arr ⟨xs⟩) => xs[i]?
  | _ => none

/-- Dump the elements from index `i`. -/
def dumpElems {α : Type} [ToJson α] (o : DumpOpts) : Nat → List α → List Json
  | _, [] => []
  | i, x :: xs => toJson (o.nested (elemFrom o.set_from i)) x :: dumpElems o (i + 1) xs

instance fromJsonList {α : Type} [FromJson α] : FromJson (List α) where
  title := "list[" ++ FromJson.title α ++ "]"
  fromJson cfg
    | .arr ⟨xs⟩ => Keel.Validator.each (fromJson cfg) xs
    | j => .error [{ kind := .listType, input := j, mode := cfg.mode }]

instance toJsonList {α : Type} [ToJson α] : ToJson (List α) := ⟨fun o xs => .arr ⟨dumpElems o 0 xs⟩⟩

instance {α : Type} [JsonSchema α] : JsonSchema (List α) := ⟨.array (JsonSchema.schema α) []⟩

/-- A list's lengths: `too_short` / `too_long` with `field_type: List`, and
`minItems` / `maxItems`. -/
instance constrainedList {β : Type} : Constrained (List β) where
  error
    | @Constraint.minLength _ _ n, x => .tooShort "List" n x.length
    | @Constraint.maxLength _ _ n, x => .tooLong "List" n x.length
    | _, _ => unsupportedError
  keywords
    | @Constraint.minLength _ _ n => [.minItems n]
    | @Constraint.maxLength _ _ n => [.maxItems n]
    | _ => []
  Std
    | @Constraint.minLength _ i _ | @Constraint.maxLength _ i _ => i = Keel.instSizedList
    | _ => True

instance {β : Type} (n : Nat) : Canonical (Constraint.minLength n : Constraint (List β)) := ⟨rfl⟩
instance {β : Type} (n : Nat) : Canonical (Constraint.maxLength n : Constraint (List β)) := ⟨rfl⟩

/-! ## `dict[str, α]` -/

/-- A string-keyed dictionary, in insertion order, each key once. -/
structure Dict (α : Type) where
  entries : List (String × α)
  nodup : (entries.map Prod.fst).Nodup

/-- The value under `k`. -/
def Dict.get? {α : Type} (d : Dict α) (k : String) : Option α := d.entries.lookup k

/-- Validate the members, each under its key, reporting every member's errors. -/
def validateMembers {α : Type} [FromJson α] (cfg : Cfg) :
    List (String × Json) → Except (List ErrorDetails) (List (String × α))
  | [] => .ok []
  | (k, v) :: kvs =>
    match (Keel.Validator.at (.key k) (fromJson cfg)) v, validateMembers cfg kvs with
    | .ok a, .ok as => .ok ((k, a) :: as)
    | .error e, .ok _ => .error e
    | .ok _, .error e => .error e
    | .error e₁, .error e₂ => .error (e₁ ++ e₂)

/-- The validated members as a dictionary (the keys were already distinct). -/
def Dict.ofEntries {α : Type} (kvs : List (String × α)) : Dict α :=
  if h : (kvs.map Prod.fst).Nodup then ⟨kvs, h⟩ else ⟨[], List.nodup_nil⟩

instance fromJsonDict {α : Type} [FromJson α] : FromJson (Dict α) where
  title := "dict[str," ++ FromJson.title α ++ "]"
  fromJson cfg
    | .obj ⟨kvs⟩ => (validateMembers cfg (dedup kvs)).map Dict.ofEntries
    | j => .error [{ kind := .dictType, input := j, mode := cfg.mode }]

/-- Dump the members. -/
def dumpMembers {α : Type} [ToJson α] (o : DumpOpts) : List (String × α) → List (String × Json)
  | [] => []
  | (k, v) :: kvs => (k, toJson (o.nested (Fields.setMember o.set_from k)) v) :: dumpMembers o kvs

instance toJsonDict {α : Type} [ToJson α] : ToJson (Dict α) := ⟨fun o d => .obj ⟨dumpMembers o d.entries⟩⟩

instance {α : Type} [JsonSchema α] : JsonSchema (Dict α) := ⟨.dict (JsonSchema.schema α)⟩

end LeanPydantic

namespace LeanPydantic

/-- The empty dictionary, `{}`. -/
instance {α : Type} : EmptyCollection (Dict α) := ⟨⟨[], List.nodup_nil⟩⟩

end LeanPydantic
