import LeanPydantic.RepoImpl.Fields
import LeanPydantic.RepoImpl.Nodup
import LeanPydantic.RepoImpl.Dedup

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

Every pass over a dict's members is linear in their number and runs in
constant stack: duplicates collapse through lean-json's hash index
(`dedupIdx`, proved equal to `dedup`), members validate in a tail
loop (`validateMembersFast`, proved equal to `validateMembers`), and the
keys' distinctness is known from the collapse (`dedupIdx_nodup`), so the
validated keys are compared once, in order, with the collapsed ones. A body with 100 000 keys is not a denial of service.
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
    | @Constraint.maxLength _ _ n, x => .tooLong "List" n (some x.length)
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

/-- `validateMembers` as a tail loop: the members validated so far (in
reverse), the errors so far (chunks in reverse), and whether any failed. -/
def validateMembersGo {α : Type} [FromJson α] (cfg : Cfg) :
    List (String × Json) → List (String × α) → List (List ErrorDetails) → Bool →
      Except (List ErrorDetails) (List (String × α))
  | [], oks, errs, failed => if failed then .error errs.reverse.flatten else .ok oks.reverse
  | (k, v) :: kvs, oks, errs, failed =>
    match (Keel.Validator.at (.key k) (fromJson cfg)) v with
    | .ok a => validateMembersGo cfg kvs ((k, a) :: oks) errs failed
    | .error e => validateMembersGo cfg kvs oks (e :: errs) true

/-- `validateMembers`, in constant stack (`validateMembersFast_eq`). -/
def validateMembersFast {α : Type} [FromJson α] (cfg : Cfg) (kvs : List (String × Json)) :
    Except (List ErrorDetails) (List (String × α)) :=
  validateMembersGo cfg kvs [] [] false

/-- `dedup` on JSON members, through a hash index sized up front. -/
def dedupFast (kvs : List (String × Json)) : List (String × Json) := dedupIdx kvs

/-- The validated members as a dictionary (the keys were already distinct;
checked in linear time). -/
def Dict.ofEntries {α : Type} (kvs : List (String × α)) : Dict α :=
  if h : nodupFast (kvs.map Prod.fst) = true then ⟨kvs, (nodupFast_iff _).1 h⟩ else ⟨[], List.nodup_nil⟩

/-- `Dict.ofEntries` when the keys are known to be `keys`, already distinct:
then one sequential comparison replaces the hash pass. -/
def Dict.ofChecked {α : Type} (keys : List String) (hk : keys.Nodup) (kvs : List (String × α)) : Dict α :=
  if h : kvs.map Prod.fst = keys then ⟨kvs, h ▸ hk⟩ else Dict.ofEntries kvs

theorem Dict.ofChecked_eq {α : Type} (keys : List String) (hk : keys.Nodup) (kvs : List (String × α)) :
    Dict.ofChecked keys hk kvs = Dict.ofEntries kvs := by
  unfold Dict.ofChecked
  split
  · rename_i h
    have hn : nodupFast (kvs.map Prod.fst) = true := (nodupFast_iff _).2 (h ▸ hk)
    simp [Dict.ofEntries, hn]
  · rfl

instance fromJsonDict {α : Type} [FromJson α] : FromJson (Dict α) where
  title := "dict[str," ++ FromJson.title α ++ "]"
  fromJson cfg
    | .obj ⟨kvs⟩ =>
      (validateMembersFast cfg (dedupFast kvs)).map
        (Dict.ofChecked ((dedupFast kvs).map Prod.fst) (dedupIdx_nodup kvs))
    | j => .error [{ kind := .dictType, input := j, mode := cfg.mode }]

/-- Dump the members. -/
def dumpMembers {α : Type} [ToJson α] (o : DumpOpts) (kvs : List (String × α)) : List (String × Json) :=
  kvs.map fun kv => (kv.1, toJson (o.nested (Fields.setMember o.set_from kv.1)) kv.2)

instance toJsonDict {α : Type} [ToJson α] : ToJson (Dict α) := ⟨fun o d => .obj ⟨dumpMembers o d.entries⟩⟩

instance {α : Type} [JsonSchema α] : JsonSchema (Dict α) := ⟨.dict (JsonSchema.schema α)⟩

end LeanPydantic

namespace LeanPydantic

/-- The empty dictionary, `{}`. -/
instance {α : Type} : EmptyCollection (Dict α) := ⟨⟨[], List.nodup_nil⟩⟩

end LeanPydantic

namespace LeanPydantic

open LeanJson (Json)
open Keel (Constraint)

/-! ## `set[α]` -/

/-- `set[α]`: distinct elements, in first-occurrence order. Python iterates a
set in hash order, which a dump cannot reproduce in general (for strings it
changes from run to run); lean-pydantic dumps in input order. pydantic's
schema says `uniqueItems: true` while it accepts and collapses duplicates,
also strictly (UP-054), so a set has no `LawfulJson` instance. -/
structure PySet (α : Type) where
  elems : List α
  nodup : elems.Nodup

/-- The first occurrence of each element, in order, in one pass with a hash
set of the elements seen. -/
def firstOccurrences {α : Type} [BEq α] [Hashable α] (xs : List α) : List α :=
  go (Std.HashSet.emptyWithCapacity xs.length) [] xs
where
  /-- Seen so far, kept so far (reversed), the rest. -/
  go (seen : Std.HashSet α) (acc : List α) : List α → List α
    | [] => acc.reverse
    | x :: xs => if seen.contains x then go seen acc xs else go (seen.insert x) (x :: acc) xs

/-- A set of the elements (each once; distinctness decided in linear time). -/
def PySet.ofList {α : Type} [DecidableEq α] [Hashable α] [LawfulHashable α] (xs : List α) : PySet α :=
  let ys := firstOccurrences xs
  if h : nodupFast ys = true then ⟨ys, (nodupFast_iff _).1 h⟩ else ⟨[], List.nodup_nil⟩

instance {α : Type} [FromJson α] [DecidableEq α] [Hashable α] [LawfulHashable α] : FromJson (PySet α) where
  title := "set[" ++ FromJson.title α ++ "]"
  fromJson cfg j :=
    let err : Except (List ErrorDetails) (PySet α) := .error [{ kind := .setType, input := j, mode := cfg.mode }]
    match j with
    | .arr ⟨xs⟩ =>
      -- strict Python wants a `set` object, which no JSON value is
      if cfg.strict && cfg.mode = .python then err
      else (Keel.Validator.each (fromJson cfg) xs).map PySet.ofList
    | _ => err

instance {α : Type} [ToJson α] : ToJson (PySet α) := ⟨fun o s => toJson o s.elems⟩
instance {α : Type} [JsonSchema α] : JsonSchema (PySet α) :=
  ⟨.array (JsonSchema.schema α) [.uniqueItems]⟩
instance {α : Type} : Keel.Sized (PySet α) := ⟨fun s => s.elems.length⟩
instance {α : Type} : EmptyCollection (PySet α) := ⟨⟨[], List.nodup_nil⟩⟩

/-- A set's lengths: `too_short` / `too_long` with `field_type: Set`. -/
instance {β : Type} : Constrained (PySet β) where
  error
    | @Constraint.minLength _ _ n, x => .tooShort "Set" n x.elems.length
    | @Constraint.maxLength _ _ n, _ => .tooLong "Set" n none
    | _, _ => unsupportedError
  keywords
    | @Constraint.minLength _ _ n => [.minItems n]
    | @Constraint.maxLength _ _ n => [.maxItems n]
    | _ => []
  Std _ := True

end LeanPydantic
