import LeanPydantic.RepoImpl.Choice

/-!
# RepoImpl: validators and serializers

pydantic's functional validators and serializers, as types:

| pydantic | lean-pydantic |
|---|---|
| `Annotated[T, AfterValidator(f)]` | `After T f`, `f : T → Except String T` |
| `Annotated[T, BeforeValidator(f)]` | `Before T f`, `f : Json → Except String Json` |
| `Annotated[T, WrapValidator(f)]` | `Wrap T f`, `f : Handler T → Json → Except Raise T` |
| `Annotated[T, PlainSerializer(g)]` | `Serialize T g`, `g : T → Json` |
| `Annotated[T, WrapSerializer(g)]` | `WrapSerialize T g`, `g : (T → Json) → T → Json` |

A validator's `.error msg` is pydantic's `raise ValueError(msg)`: a
`value_error` at the field, with the field's input. On a model type they are
pydantic's `model_validator` and `model_serializer`; on a field type,
`field_validator` and `field_serializer`.

Each is a `def` equal to `T`, so it has instances of its own; `OfNat`,
`Repr`, `DecidableEq` and `Inhabited` are `T`'s. Their round trip is not a
law in general (a validator may reject or rewrite what `T` dumps): they are
tested, not proved (`tests/Props.lean`, `tests/Conformance.lean`).
-/

namespace LeanPydantic

open LeanJson (Json)

/-- `Annotated[α, AfterValidator(f)]`: `α`'s validation, then `f`. -/
def After (α : Type) (_f : α → Except String α) : Type := α

/-- `Annotated[α, BeforeValidator(f)]`: `f` on the input, then `α`'s
validation. -/
def Before (α : Type) (_f : Json → Except String Json) : Type := α

/-- What a wrap validator calls: `α`'s own validation. -/
abbrev Handler (α : Type) := Json → Except (List ErrorDetails) α

/-- What a wrap validator raises: a `ValueError`, or the handler's errors. -/
inductive Raise where
  | value (msg : String)
  | errors (es : List ErrorDetails)

/-- `Annotated[α, WrapValidator(f)]`: `f` given the input and `α`'s
validation as its handler. -/
def Wrap (α : Type) (_f : Handler α → Json → Except Raise α) : Type := α

/-- `Annotated[α, PlainSerializer(g)]`: dumps with `g`. -/
def Serialize (α : Type) (_g : α → Json) : Type := α

/-- `Annotated[α, WrapSerializer(g)]`: dumps with `g`, given `α`'s own dump. -/
def WrapSerialize (α : Type) (_g : (α → Json) → α → Json) : Type := α

/-- pydantic's `ValueError(msg)` for the input `j`. -/
def valueError (cfg : Cfg) (j : Json) (msg : String) : List ErrorDetails :=
  [{ kind := .valueError msg, input := j, mode := cfg.mode }]

variable {α : Type}

section After
variable {f : α → Except String α}
instance [FromJson α] : FromJson (After α f) where
  title := FromJson.title α
  fromJson cfg j := do
    let a ← FromJson.fromJson (α := α) cfg j
    match f a with
    | .ok b => pure b
    | .error m => throw (valueError cfg j m)
  exact := FromJson.exact (α := α)
instance [ToJson α] : ToJson (After α f) := inferInstanceAs (ToJson α)
instance [JsonSchema α] : JsonSchema (After α f) := inferInstanceAs (JsonSchema α)
instance [Repr α] : Repr (After α f) := inferInstanceAs (Repr α)
instance [DecidableEq α] : DecidableEq (After α f) := inferInstanceAs (DecidableEq α)
instance [Inhabited α] : Inhabited (After α f) := inferInstanceAs (Inhabited α)
instance {n : Nat} [OfNat α n] : OfNat (After α f) n := inferInstanceAs (OfNat α n)
end After

section Before
variable {f : Json → Except String Json}
instance [FromJson α] : FromJson (Before α f) where
  title := FromJson.title α
  fromJson cfg j :=
    match f j with
    | .ok j' => FromJson.fromJson (α := α) cfg j'
    | .error m => .error (valueError cfg j m)
  exact j := match f j with
    | .ok j' => FromJson.exact (α := α) j'
    | .error _ => false
instance [ToJson α] : ToJson (Before α f) := inferInstanceAs (ToJson α)
instance [JsonSchema α] : JsonSchema (Before α f) := inferInstanceAs (JsonSchema α)
instance [Repr α] : Repr (Before α f) := inferInstanceAs (Repr α)
instance [DecidableEq α] : DecidableEq (Before α f) := inferInstanceAs (DecidableEq α)
instance [Inhabited α] : Inhabited (Before α f) := inferInstanceAs (Inhabited α)
instance {n : Nat} [OfNat α n] : OfNat (Before α f) n := inferInstanceAs (OfNat α n)
end Before

section Wrap
variable {f : Handler α → Json → Except Raise α}
instance [FromJson α] : FromJson (Wrap α f) where
  title := FromJson.title α
  fromJson cfg j :=
    match f (FromJson.fromJson cfg) j with
    | .ok a => .ok a
    | .error (.value m) => .error (valueError cfg j m)
    | .error (.errors es) => .error es
  exact := FromJson.exact (α := α)
instance [ToJson α] : ToJson (Wrap α f) := inferInstanceAs (ToJson α)
instance [JsonSchema α] : JsonSchema (Wrap α f) := inferInstanceAs (JsonSchema α)
instance [Repr α] : Repr (Wrap α f) := inferInstanceAs (Repr α)
instance [DecidableEq α] : DecidableEq (Wrap α f) := inferInstanceAs (DecidableEq α)
instance [Inhabited α] : Inhabited (Wrap α f) := inferInstanceAs (Inhabited α)
instance {n : Nat} [OfNat α n] : OfNat (Wrap α f) n := inferInstanceAs (OfNat α n)
end Wrap

section Serialize
variable {g : α → Json}
instance [FromJson α] : FromJson (Serialize α g) := inferInstanceAs (FromJson α)
instance [ToJson α] : ToJson (Serialize α g) where
  toJson opts a := if opts.serializers then g a else toJson opts (show α from a)
instance [JsonSchema α] : JsonSchema (Serialize α g) := inferInstanceAs (JsonSchema α)
instance [Repr α] : Repr (Serialize α g) := inferInstanceAs (Repr α)
instance [DecidableEq α] : DecidableEq (Serialize α g) := inferInstanceAs (DecidableEq α)
instance [Inhabited α] : Inhabited (Serialize α g) := inferInstanceAs (Inhabited α)
instance {n : Nat} [OfNat α n] : OfNat (Serialize α g) n := inferInstanceAs (OfNat α n)
end Serialize

section WrapSerialize
variable {g : (α → Json) → α → Json}
instance [FromJson α] : FromJson (WrapSerialize α g) := inferInstanceAs (FromJson α)
instance [ToJson α] : ToJson (WrapSerialize α g) where
  toJson opts a := if opts.serializers then g (toJson opts) a else toJson opts (show α from a)
instance [JsonSchema α] : JsonSchema (WrapSerialize α g) := inferInstanceAs (JsonSchema α)
instance [Repr α] : Repr (WrapSerialize α g) := inferInstanceAs (Repr α)
instance [DecidableEq α] : DecidableEq (WrapSerialize α g) := inferInstanceAs (DecidableEq α)
instance [Inhabited α] : Inhabited (WrapSerialize α g) := inferInstanceAs (Inhabited α)
instance {n : Nat} [OfNat α n] : OfNat (WrapSerialize α g) n := inferInstanceAs (OfNat α n)
end WrapSerialize

instance {β : Type} {g : (List β → Json) → List β → Json} : EmptyCollection (WrapSerialize (List β) g) :=
  ⟨([] : List β)⟩

end LeanPydantic
