import LeanPydantic.RepoImpl.Constraint

/-!
# RepoImpl: scalar types, `Option`, refinements

The validators follow pydantic-core's `validate_int`, `validate_float`,
`validate_bool` and `validate_str` on JSON input (`src/input/input_json.rs`),
with the lax coercions of `RepoImpl/Coerce.lean`; strict mode keeps only the
exact JSON type (and, for `float`, integers).

| Lean | pydantic | schema |
|---|---|---|
| `Int` | `int` | `{"type": "integer"}` |
| `Nat` | `NonNegativeInt` (`int`, `ge=0`) | `{"minimum": 0, "type": "integer"}` |
| `Decimal` | `FiniteFloat` (`float`, `allow_inf_nan=False`), exact | `{"type": "number"}` |
| `String` | `str` | `{"type": "string"}` |
| `Bool` | `bool` | `{"type": "boolean"}` |
| `Option α` | `α \| None` | `{"anyOf": [α, {"type": "null"}]}` |
| `α ∣ c` | `Annotated[α, …constraints]` | `α` with `c`'s keywords |
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-- A scalar validator's result as line errors: one error at the root, on
input `j`. -/
def liftKind {α : Type} (cfg : Cfg) (j : Json) : Except ErrorKind α → Except (List ErrorDetails) α
  | .ok a => .ok a
  | .error k => .error [{ kind := k, input := j, mode := cfg.mode }]

namespace Scalar

/-- pydantic's `int` validator. -/
def int (strict : Bool) : Json → Except ErrorKind Int
  | .num (.int i) => .ok i
  | .num (.float d) => if strict then .error .intType else Coerce.decimalAsInt d
  | .num _ => if strict then .error .intType else .error .finiteNumber
  | .bool b => if strict then .error .intType else .ok (if b then 1 else 0)
  | .str s => if strict then .error .intType else Coerce.strAsInt s
  | _ => .error .intType

/-- pydantic's `NonNegativeInt`: an `int`, then `ge=0`. -/
def nat (strict : Bool) (j : Json) : Except ErrorKind Nat :=
  match int strict j with
  | .ok i => if 0 ≤ i then .ok i.toNat else .error (.greaterThanEqual (.num (.int 0)))
  | .error k => .error k

/-- pydantic's `FiniteFloat` validator (`float` with `allow_inf_nan=False`),
exact. -/
def float (strict : Bool) : Json → Except ErrorKind Decimal
  | .num n => if n.isFinite then .ok (Num.toDecimal n) else .error .finiteNumber
  | .bool b => if strict then .error .floatType else .ok (Dec.ofInt (if b then 1 else 0))
  | .str s => if strict then .error .floatType else Coerce.strAsFloat s
  | _ => .error .floatType

/-- `int_as_bool`, on jiter's `i64` integers (bigger ones are `bool_type`). -/
def intAsBool (i : Int) : Except ErrorKind Bool :=
  if i = 0 then .ok false
  else if i = 1 then .ok true
  else if -Coerce.i64Bound ≤ i ∧ i < Coerce.i64Bound then .error .boolParsing
  else .error .boolType

/-- pydantic's `bool` validator. -/
def bool (strict : Bool) : Json → Except ErrorKind Bool
  | .bool b => .ok b
  | .str s => if strict then .error .boolType else Coerce.strAsBool s
  | .num (.int i) => if strict then .error .boolType else intAsBool i
  | .num (.float d) =>
    if strict then .error .boolType
    else match Coerce.decimalAsInt d with
      | .ok 0 => .ok false
      | .ok 1 => .ok true
      | .ok _ => .error .boolParsing
      | .error _ => .error .boolType
  | .num _ => .error .boolType
  | _ => .error .boolType

/-- pydantic's `str` validator. -/
def str : Json → Except ErrorKind String
  | .str s => .ok s
  | _ => .error .stringType

end Scalar

instance : FromJson Int := ⟨"int", fun cfg j => liftKind cfg j (Scalar.int cfg.strict j), fun _ => true⟩
instance : FromJson Nat := ⟨"constrained-int", fun cfg j => liftKind cfg j (Scalar.nat cfg.strict j), fun _ => true⟩
instance : FromJson Decimal where
  title := "float"
  fromJson cfg j := liftKind cfg j (Scalar.float cfg.strict j)
  exact
    | .num (.float _) => true
    | _ => false
instance : FromJson Bool := ⟨"bool", fun cfg j => liftKind cfg j (Scalar.bool cfg.strict j), fun _ => true⟩
instance : FromJson String := ⟨"str", fun cfg j => liftKind cfg j (Scalar.str j), fun _ => true⟩

instance : ToJson Int := ⟨fun _ i => .num (.int i)⟩
instance : ToJson Nat := ⟨fun _ n => .num (.int n)⟩
instance : ToJson Decimal := ⟨fun _ d => .num (.float d)⟩
instance : ToJson Bool := ⟨fun _ b => .bool b⟩
instance : ToJson String := ⟨fun _ s => .str s⟩

instance : JsonSchema Int := ⟨.integer []⟩
instance : JsonSchema Nat := ⟨.integer [.minimum (.int 0)]⟩
instance : JsonSchema Decimal := ⟨.number []⟩
instance : JsonSchema Bool := ⟨.boolean⟩
instance : JsonSchema String := ⟨.string []⟩

/-! ## `Option α`: pydantic's nullable schema -/

instance fromJsonOption {α : Type} [FromJson α] : FromJson (Option α) where
  title := "nullable[" ++ FromJson.title α ++ "]"
  exact
    | .null => true
    | j => FromJson.exact α j
  fromJson cfg
    | .null => .ok none
    | j => (fromJson cfg j).map some

instance toJsonOption {α : Type} [ToJson α] : ToJson (Option α) where
  toJson o
    | some a => toJson o a
    | none => .null

/-- `T | None`: `null` appended to `T`'s alternatives, or `anyOf [T, null]`
(pydantic flattens a nullable union into one `anyOf`). -/
def Schema.nullable : Schema → Schema
  | .anyOf alts => .anyOf (alts ++ [.null])
  | s => .anyOf [s, .null]

instance {α : Type} [JsonSchema α] : JsonSchema (Option α) := ⟨(JsonSchema.schema α).nullable⟩

/-! ## `α ∣ c`: the base validator, then the constraint -/

instance fromJsonRefined {α : Type} [FromJson α] [Constrained α] (c : Constraint α) :
    FromJson {x : α // c.holds x} where
  title := if (FromJson.title α).startsWith "constrained-" then FromJson.title α
    else "constrained-" ++ FromJson.title α
  exact := FromJson.exact α
  fromJson cfg j :=
    match fromJson cfg j with
    | .error es => .error es
    | .ok x =>
      if h : c.holds x then .ok ⟨x, h⟩
      else match c.validatePy x with
        | .error es => .error (Constraint.toDetails j cfg.mode es)
        | .ok _ => .error []

instance {α : Type} [ToJson α] (p : α → Prop) : ToJson {x : α // p x} := ⟨fun o x => toJson o x.val⟩

instance {α : Type} [JsonSchema α] [Constrained α] (c : Constraint α) :
    JsonSchema {x : α // c.holds x} :=
  ⟨(JsonSchema.schema α).withKeywords c.keywordsOf⟩

/-- Every `ToJson` type is a `LeanJson.IntoJson` type, so models and refined
values splice into `json%` literals. -/
instance (priority := low) {α : Type} [ToJson α] : LeanJson.IntoJson α := ⟨toJson {}⟩

end LeanPydantic
