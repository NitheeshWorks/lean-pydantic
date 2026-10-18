import LeanPydantic.RepoImpl.Containers

/-!
# RepoImpl: literals, unions, tuples

| Lean | pydantic | schema |
|---|---|---|
| `String ∣ oneOf ["a", "b"]` | `Literal['a', 'b']` | `{"enum": ["a", "b"], "type": "string"}` |
| `α ⊕ β ⊕ γ` | `Union[α, β, γ]` (smart mode) | `{"anyOf": [α, β, γ]}` |
| `α × β × γ` | `tuple[α, β, γ]` | `prefixItems`, `minItems`, `maxItems` |

**Smart unions** follow pydantic-core's `union.rs`: the leftmost choice that
validates strictly with an *exact* match wins; failing that, the leftmost
strict match; failing that (in lax mode), the leftmost lax match. When every
choice fails, every choice's errors are reported, each under the choice's
tag (`int`, `str`, `constrained-int`, `list[int]`, the model's name).

Right-nested `⊕` and `×` read as one flat union or tuple, as Lean writes
them: `Int × String × Bool` is `tuple[int, str, bool]`.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-! ## Python `repr`, for `literal_error` and `enum` contexts -/

/-- A character inside a Python string literal written with `quote`. -/
def pyEscape (quote : Char) (c : Char) : String :=
  if c = '\\' then "\\\\"
  else if c = quote then "\\" ++ String.singleton c
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else if c.toNat < 0x20 ∨ c.toNat = 0x7f then
    "\\x" ++ String.ofList (Nat.toDigits 16 (c.toNat / 16)) ++ String.ofList (Nat.toDigits 16 (c.toNat % 16))
  else String.singleton c

/-- Python's `repr` of a string: single quotes, unless it contains a single
quote and no double quote. -/
def pyStrRepr (s : String) : String :=
  let q := if s.contains '\'' ∧ ¬ s.contains '"' then '"' else '\''
  String.singleton q ++ String.join (s.toList.map (pyEscape q)) ++ String.singleton q

/-- Python's `repr` of a JSON scalar (`True`, `None`, `'a'`, `1`). -/
def pyRepr : Json → String
  | .str s => pyStrRepr s
  | .bool true => "True"
  | .bool false => "False"
  | .null => "None"
  | j => toString j

/-- `a`, `a or b`, `a, b or c`: how pydantic lists expected values. -/
def orJoin : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " or " ++ b
  | a :: rest => a ++ ", " ++ orJoin rest

/-! ## `Literal[...]` -/

/-- In lax mode a boolean input also matches the integer literal `1` or `0`,
as Python's `True == 1` (pydantic-core's `exact_int` accepts a bool). -/
def laxLiteralInput (cfg : Cfg) : Json → Option Json
  | .bool b => if cfg.strict then none else some (.num (.int (if b then 1 else 0)))
  | _ => none

/-- The first value whose dump is `j`. -/
def literalFind {α : Type} [ToJson α] (cs : List α) (j : Json) : Option α :=
  cs.find? (fun c => decide (toJson DumpOpts.roundTrip c = j))

/-- `Literal[v₁, …]`: the input must equal one of the values' dumps. -/
instance (priority := high) fromJsonLiteral {α : Type} [ToJson α] [DecidableEq α] (cs : List α) :
    FromJson {x : α // (Constraint.oneOf cs).holds x} where
  title := "literal[" ++ ", ".intercalate (cs.map (pyRepr ∘ toJson DumpOpts.roundTrip)) ++ "]"
  fromJson cfg j :=
    let err : Except (List ErrorDetails) {x : α // (Constraint.oneOf cs).holds x} :=
      .error [{ kind := ErrorKind.literalError (orJoin (cs.map (pyRepr ∘ toJson DumpOpts.roundTrip))),
                input := j, mode := cfg.mode }]
    match h : literalFind cs j with
    | some c => .ok ⟨c, List.mem_of_find?_eq_some h⟩
    | none =>
      match laxLiteralInput cfg j with
      | some j' =>
        match h' : literalFind cs j' with
        | some c => .ok ⟨c, List.mem_of_find?_eq_some h'⟩
        | none => err
      | none => err

instance (priority := high) {α : Type} [ToJson α] [DecidableEq α] (cs : List α) :
    JsonSchema {x : α // (Constraint.oneOf cs).holds x} :=
  ⟨.literal (cs.map (toJson DumpOpts.roundTrip))⟩

/-! ## Smart unions -/

/-- The choices of a (right-nested) union. -/
class Choices (τ : Type) where
  tags : List String
  schemas : List Schema
  /-- The leftmost choice that validates strictly and exactly. -/
  exactly : Cfg → Json → Option τ
  /-- The leftmost choice that validates strictly. -/
  strictly : Cfg → Json → Option τ
  /-- The leftmost choice that validates under `cfg`, or every choice's errors
  under its tag. -/
  laxly : Cfg → Json → Except (List ErrorDetails) τ
  dump : DumpOpts → τ → Json

/-- The strict configuration for the same input mode. -/
def Cfg.strictly (cfg : Cfg) : Cfg := { cfg with strict := true }

/-- One choice. -/
instance (priority := low) choiceOne {α : Type} [FromJson α] [ToJson α] [JsonSchema α] : Choices α where
  tags := [FromJson.title α]
  schemas := [JsonSchema.schema α]
  exactly cfg j :=
    match fromJson (α := α) cfg.strictly j with
    | .ok a => if FromJson.exact α j then some a else none
    | .error _ => none
  strictly cfg j := (fromJson (α := α) cfg.strictly j).toOption
  laxly cfg j := (Keel.Validator.at (.key (FromJson.title α)) (fromJson (α := α) cfg)) j
  dump := toJson

/-- One more choice, on the left. -/
instance choiceSum {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β] : Choices (α ⊕ β) where
  tags := FromJson.title α :: Choices.tags β
  schemas := JsonSchema.schema α :: Choices.schemas β
  exactly cfg j :=
    match fromJson (α := α) cfg.strictly j with
    | .ok a => if FromJson.exact α j then some (.inl a) else (Choices.exactly cfg j).map .inr
    | .error _ => (Choices.exactly cfg j).map .inr
  strictly cfg j :=
    match fromJson (α := α) cfg.strictly j with
    | .ok a => some (.inl a)
    | .error _ => (Choices.strictly cfg j).map .inr
  laxly cfg j :=
    match (Keel.Validator.at (.key (FromJson.title α)) (fromJson (α := α) cfg)) j with
    | .ok a => .ok (.inl a)
    | .error e₁ =>
      match Choices.laxly (τ := β) cfg j with
      | .ok b => .ok (.inr b)
      | .error e₂ => .error (e₁ ++ e₂)
  dump o
    | .inl a => toJson o a
    | .inr b => Choices.dump o b

/-- pydantic's smart-mode union. -/
def smartUnion {τ : Type} [Choices τ] (cfg : Cfg) (j : Json) : Except (List ErrorDetails) τ :=
  match Choices.exactly cfg j with
  | some r => .ok r
  | none =>
    match Choices.strictly cfg j with
    | some r => .ok r
    | none => Choices.laxly cfg j

instance fromJsonSum {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β] : FromJson (α ⊕ β) where
  title := "union[" ++ ",".intercalate (Choices.tags (α ⊕ β)) ++ "]"
  fromJson := smartUnion

instance toJsonSum {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β] : ToJson (α ⊕ β) :=
  ⟨Choices.dump⟩

instance {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β] : JsonSchema (α ⊕ β) :=
  ⟨.anyOf (Choices.schemas (α ⊕ β))⟩

/-! ## Tuples -/

/-- The items of a (right-nested) tuple. -/
class TupleItems (τ : Type) where
  arity : Nat
  titles : List String
  schemas : List Schema
  /-- Validate items from index `i` of the array `w`: each under its index,
  `missing` (with the whole array as input) where the array ends early. -/
  decode : Cfg → Json → Nat → Keel.Validator ErrorDetails (List Json) τ
  encode : DumpOpts → τ → List Json

/-- One item at index `i`, or `missing`. -/
def tupleItem {α : Type} [FromJson α] (cfg : Cfg) (w : Json) (i : Nat) :
    Keel.Validator ErrorDetails (List Json) α :=
  Keel.Validator.at (.index i) fun
    | x :: _ => fromJson cfg x
    | [] => .error [{ kind := .missing, input := w, mode := cfg.mode }]

instance (priority := low) tupleOne {α : Type} [FromJson α] [ToJson α] [JsonSchema α] : TupleItems α where
  arity := 1
  titles := [FromJson.title α]
  schemas := [JsonSchema.schema α]
  decode cfg w i := tupleItem cfg w i
  encode o a := [toJson o a]

instance tupleProd {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] :
    TupleItems (α × β) where
  arity := TupleItems.arity β + 1
  titles := FromJson.title α :: TupleItems.titles β
  schemas := JsonSchema.schema α :: TupleItems.schemas β
  decode cfg w i := Keel.Validator.both (tupleItem cfg w i) (fun xs => TupleItems.decode cfg w (i + 1) xs.tail)
  encode o p := toJson o p.1 :: TupleItems.encode o p.2

instance fromJsonProd {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] :
    FromJson (α × β) where
  title := "tuple[" ++ ", ".intercalate (TupleItems.titles (α × β)) ++ "]"
  fromJson cfg
    | .arr ⟨xs⟩ =>
      if xs.length > TupleItems.arity (α × β) then
        let k := ErrorKind.tooLong "Tuple" (TupleItems.arity (α × β)) xs.length
        .error [{ kind := k, input := .arr ⟨xs⟩, mode := cfg.mode }]
      else TupleItems.decode cfg (.arr ⟨xs⟩) 0 xs
    | j => .error [{ kind := .tupleType, input := j, mode := cfg.mode }]

instance toJsonProd {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] :
    ToJson (α × β) := ⟨fun o p => .arr ⟨TupleItems.encode o p⟩⟩

instance {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] : JsonSchema (α × β) :=
  ⟨.tuple (TupleItems.schemas (α × β))⟩

end LeanPydantic

namespace LeanPydantic

open LeanJson (Json)

/-! ## Enumerations -/

/-- An enumeration (pydantic's `class C(str, Enum)`): its name, its members
in order, and each member's value. `deriving Model` builds it for an
inductive type whose constructors take no arguments, with the constructor
names as values. -/
class Enumeration (α : Type) where
  title : String
  members : List α
  value : α → String

namespace Enumeration

variable {α : Type} [e : Enumeration α]

/-- `'red' or 'green'`: the `enum` error's `expected`. -/
def expected : String := orJoin (e.members.map fun a => pyStrRepr (e.value a))

/-- Validate a member's value. -/
def validate (cfg : Cfg) (j : Json) : Except (List ErrorDetails) α :=
  let err : Except (List ErrorDetails) α :=
    .error [{ kind := .enum (expected (α := α)), input := j, mode := cfg.mode }]
  match j with
  | .str s =>
    match e.members.find? (fun a => decide (e.value a = s)) with
    | some a => .ok a
    | none => err
  | _ => err

/-- The schema: a reference to `{"enum": [...], "title": C, "type": "string"}`. -/
def schema : Schema :=
  .ref e.title (.annotated (.literal (e.members.map fun a => .str (e.value a))) (some e.title) none)

end Enumeration

instance (priority := low) {α : Type} [e : Enumeration α] : FromJson α :=
  ⟨e.title, Enumeration.validate, fun _ => true⟩
instance (priority := low) {α : Type} [e : Enumeration α] : ToJson α := ⟨fun _ a => .str (e.value a)⟩
instance (priority := low) {α : Type} [Enumeration α] : JsonSchema α := ⟨Enumeration.schema (α := α)⟩

end LeanPydantic
