import LeanPydantic.DataTypes.Config

/-!
# DataTypes: JSON Schema

The subset of JSON Schema (draft 2020-12, as OpenAPI 3.1 uses it) that
pydantic's `model_json_schema()` emits for the supported types. `Schema` is
the abstract syntax; `Schema.toJson` prints it as pydantic does, and
`Conforms` (in `Specifications/`) is its meaning.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

/-- A validation keyword of a scalar schema. -/
inductive Keyword where
  | exclusiveMinimum (n : Number)
  | minimum (n : Number)
  | exclusiveMaximum (n : Number)
  | maximum (n : Number)
  | multipleOf (n : Number)
  | minLength (n : Nat)
  | maxLength (n : Nat)
  /-- `pattern`: its source, and the matcher that gives it meaning. -/
  | pattern (p : Keel.Pattern)

/-- A JSON Schema. -/
inductive Schema where
  /-- `{}`: anything. -/
  | any
  | null
  | boolean
  | integer (kws : List Keyword)
  | number (kws : List Keyword)
  | string (kws : List Keyword)
  | anyOf (alts : List Schema)
  /-- A model: its title, its properties in field order, its required keys. -/
  | object (title : String) (props : List (String × Schema)) (required : List String)
  /-- Annotations that do not affect validation: a field's `title` and
  `default`. -/
  | annotated (s : Schema) (title : Option String) (default : Option Json)
  deriving Inhabited

/-- The same schema with more keywords (for a refinement of a scalar). -/
def Schema.withKeywords (s : Schema) (kws : List Keyword) : Schema :=
  match s with
  | .integer k => .integer (k ++ kws)
  | .number k => .number (k ++ kws)
  | .string k => .string (k ++ kws)
  | s => s

end LeanPydantic
