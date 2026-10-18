import LeanPydantic.RepoImpl.Coerce

/-!
# RepoImpl: the error vocabulary

For every `ErrorKind`: its pydantic `type` string, its `ctx`, and its message.
The message templates are pydantic-core's (`src/errors/types.rs`,
`message_template_python` and `message_template_json`) as lists of pieces;
`render` fills them from the `ctx` the way pydantic-core's `render!` and
`to_string_render!` do (numbers by Rust's `Display`, `expected_plural` from
the length). `ErrorKind.message` is written out directly, and
`Proofs/Error.lean` proves it equal to the rendered template
(`error_type_ctx_coherent`).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

namespace ErrorKind

/-- The pydantic error `type`. -/
def type : ErrorKind → String
  | .missing => "missing"
  | .modelType _ => "model_type"
  | .jsonInvalid _ => "json_invalid"
  | .intType => "int_type"
  | .intParsing => "int_parsing"
  | .intParsingSize => "int_parsing_size"
  | .intFromFloat => "int_from_float"
  | .finiteNumber => "finite_number"
  | .floatType => "float_type"
  | .floatParsing => "float_parsing"
  | .boolType => "bool_type"
  | .boolParsing => "bool_parsing"
  | .stringType => "string_type"
  | .greaterThan _ => "greater_than"
  | .greaterThanEqual _ => "greater_than_equal"
  | .lessThan _ => "less_than"
  | .lessThanEqual _ => "less_than_equal"
  | .multipleOf _ => "multiple_of"
  | .stringTooShort _ => "string_too_short"
  | .stringTooLong _ => "string_too_long"
  | .stringPatternMismatch _ => "string_pattern_mismatch"
  | .valueError _ => "value_error"

/-- The pydantic error `ctx`, as JSON members (empty: no `ctx`). -/
def ctx : ErrorKind → List (String × Json)
  | .modelType c => [("class_name", .str c)]
  | .jsonInvalid e => [("error", .str e)]
  | .greaterThan n => [("gt", .num n)]
  | .greaterThanEqual n => [("ge", .num n)]
  | .lessThan n => [("lt", .num n)]
  | .lessThanEqual n => [("le", .num n)]
  | .multipleOf n => [("multiple_of", .num n)]
  | .stringTooShort n => [("min_length", .num (.int n))]
  | .stringTooLong n => [("max_length", .num (.int n))]
  | .stringPatternMismatch p => [("pattern", .str p)]
  | .valueError e => [("error", .str e)]
  | _ => []

/-- `""` for one, `"s"` otherwise (pydantic-core's `plural_s`). -/
def plural (n : Number) : String := if n = .int 1 then "" else "s"

/-- The message, written out. -/
def message (mode : InputMode) : ErrorKind → String
  | .missing => "Field required"
  | .modelType c => match mode with
    | .python => "Input should be a valid dictionary or instance of " ++ c
    | .json => "Input should be an object"
  | .jsonInvalid e => "Invalid JSON: " ++ e
  | .intType => "Input should be a valid integer"
  | .intParsing => "Input should be a valid integer, unable to parse string as an integer"
  | .intParsingSize => "Unable to parse input string as an integer, exceeded maximum size"
  | .intFromFloat => "Input should be a valid integer, got a number with a fractional part"
  | .finiteNumber => "Input should be a finite number"
  | .floatType => "Input should be a valid number"
  | .floatParsing => "Input should be a valid number, unable to parse string as a number"
  | .boolType => "Input should be a valid boolean"
  | .boolParsing => "Input should be a valid boolean, unable to interpret input"
  | .stringType => "Input should be a valid string"
  | .greaterThan n => "Input should be greater than " ++ Num.display n
  | .greaterThanEqual n => "Input should be greater than or equal to " ++ Num.display n
  | .lessThan n => "Input should be less than " ++ Num.display n
  | .lessThanEqual n => "Input should be less than or equal to " ++ Num.display n
  | .multipleOf n => "Input should be a multiple of " ++ Num.display n
  | .stringTooShort n =>
    "String should have at least " ++ Num.display (.int n) ++ " character" ++ plural (.int n)
  | .stringTooLong n =>
    "String should have at most " ++ Num.display (.int n) ++ " character" ++ plural (.int n)
  | .stringPatternMismatch p => "String should match pattern '" ++ p ++ "'"
  | .valueError e => "Value error, " ++ e

end ErrorKind

/-- A piece of a message template: literal text, `{key}`, or
`{expected_plural}` computed from the length under `key`. -/
inductive Piece where
  | lit (s : String)
  | var (key : String)
  | plural (key : String)

/-- pydantic-core's message template for an error `type`, by input mode
(`message_template_python` / `message_template_json`). -/
def template (mode : InputMode) (type : String) : List Piece :=
  match type with
  | "missing" => [.lit "Field required"]
  | "model_type" => match mode with
    | .python => [.lit "Input should be a valid dictionary or instance of ", .var "class_name"]
    | .json => [.lit "Input should be an object"]
  | "json_invalid" => [.lit "Invalid JSON: ", .var "error"]
  | "int_type" => [.lit "Input should be a valid integer"]
  | "int_parsing" => [.lit "Input should be a valid integer, unable to parse string as an integer"]
  | "int_parsing_size" => [.lit "Unable to parse input string as an integer, exceeded maximum size"]
  | "int_from_float" => [.lit "Input should be a valid integer, got a number with a fractional part"]
  | "finite_number" => [.lit "Input should be a finite number"]
  | "float_type" => [.lit "Input should be a valid number"]
  | "float_parsing" => [.lit "Input should be a valid number, unable to parse string as a number"]
  | "bool_type" => [.lit "Input should be a valid boolean"]
  | "bool_parsing" => [.lit "Input should be a valid boolean, unable to interpret input"]
  | "string_type" => [.lit "Input should be a valid string"]
  | "greater_than" => [.lit "Input should be greater than ", .var "gt"]
  | "greater_than_equal" => [.lit "Input should be greater than or equal to ", .var "ge"]
  | "less_than" => [.lit "Input should be less than ", .var "lt"]
  | "less_than_equal" => [.lit "Input should be less than or equal to ", .var "le"]
  | "multiple_of" => [.lit "Input should be a multiple of ", .var "multiple_of"]
  | "string_too_short" =>
    [.lit "String should have at least ", .var "min_length", .lit " character", .plural "min_length"]
  | "string_too_long" =>
    [.lit "String should have at most ", .var "max_length", .lit " character", .plural "max_length"]
  | "string_pattern_mismatch" => [.lit "String should match pattern '", .var "pattern", .lit "'"]
  | "value_error" => [.lit "Value error, ", .var "error"]
  | _ => []

/-- A context value as pydantic-core formats it into a message. -/
def displayValue : Json → String
  | .str s => s
  | .num n => Num.display n
  | j => toString j

/-- The first value under `k`. -/
def ctxLookup (k : String) : List (String × Json) → Option Json
  | [] => none
  | (k', v) :: r => if k' = k then some v else ctxLookup k r

/-- Fill a template from a context. -/
def render (ctx : List (String × Json)) : List Piece → String
  | [] => ""
  | .lit s :: ps => s ++ render ctx ps
  | .var k :: ps => (match ctxLookup k ctx with
      | some v => displayValue v
      | none => "") ++ render ctx ps
  | .plural k :: ps => (match ctxLookup k ctx with
      | some (.num n) => ErrorKind.plural n
      | _ => "s") ++ render ctx ps

namespace ErrorDetails

/-- The pydantic error `type`. -/
def type (e : ErrorDetails) : String := e.kind.type

/-- The message. -/
def msg (e : ErrorDetails) : String := e.kind.message e.mode

/-- The context (empty when pydantic attaches none). -/
def ctx (e : ErrorDetails) : List (String × Json) := e.kind.ctx

/-- The documentation link pydantic attaches (`errors.pydantic.dev`, for the
2.14 series this port follows). -/
def url (e : ErrorDetails) : String := "https://errors.pydantic.dev/2.14/v/" ++ e.type

/-- A location as JSON: keys as strings, indices as integers. -/
def locJson (l : Loc) : Json :=
  .arr (l.map fun | .key k => .str k | .index i => .num (.int i))

/-- One line error as pydantic's `errors()` gives it, members in pydantic's
order: `type`, `loc`, `msg`, `input`, then `ctx` and `url` when present and
asked for. -/
def toJson (e : ErrorDetails) (include_url := true) (include_context := true)
    (include_input := true) : Json :=
  .obj <| [("type", .str e.type), ("loc", locJson e.loc), ("msg", .str e.msg)] ++
    (if include_input then [("input", e.input)] else []) ++
    (if include_context ∧ e.ctx ≠ [] then [("ctx", .obj e.ctx)] else []) ++
    (if include_url then [("url", .str e.url)] else [])

end ErrorDetails

namespace ValidationError

/-- pydantic's `errors()`. -/
def errors (e : ValidationError) (include_url := true) (include_context := true)
    (include_input := true) : List Json :=
  e.line_errors.map (·.toJson include_url include_context include_input)

/-- pydantic's `error_count()`. -/
def error_count (e : ValidationError) : Nat := e.line_errors.length

/-- pydantic's `json()`: the errors, compact. -/
def json (e : ValidationError) (include_url := true) (include_context := true)
    (include_input := true) : String :=
  LeanJson.printStr (.arr (e.errors include_url include_context include_input))

instance : ToString ValidationError := ⟨fun e => e.json⟩

end ValidationError

end LeanPydantic
