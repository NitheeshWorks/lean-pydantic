import LeanJson
import Keel.Refine

/-!
# DataTypes: validation errors

pydantic-core reports each failure as a line error with five parts: `type`,
`loc`, `msg`, `input` and, for some types, `ctx`. Here the `type` and the `ctx`
come from one value, `ErrorKind`, whose constructors carry exactly the context
pydantic-core attaches to that error type. `msg` is then a function of the kind
and the input mode (`RepoImpl/Error.lean`), so the three parts cannot disagree.

Locations are Keel's `Loc` (keys and indices, outermost first), so the
location theorems of `Keel.Refine` (`Validator.at`, `atPath`) apply to these
errors directly.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
export Keel (Loc PathElem)
export LeanJson (Json Decimal)

/-- What kind of input is being validated: Python objects (`model_validate`,
`validate_python`) or JSON text (`model_validate_json`, `validate_json`).
pydantic-core picks some message templates by it (`model_type` says
`Input should be an object` for JSON input). -/
inductive InputMode where
  | python
  | json
  deriving DecidableEq, Repr, Inhabited

/-- A pydantic error type together with its context. Each constructor is one
pydantic-core `ErrorType`; its arguments are exactly that type's `ctx`. -/
inductive ErrorKind where
  /-- `missing`: a required field is absent. -/
  | missing
  /-- `model_type`: the input for a model is not an object. -/
  | modelType (className : String)
  /-- `json_invalid`: `model_validate_json` was given text that is not JSON. -/
  | jsonInvalid (error : String)
  | intType
  | intParsing
  | intParsingSize
  | intFromFloat
  | finiteNumber
  | floatType
  | floatParsing
  | boolType
  | boolParsing
  | stringType
  | greaterThan (gt : Number)
  | greaterThanEqual (ge : Number)
  | lessThan (lt : Number)
  | lessThanEqual (le : Number)
  | multipleOf (multipleOf : Number)
  | stringTooShort (minLength : Nat)
  | stringTooLong (maxLength : Nat)
  | stringPatternMismatch (pattern : String)
  /-- `value_error`: a failed constraint outside pydantic's own vocabulary
  (Keel's `or`, `not`, `oneOf`), reported as an after-validator's
  `ValueError` would be. -/
  | valueError (error : String)
  deriving DecidableEq, Repr, Inhabited

/-- One line error. `type`, `msg` and `ctx` are computed from `kind` and
`mode` (`ErrorDetails.type`, `.msg`, `.ctx`). -/
structure ErrorDetails where
  kind : ErrorKind
  loc : Loc := []
  input : Json
  mode : InputMode := .python
  deriving DecidableEq, Repr, Inhabited

instance : Keel.Located ErrorDetails where
  loc e := e.loc
  within k e := { e with loc := k :: e.loc }
  loc_within _ _ := rfl

/-- pydantic's `ValidationError`: the title (the model or type name) and the
line errors, of which there is always at least one. -/
structure ValidationError where
  title : String
  line_errors : List ErrorDetails
  nonempty : line_errors ≠ []

end LeanPydantic
