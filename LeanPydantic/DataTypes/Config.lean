import LeanPydantic.DataTypes.Error

/-!
# DataTypes: validation and serialisation options
-/

namespace LeanPydantic

/-- Validation settings: pydantic's `strict` flag, and the input mode. -/
structure Cfg where
  strict : Bool := false
  mode : InputMode := .python
  deriving DecidableEq, Repr, Inhabited

/-- `model_dump` options, named as in pydantic. `«include»` (`include` is a Lean keyword) and `exclude` name
top-level fields. -/
structure DumpOpts where
  «include» : Option (List String) := none
  exclude : List String := []
  exclude_defaults : Bool := false
  exclude_none : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The options that reach nested values: pydantic applies `exclude_none` and
`exclude_defaults` at every level, `include`/`exclude` only where they name a
field. -/
def DumpOpts.nested (o : DumpOpts) : DumpOpts :=
  { exclude_defaults := o.exclude_defaults, exclude_none := o.exclude_none }

end LeanPydantic
