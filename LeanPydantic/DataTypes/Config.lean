import LeanPydantic.DataTypes.Error

/-!
# DataTypes: validation and serialisation options
-/

namespace LeanPydantic

/-- Validation settings: pydantic's `strict` flag, and the input mode. -/
structure Cfg where
  strict : Bool := false
  mode : InputMode := .python
  /-- pydantic's `from_attributes`: in Python mode, a model given a
  non-object reports `model_attributes_type` instead of `model_type`. A Lean
  value has no attributes to read, so this changes only that error. -/
  from_attributes : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- `model_dump` options, named as in pydantic. `«include»` (`include` is a
Lean keyword) and `exclude` name top-level fields. `exclude_unset` needs to
know which fields were set: `set_from` is the input the value was validated
from (pydantic records this on the instance as `model_fields_set`; a Lean
structure value carries no such record, so without `set_from` every field
counts as set). -/
structure DumpOpts where
  «include» : Option (List String) := none
  exclude : List String := []
  by_alias : Bool := false
  exclude_unset : Bool := false
  exclude_defaults : Bool := false
  exclude_none : Bool := false
  set_from : Option LeanJson.Json := none
  deriving DecidableEq, Inhabited

/-- The options that reach a nested value: pydantic applies `by_alias`,
`exclude_unset`, `exclude_defaults` and `exclude_none` at every level,
`include`/`exclude` only where they name a field. `set_from` follows the
value into the input. -/
def DumpOpts.nested (o : DumpOpts) (set_from : Option LeanJson.Json := none) : DumpOpts :=
  { by_alias := o.by_alias, exclude_unset := o.exclude_unset,
    exclude_defaults := o.exclude_defaults, exclude_none := o.exclude_none, set_from }

/-- The dump that validation reads back: every field, under its alias. -/
def DumpOpts.roundTrip : DumpOpts := { by_alias := true }

end LeanPydantic
