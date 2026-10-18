import Lean
import LeanPydantic.APIs.Notation

/-!
# APIs: `deriving Model`

For a structure

```
structure Item where
  name : String
  description : Option String := none
  price : Decimal ∣ gt 0
  deriving Model
```

the handler lists the fields and nothing more:

* an instance `Model Item` whose `fields` is
  `Fields.field "name" none (Fields.field "description" (some none) (…Fields.nil))`
  and whose `lawful` proof is the matching chain of `Fields.field_lawful`
  applications, each freshness side condition closed by `decide`;
* the per-model theorems `Item.fromJson_toJson` and `Item.schema_sound`, both
  instances of the generic laws (`LawfulJson`);
* pydantic's method names in the model's namespace: `Item.model_validate`,
  `Item.model_validate_json`, `Item.model_json_schema`, `item.model_dump`,
  `item.model_dump_json`.

No proof is generated per field or per model beyond these applications of
general theorems. Field defaults are the structure's own (`:= none`); a field
without one is required. Supported: structures without parameters or parent
structures, whose defaults do not refer to other fields.
-/

namespace LeanPydantic.Derive

open Lean Elab Command Meta

/-- `Prod.fst (Prod.snd (… p))`, `i` `snd`s deep. -/
def projAt {m : Type → Type} [Monad m] [MonadQuotation m] (p : Term) : Nat → m Term
  | 0 => `(Prod.fst $p)
  | i + 1 => do projAt (← `(Prod.snd $p)) i

/-- The commands `deriving Model` emits for `declName`. -/
def mkModelCmds (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env declName do
    throwError "deriving Model: `{declName}` is not a structure"
  let indVal ← getConstInfoInduct declName
  unless indVal.numParams = 0 do
    throwError "deriving Model: `{declName}` has parameters, which are not supported yet"
  let fields := getStructureFields env declName
  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  unless ctorVal.numFields = fields.size do
    throwError "deriving Model: `{declName}` extends another structure, which is not supported yet"
  for f in fields do
    if isSubobjectField? env declName f |>.isSome then
      throwError "deriving Model: `{declName}` extends another structure, which is not supported yet"
  let tyId := mkIdent declName
  let title := Syntax.mkStrLit (declName.componentsRev.head!.toString)
  -- the field chain and its lawfulness proof, built from the last field back
  let mut fieldsStx ← `(LeanPydantic.Fields.nil)
  let mut lawStx ← `(LeanPydantic.Fields.nil_lawful)
  for f in fields.reverse do
    let nameLit := Syntax.mkStrLit f.toString
    let dflt ← match getDefaultFnForField? env declName f with
      | some d =>
        let some dInfo := env.find? d | throwError "deriving Model: no default for `{f}`"
        if dInfo.type.isForall then
          throwError "deriving Model: the default of `{f}` depends on other fields, which is not supported"
        -- the structure elaborator leaves `_default` uncompiled; compile it so
        -- the instance's code can call it
        unless (IR.findEnvDecl (← getEnv) d).isSome do
          liftCoreM <| compileDecls #[d]
        `(some $(mkIdent d))
      | none => `(none)
    fieldsStx ← `(LeanPydantic.Fields.field $nameLit $dflt $fieldsStx)
    lawStx ← `(LeanPydantic.Fields.field_lawful (by decide) $lawStx)
  -- into: the tuple of fields; back: the constructor applied to its parts
  let x := mkIdent `x
  let p := mkIdent `p
  let mut tuple ← `(())
  for f in fields.reverse do
    tuple ← `(($(mkIdent (declName ++ f)) $x, $tuple))
  let parts ← (List.range fields.size).toArray.mapM (projAt p)
  let ctor := mkIdent ctorVal.name
  let n := declName
  elabCommand (← `(command|
    instance : LeanPydantic.Model $tyId where
      title := $title
      fields := $fieldsStx
      into := fun ($x : $tyId) => $tuple
      back := fun $p => $ctor $parts*
      back_into := fun _ => rfl
      lawful := $lawStx))
  elabCommand (← `(command|
    /-- Validating a dump gives the model back (an instance of `LawfulJson`). -/
    theorem $(mkIdent (n ++ `fromJson_toJson)) (cfg : LeanPydantic.Cfg) (a : $tyId) :
        LeanPydantic.fromJson cfg (LeanPydantic.toJson {} a) = .ok a :=
      LeanPydantic.LawfulJson.fromJson_toJson cfg a))
  elabCommand (← `(command|
    /-- Strict validation accepts only input the model's schema allows. -/
    theorem $(mkIdent (n ++ `schema_sound)) (cfg : LeanPydantic.Cfg) (j : LeanJson.Json) (a : $tyId)
        (hs : cfg.strict = true) (h : LeanPydantic.fromJson cfg j = .ok a) :
        LeanPydantic.Conforms (LeanPydantic.JsonSchema.schema $tyId) j :=
      LeanPydantic.LawfulJson.schema_sound cfg j a hs h))
  let obj := mkIdent `obj
  let strict := mkIdent `strict
  let data := mkIdent `data
  let self := mkIdent `self
  let incl := mkIdent `«include»
  let excl := mkIdent `exclude
  let exd := mkIdent `exclude_defaults
  let exn := mkIdent `exclude_none
  let indent := mkIdent `indent
  elabCommand (← `(command|
    /-- `Model.model_validate(obj, strict=None)`. -/
    def $(mkIdent (n ++ `model_validate)) ($obj : LeanJson.Json) ($strict : Bool := false) :=
      LeanPydantic.Model.model_validate $tyId $obj $strict))
  elabCommand (← `(command|
    /-- `Model.model_validate_json(data, strict=None)`. -/
    def $(mkIdent (n ++ `model_validate_json)) ($data : String) ($strict : Bool := false) :=
      LeanPydantic.Model.model_validate_json $tyId $data $strict))
  elabCommand (← `(command|
    /-- `Model.model_json_schema()`. -/
    def $(mkIdent (n ++ `model_json_schema)) : LeanJson.Json :=
      LeanPydantic.Model.model_json_schema $tyId))
  elabCommand (← `(command|
    /-- `model.model_dump(include=, exclude=, exclude_defaults=, exclude_none=)`. -/
    def $(mkIdent (n ++ `model_dump)) ($self : $tyId) ($incl : Option (List String) := none)
        ($excl : List String := []) ($exd : Bool := false) ($exn : Bool := false) :
        LeanJson.Json :=
      LeanPydantic.Model.model_dump $self $incl $excl $exd $exn))
  elabCommand (← `(command|
    /-- `model.model_dump_json(indent=None, ...)`. -/
    def $(mkIdent (n ++ `model_dump_json)) ($self : $tyId) ($indent : Option Nat := none)
        ($incl : Option (List String) := none) ($excl : List String := [])
        ($exd : Bool := false) ($exn : Bool := false) : String :=
      LeanPydantic.Model.model_dump_json $self $indent $incl $excl $exd $exn))

/-- The `deriving Model` handler. -/
def mkModelHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do mkModelCmds n
  return true

initialize registerDerivingHandler ``LeanPydantic.Model mkModelHandler

end LeanPydantic.Derive
