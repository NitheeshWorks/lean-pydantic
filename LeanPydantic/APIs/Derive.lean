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
* Settings go where pydantic puts them, in a `model_config` member:

```
structure FormData where
  username : String
  password : String
  model_config : ConfigDict (extra := .forbid) := {}
  deriving Model
```

`ConfigDict` holds nothing (its value is always `{}`); the handler reads
`extra` and `populate_by_name` from its type. It is not a field of the
model: not validated, dumped or in the schema.

the per-model theorems `Item.fromJson_toJson` and `Item.schema_sound`, both
  instances of the generic laws (`LawfulJson`);
* pydantic's method names in the model's namespace: `Item.model_validate`,
  `Item.model_validate_json`, `Item.model_json_schema`, `item.model_dump`,
  `item.model_dump_json`.

No proof is generated per field or per model beyond these applications of
general theorems. Field defaults are the structure's own (`:= none`); a field
without one is required. Supported: structures without parameters or parent
structures, whose defaults do not refer to other fields.
-/

namespace LeanPydantic

/-- `Alias "itemId" Int`: a field of type `Int` that pydantic validates and
(with `by_alias`) dumps under the key `itemId`, as
`item_id: int = Field(alias='itemId')`. It is `Int` itself (an `abbrev`), so
the field is used as an `Int`; only `deriving Model` reads the alias. -/
abbrev Alias (_alias : String) (α : Type) : Type := α

/-- pydantic's `model_config = ConfigDict(extra=…, populate_by_name=…)`, as a
structure member `model_config : ConfigDict (extra := .forbid) := {}`.
`extra` is what validation does with members no field reads (`.ignore`, the
default; `.forbid`; `.allow`); `populate_by_name` lets a field with an alias
also be read by its name. The type holds no data, so a structure with this
member is still determined by its fields. -/
structure ConfigDict (extra : Extra := .ignore) (populate_by_name : Bool := false) : Type where
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A field whose default is pydantic's `Field(default_factory=…)`: the
structure's default (`tags : Factory (List String) := []`), made afresh for
each value as Lean always does, and, as in pydantic, not written into the
JSON Schema. Like `Alias`, only `deriving Model` reads it. -/
abbrev Factory (α : Type) : Type := α

end LeanPydantic

namespace LeanPydantic.Derive

open Lean Elab Command Meta

/-- The alias of a field type `Alias "a" T`, if it is one. -/
def aliasOf? (ty : Expr) : Option String :=
  if ty.isAppOfArity ``LeanPydantic.Alias 2 then
    match ty.appFn!.appArg! with
    | .lit (.strVal s) => some s
    | _ => none
  else none

/-- The settings of a `ConfigDict e p` member type: `extra` and
`populate_by_name`, if they are written out as constructors. -/
def configOf? (ty : Expr) : MetaM (Option (Option (Name × Bool))) := do
  if !ty.isAppOfArity ``LeanPydantic.ConfigDict 2 then return none
  let e ← whnf ty.appFn!.appArg!
  let p ← whnf ty.appArg!
  match e.constName?, p.constName? with
  | some en, some pn =>
    if pn == ``Bool.true then return some (some (en, true))
    else if pn == ``Bool.false then return some (some (en, false))
    else return some none
  | _, _ => return some none

/-- Whether a field type is `Factory T`, possibly under `Alias`. -/
def isFactory (ty : Expr) : Bool :=
  let ty := if ty.isAppOfArity ``LeanPydantic.Alias 2 then ty.appArg! else ty
  ty.isAppOfArity ``LeanPydantic.Factory 1

/-- `Prod.fst (Prod.snd (… p))`, `i` `snd`s deep. -/
def projAt {m : Type → Type} [Monad m] [MonadQuotation m] (p : Term) : Nat → m Term
  | 0 => `(Prod.fst $p)
  | i + 1 => do projAt (← `(Prod.snd $p)) i

/-- `deriving Model` on an inductive type whose constructors take no
arguments: an enumeration whose values are the constructor names
(pydantic's `class Color(str, Enum)`), with its laws by `decide`. -/
def mkEnumCmds (declName : Name) (indVal : InductiveVal) : CommandElabM Unit := do
  let tyId := mkIdent (`_root_ ++ declName)
  let title := Syntax.mkStrLit (declName.componentsRev.head!.toString)
  let ctors := indVal.ctors.toArray.map mkIdent
  let alts ← indVal.ctors.toArray.mapM fun c =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) => $(Syntax.mkStrLit c.componentsRev.head!.toString))
  elabCommand (← `(command| deriving instance DecidableEq for $tyId))
  elabCommand (← `(command|
    instance : LeanPydantic.Enumeration $tyId where
      title := $title
      members := [$ctors,*]
      value := fun $alts:matchAlt*))
  elabCommand (← `(command|
    instance : LeanPydantic.LawfulEnumeration $tyId :=
      ⟨by intro a; cases a <;> decide, by decide⟩))

/-- The commands `deriving Model` emits for `declName`. -/
def mkModelCmds (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  if let some (.inductInfo indVal) := env.find? declName then
    if !isStructure env declName then
      let mut nullary := indVal.numParams = 0 && indVal.numIndices = 0
      for c in indVal.ctors do
        if let some (.ctorInfo cv) := env.find? c then
          if cv.numFields ≠ 0 then nullary := false
      if nullary then
        mkEnumCmds declName indVal
        return
  unless isStructure env declName do
    throwError "deriving Model: `{declName}` is not a structure or an enumeration"
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
  let tyId := mkIdent (`_root_ ++ declName)
  let title := Syntax.mkStrLit (declName.componentsRev.head!.toString)
  let allTypes ← liftTermElabM <| forallTelescope ctorVal.type fun xs _ => xs.mapM (fun x => inferType x)
  -- a `model_config : ConfigDict …` member: the settings, and not a field
  let configs ← liftTermElabM <| allTypes.mapM fun t => configOf? t
  let mut extra : Name := ``LeanPydantic.Extra.ignore
  let mut populate := false
  for (f, c) in fields.zip configs do
    match c with
    | some (some (e, p)) =>
      unless f == `model_config do
        throwError "deriving Model: a `ConfigDict` member must be named `model_config`, not `{f}`"
      extra := e
      populate := p
    | some none => throwError "deriving Model: write `model_config`'s settings as constants, e.g. `ConfigDict (extra := .forbid)`"
    | none => pure ()
  let isConfig : Array Bool := configs.map Option.isSome
  let modelFields := ((fields.zip allTypes).zip isConfig).filterMap fun ((f, t), c) => if c then none else some (f, t)
  let fieldTypes := modelFields.map (·.2)
  -- the field chain and its lawfulness proof, built from the last field back
  let mut fieldsStx ← `(LeanPydantic.Fields.nil)
  let mut lawStx ← `(LeanPydantic.Fields.nil_lawful)
  let mut soundStx ← `(LeanPydantic.Fields.nil_sound)
  let mut byNameAny := false
  let mut aliasAny := false
  for (f, fty) in modelFields.reverse do
    let nameLit := Syntax.mkStrLit f.toString
    let aliasStx ← match aliasOf? fty with
      | some a => `(some $(Syntax.mkStrLit a))
      | none => `(none)
    let dflt ← match getDefaultFnForField? env declName f with
      | some d =>
        let some dInfo := env.find? d | throwError "deriving Model: no default for `{f}`"
        if dInfo.type.isForall then
          throwError "deriving Model: the default of `{f}` depends on other fields, which is not supported"
        -- the structure elaborator leaves `_default` uncompiled; compile it so
        -- the instance's code can call it
        unless (IR.findEnvDecl (← getEnv) d).isSome do
          liftCoreM <| compileDecls #[d]
        `(some $(mkIdent (`_root_ ++ d)))
      | none => `(none)
    let factoryStx ← if isFactory fty then `(true) else `(false)
    if (aliasOf? fty).any (· != f.toString) then aliasAny := true
    let byName := populate && (aliasOf? fty).isSome
    if byName then byNameAny := true
    let byNameStx ← if byName then `(true) else `(false)
    fieldsStx ← `(LeanPydantic.Fields.field $nameLit $aliasStx $dflt $fieldsStx $factoryStx $byNameStx)
    lawStx ← `(LeanPydantic.Fields.field_lawful (by decide) $lawStx)
    soundStx ← `(LeanPydantic.Fields.field_sound $soundStx)
  -- into: the tuple of fields; back: the constructor applied to its parts
  let x := mkIdent `x
  let p := mkIdent `p
  let mut tuple ← `(())
  for (f, _) in modelFields.reverse do
    tuple ← `(($(mkIdent (`_root_ ++ declName ++ f)) $x, $tuple))
  -- the constructor's arguments: the parts of the tuple, and `{}` for `model_config`
  let mut parts : Array Term := #[]
  let mut i := 0
  for c in isConfig do
    if c then parts := parts.push (← `(LeanPydantic.ConfigDict.mk))
    else
      parts := parts.push (← projAt p i)
      i := i + 1
  let ctor := mkIdent (`_root_ ++ ctorVal.name)
  let n := declName
  let extraStx := mkIdent extra
  elabCommand (← `(command|
    instance : LeanPydantic.Model $tyId where
      title := $title
      fields := $fieldsStx
      into := fun ($x : $tyId) => $tuple
      back := fun $p => $ctor $parts*
      back_into := fun _ => rfl
      extra := $extraStx))
  -- the laws, when every field type has them (a `Float` field has none)
  let fieldsLawful ← liftTermElabM <| fieldTypes.allM fun fty => do
    let inst ← mkAppOptM ``LeanPydantic.LawfulJson #[some fty, none, none, none]
    return (← trySynthInstance inst) matches .some _
  if fieldsLawful then
    elabCommand (← `(command|
      instance : LeanPydantic.LawfulFields $tyId := ⟨$lawStx⟩))
    elabCommand (← `(command|
      /-- Validating a dump by alias gives the model back. -/
      theorem $(mkIdent (`_root_ ++ n ++ `fromJson_toJson)) (cfg : LeanPydantic.Cfg) (a : $tyId) :
          LeanPydantic.fromJson cfg (LeanPydantic.toJson LeanPydantic.DumpOpts.roundTrip a) = .ok a :=
        LeanPydantic.Model.fromJson_toJson cfg a))
  -- schema soundness, unless a field is also read by its name (pydantic's
  -- schema lists only the alias, so a value read by name would not conform
  -- to it: UP-065)
  if fieldsLawful && !(byNameAny || (extra == ``LeanPydantic.Extra.forbid && aliasAny)) then
    elabCommand (← `(command|
      instance : LeanPydantic.LawfulModel $tyId := { lawful := $lawStx, sound := $soundStx, forbid_names := by decide }))
    elabCommand (← `(command|
      /-- Strict validation accepts only input the model's schema allows. -/
      theorem $(mkIdent (`_root_ ++ n ++ `schema_sound)) (cfg : LeanPydantic.Cfg) (j : LeanJson.Json) (a : $tyId)
          (hs : cfg.strict = true) (h : LeanPydantic.fromJson cfg j = .ok a) :
          LeanPydantic.Conforms (LeanPydantic.JsonSchema.schema $tyId) j :=
        LeanPydantic.LawfulJson.schema_sound cfg j a hs h))
  let obj := mkIdent `obj
  let strict := mkIdent `strict
  let fromAttrs := mkIdent `from_attributes
  let data := mkIdent `data
  let self := mkIdent `self
  let incl := mkIdent `«include»
  let excl := mkIdent `exclude
  let exd := mkIdent `exclude_defaults
  let exn := mkIdent `exclude_none
  let indent := mkIdent `indent
  let byAlias := mkIdent `by_alias
  let exu := mkIdent `exclude_unset
  let setFrom := mkIdent `set_from
  elabCommand (← `(command|
    /-- `Model.model_validate(obj, strict=None, from_attributes=None)`. -/
    def $(mkIdent (`_root_ ++ n ++ `model_validate)) ($obj : LeanJson.Json) ($strict : Bool := false)
        ($fromAttrs : Bool := false) :=
      LeanPydantic.Model.model_validate $tyId $obj $strict $fromAttrs))
  elabCommand (← `(command|
    /-- `Model.model_validate_json(data, strict=None)`. -/
    def $(mkIdent (`_root_ ++ n ++ `model_validate_json)) ($data : String) ($strict : Bool := false) :=
      LeanPydantic.Model.model_validate_json $tyId $data $strict))
  elabCommand (← `(command|
    /-- `Model.model_json_schema()`. -/
    def $(mkIdent (`_root_ ++ n ++ `model_json_schema)) : LeanJson.Json :=
      LeanPydantic.Model.model_json_schema $tyId))
  elabCommand (← `(command|
    /-- `model.model_dump(include=, exclude=, exclude_defaults=, exclude_none=)`. -/
    def $(mkIdent (`_root_ ++ n ++ `model_dump)) ($self : $tyId) ($incl : Option (List String) := none)
        ($excl : List String := []) ($byAlias : Bool := false) ($exu : Bool := false)
        ($exd : Bool := false) ($exn : Bool := false) ($setFrom : Option LeanJson.Json := none) :
        LeanJson.Json :=
      LeanPydantic.Model.model_dump $self $incl $excl $byAlias $exu $exd $exn $setFrom))
  elabCommand (← `(command|
    /-- `model.model_dump_json(indent=None, ...)`. -/
    def $(mkIdent (`_root_ ++ n ++ `model_dump_json)) ($self : $tyId) ($indent : LeanPydantic.Indent := {})
        ($incl : Option (List String) := none) ($excl : List String := [])
        ($byAlias : Bool := false) ($exu : Bool := false)
        ($exd : Bool := false) ($exn : Bool := false) ($setFrom : Option LeanJson.Json := none) : String :=
      LeanPydantic.Model.model_dump_json $self $indent $incl $excl $byAlias $exu $exd $exn $setFrom))

/-- The `deriving Model` handler. -/
def mkModelHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do mkModelCmds n
  return true

initialize registerDerivingHandler ``LeanPydantic.Model mkModelHandler

end LeanPydantic.Derive
