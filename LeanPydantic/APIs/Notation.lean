import Lean
import LeanPydantic.APIs.Model

/-!
# APIs: `α ∣ c` under `open LeanPydantic`, and its literals

Keel's refinement notation, made available by `open LeanPydantic` (Keel
scopes it to `open Keel`). `Decimal ∣ gt 0`, `String ∣ maxLength 50 ∧
minLength 3` and `Nat ∣ le 100` are `{x // c.holds x}` for the Keel
constraint `c`; the atom names resolve to Keel's constructors without any
`open`.

A numeric, decimal or string literal whose expected type is a refinement is
checked against the constraint at elaboration time (`decide`), so
`discount : Nat ∣ le 100 := 0` needs no proof, and `:= 101` is a type error.
-/

namespace LeanPydantic

/-- Internal: a `refinement` as a `Keel.Constraint` term. The same
translation as Keel's `refinement%`, comparing atom names without macro
scopes, so that a field default (which Lean elaborates in a hygienic copy of
the field's type) still sees `le 100` as the atom. -/
syntax "pyd_refinement% " refinement : term

macro_rules
  | `(pyd_refinement% $a ∨ $b) => `(Keel.Constraint.or (pyd_refinement% $a) (pyd_refinement% $b))
  | `(pyd_refinement% $a ∧ $b) => `(Keel.Constraint.and (pyd_refinement% $a) (pyd_refinement% $b))
  | `(pyd_refinement% ¬ $a) => `(Keel.Constraint.not (pyd_refinement% $a))
  | `(pyd_refinement% ($a)) => `(pyd_refinement% $a)
  | `(pyd_refinement% $f:ident $args:term*) =>
    let n := f.getId.eraseMacroScopes
    if Keel.atomNames.contains n then
      `($(Lean.mkIdent (`Keel.Constraint ++ n)) $args*)
    else `($f $args*)

/-- `α ∣ c`: the values of `α` satisfying the constraint `c`. -/
scoped syntax:50 (priority := high) term:51 " ∣ " refinement : term

macro_rules
  | `($a ∣ $r:refinement) => `(Keel.Refined $a (pyd_refinement% $r))

open Lean Elab Term Meta in
/-- The base type of a refinement type, if the expected type is one. -/
def refinedBase? (expected : Option Expr) : TermElabM (Option Expr) := do
  let some e := expected | return none
  let e ← whnfR (← instantiateMVars e)
  if e.isAppOfArity ``Subtype 2 then
    let p := e.appArg!
    let p ← instantiateMVars p
    -- `fun x => Keel.Constraint.holds c x`
    if let .lam _ _ body _ := p then
      if body.getAppFn.isConstOf ``Keel.Constraint.holds then
        return some e.appFn!.appArg!
  return none

open Lean Elab Term in
/-- A literal at a refinement type: the literal at the base type, with the
constraint decided. -/
def elabRefinedLit (stx : Syntax) (expected : Option Expr) : TermElabM Expr := do
  let some base ← refinedBase? expected | throwUnsupportedSyntax
  let baseStx ← Lean.PrettyPrinter.delab base
  let lit : Term := ⟨stx⟩
  elabTerm (← `(⟨($lit : $baseStx), by decide⟩)) expected

open Lean Elab Term in
@[term_elab num] def elabRefinedNum : TermElab := elabRefinedLit

open Lean Elab Term in
@[term_elab scientific] def elabRefinedScientific : TermElab := elabRefinedLit

open Lean Elab Term in
@[term_elab str] def elabRefinedStr : TermElab := elabRefinedLit

end LeanPydantic
