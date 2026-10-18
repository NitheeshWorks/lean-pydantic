import Lean
import LeanPydantic.APIs.Model
import LeanPydantic.RepoImpl.Regex.Parse

/-!
# APIs: `α ∣ c` under `open LeanPydantic`, and its literals

Keel's refinement notation, made available by `open LeanPydantic` (Keel
scopes it to `open Keel`). `Decimal ∣ gt 0`, `String ∣ maxLength 50 ∧
minLength 3` and `Nat ∣ le 100` are `Keel.Refined α c`, that is
`{x // c.holds x}`, for the Keel constraint `c`. The right-hand side is
Keel's constraint syntax, so `3 ∣ n` keeps its meaning.

A literal whose expected type is a refinement is checked against the
constraint at elaboration time (`decide`), so `discount : Nat ∣ le 100 := 0`
needs no proof and `:= 101` is a type error. Keel does this for numerals and
strings; this module adds decimal literals (`price : Decimal ∣ gt 0 := 2.5`).

`pattern "^[a-z]+$"` takes a string literal as the pattern, in Rust `regex`
syntax as pydantic's `pattern=`. The literal is compiled when the code is
elaborated: an invalid pattern is a compile error, as it is a `SchemaError`
when pydantic builds the schema.
-/

namespace LeanPydantic

/-- `α ∣ c`: the values of `α` satisfying the constraint `c`. -/
scoped syntax:50 (priority := high) term:51 " ∣ " refinement : term

macro_rules
  | `($a ∣ $r:refinement) => `(Keel.Refined $a (refinement% $r))

open Lean Elab Term Meta in
/-- A decimal literal at a refinement type: the literal at the base type,
with the constraint decided. -/
@[term_elab scientific] def elabRefinedScientific : TermElab := fun stx expected? => do
  let some ty := expected? | throwUnsupportedSyntax
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Keel.Refined 2 do throwUnsupportedSyntax
  elabTerm (← `(Subtype.mk $(⟨stx⟩) (by decide))) ty

open Lean Elab Term Meta in
/-- A string literal where a `Keel.Pattern` is expected: the regex it spells,
compiled now, so an invalid one is an error here. -/
@[term_elab str] def elabPatternLiteral : TermElab := fun stx expected? => do
  let some ty := expected? | throwUnsupportedSyntax
  let ty ← whnfR (← instantiateMVars ty)
  unless ty.isConstOf ``Keel.Pattern do throwUnsupportedSyntax
  let some src := stx.isStrLit? | throwUnsupportedSyntax
  match Regex.compile src with
  | .error e => throwError "invalid pattern {repr src}: {e}"
  | .ok _ => elabTerm (← `(LeanPydantic.Regex.ofSource $(⟨stx⟩))) ty

end LeanPydantic
