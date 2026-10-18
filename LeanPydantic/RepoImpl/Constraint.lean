import LeanPydantic.RepoImpl.Schema

/-!
# RepoImpl: Keel constraints, the pydantic way

Keel's `Constraint α` is the constraint language; this module adds what
pydantic makes of it:

* **Check order.** pydantic-core checks a constrained number's
  `multiple_of`, `le`, `lt`, `ge`, `gt` in that order and a string's
  `min_length` before `max_length`, whatever order the user wrote, and
  reports the first failure. `Constraint.validatePy` splits the conjunction
  into its conjuncts, sorts them by that rank (stably), and runs Keel's
  `validate` on each until one fails.
* **Errors and keywords.** `Constrained α` says, per carrier type, which
  pydantic error a failed atom gives (`greater_than` with `ctx.gt`, or
  `string_too_short` with `ctx.min_length`) and which JSON Schema keywords an
  atom contributes (`gt` gives `exclusiveMinimum`). The instances for numbers
  share `Constrained.numeric`, which differs per type only in how a bound is
  shown.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

end LeanPydantic

namespace Keel.Constraint

open LeanPydantic

variable {α : Type}

/-- pydantic-core's check order: `multiple_of`, `le`, `lt`, `ge`, `gt`,
`min_length`, `max_length`, `pattern`, then everything pydantic has no
keyword for. -/
def rank : Constraint α → Nat
  | @Constraint.multipleOf _ _ _ => 0
  | @Constraint.le _ _ _ => 1
  | @Constraint.lt _ _ _ => 2
  | @Constraint.ge _ _ _ => 3
  | @Constraint.gt _ _ _ => 4
  | @Constraint.minLength _ _ _ => 5
  | @Constraint.maxLength _ _ _ => 6
  | @Constraint.pattern _ _ _ => 7
  | _ => 8

/-- The conjuncts of a constraint, in the order written. -/
def conjuncts : Constraint α → List (Constraint α)
  | .and c d => conjuncts c ++ conjuncts d
  | c => [c]

/-- The conjuncts in pydantic's check order (a stable sort by `rank`). -/
def ordered (c : Constraint α) : List (Constraint α) :=
  (conjuncts c).mergeSort (fun a b => decide (rank a ≤ rank b))

/-- The errors of the first conjunct, in `ordered` order, that fails. -/
def firstFailure (x : α) : List (Constraint α) → Option (List (Keel.Refine.Error α))
  | [] => none
  | a :: as =>
    match a.validate x with
    | .error es => some es
    | .ok _ => firstFailure x as

/-- Validate in pydantic's order: `x` back, or the errors of the first
failing conjunct. -/
def validatePy (c : Constraint α) (x : α) : Except (List (Keel.Refine.Error α)) α :=
  match firstFailure x (ordered c) with
  | some es => .error es
  | none => .ok x

end Keel.Constraint

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-- How a carrier type reports a failed atom and describes an atom in JSON
Schema. Only atoms matter: `and` is handled generically, and `or`, `not`,
`oneOf` (which pydantic has no keyword for) contribute no keyword. -/
class Constrained (α : Type) where
  /-- The pydantic error for the atom `a` failing on `x`. -/
  error : Constraint α → α → ErrorKind
  /-- The JSON Schema keywords of the atom `a`. -/
  keywords : Constraint α → List Keyword
  /-- The atom uses the instances its keywords describe. Keel stores each
  atom's `Ordered`/`Divisible`/`Sized`/`Textual` instance in the atom, so an
  atom built by hand with some other instance means something else; the
  keywords are only claimed sound for atoms built by instance resolution. -/
  Std : Constraint α → Prop

/-- The error for a Keel atom outside pydantic's vocabulary. -/
def unsupportedError : ErrorKind := .valueError "the value does not satisfy the constraint"

namespace Constrained

/-- The instance for a numeric type with order `O` and divisibility `D`,
from how a bound appears in an error's `ctx` and in the schema. -/
@[instance_reducible] def numeric {α : Type} (O : Keel.Ordered α) (D : Keel.Divisible α)
    (ctx schema : α → Number) : Constrained α where
  error
    | @Constraint.gt _ _ b, _ => .greaterThan (ctx b)
    | @Constraint.ge _ _ b, _ => .greaterThanEqual (ctx b)
    | @Constraint.lt _ _ b, _ => .lessThan (ctx b)
    | @Constraint.le _ _ b, _ => .lessThanEqual (ctx b)
    | @Constraint.multipleOf _ _ k, _ => .multipleOf (ctx k)
    | _, _ => unsupportedError
  keywords
    | @Constraint.gt _ _ b => [.exclusiveMinimum (schema b)]
    | @Constraint.ge _ _ b => [.minimum (schema b)]
    | @Constraint.lt _ _ b => [.exclusiveMaximum (schema b)]
    | @Constraint.le _ _ b => [.maximum (schema b)]
    | @Constraint.multipleOf _ _ k => [.multipleOf (schema k)]
    | _ => []
  Std
    | @Constraint.gt _ i _ | @Constraint.ge _ i _ | @Constraint.lt _ i _ | @Constraint.le _ i _ => i = O
    | @Constraint.multipleOf _ i _ => i = D
    | _ => True

end Constrained

instance : Constrained Int := Constrained.numeric inferInstance inferInstance .int .int
instance : Constrained Nat := Constrained.numeric inferInstance inferInstance (fun n => .int n) (fun n => .int n)
/-- A `float` bound: a float in the error context (`{"gt": 0.0}`), as written
in the schema (`"exclusiveMinimum": 0`). -/
instance : Constrained Decimal := Constrained.numeric inferInstance inferInstance .float Num.ofDecimal

instance constrainedString : Constrained String where
  error
    | @Constraint.minLength _ _ n, _ => .stringTooShort n
    | @Constraint.maxLength _ _ n, _ => .stringTooLong n
    | @Constraint.pattern _ _ p, _ => .stringPatternMismatch p.source
    | _, _ => unsupportedError
  keywords
    | @Constraint.minLength _ _ n => [.minLength n]
    | @Constraint.maxLength _ _ n => [.maxLength n]
    | @Constraint.pattern _ _ p => [.pattern p]
    | _ => []
  Std
    | @Constraint.minLength _ i _ | @Constraint.maxLength _ i _ => i = Keel.instSizedString
    | @Constraint.pattern _ i _ => i = Keel.instTextualString
    | _ => True

end LeanPydantic

namespace Keel.Constraint

open LeanPydantic
open LeanJson (Json)

variable {α : Type} [Constrained α]

/-- All JSON Schema keywords of a constraint: those of its conjuncts. -/
def keywordsOf : Constraint α → List Keyword
  | .and c d => keywordsOf c ++ keywordsOf d
  | .or _ _ | .not _ | @Constraint.oneOf _ _ _ => []
  | c => Constrained.keywords c

/-- Every atom of `c` uses the instances its keywords describe. -/
def AllStd : Constraint α → Prop
  | .and c d => AllStd c ∧ AllStd d
  | .or _ _ | .not _ | @Constraint.oneOf _ _ _ => True
  | c => Constrained.Std c

/-- Keel's errors as pydantic line errors on input `j`. -/
def toDetails (j : Json) (mode : InputMode) (es : List (Keel.Refine.Error α)) : List ErrorDetails :=
  es.map fun e => { kind := Constrained.error e.failed e.input, loc := e.loc, input := j, mode }

end Keel.Constraint

namespace LeanPydantic

open Keel (Constraint)
open LeanJson (Decimal)

/-- `c` is built from atoms with their types' own instances, as writing
`gt 0` or `maxLength 50` always does. Found by instance resolution; the
refinement laws assume it. -/
class Canonical {α : Type} [Constrained α] (c : Constraint α) : Prop where
  std : c.AllStd

instance {α : Type} [Constrained α] (c d : Constraint α) [hc : Canonical c] [hd : Canonical d] :
    Canonical (c.and d) := ⟨⟨hc.std, hd.std⟩⟩
instance {α : Type} [Constrained α] (c d : Constraint α) : Canonical (c.or d) := ⟨trivial⟩
instance {α : Type} [Constrained α] (c : Constraint α) : Canonical (c.not) := ⟨trivial⟩
instance {α : Type} [Constrained α] [DecidableEq α] (cs : List α) :
    Canonical (Constraint.oneOf cs) := ⟨trivial⟩

instance (b : Int) : Canonical (Constraint.gt b) := ⟨rfl⟩
instance (b : Int) : Canonical (Constraint.ge b) := ⟨rfl⟩
instance (b : Int) : Canonical (Constraint.lt b) := ⟨rfl⟩
instance (b : Int) : Canonical (Constraint.le b) := ⟨rfl⟩
instance (b : Int) : Canonical (Constraint.multipleOf b) := ⟨rfl⟩
instance (b : Nat) : Canonical (Constraint.gt b) := ⟨rfl⟩
instance (b : Nat) : Canonical (Constraint.ge b) := ⟨rfl⟩
instance (b : Nat) : Canonical (Constraint.lt b) := ⟨rfl⟩
instance (b : Nat) : Canonical (Constraint.le b) := ⟨rfl⟩
instance (b : Nat) : Canonical (Constraint.multipleOf b) := ⟨rfl⟩
instance (b : Decimal) : Canonical (Constraint.gt b) := ⟨rfl⟩
instance (b : Decimal) : Canonical (Constraint.ge b) := ⟨rfl⟩
instance (b : Decimal) : Canonical (Constraint.lt b) := ⟨rfl⟩
instance (b : Decimal) : Canonical (Constraint.le b) := ⟨rfl⟩
instance (b : Decimal) : Canonical (Constraint.multipleOf b) := ⟨rfl⟩
instance (n : Nat) : Canonical (Constraint.minLength n : Constraint String) := ⟨rfl⟩
instance (n : Nat) : Canonical (Constraint.maxLength n : Constraint String) := ⟨rfl⟩
instance (p : Keel.Pattern) : Canonical (Constraint.pattern p : Constraint String) := ⟨rfl⟩

end LeanPydantic
