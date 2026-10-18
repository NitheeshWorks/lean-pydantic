import LeanPydantic
import Plausible

/-!
# Plausible properties

Randomised checks run at build time with `plausible` (`#eval
Testable.check`, which fails the build on a counter-example): restatements of
proved laws on plausible's own generators (a smoke test of the definitions
the theorems are about), and the lax coercions, which are tested rather than
proved.
-/

namespace Pbt

open LeanPydantic

def okInt (r : Except ErrorKind Int) (i : Int) : Bool :=
  match r with
  | .ok j => j == i
  | .error _ => false

def validates {α : Type} [FromJson α] [DecidableEq α] (j : LeanJson.Json) (a : α) : Bool :=
  match fromJson (α := α) {} j with
  | .ok b => decide (a = b)
  | .error _ => false

-- the int coercion reads every integer's decimal form (tested, not proved)
#eval Plausible.Testable.check (∀ i : Int, okInt (Coerce.strAsInt (toString i)) i = true)

-- with surrounding whitespace and a `.0` suffix
#eval Plausible.Testable.check (∀ i : Int, okInt (Coerce.strAsInt (" " ++ toString i ++ ".0 ")) i = true)

-- the proved round trip, on plausible's generators
#eval Plausible.Testable.check (∀ i : Int, validates (toJson {} i) i = true)
#eval Plausible.Testable.check (∀ s : String, validates (toJson {} s) s = true)
#eval Plausible.Testable.check (∀ o : Option Int, validates (toJson {} o) o = true)

-- a refinement accepts exactly the satisfying values
#eval Plausible.Testable.check (∀ n : Nat,
  (fromJson (α := {x : Nat // (Keel.Constraint.le 100 : Keel.Constraint Nat).holds x}) {} (.num (.int n))).toOption.isSome
    = decide (n ≤ 100))

end Pbt
