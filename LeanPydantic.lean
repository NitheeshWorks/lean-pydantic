import LeanPydantic.APIs
import LeanPydantic.Proofs.Verified

/-!
# LeanPydantic

A clean-room port of pydantic, pydantic-core and annotated-types to Lean 4: validation as refinement types: constraints are decidable predicates, validated values carry their proof, and the generated JSON Schema is proved sound.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
