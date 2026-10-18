import LeanPydantic.APIs
import LeanPydantic.Proofs.Verified

/-!
# LeanPydantic

A clean-room port of pydantic, pydantic-core and annotated-types to Lean 4:
validation as refinement types. Constraints are decidable predicates
(Keel's constraint language), validated values carry their proof, errors are
pydantic's, and the generated JSON Schema is proved sound.

```
import LeanPydantic
open LeanPydantic

structure Item where
  name : String
  description : Option String := none
  price : Decimal ∣ gt 0
  tax : Option Decimal := none
  deriving Model
```

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      errors, options, JSON Schema, the three classes
* `RepoImpl/`       numbers, coercions, messages, validators, `Fields`
* `Specifications/` `Conforms` and the laws (`LawfulJson`, `Fields.Lawful`)
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           `Model`, `TypeAdapter`, `model_*`, `α ∣ c`, `deriving Model`
-/
