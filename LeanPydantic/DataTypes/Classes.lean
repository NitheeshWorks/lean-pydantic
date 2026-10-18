import LeanPydantic.DataTypes.Schema

/-!
# DataTypes: the three classes

A type takes part in validation, serialisation and schema generation through
three classes, the Lean side of a pydantic core schema:

* `FromJson α`: validate a JSON value (pydantic's validator), reporting
  every failure as a located `ErrorDetails`;
* `ToJson α`: dump a value (pydantic's serialiser), under `DumpOpts`;
* `JsonSchema α`: the JSON Schema (pydantic's JSON Schema generator).

Their laws are the class `LawfulJson` in `Specifications/`.
-/

namespace LeanPydantic

open LeanJson (Json)

/-- Validation from JSON. `title` is what a `ValidationError` for this type
is titled (pydantic: the model name, or `int`, `str`, ...). -/
class FromJson (α : Type) where
  title : String
  fromJson : Cfg → Json → Except (List ErrorDetails) α
  /-- Whether a strict success on this input is an *exact* match (pydantic-core's
  `Exactness::Exact`): a `float` from an integer is strict but not exact. Smart
  unions prefer exact matches. -/
  exact : Json → Bool := fun _ => true

/-- Serialisation to JSON. -/
class ToJson (α : Type) where
  toJson : DumpOpts → α → Json

/-- The JSON Schema of a type. -/
class JsonSchema (α : Type) where
  schema : Schema

export FromJson (fromJson)
export ToJson (toJson)

end LeanPydantic
