# lean-pydantic

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [pydantic, pydantic-core and annotated-types](https://github.com/pydantic/pydantic) to Lean 4: validation as refinement types: constraints are decidable predicates, validated values carry their proof, and the generated JSON Schema is proved sound.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: [lean-json](https://github.com/NitheeshWorks/lean-json) and
[lean-keel](https://github.com/NitheeshWorks/lean-keel).

## Quickstart

pydantic's own first example (`docs/index.md`, "Pydantic examples"),
translated. `datetime` and `dict` fields arrive with the next milestone, so
`signup_ts` is a string here and `tastes` a single positive integer.

```python
from pydantic import BaseModel, PositiveInt

class User(BaseModel):
    id: int
    name: str = 'John Doe'
    signup_ts: str | None
    tastes: PositiveInt

user = User.model_validate({'id': 123, 'signup_ts': '2019-06-01 12:22', 'tastes': '9'})
print(user.id, user.model_dump_json())
#> 123 {"id":123,"name":"John Doe","signup_ts":"2019-06-01 12:22","tastes":9}
```

```lean
import LeanPydantic
open LeanPydantic

structure User where
  id : Int
  name : String := "John Doe"
  signup_ts : Option String
  tastes : Int ∣ gt 0
  deriving Model

#eval match User.model_validate (json% {"id": 123, "signup_ts": "2019-06-01 12:22", "tastes": "9"}) with
  | .ok user => s!"{user.val.id} {user.val.model_dump_json}"
  | .error e => e.json
-- 123 {"id":123,"name":"John Doe","signup_ts":"2019-06-01 12:22","tastes":9}
```

Failures are pydantic's, byte for byte:

```lean
#eval match User.model_validate (json% {"id": "not an int", "tastes": 0}) with
  | .ok _ => ""
  | .error e => e.json (include_url := false)
-- [{"type":"int_parsing","loc":["id"],"msg":"Input should be a valid integer, unable to parse string as an integer","input":"not an int"},
--  {"type":"missing","loc":["signup_ts"],"msg":"Field required","input":{"id":"not an int","tastes":0}},
--  {"type":"greater_than","loc":["tastes"],"msg":"Input should be greater than 0","input":0,"ctx":{"gt":0}}]
```

and so is `User.model_json_schema`.

### The surface

| pydantic | lean-pydantic |
|---|---|
| `class Item(BaseModel)` | `structure Item where … deriving Model` |
| `price: float` | `price : Decimal` (an exact `FiniteFloat`) |
| `x: int`, `n: NonNegativeInt`, `s: str`, `b: bool` | `Int`, `Nat`, `String`, `Bool` |
| `q: str \| None = None` | `q : Option String := none` |
| `Annotated[float, Field(gt=0)]` | `Decimal ∣ gt 0` |
| `Annotated[str, Field(max_length=50, min_length=3)]` | `String ∣ maxLength 50 ∧ minLength 3` |
| `discount: Annotated[NonNegativeInt, Field(le=100)] = 0` | `discount : Nat ∣ le 100 := 0` (checked at compile time) |
| `Item.model_validate(obj, strict=True)` | `Item.model_validate obj (strict := true)` |
| `Item.model_validate_json(data)` | `Item.model_validate_json data` |
| `item.model_dump(exclude_none=True)` | `item.model_dump (exclude_none := true)` |
| `item.model_dump_json(indent=2)` | `item.model_dump_json (indent := some 2)` |
| `Item.model_json_schema()` | `Item.model_json_schema` |
| `TypeAdapter(int).validate_python('42')` | `(TypeAdapter.new Int).validate_python (json% "42")` |
| `e.errors(include_url=False)`, `e.json()` | `e.errors (include_url := false)`, `e.json` |

The constraint language is lean-keel's (`Keel.Refine`): `gt ge lt le
multipleOf minLength maxLength`, joined with `∧`. A literal at a refined type
is checked when the file is compiled, so user code carries no proofs.

## What is proved

Every statement below is a theorem (`Proofs/Verified.lean` lists them; CI
checks they use only Lean's three axioms).

* **Validation is sound and complete.** Checking a constraint in pydantic's
  order returns the value exactly when the constraint holds:
  `c.validatePy x = .ok x ↔ c.holds x` (`validatePy_iff`), with
  `validate_sound`, `validate_complete`, and `validate_errors_nonempty`.
* **Refinements validate as their base, then their constraint.**
  `fromJson cfg j = .ok y ↔ fromJson cfg j = .ok y.val` for `y : α ∣ c`
  (`fromJson_refined_iff`).
* **Round trip.** For every model, strict or lax:
  `(Item.model_validate (item.model_dump) strict).map (·.val) = .ok item`
  (`Model.model_validate_model_dump`; per model, `Item.fromJson_toJson`).
* **The schema is sound.** What strict validation accepts conforms to
  `model_json_schema`'s schema (`Model.schema_sound`, per model
  `Item.schema_sound`), every dump conforms (`model_dump_conforms`), and a
  nullable field's schema means "null or the field type"
  (`nullable_anyOf : Conforms (schema (Option α)) j ↔ j = .null ∨ Conforms (schema α) j`).
  Each constraint keyword is sound by one induction (`keywordsOf_sound`).
* **Errors agree with themselves.** Every error's `msg` is its `type`'s
  pydantic-core template rendered from its `ctx`:
  `e.msg = render e.ctx (template e.mode e.type)` (`error_type_ctx_coherent`).
* **Errors are located.** Every error of a model's validation sits under one
  of its fields (`Model.validate_loc_prefix`), by Keel's `Validator.at`.
* **Exact numbers.** Bounds compare exact decimals at any common exponent
  (`Num.rel_at`, `Num.rel_denotes`).

These come from a few general facts: the field combinator is lawful
(`Fields.field_lawful`), and the deriving handler builds each model's proof
from it, never a proof about a particular model.

Tested rather than proved: the lax coercions (`'0042'` to `42`, `'yes'` to
`true`), which are checked byte for byte against pydantic on 581 generated
cases (`tests/ConformanceTable.lean`) and by properties.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # 584 cases replayed against pydantic's own output
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Status

Milestone 1: scalars, `Option`, constraints, models from flat structures,
errors, JSON Schema. Next (milestone 2): lists, dicts, nested models, unions,
aliases, validators, serializers, `datetime`, regex patterns.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
