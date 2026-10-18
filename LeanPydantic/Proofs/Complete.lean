import LeanPydantic.Proofs.Wrappers
import LeanPydantic.RepoImpl.PyDecimal

/-!
# Proofs: schema completeness for scalars

`schema_sound` says strict validation accepts only what the schema allows.
Completeness is the converse: every input the schema allows validates. It
holds for `bool`, `str` and plain `float` (in JSON mode, where a huge
integer is `inf` rather than Python's `OverflowError`), for `int` on integer
literals, and is preserved by `Optional`.

Where it fails, it fails as in pydantic, and the gap is pydantic's: `int`'s
`{"type": "integer"}` allows `1e30` (an integral number) and, strictly,
`1.0`, which pydantic rejects (`int_parsing_size`, `int_type`); `FiniteFloat`
and `Decimal` allow non-finite numbers that the lenient parser produces.
-/

namespace LeanPydantic

open LeanJson (Json Number)

/-- Every input the schema allows validates. -/
def SchemaComplete (α : Type) [FromJson α] [JsonSchema α] (cfg : Cfg) : Prop :=
  ∀ j, Conforms (JsonSchema.schema α) j → ∃ a, fromJson (α := α) cfg j = .ok a

theorem schema_complete_bool (cfg : Cfg) : SchemaComplete Bool cfg := by
  intro j h
  cases j <;> simp [Conforms, JsonSchema.schema, Schema.check, JsonKind.isBool] at h
  exact ⟨_, rfl⟩

theorem schema_complete_string (cfg : Cfg) : SchemaComplete String cfg := by
  intro j h
  cases j <;> simp [Conforms, JsonSchema.schema, Schema.check, JsonKind.isStr] at h
  exact ⟨_, rfl⟩

/-- Plain `float` in JSON mode: every number validates (non-finite ones too). -/
theorem schema_complete_float (cfg : Cfg) (hm : cfg.mode = .json) : SchemaComplete Float cfg := by
  intro j h
  cases j with
  | num n =>
    cases n with
    | int i => exact ⟨_, by simp [fromJson, liftKind, Scalar.plainFloat, hm]; rfl⟩
    | _ => exact ⟨_, rfl⟩
  | _ => simp [Conforms, JsonSchema.schema, Schema.check, JsonKind.isNum] at h

/-- `int` on integer literals: every one validates, strictly or not. -/
theorem schema_complete_int (cfg : Cfg) (j : Json) (h : Conforms (JsonSchema.schema Int) j)
    (hlit : ∀ d, j ≠ .num (.float d)) : ∃ a, fromJson (α := Int) cfg j = .ok a := by
  cases j with
  | num n =>
    cases n with
    | int i => exact ⟨i, rfl⟩
    | float d => exact absurd rfl (hlit d)
    | _ => simp [Conforms, JsonSchema.schema, Schema.check, JsonKind.isIntegral, Num.isIntegral] at h
  | _ => simp [Conforms, JsonSchema.schema, Schema.check, JsonKind.isIntegral] at h

/-- `Optional` preserves completeness. -/
theorem schema_complete_option {α : Type} [FromJson α] [JsonSchema α] (cfg : Cfg)
    (h : SchemaComplete α cfg) : SchemaComplete (Option α) cfg := by
  intro j hj
  cases j with
  | null => exact ⟨none, rfl⟩
  | _ =>
    rcases (nullable_anyOf _).1 hj with hn | hj
    · cases hn
    · obtain ⟨a, ha⟩ := h _ hj
      exact ⟨some a, show (fromJson (α := α) cfg _).map some = _ by rw [ha]; rfl⟩

end LeanPydantic
