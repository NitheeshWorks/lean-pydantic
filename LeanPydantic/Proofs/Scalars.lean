import LeanPydantic.Proofs.Constraint
import LeanPydantic.Proofs.Number

/-!
# Proofs: the laws of the scalar types, `Option` and refinements

Each scalar's laws are short case analyses on the JSON value. `Option α` and
`α ∣ c` get their laws from `α`'s, once, for every `α`: the refinement's
schema is sound by `keywordsOf_sound`, so a new carrier type needs only its
`LawfulConstrained` instance, and the numeric ones share
`numeric_keywords_sound`.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

theorem liftKind_ne_nil {α : Type} (cfg : Cfg) (j : Json) (r : Except ErrorKind α) :
    liftKind cfg j r ≠ .error [] := by
  cases r <;> simp [liftKind]

theorem liftKind_ok {α : Type} {cfg : Cfg} {j : Json} {r : Except ErrorKind α} {a : α} :
    liftKind cfg j r = .ok a ↔ r = .ok a := by
  cases r <;> simp [liftKind]

theorem fromJson_int (cfg : Cfg) (j : Json) :
    fromJson (α := Int) cfg j = liftKind cfg j (Scalar.int cfg.strict j) := rfl
theorem fromJson_nat (cfg : Cfg) (j : Json) :
    fromJson (α := Nat) cfg j = liftKind cfg j (Scalar.nat cfg.strict j) := rfl
theorem fromJson_decimal (cfg : Cfg) (j : Json) :
    fromJson (α := Decimal) cfg j = liftKind cfg j (Scalar.float cfg.strict j) := rfl
theorem fromJson_bool (cfg : Cfg) (j : Json) :
    fromJson (α := Bool) cfg j = liftKind cfg j (Scalar.bool cfg.strict j) := rfl
theorem fromJson_string (cfg : Cfg) (j : Json) :
    fromJson (α := String) cfg j = liftKind cfg j (Scalar.str j) := rfl

/-! ## Strict validation pins the input down -/

theorem int_strict {j : Json} {x : Int} (h : Scalar.int true j = .ok x) : j = .num (.int x) := by
  cases j with
  | num n => cases n <;> simp_all [Scalar.int]
  | _ => simp [Scalar.int] at h

theorem nat_strict {j : Json} {x : Nat} (h : Scalar.nat true j = .ok x) : j = .num (.int x) := by
  unfold Scalar.nat at h
  split at h
  · rename_i i hi
    split at h
    · rename_i h0; cases h; rw [int_strict hi]; congr; omega
    · cases h
  · cases h

theorem float_strict {j : Json} {x : Decimal} (h : Scalar.float true j = .ok x) :
    ∃ n, j = .num n ∧ n.isFinite = true ∧ x = Num.toDecimal n := by
  cases j <;> simp [Scalar.float] at h
  rename_i n
  split at h
  · cases h; exact ⟨n, rfl, by assumption, rfl⟩
  · cases h

theorem bool_strict {j : Json} {x : Bool} (h : Scalar.bool true j = .ok x) : j = .bool x := by
  cases j with
  | num n => cases n <;> simp_all [Scalar.bool]
  | _ => simp_all [Scalar.bool]

theorem str_strict {j : Json} {x : String} (h : Scalar.str j = .ok x) : j = .str x := by
  cases j <;> simp_all [Scalar.str]

/-! ## The scalar laws -/

instance : LawfulJson Int where
  fromJson_toJson _ _ := rfl
  schema_sound cfg j a hs h := by
    rw [fromJson_int, liftKind_ok, hs] at h
    rw [int_strict h]
    show Schema.check (.integer []) _ = true
    simp [Schema.check, JsonKind.isIntegral, Num.isIntegral]
  errors_ne_nil cfg j := liftKind_ne_nil cfg j _

instance : LawfulJson Nat where
  fromJson_toJson cfg n := by
    rw [fromJson_nat]
    simp [Scalar.nat, Scalar.int, liftKind, ToJson.toJson]
  schema_sound cfg j a hs h := by
    rw [fromJson_nat, liftKind_ok, hs] at h
    rw [nat_strict h]
    show Schema.check (.integer [.minimum (.int 0)]) _ = true
    simp [Schema.check, JsonKind.isIntegral, Num.isIntegral, Keyword.check, Num.le, Num.rel_int,
      LeanJson.Number.isFinite]
  errors_ne_nil cfg j := liftKind_ne_nil cfg j _

instance : LawfulJson Decimal where
  fromJson_toJson _ _ := rfl
  schema_sound cfg j a hs h := by
    rw [fromJson_decimal, liftKind_ok, hs] at h
    obtain ⟨n, rfl, -, -⟩ := float_strict h
    show Schema.check (.number []) _ = true
    simp [Schema.check, JsonKind.isNum]
  errors_ne_nil cfg j := liftKind_ne_nil cfg j _

instance : LawfulJson Bool where
  fromJson_toJson _ _ := rfl
  schema_sound cfg j a hs h := by
    rw [fromJson_bool, liftKind_ok, hs] at h
    rw [bool_strict h]
    show Schema.check .boolean _ = true
    simp [Schema.check, JsonKind.isBool]
  errors_ne_nil cfg j := liftKind_ne_nil cfg j _

instance : LawfulJson String where
  fromJson_toJson _ _ := rfl
  schema_sound cfg j a _ h := by
    rw [fromJson_string, liftKind_ok] at h
    rw [str_strict h]
    show Schema.check (.string []) _ = true
    simp [Schema.check, JsonKind.isStr]
  errors_ne_nil cfg j := liftKind_ne_nil cfg j _

instance : NonNull Int := ⟨fun _ _ => nofun⟩
instance : NonNull Nat := ⟨fun _ _ => nofun⟩
instance : NonNull Decimal := ⟨fun _ _ => nofun⟩
instance : NonNull Bool := ⟨fun _ _ => nofun⟩
instance : NonNull String := ⟨fun _ _ => nofun⟩

/-! ## Constraint keywords -/

/-- The keywords of a numeric type's atoms hold on a number `n` whenever the
type's relations on the validated value carry over to `n`. -/
theorem numeric_keywords_sound {α : Type} {O : Keel.Ordered α} {D : Keel.Divisible α}
    {ctx : α → Json} {schema : α → Number} {x : α} {n : Number} (hfin : n.isFinite = true)
    (hgt : ∀ b, @LT.lt α O.toLT b x → Num.lt (schema b) n)
    (hge : ∀ b, @LE.le α O.toLE b x → Num.le (schema b) n)
    (hlt : ∀ b, @LT.lt α O.toLT x b → Num.lt n (schema b))
    (hle : ∀ b, @LE.le α O.toLE x b → Num.le n (schema b))
    (hdvd : ∀ k, D.IsMultiple k x → Num.IsMultiple (schema k) n)
    (a : Constraint α) (hstd : (Constrained.numeric O D ctx schema).Std a) (h : a.holds x) :
    ∀ k ∈ (Constrained.numeric O D ctx schema).keywords a, k.check (.num n) = true := by
  intro k hk
  unfold Constrained.numeric at hk hstd
  cases a <;> simp only at hstd hk <;> subst_vars <;> simp_all [Constraint.holds, Keyword.check]

instance : LawfulConstrained Int where
  keywords_sound cfg j x a hstd hs hv h := by
    rw [fromJson_int, liftKind_ok, hs] at hv
    rw [int_strict hv]
    exact numeric_keywords_sound rfl (fun _ h => (Num.rel_int _ _).2 h) (fun _ h => (Num.rel_int _ _).2 h)
      (fun _ h => (Num.rel_int _ _).2 h) (fun _ h => (Num.rel_int _ _).2 h)
      (fun _ h => (Num.rel_int _ _).2 h) a hstd h

instance : LawfulConstrained Nat where
  keywords_sound cfg j x a hstd hs hv h := by
    rw [fromJson_nat, liftKind_ok, hs] at hv
    rw [nat_strict hv]
    exact numeric_keywords_sound rfl
      (fun _ h => (Num.rel_int _ _).2 (by show (_ : Int) < _; omega))
      (fun _ h => (Num.rel_int _ _).2 (by show (_ : Int) ≤ _; omega))
      (fun _ h => (Num.rel_int _ _).2 (by show (_ : Int) < _; omega))
      (fun _ h => (Num.rel_int _ _).2 (by show (_ : Int) ≤ _; omega))
      (fun _ h => (Num.rel_int _ _).2 (Int.natCast_dvd_natCast.2 h)) a hstd h

instance : LawfulConstrained Decimal where
  keywords_sound cfg j x a hstd hs hv h := by
    rw [fromJson_decimal, liftKind_ok, hs] at hv
    obtain ⟨n, rfl, hfin, rfl⟩ := float_strict hv
    have hb := Num.denotes_ofDecimal
    have hn := Num.denotes_toDecimal n
    exact numeric_keywords_sound hfin
      (fun b h => (Num.rel_denotes scaleInvariant_lt (hb b) hn).2 h)
      (fun b h => (Num.rel_denotes scaleInvariant_le (hb b) hn).2 h)
      (fun b h => (Num.rel_denotes scaleInvariant_lt hn (hb b)).2 h)
      (fun b h => (Num.rel_denotes scaleInvariant_le hn (hb b)).2 h)
      (fun b h => (Num.rel_denotes scaleInvariant_dvd (hb b) hn).2 h) a hstd h

instance : LawfulConstrained String where
  keywords_sound cfg j x a hstd _ hv h := by
    rw [fromJson_string, liftKind_ok] at hv
    rw [str_strict hv]
    intro k hk
    unfold constrainedString at hk hstd
    cases a <;> simp only at hk
    case minLength | maxLength | pattern =>
      obtain rfl : _ = _ := hstd
      simp only [List.mem_singleton] at hk; subst hk
      simpa [Keyword.check, Constraint.holds, Keel.Sized.size, Keel.Textual.text] using h
    all_goals simp at hk

end LeanPydantic
