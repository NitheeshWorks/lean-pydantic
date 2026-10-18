import LeanPydantic.Specifications

/-!
# Proofs: exact comparison of decimals and JSON numbers

One idea: a relation `R` on integers that is invariant under scaling both
sides by a positive factor (`<`, `≤`, `∣`) can be read at *any* common
exponent at or below both numbers' exponents (`Num.rel_at`, `Dec.rel_at`).
Everything else is an instance: integers compare as integers
(`Num.rel_int`), a JSON number compares like the decimal it validates to,
and a bound printed in a schema compares like the bound
(`Num.rel_ofDecimal`).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

/-- Relations unchanged by scaling both sides by a positive integer. -/
def ScaleInvariant (R : Int → Int → Prop) : Prop :=
  ∀ x y p : Int, 0 < p → (R (x * p) (y * p) ↔ R x y)

theorem scaleInvariant_lt : ScaleInvariant (· < ·) := fun _ _ _ hp => Int.mul_lt_mul_right hp
theorem scaleInvariant_le : ScaleInvariant (· ≤ ·) := fun _ _ _ hp => Int.mul_le_mul_right hp
theorem scaleInvariant_dvd : ScaleInvariant (· ∣ ·) := fun _ _ _ hp =>
  Int.mul_dvd_mul_iff_right (Int.ne_of_gt hp)

theorem pow_ten_pos (n : Nat) : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)

theorem pow_split (a b c : Int) (h1 : b ≤ a) (h2 : c ≤ b) :
    (10 : Int) ^ (a - c).toNat = 10 ^ (a - b).toNat * 10 ^ (b - c).toNat := by
  rw [← Int.pow_add]; congr 1; omega

namespace Dec

theorem keyAt_lower (d : Decimal) {E E' : Int} (h : E' ≤ E) (hE : E ≤ d.exp) :
    keyAt d E' = keyAt d E * 10 ^ (E - E').toNat := by
  unfold keyAt; rw [pow_split d.exp E E' hE h, Int.mul_assoc]

/-- A scale-invariant relation can be read at any common lower exponent. -/
theorem rel_at {R : Int → Int → Prop} (hR : ScaleInvariant R) (a b : Decimal) {E : Int}
    (hE : E ≤ min a.exp b.exp) : rel R a b ↔ R (keyAt a E) (keyAt b E) := by
  unfold rel
  rw [keyAt_lower a hE (Int.min_le_left _ _), keyAt_lower b hE (Int.min_le_right _ _)]
  exact (hR _ _ _ (pow_ten_pos _)).symm

theorem ofInt_exp (i : Int) : 0 ≤ (ofInt i).exp := by
  unfold ofInt Decimal.normalize; split <;> simp

/-- The decimal of an integer has the integer's value. -/
theorem keyAt_ofInt (i : Int) {E : Int} (hE : E ≤ 0) : keyAt (ofInt i) E = i * 10 ^ (-E).toNat := by
  unfold keyAt signed ofInt Decimal.normalize
  split
  · rename_i h; have : i = 0 := Int.natAbs_eq_zero.1 h
    subst this; simp
  · rename_i h
    have hd := Nat.dvd_of_mod_eq_zero (LeanJson.trailingZeros_spec i.natAbs h).1
    simp only
    have key : ((i.natAbs / 10 ^ LeanJson.trailingZeros i.natAbs : Nat) : Int) *
        10 ^ ((0 + (LeanJson.trailingZeros i.natAbs : Int)) - E).toNat = (i.natAbs : Int) * 10 ^ (-E).toNat := by
      rw [pow_split _ 0 E (by omega) hE, ← Int.mul_assoc, show (0 : Int) - E = -E by omega]
      have : ((0 + (LeanJson.trailingZeros i.natAbs : Int)) - 0).toNat = LeanJson.trailingZeros i.natAbs := by omega
      rw [this]
      congr 1
      exact_mod_cast Nat.div_mul_cancel hd
    by_cases hi : i < 0
    · simp only [hi, decide_true, ite_true]
      rw [Int.neg_mul, key, show (i.natAbs : Int) = -i by omega, Int.neg_mul, Int.neg_neg]
    · simp only [hi, decide_false, Bool.false_eq_true, ite_false]
      rw [key, show (i.natAbs : Int) = i by omega]

end Dec

namespace Num

theorem keyAt_lower (n : Number) {E E' : Int} (h : E' ≤ E) (hE : E ≤ exp n) :
    keyAt n E' = keyAt n E * 10 ^ (E - E').toNat := by
  cases n with
  | int i =>
    simp only [keyAt, exp] at *
    rw [show -E' = 0 - E' by omega, show -E = 0 - E by omega, pow_split 0 E E' hE h, Int.mul_assoc]
  | float d => exact Dec.keyAt_lower d h hE
  | nan | inf | negInf => simp [keyAt]

/-- A scale-invariant relation can be read at any common lower exponent. -/
theorem rel_at {R : Int → Int → Prop} (hR : ScaleInvariant R) (a b : Number) {E : Int}
    (hE : E ≤ min (exp a) (exp b)) : rel R a b ↔ R (keyAt a E) (keyAt b E) := by
  unfold rel
  rw [keyAt_lower a hE (Int.min_le_left _ _), keyAt_lower b hE (Int.min_le_right _ _)]
  exact (hR _ _ _ (pow_ten_pos _)).symm

/-- Integers compare as integers. -/
theorem rel_int {R : Int → Int → Prop} (a b : Int) : rel R (.int a) (.int b) ↔ R a b := by
  simp [rel, keyAt, exp]

/-- A JSON number has the value of the decimal it validates to. -/
theorem keyAt_toDecimal (n : Number) {E : Int} (h0 : E ≤ 0) :
    Dec.keyAt (toDecimal n) E = keyAt n E := by
  cases n with
  | int i => exact Dec.keyAt_ofInt i h0
  | float d => rfl
  | nan | inf | negInf => simpa [keyAt, toDecimal] using Dec.keyAt_ofInt 0 h0

/-- A bound as the schema prints it has the bound's value. -/
theorem keyAt_ofDecimal (d : Decimal) {E : Int} (h0 : E ≤ 0) :
    keyAt (ofDecimal d) E = Dec.keyAt d E := by
  unfold ofDecimal
  split
  · rfl
  · simp only [keyAt]
    rw [Dec.keyAt_lower d h0 (by omega)]; simp

/-- `a` has the value of `d`: they agree at every common low exponent. -/
def Denotes (a : Number) (d : Decimal) : Prop :=
  ∀ E : Int, E ≤ 0 → E ≤ exp a → E ≤ d.exp → keyAt a E = Dec.keyAt d E

theorem denotes_toDecimal (n : Number) : Denotes n (toDecimal n) :=
  fun _ h0 _ _ => (keyAt_toDecimal n h0).symm

theorem denotes_ofDecimal (d : Decimal) : Denotes (ofDecimal d) d :=
  fun _ h0 _ _ => keyAt_ofDecimal d h0

theorem denotes_float (d : Decimal) : Denotes (.float d) d := fun _ _ _ _ => rfl

/-- Numbers relate as the decimals they denote. -/
theorem rel_denotes {R : Int → Int → Prop} (hR : ScaleInvariant R) {a b : Number} {d e : Decimal}
    (ha : Denotes a d) (hb : Denotes b e) : rel R a b ↔ Dec.rel R d e := by
  let E := min (min 0 (min (exp a) (exp b))) (min d.exp e.exp)
  rw [rel_at hR a b (E := E) (by omega), Dec.rel_at hR d e (E := E) (by omega),
    ha E (by omega) (by omega) (by omega), hb E (by omega) (by omega) (by omega)]

end Num

end LeanPydantic
