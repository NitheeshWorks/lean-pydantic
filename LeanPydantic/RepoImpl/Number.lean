import LeanPydantic.DataTypes

/-!
# RepoImpl: numbers

`LeanJson.Decimal` is this library's `float`: an exact decimal (see the
deviation in `CONTRIBUTING.md`). Here it gets its order and divisibility,
compared exactly by scaling both sides to the smaller exponent, so that it can
carry Keel's `gt ge lt le multipleOf` constraints. `Number` (a JSON number,
integer or decimal) gets the same relations, which are what the JSON Schema
keywords `minimum`, `exclusiveMinimum`, ... mean.

`Number.display` renders a number the way pydantic-core puts one into an
error message: Rust's `Display` for `i64`/`f64`, which never uses an exponent
and drops a zero fraction (`0.0` shows as `0`).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

namespace Dec

/-- The signed mantissa. -/
def signed (d : Decimal) : Int := if d.neg then -(d.mant : Int) else d.mant

/-- The value scaled to exponent `E`, exact whenever `E ≤ d.exp`. -/
def keyAt (d : Decimal) (E : Int) : Int := signed d * 10 ^ (d.exp - E).toNat

/-- The decimal of an integer. -/
def ofInt (i : Int) : Decimal := Decimal.normalize (decide (i < 0)) i.natAbs 0

/-- A relation on decimals, read off the integers both values become at
their smaller exponent. `<`, `≤` and "is a multiple of" are all of this form,
and `Proofs/Number.lean` shows any common lower exponent gives the same
answer. -/
def rel (R : Int → Int → Prop) (a b : Decimal) : Prop :=
  R (keyAt a (min a.exp b.exp)) (keyAt b (min a.exp b.exp))

/-- `a < b`, exactly. -/
def lt (a b : Decimal) : Prop := rel (· < ·) a b

/-- `a ≤ b`, exactly. -/
def le (a b : Decimal) : Prop := rel (· ≤ ·) a b

/-- `x` is an integer multiple of `k`. -/
def IsMultiple (k x : Decimal) : Prop := rel (· ∣ ·) k x

/-! ### Fast decisions

Scaling to the smaller exponent multiplies by `10 ^ gap`, and the gap is
whatever the input wrote (`1e999999999`). The deciders below never build a
power larger than the other operand, so they run in time bounded by the
sizes of the mantissas; each is proved equal to the relation it decides. -/

/-- `b ^ e % m` by repeated squaring: about `log e` products of numbers below `m`. -/
def powMod (b e m : Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powMod b (e / 2) m
    let r2 := r * r % m
    if e % 2 = 0 then r2 else r2 * b % m
termination_by e
decreasing_by omega

theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn with
  | _ e ih =>
    unfold powMod
    split
    · subst_vars; simp
    · rename_i he
      rw [ih (e / 2) (by omega)]
      have hsq : b ^ e = b ^ (e / 2) * b ^ (e / 2) * b ^ (e % 2) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      split
      · rename_i h0
        rw [hsq, h0, Nat.pow_zero, Nat.mul_one, Nat.mul_mod (b ^ (e / 2))]
      · rename_i h1
        have h1' : e % 2 = 1 := by omega
        rw [hsq, h1', Nat.pow_one, Nat.mul_mod (b ^ (e / 2) * b ^ (e / 2)) b,
          Nat.mul_mod (b ^ (e / 2)) (b ^ (e / 2)), Nat.mul_mod _ b]
        simp

theorem lt_ten_pow_of_log2 {m d : Nat} (h : Nat.log2 m < d) : m < 10 ^ d :=
  calc m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) h
    _ ≤ 10 ^ d := Nat.pow_le_pow_left (by decide) d

/-- `m₁ · 10^d < m₂`, computing no power beyond the size of `m₂`. -/
def scaledLt (m₁ d m₂ : Nat) : Bool :=
  if m₁ = 0 then decide (0 < m₂)
  else if Nat.log2 m₂ < d then false
  else decide (m₁ * 10 ^ d < m₂)

theorem scaledLt_iff (m₁ d m₂ : Nat) : scaledLt m₁ d m₂ = true ↔ m₁ * 10 ^ d < m₂ := by
  unfold scaledLt
  split
  · subst_vars; simp
  · split
    · rename_i h0 hl
      have := lt_ten_pow_of_log2 hl
      have : 10 ^ d ≤ m₁ * 10 ^ d := Nat.le_mul_of_pos_left _ (by omega)
      simp only [Bool.false_eq_true, false_iff, Nat.not_lt]; omega
    · simp

/-- `m₁ < m₂ · 10^d`, computing no power beyond the size of `m₁`. -/
def ltScaled (m₁ m₂ d : Nat) : Bool :=
  if m₂ = 0 then false
  else if Nat.log2 m₁ < d then true
  else decide (m₁ < m₂ * 10 ^ d)

theorem ltScaled_iff (m₁ m₂ d : Nat) : ltScaled m₁ m₂ d = true ↔ m₁ < m₂ * 10 ^ d := by
  unfold ltScaled
  split
  · subst_vars; simp
  · split
    · rename_i h0 hl
      have := lt_ten_pow_of_log2 hl
      have : 10 ^ d ≤ m₂ * 10 ^ d := Nat.le_mul_of_pos_left _ (by omega)
      simp only [true_iff]; omega
    · simp

/-- Magnitudes `ma·10^ea < mb·10^eb`, each scaled to the smaller exponent. -/
def magLt (ma : Nat) (ea : Int) (mb : Nat) (eb : Int) : Bool :=
  if eb ≤ ea then scaledLt ma (ea - eb).toNat mb else ltScaled ma mb (eb - ea).toNat

theorem magLt_iff (ma : Nat) (ea : Int) (mb : Nat) (eb : Int) :
    magLt ma ea mb eb = true ↔ ma * 10 ^ (ea - min ea eb).toNat < mb * 10 ^ (eb - min ea eb).toNat := by
  unfold magLt
  split
  · rename_i h
    rw [scaledLt_iff, show min ea eb = eb by omega, show (eb - eb).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
  · rename_i h
    rw [ltScaled_iff, show min ea eb = ea by omega, show (ea - ea).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]



/-- A signed magnitude. -/
def sgnMul (n : Bool) (M : Nat) : Int := if n then -(M : Int) else M

theorem natAbs_sgnMul (n : Bool) (M : Nat) : (sgnMul n M).natAbs = M := by
  unfold sgnMul; split <;> simp

/-- `±ma·10^ea < ±mb·10^eb`, never building a power larger than the inputs. -/
def ltCore (na : Bool) (ma : Nat) (ea : Int) (nb : Bool) (mb : Nat) (eb : Int) : Bool :=
  match na, nb with
  | false, false => magLt ma ea mb eb
  | false, true => false
  | true, false => ma != 0 || mb != 0
  | true, true => magLt mb eb ma ea

theorem ltCore_iff (na : Bool) (ma : Nat) (ea : Int) (nb : Bool) (mb : Nat) (eb : Int) :
    ltCore na ma ea nb mb eb = true ↔
      sgnMul na (ma * 10 ^ (ea - min ea eb).toNat) < sgnMul nb (mb * 10 ^ (eb - min ea eb).toNat) := by
  have hp : ∀ k : Nat, 0 < 10 ^ k := fun k => Nat.pow_pos (by decide)
  cases na <;> cases nb <;> simp only [ltCore, sgnMul, Bool.false_eq_true, ite_false, ite_true]
  · rw [magLt_iff]; omega
  · constructor
    · intro h; cases h
    · intro h; omega
  · have h1 := hp (ea - min ea eb).toNat
    have h2 := hp (eb - min ea eb).toNat
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true]
    constructor
    · intro h
      rcases h with h | h
      · have : 0 < ma * 10 ^ (ea - min ea eb).toNat := Nat.mul_pos (by omega) h1
        omega
      · have : 0 < mb * 10 ^ (eb - min ea eb).toNat := Nat.mul_pos (by omega) h2
        omega
    · intro h
      by_cases hm : ma = 0
      · subst hm; right; intro hb; subst hb; simp at h
      · left; exact hm
  · rw [magLt_iff, Int.min_comm eb ea]; omega

/-- `mk·10^ek ∣ mx·10^ex` (scaled to the smaller exponent), in time bounded by
the sizes of the inputs, not by the exponent gap. -/
def dvdCore (mk : Nat) (ek : Int) (mx : Nat) (ex : Int) : Bool :=
  if ex ≤ ek then
    if mk = 0 then mx == 0
    else if mx = 0 then true
    else if Nat.log2 mx < (ek - ex).toNat then false
    else mx % (mk * 10 ^ (ek - ex).toNat) == 0
  else
    if mk = 0 then mx == 0
    else mx * powMod 10 (ex - ek).toNat mk % mk == 0

theorem dvdCore_iff (mk : Nat) (ek : Int) (mx : Nat) (ex : Int) :
    dvdCore mk ek mx ex = true ↔
      mk * 10 ^ (ek - min ek ex).toNat ∣ mx * 10 ^ (ex - min ek ex).toNat := by
  have hp : ∀ k : Nat, 0 < 10 ^ k := fun k => Nat.pow_pos (by decide)
  unfold dvdCore
  split
  · rename_i hle
    rw [show min ek ex = ex by omega, show (ex - ex).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
    split
    · subst_vars; simp
    · rename_i hk
      split
      · subst_vars; simp
      · rename_i hx
        split
        · rename_i hl
          have h10 := lt_ten_pow_of_log2 hl
          simp only [Bool.false_eq_true, false_iff]
          intro hd
          have := Nat.le_of_dvd (by omega) hd
          have : 10 ^ (ek - ex).toNat ≤ mk * 10 ^ (ek - ex).toNat := Nat.le_mul_of_pos_left _ (by omega)
          omega
        · simp [Nat.dvd_iff_mod_eq_zero]
  · rename_i hlt
    rw [show min ek ex = ek by omega, show (ek - ek).toNat = 0 by omega, Nat.pow_zero, Nat.mul_one]
    split
    · subst_vars
      simp only [beq_iff_eq, Nat.zero_dvd]
      have := hp (ex - ek).toNat
      constructor
      · intro h; subst h; simp
      · intro h; rcases Nat.mul_eq_zero.1 h with h | h
        · exact h
        · omega
    · simp only [beq_iff_eq, Nat.dvd_iff_mod_eq_zero, powMod_eq]
      rw [Nat.mul_mod mx (10 ^ _ % mk), Nat.mod_mod, ← Nat.mul_mod]


theorem keyAt_sgn (d : Decimal) (E : Int) :
    keyAt d E = sgnMul d.neg (d.mant * 10 ^ (d.exp - E).toNat) := by
  unfold keyAt signed sgnMul; split <;> push_cast <;> simp [Int.neg_mul]

theorem lt_iff_core (a b : Decimal) :
    lt a b ↔ ltCore a.neg a.mant a.exp b.neg b.mant b.exp = true := by
  rw [ltCore_iff]; unfold lt rel; simp only [keyAt_sgn]

theorem le_iff_core (a b : Decimal) :
    le a b ↔ ltCore b.neg b.mant b.exp a.neg a.mant a.exp = false := by
  rw [← Bool.not_eq_true, ltCore_iff]; unfold le rel
  simp only [keyAt_sgn, Int.min_comm b.exp a.exp]; omega

theorem isMultiple_iff_core (k x : Decimal) :
    IsMultiple k x ↔ dvdCore k.mant k.exp x.mant x.exp = true := by
  rw [dvdCore_iff]; unfold IsMultiple rel; simp only [keyAt_sgn]
  rw [← Int.natAbs_dvd_natAbs, natAbs_sgnMul, natAbs_sgnMul]

end Dec

instance : LT Decimal := ⟨Dec.lt⟩
instance : LE Decimal := ⟨Dec.le⟩
instance (a b : Decimal) : Decidable (a < b) := decidable_of_iff _ (Dec.lt_iff_core a b).symm
instance (a b : Decimal) : Decidable (a ≤ b) := decidable_of_iff _ (Dec.le_iff_core a b).symm

instance : Keel.Ordered Decimal := { decLT := inferInstance, decLE := inferInstance }
instance : Keel.Divisible Decimal := ⟨Dec.IsMultiple, fun k x => decidable_of_iff _ (Dec.isMultiple_iff_core k x).symm⟩

namespace Num

/-- A finite JSON number as a decimal (non-finite ones, which only the
lenient parser produces, map to `0`; validators reject them before this is
used). -/
def toDecimal : Number → Decimal
  | .int i => Dec.ofInt i
  | .float d => d
  | _ => Dec.ofInt 0

/-- The exponent a number is written at (`0` for an integer). -/
def exp : Number → Int
  | .float d => d.exp
  | _ => 0

/-- The value scaled to exponent `E`, exact whenever `E ≤ exp n` (finite
numbers only). -/
def keyAt : Number → Int → Int
  | .int i, E => i * 10 ^ (-E).toNat
  | .float d, E => Dec.keyAt d E
  | _, _ => 0

/-- A relation on JSON numbers, at their smaller exponent. -/
def rel (R : Int → Int → Prop) (a b : Number) : Prop :=
  R (keyAt a (min (exp a) (exp b))) (keyAt b (min (exp a) (exp b)))

/-- `a < b` on JSON numbers (what `exclusiveMinimum` means). -/
def lt (a b : Number) : Prop := rel (· < ·) a b

/-- `a ≤ b` on JSON numbers (what `minimum` means). -/
def le (a b : Number) : Prop := rel (· ≤ ·) a b

/-- `x` is an integer multiple of `k` (what `multipleOf` means). -/
def IsMultiple (k x : Number) : Prop := rel (· ∣ ·) k x

/-- The sign of a number as a decimal (non-finite ones read as `0`). -/
def sgn : Number → Bool
  | .int i => decide (i < 0)
  | .float d => d.neg
  | _ => false

/-- The magnitude's mantissa (non-finite ones read as `0`). -/
def mag : Number → Nat
  | .int i => i.natAbs
  | .float d => d.mant
  | _ => 0

theorem keyAt_sgn (n : Number) (E : Int) :
    keyAt n E = Dec.sgnMul (sgn n) (mag n * 10 ^ (exp n - E).toNat) := by
  cases n with
  | int i =>
    simp only [keyAt, sgn, mag, exp, Dec.sgnMul, Int.zero_sub]
    by_cases h : i < 0
    · simp only [h, decide_true, ite_true]; push_cast
      rw [Int.neg_mul_eq_neg_mul, show -(i.natAbs : Int) = i by omega]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; push_cast
      rw [show (i.natAbs : Int) = i by omega]
  | float d => simp only [keyAt, sgn, mag, exp, Dec.keyAt_sgn]
  | _ => simp [keyAt, sgn, mag, exp, Dec.sgnMul]

theorem lt_iff_core (a b : Number) :
    lt a b ↔ Dec.ltCore (sgn a) (mag a) (exp a) (sgn b) (mag b) (exp b) = true := by
  rw [Dec.ltCore_iff]; unfold lt rel; simp only [keyAt_sgn]

theorem le_iff_core (a b : Number) :
    le a b ↔ Dec.ltCore (sgn b) (mag b) (exp b) (sgn a) (mag a) (exp a) = false := by
  rw [← Bool.not_eq_true, Dec.ltCore_iff]; unfold le rel
  simp only [keyAt_sgn, Int.min_comm (exp b) (exp a)]; omega

theorem isMultiple_iff_core (k x : Number) :
    IsMultiple k x ↔ Dec.dvdCore (mag k) (exp k) (mag x) (exp x) = true := by
  rw [Dec.dvdCore_iff]; unfold IsMultiple rel; simp only [keyAt_sgn]
  rw [← Int.natAbs_dvd_natAbs, Dec.natAbs_sgnMul, Dec.natAbs_sgnMul]

instance (a b : Number) : Decidable (lt a b) := decidable_of_iff _ (lt_iff_core a b).symm
instance (a b : Number) : Decidable (le a b) := decidable_of_iff _ (le_iff_core a b).symm
instance (a b : Number) : Decidable (IsMultiple a b) := decidable_of_iff _ (isMultiple_iff_core a b).symm

/-- A decimal as a JSON number: an integer when it is one (pydantic's schema
keeps a bound written `0` as `0`), else the decimal. -/
def ofDecimal (d : Decimal) : Number :=
  if d.exp < 0 then .float d else .int (Dec.keyAt d 0)

/-- `n` zeros. -/
def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Rust's `Display` of the value: plain digits with a point where needed,
never an exponent, no trailing fraction zeros; `NaN`, `inf`, `-inf`. -/
def display : Number → String
  | .int i => toString i
  | .nan => "NaN"
  | .inf => "inf"
  | .negInf => "-inf"
  | .float d =>
    let sign := if d.neg then "-" else ""
    let digits := toString d.mant
    if 0 ≤ d.exp then sign ++ digits ++ zeros d.exp.toNat
    else
      let k := (-d.exp).toNat
      if digits.length > k then
        sign ++ String.ofList (digits.toList.take (digits.length - k)) ++ "." ++
          String.ofList (digits.toList.drop (digits.length - k))
      else sign ++ "0." ++ zeros (k - digits.length) ++ digits

end Num

end LeanPydantic

namespace LeanPydantic

open LeanJson (Decimal)

/-- `Decimal` numerals: `0`, `100`. -/
instance (n : Nat) : OfNat Decimal n := ⟨Dec.ofInt n⟩
/-- `Decimal` literals: `1.5`, `2e-3`, exact. -/
instance : OfScientific Decimal := ⟨fun m s e => Decimal.normalize false m (if s then -(e : Int) else e)⟩
instance : Neg Decimal := ⟨fun d => { d with neg := !d.neg, h_norm := d.h_norm }⟩
instance : ToString Decimal := ⟨fun d => Num.display (.float d)⟩

end LeanPydantic
