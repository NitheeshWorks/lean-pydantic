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

end Dec

instance : LT Decimal := ⟨Dec.lt⟩
instance : LE Decimal := ⟨Dec.le⟩
instance (a b : Decimal) : Decidable (a < b) := Int.decLt _ _
instance (a b : Decimal) : Decidable (a ≤ b) := Int.decLe _ _

instance : Keel.Ordered Decimal := { decLT := inferInstance, decLE := inferInstance }
instance : Keel.Divisible Decimal := ⟨Dec.IsMultiple, fun _ _ => inferInstanceAs (Decidable (_ ∣ _))⟩

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

instance (a b : Number) : Decidable (lt a b) := Int.decLt _ _
instance (a b : Number) : Decidable (le a b) := Int.decLe _ _
instance (a b : Number) : Decidable (IsMultiple a b) := inferInstanceAs (Decidable (_ ∣ _))

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
