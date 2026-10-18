import LeanPydantic.RepoImpl.Functional
import LeanPydantic.RepoImpl.Regex.Match

/-!
# RepoImpl: Python's `decimal.Decimal`

`PyDecimal` is pydantic's `Decimal` field type: a finite decimal with its
sign, coefficient and exponent, as `Decimal.as_tuple()` gives them, so
trailing zeros are kept (`Decimal("2.50")` dumps as `"2.50"`).
`Condecimal max_digits decimal_places` adds pydantic's digit limits
(`condecimal(max_digits=…, decimal_places=…)`, `Field(max_digits=…)`).
The bounds `gt`, `ge`, `lt`, `le`, `multiple_of` are the usual refinement:
`Condecimal (some 5) (some 2) ∣ gt 0`.

As in pydantic-core:

* JSON: an integer is exact; a float is parsed as an `f64` (`1e400` is
  `finite_number`) and read as Rust prints it
  (no exponent, `1e3` is `1000`); a string is parsed as `Decimal(str)`
  does; anything else is `decimal_type`.
* Python (lax): the same, except that a float goes through `str(float)`
  (`1e3` is `1000.0`, `1e-5` is `1E-5`); strict wants a `Decimal`
  instance, so every input is `is_instance_of`.
* `NaN` and the infinities are `finite_number`.
* The dump is `str(Decimal)`, a JSON string.

Deviations (tests in `tests/Conformance.lean`): only ASCII digits are read
in strings (Python also reads other Unicode decimal digits), and a float is
held as the decimal written in the JSON, which is what Rust and Python print
for it whenever it has at most 15 significant digits.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

/-- A finite Python `Decimal`: `(-1)^neg × coeff × 10^exp`. -/
structure PyDecimal where
  neg : Bool
  coeff : Nat
  exp : Int
  deriving DecidableEq, Repr, Inhabited

namespace PyDecimal

/-- The number, normalised. -/
def value (d : PyDecimal) : Decimal := Decimal.normalize d.neg d.coeff d.exp

instance : LT PyDecimal := ⟨fun a b => a.value < b.value⟩
instance : LE PyDecimal := ⟨fun a b => a.value ≤ b.value⟩
instance : Keel.Ordered PyDecimal :=
  { decLT := fun a b => inferInstanceAs (Decidable (a.value < b.value)),
    decLE := fun a b => inferInstanceAs (Decidable (a.value ≤ b.value)) }
instance : Keel.Divisible PyDecimal :=
  ⟨fun k x => Keel.Divisible.IsMultiple k.value x.value, fun k x => Keel.Divisible.dec k.value x.value⟩
instance {n : Nat} : OfNat PyDecimal n := ⟨⟨false, n, 0⟩⟩
/-- `2.50` is `Decimal("2.50")`: the literal's digits, trailing zeros kept. -/
instance : OfScientific PyDecimal := ⟨fun m s e => ⟨false, m, if s then -(e : Int) else e⟩⟩
instance : Neg PyDecimal := ⟨fun d => { d with neg := !d.neg }⟩

/-- `"0"` repeated. -/
def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- `str(Decimal)`: Python's to-scientific-string. -/
def toPy (d : PyDecimal) : String :=
  let s := (toString d.coeff).toList
  let len : Int := s.length
  let leftdigits := d.exp + len
  let dotplace : Int := if d.exp ≤ 0 ∧ leftdigits > -6 then leftdigits else 1
  let body :=
    if dotplace ≤ 0 then "0." ++ zeros (-dotplace).toNat ++ String.ofList s
    else if dotplace ≥ len then String.ofList s ++ zeros (dotplace - len).toNat
    else String.ofList (s.take dotplace.toNat) ++ "." ++ String.ofList (s.drop dotplace.toNat)
  let e := leftdigits - dotplace
  let expPart := if e = 0 then "" else "E" ++ (if e > 0 then "+" else "") ++ toString e
  (if d.neg then "-" else "") ++ body ++ expPart

instance : ToString PyDecimal := ⟨toPy⟩

/-- An integer. -/
def ofInt (i : Int) : PyDecimal := ⟨i < 0, i.natAbs, 0⟩

/-- The literal read as an `f64`, as its shortest decimal digits; `none` if
it overflows to an infinity. -/
def asDouble (d : Decimal) : Option Decimal :=
  let x := (Number.float d).toFloat
  if !x.isFinite then none else
  match Number.ofFloat x with
  | .float e => some e
  | _ => none

/-- A JSON float as pydantic-core reads it: the literal is parsed as an
`f64` (so `1e400` is `inf`, and `none` here), then `Decimal` of Rust's
display of it, which has no exponent and no `.0`. The double's shortest
digits have an exponent of at most 308, so the scaling is bounded. -/
def ofRust (d : Decimal) : Option PyDecimal :=
  (asDouble d).map fun e => if e.exp ≥ 0 then ⟨e.neg, e.mant * 10 ^ e.exp.toNat, 0⟩ else ⟨e.neg, e.mant, e.exp⟩

/-- A Python float as pydantic reads it: `Decimal(str(float))`. `repr`
writes `1000.0` (fixed, with `.0`) for a decimal exponent in `[-4, 16)` and
`1e+16` otherwise. A literal that overflows the double is `inf`, so
`none`. -/
def ofRepr (d : Decimal) : Option PyDecimal :=
  (asDouble d).map fun d =>
    let adj : Int := d.exp + (toString d.mant).length - 1
    if -4 ≤ adj ∧ adj < 16 ∧ d.exp ≥ 0 then ⟨d.neg, d.mant * 10 ^ d.exp.toNat * 10, -1⟩
    else ⟨d.neg, d.mant, d.exp⟩

/-- The leading digits, and what follows. -/
def digitRun : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if c.isDigit then
      let (ds, r) := digitRun rest
      (c :: ds, r)
    else ([], c :: rest)

/-- Digits as a number. -/
def digitsValue (ds : List Char) : Nat := Coerce.digitsVal ds

/-- What `Decimal(s)` makes of a string. -/
inductive Parsed where
  | finite (d : PyDecimal)
  | nonFinite
  | invalid

/-- `NaN`, `sNaN` (with an optional payload), `Inf`, `Infinity`, any case. -/
def isNonFinite (cs : List Char) : Bool :=
  let low := String.ofList (cs.map Char.toLower)
  let payload (p : String) := low.startsWith p && (low.drop p.length).all Char.isDigit
  low = "inf" || low = "infinity" || payload "nan" || payload "snan"

/-- Python's `Decimal(s)` on a string: surrounding white space stripped,
and every underscore dropped (CPython's `decimal` accepts `1_000`, and also
`_1` and `1__0`). -/
def parse (s : String) : Parsed :=
  let cs := ((s.toList.dropWhile Regex.isSpace).reverse.dropWhile Regex.isSpace).reverse.filter (· ≠ '_')
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if isNonFinite cs then .nonFinite else
  let (ip, r) := digitRun cs
  let (fp, r) := match r with
    | '.' :: r' => digitRun r'
    | r => ([], r)
  if ip.isEmpty && fp.isEmpty then .invalid else
  let ex : Option (Int × List Char) := match r with
    | c :: r' =>
      if c = 'e' || c = 'E' then
        let (eneg, r'') := match r' with
          | '-' :: x => (true, x)
          | '+' :: x => (false, x)
          | x => (false, x)
        let (eds, rest) := digitRun r''
        if eds.isEmpty then none
        else some ((if eneg then -(digitsValue eds : Int) else digitsValue eds), rest)
      else some (0, c :: r')
    | [] => some (0, [])
  match ex with
  | some (e, []) => .finite ⟨neg, digitsValue (ip ++ fp), e - fp.length⟩
  | _ => .invalid

/-- `as_tuple()`'s digit count and decimal places, as pydantic-core counts
them: a positive exponent adds trailing zeros, and places beyond the digits
are leading zeros. -/
def digitsInfo (coeff : Nat) (exp : Int) : Nat × Nat :=
  let n := (toString coeff).length
  if exp ≥ 0 then (0, n + exp.toNat) else (exp.natAbs, max n exp.natAbs)

/-- `Decimal.normalize()`: trailing zeros of the coefficient removed. -/
def normalized (d : PyDecimal) : Nat × Int :=
  let v := d.value
  (v.mant, v.exp)

end PyDecimal

/-- The `PyDecimal` validator. -/
def Scalar.decimal (cfg : Cfg) (j : Json) : Except ErrorKind PyDecimal :=
  let str (s : String) : Except ErrorKind PyDecimal :=
    match PyDecimal.parse s with
    | .finite d => .ok d
    | .nonFinite => .error .finiteNumber
    | .invalid => .error .decimalParsing
  match cfg.mode with
  | .json =>
    match j with
    | .num (.int i) => .ok (.ofInt i)
    | .num (.float d) => match PyDecimal.ofRust d with
      | some p => .ok p
      | none => .error .finiteNumber
    | .num _ => .error .finiteNumber
    | .str s => str s
    | _ => .error .decimalType
  | .python =>
    if cfg.strict then .error (.isInstanceOf "Decimal") else
    match j with
    | .num (.int i) => .ok (.ofInt i)
    | .num (.float d) => match PyDecimal.ofRepr d with
      | some p => .ok p
      | none => .error .finiteNumber
    | .num _ => .error .finiteNumber
    | .str s => str s
    | _ => .error .decimalType

instance : FromJson PyDecimal := ⟨"decimal", fun cfg j => liftKind cfg j (Scalar.decimal cfg j), fun _ => true⟩
instance : ToJson PyDecimal := ⟨fun _ d => .str d.toPy⟩
instance : JsonSchema PyDecimal := ⟨.anyOf [.number [], .string []]⟩
/-- A `Decimal` bound: its `str` in the error context (`{"gt": "0"}`), a
float in the schema (`"exclusiveMinimum": 0.0`). -/
instance : Constrained PyDecimal :=
  Constrained.numeric inferInstance inferInstance (fun b => .str b.toPy) (fun b => .float b.value)

/-- pydantic's `max_digits` and `decimal_places` checks, in its order: a
limit fails only if both the value and its normalised form exceed it. -/
def PyDecimal.checkDigits (maxDigits places : Option Nat) (d : PyDecimal) : Option ErrorKind :=
  let (dec, dig) := PyDecimal.digitsInfo d.coeff d.exp
  let (nm, ne) := d.normalized
  let (ndec, ndig) := PyDecimal.digitsInfo nm ne
  match maxDigits, places with
  | some m, _ =>
    if dig > m ∧ ndig > m then some (.decimalMaxDigits m)
    else match places with
      | some p =>
        if dec > p ∧ ndec > p then some (.decimalMaxPlaces p)
        else if dig - dec > m - p ∧ ndig - ndec > m - p then some (.decimalWholeDigits (m - p))
        else none
      | none => none
  | none, some p => if dec > p ∧ ndec > p then some (.decimalMaxPlaces p) else none
  | none, none => none

/-- `condecimal(max_digits=…, decimal_places=…)`. -/
def Condecimal (_max_digits _decimal_places : Option Nat) : Type := PyDecimal

section Condecimal
variable {md dp : Option Nat}
instance : FromJson (Condecimal md dp) where
  title := "decimal"
  fromJson cfg j :=
    match Scalar.decimal cfg j with
    | .ok d => match PyDecimal.checkDigits md dp d with
      | none => .ok d
      | some k => .error [{ kind := k, input := j, mode := cfg.mode }]
    | .error k => .error [{ kind := k, input := j, mode := cfg.mode }]
instance : ToJson (Condecimal md dp) := inferInstanceAs (ToJson PyDecimal)
instance : JsonSchema (Condecimal md dp) := inferInstanceAs (JsonSchema PyDecimal)
instance : Constrained (Condecimal md dp) := inferInstanceAs (Constrained PyDecimal)
instance : Keel.Ordered (Condecimal md dp) := inferInstanceAs (Keel.Ordered PyDecimal)
instance : Keel.Divisible (Condecimal md dp) := inferInstanceAs (Keel.Divisible PyDecimal)
instance {n : Nat} : OfNat (Condecimal md dp) n := inferInstanceAs (OfNat PyDecimal n)
instance : OfScientific (Condecimal md dp) := inferInstanceAs (OfScientific PyDecimal)
instance : DecidableEq (Condecimal md dp) := inferInstanceAs (DecidableEq PyDecimal)
instance : Repr (Condecimal md dp) := inferInstanceAs (Repr PyDecimal)
instance : Inhabited (Condecimal md dp) := inferInstanceAs (Inhabited PyDecimal)
end Condecimal

end LeanPydantic

namespace LeanPydantic

open LeanJson (Json Number)

/-- pydantic's plain `float` (`allow_inf_nan=True`): Lean's `Float`. JSON's
lenient `NaN`/`Infinity` tokens and the strings `"nan"`, `"inf"`,
`"-infinity"` are accepted; a dump writes the shortest decimal that reads
back (as Rust does) and `null` for the non-finite values (pydantic's default
`ser_json_inf_nan='null'`). Tested, not proved: `NaN ≠ NaN`. -/
def Scalar.plainFloat (strict : Bool) (python : Bool) : Json → Except ErrorKind Float
  | .num (.int i) =>
    -- Python's `float(int)` overflows past the largest double; jiter's reads inf
    let x := (Number.int i).toFloat
    if python && x.isInf then .error .floatType else .ok x
  | .num n => .ok n.toFloat
  | .bool b => if strict then .error .floatType else .ok (if b then 1 else 0)
  | .str s => if strict then .error .floatType else (Coerce.strAsNumber s).map Number.toFloat
  | _ => .error .floatType

instance : FromJson Float := ⟨"float", fun cfg j => liftKind cfg j (Scalar.plainFloat cfg.strict (cfg.mode = .python) j), fun _ => true⟩
instance : ToJson Float where
  toJson opts x :=
    if x.isFinite then .num (Number.ofFloat x) else
    match opts.ser_json_inf_nan with
    | .null => .null
    | .constants => .num (Number.ofFloat x)
    | .strings => .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity")
instance : JsonSchema Float := ⟨.number []⟩

instance : Keel.Ordered Float := { decLT := Float.decLt, decLE := Float.decLe }

/-- pydantic-core's float `multiple_of`: `x` is within `1e-9` of the
nearest multiple of `k`. -/
def Float.isMultipleOf (k x : Float) : Bool :=
  !((x - (x / k).round * k).abs > 1e-9)

instance : Keel.Divisible Float := ⟨fun k x => Float.isMultipleOf k x = true, fun _ _ => inferInstance⟩

/-- A `float` bound: a float in the error context (`{"gt": 0.0}`), and in
the schema as pydantic writes the bound it was given (`0` for `gt=0`). -/
instance : Constrained Float :=
  Constrained.numeric inferInstance inferInstance (fun b => .num (Number.ofFloat b))
    (fun b => match Number.ofFloat b with
      | .float d => Num.ofDecimal d
      | n => n)

end LeanPydantic
