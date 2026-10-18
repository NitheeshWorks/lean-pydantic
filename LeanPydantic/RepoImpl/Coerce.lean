import LeanPydantic.RepoImpl.Number

/-!
# RepoImpl: lax-mode coercions

pydantic-core's lax mode turns strings, booleans and floats into the requested
scalar. These follow `src/input/shared.rs` and `src/input/input_json.rs` of
pydantic-core 2.50.1 rule for rule, on character lists:

* `strAsInt`: a JSON integer literal; otherwise the string is cleaned
  (whitespace trimmed, one `+` or `-`, leading zeros, a `.0…` suffix,
  single underscores between digits) and parsed again.
* `strAsFloat`: Rust's `f64` grammar on the trimmed string, then on the
  string with underscores removed. `inf` and `nan` are recognised and
  rejected with `finite_number` (this port's `float` is exact: the
  `allow_inf_nan=False` behaviour).
* `strAsBool`: `0 f n no off false` and `1 t y on yes true`, ASCII case
  insensitive, no trimming.
* `decimalAsInt`: an integral decimal strictly inside the `i64` range.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

namespace Coerce

/-- Rust's `char::is_whitespace`: the Unicode `White_Space` property. -/
def isWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x9 ≤ n && n ≤ 0xD) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F ||
    n == 0x205F || n == 0x3000

/-- Rust's `str::trim`. -/
def trim (cs : List Char) : List Char :=
  ((cs.dropWhile isWhitespace).reverse.dropWhile isWhitespace).reverse

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The value of a list of decimal digits. -/
def digitsVal (cs : List Char) : Nat :=
  cs.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0

/-- A JSON integer literal, `-?(0|[1-9][0-9]*)`, and nothing else. -/
def jsonInt? (cs : List Char) : Option Int :=
  let (neg, ds) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  match ds with
  | [] => none
  | '0' :: _ :: _ => none
  | d :: r =>
    if (d :: r).all isDigit then
      let v : Int := digitsVal (d :: r)
      some (if neg then -v else v)
    else none

/-- pydantic-core's `strip_leading_zeros`, after the first zero: `prev` is
the character before `cs`. -/
def stripZerosAfter (prev : Char) : List Char → Option (List Char)
  | [] => some [prev]
  | c :: r =>
    if c = '0' ∨ c = '_' then stripZerosAfter c r
    else if ('1' ≤ c ∧ c ≤ '9') ∨ c = '-' then some (c :: r)
    else if c = '.' then some (prev :: c :: r)
    else none

/-- pydantic-core's `strip_leading_zeros`. -/
def stripLeadingZeros : List Char → Option (List Char)
  | '0' :: r => stripZerosAfter '0' r
  | c :: r => if ('1' ≤ c ∧ c ≤ '9') ∨ c = '-' then some (c :: r) else none
  | [] => none

/-- Drop a `.000…` suffix (at least one zero). -/
def stripDecimalZeros (cs : List Char) : List Char :=
  match cs.span (· ≠ '.') with
  | (ip, _ :: fp) => if fp ≠ [] ∧ fp.all (· = '0') then ip else cs
  | _ => cs

/-- pydantic-core's `strip_underscores`: remove single underscores between
other characters; `none` when there are none, or any are leading, trailing
or doubled. -/
def stripUnderscores (cs : List Char) : Option (List Char) :=
  if cs.head? = some '_' ∨ cs.getLast? = some '_' ∨ '_' ∉ cs ∨
      (cs.zip cs.tail).any (fun p => p.1 = '_' ∧ p.2 = '_') then none
  else some (cs.filter (· ≠ '_'))

/-- pydantic-core's `clean_int_str`. -/
def cleanIntStr (s0 : List Char) : Option (List Char) := do
  let s := trim s0
  let s ← match s with
    | '+' :: '-' :: _ => none
    | '+' :: r => some r
    | r => some r
  let (neg, s) ← match s with
    | '-' :: '-' :: _ => none
    | '-' :: '+' :: _ => none
    | '-' :: r => some (true, r)
    | r => some (false, r)
  let s ← stripLeadingZeros s
  let s := stripDecimalZeros s
  let sign : List Char := if neg then ['-'] else []
  match stripUnderscores s with
  | some t => some (sign ++ t)
  | none => if s0.length = s.length then none else some (sign ++ s)

/-- Python's 4300-digit limit on `int(str)`, as jiter applies it (the sign
counts; see UP-025). -/
def maxIntLen : Nat := 4300

/-- pydantic-core's `str_as_int`. -/
def strAsInt (s : String) : Except ErrorKind Int :=
  let cs := s.toList
  match jsonInt? cs with
  | some i => if cs.length > maxIntLen then .error .intParsingSize else .ok i
  | none =>
    match cleanIntStr cs >>= jsonInt? with
    | some i => .ok i
    | none => .error .intParsing

/-- Rust's `f64` grammar: `[+-]? (inf | infinity | nan | digits)`, where
digits are `D* [. D*] [(e|E) [+-]? D+]` with at least one mantissa digit.
`some none` is an infinity or a NaN; `some (some d)` an exact decimal. -/
def rustFloat? (cs : List Char) : Option (Option Decimal) :=
  let (neg, r) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let low := String.ofList (r.map Char.toLower)
  if low = "inf" ∨ low = "infinity" ∨ low = "nan" then some none
  else
    let (ip, r) := r.span isDigit
    let (fp, r) := match r with
      | '.' :: r' => r'.span isDigit
      | r' => ([], r')
    if ip.isEmpty ∧ fp.isEmpty then none
    else
      let ex : Option Int := match r with
        | [] => some 0
        | e :: r' =>
          if e = 'e' ∨ e = 'E' then
            let (eneg, ds) := match r' with
              | '-' :: d => (true, d)
              | '+' :: d => (false, d)
              | d => (false, d)
            if ds ≠ [] ∧ ds.all isDigit then
              some (if eneg then -(digitsVal ds : Int) else digitsVal ds)
            else none
          else none
      ex.map fun e => some (Decimal.normalize neg (digitsVal (ip ++ fp)) (e - fp.length))

/-- pydantic-core's `str_as_float`, for an exact `float`. -/
def strAsFloat (s : String) : Except ErrorKind Decimal :=
  let res := match rustFloat? (trim s.toList) with
    | some r => some r
    | none => stripUnderscores s.toList >>= rustFloat?
  match res with
  | some (some d) => .ok d
  | some none => .error .finiteNumber
  | none => .error .floatParsing

/-- pydantic-core's `str_as_bool`. -/
def strAsBool (s : String) : Except ErrorKind Bool :=
  let l := String.ofList (s.toList.map Char.toLower)
  if s = "0" ∨ l = "f" ∨ l = "n" ∨ l = "no" ∨ l = "off" ∨ l = "false" then .ok false
  else if s = "1" ∨ l = "t" ∨ l = "y" ∨ l = "on" ∨ l = "yes" ∨ l = "true" then .ok true
  else .error .boolParsing

/-- `2^63`: the edge of pydantic-core's `i64` float conversion. -/
def i64Bound : Int := 9223372036854775808

/-- The decimal digit count of a natural number (at least one). -/
def numDigits (n : Nat) : Nat := (toString n).length

/-- pydantic-core's `float_as_int`, on an exact decimal: a fractional value
is `int_from_float`; a value at least `2^63` in size `int_parsing_size`, or
`finite_number` when a double would hold it as an infinity. -/
def decimalAsInt (d : Decimal) : Except ErrorKind Int :=
  if d.exp < 0 then .error .intFromFloat
  else if d.exp + numDigits d.mant > 309 then .error .finiteNumber
  else if d.exp > 19 then .error .intParsingSize
  else
    let v := Dec.keyAt d 0
    if -i64Bound < v ∧ v < i64Bound then .ok v else .error .intParsingSize

end Coerce

end LeanPydantic
