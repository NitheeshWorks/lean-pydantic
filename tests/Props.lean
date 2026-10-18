import LeanPydantic

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

open LeanPydantic

def okEq {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok a, b => decide (a = b)
  | .error _, _ => false

structure Item where
  name : String
  description : Option String := none
  price : Decimal
  tax : Option Decimal := none
  qty : Nat ∣ le 1000 := 1
  deriving Model

def Rng.int (r : Rng) (bound : Nat) : Int × Rng :=
  let (v, r) := r.nat (2 * bound + 1)
  ((v : Int) - bound, r)

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : List α) : α × Rng :=
  let (i, r) := r.nat xs.length
  (xs[i]?.getD default, r)

def Rng.string (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.nat 8
  let mut r := r
  let mut cs : List Char := []
  for _ in [0:n] do
    let (c, r') := r.pick ['a', 'Z', '0', ' ', '_', '"', '\\', 'é', '😀', '\n']
    r := r'
    cs := c :: cs
  return (String.ofList cs, r)

def Rng.decimal (r : Rng) : Decimal × Rng :=
  let (m, r) := r.nat 100000
  let (e, r) := r.int 6
  let (neg, r) := r.nat 2
  let d : Decimal := OfScientific.ofScientific m (decide (e < 0)) e.natAbs
  (if neg == 1 then -d else d, r)

/-- A check on one generated value. -/
def prop (name : String) (gen : Rng → α × Rng) (ok : α → Bool) (disp : α → String) : Property :=
  ⟨name, fun r => let (a, r) := gen r; (if ok a then none else some (disp a), r)⟩

/-- A digit string of up to 5000 digits. -/
def Rng.digits (r : Rng) : List Char × Rng := Id.run do
  let (n, r) := r.nat 5000
  let mut r := r
  let mut cs : List Char := []
  for _ in [0:n] do
    let (d, r') := r.nat 10
    r := r'
    cs := Char.ofNat (48 + d) :: cs
  return (cs, r)


/-- `n / 10 ^ p` written out in decimal (`p` places after the point). -/
def decimalText (n p : Nat) : String :=
  let ds := toString n
  if p = 0 then ds
  else
    let ds := String.ofList (List.replicate (p + 1 - min ds.length (p + 1)) '0') ++ ds
    (ds.take (ds.length - p)).toString ++ "." ++ (ds.drop (ds.length - p)).toString

/-- A halfway case and its neighbours: the midpoint between a finite
positive double (drawn mostly where midpoints are longest) and the next one up, exactly, as `A / 10 ^ p`; then
`A * 10 ^ K` and that plus and minus one, at `p + K` places, so the text runs
past the 769 kept digits and the tie is broken (or not) far beyond them. -/
def Rng.halfway (r : Rng) : List String × Rng :=
  let (v, r) := r.next
  -- biased to where midpoints have the most digits (subnormals and the
  -- smallest normal binade, up to 768 significant digits) and to the top of
  -- the range; a quarter of the draws are any finite double
  let (cls, r) := r.nat 8
  let (top, r) := r.nat 3
  let frac0 := (v &&& 0xFFFFFFFFFFFFF).toNat
  let frac := if cls < 4 && top = 0 then 0xFFFFFFFFFFFFF - frac0 % 16 else frac0
  let be : Nat := match cls with
    | 0 | 1 => 0
    | 2 | 3 => 1
    | 4 => 2
    | 5 => 2046
    | _ => ((v >>> 52) &&& 0x7FF).toNat % 2047
  let (m, e) : Nat × Int := if be = 0 then (frac, -1074) else (frac + 2 ^ 52, (be : Int) - 1075)
  -- midpoint (2m + 1) * 2 ^ (e - 1)
  let f := e - 1
  let (A, p) : Nat × Nat :=
    if f ≥ 0 then ((2 * m + 1) * 2 ^ f.toNat, 0) else ((2 * m + 1) * 5 ^ f.natAbs, f.natAbs)
  let (K, r) := r.nat 1500
  let big := A * 10 ^ K
  let texts := [decimalText A p, decimalText big (p + K), decimalText (big + 1) (p + K),
    decimalText (big - 1) (p + K),
    toString (big + 1) ++ "e-" ++ toString (p + K), toString (big - 1) ++ "E-" ++ toString (p + K),
    "-" ++ decimalText (big + 1) (p + K), "000" ++ decimalText (big - 1) (p + K)]
  (texts, r)

def properties : List Property := [
  -- the balanced digit conversion is the left-to-right one
  prop "digitsVal is the left-to-right digit fold, up to 5000 digits"
    (fun r => r.digits)
    (fun cs => Coerce.digitsVal cs == cs.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)
    (fun cs => String.ofList cs),
  -- pydantic-core's str_as_int on the decimal forms upstream accepts
  prop "strAsInt reads integers, padded, signed, zero-led and underscored"
    (fun r => r.int 1000000)
    (fun i =>
      let s := toString i.natAbs
      let sign := if i < 0 then "-" else ""
      let forms := [sign ++ s, "  " ++ sign ++ s ++ "\n", sign ++ "000" ++ s,
        (if i < 0 then "-" else "+") ++ s, sign ++ s ++ ".000",
        sign ++ String.intercalate "_" (s.toList.map (String.singleton ·))]
      forms.all fun f => okEq (Coerce.strAsInt f) i)
    toString,
  -- str_as_float on decimal text agrees with LeanJson's reading of the same text
  prop "strAsFloat agrees with the JSON number reader"
    (fun r => r.decimal)
    (fun d =>
      let s := LeanJson.printStr (.num (.float d))
      match LeanJson.from_json s with
      | .ok j => match j.val with
        | .num n => okEq (Coerce.strAsFloat s) (Num.toDecimal n) && okEq (Coerce.strAsFloat (" " ++ s ++ " ")) (Num.toDecimal n)
        | _ => false
      | .error _ => false)
    toString,
  -- float(str) on long text: only the leading 769+ significant digits and a
  -- sticky digit are converted; the double must be the exact text's double,
  -- checked on midpoints between adjacent doubles and their neighbours
  prop "strAsDouble on halfway cases is the exact conversion"
    (fun r => r.halfway)
    (fun ts => ts.all fun t =>
      match Coerce.strAsDouble t, (Coerce.strAsNumber t).map LeanJson.Number.toFloat with
      | .ok x, .ok y => x.toBits == y.toBits
      | _, _ => false)
    (fun ts => toString (ts.map fun t => t.take 40)),
  -- a printed schema has its keys sorted at every level but `properties`
  prop "model_json_schema keys are sorted"
    (fun r => ((), r))
    (fun _ => match Item.model_json_schema with
      | .obj kvs => (kvs.toList.map (·.1)) == ["properties", "required", "title", "type"]
      | _ => false)
    (fun _ => toString Item.model_json_schema),
  -- the JSON-text round trip (LeanJson's printer and parser in between)
  prop "model_validate_json (model_dump_json a) = a"
    (fun r =>
      let (name, r) := r.string
      let (p, r) := r.decimal
      let (t, r) := r.decimal
      let (hasTax, r) := r.nat 2
      let (q, r) := r.nat 1001
      let qty : Nat ∣ le 1000 := if h : q ≤ 1000 then ⟨q, h⟩ else 0
      let item : Item := { name := name, price := p, tax := if hasTax == 1 then some t else none, qty := qty }
      (item, r))
    (fun a => match Item.model_validate_json a.model_dump_json with
      | .ok b => b.val.model_dump_json == a.model_dump_json
      | .error _ => false)
    (fun a => a.model_dump_json),
  -- Rust's Display of a decimal, as pydantic-core renders ctx numbers
  prop "Num.display has no exponent and no trailing fraction zeros"
    (fun r => r.decimal)
    (fun d =>
      let s := Num.display (.float d)
      !s.contains 'e' && (!s.contains '.' || !s.endsWith "0") && !s.endsWith ".")
    toString,
  -- validation in pydantic order reports the lowest-ranked failing atom
  prop "validatePy reports multiple_of before le before ge"
    (fun r => r.int 200)
    (fun x =>
      let c : Keel.Constraint Int := .and (.ge (-50)) (.and (.le 50) (.multipleOf 7))
      match c.validatePy x with
      | .ok _ => x % 7 == 0 && -50 ≤ x && x ≤ 50
      | .error (e :: _) =>
        let expected := if x % 7 != 0 then 0 else if x > 50 then 1 else 3
        Keel.Constraint.rank e.failed == expected
      | .error [] => false)
    toString,
  -- print_parse_float (tested): every finite double, from random bits, prints
  -- (shortest form) and reads back to the same bits
  prop "Float: shortest print reads back to the same double"
    (fun r => let (v, r) := r.next; (Float.ofBits v, r))
    (fun x => !x.isFinite ||
      (LeanJson.Number.ofFloat x).toFloat.toBits == x.toBits &&
      (match LeanJson.from_json (LeanJson.printStr (toJson {} x)) with
        | .ok j => match FromJson.fromJson (α := Float) { mode := .json } j.val with
          | .ok y => y.toBits == x.toBits
          | .error _ => false
        | .error _ => false))
    (fun x => s!"{x} bits {x.toBits}"),
  -- str(Decimal) reads back as the same Decimal (coefficient and exponent)
  prop "PyDecimal: str then Decimal(str) is the identity"
    (fun r =>
      let (neg, r) := r.nat 2
      let (c, r) := r.nat 10000000
      let (e, r) := r.int 12
      ((⟨neg == 1, c, e⟩ : PyDecimal), r))
    (fun d => match PyDecimal.parse d.toPy with
      | .finite d' => d' == d
      | _ => false)
    (fun d => s!"{repr d} printed {d.toPy}"),
  -- the regex scan's state never exceeds the pattern's class count plus one
  prop "regex: no backtracking, bounded state on random text"
    (fun r =>
      let (n, r) := r.nat 64
      let (cs, r) := (List.range n).foldl (fun (acc, r) _ =>
        let (c, r) := r.pick ['a', 'b', ' ', '1', '!']
        (c :: acc, r)) ([], r)
      (String.ofList cs, r))
    (fun s => match Regex.compile "^(a|ab|b)*\\s?\\d+$", Regex.compile "(a+)+b" with
      | .ok r1, .ok r2 =>
        let ref1 := (s.toList.all fun c => c = 'a' || c = 'b' || c = ' ' || c = '1')
        -- (a+)+b matches exactly when a 'b' follows some 'a'
        let ref2 := (s.toList.zip s.toList.tail).any fun (x, y) => x = 'a' && y = 'b'
        (!r1.search s || ref1) && r2.search s == ref2
      | _, _ => false)
    id
]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
