import LeanPydantic

/-!
# Benches: hostile sizes, with bounds

Each bench builds its input, times the call alone, prints the time and
fails if it exceeds its bound. What the bounds catch is a change of
complexity class: the quadratic dict validation, the quadratic digit
conversion and the exponent-sized decimal scaling they were added for.

The bounds are set against pydantic-core 2.14.1 on the same machine
(`scripts/bench/pydantic_times.py` measures it), with headroom for CI:

| input | pydantic-core | here | bound |
|---|---|---|---|
| 65000 digits, JSON number or string | 0.1 ms | 3-5 ms | 50 ms |
| 1 MiB digit string | - | 25-32 ms | 100 ms |
| dict, 100 000 keys, `validate_json` | 25.5 ms | 78 ms | 150 ms |
| dict, 200 000 keys + 1000 repeats, `validate_json` | 80.7 ms | 236 ms | 450 ms |
| set, 200 000 items, `validate_json` | 13.2 ms | 69 ms | 150 ms |
| dict, 100 000 keys, parsed | 10.7 ms | 38 ms | 75 ms |
| dict, 200 000 keys, parsed | 27.4 ms | 83-97 ms | 180 ms |
| set, 200 000 items, parsed | 6.2 ms | 22-24 ms | 50 ms |

Of `validate_json`'s time on the dict, 50 ms of 78 is lean-json's parser.
The parsed rows give pydantic-core a built Python `dict`, so it does no
key collapsing, while here the members arrive as a list and are collapsed
with a hash index.

Run with `lake exe bench`.
-/

open LeanPydantic

/-- A JSON object with `n` distinct keys, plus `dups` repeated ones. -/
def wideObject (n dups : Nat) : String := Id.run do
  let mut s := "{"
  for i in [0:n] do
    s := s ++ (if i = 0 then "" else ",") ++ "\"k" ++ toString i ++ "\":" ++ toString i
  for i in [0:dups] do
    s := s ++ ",\"k" ++ toString i ++ "\":0"
  return s ++ "}"

/-- A JSON array of `n` integers, half of them repeated. -/
def wideArray (n : Nat) : String := Id.run do
  let mut s := "["
  for i in [0:n] do
    s := s ++ (if i = 0 then "" else ",") ++ toString (i / 2)
  return s ++ "]"

/-- A parsed JSON value (`null` if the text does not parse). -/
def parsed (s : String) : LeanJson.Json :=
  match LeanJson.from_json s with
  | .ok v => v.val
  | .error _ => .null

/-- A bench: its input, and the check on it. The input is read from a
reference after the clock starts, so the compiler cannot compute the pure
check before it. -/
structure Bench where
  name : String
  boundMs : Nat
  {In : Type}
  input : In
  check : In → Bool

def time (b : Bench) : IO Bool := do
  let r ← IO.mkRef b.input
  let t0 ← IO.monoMsNow
  let s ← r.get
  let ok ← IO.lazyPure fun _ => b.check s
  let ms := (← IO.monoMsNow) - t0
  let pass := ok && ms ≤ b.boundMs
  IO.println s!"{if pass then "ok  " else "FAIL"}  {b.name}: {ms} ms (bound {b.boundMs} ms){if ok then "" else ", wrong result"}"
  return pass

def benches : List Bench :=
  let ta := TypeAdapter.new (Dict Int)
  let ts := TypeAdapter.new (PySet Int)
  let ti := TypeAdapter.new Int
  let tdec := TypeAdapter.new (Decimal ∣ gt 0 ∧ multipleOf 0.5)
  let tpd := TypeAdapter.new (PyDecimal ∣ gt 0)
  let digits (n : Nat) : String := String.ofList (List.replicate n '7')
  let rejects {α} (r : Except ValidationError α) : Bool := match r with | .ok _ => false | .error _ => true
  [⟨"int, 65000-digit JSON number (validate_json)", 50, digits 65000, fun s => rejects (ti.validate_json s)⟩,
    ⟨"int, 65000-digit string, lax (validate_json)", 50, "\"" ++ digits 65000 ++ "\"", fun s => rejects (ti.validate_json s)⟩,
    ⟨"int, 1 MiB digit string, lax (validate_python)", 100, digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, 4300-digit string, lax (validate_python)", 50, digits 4300, fun s =>
      match ti.validate_python (.str s) with
      | .ok _ => true
      | .error _ => false⟩,
    ⟨"float as Decimal, gt 0 and multiple_of 0.5 on 1e999999999 (validate_json)", 50, "1e999999999", fun s =>
      match tdec.validate_json s with
      | .ok _ => true
      | .error _ => false⟩,
    ⟨"float as Decimal, gt 0 on 1e-999999999 (validate_json)", 50, "1e-999999999", fun s =>
      match tdec.validate_json s with
      | .ok _ => false
      | .error _ => true⟩,
    ⟨"Decimal, gt 0 on \"1e999999999\" (validate_json)", 50, "\"1e999999999\"", fun s =>
      match tpd.validate_json s with
      | .ok _ => true
      | .error _ => false⟩,
    ⟨"dict[str, int], 100000 keys (validate_json)", 150, wideObject 100000 0, fun s =>
      match ta.validate_json s with
      | .ok d => d.val.entries.length == 100000
      | .error _ => false⟩,
    ⟨"dict[str, int], 200000 keys and 1000 repeats (validate_json)", 450, wideObject 200000 1000, fun s =>
      match ta.validate_json s with
      | .ok d => d.val.entries.length == 200000
      | .error _ => false⟩,
    ⟨"set[int], 200000 items, half repeated (validate_json)", 150, wideArray 200000, fun s =>
      match ts.validate_json s with
      | .ok v => v.val.elems.length == 100000
      | .error _ => false⟩,
    -- validation alone, on an already parsed value (pydantic's validate_python on a dict)
    ⟨"dict[str, int], 100000 keys (validate_python)", 75, parsed (wideObject 100000 0), fun j =>
      match ta.validate_python j with
      | .ok d => d.val.entries.length == 100000
      | .error _ => false⟩,
    ⟨"dict[str, int], 200000 keys (validate_python)", 180, parsed (wideObject 200000 0), fun j =>
      match ta.validate_python j with
      | .ok d => d.val.entries.length == 200000
      | .error _ => false⟩,
    ⟨"set[int], 200000 items, half repeated (validate_python)", 50, parsed (wideArray 200000), fun j =>
      match ts.validate_python j with
      | .ok v => v.val.elems.length == 100000
      | .error _ => false⟩]

def main : IO UInt32 := do
  let mut failed := 0
  for b in benches do
    unless ← time b do failed := failed + 1
  IO.println s!"{benches.length} benches, {failed} failing"
  return if failed = 0 then 0 else 1
