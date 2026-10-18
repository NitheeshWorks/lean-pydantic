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
| 1 MiB digit string | - | 6 ms | 100 ms |
| 1 MiB digits with `.0`, `.00`, `-`, ` `, `000`, `+`, `7_` | 2.6-2.9 ms | 6-7 ms | 30 ms |
| dict, 100 000 keys, `validate_json` | 25.5 ms | 78 ms | 150 ms |
| dict, 200 000 keys + 1000 repeats, `validate_json` | 80.7 ms | 236 ms | 450 ms |
| set, 200 000 items, `validate_json` | 13.2 ms | 69 ms | 150 ms |
| dict, 100 000 keys, parsed | 11.2 ms | 25 ms | 75 ms |
| dict, 200 000 keys, parsed | 32.2 ms | 58-64 ms | 180 ms |
| dict, 400 000 keys, parsed | 110.7 ms | 150-177 ms | 400 ms |
| dict, 400 000 keys, `validate_json` | 207.4 ms | 442-508 ms | 1000 ms |
| set, 200 000 items, parsed | 6.2 ms | 22-24 ms | 50 ms |
| `^(a{1,50})+$`, 10 000 / 20 000 characters | 0.03 / 0.06 ms | 94 / 94 ms | 300 ms |
| `(a\|b)` ×50 then `c`, 50 000 / 100 000 characters | 0.15 / 0.33 ms | 24 / 27 ms | 100 ms |

Of `validate_json`'s time on the dict, 50 ms of 78 is lean-json's parser.
Neither side is exactly linear past 100 000 keys: pydantic-core's own times
grow 2.9x and 3.4x per doubling from 100 000 to 400 000 keys (hash tables
outgrow the caches); the parsed rows here grow 2.3x and 2.6x.
The parsed rows give pydantic-core a built Python `dict`, so it does no
key collapsing, while here the members arrive as a list and are collapsed
with a hash index.

The pattern rows run compiled patterns (`Regex.ofSource`: derivative terms
numbered once, tables of linear forms, steps cached per call by term set).
pydantic-core (Rust `regex`): the email-like pattern 0.001 ms per call,
`^(a{1,50})+$` on 1000 characters 0.003 ms, `[ab]*a[ab]{100}c` on 20 000
random characters 22 ms, `(\w{1,10}\s?){1,10}x` 0.058 ms per call.
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

/-- `n` pseudo-random `a`/`b` characters (a fixed linear congruential sequence). -/
def randomAB (n : Nat) : String := Id.run do
  let mut x : UInt64 := 88172645463325252
  let mut cs : Array Char := Array.mkEmpty n
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    cs := cs.push (if (x >>> 33) % 2 == 0 then 'a' else 'b')
  return String.ofList cs.toList

/-- The bench patterns, compiled once (as a pattern literal in a type is). -/
def countedPat : Keel.Pattern := Regex.ofSource "^(a{1,50})+$"
def widePat : Keel.Pattern := Regex.ofSource "(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)(a|b)c"
def emailPat : Keel.Pattern := Regex.ofSource "^[a-z0-9._%+-]{1,64}@[a-z0-9.-]{1,255}\\.[a-z]{2,63}$"
def thrashPat : Keel.Pattern := Regex.ofSource "[ab]*a[ab]{100}c"
def wordsPat : Keel.Pattern := Regex.ofSource "(\\w{1,10}\\s?){1,10}x"

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
  let counted := countedPat.test
  let wide := widePat.test
  let email := emailPat.test
  let thrash := thrashPat.test
  let as (n : Nat) : String := String.ofList (List.replicate n 'a')
  let abs (n : Nat) : String := String.join (List.replicate (n / 2) "ab")
  -- 1000 distinct 64-character addresses, so no call can be shared
  let emails := (List.range 1000).map fun i =>
    let tag := toString (10000 + i)
    "first.last+" ++ tag ++ String.ofList (List.replicate 24 'x') ++ "@mail.example-domain.com"
  let runs := (List.range 1000).map fun i => as (995 + i % 10)
  [⟨"pattern email-like, 1000 calls on 64 characters (0.1 ms per call)", 100, emails, fun l => l.all email⟩,
    ⟨"pattern ^(a{1,50})+$, 1000 calls on 995-1004 characters (1 ms per call)", 1000, runs, fun l => l.all counted⟩,
    ⟨"pattern [ab]*a[ab]{100}c on 10 000 random a/b", 150, randomAB 10000, fun s => !thrash s⟩,
    ⟨"pattern [ab]*a[ab]{100}c on 20 000 random a/b", 200, randomAB 20000, fun s => !thrash s⟩,
    ⟨"pattern ^(a{1,50})+$ on 20 000 characters", 50, as 20000, fun s => counted s⟩,
    ⟨"pattern (a|b) x50 then c on 100 000 characters", 50, abs 100000, fun s => !wide s⟩,
    ⟨"pattern (\\w{1,10}\\s?){1,10}x, 1000 calls on 30 characters", 200, (List.range 1000).map (fun i => "word" ++ toString (100000 + i) ++ " another phrase here"), fun l => l.all fun s => !wordsPat.test s⟩,
    ⟨"compile (\\w{1,30}\\s?){1,20}x", 2000, "(\\w{1,30}\\s?){1,20}x", fun src =>
      match Regex.compile src with
      | .ok r => (Regex.Regex.Nfa.build r).isSome
      | .error _ => true⟩,
    ⟨"compile the email-like pattern", 200, "^[a-z0-9._%+-]{1,64}@[a-z0-9.-]{1,255}\\.[a-z]{2,63}$", fun src =>
      match Regex.compile src with
      | .ok r => (Regex.Regex.Nfa.build r).isSome
      | .error _ => false⟩,
    ⟨"int, 65000-digit JSON number (validate_json)", 50, digits 65000, fun s => rejects (ti.validate_json s)⟩,
    ⟨"int, 65000-digit string, lax (validate_json)", 50, "\"" ++ digits 65000 ++ "\"", fun s => rejects (ti.validate_json s)⟩,
    ⟨"int, 1 MiB digit string, lax (validate_python)", 100, digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    -- every form the cleaning accepts, at 1 MiB: one pass, no list built
    ⟨"int, 1 MiB digits + \".0\"", 30, digits 1048576 ++ ".0", fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, 1 MiB digits + \".00\"", 30, digits 1048576 ++ ".00", fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \"-\" + 1 MiB digits + \".0\"", 30, "-" ++ digits 1048576 ++ ".0", fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \"-\" + 1 MiB digits", 30, "-" ++ digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \" \" + 1 MiB digits", 30, " " ++ digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \"000\" + 1 MiB digits", 30, "000" ++ digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \"+\" + 1 MiB digits", 30, "+" ++ digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, \"7_\" + 1 MiB digits", 30, "7_" ++ digits 1048576, fun s => rejects (ti.validate_python (.str s))⟩,
    ⟨"int, 1 MiB digits + \" \"", 30, digits 1048576 ++ " ", fun s => rejects (ti.validate_python (.str s))⟩,
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
    ⟨"dict[str, int], 400000 keys (validate_python)", 400, parsed (wideObject 400000 0), fun j =>
      match ta.validate_python j with
      | .ok d => d.val.entries.length == 400000
      | .error _ => false⟩,
    ⟨"dict[str, int], 400000 keys (validate_json)", 1000, wideObject 400000 0, fun s =>
      match ta.validate_json s with
      | .ok d => d.val.entries.length == 400000
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
