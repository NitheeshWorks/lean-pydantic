/-!
# RepoImpl: numbers read in place

A long decimal string is read in one `String.foldl`, with no character
list: the digits go into a `DigAcc` (16-digit chunks, so every step is a
machine-word multiply-add) and the chunks are combined at the end by a
balanced product tree (`radixTree`), `O(M(n) log n)`. `numScan` is the
grammar shared by Rust's `f64` and Python's `Decimal(str)`,
`[+-]? D* [. D*] [(e|E) [+-]? D+]` with at least one mantissa digit, and
`numScan_eq` proves it equal to `numParts`, the same grammar written with
`span` on the character list.
-/

namespace LeanPydantic

namespace NumScan

/-! ## Positional values -/

/-- `c lo, …, c (lo+n-1)` as base-`B` digits, most significant first. -/
def radixVal (B : Nat) (c : Nat → Nat) (lo n : Nat) : Nat :=
  (List.range' lo n).foldl (fun a i => a * B + c i) 0

/-- `radixVal` from an accumulator, by a loop. -/
def radixLeaf (B : Nat) (c : Nat → Nat) : Nat → Nat → Nat → Nat
  | _, 0, a => a
  | i, n + 1, a => radixLeaf B c (i + 1) n (a * B + c i)

/-- `radixVal`, split in halves: a long run costs a few big
multiplications, `log n` deep, instead of `n` small ones. -/
def radixTree (B : Nat) (c : Nat → Nat) (lo n : Nat) : Nat :=
  if n ≤ 16 then radixLeaf B c lo n 0
  else
    let h := n / 2
    radixTree B c lo h * B ^ (n - h) + radixTree B c (lo + h) (n - h)
termination_by n

theorem radixLeaf_eq (B : Nat) (c : Nat → Nat) (i n a : Nat) :
    radixLeaf B c i n a = (List.range' i n).foldl (fun a i => a * B + c i) a := by
  induction n generalizing i a with
  | zero => rfl
  | succ n ih => simp [radixLeaf, ih, List.range'_succ]

theorem foldl_radix_from {α : Type} (B : Nat) (g : α → Nat) (l : List α) (x : Nat) :
    l.foldl (fun a i => a * B + g i) x = x * B ^ l.length + l.foldl (fun a i => a * B + g i) 0 := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * B + g y), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm (B ^ l.length) B]
    omega

theorem radixVal_add (B : Nat) (c : Nat → Nat) (lo m n : Nat) :
    radixVal B c lo (m + n) = radixVal B c lo m * B ^ n + radixVal B c (lo + m) n := by
  unfold radixVal
  rw [← List.range'_append_1, List.foldl_append, foldl_radix_from, List.length_range']

theorem radixTree_eq (B : Nat) (c : Nat → Nat) (lo n : Nat) :
    radixTree B c lo n = radixVal B c lo n := by
  induction n using Nat.strongRecOn generalizing lo with
  | _ n ih =>
    unfold radixTree
    split
    · rw [radixLeaf_eq]; rfl
    · rename_i hn
      have h1 : n / 2 < n := by omega
      have h2 : n - n / 2 < n := by omega
      dsimp only
      rw [ih _ h1, ih _ h2]
      have := radixVal_add B c lo (n / 2) (n - n / 2)
      rw [Nat.add_sub_cancel' (Nat.div_le_self n 2)] at this
      exact this.symm

/-- `radixVal` over a list's entries is the list's left fold. -/
theorem radixVal_getD {α : Type} (B : Nat) (g : α → Nat) (d : α) (l : List α) :
    radixVal B (fun i => g (l.getD i d)) 0 l.length = l.foldl (fun a x => a * B + g x) 0 := by
  suffices h : ∀ (pre : List α) (x : Nat),
      (List.range' pre.length l.length).foldl (fun a i => a * B + g ((pre ++ l).getD i d)) x
        = l.foldl (fun a x => a * B + g x) x by
    simpa [radixVal] using h [] 0
  induction l with
  | nil => simp
  | cons y l ih =>
    intro pre x
    simp only [List.length_cons, List.range'_succ, List.foldl_cons]
    have e : pre ++ y :: l = (pre ++ [y]) ++ l := by simp
    have hy : (pre ++ y :: l).getD pre.length d = y := by simp
    rw [hy, e]
    have := ih (pre ++ [y]) (x * B + g y)
    simpa using this

/-- The digit value of a character (`'0'` is `0`). -/
@[inline] def digitVal (c : Char) : Nat := c.toNat - 48

/-- The digit fold: the value of a list of decimal digits. -/
def digitsSpec (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + digitVal c) 0

/-- The value of a list of decimal digits, by `radixTree` on its array. -/
def digitsVal (cs : List Char) : Nat :=
  let a := cs.toArray
  radixTree 10 (fun i => digitVal (a.getD i '0')) 0 cs.length

theorem digitsVal_eq (cs : List Char) : digitsVal cs = digitsSpec cs := by
  unfold digitsVal digitsSpec
  rw [radixTree_eq]
  have := radixVal_getD 10 digitVal '0' cs
  simpa [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] using this

/-! ## The digit accumulator -/

/-- Digits pushed one at a time: full 16-digit chunks, then the `len`
digits of `cur`. -/
structure DigAcc where
  chunks : Array Nat := #[]
  cur : Nat := 0
  len : Nat := 0

/-- `10 ^ 16`. -/
def chunkBase : Nat := 10000000000000000

/-- The value of the chunks alone, as a fold. -/
def chunkSpec (l : List Nat) : Nat := l.foldl (fun a x => a * chunkBase + x) 0

/-- One digit pushed. -/
@[inline] def DigAcc.push (a : DigAcc) (d : Nat) : DigAcc :=
  if a.len = 15 then ⟨a.chunks.push (a.cur * 10 + d), 0, 0⟩
  else ⟨a.chunks, a.cur * 10 + d, a.len + 1⟩

/-- The value: the chunks by a product tree, then the open chunk. -/
def DigAcc.val (a : DigAcc) : Nat :=
  radixTree chunkBase (fun i => a.chunks.getD i 0) 0 a.chunks.size * 10 ^ a.len + a.cur

theorem DigAcc.val_eq (a : DigAcc) : a.val = chunkSpec a.chunks.toList * 10 ^ a.len + a.cur := by
  unfold DigAcc.val chunkSpec
  rw [radixTree_eq]
  have := radixVal_getD chunkBase id 0 a.chunks.toList
  simp only [id, Array.length_toList] at this
  rw [← this]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

@[simp] theorem DigAcc.val_empty : ({} : DigAcc).val = 0 := by
  simp [DigAcc.val_eq, chunkSpec]

theorem DigAcc.val_push (a : DigAcc) (d : Nat) : (a.push d).val = a.val * 10 + d := by
  unfold DigAcc.push
  split
  · rename_i h
    simp only [DigAcc.val_eq, Array.toList_push, chunkSpec, List.foldl_append, List.foldl_cons,
      List.foldl_nil, h]
    simp only [chunkBase, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    rw [show (10 : Nat) ^ 15 = 1000000000000000 by decide]
    omega
  · simp only [DigAcc.val_eq, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc]; omega

theorem DigAcc.val_foldl (a : DigAcc) (cs : List Char) :
    (cs.foldl (fun a c => a.push (digitVal c)) a).val = cs.foldl (fun n c => n * 10 + digitVal c) a.val := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simp [ih, DigAcc.val_push]

/-! ## The grammar, on a character list -/

/-- An ASCII decimal digit. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

theorem isDigit_eq_isDigit : Char.isDigit = isDigit := rfl

theorem span_loop_eq {α : Type} (p : α → Bool) (l acc : List α) :
    List.span.loop p l acc = (acc.reverse ++ l.takeWhile p, l.dropWhile p) := by
  induction l generalizing acc with
  | nil => simp [List.span.loop]
  | cons x l ih =>
    unfold List.span.loop
    cases h : p x <;> simp [h, ih]

theorem span_eq {α : Type} (p : α → Bool) (l : List α) :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, span_loop_eq]

/-- A number's parts: the sign, the digits of `D* [. D*]` as one integer,
the count of digits after the point, and the exponent. The value is
`±mant * 10 ^ (exp - frac)`. -/
structure Parts where
  neg : Bool
  mant : Nat
  frac : Nat
  exp : Int
  deriving DecidableEq, Repr

/-- An optional sign: `-` is negative. -/
def splitSign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | '+' :: r => (false, r)
  | r => (false, r)

/-- `[+-]? D+`, the exponent's digits, and nothing after. -/
def expDigits (r : List Char) : Option Int :=
  let (eneg, ds) := splitSign r
  if ds ≠ [] ∧ ds.all isDigit then
    some (if eneg then -(digitsVal ds : Int) else digitsVal ds)
  else none

/-- What may follow the mantissa: nothing, or an exponent. -/
def expPart : List Char → Option Int
  | [] => some 0
  | e :: r => if e = 'e' ∨ e = 'E' then expDigits r else none

/-- The fraction's digits, after a `.`. -/
def fracSplit : List Char → List Char × List Char
  | '.' :: r => r.span isDigit
  | r => ([], r)

/-- The mantissa and exponent, after the sign. -/
def afterSign (neg : Bool) (r : List Char) : Option Parts :=
  let (ip, r) := r.span isDigit
  let (fp, r) := fracSplit r
  if ip.isEmpty ∧ fp.isEmpty then none
  else (expPart r).map fun e => ⟨neg, digitsVal (ip ++ fp), fp.length, e⟩

/-- `[+-]? D* [. D*] [(e|E) [+-]? D+]` with a mantissa digit, by `span`. -/
def numParts (cs : List Char) : Option Parts :=
  afterSign (splitSign cs).1 (splitSign cs).2

/-! ## The grammar, as a fold -/

/-- The scan state. `phase`: 0 start, 1 after the sign, 2 integer digits,
3 fraction digits, 4 after `e`, 5 after the exponent's sign, 6 exponent
digits, 7 rejected. -/
structure St where
  phase : Nat := 0
  neg : Bool := false
  dig : Bool := false
  m : DigAcc := {}
  frac : Nat := 0
  eneg : Bool := false
  e : DigAcc := {}

/-- The first character of the mantissa. -/
@[inline] def St.mant1 (st : St) (c : Char) : St :=
  if isDigit c then { st with phase := 2, dig := true, m := st.m.push (digitVal c) }
  else if c = '.' then { st with phase := 3 }
  else { st with phase := 7 }

/-- The first character of the exponent's digits. -/
@[inline] def St.exp1 (st : St) (c : Char) : St :=
  if isDigit c then { st with phase := 6, e := st.e.push (digitVal c) }
  else { st with phase := 7 }

/-- One character. -/
def St.step (st : St) (c : Char) : St :=
  match st.phase with
  | 0 =>
    if c = '-' then { st with phase := 1, neg := true }
    else if c = '+' then { st with phase := 1 }
    else st.mant1 c
  | 1 => st.mant1 c
  | 2 =>
    if isDigit c then { st with m := st.m.push (digitVal c) }
    else if c = '.' then { st with phase := 3 }
    else if c = 'e' ∨ c = 'E' then { st with phase := 4 }
    else { st with phase := 7 }
  | 3 =>
    if isDigit c then { st with dig := true, m := st.m.push (digitVal c), frac := st.frac + 1 }
    else if c = 'e' ∨ c = 'E' then { st with phase := 4 }
    else { st with phase := 7 }
  | 4 =>
    if c = '-' then { st with phase := 5, eneg := true }
    else if c = '+' then { st with phase := 5 }
    else st.exp1 c
  | 5 => st.exp1 c
  | 6 => if isDigit c then { st with e := st.e.push (digitVal c) } else { st with phase := 7 }
  | _ => st

/-- The parts, when the scan ended inside a number. -/
def St.finish (st : St) : Option Parts :=
  if st.dig ∧ (st.phase = 2 ∨ st.phase = 3 ∨ st.phase = 6) then
    some ⟨st.neg, st.m.val, st.frac, if st.eneg then -(st.e.val : Int) else st.e.val⟩
  else none

/-- `numParts`, in one pass over the string. -/
def numScan (s : String) : Option Parts := (s.foldl St.step {}).finish

/-! ## The fold is the grammar -/

/-- Digits pushed onto an accumulator. -/
def pushAll (a : DigAcc) (l : List Char) : DigAcc := l.foldl (fun a c => a.push (digitVal c)) a

theorem pushAll_val (a : DigAcc) (l : List Char) :
    (pushAll a l).val = l.foldl (fun n c => n * 10 + digitVal c) a.val :=
  DigAcc.val_foldl a l

theorem pushAll_empty_val (l : List Char) : (pushAll {} l).val = digitsVal l := by
  rw [pushAll_val, digitsVal_eq, DigAcc.val_empty]; rfl

theorem foldl_dead (st : St) (h : st.phase = 7) (l : List Char) : l.foldl St.step st = st := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [St.step, h, ih]

theorem step_ge (st : St) (h : st.phase ≥ 7) (c : Char) : St.step st c = st := by
  unfold St.step; split <;> first | omega | rfl

theorem finish_dead (st : St) (h : st.phase = 7) : st.finish = none := by
  simp [St.finish, h]

@[simp] theorem foldl_dead_mk (l : List Char) (a b : Bool) (m : DigAcc) (f : Nat) (en : Bool)
    (e : DigAcc) : l.foldl St.step ⟨7, a, b, m, f, en, e⟩ = ⟨7, a, b, m, f, en, e⟩ :=
  foldl_dead _ rfl l

@[simp] theorem finish_dead_mk (a b : Bool) (m : DigAcc) (f : Nat) (en : Bool) (e : DigAcc) :
    St.finish ⟨7, a, b, m, f, en, e⟩ = none := finish_dead _ rfl

/-- What the mantissa so far makes with an exponent part. -/
def tailOf (st : St) (r : List Char) : Option Parts :=
  if st.dig then (expPart r).map fun e => ⟨st.neg, st.m.val, st.frac, e⟩ else none

theorem scan6 (l : List Char) : ∀ (st : St), st.phase = 6 →
    (l.foldl St.step st).finish =
      if l.all isDigit then { st with e := pushAll st.e l }.finish else none := by
  induction l with
  | nil => intro st _; simp [pushAll]
  | cons c l ih =>
    intro st h
    by_cases hc : isDigit c
    · simp only [List.foldl_cons, St.step, h, hc, ↓reduceIte, List.all_cons, Bool.true_and]
      rw [ih _ rfl]; rfl
    · simp [St.step, h, hc]

theorem scan5 (l : List Char) (st : St) (h : st.phase = 5) :
    (l.foldl St.step st).finish =
      if l ≠ [] ∧ l.all isDigit then { st with phase := 6, e := pushAll st.e l }.finish else none := by
  cases l with
  | nil => simp [St.finish, h]
  | cons c l =>
    by_cases hc : isDigit c
    · simp only [List.foldl_cons, St.step, h, St.exp1, hc, ↓reduceIte]
      rw [scan6 l _ rfl]
      simp [hc, pushAll]
    · simp [St.step, h, St.exp1, hc]

theorem scan4 (l : List Char) (st : St) (h : st.phase = 4) (he : st.e = {}) (hn : st.eneg = false) :
    (l.foldl St.step st).finish =
      if st.dig then (expDigits l).map fun e => ⟨st.neg, st.m.val, st.frac, e⟩ else none := by
  have key : ∀ (eneg : Bool) (r : List Char) (st' : St), st'.phase = 5 → st'.eneg = eneg →
      st'.e = {} → st'.dig = st.dig → st'.neg = st.neg → st'.m = st.m → st'.frac = st.frac →
      (r.foldl St.step st').finish =
        if st.dig then (if r ≠ [] ∧ r.all isDigit then
          some (⟨st.neg, st.m.val, st.frac,
            if eneg then -(digitsVal r : Int) else digitsVal r⟩ : Parts) else none).map id
        else none := by
    intro eneg r st' h5 h1 h2 h3 h4 h6 h7
    rw [scan5 r st' h5]
    by_cases hr : r ≠ [] ∧ r.all isDigit
    · simp only [hr, St.finish, h1, h2, h3, h4, h6, h7, pushAll_empty_val]
      cases st.dig <;> simp
    · simp only [hr, ↓reduceIte]; cases st.dig <;> simp
  cases l with
  | nil => simp [St.finish, h, expDigits, splitSign]
  | cons c r =>
    by_cases hm : c = '-'
    · subst hm
      simp only [List.foldl_cons, St.step, h, ↓reduceIte]
      rw [key true r ⟨5, st.neg, st.dig, st.m, st.frac, true, st.e⟩ rfl rfl he rfl rfl rfl rfl]
      simp only [expDigits, splitSign, ne_eq]
      cases st.dig <;> simp
    · by_cases hp : c = '+'
      · subst hp
        simp only [List.foldl_cons, St.step, h, hm, ↓reduceIte]
        rw [key false r ⟨5, st.neg, st.dig, st.m, st.frac, st.eneg, st.e⟩ rfl hn he rfl rfl rfl rfl]
        simp only [expDigits, splitSign, ne_eq]
        cases st.dig <;> simp
      · have e1 : (c :: r).foldl St.step st = (c :: r).foldl St.step { st with phase := 5 } := by
          simp only [List.foldl_cons]; congr 1
          simp only [St.step, h, hm, hp, ↓reduceIte, St.exp1]
        rw [e1, key false (c :: r) { st with phase := 5 } rfl hn he rfl rfl rfl rfl]
        have hs : splitSign (c :: r) = (false, c :: r) := by
          unfold splitSign; split <;> simp_all
        simp only [expDigits, hs, ne_eq]
        cases st.dig <;> simp

theorem scanTail (r : List Char) (st : St) (hp : st.phase = 2 ∨ st.phase = 3) (he : st.e = {})
    (hn : st.eneg = false) (hd : ∀ c ∈ r.head?, isDigit c = false)
    (hdot : st.phase = 2 → r.head? ≠ some '.') :
    (r.foldl St.step st).finish = tailOf st r := by
  cases r with
  | nil =>
    rcases hp with hp | hp <;> cases hdg : st.dig <;>
      simp [St.finish, tailOf, expPart, he, hn, hp, hdg]
  | cons c r =>
    have hc : isDigit c = false := hd c rfl
    by_cases hx : c = 'e' ∨ c = 'E'
    · have e1 : St.step st c = { st with phase := 4 } := by
        rcases hp with hp | hp
        · have : c ≠ '.' := fun h => hdot hp (by simp [h])
          simp [St.step, hp, hc, hx, this]
        · simp [St.step, hp, hc, hx]
      rw [List.foldl_cons, e1, scan4 r { st with phase := 4 } rfl he hn]
      simp [tailOf, expPart, hx]
    · have e1 : St.step st c = { st with phase := 7 } := by
        rcases hp with hp | hp
        · have : c ≠ '.' := fun h => hdot hp (by simp [h])
          simp [St.step, hp, hc, hx, this]
        · simp [St.step, hp, hc, hx]
      rw [List.foldl_cons, e1, foldl_dead _ rfl, finish_dead _ rfl]
      simp [tailOf, expPart, hx]

/-- After the point: the fraction's digits, then the exponent part. -/
def fracTail (st : St) (r : List Char) : Option Parts :=
  let fp := r.takeWhile isDigit
  tailOf { st with dig := st.dig || !fp.isEmpty, m := pushAll st.m fp, frac := st.frac + fp.length }
    (r.dropWhile isDigit)

/-- After the integer digits: a point and a fraction, or the exponent part. -/
def intTail (st : St) : List Char → Option Parts
  | '.' :: r => fracTail st r
  | r => tailOf st r

theorem head_dropWhile (r : List Char) : ∀ c ∈ (r.dropWhile isDigit).head?, isDigit c = false := by
  intro c hc
  induction r with
  | nil => simp at hc
  | cons x r ih =>
    by_cases hx : isDigit x
    · simp [hx] at hc; exact ih hc
    · simp [hx] at hc; subst hc; simpa using hx

theorem scan3 (l : List Char) : ∀ (st : St), st.phase = 3 → st.e = {} → st.eneg = false →
    (l.foldl St.step st).finish = fracTail st l := by
  induction l with
  | nil =>
    intro st h he hn
    rw [scanTail [] st (Or.inr h) he hn (by simp) (by simp [h])]
    simp [fracTail, pushAll]
  | cons c l ih =>
    intro st h he hn
    by_cases hc : isDigit c
    · have e1 : St.step st c =
          { st with dig := true, m := st.m.push (digitVal c), frac := st.frac + 1 } := by
        simp [St.step, h, hc]
      rw [List.foldl_cons, e1,
        ih { st with dig := true, m := st.m.push (digitVal c), frac := st.frac + 1 } h he hn]
      simp only [fracTail, List.takeWhile_cons, List.dropWhile_cons, hc, ↓reduceIte, pushAll,
        List.foldl_cons, List.isEmpty_cons, List.length_cons]
      congr 2
      all_goals first | simp | omega
    · rw [scanTail (c :: l) st (Or.inr h) he hn (by simp [hc]) (by simp [h])]
      simp [fracTail, hc, pushAll]

theorem scan2 (l : List Char) : ∀ (st : St), st.phase = 2 → st.e = {} → st.eneg = false →
    (l.foldl St.step st).finish =
      intTail { st with m := pushAll st.m (l.takeWhile isDigit) } (l.dropWhile isDigit) := by
  induction l with
  | nil =>
    intro st h he hn
    rw [scanTail [] st (Or.inl h) he hn (by simp) (by simp)]
    simp [intTail, pushAll]
  | cons c l ih =>
    intro st h he hn
    by_cases hc : isDigit c
    · have e1 : St.step st c = { st with m := st.m.push (digitVal c) } := by
        simp [St.step, h, hc]
      rw [List.foldl_cons, e1, ih { st with m := st.m.push (digitVal c) } h he hn]
      simp [hc, pushAll]
    · by_cases hd : c = '.'
      · subst hd
        have e1 : St.step st '.' = { st with phase := 3 } := by
          simp [St.step, h, hc]
        rw [List.foldl_cons, e1, scan3 l { st with phase := 3 } rfl he hn]
        simp [intTail, hc, pushAll, fracTail, tailOf]
      · rw [scanTail (c :: l) st (Or.inl h) he hn (by simp [hc]) (by simp [hd])]
        have : intTail st (c :: l) = tailOf st (c :: l) := by
          unfold intTail; split <;> simp_all
        simp [hc, pushAll, this]

theorem pushAll_append (a : DigAcc) (l₁ l₂ : List Char) :
    pushAll (pushAll a l₁) l₂ = pushAll a (l₁ ++ l₂) := by
  simp [pushAll, List.foldl_append]

theorem scan1 (neg : Bool) (l : List Char) :
    (l.foldl St.step ⟨1, neg, false, {}, 0, false, {}⟩).finish = afterSign neg l := by
  cases l with
  | nil => simp [St.finish, afterSign, fracSplit, span_eq]
  | cons c r =>
    by_cases hc : isDigit c
    · have e1 : St.step ⟨1, neg, false, {}, 0, false, {}⟩ c =
          ⟨2, neg, true, pushAll {} [c], 0, false, {}⟩ := by
        simp [St.step, St.mant1, hc, pushAll]
      rw [List.foldl_cons, e1, scan2 r _ rfl rfl rfl]
      simp only [afterSign, span_eq, List.takeWhile_cons, List.dropWhile_cons, hc, ↓reduceIte,
        pushAll_append]
      generalize r.takeWhile isDigit = ip
      generalize r.dropWhile isDigit = R
      cases R with
      | nil => simp [intTail, fracSplit, tailOf, expPart, pushAll_empty_val]
      | cons x R =>
        by_cases hx : x = '.'
        · subst hx
          simp [intTail, fracSplit, fracTail, tailOf, span_eq, pushAll_append, pushAll_empty_val]
        · have h1 : fracSplit (x :: R) = ([], x :: R) := by
            unfold fracSplit; split <;> simp_all
          have h2 : intTail ⟨2, neg, true, pushAll {} (c :: ip), 0, false, {}⟩ (x :: R) =
              tailOf ⟨2, neg, true, pushAll {} (c :: ip), 0, false, {}⟩ (x :: R) := by
            unfold intTail; split <;> simp_all
          simp only [List.singleton_append] at *
          rw [h1, h2]
          simp [tailOf, pushAll_empty_val]
    · by_cases hd : c = '.'
      · subst hd
        have e1 : St.step ⟨1, neg, false, {}, 0, false, {}⟩ '.' = ⟨3, neg, false, {}, 0, false, {}⟩ := by
          simp [St.step, St.mant1, hc]
        rw [List.foldl_cons, e1, scan3 r _ rfl rfl rfl]
        simp only [afterSign, span_eq, List.takeWhile_cons, List.dropWhile_cons, hc, fracSplit,
          fracTail, tailOf]
        cases hf : (r.takeWhile isDigit).isEmpty <;> simp [hf, pushAll_empty_val]
      · have e1 : St.step ⟨1, neg, false, {}, 0, false, {}⟩ c = ⟨7, neg, false, {}, 0, false, {}⟩ := by
          simp [St.step, St.mant1, hc, hd]
        have h1 : fracSplit (c :: r) = ([], c :: r) := by
          unfold fracSplit; split <;> simp_all
        rw [List.foldl_cons, e1, foldl_dead _ rfl, finish_dead _ rfl]
        simp [afterSign, span_eq, hc, h1]

/-- The fold is the grammar. -/
theorem numScan_eq (s : String) : numScan s = numParts s.toList := by
  unfold numScan numParts
  rw [String.foldl_eq_foldl_toList]
  generalize s.toList = l
  cases l with
  | nil => simp [St.finish, splitSign, afterSign, fracSplit, span_eq]
  | cons c r =>
    by_cases hm : c = '-'
    · subst hm
      have e1 : St.step {} '-' = ⟨1, true, false, {}, 0, false, {}⟩ := by simp [St.step]
      rw [List.foldl_cons, e1, scan1]; rfl
    · by_cases hp : c = '+'
      · subst hp
        have e1 : St.step {} '+' = ⟨1, false, false, {}, 0, false, {}⟩ := by simp [St.step]
        rw [List.foldl_cons, e1, scan1]; rfl
      · have e1 : St.step {} c = St.step ⟨1, false, false, {}, 0, false, {}⟩ c := by
          simp [St.step, hm, hp]; rfl
        have hs : splitSign (c :: r) = (false, c :: r) := by
          unfold splitSign; split <;> simp_all
        rw [List.foldl_cons, e1, ← List.foldl_cons, scan1, hs]

/-! ## What a number is made of -/

/-- The characters a number may contain. -/
def allowed : List Char := "0123456789+-.eE".toList

theorem isDigit_mem {c : Char} (h : isDigit c = true) : c ∈ allowed := by
  have h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, h.2⟩
  have : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
      c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h <;>
    · have : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
      rw [h] at this; subst this; decide

theorem step_dead_of_not_allowed (st : St) (c : Char) (hc : c ∉ allowed) :
    (St.step st c).phase ≥ 7 := by
  have hd : isDigit c = false := by
    cases h : isDigit c
    · rfl
    · exact absurd (isDigit_mem h) hc
  have hne : ∀ x ∈ allowed, c ≠ x := fun x hx h => hc (h ▸ hx)
  have h1 : c ≠ '+' := hne _ (by decide)
  have h2 : c ≠ '-' := hne _ (by decide)
  have h3 : c ≠ '.' := hne _ (by decide)
  have h4 : c ≠ 'e' := hne _ (by decide)
  have h5 : c ≠ 'E' := hne _ (by decide)
  unfold St.step
  split
  all_goals (try simp_all [St.mant1, St.exp1])
  all_goals omega

theorem foldl_ge (l : List Char) (st : St) (h : st.phase ≥ 7) : l.foldl St.step st = st := by
  induction l with
  | nil => rfl
  | cons c l ih => rw [List.foldl_cons, step_ge st h, ih]

theorem scan_allowed (l : List Char) : ∀ (st : St), (l.foldl St.step st).finish ≠ none →
    ∀ c ∈ l, c ∈ allowed := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro st h c hc
    by_cases hx : x ∈ allowed
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hx
      · exact ih _ h c hc
    · exfalso
      apply h
      rw [List.foldl_cons, foldl_ge _ _ (step_dead_of_not_allowed st x hx)]
      have := step_dead_of_not_allowed st x hx
      simp only [St.finish]
      split
      · omega
      · rfl

/-- A scanned number holds only number characters. -/
theorem numScan_allowed {s : String} {p : Parts} (h : numScan s = some p) :
    ∀ c ∈ s.toList, c ∈ allowed := by
  unfold numScan at h
  rw [String.foldl_eq_foldl_toList] at h
  exact scan_allowed _ {} (by simp [h])

/-- After the sign, a number starts with a digit or a point. -/
theorem afterSign_head {neg : Bool} {r : List Char} {p : Parts} (h : afterSign neg r = some p) :
    ∃ c t, r = c :: t ∧ (isDigit c = true ∨ c = '.') := by
  cases r with
  | nil => simp [afterSign, span_eq, fracSplit] at h
  | cons c t =>
    refine ⟨c, t, rfl, ?_⟩
    by_cases hc : isDigit c = true
    · exact Or.inl hc
    · by_cases hd : c = '.'
      · exact Or.inr hd
      · exfalso
        have h1 : fracSplit (c :: t) = ([], c :: t) := by
          unfold fracSplit; split <;> simp_all
        simp [afterSign, span_eq, hc, h1] at h

end NumScan

end LeanPydantic
