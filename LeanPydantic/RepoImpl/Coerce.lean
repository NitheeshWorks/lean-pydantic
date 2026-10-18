import LeanPydantic.RepoImpl.Number
import LeanPydantic.RepoImpl.NumScan

/-!
# RepoImpl: lax-mode coercions

pydantic-core's lax mode turns strings, booleans and floats into the requested
scalar. These follow `src/input/shared.rs` and `src/input/input_json.rs` of
pydantic-core 2.50.1 rule for rule, on character lists:

* `strAsInt`: a JSON integer literal (one whose leading literal is over
  4300 characters is `int_parsing_size`, decided in one pass); otherwise the
  string is cleaned
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

-- An ASCII digit, and the value of a list of digits: `NumScan`'s, a
-- product tree that `NumScan.digitsVal_eq` proves equal to the digit fold.
export NumScan (isDigit digitsVal)


/-- Whether the characters are a JSON integer literal, without converting. -/
def isJsonInt (cs : List Char) : Bool :=
  let ds := match cs with
    | '-' :: r => r
    | r => r
  match ds with
  | [] => false
  | '0' :: _ :: _ => false
  | ds => ds.all isDigit

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
  match cs.dropWhile (· ≠ '.') with
  | _ :: fp => if fp ≠ [] ∧ fp.all (· = '0') then cs.takeWhile (· ≠ '.') else cs
  | [] => cs

/-- pydantic-core's `strip_underscores`: remove single underscores between
other characters; `none` when there are none, or any are leading, trailing
or doubled. -/
def stripUnderscores (cs : List Char) : Option (List Char) :=
  if cs.head? = some '_' ∨ cs.getLast? = some '_' ∨ '_' ∉ cs ∨
      (cs.zip cs.tail).any (fun p => p.1 = '_' ∧ p.2 = '_') then none
  else some (cs.filter (· ≠ '_'))

/-- A leading `+` dropped (`+-` is invalid). -/
def stripPlus : List Char → Option (List Char)
  | '+' :: '-' :: _ => none
  | '+' :: r => some r
  | r => some r

/-- A leading `-` taken off as the sign (`--` and `-+` are invalid). -/
def splitSign : List Char → Option (Bool × List Char)
  | '-' :: '-' :: _ => none
  | '-' :: '+' :: _ => none
  | '-' :: r => some (true, r)
  | r => some (false, r)

/-- The end of `clean_int_str`: the `.0…` suffix and the underscores, then
the sign back. -/
def finishClean (s0 : List Char) (neg : Bool) (s : List Char) : Option (List Char) :=
  let s := stripDecimalZeros s
  let sign : List Char := if neg then ['-'] else []
  match stripUnderscores s with
  | some t => some (sign ++ t)
  | none => if s0.length = s.length then none else some (sign ++ s)

/-- pydantic-core's `clean_int_str`. -/
def cleanIntStr (s0 : List Char) : Option (List Char) :=
  (stripPlus (trim s0)).bind fun s =>
    (splitSign s).bind fun ns => (stripLeadingZeros ns.2).bind (finishClean s0 ns.1)

/-- Python's 4300-digit limit on `int(str)`, as jiter applies it (the sign
counts; see UP-025). -/
def maxIntLen : Nat := 4300


/-! ## Rejecting over-long digit runs in one pass -/

/-- What jiter reads first: an optional `-`, then a run of digits led by
`1`–`9`. `phase` 0: nothing read; 1: after `-`; 2: in the run; 3: done
(the run ended, or there is none). `len` counts the run with its sign. -/
structure PrefixScan where
  phase : Nat := 0
  len : Nat := 0
  deriving Inhabited

/-- One character of the prefix scan. -/
def PrefixScan.step (st : PrefixScan) (c : Char) : PrefixScan :=
  match st.phase with
  | 0 => if c = '-' then ⟨1, 1⟩ else if '1' ≤ c ∧ c ≤ '9' then ⟨2, 1⟩ else ⟨3, 0⟩
  | 1 => if '1' ≤ c ∧ c ≤ '9' then ⟨2, st.len + 1⟩ else ⟨3, 0⟩
  | 2 => if isDigit c then ⟨2, st.len + 1⟩ else ⟨3, st.len⟩
  | _ => st

/-- jiter's `NumberOutOfRange` on a string: its leading integer literal is
longer than 4300 characters (sign included), whatever follows it. -/
def longPrefix (cs : List Char) : Bool :=
  let st := cs.foldl PrefixScan.step {}
  decide (st.phase ≥ 2) && decide (st.len > maxIntLen)

/-- Counting the digits that every cleaning keeps: those from the first
`1`–`9` on, before any `.`. -/
structure KeptScan where
  nz : Bool := false
  dot : Bool := false
  count : Nat := 0
  deriving Inhabited

/-- One character of the count. -/
def KeptScan.step (st : KeptScan) (c : Char) : KeptScan :=
  let nz := st.nz || (decide ('1' ≤ c ∧ c ≤ '9') && !st.dot)
  { nz, dot := st.dot || c == '.', count := if nz && !st.dot && isDigit c then st.count + 1 else st.count }

/-- The digits every cleaning keeps. -/
def keptDigits (cs : List Char) : Nat := (cs.foldl KeptScan.step {}).count

theorem foldl_neutral (p : Char → Bool) (hp : ∀ st c, p c = false → KeptScan.step st c = st) :
    ∀ (l : List Char) (st : KeptScan), (l.filter p).foldl KeptScan.step st = l.foldl KeptScan.step st
  | [], _ => rfl
  | c :: l, st => by
    by_cases h : p c
    · simp [h, foldl_neutral p hp l]
    · simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, List.foldl_cons]
      rw [hp st c (by simpa using h), foldl_neutral p hp l]

theorem step_ws (st : KeptScan) (c : Char) (h : isWhitespace c = true) : KeptScan.step st c = st := by
  have h1 : ¬('1' ≤ c ∧ c ≤ '9') := by
    rintro ⟨a, b⟩; simp only [isWhitespace] at h
    have : 49 ≤ c.toNat := a; have : c.toNat ≤ 57 := b
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega
  have h2 : c ≠ '.' := by rintro rfl; simp [isWhitespace] at h
  have h3 : isDigit c = false := by
    simp only [isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.not_le]
    simp only [isWhitespace] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    by_cases hc : c.toNat < 48
    · left; exact hc
    · right; show 57 < c.toNat; omega
  cases st; simp [KeptScan.step, h1, h2, h3]

theorem foldl_ws : ∀ (l : List Char) (st : KeptScan), (∀ c ∈ l, isWhitespace c = true) →
    l.foldl KeptScan.step st = st
  | [], _, _ => rfl
  | c :: l, st, h => by
    simp only [List.foldl_cons]
    rw [step_ws st c (h c (by simp))]; exact foldl_ws l st (fun x hx => h x (by simp [hx]))

theorem trim_split (l : List Char) : ∃ a b, l = a ++ trim l ++ b ∧ (∀ c ∈ a, isWhitespace c = true) ∧
    ∀ c ∈ b, isWhitespace c = true := by
  refine ⟨l.takeWhile isWhitespace, ((l.dropWhile isWhitespace).reverse.takeWhile isWhitespace).reverse, ?_, ?_, ?_⟩
  · unfold trim
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := isWhitespace) (l := l)]
    rw [List.append_assoc]; congr 1
    have := List.takeWhile_append_dropWhile (p := isWhitespace) (l := (l.dropWhile isWhitespace).reverse)
    calc l.dropWhile isWhitespace = (l.dropWhile isWhitespace).reverse.reverse := by simp
      _ = (List.takeWhile isWhitespace (l.dropWhile isWhitespace).reverse ++
            List.dropWhile isWhitespace (l.dropWhile isWhitespace).reverse).reverse := by rw [this]
      _ = _ := List.reverse_append
  · intro c hc; exact List.all_eq_true.1 List.all_takeWhile c hc
  · intro c hc; exact List.all_eq_true.1 List.all_takeWhile c (List.mem_reverse.1 hc)

theorem kept_trim (st : KeptScan) (l : List Char) :
    (trim l).foldl KeptScan.step st = l.foldl KeptScan.step st := by
  obtain ⟨a, b, h, ha, hb⟩ := trim_split l
  conv => rhs; rw [h]
  simp only [List.foldl_append, foldl_ws a st ha, foldl_ws b _ hb]


/-- `-`, `+`, `_` and white space change nothing in the count. -/
def Neutral (c : Char) : Prop := c = '-' ∨ c = '+' ∨ c = '_' ∨ isWhitespace c = true

theorem step_neutral (st : KeptScan) (c : Char) (h : Neutral c) : KeptScan.step st c = st := by
  rcases h with rfl | rfl | rfl | h
  · cases st; simp [KeptScan.step, isDigit]
  · cases st; simp [KeptScan.step, isDigit]
  · cases st; simp [KeptScan.step, isDigit]
  · exact step_ws st c h

theorem step_zero_init : KeptScan.step {} '0' = {} := by simp [KeptScan.step, isDigit]

theorem stripZerosAfter_kept (prev : Char) (hp : prev = '0' ∨ prev = '_') :
    ∀ (r r' : List Char), stripZerosAfter prev r = some r' →
      r'.foldl KeptScan.step {} = r.foldl KeptScan.step {}
  | [], r', h => by
    simp only [stripZerosAfter, Option.some.injEq] at h; subst h
    rcases hp with rfl | rfl
    · simp [step_zero_init]
    · simp [step_neutral _ _ (Or.inr (Or.inr (Or.inl rfl)) : _)]
  | c :: r, r', h => by
    unfold stripZerosAfter at h
    split at h
    · rename_i hc
      rw [stripZerosAfter_kept c hc r r' h]
      rcases hc with rfl | rfl
      · simp [step_zero_init]
      · simp [step_neutral _ _ (Or.inr (Or.inr (Or.inl rfl)) : _)]
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          rcases hp with rfl | rfl
          · simp [step_zero_init]
          · simp [step_neutral _ _ (Or.inr (Or.inr (Or.inl rfl)) : _)]
        · cases h

theorem stripLeadingZeros_kept (s s' : List Char) (h : stripLeadingZeros s = some s') :
    s'.foldl KeptScan.step {} = s.foldl KeptScan.step {} := by
  unfold stripLeadingZeros at h
  split at h
  · rename_i r
    rw [stripZerosAfter_kept '0' (.inl rfl) r s' h]; simp [step_zero_init]
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  · cases h

theorem count_after_dot : ∀ (l : List Char) (st : KeptScan), st.dot = true →
    (l.foldl KeptScan.step st).count = st.count
  | [], _, _ => rfl
  | c :: l, st, h => by
    simp only [List.foldl_cons]
    rw [count_after_dot l _ (by simp [KeptScan.step, h])]
    simp [KeptScan.step, h]

theorem dropWhile_cons_head (p : Char → Bool) :
    ∀ (l fp : List Char) (x : Char), l.dropWhile p = x :: fp → p x = false
  | [], _, _, h => by simp at h
  | y :: l, fp, x, h => by
    simp only [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_cons_head p l fp x h
    · rename_i hy; simp only [List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simpa using hy

theorem stripDecimalZeros_kept (s : List Char) :
    ((stripDecimalZeros s).foldl KeptScan.step {}).count = (s.foldl KeptScan.step {}).count := by
  unfold stripDecimalZeros
  split
  · rename_i x fp hs
    split
    · have hx : x = '.' := by have := dropWhile_cons_head _ s fp x hs; simpa using this
      subst hx
      have hsplit : s = s.takeWhile (fun c => decide (c ≠ '.')) ++ ('.' :: fp) := by
        conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c => decide (c ≠ '.')) (l := s)]
        rw [hs]
      conv => rhs; rw [hsplit]
      rw [List.foldl_append, List.foldl_cons, count_after_dot fp _ (by simp [KeptScan.step])]
      simp [KeptScan.step, isDigit]
    · rfl
  · rfl

theorem stripUnderscores_eq (s t : List Char) (h : stripUnderscores s = some t) : t = s.filter (· ≠ '_') := by
  unfold stripUnderscores at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h; exact h.symm

theorem kept_filter_underscore (s : List Char) (st : KeptScan) :
    (s.filter (fun c => decide (c ≠ '_'))).foldl KeptScan.step st = s.foldl KeptScan.step st :=
  foldl_neutral _ (fun st c h => step_neutral st c (Or.inr (Or.inr (Or.inl (by simpa using h))))) s st

theorem kept_cons_neutral (c : Char) (l : List Char) (h : Neutral c) (st : KeptScan) :
    (c :: l).foldl KeptScan.step st = l.foldl KeptScan.step st := by
  simp [step_neutral st c h]

theorem stripPlus_kept (s s' : List Char) (h : stripPlus s = some s') :
    s'.foldl KeptScan.step {} = s.foldl KeptScan.step {} := by
  unfold stripPlus at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h; subst h; rename_i r _; rw [kept_cons_neutral '+' r (.inr (.inl rfl))]
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem splitSign_kept (s : List Char) (ns : Bool × List Char) (h : splitSign s = some ns) :
    ns.2.foldl KeptScan.step {} = s.foldl KeptScan.step {} := by
  unfold splitSign at h
  split at h
  · cases h
  · cases h
  · simp only [Option.some.injEq] at h; subst h; rename_i r _ _; rw [kept_cons_neutral '-' r (.inl rfl)]
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem finishClean_kept (s0 : List Char) (neg : Bool) (s c : List Char) (h : finishClean s0 neg s = some c) :
    (c.foldl KeptScan.step {}).count = (s.foldl KeptScan.step {}).count := by
  have hsign : ∀ l : List Char, ((if neg = true then ['-'] else []) ++ l).foldl KeptScan.step {} =
      l.foldl KeptScan.step {} := by
    intro l; split
    · exact kept_cons_neutral '-' l (.inl rfl) {}
    · rfl
  unfold finishClean at h
  simp only at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq] at h; subst h
    rw [hsign, stripUnderscores_eq _ _ ht, kept_filter_underscore, stripDecimalZeros_kept]
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h
      rw [hsign, stripDecimalZeros_kept]

/-- **Cleaning keeps the counted digits.** -/
theorem cleanIntStr_kept (s0 c : List Char) (h : cleanIntStr s0 = some c) : keptDigits c = keptDigits s0 := by
  unfold keptDigits
  rw [← kept_trim {} s0]
  unfold cleanIntStr at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, ns, h₂, s₃, h₃, h₄⟩ := h
  rw [finishClean_kept _ _ _ _ h₄, stripLeadingZeros_kept _ _ h₃, splitSign_kept _ _ h₂, stripPlus_kept _ _ h₁]

theorem count_le : ∀ (l : List Char) (st : KeptScan), (l.foldl KeptScan.step st).count ≤ st.count + l.length
  | [], _ => by simp
  | c :: l, st => by
    simp only [List.foldl_cons, List.length_cons]
    have := count_le l (KeptScan.step st c)
    have : (KeptScan.step st c).count ≤ st.count + 1 := by simp only [KeptScan.step]; split <;> omega
    omega

theorem keptDigits_le (l : List Char) : keptDigits l ≤ l.length := by
  have := count_le l {}; simpa [keptDigits] using this


theorem prefix_digits : ∀ (r : List Char) (n : Nat), (∀ c ∈ r, isDigit c = true) →
    r.foldl PrefixScan.step ⟨2, n⟩ = ⟨2, n + r.length⟩
  | [], n, _ => rfl
  | c :: r, n, h => by
    simp only [List.foldl_cons]
    have hc : isDigit c = true := h c (by simp)
    rw [show PrefixScan.step ⟨2, n⟩ c = ⟨2, n + 1⟩ by simp [PrefixScan.step, hc],
      prefix_digits r (n + 1) (fun x hx => h x (by simp [hx]))]
    simp; omega

theorem nonzero_of_digit (d : Char) (hd : isDigit d = true) (h0 : d ≠ '0') : '1' ≤ d ∧ d ≤ '9' := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨a, b⟩ := hd
  have a' : 48 ≤ d.toNat := a
  have : d.toNat ≠ 48 := fun e => h0 (Char.toNat_inj.1 (by simpa using e))
  exact ⟨show 49 ≤ d.toNat by omega, b⟩

theorem jsonDigits_body (d : Char) (r : List Char) (hd0 : d ≠ '0')
    (hall : (d :: r).all isDigit = true) : ('1' ≤ d ∧ d ≤ '9') ∧ ∀ c ∈ r, isDigit c = true := by
  simp only [List.all_cons, Bool.and_eq_true] at hall
  exact ⟨nonzero_of_digit d hall.1 hd0, List.all_eq_true.1 hall.2⟩

theorem jsonDigits_unsigned (d : Char) (r : List Char) (hr : r ≠ []) (hd : d ≠ '-')
    (hj : isJsonInt (d :: r) = true) : ('1' ≤ d ∧ d ≤ '9') ∧ ∀ c ∈ r, isDigit c = true := by
  obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by cases r with
    | nil => exact absurd rfl hr
    | cons y ys => exact ⟨y, ys, rfl⟩
  by_cases hd0 : d = '0'
  · subst hd0; simp [isJsonInt] at hj
  · apply jsonDigits_body d _ hd0
    unfold isJsonInt at hj
    split at hj
    · rename_i heq; simp at heq; exact absurd heq.1 hd
    · simp only at hj
      split at hj
      · simp at hj
      · rename_i h; simp at h; exact absurd h.1 hd0
      · exact hj

theorem jsonDigits_signed (d : Char) (r : List Char) (hr : r ≠ [])
    (hj : isJsonInt ('-' :: d :: r) = true) : ('1' ≤ d ∧ d ≤ '9') ∧ ∀ c ∈ r, isDigit c = true := by
  obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by cases r with
    | nil => exact absurd rfl hr
    | cons y ys => exact ⟨y, ys, rfl⟩
  by_cases hd0 : d = '0'
  · subst hd0; simp [isJsonInt] at hj
  · apply jsonDigits_body d _ hd0
    unfold isJsonInt at hj
    simp only at hj
    split at hj
    · simp at hj
    · rename_i h; simp at h; exact absurd h.1 hd0
    · exact hj

theorem isJsonInt_long (cs : List Char) (hj : isJsonInt cs = true) (hl : cs.length > maxIntLen) :
    longPrefix cs = true := by
  have hm : maxIntLen = 4300 := rfl
  simp only [longPrefix, Bool.and_eq_true, decide_eq_true_eq]
  cases cs with
  | nil => simp [hm] at hl
  | cons x xs =>
    by_cases hx : x = '-'
    · subst hx
      cases xs with
      | nil => simp [hm] at hl
      | cons d r =>
        have hr : r ≠ [] := by rintro rfl; simp [hm] at hl
        obtain ⟨hnz, hdig⟩ := jsonDigits_signed d r hr hj
        simp only [List.foldl_cons]
        rw [show PrefixScan.step {} '-' = ⟨1, 1⟩ by simp [PrefixScan.step],
          show PrefixScan.step ⟨1, 1⟩ d = ⟨2, 2⟩ by simp [PrefixScan.step, hnz],
          prefix_digits r 2 hdig]
        simp only [List.length_cons] at hl; simp; omega
    · have hr : xs ≠ [] := by rintro rfl; simp [hm] at hl
      obtain ⟨hnz, hdig⟩ := jsonDigits_unsigned x xs hr hx hj
      simp only [List.foldl_cons]
      rw [show PrefixScan.step {} x = ⟨2, 1⟩ by simp [PrefixScan.step, hx, hnz], prefix_digits xs 1 hdig]
      simp only [List.length_cons] at hl; simp; omega

/-- pydantic-core's `str_as_int`, on the characters: jiter first, which
reports `int_parsing_size` when the leading integer literal is too long,
whatever follows; then the cleaned string, where too long is `int_parsing`. -/
def strAsIntChars (cs : List Char) : Except ErrorKind Int :=
  if longPrefix cs then .error .intParsingSize
  else if isJsonInt cs then
    match jsonInt? cs with
    | some i => .ok i
    | none => .error .intParsing
  else
    match cleanIntStr cs with
    | some c =>
      if c.length > maxIntLen then .error .intParsing
      else match jsonInt? c with
        | some i => .ok i
        | none => .error .intParsing
    | none => .error .intParsing

/-- **Too many kept digits is `int_parsing`**: no cleaning can bring them
under the limit. -/
theorem strAsIntChars_kept (cs : List Char) (hp : longPrefix cs = false) (hk : keptDigits cs > maxIntLen) :
    strAsIntChars cs = .error .intParsing := by
  unfold strAsIntChars
  simp only [hp, Bool.false_eq_true, ite_false]
  split
  · rename_i hj
    exfalso
    by_cases hl : cs.length > maxIntLen
    · rw [isJsonInt_long cs hj hl] at hp; cases hp
    · have := keptDigits_le cs; omega
  · split
    · rename_i c hc
      have h1 := cleanIntStr_kept cs c hc
      have h2 := keptDigits_le c
      have : c.length > maxIntLen := by omega
      simp [this]
    · rfl

/-- The prefix scan and the count side by side, in one flat cell. -/
structure IntScan where
  phase : Nat := 0
  len : Nat := 0
  nz : Bool := false
  dot : Bool := false
  count : Nat := 0

/-- Both scans' step, written out on the flat cell. -/
def IntScan.step (st : IntScan) (c : Char) : IntScan :=
  let digit := '0' ≤ c && c ≤ '9'
  let nonzero := '1' ≤ c && c ≤ '9'
  let nz := st.nz || (nonzero && !st.dot)
  let count := if nz && !st.dot && digit then st.count + 1 else st.count
  let dot := st.dot || c == '.'
  match st.phase with
  | 0 => if c = '-' then ⟨1, 1, nz, dot, count⟩ else if nonzero then ⟨2, 1, nz, dot, count⟩ else ⟨3, 0, nz, dot, count⟩
  | 1 => if nonzero then ⟨2, st.len + 1, nz, dot, count⟩ else ⟨3, 0, nz, dot, count⟩
  | 2 => if digit then ⟨2, st.len + 1, nz, dot, count⟩ else ⟨3, st.len, nz, dot, count⟩
  | _ => ⟨st.phase, st.len, nz, dot, count⟩

theorem IntScan.step_proj (st : IntScan) (c : Char) :
    PrefixScan.step ⟨st.phase, st.len⟩ c = ⟨(st.step c).phase, (st.step c).len⟩ ∧
    KeptScan.step ⟨st.nz, st.dot, st.count⟩ c = ⟨(st.step c).nz, (st.step c).dot, (st.step c).count⟩ := by
  obtain ⟨phase, len, nz, dot, count⟩ := st
  have hAC : '1' ≤ c → '0' ≤ c := fun h => Char.le_trans (by decide) h
  by_cases h1 : c = '-'
  · subst h1; rcases phase with _ | _ | _ | n <;> simp [PrefixScan.step, KeptScan.step, IntScan.step, isDigit]
  · by_cases hA : '1' ≤ c <;> by_cases hB : c ≤ '9' <;> by_cases hC : '0' ≤ c <;>
      (try exact absurd (hAC hA) hC) <;>
      rcases phase with _ | _ | _ | n <;>
      simp [PrefixScan.step, KeptScan.step, IntScan.step, isDigit, hA, hB, hC, h1]

/-- The prefix scan and the count, in one pass over the string. -/
def intScan (s : String) : IntScan := s.foldl IntScan.step {}

theorem foldl_intScan : ∀ (l : List Char) (st : IntScan),
    (l.foldl IntScan.step st).phase = (l.foldl PrefixScan.step ⟨st.phase, st.len⟩).phase ∧
    (l.foldl IntScan.step st).len = (l.foldl PrefixScan.step ⟨st.phase, st.len⟩).len ∧
    (l.foldl IntScan.step st).count = (l.foldl KeptScan.step ⟨st.nz, st.dot, st.count⟩).count
  | [], _ => ⟨rfl, rfl, rfl⟩
  | c :: l, st => by
    simp only [List.foldl_cons]
    obtain ⟨hp, hk⟩ := IntScan.step_proj st c
    rw [hp, hk]
    exact foldl_intScan l (IntScan.step st c)

theorem intScan_eq (s : String) :
    (intScan s).phase = (s.toList.foldl PrefixScan.step {}).phase ∧
    (intScan s).len = (s.toList.foldl PrefixScan.step {}).len ∧
    (intScan s).count = keptDigits s.toList := by
  unfold intScan keptDigits; rw [String.foldl_eq_foldl_toList]; exact foldl_intScan _ _

/-- pydantic-core's `str_as_int`. One pass over the string decides the
over-long cases (any length, any form), so a megabyte header is rejected
without building a list; the rest is `strAsIntChars` (`strAsInt_eq`). -/
def strAsInt (s : String) : Except ErrorKind Int :=
  let st := intScan s
  if decide (st.phase ≥ 2) && decide (st.len > maxIntLen) then .error .intParsingSize
  else if st.count > maxIntLen then .error .intParsing
  else strAsIntChars s.toList

theorem strAsInt_eq (s : String) : strAsInt s = strAsIntChars s.toList := by
  obtain ⟨h1, h2, h3⟩ := intScan_eq s
  unfold strAsInt
  simp only [h1, h2, h3]
  split
  · rename_i h
    have hp : longPrefix s.toList = true := by simpa [longPrefix] using h
    simp [strAsIntChars, hp]
  · rename_i h
    have hp : longPrefix s.toList = false := by simpa [longPrefix] using h
    split
    · rename_i hk
      exact (strAsIntChars_kept _ hp hk).symm
    · rfl

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

/-- pydantic-core's `str_as_float`, for an exact `float`, on the characters. -/
def strAsFloatChars (cs : List Char) : Except ErrorKind Decimal :=
  let res := match rustFloat? (trim cs) with
    | some r => some r
    | none => stripUnderscores cs >>= rustFloat?
  match res with
  | some (some d) => .ok d
  | some none => .error .finiteNumber
  | none => .error .floatParsing

/-- pydantic-core's `str_as_float` for a plain `float` (`allow_inf_nan=True`),
on the characters: the number, `NaN` and the infinities included. -/
def strAsNumberChars (cs : List Char) : Except ErrorKind Number :=
  let classify (cs : List Char) (r : Option (Option Decimal)) : Option Number :=
    r.map fun
      | some d => .float d
      | none =>
        let low := String.ofList (cs.map Char.toLower)
        if low.endsWith "nan" then .nan else if cs.head? = some '-' then .negInf else .inf
  let t := trim cs
  let res := match classify t (rustFloat? t) with
    | some r => some r
    | none => stripUnderscores cs >>= fun u => classify u (rustFloat? u)
  match res with
  | some n => .ok n
  | none => .error .floatParsing

/-- A scanned number as an exact decimal. -/
def partsDecimal (p : NumScan.Parts) : Decimal := Decimal.normalize p.neg p.mant (p.exp - p.frac)

/-- pydantic-core's `str_as_float`, for an exact `float`: a plain number is
read in place (`NumScan.numScan`), anything else on the characters
(`strAsFloat_eq`). -/
def strAsFloat (s : String) : Except ErrorKind Decimal :=
  match NumScan.numScan s with
  | some p => .ok (partsDecimal p)
  | none => strAsFloatChars s.toList

/-- pydantic-core's `str_as_float` for a plain `float` (`allow_inf_nan=True`):
a plain number in place, anything else on the characters
(`strAsNumber_eq`). -/
def strAsNumber (s : String) : Except ErrorKind Number :=
  match NumScan.numScan s with
  | some p => .ok (.float (partsDecimal p))
  | none => strAsNumberChars s.toList

theorem dropWhile_none {p : Char → Bool} {l : List Char} (h : ∀ c ∈ l, p c = false) :
    l.dropWhile p = l := by
  cases l with
  | nil => rfl
  | cons c l => simp [h c (by simp)]

theorem trim_allowed {l : List Char} (h : ∀ c ∈ l, c ∈ NumScan.allowed) : trim l = l := by
  have hw : ∀ c ∈ l, isWhitespace c = false := by
    intro c hc
    have : ∀ x ∈ NumScan.allowed, isWhitespace x = false := by decide
    exact this c (h c hc)
  unfold trim
  rw [dropWhile_none hw, dropWhile_none (by simpa using hw), List.reverse_reverse]

/-- The characters after the sign that `rustFloat?` reads as `inf` or `nan`
are never a number's. -/
theorem low_ne {c : Char} {t : List Char} (hc : NumScan.isDigit c = true ∨ c = '.') (w : String)
    (hw : w.toList.head? = some 'i' ∨ w.toList.head? = some 'n') :
    String.ofList ((c :: t).map Char.toLower) ≠ w := by
  intro h
  have hm : c ∈ NumScan.allowed := by
    rcases hc with hc | hc
    · exact NumScan.isDigit_mem hc
    · subst hc; decide
  have hl : ∀ x ∈ NumScan.allowed, x.toLower ≠ 'i' ∧ x.toLower ≠ 'n' := by decide
  have := congrArg (fun s => s.toList.head?) h
  simp only [String.toList_ofList, List.map_cons, List.head?_cons] at this
  rw [← this] at hw
  rcases hw with hw | hw <;> simp at hw
  · exact (hl c hm).1 hw
  · exact (hl c hm).2 hw

/-- On a number, `rustFloat?` is `numParts`. -/
theorem rustFloat?_of_numParts {cs : List Char} {p : NumScan.Parts}
    (h : NumScan.numParts cs = some p) : rustFloat? cs = some (some (partsDecimal p)) := by
  suffices key : ∀ neg r, NumScan.afterSign neg r = some p →
      (let low := String.ofList (r.map Char.toLower)
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
          ex.map fun e => some (Decimal.normalize neg (digitsVal (ip ++ fp)) (e - fp.length)))
        = some (some (partsDecimal p)) by
    unfold NumScan.numParts at h
    unfold rustFloat?
    split
    rename_i neg r hcs
    have : NumScan.splitSign cs = (neg, r) := by
      rw [← hcs]; rfl
    rw [this] at h
    exact key _ _ h
  intro neg r h
  obtain ⟨c, t, rfl, hc⟩ := NumScan.afterSign_head h
  have h1 := low_ne (t := t) hc "inf" (by decide)
  have h2 := low_ne (t := t) hc "infinity" (by decide)
  have h3 := low_ne (t := t) hc "nan" (by decide)
  simp only [h1, h2, h3, or_self, ↓reduceIte]
  rw [← Option.map_some (f := fun p => some (partsDecimal p)), ← h]
  unfold NumScan.afterSign
  generalize List.span isDigit (c :: t) = A
  rcases A with ⟨ip, R⟩
  have hf : (match R with | '.' :: r' => List.span isDigit r' | r' => ([], r')) = NumScan.fracSplit R := rfl
  dsimp only
  rw [hf]
  generalize NumScan.fracSplit R = B
  rcases B with ⟨fp, R2⟩
  dsimp only
  by_cases hcond : ip.isEmpty = true ∧ fp.isEmpty = true
  · simp only [hcond, and_self, ↓reduceIte, Option.map_none]
  · simp only [hcond, ↓reduceIte, Option.map_map]
    rfl

theorem strAsFloat_eq (s : String) : strAsFloat s = strAsFloatChars s.toList := by
  unfold strAsFloat
  split
  · rename_i p h
    have hp : NumScan.numParts s.toList = some p := NumScan.numScan_eq s ▸ h
    have ht := trim_allowed (NumScan.numScan_allowed h)
    simp [strAsFloatChars, ht, rustFloat?_of_numParts hp]
  · rfl

theorem strAsNumber_eq (s : String) : strAsNumber s = strAsNumberChars s.toList := by
  unfold strAsNumber
  split
  · rename_i p h
    have hp : NumScan.numParts s.toList = some p := NumScan.numScan_eq s ▸ h
    have ht := trim_allowed (NumScan.numScan_allowed h)
    simp [strAsNumberChars, ht, rustFloat?_of_numParts hp]
  · rfl

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
