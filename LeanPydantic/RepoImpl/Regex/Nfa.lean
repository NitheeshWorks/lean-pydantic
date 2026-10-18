import LeanPydantic.RepoImpl.Regex.Match
import Std.Data.HashMap.Lemmas

/-!
# RepoImpl: the scan, compiled

`scan` rebuilds derivative terms at every character. `Nfa.build` does that
work once per pattern: it numbers every derivative term (Antimirov's partial
derivatives, at most one per character class, plus the pattern), and for
each term and context slot stores its linear form (`lin`: each derivative
with the class that guards it) with the derivatives as numbers, and its
nullability. Matching (`Nfa.run`) then keeps a set of term numbers: per
character, one class test per live edge and an array of seen flags, no
term is built, hashed or compared.

The tables carry their correctness as fields (`Nfa.hTrans`, `hNul`, `hFin`):
the numbering is checked when the pattern is compiled, and `build` gives
`none` (and the plain scan is used) if it is incomplete. `pd_eq_lin` shows
the linear form is `pd`; `Proofs/Regex.lean` proves `Nfa.search_eq`: the
compiled matcher is `search`.
-/

namespace LeanPydantic.Regex

deriving instance Hashable for Atom
deriving instance Hashable for Cls
deriving instance Hashable for Assertion
deriving instance Hashable for Regex

/-- What an assertion reads of the character on one side of a position:
whether there is none (an end), and whether it is a word character. -/
def ctx (p : Option Char) : Bool × Bool := (p.isNone, wordAt p)

/-- `Assertion.holds`, on the two sides' bits. -/
def Assertion.holdsB : Assertion → Bool × Bool → Bool × Bool → Bool
  | .start, p, _ => p.1
  | .finish, _, n => n.1
  | .wordBoundary, p, n => p.2 != n.2
  | .notWordBoundary, p, n => p.2 == n.2
  | .wordStart, p, n => !p.2 && n.2
  | .wordEnd, p, n => p.2 && !n.2

theorem Assertion.holds_eq (a : Assertion) (p n : Option Char) : a.holds p n = a.holdsB (ctx p) (ctx n) := by
  cases a <;> rfl

namespace Regex

/-- `nullable`, on the two sides' bits. -/
def nullB (pc nc : Bool × Bool) : Regex → Bool
  | empty => false
  | eps => true
  | cls _ => false
  | assert a => a.holdsB pc nc
  | alt r s => nullB pc nc r || nullB pc nc s
  | cat r s => nullB pc nc r && nullB pc nc s
  | star _ => true

theorem nullable_eq (p n : Option Char) : ∀ r : Regex, nullable p n r = nullB (ctx p) (ctx n) r
  | empty | eps | cls _ | star _ => rfl
  | assert a => Assertion.holds_eq a p n
  | alt r s | cat r s => by simp only [nullable, nullB, nullable_eq p n r, nullable_eq p n s]

/-- Antimirov's linear form, in context: the derivatives of `r` by a
character with their guarding class, when the character before has bits
`pc` and the character read is a word character exactly when `nw`. -/
def lin (pc : Bool × Bool) (nw : Bool) : Regex → List (Cls × Regex)
  | empty => []
  | eps => []
  | cls k => [(k, eps)]
  | assert _ => []
  | alt r s => lin pc nw r ++ lin pc nw s
  | cat r s =>
    (lin pc nw r).map (fun kq => (kq.1, seq kq.2 s)) ++ (if nullB pc (false, nw) r then lin pc nw s else [])
  | star r => (lin pc nw r).map (fun kq => (kq.1, seq kq.2 (star r)))

/-- The derivatives by `c` that the linear form's classes let through. -/
def pick (c : Char) (l : List (Cls × Regex)) : List Regex :=
  l.filterMap fun kq => if kq.1.test c then some kq.2 else none

/-- **The partial derivatives are the linear form, filtered by `c`.** -/
theorem pd_eq_lin (p : Option Char) (c : Char) : ∀ r : Regex, pd p c r = pick c (lin (ctx p) (isWord c) r)
  | empty | eps | assert _ => rfl
  | cls k => by simp only [pd, lin, pick, List.filterMap_cons, List.filterMap_nil]; split <;> rfl
  | alt r s => by simp only [pd, lin, pick, List.filterMap_append, pd_eq_lin p c r, pd_eq_lin p c s]
  | cat r s => by
    have hn : nullable p (some c) r = nullB (ctx p) (false, isWord c) r := nullable_eq p (some c) r
    simp only [pd, lin, pick, List.filterMap_append, pd_eq_lin p c r, pd_eq_lin p c s, hn]
    congr 1
    · simp only [List.filterMap_map, List.map_filterMap]
      congr 1; funext kq; simp only [Function.comp]; split <;> simp_all
    · split <;> rfl
  | star r => by
    simp only [pd, lin, pick, pd_eq_lin p c r, List.filterMap_map, List.map_filterMap]
    congr 1; funext kq; simp only [Function.comp]; split <;> simp_all


/-! ## Sets of term numbers -/

/-- `l` without repeats (numbers below `n`; any others are kept as they are). -/
def dedupIds (n : Nat) (l : List Nat) : List Nat := go (Array.replicate n false) [] l
where
  go (seen : Array Bool) (acc : List Nat) : List Nat → List Nat
    | [] => acc
    | j :: l => if seen[j]?.getD false then go seen acc l else go (seen.set! j true) (j :: acc) l

theorem dedupIds_go_mem : ∀ (l : List Nat) (seen : Array Bool) (acc : List Nat),
    (∀ x, seen[x]?.getD false = true → x ∈ acc) → ∀ x, x ∈ dedupIds.go seen acc l ↔ x ∈ acc ∨ x ∈ l
  | [], _, _, _, x => by simp [dedupIds.go]
  | j :: l, seen, acc, h, x => by
    simp only [dedupIds.go]
    split
    · rename_i hj
      rw [dedupIds_go_mem l seen acc h x]
      have := h j hj
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl this
        · exact .inr h
    · rw [dedupIds_go_mem l _ (j :: acc) ?_ x]
      · simp only [List.mem_cons]
        constructor
        · rintro ((rfl | h) | h)
          · exact .inr (.inl rfl)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | rfl | h)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr h
      · intro y hy
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
        split at hy
        · subst_vars; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h y hy)

theorem mem_dedupIds (n : Nat) (l : List Nat) (x : Nat) : x ∈ dedupIds n l ↔ x ∈ l := by
  unfold dedupIds
  rw [dedupIds_go_mem l _ [] (fun y hy => by simp [Array.getElem?_replicate] at hy; split at hy <;> simp at hy) x]
  simp


/-! ## The compiled matcher -/

/-- A context's table slot: the character before (`pc`) and whether the one
read is a word character (`nw`). -/
def code (pc : Bool × Bool) (nw : Bool) : Nat :=
  (if pc.1 then 4 else 0) + (if pc.2 then 2 else 0) + (if nw then 1 else 0)

/-- The slot's context. -/
def decode (k : Nat) : (Bool × Bool) × Bool := ((k / 4 % 2 == 1, k / 2 % 2 == 1), k % 2 == 1)

theorem decode_code (pc : Bool × Bool) (nw : Bool) : decode (code pc nw) = (pc, nw) := by
  obtain ⟨a, b⟩ := pc; cases a <;> cases b <;> cases nw <;> rfl

theorem code_lt (pc : Bool × Bool) (nw : Bool) : code pc nw < 8 := by
  obtain ⟨a, b⟩ := pc; cases a <;> cases b <;> cases nw <;> decide

/-- The pattern compiled once: its derivative terms numbered (`terms[0]` is
the pattern), and for each term and context slot, its linear form with the
derivatives as numbers, and whether it is nullable before a character and
at the end. The fields after the tables say they are right. -/
structure Nfa (r : Regex) where
  terms : Array Regex
  trans : Array (Array (Array (Cls × Nat)))
  nul : Array (Array Bool)
  fin : Array (Array Bool)
  start : terms[0]? = some r
  hTrans : ∀ (j : Nat) (t : Regex), terms[j]? = some t → ∀ (pc : Bool × Bool) (nw : Bool),
    ((trans[j]?.bind (·[code pc nw]?)).getD #[]).toList.map (fun e => (e.1, terms[e.2]?)) =
      (lin pc nw t).map (fun kq => (kq.1, some kq.2))
  hNul : ∀ (j : Nat) (t : Regex), terms[j]? = some t → ∀ (pc : Bool × Bool) (nw : Bool),
    (nul[j]?.bind (·[code pc nw]?)).getD false = nullB pc (false, nw) t
  hFin : ∀ (j : Nat) (t : Regex), terms[j]? = some t → ∀ (pc : Bool × Bool),
    (fin[j]?.bind (·[code pc false]?)).getD false = nullB pc (true, false) t

namespace Nfa

variable {r : Regex} (N : Nfa r)

/-- The numbered derivatives of term `j`, with their classes. -/
@[inline] def edges (j : Nat) (pc : Bool × Bool) (nw : Bool) : Array (Cls × Nat) :=
  (N.trans.getD j #[]).getD (code pc nw) #[]

/-- Whether term `j` is nullable before a character. -/
@[inline] def nulAt (j : Nat) (pc : Bool × Bool) (nw : Bool) : Bool :=
  if j < N.terms.size then (N.nul.getD j #[]).getD (code pc nw) false else false

/-- Whether term `j` is nullable at the end. -/
@[inline] def finAt (j : Nat) (pc : Bool × Bool) : Bool :=
  if j < N.terms.size then (N.fin.getD j #[]).getD (code pc false) false else false

theorem getD2 {β : Type} (a : Array (Array β)) (j k : Nat) (d : β) :
    (a.getD j #[]).getD k d = (a[j]?.bind (·[k]?)).getD d := by
  simp only [Array.getD_eq_getD_getElem?]
  cases a[j]? <;> simp

theorem edges_eq (j : Nat) (pc : Bool × Bool) (nw : Bool) :
    N.edges j pc nw = (N.trans[j]?.bind (·[code pc nw]?)).getD #[] := getD2 _ _ _ _

/-- The derivatives of the set by `c`, as numbers, and the pattern again. -/
def next (pc : Bool × Bool) (c : Char) (S : List Nat) : List Nat :=
  let nw := isWord c
  dedupIds N.terms.size (0 :: S.flatMap fun j =>
    if j < N.terms.size then
      (N.edges j pc nw).toList.filterMap fun e => if e.1.test c then some e.2 else none
    else [])

/-- Add an edge's target if its class takes `c` and it is not in yet. -/
@[inline] def addEdge (c : Char) (sa : Array Bool × List Nat) (e : Cls × Nat) : Array Bool × List Nat :=
  if e.1.test c then
    if sa.1[e.2]?.getD false then sa else (sa.1.set! e.2 true, e.2 :: sa.2)
  else sa

/-- `addEdge` over the edges from `i` on, with the flags and the set as
separate arguments so the flag array is updated in place. -/
def edgeLoop (es : Array (Cls × Nat)) (c : Char) (i : Nat) (seen : Array Bool) (acc : List Nat) :
    Array Bool × List Nat :=
  if h : i < es.size then
    let e := es[i]
    if e.1.test c then
      if seen[e.2]?.getD false then edgeLoop es c (i + 1) seen acc
      else edgeLoop es c (i + 1) (seen.set! e.2 true) (e.2 :: acc)
    else edgeLoop es c (i + 1) seen acc
  else (seen, acc)
termination_by es.size - i

theorem edgeLoop_eq (es : Array (Cls × Nat)) (c : Char) (i : Nat) (seen : Array Bool) (acc : List Nat) :
    edgeLoop es c i seen acc = (es.toList.drop i).foldl (addEdge c) (seen, acc) := by
  unfold edgeLoop
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp only [List.foldl_cons, addEdge, Array.getElem_toList]
    split
    · split
      · exact edgeLoop_eq es c (i + 1) seen acc
      · exact edgeLoop_eq es c (i + 1) _ _
    · exact edgeLoop_eq es c (i + 1) seen acc
  · rename_i h
    rw [List.drop_of_length_le (by simp; omega)]
    rfl
termination_by es.size - i

/-- `next`'s work in one pass: every live term's edges, into a seen-flag
array and the new set. -/
def stepGo (pc : Bool × Bool) (nw : Bool) (c : Char) : List Nat → Array Bool × List Nat → Array Bool × List Nat
  | [], sa => sa
  | j :: S, (seen, acc) =>
    stepGo pc nw c S (if j < N.terms.size then edgeLoop (N.edges j pc nw) c 0 seen acc else (seen, acc))

/-- `next`, with no intermediate lists (`nextFast_mem`). -/
def nextFast (pc : Bool × Bool) (c : Char) (S : List Nat) : List Nat :=
  (N.stepGo pc (isWord c) c S ((Array.replicate N.terms.size false).set! 0 true, [0])).2

/-- What the seen flags promise: a flagged number is in the set. -/
def SeenOk (sa : Array Bool × List Nat) : Prop := ∀ x, sa.1[x]?.getD false = true → x ∈ sa.2

theorem addEdge_spec (c : Char) (sa : Array Bool × List Nat) (e : Cls × Nat) (h : SeenOk sa) :
    SeenOk (addEdge c sa e) ∧ ∀ x, x ∈ (addEdge c sa e).2 ↔ x ∈ sa.2 ∨ (e.1.test c = true ∧ e.2 = x) := by
  unfold addEdge
  split
  · rename_i ht
    split
    · rename_i hs
      refine ⟨h, fun x => ⟨.inl, ?_⟩⟩
      rintro (hx | ⟨-, rfl⟩)
      · exact hx
      · exact h _ hs
    · refine ⟨?_, fun x => ?_⟩
      · intro y hy
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
        split at hy
        · subst_vars; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h y hy)
      · simp only [List.mem_cons, ht, true_and]
        constructor
        · rintro (rfl | hx)
          · exact .inr rfl
          · exact .inl hx
        · rintro (hx | rfl)
          · exact .inr hx
          · exact .inl rfl
  · rename_i ht
    refine ⟨h, fun x => ⟨.inl, ?_⟩⟩
    rintro (hx | ⟨hc, -⟩)
    · exact hx
    · exact absurd hc ht

theorem foldl_addEdge (c : Char) : ∀ (es : List (Cls × Nat)) (sa : Array Bool × List Nat), SeenOk sa →
    SeenOk (es.foldl (addEdge c) sa) ∧
      ∀ x, x ∈ (es.foldl (addEdge c) sa).2 ↔ x ∈ sa.2 ∨ ∃ e ∈ es, e.1.test c = true ∧ e.2 = x
  | [], sa, h => ⟨h, fun x => by simp⟩
  | e :: es, sa, h => by
    obtain ⟨h1, h2⟩ := addEdge_spec c sa e h
    obtain ⟨h3, h4⟩ := foldl_addEdge c es _ h1
    refine ⟨h3, fun x => ?_⟩
    simp only [List.foldl_cons, h4, h2, List.mem_cons]
    constructor
    · rintro ((hx | hx) | ⟨e', he', hx⟩)
      · exact .inl hx
      · exact .inr ⟨e, .inl rfl, hx⟩
      · exact .inr ⟨e', .inr he', hx⟩
    · rintro (hx | ⟨e', (rfl | he'), hx⟩)
      · exact .inl (.inl hx)
      · exact .inl (.inr hx)
      · exact .inr ⟨e', he', hx⟩

theorem stepGo_spec (pc : Bool × Bool) (nw : Bool) (c : Char) : ∀ (S : List Nat) (sa : Array Bool × List Nat),
    SeenOk sa → ∀ x, x ∈ (N.stepGo pc nw c S sa).2 ↔
      x ∈ sa.2 ∨ ∃ j ∈ S, j < N.terms.size ∧ ∃ e ∈ (N.edges j pc nw).toList, e.1.test c = true ∧ e.2 = x
  | [], sa, _, x => by simp [stepGo]
  | j :: S, sa, h, x => by
    simp only [stepGo]
    split
    · rename_i hj
      rw [edgeLoop_eq, List.drop_zero]
      obtain ⟨h1, h2⟩ := foldl_addEdge c (N.edges j pc nw).toList sa h
      rw [stepGo_spec pc nw c S _ h1 x, h2]
      simp only [List.mem_cons]
      constructor
      · rintro ((hx | hx) | ⟨j', hj', hx⟩)
        · exact .inl hx
        · exact .inr ⟨j, .inl rfl, hj, hx⟩
        · exact .inr ⟨j', .inr hj', hx⟩
      · rintro (hx | ⟨j', (rfl | hj'), hl, hx⟩)
        · exact .inl (.inl hx)
        · exact .inl (.inr hx)
        · exact .inr ⟨j', hj', hl, hx⟩
    · rename_i hj
      rw [stepGo_spec pc nw c S _ h x]
      simp only [List.mem_cons]
      constructor
      · rintro (hx | ⟨j', hj', hx⟩)
        · exact .inl hx
        · exact .inr ⟨j', .inr hj', hx⟩
      · rintro (hx | ⟨j', (rfl | hj'), hl, hx⟩)
        · exact .inl hx
        · exact absurd hl hj
        · exact .inr ⟨j', hj', hl, hx⟩

theorem nextFast_mem (pc : Bool × Bool) (c : Char) (S : List Nat) (x : Nat) :
    x ∈ N.nextFast pc c S ↔ x ∈ N.next pc c S := by
  unfold nextFast next
  rw [N.stepGo_spec pc (isWord c) c S _ ?_ x, mem_dedupIds]
  · simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
    constructor
    · rintro (hx | ⟨j, hj, hl, e, he, hc, rfl⟩)
      · exact .inl hx
      · refine .inr ⟨j, hj, ?_⟩
        simp only [hl, ↓reduceIte]; rw [List.mem_filterMap]
        exact ⟨e, he, by simp [hc]⟩
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact .inl hx
      · split at hx
        · rename_i hl
          rw [List.mem_filterMap] at hx
          obtain ⟨e, he, hex⟩ := hx
          split at hex
          · rename_i hc; simp only [Option.some.injEq] at hex
            exact .inr ⟨j, hj, hl, e, he, hc, hex⟩
          · cases hex
        · cases hx
  · intro y hy
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_replicate] at hy
    split at hy
    · subst_vars; exact List.mem_singleton_self _
    · split at hy <;> simp at hy

/-- The scan over term numbers. -/
def run : Option Char → List Char → List Nat → Bool
  | p, [], S => S.any (N.finAt · (ctx p))
  | p, c :: cs, S => if S.any (N.nulAt · (ctx p) (isWord c)) then true else run (some c) cs (N.nextFast (ctx p) c S)

/-! ### Caching the steps of one call

Within a call the term sets met repeat (for `^(a{1,50})+$` on a run of
`a`, after the first fifty characters every set has been seen), so the
sets are numbered as they appear and each step is cached by (set number,
the bits of the character before, the character). A cached step is one
hash lookup. Past `maxStates` sets nothing more is cached and the rest of
the text runs `run` directly, so a pattern whose sets never repeat costs one
plain step per character. `Cache.good` says every cached step is `run`'s. -/

/-- The cache key: a set's number, the bits of the character before, the
character. -/
abbrev Key := Nat × Bool × Bool × Char

/-- The sets met so far, an index from a set to its number, and the cached
steps. -/
structure Cache where
  states : Array (List Nat)
  index : Std.HashMap (List Nat) Nat
  trans : Std.HashMap Key (Bool × Nat)
  indexed : ∀ (S : List Nat) (j : Nat), index[S]? = some j → states[j]? = some S
  good : ∀ (i : Nat) (b₁ b₂ : Bool) (c : Char) (acc : Bool) (j : Nat), trans[(i, b₁, b₂, c)]? = some (acc, j) →
    ∃ S, states[i]? = some S ∧ acc = S.any (N.nulAt · (b₁, b₂) (isWord c)) ∧
      states[j]? = some (N.nextFast (b₁, b₂) c S)

/-- More sets than this in one call and nothing more is cached. -/
def maxStates : Nat := 1024

namespace Cache

variable {N}

/-- One set and no steps. -/
def start (S : List Nat) : Cache N where
  states := #[S]
  index := (∅ : Std.HashMap (List Nat) Nat).insert S 0
  trans := ∅
  indexed := by
    intro S' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  good := by intro i b₁ b₂ c acc j h; simp at h

/-- Add a set at the end. -/
def push (d : Cache N) (S : List Nat) : Cache N where
  states := d.states.push S
  index := d.index.insert S d.states.size
  trans := d.trans
  indexed := by
    intro S' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; simp
    · have h₁ := d.indexed S' j h
      rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
  good := by
    intro i b₁ b₂ c acc j h
    obtain ⟨S₀, h₁, h₂, h₃⟩ := d.good i b₁ b₂ c acc j h
    refine ⟨S₀, ?_, h₂, ?_⟩
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₃
      · exact h₃

/-- `d'` has every set of `d`, at the same number. -/
def Extends (d d' : Cache N) : Prop := ∀ (i : Nat) (S : List Nat), d.states[i]? = some S → d'.states[i]? = some S

theorem push_extends (d : Cache N) (S : List Nat) : Extends d (d.push S) := by
  unfold Extends; intro i S₀ h
  show (d.states.push S)[i]? = some S₀
  rw [Array.getElem?_push]; split
  · subst_vars; simp at h
  · exact h

/-- The number of the set `S`, adding it if it is new. -/
def intern (d : Cache N) (S : List Nat) : Cache N × Nat :=
  match d.index[S]? with
  | some j => (d, j)
  | none => (d.push S, d.states.size)

theorem intern_spec (d : Cache N) (S : List Nat) :
    Extends d (d.intern S).1 ∧ (d.intern S).1.states[(d.intern S).2]? = some S := by
  unfold intern
  split
  · rename_i j h; exact ⟨fun _ _ h => h, d.indexed S j h⟩
  · exact ⟨push_extends d S, by simp [push]⟩

/-- Record a step that is `run`'s. -/
def record (d : Cache N) (i : Nat) (pc : Bool × Bool) (c : Char) (j : Nat) (S : List Nat)
    (hi : d.states[i]? = some S) (hj : d.states[j]? = some (N.nextFast pc c S)) : Cache N where
  states := d.states
  index := d.index
  indexed := d.indexed
  trans := d.trans.insert (i, pc.1, pc.2, c) (S.any (N.nulAt · pc (isWord c)), j)
  good := by
    intro i' b₁ b₂ c' acc j' h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨S, hi, rfl, hj⟩
    · exact d.good i' b₁ b₂ c' acc j' h

/-- The step from set `i` (`S`) by `c`, computed and recorded. -/
def advance (d : Cache N) (i : Nat) (pc : Bool × Bool) (c : Char) (S : List Nat) (hS : d.states[i]? = some S) :
    Cache N × Nat :=
  let S' := N.nextFast pc c S
  let hs := d.intern_spec S'
  ((d.intern S').1.record i pc c (d.intern S').2 S (hs.1 _ _ hS) hs.2, (d.intern S').2)

theorem advance_spec (d : Cache N) (i : Nat) (pc : Bool × Bool) (c : Char) (S : List Nat)
    (hS : d.states[i]? = some S) :
    (d.advance i pc c S hS).1.states[(d.advance i pc c S hS).2]? = some (N.nextFast pc c S) :=
  (d.intern_spec _).2

end Cache

/-- `run`, through the cache. -/
def crun (d : Cache N) (i : Nat) (p : Option Char) : List Char → Bool
  | [] => (d.states[i]?.getD []).any (N.finAt · (ctx p))
  | c :: cs =>
    let pc := ctx p
    match d.trans[(i, pc.1, pc.2, c)]? with
    | some (acc, j) => if acc then true else crun d j (some c) cs
    | none =>
      match hS : d.states[i]? with
      | none => false
      | some S =>
        if S.any (N.nulAt · pc (isWord c)) then true
        else if d.states.size < maxStates then
          let a := d.advance i pc c S hS
          crun a.1 a.2 (some c) cs
        else N.run (some c) cs (N.nextFast pc c S)

theorem crun_eq : ∀ (cs : List Char) (d : Cache N) (i : Nat) (p : Option Char) (S : List Nat),
    d.states[i]? = some S → N.crun d i p cs = N.run p cs S
  | [], d, i, p, S, h => by simp [crun, run, h]
  | c :: cs, d, i, p, S, h => by
    unfold crun
    simp only
    split
    · rename_i acc j hc
      obtain ⟨S₀, h₀, hacc, hj⟩ := d.good _ _ _ _ _ _ hc
      rw [h] at h₀; cases h₀
      simp only [run, ← hacc]
      split
      · rfl
      · exact crun_eq cs d j (some c) _ hj
    · split
      · rename_i hS; rw [h] at hS; cases hS
      · rename_i S₁ hS
        have e : S₁ = S := by rw [h] at hS; cases hS; rfl
        subst e
        simp only [run]
        split
        · rfl
        · split
          · exact crun_eq cs _ _ (some c) _ (Cache.advance_spec d i (ctx p) c S₁ hS)
          · rfl

/-- Below this length a text runs `run` directly: too short for the
cache's bookkeeping to pay. -/
def cacheFrom : Nat := 256

/-- Whether the pattern matches somewhere in `s`. -/
def search (s : String) : Bool :=
  let cs := s.toList
  if cs.length ≤ cacheFrom then N.run none cs [0] else N.crun (Cache.start [0]) 0 none cs

theorem search_run (s : String) : N.search s = N.run none s.toList [0] := by
  unfold search; simp only
  split
  · rfl
  · exact N.crun_eq s.toList _ 0 none [0] rfl

end Nfa

/-! ## Compiling a pattern -/

/-- Every context slot. -/
def combos : List ((Bool × Bool) × Bool) := (List.range 8).map decode

theorem mem_combos (pc : Bool × Bool) (nw : Bool) : (pc, nw) ∈ combos := by
  rw [← decode_code pc nw]; exact List.mem_map.2 ⟨_, List.mem_range.2 (code_lt pc nw), rfl⟩

/-- Number `q`, adding it if it is new. -/
def intern (st : Array Regex × Std.HashMap Regex Nat) (q : Regex) : Array Regex × Std.HashMap Regex Nat :=
  if st.2.contains q then st else (st.1.push q, st.2.insert q st.1.size)

/-- No assertion but `$` inside: then the context never matters. -/
def ctxFree : Regex → Bool
  | assert .finish => true
  | assert _ => false
  | alt r s => ctxFree r && ctxFree s
  | cat r s => ctxFree r && ctxFree s
  | star r => ctxFree r
  | _ => true

theorem nullB_ctxFree (pc nc pc' nc' : Bool × Bool) (hn : nc.1 = nc'.1) :
    ∀ r : Regex, ctxFree r = true → nullB pc nc r = nullB pc' nc' r
  | empty, _ | eps, _ | cls _, _ | star _, _ => rfl
  | assert a, h => by cases a <;> simp_all [ctxFree, nullB, Assertion.holdsB]
  | alt r s, h | cat r s, h => by
    simp only [ctxFree, Bool.and_eq_true] at h
    simp only [nullB, nullB_ctxFree pc nc pc' nc' hn r h.1, nullB_ctxFree pc nc pc' nc' hn s h.2]

theorem lin_ctxFree (pc : Bool × Bool) (nw : Bool) :
    ∀ r : Regex, ctxFree r = true → lin pc nw r = lin (false, false) false r
  | empty, _ | eps, _ | cls _, _ | assert _, _ => rfl
  | alt r s, h => by
    simp only [ctxFree, Bool.and_eq_true] at h
    simp only [lin, lin_ctxFree pc nw r h.1, lin_ctxFree pc nw s h.2]
  | cat r s, h => by
    simp only [ctxFree, Bool.and_eq_true] at h
    simp only [lin, lin_ctxFree pc nw r h.1, lin_ctxFree pc nw s h.2,
      nullB_ctxFree pc (false, nw) (false, false) (false, false) rfl r h.1]
  | star r, h => by
    simp only [ctxFree] at h
    simp only [lin, lin_ctxFree pc nw r h]

/-- The slots whose linear forms differ: one when the context never matters. -/
def slots (t : Regex) : List ((Bool × Bool) × Bool) := if ctxFree t then [((false, false), false)] else combos

/-- Number every derivative term reachable from the terms from `i` on, in
every context (at most `fuel` terms). -/
def close : Nat → Nat → Array Regex × Std.HashMap Regex Nat → Array Regex × Std.HashMap Regex Nat
  | 0, _, st => st
  | f + 1, i, st =>
    match st.1[i]? with
    | none => st
    | some t =>
      close f (i + 1) ((slots t).foldl (fun st pn => (lin pn.1 pn.2 t).foldl (fun st kq => intern st kq.2) st) st)

/-- A linear form with the derivatives as numbers. -/
def numbered (idx : Std.HashMap Regex Nat) (l : List (Cls × Regex)) : Array (Cls × Nat) :=
  (l.map fun kq => (kq.1, idx.getD kq.2 0)).toArray

/-- A term's table row: its linear form in each slot, with the derivatives
as numbers (computed once when the context never matters). -/
def transRow (idx : Std.HashMap Regex Nat) (t : Regex) : Array (Array (Cls × Nat)) :=
  if ctxFree t then
    let e := numbered idx (lin (false, false) false t)
    (Array.range 8).map fun _ => e
  else (Array.range 8).map fun k => numbered idx (lin (decode k).1 (decode k).2 t)

theorem transRow_get (idx : Std.HashMap Regex Nat) (t : Regex) (pc : Bool × Bool) (nw : Bool) :
    (transRow idx t)[code pc nw]? = some (numbered idx (lin pc nw t)) := by
  have hk := code_lt pc nw
  unfold transRow
  split
  · rename_i hf; simp [hk, lin_ctxFree pc nw t hf]
  · simp [hk, decode_code]

/-- A term's nullability before a character, in each slot. -/
def nulRow (t : Regex) : Array Bool :=
  if ctxFree t then
    let b := nullB (false, false) (false, false) t
    (Array.range 8).map fun _ => b
  else (Array.range 8).map fun k => nullB (decode k).1 (false, (decode k).2) t

theorem nulRow_get (t : Regex) (pc : Bool × Bool) (nw : Bool) :
    (nulRow t)[code pc nw]? = some (nullB pc (false, nw) t) := by
  have hk := code_lt pc nw
  unfold nulRow
  split
  · rename_i hf; simp [hk, nullB_ctxFree pc (false, nw) (false, false) (false, false) rfl t hf]
  · simp [hk, decode_code]

/-- A term's nullability at the end, in each slot. -/
def finRow (t : Regex) : Array Bool :=
  if ctxFree t then
    let b := nullB (false, false) (true, false) t
    (Array.range 8).map fun _ => b
  else (Array.range 8).map fun k => nullB (decode k).1 (true, false) t

theorem finRow_get (t : Regex) (pc : Bool × Bool) :
    (finRow t)[code pc false]? = some (nullB pc (true, false) t) := by
  have hk := code_lt pc false
  unfold finRow
  split
  · rename_i hf; simp [hk, nullB_ctxFree pc (true, false) (false, false) (true, false) rfl t hf]
  · simp [hk, decode_code]

/-- Every derivative of `t` was numbered, and its number stands for it. -/
def checkTerm (terms : Array Regex) (idx : Std.HashMap Regex Nat) (t : Regex) : Bool :=
  (slots t).all fun pn => (lin pn.1 pn.2 t).all fun kq => decide (terms[idx.getD kq.2 0]? = some kq.2)

theorem checkTerm_spec {terms : Array Regex} {idx : Std.HashMap Regex Nat} {t : Regex}
    (h : checkTerm terms idx t = true) (pc : Bool × Bool) (nw : Bool) :
    ∀ kq ∈ lin pc nw t, terms[idx.getD kq.2 0]? = some kq.2 := by
  intro kq hkq
  unfold checkTerm slots at h
  split at h
  · rename_i hf
    rw [lin_ctxFree pc nw t hf] at hkq
    have h1 := List.all_eq_true.1 h ((false, false), false) (by simp)
    have h2 := List.all_eq_true.1 h1 kq hkq
    simpa using h2
  · have h1 := List.all_eq_true.1 h (pc, nw) (mem_combos pc nw)
    have h2 := List.all_eq_true.1 h1 kq hkq
    simpa using h2

theorem range8_get {k : Nat} (h : k < 8) : (Array.range 8)[k]? = some k := by
  simp [h]

/-- The more terms a pattern may have than this, the more `close` may stop
short; the check then fails and the plain scan is used. -/
def maxTerms : Nat := 20016

/-- Compile `r`: number its derivative terms and fill the tables, checking
the numbering (`none`, and the plain scan, if it is incomplete). -/
def Nfa.build (r : Regex) : Option (Nfa r) :=
  let st := close maxTerms 0 (#[r], (∅ : Std.HashMap Regex Nat).insert r 0)
  let terms := st.1
  let idx := st.2
  if h0 : terms[0]? = some r then
    if hc : terms.all (checkTerm terms idx) = true then
      some {
        terms, trans := terms.map (transRow idx), nul := terms.map nulRow, fin := terms.map finRow
        start := h0
        hTrans := by
          intro j t ht pc nw
          have hj : j < terms.size := by
            rcases Nat.lt_or_ge j terms.size with h | h
            · exact h
            · simp [Array.getElem?_eq_none h] at ht
          have htj : terms[j] = t := by simpa [hj] using ht
          have hchk := (Array.all_eq_true.1 hc) j hj
          rw [htj] at hchk
          simp only [Array.getElem?_map, ht, Option.map_some, Option.bind_some, transRow_get,
            Option.getD_some, numbered, List.toList_toArray, List.map_map]
          apply List.map_congr_left
          intro kq hkq
          simp only [Function.comp]
          rw [checkTerm_spec hchk pc nw kq hkq]
        hNul := by
          intro j t ht pc nw
          simp [Array.getElem?_map, ht, nulRow_get]
        hFin := by
          intro j t ht pc
          simp [Array.getElem?_map, ht, finRow_get] }
    else none
  else none

end Regex
end LeanPydantic.Regex
