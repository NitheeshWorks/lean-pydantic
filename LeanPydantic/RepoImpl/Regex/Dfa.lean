import LeanPydantic.RepoImpl.Regex.Match
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
# RepoImpl: the scan as a lazily built DFA

`scan` recomputes the derivatives of its term set at every character. The
sets met are few (each is a set of partial derivatives of `r`), so
`searchDfa` numbers them as they appear and caches each transition, keyed by
the state's number, the two bits of the previous character that assertions
read (`ctx`), and the character. A cached step is one hash lookup.

Each cached transition is the scan's step: `Dfa.good` is a field, kept by
every update (`Dfa.record` needs the congruence lemmas `nullable_congr`,
`pd_congr`: the scan reads the previous character only through `ctx`). The
set-to-number index is proved right (`Dfa.indexed`). Past `maxStates` the
table starts afresh from the current state, so memory is bounded and the
worst case is the plain scan. `searchDfa_eq` proves the result is `search`'s.
-/

namespace LeanPydantic.Regex

deriving instance Hashable for Atom
deriving instance Hashable for Cls
deriving instance Hashable for Assertion
deriving instance Hashable for Regex

/-- What the scan needs of the character before a position: whether there is
none (the start), and whether it is a word character. -/
def ctx (p : Option Char) : Bool × Bool := (p.isNone, wordAt p)

theorem Assertion.holds_congr {p p' : Option Char} (h : ctx p = ctx p') (a : Assertion) (n : Option Char) :
    a.holds p n = a.holds p' n := by
  simp only [ctx, Prod.mk.injEq] at h
  cases a <;> simp [Assertion.holds, h.1, h.2]

namespace Regex

theorem nullable_congr {p p' : Option Char} (h : ctx p = ctx p') (n : Option Char) :
    ∀ r : Regex, nullable p n r = nullable p' n r
  | empty | eps | cls _ | star _ => rfl
  | assert a => Assertion.holds_congr h a n
  | alt r s | cat r s => by simp only [nullable, nullable_congr h n r, nullable_congr h n s]

theorem pd_congr {p p' : Option Char} (h : ctx p = ctx p') (c : Char) :
    ∀ r : Regex, pd p c r = pd p' c r
  | empty | eps | cls _ | assert _ => rfl
  | alt r s => by simp only [pd, pd_congr h c r, pd_congr h c s]
  | cat r s => by simp only [pd, pd_congr h c r, pd_congr h c s, nullable_congr h (some c) r]
  | star r => by simp only [pd, pd_congr h c r]

/-! A miss computes `next` with a hash set of the terms kept, not by
comparing every pair (`nextFast_eq`). -/

/-- `uniq` with a hash set of the terms kept. -/
def uniqGo (seen : Std.HashSet Regex) (acc : List Regex) : List Regex → List Regex
  | [] => acc
  | q :: l => if seen.contains q then uniqGo seen acc l else uniqGo (seen.insert q) (q :: acc) l

theorem uniqGo_eq : ∀ (l : List Regex) (seen : Std.HashSet Regex) (acc : List Regex),
    (∀ x, x ∈ seen ↔ x ∈ acc) → uniqGo seen acc l = l.foldl (fun acc q => acc.insert q) acc
  | [], _, _, _ => rfl
  | q :: l, seen, acc, h => by
    simp only [uniqGo, List.foldl_cons]
    by_cases hq : q ∈ acc
    · have : seen.contains q = true := Std.HashSet.contains_iff_mem.2 ((h q).2 hq)
      rw [List.insert_of_mem hq]; simp only [this, ite_true]
      exact uniqGo_eq l seen acc h
    · have : seen.contains q = false := by
        cases hc : seen.contains q
        · rfl
        · exact absurd ((h q).1 (Std.HashSet.contains_iff_mem.1 hc)) hq
      rw [List.insert_of_not_mem hq]; simp only [this, Bool.false_eq_true, ite_false]
      apply uniqGo_eq
      intro x
      simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons, h x]
      constructor
      · rintro (e | e)
        · exact .inl e.symm
        · exact .inr e
      · rintro (e | e)
        · exact .inl e.symm
        · exact .inr e

/-- `next`, deduplicating with a hash set. -/
def nextFast (r : Regex) (p : Option Char) (c : Char) (T : List Regex) : List Regex :=
  let l := T.flatMap (pd p c)
  (uniqGo (Std.HashSet.emptyWithCapacity l.length) [] l).insert r

theorem nextFast_eq (r : Regex) (p : Option Char) (c : Char) (T : List Regex) :
    nextFast r p c T = next r p c T := by
  simp only [nextFast, next, uniq]
  rw [uniqGo_eq]
  intro x; simp [Std.HashSet.not_mem_emptyWithCapacity]


theorem next_congr {p p' : Option Char} (h : ctx p = ctx p') (r : Regex) (c : Char) (T : List Regex) :
    next r p c T = next r p' c T := by
  have e : pd p c = pd p' c := funext (pd_congr h c)
  simp only [next, e]

end Regex

/-- The cache key: a state's number, the context bits, the character. -/
abbrev Key := Nat × Bool × Bool × Char

/-- A lazily built DFA for the scan of `r`: the state sets met so far, an
index from a set to its number, and the transitions computed so far.
`indexed` says the index is right, `good` that every cached transition is
the scan's step. -/
structure Dfa (r : Regex) where
  states : Array (List Regex)
  index : Std.HashMap (List Regex) Nat
  trans : Std.HashMap Key (Bool × Nat)
  indexed : ∀ (T : List Regex) (j : Nat), index[T]? = some j → states[j]? = some T
  good : ∀ (i : Nat) (b₁ b₂ : Bool) (c : Char) (acc : Bool) (j : Nat), trans[(i, b₁, b₂, c)]? = some (acc, j) →
    ∀ p : Option Char, ctx p = (b₁, b₂) → ∃ T, states[i]? = some T ∧ acc = T.any (Regex.nullable p (some c)) ∧
      states[j]? = some (Regex.next r p c T)

namespace Dfa

variable {r : Regex}

/-- The DFA with one state and no transitions. -/
def start (r : Regex) (T : List Regex) : Dfa r where
  states := #[T]
  index := (∅ : Std.HashMap (List Regex) Nat).insert T 0
  trans := ∅
  indexed := by
    intro T' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  good := by intro i b₁ b₂ c acc j h; simp at h

/-- `d'` has every state of `d`, at the same number. -/
def Extends (d d' : Dfa r) : Prop := ∀ (i : Nat) (T : List Regex), d.states[i]? = some T → d'.states[i]? = some T

/-- Add a state at the end. -/
def push (d : Dfa r) (T : List Regex) : Dfa r where
  states := d.states.push T
  index := d.index.insert T d.states.size
  trans := d.trans
  indexed := by
    intro T' j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk
      simp only [Option.some.injEq] at h; subst h; simp
    · have h₁ := d.indexed T' j h
      rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
  good := by
    intro i b₁ b₂ c acc j h p hp
    obtain ⟨T₀, h₁, h₂, h₃⟩ := d.good i b₁ b₂ c acc j h p hp
    refine ⟨T₀, ?_, h₂, ?_⟩
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₁
      · exact h₁
    · rw [Array.getElem?_push]; split
      · subst_vars; simp at h₃
      · exact h₃

theorem push_extends (d : Dfa r) (T : List Regex) : Extends d (d.push T) := by
  unfold Extends; intro i T₀ h
  show (d.states.push T)[i]? = some T₀
  rw [Array.getElem?_push]; split
  · subst_vars; simp at h
  · exact h

/-- The number of the state `T`, adding it if it is new. -/
def intern (d : Dfa r) (T : List Regex) : Dfa r × Nat :=
  match d.index[T]? with
  | some j => (d, j)
  | none => (d.push T, d.states.size)

theorem intern_spec (d : Dfa r) (T : List Regex) :
    Extends d (d.intern T).1 ∧ (d.intern T).1.states[(d.intern T).2]? = some T := by
  unfold intern
  split
  · rename_i j h; exact ⟨fun _ _ h => h, d.indexed T j h⟩
  · exact ⟨push_extends d T, by simp [push]⟩

/-- Record a transition that is the scan's step. -/
def record (d : Dfa r) (i : Nat) (p : Option Char) (c : Char) (j : Nat) (T : List Regex)
    (hi : d.states[i]? = some T) (hj : d.states[j]? = some (Regex.next r p c T)) : Dfa r where
  states := d.states
  index := d.index
  indexed := d.indexed
  trans := d.trans.insert (i, (ctx p).1, (ctx p).2, c) (T.any (Regex.nullable p (some c)), j)
  good := by
    intro i' b₁ b₂ c' acc j' h p' hp'
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq, Prod.mk.injEq] at hk
      obtain ⟨rfl, hb₁, hb₂, rfl⟩ := hk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc : ctx p = ctx p' := by rw [hp']; exact Prod.ext hb₁ hb₂
      refine ⟨T, hi, ?_, ?_⟩
      · rw [show Regex.nullable p (some c) = Regex.nullable p' (some c) from funext (Regex.nullable_congr hc (some c))]
      · rw [hj, Regex.next_congr hc]
    · exact d.good i' b₁ b₂ c' acc j' h p' hp'

end Dfa

/-- More states than this and the DFA starts afresh (from the current state). -/
def maxStates : Nat := 2048

/-- The transition from state `i` (the set `T`) by `c` after `p`, computed
and recorded: the new DFA and the next state's number. A full table starts
afresh, keeping only the current state. -/
def Dfa.advance {r : Regex} (d : Dfa r) (i : Nat) (p : Option Char) (c : Char) (T : List Regex)
    (hT : d.states[i]? = some T) : Dfa r × Nat :=
  if d.states.size < maxStates then go d i hT else go (Dfa.start r T) 0 rfl
where
  /-- Intern the next set and record the transition. -/
  go (d₀ : Dfa r) (i₀ : Nat) (h₀ : d₀.states[i₀]? = some T) : Dfa r × Nat :=
    let T' := Regex.nextFast r p c T
    let hs := d₀.intern_spec T'
    ((d₀.intern T').1.record i₀ p c (d₀.intern T').2 T (hs.1 _ _ h₀) (Regex.nextFast_eq r p c T ▸ hs.2),
      (d₀.intern T').2)

theorem Dfa.advance_spec {r : Regex} (d : Dfa r) (i : Nat) (p : Option Char) (c : Char) (T : List Regex)
    (hT : d.states[i]? = some T) :
    (d.advance i p c T hT).1.states[(d.advance i p c T hT).2]? = some (Regex.next r p c T) := by
  rw [← Regex.nextFast_eq]
  unfold advance; split
  all_goals exact (Dfa.intern_spec _ _).2

namespace Regex

/-- The scan, through the DFA: a cached transition is taken as it is; a new
one is the scan's step, computed once and recorded. -/
def dscan (r : Regex) (d : Dfa r) (i : Nat) (p : Option Char) : List Char → Bool
  | [] => (d.states[i]?.getD []).any (nullable p none)
  | c :: cs =>
    match d.trans[(i, (ctx p).1, (ctx p).2, c)]? with
    | some (acc, j) => if acc then true else dscan r d j (some c) cs
    | none =>
      match hT : d.states[i]? with
      | none => false
      | some T =>
        if T.any (nullable p (some c)) then true else
        let a := d.advance i p c T hT
        dscan r a.1 a.2 (some c) cs

theorem dscan_eq (r : Regex) :
    ∀ (cs : List Char) (d : Dfa r) (i : Nat) (p : Option Char) (T : List Regex),
      d.states[i]? = some T → dscan r d i p cs = scan r p cs T
  | [], d, i, p, T, h => by simp [dscan, scan, h]
  | c :: cs, d, i, p, T, h => by
    unfold dscan
    split
    · rename_i acc j hc
      obtain ⟨T₀, h₀, hacc, hj⟩ := d.good _ _ _ _ _ _ hc p rfl
      rw [h] at h₀; cases h₀
      simp only [scan, ← hacc]
      split
      · rfl
      · exact dscan_eq r cs d j (some c) _ hj
    · split
      · rename_i hT; rw [h] at hT; cases hT
      · rename_i T₁ hT
        have e : T₁ = T := by rw [h] at hT; cases hT; rfl
        subst e
        simp only [scan]
        split
        · rfl
        · exact dscan_eq r cs _ _ (some c) _ (Dfa.advance_spec d i p c T₁ hT)

/-- `search`, through a lazily built DFA. -/
def searchDfa (r : Regex) (s : String) : Bool := dscan r (Dfa.start r [r]) 0 none s.toList

theorem searchDfa_eq (r : Regex) (s : String) : searchDfa r s = search r s :=
  dscan_eq r s.toList _ 0 none [r] rfl

end Regex
end LeanPydantic.Regex
