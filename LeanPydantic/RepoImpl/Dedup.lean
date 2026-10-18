import LeanPydantic.RepoImpl.Schema
import Std.Data.HashMap.Lemmas

/-!
# RepoImpl: `dedup` in linear time

`dedup` (what a Python `dict` keeps of repeated keys: one entry per key, at
its first position, with its last value) inserts each member by scanning the
entries so far, which is quadratic. `dedupIdx` keeps a hash index from each
key to its slot in the output, sized up front, and `dedupIdx_eq` proves it
is `dedup`.
-/

namespace LeanPydantic

/-- `dedup` in one pass: `idx` maps each key seen to its slot in `out`. -/
def dedupGo {β : Type} (idx : Std.HashMap String Nat) (out : Array (String × β)) :
    List (String × β) → Array (String × β)
  | [] => out
  | (k, v) :: r =>
    match idx[k]? with
    | some i => dedupGo idx (out.set! i (k, v)) r
    | none => dedupGo (idx.insert k out.size) (out.push (k, v)) r

/-- `idx` indexes the keys of `out`. -/
def IdxInv {β : Type} (idx : Std.HashMap String Nat) (out : Array (String × β)) : Prop :=
  ∀ k i, idx[k]? = some i ↔ ∃ h : i < out.size, out[i].1 = k

theorem dictInsert_not_mem {β : Type} (k : String) (v : β) :
    ∀ l : List (String × β), (∀ kv ∈ l, kv.1 ≠ k) → dictInsert k v l = l ++ [(k, v)]
  | [] , _ => rfl
  | (k', v') :: l, h => by
    have h1 : k' ≠ k := h (k', v') (by simp)
    simp only [dictInsert, h1, ite_false, List.cons_append]
    rw [dictInsert_not_mem k v l (fun kv hm => h kv (by simp [hm]))]

theorem dictInsert_at {β : Type} (k : String) (v : β) :
    ∀ (l : List (String × β)) (i : Nat) (hi : i < l.length), l[i].1 = k →
      (∀ j (hj : j < l.length), l[j].1 = k → j = i) → dictInsert k v l = l.set i (k, v)
  | [], i, hi, _, _ => by simp at hi
  | (k', v') :: l, 0, _, he, _ => by simp_all [dictInsert]
  | (k', v') :: l, i + 1, hi, he, hu => by
    have h1 : k' ≠ k := by
      intro h; have := hu 0 (by simp) (by simpa using h); omega
    simp only [dictInsert, h1, ite_false, List.set_cons_succ]
    rw [dictInsert_at k v l i (by simpa using hi) (by simpa using he)
      (fun j hj hk => by have := hu (j + 1) (by simpa using hj) (by simpa using hk); omega)]

theorem dedupGo_eq {β : Type} :
    ∀ (kvs : List (String × β)) (idx : Std.HashMap String Nat) (out : Array (String × β)),
      IdxInv idx out → (dedupGo idx out kvs).toList = kvs.foldl (fun acc kv => dictInsert kv.1 kv.2 acc) out.toList
  | [], _, _, _ => rfl
  | (k, v) :: r, idx, out, hinv => by
    simp only [dedupGo, List.foldl_cons]
    split
    · rename_i i hk
      obtain ⟨hi, hik⟩ := (hinv k i).1 hk
      have hset : dictInsert k v out.toList = (out.set! i (k, v)).toList := by
        rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
        exact dictInsert_at k v out.toList i (by simpa using hi) (by simpa using hik)
          (fun j hj hjk => by
            have h2 := (hinv k j).2 ⟨by simpa using hj, by simpa using hjk⟩
            rw [hk] at h2; exact (Option.some.inj h2).symm)
      rw [hset]
      apply dedupGo_eq
      intro k' j
      rw [hinv k' j]
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      constructor
      · rintro ⟨hj, hjk⟩; refine ⟨hj, ?_⟩
        by_cases hij : i = j <;> simp_all
      · rintro ⟨hj, hjk⟩; refine ⟨hj, ?_⟩
        by_cases hij : i = j <;> simp_all
    · rename_i hk
      have hnm : ∀ kv ∈ out.toList, kv.1 ≠ k := by
        intro kv hm he
        obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hm
        have := (hinv k j).2 ⟨by simpa using hj, by simp_all⟩
        simp_all
      rw [dictInsert_not_mem k v _ hnm, ← Array.toList_push]
      apply dedupGo_eq
      intro k' j
      rw [Std.HashMap.getElem?_insert]
      simp only [Array.size_push, Array.getElem_push]
      by_cases hkk : k = k'
      · subst hkk
        simp only [beq_self_eq_true, ite_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨by omega, by simp⟩
        · rintro ⟨hj, hjk⟩
          split at hjk
          · rename_i hlt; exact absurd hjk (hnm _ (by simp))
          · omega
      · simp only [beq_iff_eq, hkk, ite_false]
        rw [hinv k' j]
        constructor
        · rintro ⟨hj, hjk⟩; exact ⟨by omega, by simp [hj, hjk]⟩
        · rintro ⟨hj, hjk⟩
          split at hjk
          · rename_i hlt; exact ⟨hlt, hjk⟩
          · simp at hjk; exact absurd hjk hkk

/-- `dedup`, linear: a hash index into the output, sized up front. -/
def dedupIdx {β : Type} (kvs : List (String × β)) : List (String × β) :=
  (dedupGo (Std.HashMap.emptyWithCapacity kvs.length) (Array.mkEmpty kvs.length) kvs).toList

theorem dedupIdx_eq {β : Type} (kvs : List (String × β)) : dedupIdx kvs = dedup kvs := by
  unfold dedupIdx dedup
  rw [dedupGo_eq]; · rfl
  intro k i; simp

end LeanPydantic

namespace LeanPydantic

theorem dictInsert_keys {β : Type} (k : String) (v : β) :
    ∀ l : List (String × β), ((l.map Prod.fst).Nodup) → ((dictInsert k v l).map Prod.fst).Nodup
  | [], _ => by simp [dictInsert]
  | (k', v') :: l, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [dictInsert]
    split
    · rename_i he; subst he; simpa using h
    · rename_i hne
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, dictInsert_keys k v l h.2⟩
      intro hm
      have : ∀ l' : List (String × β), k' ∈ (dictInsert k v l').map Prod.fst → k' ∈ l'.map Prod.fst := by
        intro l'
        induction l' with
        | nil =>
          simp only [dictInsert, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => absurd e hne
        | cons a t ih =>
          simp only [dictInsert]
          split
          · simp only [List.map_cons, List.mem_cons]
            rintro (e | e)
            · exact absurd e hne
            · exact .inr e
          · simp only [List.map_cons, List.mem_cons]
            rintro (e | e)
            · exact .inl e
            · exact .inr (ih e)
      exact h.1 (this l hm)

/-- A dict's keys are distinct. -/
theorem dedup_nodup {β : Type} (kvs : List (String × β)) : ((dedup kvs).map Prod.fst).Nodup := by
  unfold dedup
  suffices ∀ acc : List (String × β), (acc.map Prod.fst).Nodup →
      ((kvs.foldl (fun acc kv => dictInsert kv.1 kv.2 acc) acc).map Prod.fst).Nodup from this [] (by simp)
  induction kvs with
  | nil => intro acc h; exact h
  | cons kv kvs ih => intro acc h; exact ih _ (dictInsert_keys kv.1 kv.2 acc h)

theorem dedupIdx_nodup {β : Type} (kvs : List (String × β)) : ((dedupIdx kvs).map Prod.fst).Nodup := by
  rw [dedupIdx_eq]; exact dedup_nodup kvs

end LeanPydantic
