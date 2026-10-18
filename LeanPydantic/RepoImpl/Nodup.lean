import Std.Data.HashSet
import Std.Data.HashSet.Lemmas

/-!
# RepoImpl: deciding `Nodup` in linear time

`List.Nodup` is decidable by comparing every pair, which is quadratic: on a
request body with 100 000 keys that is a denial of service. `nodupFast`
decides it with a hash set, one pass, and `nodupFast_iff` proves it decides
exactly `Nodup`, so the invariants of `Dict` and `PySet` are still fields
with proofs.
-/

namespace LeanPydantic

variable {α : Type} [BEq α] [Hashable α]

/-- Whether the list has no duplicates, with a hash set of the elements seen. -/
def nodupFast (l : List α) : Bool := go (Std.HashSet.emptyWithCapacity l.length) l
where
  /-- The rest has no duplicates, and none of it was seen. -/
  go (seen : Std.HashSet α) : List α → Bool
    | [] => true
    | x :: xs => if seen.contains x then false else go (seen.insert x) xs

theorem nodupFast_go_iff [LawfulBEq α] [LawfulHashable α] (l : List α) (seen : Std.HashSet α) :
    nodupFast.go seen l = true ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen := by
  induction l generalizing seen with
  | nil => simp [nodupFast.go]
  | cons x xs ih =>
    simp only [nodupFast.go]
    by_cases hx : seen.contains x = true
    · simp only [hx, ite_true, Bool.false_eq_true, false_iff, not_and]
      intro _ h
      exact absurd (Std.HashSet.contains_iff_mem.1 hx) (h x List.mem_cons_self)
    · simp only [hx, Bool.false_eq_true, ite_false, ih, Std.HashSet.mem_insert, beq_iff_eq,
        List.nodup_cons, List.mem_cons, forall_eq_or_imp]
      have hx' : x ∉ seen := fun h => hx (Std.HashSet.contains_iff_mem.2 h)
      constructor
      · rintro ⟨hn, h⟩
        exact ⟨⟨fun hm => h x hm (.inl rfl), hn⟩, hx', fun y hy hs => h y hy (.inr hs)⟩
      · rintro ⟨⟨hm, hn⟩, -, h⟩
        refine ⟨hn, fun y hy hxy => ?_⟩
        rcases hxy with e | hs
        · exact hm (e ▸ hy)
        · exact h y hy hs

/-- `nodupFast` decides `Nodup`. -/
theorem nodupFast_iff [LawfulBEq α] [LawfulHashable α] (l : List α) : nodupFast l = true ↔ l.Nodup := by
  simp [nodupFast, nodupFast_go_iff, Std.HashSet.not_mem_emptyWithCapacity]

end LeanPydantic
