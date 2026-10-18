import LeanPydantic.Proofs.Wrappers

/-!
# Proofs: the field combinators are lawful

`Fields.nil` is lawful, and `Fields.field name d rest` is lawful whenever the
field's type is and `rest` is, provided `name` is not already a field of
`rest`. A model's `Fields` value is a chain of these, so its laws need no
proof beyond one `nil_lawful` and one `field_lawful` per field, which the
`deriving Model` handler writes; the freshness side conditions close by
`decide`. `model_lawful` then turns a lawful `Fields` into the laws of the
model.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open LeanJson.Json (lookupLast)

/-! ## Last-wins lookup -/

theorem lookupLast_cons_ne {k k' : String} (h : k' ≠ k) (v : Json) (l : List (String × Json)) :
    lookupLast k ((k', v) :: l) = lookupLast k l := by
  simp only [lookupLast]; cases lookupLast k l <;> simp [h]

theorem lookupLast_eq_none {k : String} :
    ∀ {l : List (String × Json)}, k ∉ l.map Prod.fst → lookupLast k l = none
  | [], _ => rfl
  | (k', v) :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [lookupLast_cons_ne (Ne.symm h.1), lookupLast_eq_none h.2]

theorem lookupLast_cons_self {k : String} {v : Json} {l : List (String × Json)}
    (h : k ∉ l.map Prod.fst) : lookupLast k ((k, v) :: l) = some v := by
  simp [lookupLast, lookupLast_eq_none h]

namespace Fields

variable {α β : Type}

/-! ## One field's validator -/

theorem member_ok [FromJson α] {cfg : Cfg} {j : Json} {name : String} {d : Option α}
    {kvs : List (String × Json)} {a : α} (h : member cfg j name d kvs = .ok a) :
    match lookupLast name kvs with
    | some v => fromJson cfg v = .ok a
    | none => d = some a := by
  unfold member at h
  rw [Keel.Validator.at_ok_iff] at h
  split at h
  · rename_i v hv; rw [hv]; exact h
  · rename_i hv; rw [hv]
    cases d with
    | some x => cases h; rfl
    | none => cases h

theorem member_error [FromJson α] [JsonSchema α] [ToJson α] [LawfulJson α] {cfg : Cfg} {j : Json}
    {name : String} {d : Option α} {kvs : List (String × Json)} {es : List ErrorDetails}
    (h : member cfg j name d kvs = .error es) :
    es ≠ [] ∧ ∀ e ∈ es, ∃ l, e.loc = .key name :: l := by
  unfold member at h
  obtain ⟨es', h', rfl⟩ := (Keel.Validator.at_error_iff _ _ _ _).1 h
  refine ⟨?_, fun e he => ?_⟩
  · simp only [ne_eq, List.map_eq_nil_iff]
    intro hn; subst hn
    split at h'
    · exact LawfulJson.errors_ne_nil (α := α) cfg _ h'
    · split at h' <;> cases h'
  · obtain ⟨e', -, rfl⟩ := List.mem_map.1 he
    exact ⟨e'.loc, rfl⟩

theorem keep_default (name : String) (v : Json) (b : Bool) : keep {} name v b = true := by
  simp [keep]

theorem encode_field [FromJson α] [ToJson α] [JsonSchema α] (name : String) (d : Option α)
    (rest : Fields β) (a : α) (b : β) :
    (field name d rest).encode {} (a, b) = (name, toJson {} a) :: rest.encode {} b := by
  simp [field, keep_default, DumpOpts.nested]

/-! ## The laws -/

theorem nil_lawful : Fields.nil.Lawful where
  decode_encode _ _ _ _ _ := rfl
  encode_keys _ := rfl
  sound _ _ _ _ _ _ := ⟨rfl, fun _ h => nomatch h⟩
  ne_nil _ _ _ := nofun
  loc_key _ _ _ _ h := nomatch h

/-- **The field combinator is lawful.** -/
theorem field_lawful [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] {name : String}
    {d : Option α} {rest : Fields β} (hfresh : name ∉ rest.keys) (hr : rest.Lawful) :
    (field name d rest).Lawful where
  decode_encode cfg j p kvs h := by
    obtain ⟨a, b⟩ := p
    have hk : ∀ k ∈ rest.keys, lookupLast k kvs = lookupLast k (rest.encode {} b) := by
      intro k hk
      rw [h k (List.mem_cons_of_mem _ hk), encode_field,
        lookupLast_cons_ne (fun (e : name = k) => hfresh (e ▸ hk))]
    have hn : lookupLast name kvs = some (toJson {} a) := by
      rw [h name List.mem_cons_self, encode_field, lookupLast_cons_self (by rw [hr.encode_keys]; exact hfresh)]
    show Keel.Validator.both _ _ kvs = _
    rw [Keel.Validator.both_ok_iff]
    refine ⟨?_, hr.decode_encode cfg j b kvs hk⟩
    unfold member
    rw [Keel.Validator.at_ok_iff]
    simp only [hn]
    exact LawfulJson.fromJson_toJson cfg a
  encode_keys p := by
    obtain ⟨a, b⟩ := p
    rw [encode_field]; simp [hr.encode_keys b]; rfl
  sound cfg j kvs p hs h := by
    obtain ⟨a, b⟩ := p
    change Keel.Validator.both _ _ kvs = _ at h
    obtain ⟨hm, hrest⟩ := (Keel.Validator.both_ok_iff _ _ _ _ _).1 h
    obtain ⟨hp, hreq⟩ := hr.sound cfg j kvs b hs hrest
    have hmo := member_ok hm
    refine ⟨?_, ?_⟩
    · show (_ && _) = true
      rw [hp, Bool.and_true]
      split
      · rename_i v hv; rw [hv] at hmo
        exact LawfulJson.schema_sound cfg v a hs hmo
      · rfl
    · intro r hr'
      show (lookupLast r kvs).isSome = true
      simp only [field] at hr'
      split at hr'
      · exact hreq r hr'
      · rename_i hd
        rcases List.mem_cons.1 hr' with rfl | hr'
        · split at hmo
          · rename_i v hv; rw [hv]; rfl
          · subst hmo; simp at hd
        · exact hreq r hr'
  ne_nil cfg j kvs h := by
    change Keel.Validator.both _ _ kvs = _ at h
    have := Keel.Validator.both_error _ _ _ _ h
    revert this
    cases hm : member cfg j name d kvs with
    | error e =>
      have := (member_error hm).1
      cases hw : rest.decode cfg j kvs <;> simp_all
    | ok a =>
      cases hw : rest.decode cfg j kvs with
      | error e => intro he; simp only [List.nil_append] at he; subst he; exact hr.ne_nil cfg j kvs hw
      | ok b => simp [Keel.Validator.both, hm, hw] at h
  loc_key cfg j kvs es h := by
    change Keel.Validator.both _ _ kvs = _ at h
    have hes := Keel.Validator.both_error _ _ _ _ h
    intro e he
    rw [hes, List.mem_append] at he
    rcases he with he | he
    · split at he
      · rename_i es' hm
        obtain ⟨l, hl⟩ := (member_error hm).2 e he
        exact ⟨name, List.mem_cons_self, l, hl⟩
      · simp at he
    · split at he
      · rename_i es' hw
        obtain ⟨k, hk, l, hl⟩ := hr.loc_key cfg j kvs es' hw e he
        exact ⟨k, List.mem_cons_of_mem _ hk, l, hl⟩
      · simp at he

end Fields

end LeanPydantic
