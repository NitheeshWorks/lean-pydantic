import LeanPydantic.Proofs.Containers

/-!
# Proofs: literals, unions, tuples, enumerations

* A literal validates its values' dumps back to themselves (dumps are
  injective, by the element's own round trip), and what it accepts is one of
  its `enum` values.
* **`union_smart_leftmost`**: the leftmost choice that validates strictly and
  exactly is the union's result, whatever the later choices would say.
* A tuple is lawful item by item (`LawfulTupleItems`, preserved by `×`).
* An enumeration is lawful when every value is a member and the values are
  distinct, both closed by `decide` in `deriving Model`.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-! ## A first match -/

theorem find?_eq_of_unique {α : Type} (p : α → Bool) (y : α) (hp : ∀ c, p c = true ↔ c = y) :
    ∀ cs : List α, y ∈ cs → cs.find? p = some y
  | [], h => nomatch h
  | c :: cs, h => by
    by_cases hc : p c = true
    · obtain rfl := (hp c).1 hc
      simp [hc]
    · simp only [List.find?_cons, hc]
      have : c ≠ y := fun e => hc ((hp c).2 e)
      exact find?_eq_of_unique p y hp cs ((List.mem_cons.1 h).resolve_left (Ne.symm this))

theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, h, a, b, ha, hb, hf => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (hf ▸ List.mem_map_of_mem hb') h.1
    · exact absurd (hf.symm ▸ List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map h.2 ha' hb' hf

/-- A lawful type's round-trip dump is injective. -/
theorem toJson_injective {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] {a b : α}
    (h : toJson DumpOpts.roundTrip a = toJson DumpOpts.roundTrip b) : a = b := by
  have ha := LawfulJson.fromJson_toJson (α := α) {} a
  have hb := LawfulJson.fromJson_toJson (α := α) {} b
  rw [h, hb] at ha; cases ha; rfl

/-! ## `Literal[...]` -/

section Literal

variable {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [DecidableEq α] (cs : List α)

omit [FromJson α] [JsonSchema α] [LawfulJson α] in
theorem fromJson_literal (cfg : Cfg) (j : Json) :
    fromJson (α := {x : α // (Constraint.oneOf cs).holds x}) cfg j =
      (fromJsonLiteral cs).fromJson cfg j := rfl

omit [FromJson α] [JsonSchema α] [LawfulJson α] [DecidableEq α] in
theorem laxLiteralInput_strict {cfg : Cfg} (hs : cfg.strict = true) (j : Json) :
    laxLiteralInput cfg j = none := by
  cases j <;> simp [laxLiteralInput, hs]

omit [DecidableEq α] in
theorem literalFind_dump (y : α) (hy : y ∈ cs) : literalFind cs (toJson DumpOpts.roundTrip y) = some y :=
  find?_eq_of_unique _ y (fun c => by
    simp only [decide_eq_true_eq]
    exact ⟨toJson_injective, fun e => e ▸ rfl⟩) cs hy

omit [FromJson α] [JsonSchema α] [LawfulJson α] [DecidableEq α] in
theorem literalFind_spec {j : Json} {c : α} (h : literalFind cs j = some c) :
    c ∈ cs ∧ toJson DumpOpts.roundTrip c = j := by
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

instance (priority := high) : LawfulJson {x : α // (Constraint.oneOf cs).holds x} where
  fromJson_toJson cfg y := by
    rw [fromJson_literal]
    unfold fromJsonLiteral
    simp only
    have hy := literalFind_dump cs y.val y.property
    have : toJson DumpOpts.roundTrip y = toJson DumpOpts.roundTrip y.val := rfl
    split
    · rename_i c hc
      rw [this, hy] at hc; cases hc; rfl
    · rename_i hc
      rw [this, hy] at hc; cases hc
  schema_sound cfg j y hs h := by
    rw [fromJson_literal] at h
    unfold fromJsonLiteral at h
    simp only at h
    split at h
    · rename_i c hc
      cases h
      obtain ⟨hm, hp⟩ := literalFind_spec cs hc
      show Schema.check (.literal _) j = true
      simp only [Schema.check, decide_eq_true_eq, List.mem_map]
      exact ⟨c, hm, hp⟩
    · rw [laxLiteralInput_strict hs] at h; cases h
  errors_ne_nil cfg j := by
    rw [fromJson_literal]
    unfold fromJsonLiteral
    simp only
    split
    · nofun
    · split
      · split <;> nofun
      · nofun

end Literal

/-! ## Smart unions -/

/-- **Smart unions pick the leftmost exact match**: if the leftmost choice
validates the input strictly and exactly, that is the union's value. -/
theorem union_smart_leftmost {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β]
    (cfg : Cfg) (j : Json) (a : α) (h : fromJson (α := α) cfg.strictly j = .ok a)
    (hx : FromJson.exact α j = true) : fromJson (α := α ⊕ β) cfg j = .ok (.inl a) := by
  show smartUnion cfg j = _
  unfold smartUnion
  have : Choices.exactly (τ := α ⊕ β) cfg j = some (.inl a) := by
    show (match fromJson (α := α) cfg.strictly j with
      | .ok a => if FromJson.exact α j then some (Sum.inl a) else (Choices.exactly (τ := β) cfg j).map Sum.inr
      | .error _ => (Choices.exactly (τ := β) cfg j).map Sum.inr) = _
    rw [h]; simp [hx]
  rw [this]

/-- Failing an exact match, the leftmost strict match wins. -/
theorem union_smart_strict {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [Choices β]
    (cfg : Cfg) (j : Json) (a : α) (hnone : Choices.exactly (τ := α ⊕ β) cfg j = none)
    (h : fromJson (α := α) cfg.strictly j = .ok a) : fromJson (α := α ⊕ β) cfg j = .ok (.inl a) := by
  show smartUnion cfg j = _
  unfold smartUnion
  rw [hnone]
  have : Choices.strictly (τ := α ⊕ β) cfg j = some (.inl a) := by
    show (match fromJson (α := α) cfg.strictly j with
      | .ok a => some (Sum.inl a)
      | .error _ => (Choices.strictly (τ := β) cfg j).map Sum.inr) = _
    rw [h]
  rw [this]

/-! ## Tuples -/

/-- The laws of a tuple's items. -/
class LawfulTupleItems (τ : Type) [TupleItems τ] : Prop where
  decode_encode : ∀ (cfg : Cfg) (w : Json) (i : Nat) (t : τ) (rest : List Json),
    TupleItems.decode cfg w i (TupleItems.encode DumpOpts.roundTrip t ++ rest) = .ok t
  encode_length : ∀ (o : DumpOpts) (t : τ), (TupleItems.encode o t).length = TupleItems.arity τ
  sound : ∀ (cfg : Cfg) (w : Json) (i : Nat) (xs : List Json) (t : τ), cfg.strict = true →
    xs.length ≤ TupleItems.arity τ → TupleItems.decode cfg w i xs = .ok t →
      Schema.checkTuple (TupleItems.schemas τ) xs = true
  ne_nil : ∀ (cfg : Cfg) (w : Json) (i : Nat) (xs : List Json), TupleItems.decode (τ := τ) cfg w i xs ≠ .error []
  arity_pos : 0 < TupleItems.arity τ

theorem tupleItem_ne_nil {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α]
    (cfg : Cfg) (w : Json) (i : Nat) (xs : List Json) : tupleItem (α := α) cfg w i xs ≠ .error [] := by
  intro he
  obtain ⟨es', h', hm⟩ := (Keel.Validator.at_error_iff _ _ _ _).1 he
  cases xs with
  | nil => cases h'; simp at hm
  | cons x _ => simp at hm; subst hm; exact LawfulJson.errors_ne_nil cfg x h'

instance (priority := low) {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] :
    LawfulTupleItems α where
  decode_encode cfg w i t rest := by
    show tupleItem cfg w i (toJson DumpOpts.roundTrip t :: rest) = _
    unfold tupleItem
    rw [Keel.Validator.at_ok_iff]
    exact LawfulJson.fromJson_toJson cfg t
  encode_length _ _ := rfl
  sound cfg w i xs t hs hl h := by
    change tupleItem cfg w i xs = _ at h
    unfold tupleItem at h
    rw [Keel.Validator.at_ok_iff] at h
    match xs, hl with
    | [x], _ =>
      show Schema.checkTuple [JsonSchema.schema α] [x] = true
      simp only [Schema.checkTuple, Bool.and_true]
      exact LawfulJson.schema_sound cfg x t hs h
    | [], _ => cases h
    | _ :: _ :: _, hl => simp [TupleItems.arity] at hl
  ne_nil := tupleItem_ne_nil
  arity_pos := Nat.one_pos

instance {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [TupleItems β]
    [hb : LawfulTupleItems β] : LawfulTupleItems (α × β) where
  decode_encode cfg w i t rest := by
    obtain ⟨a, b⟩ := t
    show Keel.Validator.both (tupleItem cfg w i) (fun xs => TupleItems.decode cfg w (i + 1) xs.tail)
      (toJson DumpOpts.roundTrip a :: (TupleItems.encode DumpOpts.roundTrip b ++ rest)) = _
    rw [Keel.Validator.both_ok_iff]
    refine ⟨?_, hb.decode_encode cfg w (i + 1) b rest⟩
    unfold tupleItem
    rw [Keel.Validator.at_ok_iff]
    exact LawfulJson.fromJson_toJson cfg a
  encode_length o t := by
    show (toJson o t.1 :: TupleItems.encode o t.2).length = TupleItems.arity β + 1
    simp [hb.encode_length]
  sound cfg w i xs t hs hl h := by
    obtain ⟨a, b⟩ := t
    change Keel.Validator.both _ _ xs = _ at h
    obtain ⟨ha, hb'⟩ := (Keel.Validator.both_ok_iff _ _ _ _ _).1 h
    unfold tupleItem at ha
    rw [Keel.Validator.at_ok_iff] at ha
    cases xs with
    | nil => cases ha
    | cons x xs =>
      show Schema.checkTuple (JsonSchema.schema α :: TupleItems.schemas β) (x :: xs) = true
      simp only [Schema.checkTuple]
      rw [LawfulJson.schema_sound cfg x a hs ha, Bool.true_and]
      have har : TupleItems.arity (α × β) = TupleItems.arity β + 1 := rfl
      exact hb.sound cfg w (i + 1) xs b hs (by simp at hl; omega) hb'
  ne_nil cfg w i xs h := by
    change Keel.Validator.both _ _ xs = _ at h
    have hes := Keel.Validator.both_error _ _ _ _ h
    have h1 := tupleItem_ne_nil (α := α) cfg w i xs
    have h2 := hb.ne_nil cfg w (i + 1) xs.tail
    revert hes
    cases e1 : tupleItem (α := α) cfg w i xs <;> cases e2 : TupleItems.decode (τ := β) cfg w (i + 1) xs.tail <;>
      simp_all [Keel.Validator.both]
  arity_pos := Nat.succ_pos _

theorem fromJson_prod {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] (cfg : Cfg)
    (xs : List Json) : fromJson (α := α × β) cfg (.arr ⟨xs⟩) =
      if xs.length > TupleItems.arity (α × β) then
        .error [ErrorDetails.mk (.tooLong "Tuple" (TupleItems.arity (α × β)) xs.length) [] (.arr ⟨xs⟩) cfg.mode]
      else TupleItems.decode cfg (.arr ⟨xs⟩) 0 xs := rfl

instance {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] [TupleItems β]
    [LawfulTupleItems β] : LawfulJson (α × β) where
  fromJson_toJson cfg t := by
    show fromJson cfg (.arr ⟨TupleItems.encode DumpOpts.roundTrip t⟩) = _
    rw [fromJson_prod]
    split
    · rename_i hl; rw [LawfulTupleItems.encode_length] at hl; omega
    · simpa using LawfulTupleItems.decode_encode cfg (.arr ⟨TupleItems.encode DumpOpts.roundTrip t⟩) 0 t []
  schema_sound cfg j t hs h := by
    cases j with
    | arr a =>
      cases a with
      | mk xs =>
        rw [fromJson_prod] at h
        split at h
        · cases h
        · rename_i hl
          show Schema.check (.tuple _) _ = true
          simp only [Schema.check]
          exact LawfulTupleItems.sound cfg _ 0 xs t hs (by omega) h
    | _ => cases h
  errors_ne_nil cfg j := by
    cases j with
    | arr a =>
      cases a with
      | mk xs =>
        rw [fromJson_prod]
        split
        · nofun
        · exact LawfulTupleItems.ne_nil cfg _ 0 xs
    | _ => nofun

instance {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] [TupleItems β] : NonNull (α × β) :=
  ⟨fun _ _ => nofun⟩

/-! ## Enumerations -/

/-- The laws of an enumeration: every value of the type is a member, and the
members' values are distinct. -/
class LawfulEnumeration (α : Type) [e : Enumeration α] : Prop where
  complete : ∀ a : α, a ∈ e.members
  distinct : (e.members.map e.value).Nodup

instance (priority := low) {α : Type} [e : Enumeration α] [h : LawfulEnumeration α] : LawfulJson α where
  fromJson_toJson cfg a := by
    show Enumeration.validate cfg (.str (e.value a)) = _
    unfold Enumeration.validate
    simp only
    rw [find?_eq_of_unique _ a (fun c => by
      simp only [decide_eq_true_eq]
      constructor
      · intro hv
        exact inj_of_nodup_map h.distinct (h.complete c) (h.complete a) hv
      · intro hc; rw [hc]) e.members (h.complete a)]
  schema_sound cfg j a _ hv := by
    change Enumeration.validate cfg j = _ at hv
    unfold Enumeration.validate at hv
    cases j with
    | str s =>
      simp only at hv
      split at hv
      · rename_i c hc
        cases hv
        have hp := List.find?_some hc
        simp only [decide_eq_true_eq] at hp
        show Schema.check (.ref _ (.annotated (.literal _) _ _)) _ = true
        simp only [Schema.check, decide_eq_true_eq, List.mem_map]
        exact ⟨a, List.mem_of_find?_eq_some hc, by rw [hp]⟩
      · cases hv
    | _ => cases hv
  errors_ne_nil cfg j := by
    show Enumeration.validate cfg j ≠ _
    unfold Enumeration.validate
    cases j <;> simp only <;> (try split) <;> nofun

instance (priority := low) {α : Type} [Enumeration α] : NonNull α := ⟨fun _ _ => nofun⟩

end LeanPydantic
