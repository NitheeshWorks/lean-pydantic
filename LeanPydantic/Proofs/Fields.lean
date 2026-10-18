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

variable {factory byName : Bool}

/-- The validator of a field read by `key`, and also by `name` when `byName`. -/
abbrev fieldMember [FromJson α] (byName : Bool) (cfg : Cfg) (j : Json) (key name : String) (d : Option α) :
    Keel.Validator ErrorDetails (List (String × Json)) α :=
  if byName then memberBy cfg j key name d else member cfg j key d

theorem fieldMember_present [FromJson α] {cfg : Cfg} {j : Json} {key name : String} {d : Option α}
    {kvs : List (String × Json)} {v : Json} (h : lookupLast key kvs = some v) :
    fieldMember byName cfg j key name d kvs = member cfg j key d kvs := by
  cases byName
  · rfl
  · simp only [fieldMember, ite_true, memberBy, h]

theorem fieldMember_error [FromJson α] [JsonSchema α] [ToJson α] [LawfulJson α] {cfg : Cfg} {j : Json}
    {key name : String} {d : Option α} {kvs : List (String × Json)} {es : List ErrorDetails}
    (h : fieldMember byName cfg j key name d kvs = .error es) :
    es ≠ [] ∧ ∀ e ∈ es, ∃ k, (k = key ∨ k = name) ∧ ∃ l, e.loc = .key k :: l := by
  have of_member : ∀ k, (k = key ∨ k = name) → member cfg j k d kvs = .error es →
      es ≠ [] ∧ ∀ e ∈ es, ∃ k, (k = key ∨ k = name) ∧ ∃ l, e.loc = .key k :: l := by
    intro k hk hm
    obtain ⟨hne, hl⟩ := member_error hm
    exact ⟨hne, fun e he => ⟨k, hk, hl e he⟩⟩
  cases byName
  · exact of_member key (Or.inl rfl) h
  · simp only [fieldMember, ite_true, memberBy] at h
    split at h
    · exact of_member key (Or.inl rfl) h
    · split at h
      · exact of_member name (Or.inr rfl) h
      · exact of_member key (Or.inl rfl) h

theorem keep_roundTrip (name : String) (v : Json) (b s : Bool) :
    keep DumpOpts.roundTrip name v b s = true := by
  simp [keep, DumpOpts.roundTrip]

theorem encode_field [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) (a : α) (b : β) :
    (field name alias d rest factory byName).encode DumpOpts.roundTrip (a, b) =
      (alias.getD name, toJson DumpOpts.roundTrip a) :: rest.encode DumpOpts.roundTrip b := by
  simp only [field, keep_roundTrip, ite_true]
  rfl

theorem field_keys [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) :
    (field name alias d rest factory byName).keys = alias.getD name :: rest.keys := rfl

theorem field_names [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) :
    (field name alias d rest factory byName).names = name :: rest.names := rfl

theorem field_decode [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) (cfg : Cfg) (j : Json) :
    (field name alias d rest factory byName).decode cfg j =
      Keel.Validator.both (fieldMember byName cfg j (alias.getD name) name d) (rest.decode cfg j) := rfl

theorem field_props [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) :
    ∃ t df, (field name alias d rest factory byName).props =
      (alias.getD name, .annotated (JsonSchema.schema α) t df) :: rest.props := ⟨_, _, rfl⟩

theorem field_required [FromJson α] [ToJson α] [JsonSchema α] (name : String) (alias : Option String)
    (d : Option α) (rest : Fields β) :
    (field name alias d rest factory byName).required =
      if d.isSome then rest.required else alias.getD name :: rest.required := rfl

theorem mem_ite_cons {γ : Type} {c : Bool} {x p : γ} {l : List γ} (h : p ∈ (if c = true then x :: l else l)) :
    (p = x ∧ c = true) ∨ p ∈ l := by
  cases c
  · exact Or.inr (by simpa using h)
  · simp only [ite_true, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr h

theorem mem_ite_singleton {γ : Type} {c : Bool} {x q : γ} (h : q ∈ (if c = true then [x] else [])) :
    c = true ∧ q = x := by
  cases c
  · simp at h
  · simpa using h

theorem ite_cons_mem_head {γ : Type} {c : Bool} {x : γ} {l : List γ} (h : c = true) :
    x ∈ (if c = true then x :: l else l) := by
  rw [if_pos h]; exact List.mem_cons_self

theorem mem_ite_cons_of_mem {γ : Type} {c : Bool} {x p : γ} {l : List γ} (h : p ∈ l) :
    p ∈ (if c = true then x :: l else l) := by
  cases c
  · simpa using h
  · exact List.mem_cons_of_mem _ h

theorem keep_unset {o : DumpOpts} {n : String} {v : Json} {d s : Bool} (h : keep o n v d s = true)
    (hu : o.exclude_unset = true) : s = true := by
  cases s
  · simp [keep, hu] at h
  · rfl

/-! ## The laws -/

theorem nil_lawful : Fields.nil.Lawful where
  lookups_head := rfl
  props_keys := rfl
  decode_encode _ _ _ _ _ := rfl
  encode_keys _ := rfl
  ne_nil _ _ _ := nofun
  loc_key _ _ _ _ h := nomatch h
  unset_subset _ _ _ _ h := nomatch h
  unset_complete _ _ _ _ _ _ _ _ h := nomatch h
  names_nodup := List.nodup_nil
  setFields_sub _ _ _ h := nomatch h
  names_set _ _ _ h := nomatch h

theorem nil_sound : Fields.nil.Sound where
  by_key := rfl
  sound _ _ _ _ _ _ := ⟨by simp [nil, Schema.checkProps], fun _ h => nomatch h⟩

/-- **The field combinator is lawful**, with or without `populate_by_name`. -/
theorem field_lawful [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] {name : String}
    {alias : Option String} {d : Option α} {rest : Fields β} (hfresh : alias.getD name ∉ rest.keys)
    (hname : name ∉ rest.names) (hr : rest.Lawful) : (field name alias d rest factory byName).Lawful where
  names_nodup := List.nodup_cons.2 ⟨hname, hr.names_nodup⟩
  setFields_sub sf ns q hq := by
    dsimp only [field] at hq ⊢
    rw [List.zip_cons_cons]
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨-, rfl⟩ := mem_ite_singleton hq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hr.setFields_sub sf ns q hq)
  names_set sf ns q hq hn := by
    dsimp only [field] at hq ⊢
    rw [List.zip_cons_cons] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact List.mem_append_left _ (by simp [isSet, hn])
    · exact List.mem_append_right _ (hr.names_set sf ns q hq hn)
  lookups_head := by
    show (if byName then [alias.getD name, name] else [alias.getD name]).head? :: rest.lookups.map List.head? =
      some (alias.getD name) :: rest.keys.map some
    rw [hr.lookups_head]; cases byName <;> rfl
  props_keys := by
    obtain ⟨t, df, hpr⟩ := field_props (factory := factory) (byName := byName) name alias d rest
    rw [hpr, field_keys, List.map_cons, hr.props_keys]
  decode_encode cfg j p kvs h := by
    obtain ⟨a, b⟩ := p
    rw [field_keys] at h
    have hk : ∀ k ∈ rest.keys, lookupLast k kvs = lookupLast k (rest.encode DumpOpts.roundTrip b) := by
      intro k hk
      rw [h k (List.mem_cons_of_mem _ hk), encode_field (byName := byName),
        lookupLast_cons_ne (fun (e : alias.getD name = k) => hfresh (e ▸ hk))]
    have hn : lookupLast (alias.getD name) kvs = some (toJson DumpOpts.roundTrip a) := by
      rw [h _ List.mem_cons_self, encode_field (byName := byName),
        lookupLast_cons_self (by rw [hr.encode_keys]; exact hfresh)]
    rw [field_decode, Keel.Validator.both_ok_iff]
    refine ⟨?_, hr.decode_encode cfg j b kvs hk⟩
    rw [fieldMember_present hn]
    unfold member
    rw [Keel.Validator.at_ok_iff]
    simp only [hn]
    exact LawfulJson.fromJson_toJson cfg a
  encode_keys p := by
    obtain ⟨a, b⟩ := p
    rw [encode_field, field_keys]; simp [hr.encode_keys b]
  ne_nil cfg j kvs h := by
    rw [field_decode] at h
    have := Keel.Validator.both_error _ _ _ _ h
    revert this
    cases hm : fieldMember byName cfg j (alias.getD name) name d kvs with
    | error e =>
      have := (fieldMember_error hm).1
      cases hw : rest.decode cfg j kvs <;> simp_all
    | ok a =>
      cases hw : rest.decode cfg j kvs with
      | error e => intro he; simp only [List.nil_append] at he; subst he; exact hr.ne_nil cfg j kvs hw
      | ok b => simp [Keel.Validator.both, hm, hw] at h
  loc_key cfg j kvs es h := by
    rw [field_decode] at h
    have hes := Keel.Validator.both_error _ _ _ _ h
    intro e he
    rw [hes, List.mem_append] at he
    rw [field_keys, field_names]
    rcases he with he | he
    · split at he
      · rename_i es' hm
        obtain ⟨k, hk, l, hl⟩ := (fieldMember_error hm).2 e he
        rcases hk with rfl | rfl
        · exact ⟨_, Or.inl List.mem_cons_self, l, hl⟩
        · exact ⟨_, Or.inr List.mem_cons_self, l, hl⟩
      · simp at he
    · split at he
      · rename_i es' hw
        obtain ⟨k, hk, l, hl⟩ := hr.loc_key cfg j kvs es' hw e he
        rcases hk with hk | hk
        · exact ⟨k, Or.inl (List.mem_cons_of_mem _ hk), l, hl⟩
        · exact ⟨k, Or.inr (List.mem_cons_of_mem _ hk), l, hl⟩
      · simp at he
  unset_subset o b hu p hp := by
    obtain ⟨a, b⟩ := b
    simp only [field] at hp ⊢
    rcases mem_ite_cons hp with ⟨rfl, hk⟩ | hp
    · have := keep_unset hk hu
      exact ⟨(name, alias.getD name), List.mem_append_left _ (by simp [this]), by simp only [dumpKey]⟩
    · obtain ⟨q, hq, he⟩ := hr.unset_subset o b hu p hp
      exact ⟨q, List.mem_append_right _ hq, he⟩
  unset_complete o b hu hi he hn hd q hq := by
    obtain ⟨a, b⟩ := b
    dsimp only [field] at hq ⊢
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hs, rfl⟩ := mem_ite_singleton hq
      exact ⟨_, ite_cons_mem_head (by simp [keep, hu, hi, he, hn, hd, hs]), by simp only [dumpKey]⟩
    · obtain ⟨p, hp, hpe⟩ := hr.unset_complete o b hu hi he hn hd q hq
      exact ⟨p, mem_ite_cons_of_mem hp, hpe⟩

/-- **The field combinator keeps the schema law**, for a field read by its
key alone. -/
theorem field_sound [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] {name : String}
    {alias : Option String} {d : Option α} {rest : Fields β}
    (hr : rest.Sound) : (field name alias d rest factory).Sound where
  by_key := by
    show [alias.getD name] :: rest.lookups = (alias.getD name :: rest.keys).map ([·])
    rw [hr.by_key]; rfl
  sound cfg j kvs p hs h := by
    obtain ⟨a, b⟩ := p
    rw [field_decode] at h
    obtain ⟨hm, hrest⟩ := (Keel.Validator.both_ok_iff _ _ _ _ _).1 h
    obtain ⟨hp, hreq⟩ := hr.sound cfg j kvs b hs hrest
    have hmo := member_ok hm
    refine ⟨?_, ?_⟩
    · obtain ⟨t, df, hpr⟩ := field_props (factory := factory) (byName := false) name alias d rest
      rw [hpr]
      simp only [Schema.checkProps, hp, Bool.and_true]
      split
      · rename_i v hv; rw [hv] at hmo
        simp only [Schema.check]
        exact LawfulJson.schema_sound cfg v a hs hmo
      · rfl
    · intro r hr'
      rw [field_required] at hr'
      split at hr'
      · exact hreq r hr'
      · rename_i hd
        rcases List.mem_cons.1 hr' with rfl | hr'
        · split at hmo
          · rename_i v hv; rw [hv]; rfl
          · subst hmo; simp at hd
        · exact hreq r hr'

/-! ## The extra policy -/

theorem lookupLast_isSome_iff {k : String} : ∀ {kvs : List (String × Json)},
    (lookupLast k kvs).isSome = true ↔ k ∈ kvs.map Prod.fst
  | [] => by simp [lookupLast]
  | (k', v) :: kvs => by
    have ih := lookupLast_isSome_iff (k := k) (kvs := kvs)
    simp only [lookupLast, List.map_cons, List.mem_cons]
    cases hw : lookupLast k kvs with
    | some w =>
      rw [hw] at ih
      simp only [Option.isSome_some, true_iff] at ih ⊢
      exact Or.inr ih
    | none =>
      rw [hw] at ih
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at ih
      by_cases h : k' = k
      · subst h; simp
      · simp only [h, ite_false, Option.isSome_none, Bool.false_eq_true, false_iff, not_or]
        exact ⟨fun e => h e.symm, ih⟩

theorem lookupFirst_single (k : String) (kvs : List (String × Json)) :
    lookupFirst [k] kvs = (lookupLast k kvs).map (k, ·) := by
  simp only [lookupFirst]; cases lookupLast k kvs <;> rfl

/-- Without `populate_by_name`, the fields read exactly their keys that the
input has. -/
theorem lookupFirst_single_fst (k : String) (kvs : List (String × Json)) :
    (lookupFirst [k] kvs).map Prod.fst = (lookupLast k kvs).map (fun _ => k) := by
  rw [lookupFirst_single, Option.map_map]; rfl

theorem mem_consumed_iff {F : Fields β} (hk : F.ByKey) (kvs : List (String × Json)) (k : String) :
    k ∈ F.consumed kvs ↔ k ∈ F.keys ∧ k ∈ kvs.map Prod.fst := by
  rw [← lookupLast_isSome_iff]
  simp only [consumed, show F.lookups = _ from hk, List.mem_filterMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨k', hk', rfl⟩, h⟩
    rw [lookupFirst_single_fst] at h
    cases hv : lookupLast k' kvs with
    | none => rw [hv] at h; cases h
    | some v => rw [hv] at h; cases h; exact ⟨hk', by rw [hv]; rfl⟩
  · rintro ⟨hk, hm⟩
    refine ⟨[k], ⟨k, hk, rfl⟩, ?_⟩
    rw [lookupFirst_single_fst]
    cases hv : lookupLast k kvs with
    | none => rw [hv] at hm; cases hm
    | some v => rfl

/-- A field's key that the input has is read (it is tried first). -/
theorem key_mem_consumed {F : Fields β} (hl : F.Lawful) (kvs : List (String × Json)) {k : String}
    (hk : k ∈ F.keys) (hm : k ∈ kvs.map Prod.fst) : k ∈ F.consumed kvs := by
  have : some k ∈ F.lookups.map List.head? := by rw [hl.lookups_head]; exact List.mem_map_of_mem hk
  obtain ⟨l, hl', he⟩ := List.mem_map.1 this
  cases l with
  | nil => cases he
  | cons k' t =>
    cases he
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (lookupLast_isSome_iff.2 hm)
    simp only [consumed, List.mem_filterMap]
    exact ⟨k :: t, hl', by simp [lookupFirst, hv]⟩

theorem extras_eq_nil_iff (F : Fields β) (mode : InputMode) (kvs : List (String × Json)) :
    F.extras mode kvs = [] ↔ ∀ p ∈ kvs, p.1 ∈ F.accepted mode kvs := by
  simp [extras, List.filter_eq_nil_iff]

theorem forbidExtras_ok_iff (cfg : Cfg) (F : Fields β) (kvs : List (String × Json)) :
    forbidExtras cfg F kvs = .ok () ↔ F.extras cfg.mode kvs = [] := by
  unfold forbidExtras; split <;> simp_all

theorem forbidExtras_error (cfg : Cfg) (F : Fields β) (kvs : List (String × Json)) (es : List ErrorDetails)
    (h : forbidExtras cfg F kvs = .error es) :
    es ≠ [] ∧ ∀ e ∈ es, ∃ kv ∈ kvs, e.loc = [.key kv.1] := by
  unfold forbidExtras at h
  cases hx : F.extras cfg.mode kvs with
  | nil => rw [hx] at h; cases h
  | cons x xs =>
    rw [hx] at h
    cases h
    refine ⟨by simp, fun e he => ?_⟩
    obtain ⟨kv, hkv, rfl⟩ := List.mem_map.1 he
    rw [← hx] at hkv
    exact ⟨kv, (List.mem_filter.1 hkv).1, rfl⟩

/-- **`extra='forbid'`**: a model validates an object exactly when it has no
extras (`accepted`: the keys its fields read from Python objects; every
field key and name from JSON text) and every field validates. -/
theorem validate_forbid_iff (title : String) (F : Fields β) (back : β → α) (cfg : Cfg)
    (kvs : List (String × Json)) (a : α) :
    validate title .forbid F back cfg (.obj ⟨kvs⟩) = .ok a ↔
      (∀ p ∈ kvs, p.1 ∈ F.accepted cfg.mode kvs) ∧ ∃ b, F.decode cfg (.obj ⟨kvs⟩) kvs = .ok b ∧ back b = a := by
  rw [← extras_eq_nil_iff, ← forbidExtras_ok_iff]
  simp only [validate]
  cases cfg.mode with
  | python =>
    constructor
    · intro h
      cases hb : Keel.Validator.both (F.decode cfg (.obj ⟨kvs⟩)) (forbidExtras cfg F) kvs with
      | error e => rw [hb] at h; cases h
      | ok p =>
        rw [hb] at h
        obtain ⟨b, u⟩ := p
        obtain ⟨hd, hf⟩ := (Keel.Validator.both_ok_iff _ _ _ _ _).1 hb
        simp only [Except.map, Except.ok.injEq] at h
        exact ⟨hf, b, hd, h⟩
    · rintro ⟨hf, b, hd, rfl⟩
      rw [(Keel.Validator.both_ok_iff _ _ _ b ()).2 ⟨hd, hf⟩]; rfl
  | json =>
    constructor
    · intro h
      cases hb : Keel.Validator.both (forbidExtras cfg F) (F.decode cfg (.obj ⟨kvs⟩)) kvs with
      | error e => rw [hb] at h; cases h
      | ok p =>
        rw [hb] at h
        obtain ⟨u, b⟩ := p
        obtain ⟨hf, hd⟩ := (Keel.Validator.both_ok_iff _ _ _ _ _).1 hb
        simp only [Except.map, Except.ok.injEq] at h
        exact ⟨hf, b, hd, h⟩
    · rintro ⟨hf, b, hd, rfl⟩
      rw [(Keel.Validator.both_ok_iff _ _ _ () b).2 ⟨hf, hd⟩]; rfl

/-- Without `populate_by_name`, a member is accepted exactly when its key is
one of `acceptedNames`. -/
theorem mem_accepted_iff {F : Fields β} (hl : F.ByKey) (mode : InputMode) (kvs : List (String × Json))
    (k : String) (hk : k ∈ kvs.map Prod.fst) : k ∈ F.accepted mode kvs ↔ k ∈ F.acceptedNames mode := by
  cases mode with
  | python => simp only [accepted, acceptedNames, mem_consumed_iff hl, hk, and_true]
  | json => rfl

/-- `extra='forbid'` without `populate_by_name`: a model validates an object
exactly when every member's key is accepted (a field's key; from JSON text,
also a field's name) and every field validates. -/
theorem validate_forbid_keys_iff {title : String} {F : Fields β} {back : β → α} (hl : F.ByKey) (cfg : Cfg)
    (kvs : List (String × Json)) (a : α) :
    validate title .forbid F back cfg (.obj ⟨kvs⟩) = .ok a ↔
      (∀ p ∈ kvs, p.1 ∈ F.acceptedNames cfg.mode) ∧
        ∃ b, F.decode cfg (.obj ⟨kvs⟩) kvs = .ok b ∧ back b = a := by
  rw [validate_forbid_iff]
  have : (∀ p ∈ kvs, p.1 ∈ F.accepted cfg.mode kvs) ↔ ∀ p ∈ kvs, p.1 ∈ F.acceptedNames cfg.mode :=
    ⟨fun h p hp => (mem_accepted_iff hl _ kvs p.1 (List.mem_map_of_mem hp)).1 (h p hp),
     fun h p hp => (mem_accepted_iff hl _ kvs p.1 (List.mem_map_of_mem hp)).2 (h p hp)⟩
  rw [this]

theorem keys_sub_acceptedNames (F : Fields β) (mode : InputMode) (k : String) (h : k ∈ F.keys) :
    k ∈ F.acceptedNames mode := by
  cases mode with
  | python => exact h
  | json => exact List.mem_append_left _ h

/-- Validating a default dump gives the value back, under every policy. -/
theorem validate_encode {title : String} {extra : Extra} {F : Fields β} {back : β → α} {into : α → β}
    (hl : F.Lawful) (hb : ∀ a, back (into a) = a) (cfg : Cfg) (a : α) :
    validate title extra F back cfg (.obj ⟨F.encode DumpOpts.roundTrip (into a)⟩) = .ok a := by
  have hdec := hl.decode_encode cfg (.obj ⟨F.encode DumpOpts.roundTrip (into a)⟩) (into a) _ (fun _ _ => rfl)
  cases extra with
  | forbid =>
    refine (validate_forbid_iff title F back cfg _ a).2 ⟨fun p hp => ?_, into a, hdec, hb a⟩
    have hk : p.1 ∈ F.keys := by rw [← hl.encode_keys (into a)]; exact List.mem_map_of_mem hp
    cases cfg.mode with
    | python => exact key_mem_consumed hl _ hk (List.mem_map_of_mem hp)
    | json => exact List.mem_append_left _ hk
  | ignore | allow => simp [validate, hdec, Except.map, hb]

/-- What strict validation accepts conforms to the model's schema, under
every policy (`additionalProperties: false` under `forbid`), provided under
`forbid` that every field name is a key: pydantic's JSON validation accepts
(and drops) an aliased field's name, which its schema forbids. -/
theorem validate_sound {title : String} {extra : Extra} {F : Fields β} {back : β → α} (hl : F.Lawful)
    (hsd : F.Sound) (hn : extra = .forbid → ∀ n ∈ F.names, n ∈ F.keys)
    (cfg : Cfg) (j : Json) (a : α) (hs : cfg.strict = true) (h : validate title extra F back cfg j = .ok a) :
    Schema.check (schema title extra F) j = true := by
  rcases j with _ | _ | _ | _ | _ | ⟨⟨kvs⟩⟩
  all_goals try (simp [validate] at h; done)
  obtain ⟨b, hd, hx⟩ : ∃ b, F.decode cfg (.obj ⟨kvs⟩) kvs = .ok b ∧
      (extra = .forbid → ∀ p ∈ kvs, p.1 ∈ F.keys) := by
    cases extra with
    | forbid =>
      obtain ⟨hk, b, hd, -⟩ := (validate_forbid_keys_iff hsd.by_key cfg kvs a).1 h
      refine ⟨b, hd, fun _ p hp => ?_⟩
      have := hk p hp
      cases hm : cfg.mode with
      | python => rw [hm] at this; exact this
      | json =>
        rw [hm] at this
        rcases List.mem_append.1 this with h' | h'
        · exact h'
        · exact hn rfl _ h'
    | ignore | allow =>
      simp only [validate] at h
      cases hd : F.decode cfg (.obj ⟨kvs⟩) kvs with
      | error e => rw [hd] at h; cases h
      | ok b => exact ⟨b, rfl, nofun⟩
  obtain ⟨hp, hr⟩ := hsd.sound cfg _ kvs b hs hd
  simp only [schema, Schema.check, hp, Bool.true_and, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  refine ⟨hr, ?_⟩
  by_cases hf : extra = .forbid
  · right
    intro kv hkv
    have hk := hx hf kv hkv
    rw [← hl.props_keys] at hk
    obtain ⟨q, hq, he⟩ := List.mem_map.1 hk
    exact List.any_eq_true.2 ⟨q, hq, by simp [he]⟩
  · exact Or.inl hf

/-- A failed validation names at least one error, under every policy. -/
theorem validate_ne_nil {title : String} {extra : Extra} {F : Fields β} {back : β → α} (hl : F.Lawful)
    (cfg : Cfg) (j : Json) : validate title extra F back cfg j ≠ .error [] := by
  rcases j with _ | _ | _ | _ | _ | ⟨⟨kvs⟩⟩
  all_goals try (simp [validate]; done)
  have hne := hl.ne_nil cfg (.obj ⟨kvs⟩) kvs
  cases extra with
  | forbid =>
    simp only [validate]
    cases cfg.mode <;>
    cases hd : F.decode cfg (.obj ⟨kvs⟩) kvs <;> cases hf : forbidExtras cfg F kvs <;>
      simp_all [Keel.Validator.both, Except.map] <;> simp_all [forbidExtras_error cfg F kvs _ hf]
  | ignore | allow =>
    simp only [validate]
    cases hd : F.decode cfg (.obj ⟨kvs⟩) kvs <;> simp_all [Except.map]

/-- Every error of a model on an object is under one of its fields' keys,
or, under `forbid`, under one of the input's keys. -/
theorem validate_loc {title : String} {extra : Extra} {F : Fields β} {back : β → α} (hl : F.Lawful)
    (cfg : Cfg) (kvs : List (String × Json)) (es : List ErrorDetails)
    (h : validate title extra F back cfg (.obj ⟨kvs⟩) = .error es) :
    ∀ e ∈ es, ∃ k, (k ∈ F.keys ∨ k ∈ F.names ∨ (extra = .forbid ∧ k ∈ kvs.map Prod.fst)) ∧ ∃ l, e.loc = .key k :: l := by
  have field_errs : ∀ es', F.decode cfg (.obj ⟨kvs⟩) kvs = .error es' → ∀ e ∈ es',
      ∃ k, (k ∈ F.keys ∨ k ∈ F.names ∨ (extra = .forbid ∧ k ∈ kvs.map Prod.fst)) ∧ ∃ l, e.loc = .key k :: l := by
    intro es' hd e he
    obtain ⟨k, hk, l, hl'⟩ := hl.loc_key cfg _ kvs es' hd e he
    rcases hk with hk | hk
    · exact ⟨k, Or.inl hk, l, hl'⟩
    · exact ⟨k, Or.inr (Or.inl hk), l, hl'⟩
  have extra_errs : extra = .forbid → ∀ es', forbidExtras cfg F kvs = .error es' → ∀ e ∈ es',
      ∃ k, (k ∈ F.keys ∨ k ∈ F.names ∨ (extra = .forbid ∧ k ∈ kvs.map Prod.fst)) ∧ ∃ l, e.loc = .key k :: l := by
    intro hx es' hf e he
    obtain ⟨kv, hkv, hloc⟩ := (forbidExtras_error cfg F kvs es' hf).2 e he
    exact ⟨kv.1, Or.inr (Or.inr ⟨hx, List.mem_map_of_mem hkv⟩), [], hloc⟩
  cases extra with
  | forbid =>
    simp only [validate] at h
    cases hm : cfg.mode with
    | python =>
      rw [hm] at h
      cases hb : Keel.Validator.both (F.decode cfg (.obj ⟨kvs⟩)) (forbidExtras cfg F) kvs with
      | ok p => rw [hb] at h; cases h
      | error es' =>
        rw [hb] at h; cases h
        have hes := Keel.Validator.both_error _ _ _ _ hb
        intro e he
        rw [hes, List.mem_append] at he
        rcases he with he | he
        · split at he
          · rename_i es'' hd; exact field_errs es'' hd e he
          · simp at he
        · split at he
          · rename_i es'' hf; exact extra_errs rfl es'' hf e he
          · simp at he
    | json =>
      rw [hm] at h
      cases hb : Keel.Validator.both (forbidExtras cfg F) (F.decode cfg (.obj ⟨kvs⟩)) kvs with
      | ok p => rw [hb] at h; cases h
      | error es' =>
        rw [hb] at h; cases h
        have hes := Keel.Validator.both_error _ _ _ _ hb
        intro e he
        rw [hes, List.mem_append] at he
        rcases he with he | he
        · split at he
          · rename_i es'' hf; exact extra_errs rfl es'' hf e he
          · simp at he
        · split at he
          · rename_i es'' hd; exact field_errs es'' hd e he
          · simp at he
  | ignore | allow =>
    simp only [validate] at h
    cases hd : F.decode cfg (.obj ⟨kvs⟩) kvs with
    | ok b => rw [hd] at h; cases h
    | error es' =>
      rw [hd] at h
      simp only [Except.map, Except.error.injEq] at h
      subst h
      exact field_errs _ hd

theorem dictInsert_key {γ : Type} (k : String) (v : γ) :
    ∀ (acc : List (String × γ)) (p : String × γ), p ∈ dictInsert k v acc → p.1 = k ∨ p.1 ∈ acc.map Prod.fst
  | [], p, h => by simp [dictInsert] at h; exact Or.inl (by rw [h])
  | (k', v') :: acc, p, h => by
    simp only [dictInsert] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_map_of_mem (List.mem_cons_of_mem _ h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (by simp)
      · rcases dictInsert_key k v acc p h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)

theorem dedup_key {γ : Type} :
    ∀ (l acc : List (String × γ)) (p : String × γ),
      p ∈ l.foldl (fun acc kv => dictInsert kv.1 kv.2 acc) acc → p.1 ∈ acc.map Prod.fst ∨ p.1 ∈ l.map Prod.fst
  | [], acc, p, h => Or.inl (List.mem_map_of_mem h)
  | kv :: l, acc, p, h => by
    rcases dedup_key l _ p h with h | h
    · obtain ⟨q, hq, he⟩ := List.mem_map.1 h
      rcases dictInsert_key kv.1 kv.2 acc q hq with h' | h'
      · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inl (he ▸ h'))
      · exact Or.inl (he ▸ h')
    · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)

theorem dictInsert_has {γ : Type} (k : String) (v : γ) :
    ∀ acc : List (String × γ), k ∈ (dictInsert k v acc).map Prod.fst
  | [] => by simp [dictInsert]
  | (k', v') :: acc => by
    simp only [dictInsert]
    split
    · simp
    · simp only [List.map_cons, List.mem_cons]; exact Or.inr (dictInsert_has k v acc)

theorem dictInsert_keeps {γ : Type} (k : String) (v : γ) {k' : String} :
    ∀ acc : List (String × γ), k' ∈ acc.map Prod.fst → k' ∈ (dictInsert k v acc).map Prod.fst
  | [], h => by simp at h
  | (k'', v') :: acc, h => by
    simp only [dictInsert]
    simp only [List.map_cons, List.mem_cons] at h
    split
    · rename_i he
      simp only [List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inl (h.trans he)
      · exact Or.inr h
    · simp only [List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (dictInsert_keeps k v acc h)

theorem foldl_dictInsert_keys {γ : Type} {k : String} :
    ∀ (l acc : List (String × γ)), (k ∈ acc.map Prod.fst ∨ k ∈ l.map Prod.fst) →
      k ∈ (l.foldl (fun acc kv => dictInsert kv.1 kv.2 acc) acc).map Prod.fst
  | [], acc, h => by simpa using h
  | kv :: l, acc, h => by
    apply foldl_dictInsert_keys l
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inl (dictInsert_keeps _ _ acc h)
    · exact Or.inl (h ▸ dictInsert_has _ _ acc)
    · exact Or.inr h

/-- A Python `dict` built from pairs keeps every key. -/
theorem mem_dedup_keys {γ : Type} {k : String} {l : List (String × γ)} (h : k ∈ l.map Prod.fst) :
    k ∈ (dedup l).map Prod.fst :=
  foldl_dictInsert_keys l [] (Or.inr h)

/-- In a zip whose first list has no duplicates, the first component fixes
the pair. -/
theorem zip_fst_inj {γ δ : Type} : ∀ {as : List γ} {bs : List δ} {q q' : γ × δ}, as.Nodup →
    q ∈ as.zip bs → q' ∈ as.zip bs → q.1 = q'.1 → q = q'
  | [], _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | a :: as, b :: bs, q, q', hn, hq, hq', he => by
    rw [List.zip_cons_cons] at hq hq'
    obtain ⟨ha, hn⟩ := List.nodup_cons.1 hn
    rcases List.mem_cons.1 hq with rfl | hq <;> rcases List.mem_cons.1 hq' with rfl | hq'
    · rfl
    · have := (List.of_mem_zip hq').1
      simp only at he; rw [← he] at this; exact absurd this ha
    · have := (List.of_mem_zip hq).1
      simp only at he; rw [he] at this; exact absurd this ha
    · exact zip_fst_inj hn hq hq' he

/-- **A field counts as set exactly when its name is in `fieldsSet`**
(pydantic's `model_fields_set`). -/
theorem mem_fieldsSet_iff {F : Fields β} (hl : F.Lawful) (extra : Extra) (src : Option Json) (mode : InputMode)
    {q : String × String} (hq : q ∈ F.names.zip F.keys) :
    q.1 ∈ F.fieldsSet extra src mode ↔ q ∈ F.setFields src (F.extraKeys extra src mode) := by
  constructor
  · intro h
    simp only [fieldsSet, List.mem_append, List.mem_filter] at h
    rcases h with h | ⟨h, -⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.1 h
      rw [zip_fst_inj hl.names_nodup hq (hl.setFields_sub _ _ q' hq') he.symm]
      exact hq'
    · exact hl.names_set _ _ q hq h
  · intro h
    exact List.mem_append_left _ (List.mem_map_of_mem h)

/-- An extra a dump writes is one of the input's extras' keys. -/
theorem extraDump_key (F : Fields β) (o : DumpOpts) :
    ∀ p ∈ F.extraDump o, p.1 ∈ F.extraKeys .allow o.set_from o.set_mode := by
  intro p hp
  unfold extraDump at hp
  unfold extraKeys
  split at hp
  · rename_i kvs hs
    simp only [↓reduceIte]
    exact List.mem_map_of_mem (List.mem_filter.1 hp).1
  · simp at hp

theorem dump_roundTrip (extra : Extra) (F : Fields β) (into : α → β) (a : α) :
    dump extra F into DumpOpts.roundTrip a = .obj ⟨F.encode DumpOpts.roundTrip (into a)⟩ := by
  have : F.extraKeys extra DumpOpts.roundTrip.set_from DumpOpts.roundTrip.set_mode = [] := by
    unfold extraKeys; split <;> rfl
  simp only [dump, this]
  simp [extraDump, DumpOpts.roundTrip]

end Fields

end LeanPydantic
