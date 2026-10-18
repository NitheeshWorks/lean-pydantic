import LeanPydantic.Proofs.Fields

/-!
# Proofs: lists and dicts inherit the laws of their elements

A list validates as Keel's `each`, so its round trip is `mapM` of the
element's round trip, and strict soundness is "every element conforms". A
dict is the same over its members, after Python `dict` collapsing, which is
the identity on the distinct keys a dump has (`dedup_of_nodup`).
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open Keel (Constraint)

/-! ## `mapM` facts -/

theorem mapM_map_ok {ι α ε : Type} (v : ι → Except ε α) (f : α → ι) (h : ∀ a, v (f a) = .ok a) :
    ∀ xs : List α, (xs.map f).mapM v = .ok xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.mapM_cons, h, mapM_map_ok v f h xs]
    rfl

theorem mapM_ok_mem {ι α ε : Type} (v : ι → Except ε α) :
    ∀ (xs : List ι) (ys : List α), xs.mapM v = .ok ys → ∀ x ∈ xs, ∃ y, v x = .ok y
  | [], _, _, _, hx => nomatch hx
  | x :: xs, ys, h, z, hz => by
    simp only [List.mapM_cons] at h
    cases hv : v x with
    | error e => rw [hv] at h; cases h
    | ok a =>
      rw [hv] at h
      cases hr : xs.mapM v with
      | error e => simp [hr, bind, Except.bind] at h
      | ok as =>
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨a, hv⟩
        · exact mapM_ok_mem v xs as hr z hz

theorem mapM_ok_length {ι α ε : Type} (v : ι → Except ε α) :
    ∀ (xs : List ι) (ys : List α), xs.mapM v = .ok ys → ys.length = xs.length
  | [], ys, h => by cases h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hv : v x with
    | error e => rw [hv] at h; cases h
    | ok a =>
      rw [hv] at h
      cases hr : xs.mapM v with
      | error e => simp [hr, bind, Except.bind] at h
      | ok as =>
        simp [hr, bind, Except.bind, pure, Except.pure] at h
        subst h; simp [mapM_ok_length v xs as hr]

theorem eachFrom_ne_nil {ι α : Type} (v : Keel.Validator ErrorDetails ι α) (hv : ∀ x, v x ≠ .error []) :
    ∀ (i : Nat) (xs : List ι), Keel.Validator.eachFrom v i xs ≠ .error []
  | _, [] => nofun
  | i, x :: xs => by
    have ih := eachFrom_ne_nil v hv (i + 1) xs
    unfold Keel.Validator.eachFrom
    have hat : ∀ e, (v.at (.index i)) x = .error e → e ≠ [] := by
      intro e he
      obtain ⟨e', h', rfl⟩ := (Keel.Validator.at_error_iff _ _ _ _).1 he
      intro hn; exact hv x (by simp_all)
    split <;> simp_all

theorem checkAll_iff (s : Schema) : ∀ xs : List Json, Schema.checkAll s xs = true ↔ ∀ x ∈ xs, s.check x = true
  | [] => by simp [Schema.checkAll]
  | x :: xs => by simp [Schema.checkAll, checkAll_iff s xs]

/-! ## `list[α]` -/

theorem dumpElems_roundTrip {α : Type} [ToJson α] :
    ∀ (i : Nat) (xs : List α), dumpElems DumpOpts.roundTrip i xs = xs.map (toJson DumpOpts.roundTrip)
  | _, [] => rfl
  | i, x :: xs => by
    simp only [dumpElems, List.map_cons, dumpElems_roundTrip (i + 1) xs]
    rfl

theorem fromJson_list_arr {α : Type} [FromJson α] (cfg : Cfg) (xs : List Json) :
    fromJson (α := List α) cfg (.arr ⟨xs⟩) = Keel.Validator.each (fromJson cfg) xs := rfl

theorem fromJson_list_strict {α : Type} [FromJson α] {cfg : Cfg} {j : Json} {ys : List α}
    (h : fromJson cfg j = .ok ys) : ∃ xs, j = .arr ⟨xs⟩ ∧ xs.mapM (fromJson cfg) = .ok ys := by
  cases j with
  | arr a =>
    cases a with
    | mk xs => exact ⟨xs, rfl, (Keel.Validator.each_ok_iff _ _ _).1 h⟩
  | _ => cases h

instance {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] : LawfulJson (List α) where
  fromJson_toJson cfg xs := by
    show fromJson cfg (.arr ⟨dumpElems DumpOpts.roundTrip 0 xs⟩) = _
    rw [fromJson_list_arr, dumpElems_roundTrip, Keel.Validator.each_ok_iff]
    exact mapM_map_ok _ _ (LawfulJson.fromJson_toJson cfg) xs
  schema_sound cfg j ys hs h := by
    obtain ⟨xs, rfl, hm⟩ := fromJson_list_strict h
    show Schema.check (.array _ []) _ = true
    simp only [Schema.check, List.all_nil, Bool.and_true]
    rw [checkAll_iff]
    intro x hx
    obtain ⟨y, hy⟩ := mapM_ok_mem _ xs ys hm x hx
    exact LawfulJson.schema_sound cfg x y hs hy
  errors_ne_nil cfg j := by
    cases j with
    | arr a =>
      cases a
      exact eachFrom_ne_nil _ (LawfulJson.errors_ne_nil cfg) 0 _
    | _ => nofun

instance {α : Type} [ToJson α] : NonNull (List α) := ⟨fun _ _ => nofun⟩

instance {β : Type} [FromJson β] : LawfulConstrained (List β) where
  keywords_sound cfg j ys a hstd _ hv h := by
    obtain ⟨xs, rfl, hm⟩ := fromJson_list_strict hv
    have hl := mapM_ok_length _ xs ys hm
    intro k hk
    unfold constrainedList at hk hstd
    cases a <;> simp only at hk
    case minLength | maxLength =>
      obtain rfl : _ = _ := hstd
      simp only [List.mem_singleton] at hk; subst hk
      simp only [Constraint.holds, Keel.Sized.size] at h
      simp [Keyword.check]
      omega
    all_goals simp at hk

/-! ## `dict[str, α]` -/

theorem dictInsert_fresh {β : Type} (k : String) (v : β) :
    ∀ acc : List (String × β), k ∉ acc.map Prod.fst → dictInsert k v acc = acc ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: acc, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [dictInsert, Ne.symm h.1, dictInsert_fresh k v acc h.2]

theorem foldl_dictInsert {β : Type} :
    ∀ (acc kvs : List (String × β)), ((acc ++ kvs).map Prod.fst).Nodup →
      kvs.foldl (fun a kv => dictInsert kv.1 kv.2 a) acc = acc ++ kvs
  | acc, [], _ => by simp
  | acc, (k, v) :: kvs, h => by
    have hk : k ∉ acc.map Prod.fst := by
      intro hm
      simp only [List.map_append, List.map_cons] at h
      exact (List.nodup_append.1 h).2.2 _ hm _ List.mem_cons_self rfl
    simp only [List.foldl_cons]
    rw [dictInsert_fresh k v acc hk, foldl_dictInsert (acc ++ [(k, v)]) kvs (by simpa using h)]
    simp

/-- Collapsing distinct keys changes nothing. -/
theorem dedup_of_nodup {β : Type} (kvs : List (String × β)) (h : (kvs.map Prod.fst).Nodup) :
    dedup kvs = kvs := by
  unfold dedup; simpa using foldl_dictInsert [] kvs (by simpa using h)

theorem dumpMembers_roundTrip {α : Type} [ToJson α] :
    ∀ kvs : List (String × α),
      dumpMembers DumpOpts.roundTrip kvs = kvs.map fun kv => (kv.1, toJson DumpOpts.roundTrip kv.2) := by
  intro kvs
  simp only [dumpMembers]
  rfl

/-! ### The linear implementation is the specification -/

theorem dictInsert_eq_insertLast (k : String) (v : Json) :
    ∀ l : List (String × Json), dictInsert k v l = Json.insertLast k v l
  | [] => rfl
  | (k', v') :: l => by simp only [dictInsert, Json.insertLast, dictInsert_eq_insertLast k v l]

/-- The hash-indexed collapse is `dedup`. -/
theorem dedupFast_eq (kvs : List (String × Json)) : dedupFast kvs = dedup kvs := dedupIdx_eq kvs

theorem validateMembersGo_eq {α : Type} [FromJson α] (cfg : Cfg) :
    ∀ (kvs : List (String × Json)) (oks : List (String × α)) (errs : List (List ErrorDetails))
      (failed : Bool),
      validateMembersGo cfg kvs oks errs failed =
        match validateMembers cfg kvs with
        | .ok as => if failed then .error errs.reverse.flatten else .ok (oks.reverse ++ as)
        | .error e => .error (errs.reverse.flatten ++ e)
  | [], oks, errs, failed => by cases failed <;> simp [validateMembersGo, validateMembers]
  | (k, v) :: kvs, oks, errs, failed => by
    rw [validateMembersGo, validateMembers]
    cases ha : Keel.Validator.at (.key k) (fromJson (α := α) cfg) v <;>
      cases hr : validateMembers (α := α) cfg kvs <;> cases failed <;>
      simp [validateMembersGo_eq cfg kvs, hr]

/-- The tail loop is `validateMembers`. -/
theorem validateMembersFast_eq {α : Type} [FromJson α] (cfg : Cfg) (kvs : List (String × Json)) :
    validateMembersFast (α := α) cfg kvs = validateMembers cfg kvs := by
  rw [validateMembersFast, validateMembersGo_eq]
  cases validateMembers (α := α) cfg kvs <;> simp

/-- A dict validates as `validateMembers` on the collapsed members says. -/
theorem fromJson_dict_obj {α : Type} [FromJson α] (cfg : Cfg) (kvs : List (String × Json)) :
    fromJson (α := Dict α) cfg (.obj ⟨kvs⟩) = (validateMembers cfg (dedup kvs)).map Dict.ofEntries := by
  show (validateMembersFast cfg (dedupFast kvs)).map Dict.ofEntries = _
  rw [validateMembersFast_eq, dedupFast_eq]

theorem validateMembers_dump {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] (cfg : Cfg) :
    ∀ kvs : List (String × α),
      validateMembers cfg (kvs.map fun kv => (kv.1, toJson DumpOpts.roundTrip kv.2)) = .ok kvs
  | [] => rfl
  | (k, v) :: kvs => by
    simp only [List.map_cons, validateMembers]
    rw [show (Keel.Validator.at (.key k) (fromJson (α := α) cfg)) (toJson DumpOpts.roundTrip v) = .ok v from
      (Keel.Validator.at_ok_iff _ _ _ _).2 (LawfulJson.fromJson_toJson cfg v), validateMembers_dump cfg kvs]

theorem validateMembers_ok {α : Type} [FromJson α] (cfg : Cfg) :
    ∀ (kvs : List (String × Json)) (as : List (String × α)), validateMembers cfg kvs = .ok as →
      ∀ kv ∈ kvs, ∃ a, fromJson (α := α) cfg kv.2 = .ok a
  | [], _, _, _, h => nomatch h
  | (k, v) :: kvs, as, h, kv, hkv => by
    unfold validateMembers at h
    split at h
    · rename_i a as' ha hr
      rcases List.mem_cons.1 hkv with rfl | hkv
      · exact ⟨a, (Keel.Validator.at_ok_iff _ _ _ _).1 ha⟩
      · exact validateMembers_ok cfg kvs as' hr kv hkv
    all_goals cases h

theorem validateMembers_ne_nil {α : Type} [FromJson α] (cfg : Cfg)
    (hv : ∀ j, fromJson (α := α) cfg j ≠ .error []) :
    ∀ kvs : List (String × Json), validateMembers (α := α) cfg kvs ≠ .error []
  | [] => nofun
  | (k, v) :: kvs => by
    have ih := validateMembers_ne_nil cfg hv kvs
    unfold validateMembers
    have hat : ∀ e, (Keel.Validator.at (.key k) (fromJson (α := α) cfg)) v = .error e → e ≠ [] := by
      intro e he
      obtain ⟨e', h', rfl⟩ := (Keel.Validator.at_error_iff _ _ _ _).1 he
      intro hn; exact hv v (by simp_all)
    split <;> simp_all

theorem checkValues_iff (s : Schema) :
    ∀ kvs : List (String × Json), Schema.checkValues s kvs = true ↔ ∀ kv ∈ kvs, s.check kv.2 = true
  | [] => by simp [Schema.checkValues]
  | (k, v) :: kvs => by simp [Schema.checkValues, checkValues_iff s kvs]

instance {α : Type} [FromJson α] [ToJson α] [JsonSchema α] [LawfulJson α] : LawfulJson (Dict α) where
  fromJson_toJson cfg d := by
    obtain ⟨kvs, hn⟩ := d
    show fromJson cfg (.obj ⟨dumpMembers DumpOpts.roundTrip kvs⟩) = _
    rw [fromJson_dict_obj, dumpMembers_roundTrip, dedup_of_nodup _ (by simpa [Function.comp_def] using hn),
      validateMembers_dump]
    simp [Except.map, Dict.ofEntries, (nodupFast_iff _).2 hn]
  schema_sound cfg j d hs h := by
    cases j with
    | obj a =>
      cases a with
      | mk kvs =>
        show Schema.check (.dict _) _ = true
        simp only [Schema.check]
        rw [fromJson_dict_obj] at h
        cases hm : validateMembers (α := α) cfg (dedup kvs) with
        | error e => rw [hm] at h; cases h
        | ok as =>
          rw [checkValues_iff]
          intro kv hkv
          obtain ⟨a, ha⟩ := validateMembers_ok cfg _ as hm kv hkv
          exact LawfulJson.schema_sound cfg kv.2 a hs ha
    | _ => cases h
  errors_ne_nil cfg j := by
    cases j with
    | obj a =>
      cases a with
      | mk kvs =>
        rw [fromJson_dict_obj]
        have := validateMembers_ne_nil (α := α) cfg (LawfulJson.errors_ne_nil cfg) (dedup kvs)
        cases hm : validateMembers (α := α) cfg (dedup kvs) <;> simp_all [Except.map]
    | _ => nofun

instance {α : Type} [ToJson α] : NonNull (Dict α) := ⟨fun _ _ => nofun⟩

end LeanPydantic
