import LeanPydantic.RepoImpl.PyDecimal

/-!
# RepoImpl: Python's `repr` and `str(ValidationError)`

What `print` shows in pydantic's docs:

* `repr(m)` of a model, `Item(name='x', price=1.0)`, and `str(m)`,
  `name='x' price=1.0` (pydantic's `__repr_str__`). `PyRepr α` is the `repr`
  of a value of `α`; the model instances are in `APIs/Model.lean`.
* `str(e)` of a `ValidationError`, pydantic-core's `ValidationError.display`:

  ```
  1 validation error for Item
  price
    Input should be a valid number [type=float_type, input_value=[], input_type=list]
      For further information visit https://errors.pydantic.dev/2.14/v/float_type
  ```

  The input is shown as its Python `repr`, cut to 50 bytes
  (`write_truncated_to_limited_bytes`), with its Python type's name.

A JSON input is a Python value of type `dict`, `list`, `str`, `int`,
`float`, `bool` or `NoneType` (what `json.loads` and jiter build), so
`pyReprJson` is the `repr` of that value. A float is written as Python's
`float.__repr__` writes it: the shortest digits that read back, fixed for a
decimal exponent in `[-4, 16)` (`1000.0`, `0.0001`), else `1e+16`, `1.5e-05`.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)

/-! ## A line error's input: its type and its cut `repr` (`pyReprJson` is in `Choice.lean`) -/

/-- The name of the Python type of the value a JSON value stands for. -/
def pyTypeName : Json → String
  | .null => "NoneType"
  | .bool _ => "bool"
  | .num (.int _) => "int"
  | .num _ => "float"
  | .str _ => "str"
  | .arr _ => "list"
  | .obj _ => "dict"

/-- pydantic-core's `write_truncated_to_limited_bytes s 50`: a text longer
than 50 bytes keeps its first 25 bytes and its last 24 (each cut moved to a
character boundary, inward), joined by `...`. -/
def truncateRepr (s : String) (maxLen : Nat := 50) : String :=
  if s.utf8ByteSize ≤ maxLen then s else
  let mid := (maxLen + 1) / 2
  let fits (k : Nat) (cs : List Char) : List Char :=
    (cs.foldl (fun (acc : List Char × Nat × Bool) c =>
      let (out, n, open_) := acc
      if open_ ∧ n + c.utf8Size ≤ k then (c :: out, n + c.utf8Size, true) else (out, n, false))
      ([], 0, true)).1.reverse
  let head := fits mid s.toList
  let tail := (fits (mid - 1) s.toList.reverse).reverse
  String.ofList head ++ "..." ++ String.ofList tail

/-! ## `repr` of values -/

/-- Python's `repr` of a value of `α`, as `print` shows it inside a
container or a model. `reprIn src mode a` is the `repr` of `a` validated from
the input `src` (in `mode`), when known: a model under `extra='allow'` shows
its input's extras, as a pydantic instance keeps them. -/
class PyRepr (α : Type) where
  reprIn : Option Json → InputMode → α → String

/-- Python's `repr(a)`. -/
def pyRepr {α : Type} [PyRepr α] (a : α) : String := PyRepr.reprIn none .python a

/-- The item at index `i` of an array input. -/
def itemAt (src : Option Json) (i : Nat) : Option Json :=
  match src with
  | some (.arr ⟨xs⟩) => xs[i]?
  | _ => none

/-- Any other type: the `repr` of its dump (without serializers, keeping
`inf` and `nan`). That is the Python value for scalars, `Option`, literals
and every type whose Python value is its dump. -/
instance (priority := 50) pyReprOfToJson {α : Type} [ToJson α] : PyRepr α :=
  ⟨fun _ _ a => pyReprJson (toJson { serializers := false, ser_json_inf_nan := .constants } a)⟩

instance {α : Type} [PyRepr α] : PyRepr (Option α) :=
  ⟨fun src m => fun | none => "None" | some a => PyRepr.reprIn src m a⟩

instance {α : Type} [PyRepr α] : PyRepr (List α) :=
  ⟨fun src m xs => "[" ++ ", ".intercalate (xs.zipIdx.map fun (x, i) => PyRepr.reprIn (itemAt src i) m x) ++ "]"⟩

instance {α : Type} [PyRepr α] : PyRepr (Dict α) :=
  ⟨fun src m d => "{" ++ ", ".intercalate (d.entries.map fun (k, v) =>
    pyStrRepr k ++ ": " ++ PyRepr.reprIn (Fields.setMember src k) m v) ++ "}"⟩

/-- `{1, 3}`, or `set()`; in input order (Python: hash order). -/
instance {α : Type} [PyRepr α] : PyRepr (PySet α) :=
  ⟨fun _ _ s => if s.elems.isEmpty then "set()" else "{" ++ ", ".intercalate (s.elems.map pyRepr) ++ "}"⟩

instance {α : Type} (p : α → Prop) [PyRepr α] : PyRepr {x : α // p x} := ⟨fun src m x => PyRepr.reprIn src m x.val⟩

instance {α β : Type} [PyRepr α] [PyRepr β] : PyRepr (α ⊕ β) :=
  ⟨fun src m => fun | .inl a => PyRepr.reprIn src m a | .inr b => PyRepr.reprIn src m b⟩

/-- The items of a tuple from index `i`: right-nested `×` is one flat tuple. -/
class PyReprItems (τ : Type) where
  items : Option Json → InputMode → Nat → τ → List String

instance (priority := low) {α : Type} [PyRepr α] : PyReprItems α :=
  ⟨fun src m i a => [PyRepr.reprIn (itemAt src i) m a]⟩
instance {α β : Type} [PyRepr α] [PyReprItems β] : PyReprItems (α × β) :=
  ⟨fun src m i p => PyRepr.reprIn (itemAt src i) m p.1 :: PyReprItems.items src m (i + 1) p.2⟩

instance {α β : Type} [PyRepr α] [PyReprItems β] : PyRepr (α × β) :=
  ⟨fun src m p => "(" ++ ", ".intercalate (PyReprItems.items src m 0 p) ++ ")"⟩

/-- `<Color.red: 'red'>`. -/
instance (priority := 75) {α : Type} [e : Enumeration α] : PyRepr α :=
  ⟨fun _ _ a => "<" ++ e.title ++ "." ++ e.value a ++ ": " ++ pyStrRepr (e.value a) ++ ">"⟩

instance : PyRepr PyDecimal := ⟨fun _ _ d => "Decimal(" ++ pyStrRepr d.toPy ++ ")"⟩
instance {md dp : Option Nat} : PyRepr (Condecimal md dp) := inferInstanceAs (PyRepr PyDecimal)

instance {α : Type} {f : α → Except String α} [PyRepr α] : PyRepr (After α f) := inferInstanceAs (PyRepr α)
instance {α : Type} {f : Json → Except String Json} [PyRepr α] : PyRepr (Before α f) :=
  inferInstanceAs (PyRepr α)
instance {α : Type} {f : Handler α → Json → Except Raise α} [PyRepr α] : PyRepr (Wrap α f) :=
  inferInstanceAs (PyRepr α)
instance {α : Type} {g : α → Json} [PyRepr α] : PyRepr (Serialize α g) := inferInstanceAs (PyRepr α)
instance {α : Type} {g : (α → Json) → α → Json} [PyRepr α] : PyRepr (WrapSerialize α g) :=
  inferInstanceAs (PyRepr α)

/-! ## `str(ValidationError)` -/

/-- A location as pydantic-core displays it: `items.0.name`, a key with a
dot in backticks. -/
def locDisplay (l : Keel.Loc) : String :=
  ".".intercalate (l.map fun
    | .key k => if k.contains '.' then "`" ++ k ++ "`" else k
    | .index i => toString i)

namespace ErrorDetails

/-- One line error as `str(e)` shows it (pydantic-core's `PyLineError.pretty`). -/
def pretty (e : ErrorDetails) (include_url : Bool := true) : String :=
  (if e.loc.isEmpty then "" else locDisplay e.loc ++ "\n") ++
  "  " ++ e.msg ++ " [type=" ++ e.type ++ ", input_value=" ++ truncateRepr (pyReprJson e.input) ++
  ", input_type=" ++ pyTypeName e.input ++
  (if include_url then "]\n    For further information visit " ++ e.url else "]")

end ErrorDetails

namespace ValidationError

/-- `str(e)`: `N validation error(s) for Title`, then each line error. -/
def str (e : ValidationError) (include_url : Bool := true) : String :=
  let n := e.line_errors.length
  s!"{n} validation error{if n = 1 then "" else "s"} for {e.title}\n" ++
    "\n".intercalate (e.line_errors.map (·.pretty include_url))

/-- `print(e)` shows `str(e)`. -/
instance (priority := high) : ToString ValidationError := ⟨fun e => e.str⟩

end ValidationError

end LeanPydantic
