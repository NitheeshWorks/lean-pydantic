import LeanPydantic.RepoImpl.Error

/-!
# RepoImpl: JSON Schema, printed and checked

`Schema.toJson` prints a schema as pydantic's `model_json_schema()` does:
keys sorted (pydantic's `GenerateJsonSchema.sort`), except the members of
`properties`, which keep field order; a keyword given twice keeps its last
value, as pydantic's merged `Field` metadata does.

`Schema.check s j` decides whether `j` is valid under `s`, by the JSON Schema
meaning of each keyword: numeric keywords constrain only numbers, length and
pattern keywords only strings, `integer` accepts any integral number
(`1.0` included), `properties` constrain the members present (last one wins,
as in pydantic), and `required` keys must be present. `Conforms` is
`check = true`.
-/

namespace LeanPydantic

open LeanJson (Json Number Decimal)
open LeanJson.Json (isNull)

/-- Insert with Python `dict` semantics: an existing key keeps its position
and takes the new value; a new key goes at the end. -/
def dictInsert {β : Type} (k : String) (v : β) : List (String × β) → List (String × β)
  | [] => [(k, v)]
  | (k', v') :: kvs => if k' = k then (k, v) :: kvs else (k', v') :: dictInsert k v kvs

/-- The entries a Python `dict` built from these pairs holds. -/
def dedup {β : Type} (kvs : List (String × β)) : List (String × β) :=
  kvs.foldl (fun acc kv => dictInsert kv.1 kv.2 acc) []

namespace Keyword

/-- The keyword's name and value. -/
def toPair : Keyword → String × Json
  | .exclusiveMinimum n => ("exclusiveMinimum", .num n)
  | .minimum n => ("minimum", .num n)
  | .exclusiveMaximum n => ("exclusiveMaximum", .num n)
  | .maximum n => ("maximum", .num n)
  | .multipleOf n => ("multipleOf", .num n)
  | .minLength n => ("minLength", .num (.int n))
  | .maxLength n => ("maxLength", .num (.int n))
  | .pattern p => ("pattern", .str p.source)
  | .minItems n => ("minItems", .num (.int n))
  | .maxItems n => ("maxItems", .num (.int n))
  | .uniqueItems => ("uniqueItems", .bool true)

/-- A numeric keyword on a non-finite number, as a JSON Schema validator
comparing IEEE doubles decides it: `inf` exceeds every bound, `-inf` is
below every bound, `NaN` compares false, and neither is a multiple of
anything. -/
def nonFinite : Keyword → Number → Bool
  | .exclusiveMinimum _, .inf | .minimum _, .inf => true
  | .exclusiveMaximum _, .negInf | .maximum _, .negInf => true
  | _, _ => false

/-- Whether `j` satisfies the keyword. -/
def check : Keyword → Json → Bool
  | k, .num n =>
    if n.isFinite then
      match k with
      | .exclusiveMinimum b => decide (Num.lt b n)
      | .minimum b => decide (Num.le b n)
      | .exclusiveMaximum b => decide (Num.lt n b)
      | .maximum b => decide (Num.le n b)
      | .multipleOf b => decide (Num.IsMultiple b n)
      | _ => true
    else match k with
      | .minLength _ | .maxLength _ | .pattern _ | .minItems _ | .maxItems _ | .uniqueItems => true
      | k => nonFinite k n
  | .minLength k, .str s => decide (k ≤ s.length)
  | .maxLength k, .str s => decide (s.length ≤ k)
  | .pattern p, .str s => p.test s
  | .minItems k, .arr ⟨xs⟩ => decide (k ≤ xs.length)
  | .maxItems k, .arr ⟨xs⟩ => decide (xs.length ≤ k)
  | .uniqueItems, .arr ⟨xs⟩ => decide xs.Nodup
  | _, _ => true

end Keyword

/-- Whether a number is integral. -/
def Num.isIntegral : Number → Bool
  | .int _ => true
  | .float d => decide (0 ≤ d.exp)
  | _ => false

/-- Sort members by key, stably (insertion sort; schemas are small). -/
def sortKeys (kvs : List (String × Json)) : List (String × Json) :=
  kvs.foldr (fun kv acc => insert kv acc) []
where
  insert (kv : String × Json) : List (String × Json) → List (String × Json)
    | [] => [kv]
    | x :: xs => if decide (x.1 < kv.1) then x :: insert kv xs else kv :: x :: xs

/-- Members with each key once, keeping its last value. -/
def lastWins (kvs : List (String × Json)) : List (String × Json) :=
  LeanJson.Json.dedupKeysList kvs

namespace JsonKind
def isBool : Json → Bool | .bool _ => true | _ => false
def isNum : Json → Bool | .num _ => true | _ => false
def isStr : Json → Bool | .str _ => true | _ => false
def isIntegral : Json → Bool | .num n => Num.isIntegral n | _ => false
end JsonKind

/-- The JSON type all of a literal's values share, if they share one. -/
def literalType (vs : List Json) : Option String :=
  let ty : Json → Option String
    | .str _ => some "string"
    | .bool _ => some "boolean"
    | .num (.int _) => some "integer"
    | .null => some "null"
    | _ => none
  match vs.map ty with
  | some t :: ts => if ts.all (· = some t) then some t else none
  | _ => none

namespace Schema

mutual
/-- The schema's members, before sorting. -/
def members : Schema → List (String × Json)
  | .any => []
  | .null => [("type", .str "null")]
  | .boolean => [("type", .str "boolean")]
  | .integer kws => kws.map Keyword.toPair ++ [("type", .str "integer")]
  | .number kws => kws.map Keyword.toPair ++ [("type", .str "number")]
  | .string kws => kws.map Keyword.toPair ++ [("type", .str "string")]
  | .array items kws => [("items", toJson items)] ++ kws.map Keyword.toPair ++ [("type", .str "array")]
  | .tuple ps =>
    [("maxItems", .num (.int ps.length)), ("minItems", .num (.int ps.length)),
      ("prefixItems", .arr ⟨toJsonList ps⟩), ("type", .str "array")]
  | .dict v => [("additionalProperties", toJson v), ("type", .str "object")]
  | .literal vs =>
    (match vs with
      | [v] => [("const", v)]
      | _ => [("enum", .arr ⟨vs⟩)]) ++
    (match literalType vs with
      | some t => [("type", .str t)]
      | none => [])
  | .anyOf alts => [("anyOf", .arr ⟨toJsonList alts⟩)]
  | .object title props required =>
    [("properties", .obj ⟨toJsonProps props⟩)] ++
    (if required = [] then [] else [("required", .arr ⟨required.map .str⟩)]) ++
    [("title", .str title), ("type", .str "object")]
  | .ref name _ => [("$ref", .str ("#/$defs/" ++ name))]
  | .annotated s title default =>
    members s ++ (match default with | some d => [("default", d)] | none => []) ++
      (match title with | some t => [("title", .str t)] | none => [])

/-- The schema as pydantic prints it, inside a document (references stay
references). -/
def toJson (s : Schema) : Json := .obj ⟨sortKeys (lastWins (members s))⟩

def toJsonList : List Schema → List Json
  | [] => []
  | s :: ss => toJson s :: toJsonList ss

def toJsonProps : List (String × Schema) → List (String × Json)
  | [] => []
  | (k, s) :: ps => (k, toJson s) :: toJsonProps ps
end

mutual
/-- Every named schema referenced from `s`, outermost first. -/
def defs : Schema → List (String × Schema)
  | .array items _ => defs items
  | .tuple ps => defsList ps
  | .dict v => defs v
  | .anyOf alts => defsList alts
  | .object _ props _ => defsProps props
  | .ref name target => (name, target) :: defs target
  | .annotated s _ _ => defs s
  | _ => []

def defsList : List Schema → List (String × Schema)
  | [] => []
  | s :: ss => defs s ++ defsList ss

def defsProps : List (String × Schema) → List (String × Schema)
  | [] => []
  | (_, s) :: ps => defs s ++ defsProps ps
end

/-- The named schema itself, for a reference; anything else as it is. -/
def unref : Schema → Schema
  | .ref _ target => target
  | s => s

/-- Each name once, first occurrence kept. -/
def dedupDefs (ds : List (String × Schema)) : List (String × Schema) :=
  ds.foldl (fun acc d => if acc.any (·.1 == d.1) then acc else acc ++ [d]) []

/-- A whole JSON Schema document, as `model_json_schema()` and
`TypeAdapter.json_schema()` print it: a top-level reference is replaced by
what it names, and every named schema goes under `$defs`, sorted by name. -/
def document (s : Schema) : Json :=
  let top := s.unref
  let ds := dedupDefs (match s with
    | .ref _ target => defs target
    | _ => defs s)
  let ms := members top ++
    (if ds = [] then [] else [("$defs", .obj ⟨sortKeys (ds.map fun (n, d) => (n, toJson d))⟩)])
  .obj ⟨sortKeys (lastWins ms)⟩

/-- Whether pydantic gives a field of this schema a `title`: not for a
reference to a model or an enumeration, nor for a nullable one
(`field_title_should_be_set`). -/
def wantsTitle : Schema → Bool
  | .ref _ _ => false
  | .anyOf [s, .null] => wantsTitle s
  | _ => true

mutual
/-- Whether `j` is valid under the schema. -/
def check : Schema → Json → Bool
  | .any, _ => true
  | .null, j => isNull j
  | .boolean, j => JsonKind.isBool j
  | .integer kws, j => JsonKind.isIntegral j && kws.all (·.check j)
  | .number kws, j => JsonKind.isNum j && kws.all (·.check j)
  | .string kws, j => JsonKind.isStr j && kws.all (·.check j)
  | .array items kws, j =>
    (match j with
      | .arr ⟨xs⟩ => checkAll items xs
      | _ => false) && kws.all (·.check j)
  | .tuple ps, j =>
    match j with
    | .arr ⟨xs⟩ => checkTuple ps xs
    | _ => false
  | .dict v, j =>
    match j with
    | .obj ⟨kvs⟩ => checkValues v (dedup kvs)
    | _ => false
  | .literal vs, j => decide (j ∈ vs)
  | .anyOf alts, j => checkAny alts j
  | .object _ props required, j =>
    match j with
    | .obj ⟨kvs⟩ => checkProps props kvs && required.all (fun r => (LeanJson.Json.lookupLast r kvs).isSome)
    | _ => false
  | .ref _ target, j => check target j
  | .annotated s _ _, j => check s j

def checkAll (s : Schema) : List Json → Bool
  | [] => true
  | x :: xs => check s x && checkAll s xs

def checkTuple : List Schema → List Json → Bool
  | [], [] => true
  | s :: ss, x :: xs => check s x && checkTuple ss xs
  | _, _ => false

def checkValues (s : Schema) : List (String × Json) → Bool
  | [] => true
  | (_, v) :: kvs => check s v && checkValues s kvs

def checkAny : List Schema → Json → Bool
  | [], _ => false
  | s :: ss, j => check s j || checkAny ss j

def checkProps : List (String × Schema) → List (String × Json) → Bool
  | [], _ => true
  | (k, s) :: ps, kvs =>
    (match LeanJson.Json.lookupLast k kvs with
      | some v => check s v
      | none => true) && checkProps ps kvs
end

end Schema

end LeanPydantic
