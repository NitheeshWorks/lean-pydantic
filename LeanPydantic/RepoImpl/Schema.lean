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
      | .minLength _ | .maxLength _ | .pattern _ => true
      | k => nonFinite k n
  | .minLength k, .str s => decide (k ≤ s.length)
  | .maxLength k, .str s => decide (s.length ≤ k)
  | .pattern p, .str s => p.test s
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
  LeanJson.Json.dedupKeys kvs

namespace JsonKind
def isBool : Json → Bool | .bool _ => true | _ => false
def isNum : Json → Bool | .num _ => true | _ => false
def isStr : Json → Bool | .str _ => true | _ => false
def isIntegral : Json → Bool | .num n => Num.isIntegral n | _ => false
end JsonKind

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
  | .anyOf alts => [("anyOf", .arr (toJsonList alts))]
  | .object title props required =>
    [("properties", .obj (toJsonProps props))] ++
    (if required = [] then [] else [("required", .arr (required.map .str))]) ++
    [("title", .str title), ("type", .str "object")]
  | .annotated s title default =>
    members s ++ (match default with | some d => [("default", d)] | none => []) ++
      (match title with | some t => [("title", .str t)] | none => [])

/-- The schema as pydantic prints it. -/
def toJson (s : Schema) : Json := .obj (sortKeys (lastWins (members s)))

def toJsonList : List Schema → List Json
  | [] => []
  | s :: ss => toJson s :: toJsonList ss

def toJsonProps : List (String × Schema) → List (String × Json)
  | [] => []
  | (k, s) :: ps => (k, toJson s) :: toJsonProps ps
end

mutual
/-- Whether `j` is valid under the schema. -/
def check : Schema → Json → Bool
  | .any, _ => true
  | .null, j => isNull j
  | .boolean, j => JsonKind.isBool j
  | .integer kws, j => JsonKind.isIntegral j && kws.all (·.check j)
  | .number kws, j => JsonKind.isNum j && kws.all (·.check j)
  | .string kws, j => JsonKind.isStr j && kws.all (·.check j)
  | .anyOf alts, j => checkAny alts j
  | .object _ props required, j =>
    match j with
    | .obj kvs => checkProps props kvs && required.all (fun r => (LeanJson.Json.lookupLast r kvs).isSome)
    | _ => false
  | .annotated s _ _, j => check s j

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
