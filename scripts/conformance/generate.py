#!/usr/bin/env python3
"""Generate tests/ConformanceTable.lean by running pydantic on many inputs.

A developer tool, not run in CI (the stack runs no Python in CI). It needs the
released pydantic named in docs/traceability.toml:

  /home/nitheesh/Official/NitheeshWorks/upstream-spec/.venv/bin/python -I \
      scripts/conformance/generate.py > tests/ConformanceTable.lean

Each row is (upstream test, Lean type tag, mode, strict, input JSON text,
pydantic's output). The output is `dump_json` of the result, or the
`ValidationError.json()` of the failure, byte for byte. Rows whose Python-mode
input `json.loads` would change (huge or over-precise floats) are not
generated.
"""
import json, sys
from decimal import Decimal
from enum import Enum
from typing import Annotated, Literal, Optional, Union
from pydantic import BaseModel, Field, FiniteFloat, NonNegativeInt, TypeAdapter, ValidationError, constr

class Item(BaseModel):
    name: str
    description: Optional[str] = None
    price: FiniteFloat
    tax: Optional[FiniteFloat] = None

class Offer(BaseModel):
    price: Annotated[FiniteFloat, Field(gt=0)]
    discount: Annotated[NonNegativeInt, Field(le=100)] = 0
    q: Optional[Annotated[str, Field(max_length=50, min_length=3)]] = None
    item_id: int
    ok: bool = True

class Image(BaseModel):
    url: str
    name: str

class Shop(BaseModel):
    name: str
    tags: list[str] = []
    image: Optional[Image] = None
    images: list[Image]
    item_id: int = Field(alias='itemId')
    sizes: Annotated[list[int], Field(min_length=1, max_length=2)]
    stock: dict[str, int] = {}

class Color(str, Enum):
    red = 'red'
    green = 'green'

class Im(BaseModel):
    url: str

class E2(BaseModel):
    c: Color
    l: Literal['a', 'b'] = 'a'
    one: Literal['x']
    u: Union[int, str]
    t: tuple[int, str]
    d: dict[str, int]

TYPES = {
    'int': int,
    'nat': NonNegativeInt,
    'float': FiniteFloat,
    'bool': bool,
    'str': str,
    'opt_int': Optional[int],
    'opt_str': Optional[str],
    'int_gt0_le100': Annotated[int, Field(gt=0, le=100)],
    'int_mult3': Annotated[int, Field(multiple_of=3, ge=-10, lt=50)],
    'str_3_5': Annotated[str, Field(min_length=3, max_length=5)],
    'str_1_1': Annotated[str, Field(min_length=1, max_length=1)],
    'float_gt0_le2_5_mult0_5': Annotated[FiniteFloat, Field(gt=0, le=2.5, multiple_of=0.5)],
    'nat_le10': Annotated[NonNegativeInt, Field(le=10)],
    'item': Item,
    'offer': Offer,
    'list_int': list[int],
    'list_str_1_2': Annotated[list[str], Field(min_length=1, max_length=2)],
    'dict_int': dict[str, int],
    'opt_list_int': Optional[list[int]],
    'list_item': list[Item],
    'image': Image,
    'shop': Shop,
    'color': Color,
    'e2': E2,
    'literal_ab': Literal['a', 'b'],
    'literal_quote': Literal["b'c", 'd"e', 'x'],
    'literal_int': Literal[1, 2],
    'union_int_str': Union[int, str],
    'union_str_int': Union[str, int],
    'union_float_int': Union[FiniteFloat, int],
    'union_int_float': Union[int, FiniteFloat],
    'union_mixed': Union[Annotated[int, Field(gt=0)], list[int], Im, str],
    'opt_union': Optional[Union[int, str]],
    'tuple_isb': tuple[int, str, bool],
    'tuple_is': tuple[int, str],
    'decimal': Decimal,
    'plain_float': float,
    'float_gt0': Annotated[float, Field(gt=0)],
    'condecimal_5_2': Annotated[Decimal, Field(max_digits=5, decimal_places=2)],
    'condecimal_gt0_3': Annotated[Decimal, Field(gt=0, max_digits=3)],
    'condecimal_places1_mult': Annotated[Decimal, Field(decimal_places=1, multiple_of=Decimal('0.5'), le=10)],
}

PC = 'pydantic-core/tests/validators/'
INT_IN = ['0', '1', '-1', '42', '"42"', '" 42 "', '"+5"', '"-0"', '"01"', '"09"', '"00_"', '"0:"',
    '"+4_2"', '"+0_42"', '"+4_2.0"', '"+04_2.0"', '"++4_2"', '"-+1"', '"+-1"', '"--0001"', '"-+0001"',
    '"-0-001"', '"-0+001"', '"-00001"', '"-00042_000"', '"4_2"', '"0_42"', '"4_2.0"', '"04_2.0"',
    '"  04_2.0 "', '"  0_42.0 "', '"  _042.0 "', '"42_"', '"42_.0"', '"000001"', '"123456789.0"', '" "',
    '"1."', '"42."', '"123456789123456.00001"', '10000000000', '9223372036854775807',
    '9223372036854775808', '18446744073709551614', '12.5', '"wrong"', 'null', '[1, 2]', '{}', 'true',
    'false', '1.0', '-0.0', '1e3', '"1e3"', '"1.5"', '"0x10"', '""', '"12a"', '"0-5"', '"00-7"',
    '"1_000"', '"1__0"', '"_1"', '"1_"', '9.2e18', '9.3e18', '1e19', 'NaN', 'Infinity', '-Infinity',
    '"\\u20021\\u2002"', '"9' + '9' * 4300 + '"']
FLOAT_IN = ['0', '1', '-1', '1.5', '-2.25', '"1.5"', '" 1.5 "', '"1e3"', '"1_0"', '"1_000.5"', 'true',
    'false', '"abc"', 'null', '"-0"', '"inf"', '"nan"', '"-inf"', '"Infinity"', 'NaN', 'Infinity',
    '-Infinity', '[]', '{}', '"1."', '".5"', '"+.5"', '"e5"', '"."', '"1e"', '"1e+5"', '0.1', '100.0',
    '1e20', '1e-7', '"1_"', '" 1_0"']
BOOL_IN = ['true', 'false', '"true"', '"True"', '"TRUE"', '"yes"', '"on"', '"1"', '"0"', '"f"', '"n"',
    '"off"', '" true"', '1', '0', '2', '-1', '1.0', '0.0', '1.5', '2.0', 'null', '"t"', '"y"', '"no"',
    '"false"', '"maybe"', '[]', '9223372036854775808', 'NaN']
STR_IN = ['""', '"x"', '"hello"', '1', '1.5', 'true', 'null', '[]', '{}', '"caf\\u00e9"', '"\\ud83d\\ude00"']
OPT_IN = ['null', '1', '"x"', '1.5', 'true', '[]']
CON_INT_IN = ['0', '1', '50', '100', '101', '-1', '"7"', '7', '9', '-12', '-9', '48', '51', '1.5', '"x"']
CON_STR_IN = ['""', '"ab"', '"abc"', '"abcde"', '"abcdef"', '"a"', '"\\u00e9\\u00e9\\u00e9"', '"\\ud83d\\ude00"', '5']
CON_FLOAT_IN = ['0', '0.5', '0.7', '1', '2.5', '3', '2.75', '-1', '"1.5"', 'NaN', '0.25']
NAT_IN = ['0', '5', '10', '11', '-1', '"3"', '1.0', '-0.5']
ITEM_IN = ['{"price": -1}', '5', '[]', '"x"', 'null', '{"name": 1, "price": "abc"}',
    '{"name": "x", "price": "1.5"}', '{"name": "Foo", "price": 50.5}',
    '{"name": "Foo", "description": "A very nice Item", "price": 35.4, "tax": 3.2}',
    '{"name": "x", "price": 1, "tax": null}', '{"name": "x", "price": 1, "extra": [1, 2]}',
    '{"name": "x", "name": "y", "price": 2}', '{"name": null, "price": null}', '{}',
    '{"name": "x", "price": NaN}', '{"name": "x", "price": 1, "description": 7}']
OFFER_IN = ['{"price": 0, "discount": 101, "q": "ab", "item_id": "x1", "ok": "maybe"}',
    '{"price": 1, "discount": 1.5, "item_id": 1.0, "q": 5}', '{"price": 1, "item_id": true, "discount": "1.0"}',
    '{"price": 2.5, "item_id": 3}', '{"price": -1, "item_id": 3, "discount": -1}', '{"item_id": 1}',
    '{"price": 1, "item_id": 1, "q": "abcd", "ok": "yes"}', '{"price": 1, "item_id": 1, "q": null}',
    '7', '{"price": "inf", "item_id": 1}']

LIST_IN = ['[]', '[1, 2, 3]', '["1", " 2 "]', '[1, "x", 2.5, null]', '"ab"', '{}', 'null', '5', '[[1]]', '[true]']
LIST_STR_IN = ['[]', '["a"]', '["a", "b"]', '["a", "b", "c"]', '[1]', '"a"']
DICT_IN = ['{}', '{"a": 1, "b": "2"}', '{"a": "x", "b": 1.5, "c": 3}', '[]', '"x"', 'null', '{"a": 1, "a": 2}']
OPT_LIST_IN = ['null', '[1]', '["x"]', '1']
LIST_ITEM_IN = ['[]', '[{"name": "a", "price": 1}]', '[{"name": "a"}, 5, {"price": "x"}]', '{}']
IMAGE_IN = ['{"url": "u", "name": "n"}', '{"url": 1}', '[]']
SHOP_IN = ['{"name":"x","images":[{"url":1},{"name":"a","url":"u"},5],"itemId":"z","sizes":[],"tags":"ab","image":[]}',
    '{"name":"x","images":{},"item_id":3,"sizes":[1,2,3]}', '{"name":"x","images":[],"itemId":3,"sizes":["a",2.5]}',
    '{"name":"x","images":[],"itemId":3,"sizes":[1]}',
    '{"name":"x","images":[{"url":"u","name":"n"}],"itemId":"7","sizes":[1,2],"image":{"url":"a","name":"b"},"stock":{"a":1}}',
    '{"name":"x","images":[],"itemId":3,"sizes":[1],"image":null,"stock":{"a":"x","b":[]}}',
    '{"name":"x","images":[],"itemId":3,"sizes":[1],"tags":["t", 1, null]}']

ROWS = [
    ('int', INT_IN, PC + 'test_int.py::test_int_py_and_json'),
    ('nat', NAT_IN, 'pydantic/tests/test_types.py::test_strict_raw_type'),
    ('float', FLOAT_IN, PC + 'test_float.py::test_non_finite_json_values'),
    ('bool', BOOL_IN, PC + 'test_bool.py::test_bool'),
    ('str', STR_IN, PC + 'test_string.py::test_str'),
    ('opt_int', OPT_IN, PC + 'test_nullable.py::test_nullable'),
    ('opt_str', OPT_IN, PC + 'test_nullable.py::test_nullable'),
    ('int_gt0_le100', CON_INT_IN, PC + 'test_int.py::test_int_kwargs'),
    ('int_mult3', CON_INT_IN, PC + 'test_int.py::test_int_kwargs'),
    ('str_3_5', CON_STR_IN, PC + 'test_string.py::test_constrained_str'),
    ('str_1_1', CON_STR_IN, PC + 'test_string.py::test_constrained_str'),
    ('float_gt0_le2_5_mult0_5', CON_FLOAT_IN, PC + 'test_float.py::test_float_kwargs'),
    ('nat_le10', NAT_IN, 'pydantic/tests/test_types.py::test_constraints_arbitrary_type'),
    ('item', ITEM_IN, 'pydantic/tests/test_main.py::test_ultra_simple_failed'),
    ('offer', OFFER_IN, 'pydantic/tests/test_main.py::test_default_factory_field'),
    ('list_int', LIST_IN, PC + 'test_list.py::test_list_py_or_json'),
    ('list_str_1_2', LIST_STR_IN, PC + 'test_list.py::test_list_length_constraints'),
    ('dict_int', DICT_IN, PC + 'test_dict.py::test_dict'),
    ('opt_list_int', OPT_LIST_IN, PC + 'test_nullable.py::test_nullable'),
    ('list_item', LIST_ITEM_IN, 'pydantic/tests/test_main.py::test_nested_model'),
    ('image', IMAGE_IN, 'pydantic/tests/test_main.py::test_nested_model'),
    ('shop', SHOP_IN, 'pydantic/tests/test_aliases.py::test_alias_error'),
]
CHOICE_IN = ['"5"', '5', '5.0', '5.5', '[]', 'true', 'null', '{"url": 1}', '-5', '[1, "x"]', '{"url": "u"}', '"z"', '"a"', '1', '3']
TUPLE_IN = ['[1, "a"]', '[1, "a", true]', '[1,"a",true,4]', '["x", 2, "q"]', '{}', '[]', '[1]', '"ab"']
COLOR_IN = ['"red"', '"green"', '"blue"', '1', 'null', '"Red"']
E2_IN = ['{"c":"blue","l":"c","one":"y","u":[],"t":[1],"d":{"a":"x"}}', '{"c":"red","one":"x","u":"5","t":[1,"a",3],"d":[]}',
    '{"c":"green","one":"x","u":5,"t":[1,"a"],"d":{"k":1},"l":"b"}', '{"c":"red","one":"x","u":true,"t":["1","a"],"d":{}}']
ROWS += [
    ('color', COLOR_IN, PC + 'test_enums.py::test_plain_enum'),
    ('e2', E2_IN, 'pydantic/tests/test_main.py::test_enum_values'),
    ('literal_ab', CHOICE_IN, PC + 'test_literal.py::test_literal_py_and_json'),
    ('literal_quote', ['"b\'c"', '"q"', '1'], PC + 'test_literal.py::test_literal_py_and_json'),
    ('literal_int', CHOICE_IN, PC + 'test_literal.py::test_literal_py_and_json'),
    ('union_int_str', CHOICE_IN, PC + 'test_union.py::test_union_bool_int'),
    ('union_str_int', CHOICE_IN, PC + 'test_union.py::test_union_bool_int'),
    ('union_float_int', CHOICE_IN, PC + 'test_union.py::test_int_float'),
    ('union_int_float', CHOICE_IN, PC + 'test_union.py::test_int_float'),
    ('union_mixed', CHOICE_IN, PC + 'test_union.py::test_model_a'),
    ('opt_union', CHOICE_IN, PC + 'test_nullable.py::test_union_nullable_bool_int'),
    ('tuple_isb', TUPLE_IN, PC + 'test_tuple.py::test_tuple_json'),
    ('tuple_is', TUPLE_IN, PC + 'test_tuple.py::test_tuple_json'),
]

DECIMAL_IN = ['1.5', '"1.5"', '123.456', '1234.5', '"abc"', '12345.6', '1e3', '0.001', '"NaN"', '"Infinity"',
              '"-inf"', '"snan"', 'true', 'null', '[1]', '"  2.50 "', '100', '1.10', '-0.0', '0.0', '"1_000"', '"1__0"',
              '"_1"', '0.00100', '"1e3"', '"1E-7"', '"-0.000"', '"+5."', '".5"', '"."', '"1e"', '1e-7', '1.5e-5', '1e16',
              '123456789', '-12.5', '"00012.30"', '0.5', '9.5', '10.5', '10', '"7.25"', '"1.2e2"']
FLOAT_PLAIN_IN = ['1.5', '1', '-0.0', '1e400', '-1e400', 'NaN', 'Infinity', '-Infinity', '"nan"', '"NaN"', '"inf"',
                  '"-inf"', '"+Infinity"', '"-infinity"', '"1_0.5"', '" 2.5 "', '"x"', 'true', 'false', 'null', '[1]',
                  '0.1', '1e16', '1e-7', '123456789012345678', '0.30000000000000004', '5e-324', '1.7976931348623157e308']
ROWS += [
    ('plain_float', FLOAT_PLAIN_IN, PC + 'test_float.py::test_float_inf_nan'),
    # an out-of-range literal is reported as written (pydantic: as the float, -Infinity): traceability
    ('float_gt0', [t for t in FLOAT_PLAIN_IN if t != '-1e400'], PC + 'test_float.py::test_float_kwargs'),
]
ROWS += [
    ('decimal', DECIMAL_IN, PC + 'test_decimal.py::test_decimal'),
    ('condecimal_5_2', DECIMAL_IN, PC + 'test_decimal.py::test_decimal_digits'),
    ('condecimal_gt0_3', DECIMAL_IN, PC + 'test_decimal.py::test_decimal_kwargs'),
    ('condecimal_places1_mult', DECIMAL_IN, PC + 'test_decimal.py::test_decimal_multiple_of'),
]

STRICT_ROWS = [
    ('decimal', ['1.5', '"1.5"', '1', 'true'], PC + 'test_decimal.py::test_decimal_strict_py'),
    ('plain_float', ['1.5', '1', '"1.5"', 'true', 'NaN'], PC + 'test_float.py::test_float_strict'),
    ('int', ['1', '"1"', '1.0', 'true', 'null'], PC + 'test_int.py::test_int_strict'),
    ('float', ['1', '1.5', '"1.5"', 'true'], PC + 'test_float.py::test_float_strict'),
    ('bool', ['true', '"true"', '1'], PC + 'test_bool.py::test_bool_strict'),
    ('str', ['"x"', '1'], PC + 'test_string.py::test_str'),
    ('item', ['{"name": "x", "price": 1}', '{"name": "x", "price": "1"}'], 'pydantic/tests/test_main.py::test_model_validate_strict'),
]
PD_DUMP = 'pydantic/tests/test_main.py::test_exclude_unset_dict'
JSON_ONLY = [('item', ['{"name": "x",', '{"name": "x", "price": 1} x', '', '[1,]'],
    'pydantic/tests/test_types.py::test_invalid_model_json'),
    ('int', ['"1', '01', '-'], 'pydantic/tests/test_types.py::test_invalid_simple_json')]

def lean_str(s):
    out = []
    for ch in s:
        if ch == '\\': out.append('\\\\')
        elif ch == '"': out.append('\\"')
        elif ch == '\n': out.append('\\n')
        elif ord(ch) < 0x20 or ord(ch) == 0x7f: out.append('\\u%04x' % ord(ch))
        else: out.append(ch)
    return '"' + ''.join(out) + '"'

def run(tag, mode, strict, text):
    ta = TypeAdapter(TYPES[tag])
    try:
        if mode == 'json':
            r = ta.validate_json(text, strict=strict)
        elif mode == 'python-attrs':
            r = ta.validate_python(json.loads(text), strict=strict, from_attributes=True)
        else:
            r = ta.validate_python(json.loads(text), strict=strict)
        return ta.dump_json(r).decode()
    except ValidationError as e:
        return e.json()

def python_ok(text):
    """json.loads keeps the value as LeanJson does."""
    try:
        v = json.loads(text)
    except Exception:
        return False
    def ok(x):
        if isinstance(x, float):
            return x != x or abs(x) == float('inf') or repr(x) in text or float(repr(x)) == x and len(repr(x)) < 18
        if isinstance(x, list): return all(ok(y) for y in x)
        if isinstance(x, dict): return len(x) == text.count(':') and all(ok(y) for y in x.values())
        return True
    return ok(v)

rows = []
for tag, inputs, ref in ROWS:
    for text in inputs:
        for mode in ('python', 'json'):
            if mode == 'python' and not python_ok(text): continue
            rows.append((ref, tag, mode, False, text, run(tag, mode, False, text)))
for tag, inputs, ref in STRICT_ROWS:
    for text in inputs:
        for mode in ('python', 'json'):
            rows.append((ref, tag, mode, True, text, run(tag, mode, True, text)))
# validate_python(from_attributes=True), as FastAPI calls it: model_attributes_type
ATTRS_ROWS = [('shop', ['5', '"x"', 'null', '[1]', '{"name":"x","images":[3],"itemId":1,"sizes":[1]}',
                        '{"name":"x","images":[],"itemId":1,"sizes":[1],"image":7}',
                        '{"name":"x","images":[{"url":1}],"itemId":1,"sizes":[1]}'],
               'pydantic/tests/test_main.py::test_validate_python_from_attributes')]
for tag, inputs, ref in ATTRS_ROWS:
    for text in inputs:
        for strict in (False, True):
            rows.append((ref, tag, 'python-attrs', strict, text, run(tag, 'python-attrs', strict, text)))
for tag, inputs, ref in JSON_ONLY:
    for text in inputs:
        rows.append((ref, tag, 'json', False, text, run(tag, 'json', False, text)))

# model_dump_json(by_alias, exclude_unset, exclude_none, exclude_defaults) after validate_python
DUMP_ROWS = [('shop', t, opts) for t in [
    '{"name":"x","images":[],"itemId":3,"sizes":[1]}',
    '{"name":"x","images":[{"url":"u","name":"n"}],"itemId":"7","sizes":[1,2],"image":{"url":"a","name":"b"},"stock":{"a":1}}',
    '{"name":"x","images":[],"itemId":3,"sizes":[1],"image":null,"tags":[]}']
  for opts in [(False, False, False, False), (True, False, False, False), (False, True, False, False),
               (True, True, False, False), (False, False, True, False), (False, False, False, True)]] + \
  [('offer', t, opts) for t in ['{"price": 2.5, "item_id": 3}', '{"price": 1, "item_id": 1, "q": "abcd", "discount": 0}']
   for opts in [(False, True, False, False), (False, False, False, True)]]

def run_dump(tag, text, opts):
    ta = TypeAdapter(TYPES[tag])
    v = ta.validate_python(json.loads(text))
    ba, eu, en, ed = opts
    return v.model_dump_json(by_alias=ba, exclude_unset=eu, exclude_none=en, exclude_defaults=ed)

dumps = [(PD_DUMP, tag, text, opts, run_dump(tag, text, opts)) for tag, text, opts in DUMP_ROWS]

schemas = [(tag, json.dumps(TypeAdapter(t).json_schema(), separators=(',', ':'), ensure_ascii=False))
           for tag, t in TYPES.items()]

print('/-! Generated by `scripts/conformance/generate.py` from pydantic 2.14.1 /')
print('pydantic-core 2.50.1. Do not edit by hand. -/')
print()
print('/-- (upstream test, type tag, mode, strict, input, pydantic output) -/')
print('def validationTable : List (String × String × String × Bool × String × String) := [')
print(',\n'.join('  (%s, %s, %s, %s, %s, %s)' % (lean_str(r), lean_str(t), lean_str(m), 'true' if s else 'false',
      lean_str(i), lean_str(o)) for r, t, m, s, i, o in rows))
print(']')
print()
print('/-- (upstream test, type tag, input, (by_alias, exclude_unset, exclude_none, exclude_defaults), pydantic dump) -/')
print('def dumpTable : List (String × String × String × (Bool × Bool × Bool × Bool) × String) := [')
print(',\n'.join('  (%s, %s, %s, (%s), %s)' % (lean_str(r), lean_str(t), lean_str(i), ', '.join('true' if b else 'false' for b in o), lean_str(out))
      for r, t, i, o, out in dumps))
print(']')
print()
print('/-- (type tag, `TypeAdapter(T).json_schema()`, compact) -/')
print('def schemaTable : List (String × String) := [')
print(',\n'.join('  (%s, %s)' % (lean_str(t), lean_str(s)) for t, s in schemas))
print(']')

# `pattern`: does constr(pattern=p) accept s (Rust regex, unanchored search), or is p a SchemaError
REGEX_REF = 'pydantic/tests/test_types.py::test_pattern'
REGEX_INPUTS = ['', 'a', 'abc', 'xxabcxx', 'ABC', 'abc\n', '\nabc', 'a b', 'foo bar', 'foo_bar', 'x-1',
                '12345', '1234', '123456', '٣٤٥', 'é', 'Ünïcödé', '😀', 'a\tb', ' ', ' x', 'xxx123', 'xxx12',
                'bob@example.com', 'not an email', '2024-01-31', '2024-1-31', 'A1', 'a1', '_1', 'aaaa', 'aa', 'a{2}',
                '-', ']', '[', '^', '$', '.', '*', '\\', 'ab12CD', '550e8400-e29b-41d4-a716-446655440000', 'a.b', 'a+b']
REGEX_PATTERNS = [
    # from upstream tests
    '^text$', 'abc', r'^\d{5}$', r'^\w\d$', r'^xxx\d{3}$', r'[A-Z0-9]+', r'[A-Za-z0-9]+',
    # common field patterns
    r'^[a-z0-9_-]{3,16}$', r'^[^@\s]+@[^@\s]+\.[a-z]{2,}$', r'^\d{4}-\d{2}-\d{2}$',
    r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$', r'^(?:[a-z]+\.)*[a-z]+$', r'^\+?[0-9 ]+$',
    # syntax and semantics
    '^abc$', 'a|', '()', '(|a)', '(?:)', r'\d', r'\D', r'\w', r'\W', r'\s', r'\S', r'^\s*$', r'\bfoo\b', r'\Bo', r'\<b', r'a\>',
    r'\Aa', r'c\z', '$a', '^*', r'\b*', 'a**', 'a{2}{3}', '^a{2,3}$', 'a{2,}', '^a{0}$', 'a{ 2}', 'a{2, 3}', 'x*?y', 'a+?', 'a??',
    '[a-]', '[-a]', '[a-b-c]', '[^]a]', '[]a]', '[a^]', r'[\]]', r'[\[]', r'[\w]', r'[^\d\s]', '[a&&b]', '[a-z&&[^aeiou]]',
    '[a--b]', '[a-c--b]', '[a~~b]', '[a&b]', '[[a][b]]', r'\x41', r'\x{1F600}', r'A', r'\u{41}', r'\U0001F600',
    r'\#', r'\ ', r'\-', r'\_', r'\/', r'\.', r'\*', r'\\', r'\^', r'\$', r'\{', '.', '^.$', '[^a]', 'é', '(?P<n>a)', '(?<n>a)b',
    '^(a+)+$', '(a|aa)*b', r'^(\w+\s?)*$', ']', '}', 'a|b|c', '(a|b)(c|d)', '((a))', r'^\p{L}$', r'\v', r'\f', r'\a', r'\t',
    # rejected by pydantic
    'a{', 'a{2', '{', 'x{a}', '[[]', '[]', '[^]', '(?=a)', 'a{,3}', r'\Z', '*a', '\\', r'\h', r'\0', r'\e', r'[\d-z]', '[z-a]',
    r'[\b]', '[a-\\x{10}]', 'a{2,1}', 'a{4294967296}', '(?P<1a>x)', '(?<a>x)(?<a>y)', '(a', 'a)', 'x|*', r'\Q', r'\N',
    r'\b{start}a', '(?i)ab', '(?s).', r'\p{L}', '[[:alpha:]]',
]

def regex_result(p, s):
    try:
        ta = TypeAdapter(constr(pattern=p))
    except Exception:
        return 'error'
    try:
        ta.validate_python(s)
        return 'true'
    except ValidationError:
        return 'false'

regex_rows = []
for p in REGEX_PATTERNS:
    for s in REGEX_INPUTS:
        res = regex_result(p, s)
        regex_rows.append((p, s, res))
        if res == 'error':
            break

print()
CHUNK = 400
chunks = [regex_rows[i:i + CHUNK] for i in range(0, len(regex_rows), CHUNK)]
for k, rows_k in enumerate(chunks):
    print('def regexTable%d : List (String × String × String) := [' % k)
    print(',\n'.join('  (%s, %s, %s)' % (lean_str(p), lean_str(s), lean_str(r)) for p, s, r in rows_k))
    print(']')
    print()
print('/-- (pattern, input, whether `constr(pattern=…)` accepts it: "true", "false", or "error" for a SchemaError) -/')
print('def regexTable : List (String × String × String) :=')
print('  ' + ' ++ '.join('regexTable%d' % k for k in range(len(chunks))))
