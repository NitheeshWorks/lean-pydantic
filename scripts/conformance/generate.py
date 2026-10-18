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
from pydantic import BaseModel, ConfigDict, Field, FiniteFloat, NonNegativeInt, TypeAdapter, ValidationError, constr

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

class ExtraForbid(BaseModel):
    model_config = ConfigDict(extra='forbid')
    a: int
    b: str = Field(alias='B')

class ExtraAllow(BaseModel):
    model_config = ConfigDict(extra='allow')
    a: int
    b: str = Field('x', alias='B')

class ExtraPop(BaseModel):
    model_config = ConfigDict(extra='forbid', populate_by_name=True)
    a: int
    b: str = Field(alias='B')

class ExtraNested(BaseModel):
    model_config = ConfigDict(extra='forbid')
    inner: ExtraAllow
    f: Optional[ExtraForbid] = None

class ExtraAliasAllow(BaseModel):
    model_config = ConfigDict(extra='allow')
    a: str = Field('default', alias='alias_a')
    b: str = Field('default', alias='alias_b')

class FormData(BaseModel):
    username: str
    password: str
    model_config = {'extra': 'forbid'}

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
    'set_int': set[int],
    'set_int_min2': Annotated[set[int], Field(min_length=2, max_length=3)],
    'decimal': Decimal,
    'plain_float': float,
    'float_gt0': Annotated[float, Field(gt=0)],
    'condecimal_5_2': Annotated[Decimal, Field(max_digits=5, decimal_places=2)],
    'condecimal_gt0_3': Annotated[Decimal, Field(gt=0, max_digits=3)],
    'condecimal_places1_mult': Annotated[Decimal, Field(decimal_places=1, multiple_of=Decimal('0.5'), le=10)],
    'extra_forbid': ExtraForbid,
    'extra_allow': ExtraAllow,
    'extra_pop': ExtraPop,
    'extra_nested': ExtraNested,
    'extra_alias_allow': ExtraAliasAllow,
    'form_data': FormData,
}

PC = 'pydantic-core/tests/validators/'
_D = '7' * 4301
_E = '7' * 4300
LONG_INT_FORMS = [_D, _D + '.0', _D + '.00', '-' + _D + '.0', ' ' + _D, '000' + _D, '+' + _D, '7_' + _D,
    '-' + _E, '-' + _E[1:], _D + ' ', _D + 'x', '0' + _D, '-0' + _D, _E + '.0', '000' + _E, ' ' + _E + ' ', '+' + _E,
    '7_' + _E[1:], _E[:10] + '_' + _E[10:], _D[:10] + '_' + _D[10:], '0' * 4301 + '1', '0' * 4301 + '.0']
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
    # over-long strings, every form: jiter's leading-literal limit is int_parsing_size,
    # the cleaned forms' is int_parsing
    ('int', ['"' + f + '"' for f in LONG_INT_FORMS], PC + 'test_int.py::test_long_int'),
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
              '123456789', '-12.5', '"00012.30"', '0.5', '9.5', '10.5', '10', '"7.25"', '"1.2e2"', '1e400', '1e999999999', '-1e309', '1.5e-400', '0e999999999',
              '123456789012345678901234567890e5', '1e300', '"1e999999999"', '1e22', '0.1e-5']
DECIMAL_WIDE_QUOTIENT = ['123456789012345678901234567890e5', '1e300', '"1e999999999"']
# Python iterates a set in hash order; these inputs are already in that order
SET_IN = ['[1,1,2]', '[1,2,3]', '[]', '[1]', '[0,1,2,3,4]', '5', '"ab"', '[1,"x",2]', '[1,"x",[]]', '{"a":1}', 'null',
          '["1","2"]', '[1.0,2]', '[true]']
ROWS += [
    ('set_int', SET_IN, PC + 'test_set.py::test_set_ints_both'),
    ('set_int_min2', SET_IN, PC + 'test_set.py::test_set_kwargs'),
]
STRICT_ROWS_SET = [('set_int', SET_IN, PC + 'test_set.py::test_set_strict')]

FLOAT_PLAIN_IN = ['1.5', '1', '-0.0', '1e400', '-1e400', 'NaN', 'Infinity', '-Infinity', '"nan"', '"NaN"', '"inf"',
                  '"-inf"', '"+Infinity"', '"-infinity"', '"1_0.5"', '" 2.5 "', '"x"', 'true', 'false', 'null', '[1]',
                  '0.1', '1e16', '1e-7', '123456789012345678', '0.30000000000000004', '5e-324', '1.7976931348623157e308',
                  # rounding edges, subnormals, signed zero, overflow, huge integers, shortest repr
                  '9007199254740993', '9007199254740995', '2.2250738585072011e-308', '2.2250738585072014e-308',
                  '4.9e-324', '2.4703282292062327e-324', '2.4703282292062328e-324', '1e-400', '-1e-400',
                  '2.00000000000000011102230246251565404236316680908203125',
                  '2.000000000000000111022302462515654042363166809082031251', '1e23', '8.98846567431158e307',
                  '1.7976931348623158e308', '1.7976931348623159e308', '12345678901234567890', '-12345678901234567890',
                  '1' + '0' * 400, '-0', '0.0', '-0.0e10', '100', '1e15', '1e21', '1e22', '123456.789e3', '0.000001',
                  '0.0000001', '1.5e300', '3.141592653589793238462643383279', '"1e400"', '"-0.0"', '"4.9e-324"',
                  '"12345678901234567890"', '"0x10"', '"1e"', '".5"', '"5."', '"+.5e1"', '"in f"', '"Infinity "']
ROWS += [
    ('plain_float', FLOAT_PLAIN_IN, PC + 'test_float.py::test_float_inf_nan'),
    ('float_gt0', FLOAT_PLAIN_IN, PC + 'test_float.py::test_float_kwargs'),
]
ROWS += [
    ('decimal', DECIMAL_IN, PC + 'test_decimal.py::test_decimal'),
    ('condecimal_5_2', DECIMAL_IN, PC + 'test_decimal.py::test_decimal_digits'),
    ('condecimal_gt0_3', DECIMAL_IN, PC + 'test_decimal.py::test_decimal_kwargs'),
    # multiple_of on a Decimal is exact here; Python's divides at 28 digits and
    # rejects any quotient wider than that (UP-055), so these are left out
    ('condecimal_places1_mult', [x for x in DECIMAL_IN if x not in DECIMAL_WIDE_QUOTIENT],
     PC + 'test_decimal.py::test_decimal_multiple_of'),
]

# model_config['extra'] and populate_by_name (no repeated keys: JSON text with
# a repeated extra key is a documented deviation, pinned by a hand case)
EXTRA_FORBID_IN = ['{"a":1,"B":"q"}', '{"z":1,"a":"x","b":"q","B":2,"y":null}', '{"a":1,"B":"q","extra":[1,{"k":2}]}',
    '{}', '{"z":1}', '[]', '5', '{"a":1,"b":"q"}', '{"B":"q","a":1,"a2":true}']
EXTRA_ALLOW_IN = ['{"a":1}', '{"z":1,"a":1,"b":"q","y":[1]}', '{"a":1,"B":"v","c":{"d":null}}', '{"c":"c"}',
    '{"a":"x","w":1}', '{"B":"v","a":2,"z":[]}']
EXTRA_POP_IN = ['{"a":1,"b":"q"}', '{"a":1,"B":"q"}', '{"a":1,"b":"q","B":"r"}', '{"a":1,"b":5}', '{"a":1}',
    '{"a":1,"B":"q","c":0}', '{"b":"q","c":0}']
EXTRA_NESTED_IN = ['{"inner":{"a":1,"q":2},"f":{"a":1,"B":"s","w":0},"k":1}', '{"inner":{"a":1,"q":2}}',
    '{"inner":{"a":1},"f":null}', '{"inner":5,"x":1}', '{"f":{"a":1,"B":"s"},"inner":{"a":3,"B":"t","r":[1]}}']
EXTRA_ALIAS_IN = ['{"alias_a":"a","c":"c"}', '{"extra_key":"extra"}', '{"a":"x","alias_b":"y"}']
FORM_IN = ['{"username":"Foo","password":"secret"}', '{"username":"Foo","password":"secret","extra":"extra"}',
    '{}', '{"username":"Foo"}']
ROWS += [
    ('extra_forbid', EXTRA_FORBID_IN, 'pydantic/tests/test_main.py::test_forbidden_extra_fails'),
    ('extra_allow', EXTRA_ALLOW_IN, 'pydantic/tests/test_main.py::test_allow_extra'),
    ('extra_pop', EXTRA_POP_IN, 'pydantic/tests/test_config.py::test_populate_by_name_still_effective'),
    ('extra_nested', EXTRA_NESTED_IN, 'pydantic/tests/test_main.py::test_forbidden_extra_fails'),
    ('extra_alias_allow', EXTRA_ALIAS_IN, 'pydantic/tests/test_main.py::test_dict_with_extra_keys'),
    ('form_data', FORM_IN, 'fastapi/tests/test_tutorial/test_request_form_models/test_tutorial002.py'),
]

STRICT_ROWS = [
    ('extra_forbid', ['{"a":1,"B":"q","z":0}', '{"a":"1","B":"q","z":0}'], 'pydantic/tests/test_main.py::test_forbidden_extra_fails'),
    ('decimal', ['1.5', '"1.5"', '1', 'true'], PC + 'test_decimal.py::test_decimal_strict_py'),
    ('plain_float', ['1.5', '1', '"1.5"', 'true', 'NaN'], PC + 'test_float.py::test_float_strict'),
    ('int', ['1', '"1"', '1.0', 'true', 'null'], PC + 'test_int.py::test_int_strict'),
    ('float', ['1', '1.5', '"1.5"', 'true'], PC + 'test_float.py::test_float_strict'),
    ('bool', ['true', '"true"', '1'], PC + 'test_bool.py::test_bool_strict'),
    ('str', ['"x"', '1'], PC + 'test_string.py::test_str'),
    ('item', ['{"name": "x", "price": 1}', '{"name": "x", "price": "1"}'], 'pydantic/tests/test_main.py::test_model_validate_strict'),
]
PD_DUMP = 'pydantic/tests/test_main.py::test_exclude_unset_dict'
PD_DUMP_EXTRA = 'pydantic/tests/test_main.py::test_dict_exclude_unset_populated_by_alias_with_extra'
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
for tag, inputs, ref in STRICT_ROWS_SET:
    for text in inputs:
        for mode in ('python', 'json'):
            rows.append((ref, tag, mode, True, text, run(tag, mode, True, text)))
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
   for opts in [(False, True, False, False), (False, False, False, True)]] + \
  [(tag, t, opts) for tag, ts in [('extra_alias_allow', EXTRA_ALIAS_IN), ('extra_allow', EXTRA_ALLOW_IN[:3]),
                                  ('extra_nested', EXTRA_NESTED_IN[1:3])] for t in ts
   for opts in [(False, False, False, False), (True, False, False, False), (False, True, False, False),
                (True, True, False, False), (False, False, True, False)]]
# an extra named like an aliased field puts that name in pydantic's
# model_fields_set, so exclude_unset dumps the field
DUMP_ROWS += [('extra_allow', t, opts) for t in ['{"a":1,"b":"v"}', '{"a":1,"B":"w","b":"v"}', '{"y":[2],"b":"v","a":3}']
              for opts in [(True, True, False, False), (False, True, False, False)]]

def run_dump(tag, text, opts):
    ta = TypeAdapter(TYPES[tag])
    v = ta.validate_python(json.loads(text))
    ba, eu, en, ed = opts
    return v.model_dump_json(by_alias=ba, exclude_unset=eu, exclude_none=en, exclude_defaults=ed)

dumps = [(PD_DUMP if tag in ('shop', 'offer') else PD_DUMP_EXTRA, tag, text, opts, run_dump(tag, text, opts))
         for tag, text, opts in DUMP_ROWS]

# repr(value) (and str(value) for a model) of what validation returns, or
# str(ValidationError): what `print` shows in pydantic's docs
REPR_REF = 'pydantic/tests/test_main.py::test_ultra_simple_repr'
STR_ERR_REF = 'pydantic-core/tests/test_misc.py::test_validation_error_multiple'

def run_repr(tag, mode, strict, text, out):
    """(validated?, repr(v) or str(v), or str(e))"""
    ta = TypeAdapter(TYPES[tag])
    try:
        v = ta.validate_json(text, strict=strict) if mode == 'json' else ta.validate_python(json.loads(text), strict=strict)
        return True, (repr(v) if out == 'repr' else str(v))
    except ValidationError as e:
        return False, str(e)

repr_rows = []
seen = set()
for ref, tag, mode, strict, text, _ in rows:
    if mode == 'python-attrs' or (tag, mode, strict, text) in seen: continue
    seen.add((tag, mode, strict, text))
    is_model = isinstance(TYPES[tag], type) and issubclass(TYPES[tag], BaseModel)
    ok, r = run_repr(tag, mode, strict, text, 'repr')
    repr_rows.append((REPR_REF if ok else STR_ERR_REF, tag, mode, strict, 'repr', text, r))
    if ok and is_model:
        repr_rows.append((REPR_REF, tag, mode, strict, 'str', text, run_repr(tag, mode, strict, text, 'str')[1]))

schemas = [(tag, json.dumps(TypeAdapter(t).json_schema(), separators=(',', ':'), ensure_ascii=False))
           for tag, t in TYPES.items()]

print('/-! Generated by `scripts/conformance/generate.py` from pydantic 2.14.1 /')
print('pydantic-core 2.50.1. Do not edit by hand. -/')
print()
print('/-- (upstream test, type tag, mode, strict, input, pydantic output) -/')
VT = 'List (String × String × String × Bool × String × String)'
vchunks = [rows[i:i + 400] for i in range(0, len(rows), 400)]
for k, ch in enumerate(vchunks):
    print('def validationTable%d : %s := [' % (k, VT))
    print(',\n'.join('  (%s, %s, %s, %s, %s, %s)' % (lean_str(r), lean_str(t), lean_str(m), 'true' if s else 'false',
          lean_str(i), lean_str(o)) for r, t, m, s, i, o in ch))
    print(']')
    print()
print('def validationTable : %s :=' % VT)
print('  ' + ' ++ '.join('validationTable%d' % k for k in range(len(vchunks))))
print()
# model_fields_set (sorted) of each validated input, by alias and by name,
# from Python objects and from JSON text
FS_TAGS = {'extra_forbid', 'extra_allow', 'extra_pop', 'extra_alias_allow', 'shop', 'form_data'}
FS_EXTRA = [('extra_allow', ['{"a":1,"b":"v"}', '{"a":1,"B":"w","b":"v"}', '{"a":1,"B":"w"}', '{"b":"v","a":2,"q":1}']),
            ('extra_pop', ['{"a":1,"b":"v"}', '{"a":1,"B":"w"}', '{"a":1,"B":"w","b":"v"}']),
            ('extra_alias_allow', ['{"a":"x","alias_b":"y"}', '{"alias_a":"x","b":"y"}', '{}'])]
fs_rows = []
fs_seen = set()
for tag, inputs in [(t, i) for t, i, _ in ROWS if t in FS_TAGS] + FS_EXTRA:
    for text in inputs:
        for mode in ('python', 'json'):
            if (tag, mode, text) in fs_seen or (mode == 'python' and not python_ok(text)): continue
            fs_seen.add((tag, mode, text))
            ta = TypeAdapter(TYPES[tag])
            try:
                v = ta.validate_json(text) if mode == 'json' else ta.validate_python(json.loads(text))
            except ValidationError:
                continue
            fs_rows.append((tag, mode, text, json.dumps(sorted(v.model_fields_set), separators=(',', ':'))))
print('/-- (type tag, mode, input, sorted `model_fields_set` of the validated model) -/')
print('def fieldsSetTable : List (String × String × String × String) := [')
print(',\n'.join('  (%s, %s, %s, %s)' % (lean_str(t), lean_str(m), lean_str(i), lean_str(o)) for t, m, i, o in fs_rows))
print(']')
print()
print('/-- (upstream test, type tag, input, (by_alias, exclude_unset, exclude_none, exclude_defaults), pydantic dump) -/')
print('def dumpTable : List (String × String × String × (Bool × Bool × Bool × Bool) × String) := [')
print(',\n'.join('  (%s, %s, %s, (%s), %s)' % (lean_str(r), lean_str(t), lean_str(i), ', '.join('true' if b else 'false' for b in o), lean_str(out))
      for r, t, i, o, out in dumps))
print(']')
print()
RT = 'List (String × String × String × Bool × String × String × String)'
rchunks = [repr_rows[i:i + 400] for i in range(0, len(repr_rows), 400)]
for k, ch in enumerate(rchunks):
    print('def reprTable%d : %s := [' % (k, RT))
    print(',\n'.join('  (%s, %s, %s, %s, %s, %s, %s)' % (lean_str(r), lean_str(t), lean_str(m), 'true' if st else 'false',
          lean_str(o), lean_str(i), lean_str(x)) for r, t, m, st, o, i, x in ch))
    print(']')
    print()
print('/-- (upstream test, type tag, mode, strict, "repr" or "str", input, `repr(v)` / `str(v)` of the result or `str(e)`) -/')
print('def reprTable : %s :=' % RT)
print('  ' + ' ++ '.join('reprTable%d' % k for k in range(len(rchunks))))
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

# Inline flags, POSIX classes, case folding, (?-u) and the corners of Rust's
# class and escape grammar, on inputs that tell them apart.
REGEX_FLAG_INPUTS = ['', 'a', 'A', 'b', 'ab', 'AB', 'Ab', 'abc', 'AbC', 'a b', 'a\nb', 'a\r\nb', 'a\rb', '\r',
                     'k', 'K', '\u212a', 'S', '\u017f', 'é', 'É', 'ß', '\u1e9e', 'Σ', 'ς', 'ǅ', 'ı', 'I',
                     '1', '_', '-', ':', '#', ' ', '\t', 'aa', 'aaa', ']', '[', '😀']
REGEX_FLAG_PATTERNS = [
    # flag syntax and scope
    '(?i)abc', '(?i:a)b', '(?i)a(?-i)b', '(?i)(a(?-i)b)c', '(?i:a(?-i)b)c', 'a|(?i)b|c', '(?i)', '(?i)|a',
    'a(?i)|B', '(?:(?i)a)a', '(?i)(?:a|(?-i)b)|c', '(?i-i)a', '(?ii)a', '(?-)a', '(?i-)a', '(?-i-s)a', '(?z)a',
    '(?)a', '(?i)*', 'x(?i)*', '(?i)?', '(?i){2}', '(?i:)', '(?-i:)', '(?i)(?i)a', '(?U)a+', '(?U)a+?', '(?-U)a',
    '(?i-U)a', '(?u)a', '(?u:a)', '(?#x)', '(?P=n)', '(?=a)', '(?<=a)b', '(?<!a)b', '(?!a)', '(?i',
    # case folding (Rust's simple case folding)
    '(?i)k', '(?i)K', r'(?i)\x{212a}', '(?i)s', r'(?i)\u017f', '(?i)ß', '(?i)σ', '(?i)ς', '(?i)ǅ', '(?i)ı',
    '(?i)i', '(?i)é', '(?i)[a-z]', '(?i)[k]', '(?i)[^k]', '(?i)[^a]', '(?i)[a-z&&[^k]]', '(?i)[k&&K]',
    '(?i)[k--K]', '(?i)[k~~K]', r'(?i)\w', r'(?i)\W', r'(?i)[^\W]', r'(?i)\d', r'(?i)\x41', '(?i)[[:upper:]]',
    '(?i)[[:lower:]]', '(?i)[[:^lower:]]', '(?i)^[a-z0-9_-]{3,16}$', '(?i)[[^k]&&[a-z]]', '(?i)😀',
    # dot and line ends
    '(?s).', '(?s)a.b', '(?is)a.b', '(?R).', '(?sR).', '(?R)a.b', '(?s:.)a', '(?s)(?-s).', '^.$', '(?R)^.$',
    '(?m)^b', '(?m)a$', '(?mR)^b', '(?m)a', r'(?m)\Aa', r'(?m)\z', '(?m)(?-m)^a', '(?m:a)^b',
    # (?x)
    '(?x)a b', '(?x)a # c\nb', '(?x)a#c', '(?x)[a b]', '(?x)[ ^a]', '(?x)[a - c]', '(?x)[a#]\nb]', r'(?x)a\ b',
    r'(?x)a\#b', '(?x)[#]', '(?x)a{ 2 , 3 }', '(?x)a {2}', 'a {2}', '(?x)a + ', '(?x)a+ ?', '(?x)a{2} ?',
    '(?x)(?P< n>a)', '(?x)( ?:a)', '( ?:a)', '(?x)(? i)a', '(?x)(?i x)a', r'(?x)\x 41', r'(?x)\x{ 41 }',
    r'(?x)\u00 41', '(?x)\\', '(?x)a\u3000b', '(?x)a\u200bb', '(?x)a\u2028b', '(?x)(?-x)a b', '(?x)a(?-x: b) c',
    '(?x:a b)', '(?ix)A B', '(?x)[ ] ]', '(?x)[]', '(?x)[ ]', '(?x)[a& &b]', '(?x)[a - - b]', '(?x)[a- -b]',
    r'(?x)\b{ start }a', r'(?x)\b {start}a', '(?x)a{1 0}', r'(?x)\d +', '(?x)[[:alpha: ]]', '(?x)[ [:alpha:] ]',
    '(?x)(  a  )',
    # POSIX classes
    '[[:alpha:]]', '[[:^alpha:]]', '[[:alnum:]]', '[[:ascii:]]', '[[:blank:]]', '[[:cntrl:]]', '[[:digit:]]',
    '[[:graph:]]', '[[:lower:]]', '[[:print:]]', '[[:punct:]]', '[[:space:]]', '[[:upper:]]', '[[:word:]]',
    '[[:xdigit:]]', '[[:^space:]]', '[[:foo:]]', '[:alpha:]', '[[:alpha:]', '[[:alpha:]]]', '[[:alpha:]x]',
    '[x[:digit:]]', '[[:alpha:][:digit:]]', '[^[:alpha:]]', '[[:alpha:]&&[:lower:]]', '[[:alpha:]--[:upper:]]',
    '[a-[:alpha:]]', '[[:alpha:]-a]', r'[\d-[:alpha:]]', '[[:a]b:]]', '[[:^word:]]',
    # leading `-` and `]`, empty operands
    '[--a]', '[---a]', '[^-a]', '[]-a]', '[!-[]', '[a&&]', '[&&a]', '[a--]', '[-]', '[^-]', '[--]',
    # (?-u)
    '(?-u)a', '(?-u)é', r'(?-u)\x{e9}', r'(?-u)[\x{e9}]', '(?-u)[é]', r'(?-u)\xff', r'(?-u)\x41', r'(?-u)\d',
    r'(?-u)\s', r'(?-u)\w', r'(?-u)\W', r'(?-u)[\w]', r'(?-u)[^\W]', '(?-u)[^a]', '(?-u).', '(?s-u).',
    '(?-u)[[:alpha:]]', '(?-u)[[:^alpha:]]', r'(?-u)[^\x00-\xff]', r'(?-u)[\xff&&a]', '(?-u)[a-z--b]',
    '(?-u)(?i)é', '(?-u)(?i)k', '(?i-u)[a-z]', r'(?-u)(?u:\w)', r'(?-u:\w)é', r'(?-u)\p{L}', '(?-u)$',
    r'(?-u)\Aa', r'(?-u)\b', r'(?-u)\B', r'(?-u)\<a',
    # special word boundaries, hex escapes, counts
    r'\b{start}a', r'\b{end}', r'a\b{end}', r'\b{start-half}a', r'\b{end-half}', r'\b{word}', r'\b{ start}',
    r'\b{2}', '\\b{', r'(?i)\b{start}A', r'\x{000000041}', r'\x{0000000041}', r'\x{100000000}', r'\x{110000}',
    r'\x{d800}', 'a{\t2}', 'a{ 2, }', 'a{2 ,3}', 'a{\u30002}',
]
for p in REGEX_FLAG_PATTERNS:
    for s in REGEX_FLAG_INPUTS:
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
