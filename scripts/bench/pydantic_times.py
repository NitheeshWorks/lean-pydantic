"""pydantic-core's times on the inputs of tests/Bench.lean (best of 5), for
choosing the benches' bounds. Run with upstream-spec/.venv/bin/python -I."""
import time
from pydantic import TypeAdapter


def wide_object(n, dups):
    return '{' + ','.join([f'"k{i}":{i}' for i in range(n)] + [f'"k{i}":0' for i in range(dups)]) + '}'


def best(f, s):
    ts = []
    for _ in range(5):
        t0 = time.perf_counter(); f(s); ts.append(time.perf_counter() - t0)
    return min(ts) * 1000


cases = [
    ('dict[str, int], 100000 keys', TypeAdapter(dict[str, int]), wide_object(100000, 0)),
    ('dict[str, int], 200000 keys and 1000 repeats', TypeAdapter(dict[str, int]), wide_object(200000, 1000)),
    ('set[int], 200000 items, half repeated', TypeAdapter(set[int]), '[' + ','.join(str(i // 2) for i in range(200000)) + ']'),
    ('int, 65000 digits (rejected)', TypeAdapter(int), '1' * 65000),
    ('int, 65000-digit string (rejected)', TypeAdapter(int), '"' + '1' * 65000 + '"'),
]
for name, ta, s in cases:
    def f(x):
        try:
            ta.validate_json(x)
        except Exception:
            pass
    print(f'{name}: {best(f, s):.1f} ms')

# validation alone, on already-parsed input (Lean: validate_python on a parsed Json)
import json
for name, ta, s in cases[:3]:
    v = json.loads(s)
    print(f'{name} (validate_python): {best(ta.validate_python, v):.1f} ms')

# patterns (Lean: Regex.searchDfa on the same text)
from typing import Annotated
from pydantic import Field
wide = '(a|b)' * 50 + 'c'
for name, pat, text in [('^(a{1,50})+$, 10 000', r'^(a{1,50})+$', 'a' * 10000),
                        ('^(a{1,50})+$, 20 000', r'^(a{1,50})+$', 'a' * 20000),
                        ('(a|b)x50 c, 50 000', wide, 'ab' * 25000),
                        ('(a|b)x50 c, 100 000', wide, 'ab' * 50000)]:
    ta = TypeAdapter(Annotated[str, Field(pattern=pat)])
    def run(t, ta=ta):
        try:
            ta.validate_python(t)
        except Exception:
            pass
    print(f'pattern {name}: {best(run, text):.2f} ms')
