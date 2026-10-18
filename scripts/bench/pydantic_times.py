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

# patterns (Lean: the compiled pattern, Regex.ofSource, on the same text)
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

# float and Decimal from a 1 MiB string (Lean: validate_python on the string)
from decimal import Decimal
digits = '7' * 1048576
for name, ta, text in [('float, 2 MiB digit string', TypeAdapter(float), digits * 2),
                       ('float, 4 MiB digit string', TypeAdapter(float), digits * 4),
                       ('float, "0." + 300 zeros + 1 MiB digits', TypeAdapter(float), '0.' + '0' * 300 + digits),
                       ('Decimal, 2 MiB digit string', TypeAdapter(Decimal), digits * 2),
                       ('Decimal, 4 MiB digit string', TypeAdapter(Decimal), digits * 4),
                       ('float, 1 MiB digit string', TypeAdapter(float), digits),
                       ('float, 1 MiB digits + ".5e-3"', TypeAdapter(float), digits + '.5e-3'),
                       ('Decimal, 1 MiB digit string', TypeAdapter(Decimal), digits),
                       ('Decimal, 1 MiB digits + ".5"', TypeAdapter(Decimal), digits + '.5')]:
    print(f'{name}: {best(ta.validate_python, text):.2f} ms')

# pattern calls, passing and failing (Lean: the same inputs in tests/Bench.lean)
def per_call(pat, texts):
    ta = TypeAdapter(Annotated[str, Field(pattern=pat)])
    def run(ts):
        for t in ts:
            try:
                ta.validate_python(t)
            except Exception:
                pass
    return best(run, texts) / len(texts)

email = r'^[a-z0-9._%+-]{1,64}@[a-z0-9.-]{1,255}\.[a-z]{2,63}$'
emails = ['first.last+' + str(10000 + i) + 'x' * 24 + '@mail.example-domain.com' for i in range(1000)]
runs = ['a' * (995 + i % 10) for i in range(1000)]
words = ['word' + str(100000 + i) + ' another phrase here' for i in range(1000)]
for name, pat, texts in [
        ('email-like, passing', email, emails),
        ('email-like, failing (no @)', email, [e.replace('@', '#') for e in emails]),
        ('email-like, failing (one-letter TLD)', email, [e[:-3] + 'c' for e in emails]),
        ('email-like, failing (upper case at the end)', email, [e + 'M' for e in emails]),
        ('email-like, failing (65-character local part)', email, ['y' * 60 + str(10000 + i) + '@mail.example-domain.com' for i in range(1000)]),
        ('^(a{1,50})+$, passing', r'^(a{1,50})+$', runs),
        ('^(a{1,50})+$, failing (b at the end)', r'^(a{1,50})+$', [r + 'b' for r in runs]),
        ('(\\w{1,10}\\s?){1,10}x, failing', r'(\w{1,10}\s?){1,10}x', words),
        ('(\\w{1,10}\\s?){1,10}x, passing', r'(\w{1,10}\s?){1,10}x', [w + 'x' for w in words])]:
    print(f'pattern {name}: {per_call(pat, texts) * 1000:.2f} us per call')
