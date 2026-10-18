#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. The verification gate
# (`lake exe axioms`, scripts/Axioms.lean) checks every declaration on the
# compiled environment. Exits on the first failure.
#
#   scripts/check.sh            # everything
#   scripts/check.sh --quick    # build and the verification gate (no tests)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=LeanPydantic

echo "== build =="
lake build

echo "== verification gate =="
# scripts/Axioms.lean is pinned to the stack-tools copy.
echo "$(cat scripts/Axioms.sha256)  scripts/Axioms.lean" | sha256sum --check --quiet
lake exe axioms "$LIB"

[[ "${1:-}" == "--quick" ]] && exit 0

echo "== property tests =="
lake exe props

echo "== conformance =="
lake exe conformance

echo "== benches =="
lake exe bench

echo "== traceability =="
python3 scripts/traceability-check.py

if [[ "${1:-}" == "--pbt" ]]; then
  echo "== plausible =="
  (cd tests/pbt && lake build && ./.lake/build/bin/pbt)
fi
echo "all clean"
