#!/usr/bin/env bash
# Local mirror of the comparator auditability gate. This does NOT replace a real
# leanprover/comparator run (which re-exports the closure through the nanoda and
# Lean default kernels — see comparator/README.md and .github/workflows/
# comparator.yml). It is the cheap offline pre-flight every commit can run:
#
#   1. Build the three comparator modules:
#        Challenge   — mathlib-only sorry stubs (must elaborate w/ Mathlib alone)
#        Solution    — project proofs discharging each stub
#        Conformance — `@Challenge.X = @Solution.X := rfl` for all 19 names,
#                      so a statement mismatch fails the build (proof irrelevance)
#   2. Run the axiom audit: every Solution theorem's #print axioms closure must
#      be a subset of {propext, Classical.choice, Quot.sound}.
#
# Exits 0 iff all three modules build and every listed theorem is axiom-clean.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

NAMES="$(grep -cE '^#print axioms' comparator/axiom-audit.lean || true)"

echo "== building Challenge / Solution / Conformance =="
./lake-build.sh Challenge Solution Conformance

echo "== axiom audit (Solution.*) =="
OUT="$(mktemp "${TMPDIR:-/tmp}/comparator-audit.XXXXXX")"
trap 'rm -f "$OUT"' EXIT
lake env lean comparator/axiom-audit.lean >"$OUT" 2>&1 || {
  echo "FAIL: axiom-audit.lean errored (renamed theorem? library not built?)" >&2
  cat "$OUT" >&2
  exit 1
}

fail=0
if grep -Eiq "sorryAx|unknown identifier|unknown constant|error:" "$OUT"; then
  echo "FAIL: audit reported sorry/error:" >&2
  grep -Ei "sorryAx|unknown identifier|unknown constant|error:" "$OUT" >&2
  fail=1
fi
if grep -Fq "Lean.ofReduce" "$OUT"; then
  echo "FAIL: a Solution theorem uses native_decide (Lean.ofReduce*); not permitted in this comparator set." >&2
  fail=1
fi

GOT="$(grep -Fc "depend" "$OUT" || true)"
if [[ "$GOT" -ne "$NAMES" ]]; then
  echo "FAIL: expected $NAMES axiom reports, got $GOT." >&2
  fail=1
fi

if [[ "$fail" -ne 0 ]]; then
  cat "$OUT" >&2
  exit 1
fi

echo "OK: $NAMES comparator theorems build, conform (Challenge ≡ Solution), and are axiom-clean"
echo "    (subset of {propext, Classical.choice, Quot.sound}; no sorryAx, no native_decide)."
