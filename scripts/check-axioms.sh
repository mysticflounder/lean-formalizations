#!/usr/bin/env bash
# Release gate: assert every README-advertised "axiom-clean" theorem depends on
# ONLY Lean/mathlib core axioms — no `sorryAx`, no custom axioms.
#
# The checked list lives in scripts/axiom-check.lean (the README "Reproduce the
# verification" list). This wrapper elaborates that file against the already-built
# library and asserts the report is clean. Build the library first:
#   ./lake-build.sh            # then:
#   ./scripts/check-axioms.sh
#
# Exits 0 iff every checked theorem is axiom-clean. Prints the full report.
#
# Allowed axioms (project policy): propext, Classical.choice, Quot.sound, plus
# Lean.ofReduceBool / Lean.ofReduceNat under the native_decide bv_decide standard.
# The verified core currently uses NO native_decide and defines NO custom axiom
# (verified: `grep -rn '^axiom ' LeanFormalizations/` is empty), so the only
# disallowed axiom that can appear is sorryAx.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
CHECK_LEAN="scripts/axiom-check.lean"

if [[ ! -f "$CHECK_LEAN" ]]; then
  echo "missing $CHECK_LEAN" >&2
  exit 1
fi

# Expected number of reports = number of `#print axioms` lines in the check file.
EXPECTED="$(grep -Fc '#print axioms' "$CHECK_LEAN")"

OUT="$(mktemp "${TMPDIR:-/tmp}/axiom-check.XXXXXX")"
trap 'rm -f "$OUT"' EXIT

if ! lake env lean "$CHECK_LEAN" >"$OUT" 2>&1; then
  echo "FAIL: lean errored while elaborating $CHECK_LEAN (renamed/removed theorem? library not built?)" >&2
  cat "$OUT" >&2
  exit 1
fi

cat "$OUT"
echo "---"

fail=0

# 1. No sorry anywhere in the checked closure.
if grep -Fq "sorryAx" "$OUT"; then
  echo "FAIL: a checked theorem depends on sorryAx:" >&2
  grep -F "sorryAx" "$OUT" >&2
  fail=1
fi

# 2. No elaboration errors (e.g. an `unknown identifier` from a renamed theorem).
if grep -Fiq "unknown identifier" "$OUT" || grep -Fiq "unknown constant" "$OUT" || grep -Fiq "error:" "$OUT"; then
  echo "FAIL: lean reported an error in the check file:" >&2
  fail=1
fi

# 3. Every theorem produced exactly one axiom report (both "depends on axioms"
#    and "does not depend on any axioms" contain the substring "depend").
GOT="$(grep -Fc "depend" "$OUT" || true)"
if [[ "$GOT" -ne "$EXPECTED" ]]; then
  echo "FAIL: expected $EXPECTED axiom reports, got $GOT (a theorem failed to print?)" >&2
  fail=1
fi

# 4. Forward-looking notice: surface native_decide axioms (allowed, but should be
#    a deliberate, reported choice — see CLAUDE.md native_decide policy).
if grep -Fq "Lean.ofReduce" "$OUT"; then
  echo "NOTICE: a checked theorem depends on Lean.ofReduce* (native_decide). Allowed under the bv_decide standard, but confirm it is intended." >&2
fi

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "OK: all $EXPECTED advertised theorems are axiom-clean ([propext, Classical.choice, Quot.sound])."
