#!/usr/bin/env bash
# Offline pre-flight for the comparator auditability gate. This does NOT replace
# a real leanprover/comparator run (which re-exports the closure through the
# nanoda and Lean default kernels and checks statement identity between the two
# modules — see comparator/README.md and .github/workflows/comparator.yml). It
# is the cheap check every commit can run.
#
# The comparator set is split into one configuration per formalization. Each
# group has its own directory comparator/<Group>/ that contains:
#   Challenge.lean   — mathlib-only sorry stubs (must elaborate w/ Mathlib alone)
#   Solution.lean    — project proofs discharging each stub, under the SAME
#                      top-level theorem names the group config lists
#   config.json      — the leanprover/comparator configuration for the group
#   axiom-audit.lean — one `#print axioms` line per theorem of the group
#
# The script does two steps for each group:
#   1. Build the group library (this builds the Challenge and Solution roots).
#   2. Run the axiom audit: every Solution theorem's #print axioms closure must
#      be a subset of {propext, Classical.choice, Quot.sound}.
#
# Statement identity between Challenge and Solution is checked by the real
# comparator run, not here. The script checks every group, records the groups
# that fail, and exits 0 only if all checked groups pass.
#
# Usage:
#   comparator/check-conformance.sh                 # check all groups
#   comparator/check-conformance.sh Bsg TreeOrder   # check only these groups
set -euo pipefail

# The full group list. To add a group, add its name to this list.
ALL_GROUPS=(
  Bsg
  Isometry2D
  SmallCombinatorics
  ConvexSlicing
  TreeOrder
  DistinctDistances
  NearEnemy
  PachDeZeeuw
  PlanarMaps
)

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Positional arguments select the groups. No arguments means all groups.
if [[ "$#" -gt 0 ]]; then
  SELECTED=("$@")
else
  SELECTED=("${ALL_GROUPS[@]}")
fi

for g in "${SELECTED[@]}"; do
  if [[ ! -d "comparator/$g" ]]; then
    echo "unknown group: $g (there is no directory comparator/$g)" >&2
    exit 2
  fi
done

WORK="$(mktemp -d "${TMPDIR:-/tmp}/comparator-audit.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

FAILED=()
TOTAL=0

for g in "${SELECTED[@]}"; do
  AUDIT="comparator/$g/axiom-audit.lean"
  NAMES="$(grep -cE '^#print axioms' "$AUDIT" || true)"
  OUT="$WORK/$g.out"
  fail=0

  echo "== $g: building Challenge / Solution =="
  if ! ./lake-build.sh "$g"; then
    echo "FAIL[$g]: the group library did not build." >&2
    FAILED+=("$g")
    continue
  fi

  echo "== $g: axiom audit ($NAMES theorems) =="
  if ! lake env lean "$AUDIT" >"$OUT" 2>&1; then
    echo "FAIL[$g]: $AUDIT errored (renamed theorem? library not built?)" >&2
    cat "$OUT" >&2
    FAILED+=("$g")
    continue
  fi

  if grep -Eiq "sorryAx|unknown identifier|unknown constant|error:" "$OUT"; then
    echo "FAIL[$g]: audit reported sorry/error:" >&2
    grep -Ei "sorryAx|unknown identifier|unknown constant|error:" "$OUT" >&2
    fail=1
  fi
  if grep -Fq "Lean.ofReduce" "$OUT"; then
    echo "FAIL[$g]: a Solution theorem uses native_decide (Lean.ofReduce*); not permitted in this comparator set." >&2
    fail=1
  fi

  GOT="$(grep -Fc "depend" "$OUT" || true)"
  if [[ "$GOT" -ne "$NAMES" ]]; then
    echo "FAIL[$g]: expected $NAMES axiom reports, got $GOT." >&2
    fail=1
  fi

  if [[ "$fail" -ne 0 ]]; then
    cat "$OUT" >&2
    FAILED+=("$g")
    continue
  fi

  TOTAL=$((TOTAL + NAMES))
  echo "OK[$g]: $NAMES theorems build and are axiom-clean."
done

if [[ "${#FAILED[@]}" -ne 0 ]]; then
  echo "FAIL: ${#FAILED[@]} of ${#SELECTED[@]} groups failed: ${FAILED[*]}" >&2
  exit 1
fi

echo "OK: $TOTAL comparator theorems in ${#SELECTED[@]} groups build and are axiom-clean"
echo "    (subset of {propext, Classical.choice, Quot.sound}; no sorryAx, no native_decide)."
echo "    Statement identity (Challenge ≡ Solution) is verified by the leanprover/comparator run."
