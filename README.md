# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
salvaged from a now-dead Erdős-Problem-98 formalization project. The aim is a
clean home for lemmas that are useful **independently of that project** — ideally
as mathlib contributions.

## Verified content

### `LeanFormalizations/Combinatorics/Additive/` — Balog–Szemerédi–Gowers ✅

- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms: asymmetric,
  symmetric, and with explicit polynomial-in-`η` constants.
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector.

**Status: VERIFIED.** Builds against **mathlib v4.27.0 only** (no other
dependency), and

```
#print axioms Erdos98Proof.External.balog_szemeredi_gowers_asymmetric
#print axioms Erdos98Proof.External.balog_szemeredi_gowers_symmetric
#print axioms Erdos98Proof.External.balog_szemeredi_gowers_asymmetric_explicit
```

each reports exactly `[propext, Classical.choice, Quot.sound]` — the Lean/mathlib
core axioms, **no `sorry`, no custom axioms.** mathlib (v4.27.0) does **not**
contain BSG, so this fills a genuine gap. This is the primary salvage candidate
and is mathlib-PR-worthy (pending a novelty re-check against mathlib master and a
namespace rename — see TODO).

Reproduce:

```bash
lake exe cache get
lake build
lake env lean - <<'EOF'
import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers
#print axioms Erdos98Proof.External.balog_szemeredi_gowers_asymmetric
EOF
```

## Quarantined — not yet ported (`unported/`)

- **`unported/Geometry/Euclidean/`** — a plane-isometry rigidity result (the set
  of isometries of the plane sending one nondegenerate ordered pair to another
  has `ncard ≤ 2` / is `Finite`), plus its `Foundation`. **Not in the build.**
  On inspection it is *not* cleanly mathlib-only: `Foundation.lean` defines the
  ambient plane via the `ℝ²` notation and an `hIndexed` that references the
  Erdős-98 predicates `InGeneralPosition` / `distinctDistances` — all supplied by
  the source project's `formal_conjectures` fork, not mathlib. Porting it (replace
  `ℝ²` with `EuclideanSpace ℝ (Fin 2)`, drop the Erdős-98–specific `Config`/
  `hIndexed`, re-check `IsometryClassification` for other fork dependencies) is a
  small refactor, not done yet. The underlying rigidity lemma is general and may
  be worth a mathlib contribution, but its novelty vs. mathlib is unverified.

## Provenance

Recovered from the source project's git history at commit `0daa7b1` (the parent
of the first deletion commit `bc4c5c9` in the "strengthened ES-GK" incident). The
source project's own headline theorem was circular and is **not** included here.

## TODO

1. ~~Build standalone + `#print axioms`~~ — **done** for BSG (mathlib-only,
   axiom-clean).
2. ~~Strip the `formal_conjectures` dependency~~ — **done** for the BSG cluster
   (now `import Mathlib`).
3. **Rename the `Erdos98Proof` namespace** to a neutral one before any PR.
4. **mathlib-master novelty check** for BSG (it may have landed upstream since
   v4.27.0).
5. **Port the geometry cluster** out of `unported/` to mathlib-only, or drop it.
6. Clean up the four unused-variable lint warnings in `BalogSzemerediGowers.lean`.

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
