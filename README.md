# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
intended as a clean, importable home for lemmas that are useful on their own —
ideally as mathlib contributions. Everything builds against **mathlib only**
(`import Mathlib`); there is no other dependency.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`, `lakefile.toml`).

## Provenance

Much of this code was salvaged from a now-dormant Erdős-Problem-98 formalization
project and re-extracted as standalone, mathlib-only modules. The source
project's own headline theorem was circular and is **not** included here. What is
kept is the *general* mathematics that stands on its own.

## Status legend

| Mark | Meaning |
|------|---------|
| ✅ **VERIFIED** | Live content is `sorry`-free and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` (Lean/mathlib core only — no `sorry`, no custom axioms). |
| 🟡 **PARTIAL** | Compiles, but some live declarations contain `sorry` (or a labelled conjectured residual). Honestly marked per-declaration. |
| ⚪ **STATEMENT-SURFACE** | A `Prop` is *stated* (`def … : Prop`) as an interface but **not proven**. Carries no mathematical content beyond the statement. |

## Verified content ✅

### `LeanFormalizations/Combinatorics/Additive/` — Balog–Szemerédi–Gowers

- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms:
  - `Finset.balog_szemeredi_gowers_asymmetric` (equal-cardinality two-set form),
  - `Finset.balog_szemeredi_gowers_symmetric` (single-set form),
  - `Finset.balog_szemeredi_gowers_asymmetric_explicit` (explicit
    polynomial-in-`η` constants).
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector.

mathlib (v4.30.0) does **not** contain BSG, so this fills a genuine gap, while
reusing mathlib's `Finset.addEnergy`. **All three theorems are axiom-clean.**

### `LeanFormalizations/Geometry/Euclidean/` — 2D two-point isometry classification

- **`IsometryClassification.lean`** — for `a b c d : EuclideanSpace ℝ (Fin 2)`
  with `a ≠ b` and `dist a b = dist c d`, the set of isometries sending `a ↦ c`,
  `b ↦ d` has `ncard ≤ 2` (`twoPoint_isometry_ncard_le_two`) and is `Finite`
  (`twoPoint_isometry_set_finite`), plus the underlying linear-isometry bounds.
  Proof: Mazur–Ulam reduction to the linear part, then a right-angle-rotation
  argument specific to two dimensions. **Axiom-clean.**

### `LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean` — real-algebraic-geometry core

A ~7000-line plane-algebraic-geometry development (namespace
`PachDeZeeuw.Algebraic`): resultants over `ℝ[x,y]`, common-component theory,
fiber-finiteness, and **explicit point-pair intersection bounds** — the genuine
Bézout-type content. Its **live content is `sorry`-free** (the remaining `sorry`s
are inside commented-out WIP blocks). Headline theorems confirmed axiom-clean:

- `resultant_ne_zero_of_fraction_coprime`,
  `resultant_ne_zero_of_isRelPrime_primitive_curry`
- `coeffline_nonvertical_pair_intersection_bound`,
  `zeroCurry_nonvertical_pair_intersection_bound`
- `fiber_ncard_le_max_totalDegree`, `ncard_coeff_roots_le_totalDegree`

> Note: this is the real proof content that the `Bezout` statement-surface below
> only *states*. It still contains large commented-out WIP blocks (slated for
> deletion) and uses project-flavored names pending the idiomaticity cleanup.

### Reproduce the verification

```bash
lake exe cache get
lake build
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms Finset.balog_szemeredi_gowers_asymmetric
#print axioms Finset.balog_szemeredi_gowers_symmetric
#print axioms Finset.balog_szemeredi_gowers_asymmetric_explicit
#print axioms EuclideanGeometry.twoPoint_isometry_ncard_le_two
#print axioms EuclideanGeometry.twoPoint_isometry_set_finite
#print axioms PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound
#print axioms PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry
EOF
```

(Or use `./lake-build.sh` — a memory-capped, single-flight wrapper.)

## Partial / work-in-progress 🟡 — `LeanFormalizations/PachDeZeeuw/`

A vendored, ported copy of the Pach–de Zeeuw "distinct distances on algebraic
curves" program. It **compiles** but is **not finished**: most modules carry
`sorry` or consume unproven statement-surfaces. The reduction theorems are
honestly stated as *conditional* results (`theorem … (h : SomeStatement) : …`).

- **`CrossingLemma/`** — the multigraph crossing lemma via combinatorial maps.
  The combinatorial-map / Euler-bound / edge-insertion machinery is largely
  `sorry`-free; the full crossing lemma bottoms out in a labelled conjectured
  geometric residual (`exists_twoSidedPartition_of_arc`, `sorry`). A separate
  `subsetAveraging_master` (`sorry`) is a documented dead-end, not used downstream.
- **`PachSharir/`** — the Pach–Sharir incidence bound (`theorem23`/`corollary24`
  contain `sorry`).
- **`AuxiliaryCurves`, `IncidenceBound`, `Theorem11`, `Theorem12`,
  `IncidenceAssembly`, `Basic`, `CurveInterface`** — the reduction chain to
  Theorem 1.1; conditional on the statement-surfaces, some `sorry`.

## Statement-surfaces ⚪ — `LeanFormalizations/PachDeZeeuw/`

These define a `Prop` but do **not** prove it — accepted classical inputs:

- **`Bezout.lean`** — `Bezout21Statement` (Bézout's inequality in `ℝ²`).
- **`MilnorThom.lean`** — `MilnorThom22Statement` (Oleĭnik–Petrovskiĭ / Milnor /
  Thom connected-components bound).
- **`CurveSymmetries.lean`** — `Lemma25Statement` / `Lemma26Statement`
  (symmetries of plane algebraic curves).

## Known idiomaticity gaps (pre-PR)

An audit flagged work needed before any mathlib PR (see `ROADMAP.md`): project
namespaces (`.PDZ`, `.ST`, `External`) and identifier jargon to rename, ~25 `def
… : Prop` statement-surfaces, dead source-project references in docstrings, and a
large commented-out WIP block in `AlgebraicPrelim.lean` to delete. The verified
core (BSG, geometry) is closest to PR-ready.

## Layout

```
LeanFormalizations.lean                    -- root aggregator (imports everything)
LeanFormalizations/
  Combinatorics/Additive/                  -- BSG ✅
  Geometry/Euclidean/                       -- isometry classification ✅
  PachDeZeeuw/                              -- Pach–de Zeeuw program
    AlgebraicPrelim.lean                    -- resultant/intersection core ✅
    Bezout.lean MilnorThom.lean CurveSymmetries.lean   -- statement-surfaces ⚪
    CrossingLemma/ PachSharir/              -- 🟡
    Theorem11 Theorem12 IncidenceBound IncidenceAssembly ...  -- 🟡
```

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
