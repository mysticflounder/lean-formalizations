# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
intended as a clean, importable home for lemmas that are useful on their own —
ideally as mathlib contributions. Everything here is mathlib-only (`import
Mathlib`), with no other dependency.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`, `lakefile.toml`).

## Verified content

### `LeanFormalizations/Combinatorics/Additive/` — Balog–Szemerédi–Gowers ✅

- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms:
  - `Finset.balog_szemeredi_gowers_asymmetric` (equal-cardinality two-set form),
  - `Finset.balog_szemeredi_gowers_symmetric` (single-set form),
  - `Finset.balog_szemeredi_gowers_asymmetric_explicit` (explicit
    polynomial-in-`η` constants).
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector.

mathlib (v4.30.0) does **not** contain BSG — confirmed by search (no
`balog`/`szemeredi_gowers`/`bsg` anywhere) — so this fills a genuine gap, while
reusing mathlib's `Finset.addEnergy` and `Finset.addConvolution`.

### `LeanFormalizations/Geometry/Euclidean/` — 2D two-point isometry classification ✅

- **`IsometryClassification.lean`** — for points `a b c d : EuclideanSpace ℝ
  (Fin 2)` with `a ≠ b` and `dist a b = dist c d`, the set of isometries `g`
  sending `a ↦ c`, `b ↦ d` has `ncard ≤ 2` (`twoPoint_isometry_ncard_le_two`)
  and is `Finite` (`twoPoint_isometry_set_finite`), plus the underlying
  linear-isometry bounds. Proof: Mazur–Ulam reduction to the linear part, then a
  right-angle-rotation argument specific to two dimensions.

**Status: VERIFIED, axiom-clean.** Every main theorem reports exactly
`[propext, Classical.choice, Quot.sound]` — the Lean/mathlib core axioms, with
**no `sorry` and no custom axioms.**

Reproduce:

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
EOF
```

## Roadmap

See `ROADMAP.md` for upcoming work (source-paper correctness audit, an
advertising write-up, and mathlib-PR prep).

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
</content>
