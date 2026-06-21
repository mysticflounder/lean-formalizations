# Corollary 24 — the generic-rotation existence lemma (Edge B, `ShearExists.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in
an isolated worktree, ported + gated on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open MvPolynomial`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/ShearExists.lean`.

## Scope

The headline existence lemma of Edge B's generic-direction WLOG
(`docs/corollary24-generic-rotation-scope.md` §4, §7 item 4). This file is pure assembly:
it consumes the four already-landed, axiom-clean bricks (items 1–3 + the Irreducible row)
plus the repo's finite-avoidance pattern, and produces one existence statement. No new
analysis. The deliverable, with the exact required signature:

```lean
theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P
```

`edgeB_crossingInput` (item 5 / task #43) consumes this: it obtains `s`, then transfers the
incidence count back through the affine-invariant shear.

## Route (the §4 assembly)

Pick the good scalar `s` off the complement of a finite bad-scalar set `B₁ ∪ B₂`:

* **`B₁ := ⋃ h ∈ Γ, {s | pderiv (1 : Fin 2) (shearPoly s h) = 0}`** — per-curve
  `∂_y`-degeneracy roots. Each member finite by `partialY_shearPoly_finite_bad h (hpos h …)`
  (`ShearPartialY.lean`); the union over the finite family `Γ` finite by `Set.Finite.biUnion`.
* **`B₂ := ⋃ pq ∈ P.offDiag, {s | (sepPoly pq.1 pq.2).IsRoot s}`** — pairwise x-collision
  roots. For a pair `(p,q)`, the two points share their `T_s`-x-value iff `s` is a root of
  the univariate `sepPoly p q := C (p.1 − q.1) − C (p.2 − q.2)·X`. Nonzero on a distinct pair
  (`sepPoly_ne_zero`), so its root set is finite (`Polynomial.finite_setOf_isRoot`); union
  over `P.offDiag` finite by `Set.Finite.biUnion`.

`Set.Finite.exists_notMem` on `B₁ ∪ B₂` gives `s ∉ B₁ ∪ B₂`. The four clauses discharge:
`s ∉ B₁` ⟹ `∂_y ≠ 0`; degree clause = `shearPoly_totalDegree_le · hdeg`; irreducibility
clause = `irreducible_shearPoly_iff.mpr · hirr` (neither depends on the chosen `s`);
`s ∉ B₂` ⟹ the x-separation `InjOn` (a colliding distinct pair would put `s` in `B₂`).

## Declarations (3, all axiom-clean)

* `sepPoly (p q : ℝ × ℝ) : Polynomial ℝ` (`noncomputable def`) — the degree-`≤ 1`
  x-separation polynomial `C (p.1 − q.1) − C (p.2 − q.2)·X`.
* `sepPoly_eval` — `(sepPoly p q).eval s = (p.1 − q.1) − s·(p.2 − q.2)` (`simp` + `ring`).
* `sepPoly_ne_zero (hpq : p ≠ q)` — `sepPoly p q ≠ 0`: two-case coefficient argument
  (`p.2 = q.2 ⟹ p.1 ≠ q.1` so `coeff 0 ≠ 0`; else `coeff 1 = −(p.2 − q.2) ≠ 0`).
* `exists_good_shear` — the deliverable (assembly above).

## Encoding choice (vs. the route), sound

The x-separation bad set is built directly from the degree-`≤ 1` `sepPoly` rather than
through `momentPoly` (`GenericProjection.lean`). It reuses only the generic finiteness
pattern (`Polynomial.finite_setOf_isRoot` + `Set.Finite.biUnion` + `Finset.mem_offDiag`),
not `momentPoly` itself — the import is kept for the matching header but the `momentPoly`
machinery is not invoked. This makes `sepPoly_ne_zero` a two-line coefficient case split
instead of a moment-matrix nonvanishing argument.

## Gate

* Builds green in main standalone (8486 jobs) and via the `CrossingLemma.lean` aggregator
  (8522 jobs); `ShearExists.lean` is warning-free (the `unusedSimpArgs` linter note in the
  aggregator build is pre-existing drift in `PLCollarSeparation.lean:1341`, a different file).
* Independent `#print axioms` (`exists_good_shear`, `sepPoly_eval`, `sepPoly_ne_zero`) =
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`, no
  `Lean.ofReduceBool`, no custom axioms). `sepPoly` is a `noncomputable def`, no closure.
* No shipped `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `#print`.

## Remaining

The generic-rotation (shear WLOG) layer is now complete (items 1–4 + Irreducible).
Next: item 5 / task #43 — `edgeBMultigraph` + `edgeB_crossingInput`, the incidence
transfer-back consuming `exists_good_shear` (uses `curveArc` + `endAnchor_curveArc_*` + the
two `CurveArc` disjointness lemmas + `TwoDegreesOfFreedom`, `Theorem23.lean:45`).
