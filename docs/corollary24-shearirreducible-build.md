# Corollary 24 — irreducibility preserved by the shear (Edge B, `ShearIrreducible.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in
an isolated worktree, ported + gated on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open MvPolynomial`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/ShearIrreducible.lean`.

## Scope

The irreducibility-transfer brick of Edge B's generic-direction WLOG
(`docs/corollary24-generic-rotation-scope.md` §3.4 row "Irreducible", §6, §7). The
deliverable:

```lean
theorem irreducible_shearPoly_iff (s : ℝ) (h : PlanePoly) :
    Irreducible (shearPoly s h) ↔ Irreducible h
```

`exists_good_shear` consumes the `.mpr` direction (`Irreducible h → Irreducible (shearPoly s h)`);
the `AlgEquiv` route gives the full iff for free.

## Route (fully scoped recipe)

`shearPoly s = aeval (shearVars s)` (`Shear.lean`) is an `ℝ`-algebra **equivalence** whose
inverse is the `(−s)`-shear, because the two per-variable substitutions cancel:
`aeval (shearVars s) (shearVars (−s) i) = X i` for each `i` (for `i = 0`, the `X 1` terms
cancel via `C (−s) = − C s`; `i = 1` is `X 1 ↦ X 1`). Irreducibility transfers across a
multiplicative equivalence.

## Declarations (6, all axiom-clean)

* `aeval_shearVars_shearVars (a b) (a + b = 0) (i)` — the per-variable cancellation
  `aeval (shearVars a) (shearVars b i) = X i`. `fin_cases i`; `map_add/map_mul/aeval_X/aeval_C`,
  `C_neg`, `ring`.
* `shearAlgHom_comp_inv s`, `shearAlgHom_inv_comp s` — the two `comp = id` obligations,
  reduced to the cancellation on each `X i` via `algHom_ext`.
* `shearAlgEquiv s : PlanePoly ≃ₐ[ℝ] PlanePoly` — `AlgEquiv.ofAlgHom (aeval (shearVars s))
  (aeval (shearVars (-s)))` with the two obligations above.
* `shearAlgEquiv_apply` (`@[simp]`) — `shearAlgEquiv s h = shearPoly s h`
  (`AlgEquiv.ofAlgHom_apply` + `rfl`).
* `irreducible_shearPoly_iff` — `rw [← shearAlgEquiv_apply]; exact MulEquiv.irreducible_iff
  (shearAlgEquiv s)`.

## Irreducible-transfer lemma

`MulEquiv.irreducible_iff (f : F) : Irreducible (f x) ↔ Irreducible x` (mathlib
`Algebra.Group.Irreducible.Lemmas`), applied with `f := shearAlgEquiv s` — an `AlgEquiv`
satisfies `MulEquivClass`, so it is passed directly (no `.toMulEquiv` needed).
`Irreducible.map` is the `.mp` direction of this iff.

## Gate

* Builds green in main via the `CrossingLemma.lean` aggregator (8520 jobs); warning-free.
* Independent `#print axioms` (`irreducible_shearPoly_iff`, `shearAlgEquiv`, `shearAlgEquiv_apply`)
  = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`, no
  `Lean.ofReduceBool`, no custom axioms).
* No shipped `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `#print`.

## Remaining for the generic-rotation tail

* `exists_good_shear` (§7 item 4): combine `irreducible_shearPoly_iff.mpr` with the
  `ShearPartialY.lean` finite bad set + the GR-1 degree bound + the separation root sets over
  the repo's finite-avoidance engine. Then task #43 (`edgeBMultigraph`).
