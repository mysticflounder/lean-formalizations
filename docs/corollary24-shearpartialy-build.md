# Corollary 24 — finite bad-shear set (∂_y ≠ 0 chain) (Edge B, `ShearPartialY.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in
an isolated worktree, ported + gated on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open MvPolynomial`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/ShearPartialY.lean`.

## Scope

The per-curve "bad scalar set is finite" brick of Edge B's generic-direction WLOG
(`docs/corollary24-generic-rotation-scope.md` §3.2, §7 item 3). The deliverable:

```lean
theorem partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :
    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite
```

The downstream `exists_good_shear` (§7 item 4, not yet landed) `Set.Finite.biUnion`s
this over the finite curve family and picks `s` in the complement
(`Set.Finite.exists_notMem`), so the finite-set shape is exactly what is consumed.

## Route (scope §3.2, EMPIRICALLY VERIFIED in `/tmp/shear_fix.py`)

Let `D := h.totalDegree ≥ 1` (so `h ≠ 0`). Under the shear `x ↦ x + s·y`, `y ↦ y`,
the coefficient of the pure `y^D` monomial `Finsupp.single 1 D` in `shearPoly s h`, as a
function of `s`, is the univariate real polynomial `P(s) = ∑_{a+b=D} (coeff x^a y^b in h)·s^a
= H(s,1)` (the top form `H` at `(s,1)`). Only top-degree monomials contribute a pure `y^D`
term; distinct ones have distinct `a`, so `P = 0 ⟺ H = 0`, and `H ≠ 0` (since `h ≠ 0`).
`P` is a nonzero real univariate polynomial, hence finitely many roots; off them the `y^D`
coefficient is `≠ 0`, forcing `pderiv 1 (shearPoly s h) ≠ 0`. So the bad set `⊆ {roots of P}`.

## Declarations

Public (exported for the downstream assembly):

* `shearTopPoly h : Polynomial ℝ` — the `s`-polynomial `P(s) = H(s,1)`, built as an explicit
  `∑_{m ∈ h.support, m 0 + m 1 = D} C (coeff m h) · X^(m 0)`.
* `coeff_yD_shear_eq_eval` — the coefficient identity
  `coeff (single 1 D) (shearPoly s h) = (shearTopPoly h).eval s`.
* `shearTopPoly_ne_zero (h ≠ 0)` — `P ≠ 0`: the top monomial `m₀` (degree `D`, `coeff ≠ 0`)
  is the unique degree-`D` monomial with that `x`-exponent, so `P.coeff (m₀ 0) = coeff m₀ h ≠ 0`.
* `partialY_shearPoly_finite_bad` — the deliverable: bad set `⊆` root set of `P`, finite via
  `Polynomial.finite_setOf_isRoot` + `Set.Finite.subset`.

Private support: `msum_eq`, `sum_support_single` (`Fin 2` finsupp-degree bridges);
`coeff_single_one_pow` (`coeff (single 1 a) ((X₀+s·X₁)^a) = s^a`, induction);
`shear_monomial`, `coeff_yD_shear_monomial`, `coeff_yD_shear_monomial_lt` (per-monomial
shear coefficients); `coeff_X_mul_pderiv` (`coeff m (X i · ∂ᵢ g) = (m i) • coeff m g`),
`coeff_yD_eq_zero_of_pderiv_eq_zero` (the `pderiv → y^D coeff = 0` bridge).

## Encoding choices (vs. the route's suggested path), both sound

1. `P` is the explicit `Finset.sum` above rather than `aeval ![X,1] (homogeneousComponent D h)`.
   This makes both the coefficient identity and `P ≠ 0` provable from one per-monomial
   expansion (mathlib has no packaged "`homogeneousComponent` nonzero at `totalDegree`" lemma).
2. "`y^D` coeff ≠ 0 ⟹ pderiv 1 ≠ 0" goes through `X 1 * pderiv 1 g` (via the mathlib-present
   `X_mul_pderiv_monomial`, extended by linearity in `coeff_X_mul_pderiv`) rather than
   `Curry1`/`yLeadCoeff` — mathlib has no `coeff`-of-`pderiv` lemma.

The `coeff_yD_shear_monomial_lt` step reuses the landed GR-1 bound `shearPoly_totalDegree_le`
(`Shear.lean`): the shear does not raise total degree, so a degree-`< D` monomial's image has
total degree `< D` and zero `y^D` coefficient.

## Gate

* Builds green in main via the `CrossingLemma.lean` aggregator (8520 jobs); warning-free.
* Independent `#print axioms` (`partialY_shearPoly_finite_bad`, `coeff_yD_shear_eq_eval`,
  `shearTopPoly_ne_zero`) = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no
  `native_decide`, no `Lean.ofReduceBool`, no custom axioms).
* No shipped `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `#print`.

## Remaining for the generic-rotation tail

* `exists_good_shear` (§7 item 4): assemble this finite bad set + the separation root sets +
  the GR-1 degree bound + `irreducible_shearPoly_iff` over the repo's finite-avoidance engine
  (`GenericProjection.lean:92–117`). Then task #43 (`edgeBMultigraph`).
