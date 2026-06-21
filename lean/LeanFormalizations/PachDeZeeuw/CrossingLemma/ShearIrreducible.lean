/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear

/-!
# Irreducibility is preserved by the shear substitution (`generic-rotation` step)

The shear `shearPoly s` of `Shear.lean` (substitution `x ↦ x + s·y`, `y ↦ y` on
`PlanePoly = MvPolynomial (Fin 2) ℝ`) is an `ℝ`-algebra *equivalence*: its inverse is the
`(−s)`-shear (substitution `x ↦ x − s·y`, `y ↦ y`), because the two per-variable
substitutions are mutually inverse. As a multiplicative equivalence it transports
irreducibility in both directions, so a polynomial is irreducible iff its shear is.

This file ships exactly the `generic-rotation` deliverable
(`docs/corollary24-generic-rotation-scope.md` §3.4 row "Irreducible", §6, §7 item 4):

* `shearAlgEquiv s` — the shear packaged as `PlanePoly ≃ₐ[ℝ] PlanePoly` (the `AlgEquiv`
  whose underlying forward map is `aeval (shearVars s)` and whose inverse is
  `aeval (shearVars (-s))`), via `AlgEquiv.ofAlgHom`.
* `shearAlgEquiv_apply` — the coercion of `shearAlgEquiv s` agrees with `shearPoly s`.
* `irreducible_shearPoly_iff` — `Irreducible (shearPoly s h) ↔ Irreducible h`.

The downstream `exists_good_shear` consumes the `←`/`.mpr` direction
(`Irreducible h → Irreducible (shearPoly s h)`); the `AlgEquiv` gives the full iff for free.

The irreducible-transfer step is `MulEquiv.irreducible_iff` (an `AlgEquiv` is a
`MulEquivClass`, and irreducibility is preserved by multiplicative equivalences — mathlib
`Algebra.Group.Irreducible.Lemmas`, of which `Irreducible.map` is the forward direction).

All names live in `PachDeZeeuw.Algebraic`, so `PlanePoly`, `shearVars`, `shearPoly`
resolve unqualified (matching `Shear`).
-/

namespace PachDeZeeuw.Algebraic

open MvPolynomial

/-- The two `shearVars` substitutions with opposite signs cancel on each variable: if
`a + b = 0` then `aeval (shearVars a) (shearVars b i) = X i`. This is the per-variable
inverse computation underlying both `comp = id` obligations of `shearAlgEquiv`.

For `i = 0`: `aeval (shearVars a) (X 0 + C b · X 1) = (X 0 + C a · X 1) + C b · X 1`, and
`C b = − C a` (since `b = −a`), so the `X 1` terms cancel to `X 0`. For `i = 1`:
`aeval (shearVars a) (X 1) = X 1`. -/
lemma aeval_shearVars_shearVars (a b : ℝ) (hab : a + b = 0) (i : Fin 2) :
    aeval (shearVars a) (shearVars b i) = (X i : PlanePoly) := by
  obtain rfl : b = -a := by linarith
  fin_cases i
  · show aeval (shearVars a) (X 0 + C (-a) * X 1) = X 0
    rw [map_add, map_mul, aeval_X, aeval_X, aeval_C, algebraMap_eq, C_neg]
    show (X 0 + C a * X 1) + (- C a) * X 1 = (X 0 : PlanePoly)
    ring
  · show aeval (shearVars a) (X 1) = X 1
    rw [aeval_X]; rfl

/-- The forward∘inverse composition of the shear algebra homs is the identity: the
`s`-shear after the `(−s)`-shear. Reduced to `aeval_shearVars_shearVars` on each `X i`. -/
lemma shearAlgHom_comp_inv (s : ℝ) :
    (aeval (shearVars s)).comp (aeval (shearVars (-s))) = AlgHom.id ℝ PlanePoly := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
  exact aeval_shearVars_shearVars s (-s) (by ring) i

/-- The inverse∘forward composition of the shear algebra homs is the identity: the
`(−s)`-shear after the `s`-shear. The sign-swapped companion of `shearAlgHom_comp_inv`. -/
lemma shearAlgHom_inv_comp (s : ℝ) :
    (aeval (shearVars (-s))).comp (aeval (shearVars s)) = AlgHom.id ℝ PlanePoly := by
  apply algHom_ext
  intro i
  rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
  exact aeval_shearVars_shearVars (-s) s (by ring) i

/-- The shear packaged as an `ℝ`-algebra equivalence of `PlanePoly`: forward map
`aeval (shearVars s)` (the `s`-shear `shearPoly s`), inverse map `aeval (shearVars (-s))`
(the `(−s)`-shear). The two `comp = id` obligations are `shearAlgHom_comp_inv` and
`shearAlgHom_inv_comp`. -/
noncomputable def shearAlgEquiv (s : ℝ) : PlanePoly ≃ₐ[ℝ] PlanePoly :=
  AlgEquiv.ofAlgHom (aeval (shearVars s)) (aeval (shearVars (-s)))
    (shearAlgHom_comp_inv s) (shearAlgHom_inv_comp s)

/-- The coercion of `shearAlgEquiv s` is `shearPoly s`: applying the equivalence is the
forward algebra hom `aeval (shearVars s)`, which is `shearPoly s` by definition. -/
@[simp] lemma shearAlgEquiv_apply (s : ℝ) (h : PlanePoly) :
    shearAlgEquiv s h = shearPoly s h := by
  rw [shearAlgEquiv, AlgEquiv.ofAlgHom_apply]
  rfl

/-- **The irreducibility transfer.** A polynomial is irreducible iff its shear is. The
shear is the multiplicative equivalence `shearAlgEquiv s`, and irreducibility is preserved
by multiplicative equivalences (`MulEquiv.irreducible_iff`). The `←`/`.mpr` direction
(`Irreducible h → Irreducible (shearPoly s h)`) is what `exists_good_shear` consumes. -/
theorem irreducible_shearPoly_iff (s : ℝ) (h : PlanePoly) :
    Irreducible (shearPoly s h) ↔ Irreducible h := by
  rw [← shearAlgEquiv_apply s h]
  exact MulEquiv.irreducible_iff (shearAlgEquiv s)

end PachDeZeeuw.Algebraic
