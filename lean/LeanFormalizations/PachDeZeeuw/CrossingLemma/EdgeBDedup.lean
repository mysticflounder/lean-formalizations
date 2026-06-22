/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc

/-!
# Edge-B deduplication lemma (Lemma A)

Distinct real zero sets imply non-associated polynomials.

This is the algebraic engine for deduplicating irreducible curve carriers by
their real zero set in `ℝ × ℝ`. The argument is pure ring-hom algebra:
evaluation at a fixed point is a ring homomorphism, ring homs send units to
units, and units in the field ℝ are nonzero.
-/

namespace PachDeZeeuw.Algebraic

-- Abbreviation for the evaluation map used in evalPlane.
private abbrev evalCoeff (xy : ℝ × ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then xy.1 else xy.2

/-- If two plane polynomials have distinct real zero sets, they are not
associated. The proof goes via the contrapositive: if `h` and `k` are
associated (via a unit `u` with `h * u = k`), then for any point `xy`,
evaluation sends the unit equation to a unit-multiple relation in ℝ, so
`evalPlane h xy = 0 ↔ evalPlane k xy = 0`, giving equal zero sets. -/
lemma not_associated_of_ne_evalPlaneZeroSet
    (h k : PlanePoly) (hne : evalPlaneZeroSet h ≠ evalPlaneZeroSet k) :
    ¬ Associated h k := by
  intro hassoc
  apply hne
  obtain ⟨u, hu⟩ := hassoc
  -- hu : h * ↑u = k
  ext xy
  simp only [mem_evalPlaneZeroSet, evalPlane]
  -- Goal: MvPolynomial.eval (evalCoeff xy) h = 0
  --     ↔ MvPolynomial.eval (evalCoeff xy) k = 0
  -- The evaluation ring hom sends the unit ↑u to a unit in ℝ, hence nonzero.
  have hunit_val : MvPolynomial.eval (evalCoeff xy) (↑u : PlanePoly) ≠ 0 := by
    have hunit : IsUnit (MvPolynomial.eval (evalCoeff xy) (↑u : PlanePoly)) :=
      IsUnit.map (MvPolynomial.eval (evalCoeff xy)).toMonoidHom (Units.isUnit u)
    exact hunit.ne_zero
  -- k = h * ↑u, so eval k = eval h * eval u
  have hk_eq : MvPolynomial.eval (evalCoeff xy) k =
      MvPolynomial.eval (evalCoeff xy) h * MvPolynomial.eval (evalCoeff xy) (↑u : PlanePoly) := by
    rw [← hu, map_mul]
  rw [hk_eq]
  constructor
  · intro heq
    simp [heq]
  · intro hprod
    rcases mul_eq_zero.mp hprod with h0 | hu0
    · exact h0
    · exact absurd hu0 hunit_val

end PachDeZeeuw.Algebraic
