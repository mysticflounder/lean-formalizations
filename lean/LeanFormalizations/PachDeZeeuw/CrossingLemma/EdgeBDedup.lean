/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.ChartBridge

/-!
# Edge-B deduplication lemma (Lemma A) and curve–curve clause (deduped_cc)

This file contains two lemmas:

**Lemma A** (`not_associated_of_ne_evalPlaneZeroSet`): Distinct real zero sets
in `ℝ × ℝ` imply non-associated polynomials. The argument is pure ring-hom
algebra: evaluation at a fixed point is a ring homomorphism, ring homs send
units to units, and units in the field ℝ are nonzero.

**deduped_cc** (`planeCurveZeroSet_inter_encard_le`): Two distinct irreducible
plane curves of degree ≤ d meet in at most `(2d+1)^4` points (as `encard`).
The proof composes Lemma A, the chart bridge, and
`irreducible_pair_intersection_bound` (Bézout), then converts from `ncard` to
`encard` via `Set.Finite.cast_ncard_eq` and `exact_mod_cast`.
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

/-! ### Curve–curve intersection bound (deduped_cc) -/

/-- **Curve–curve clause.** Two distinct irreducible plane polynomials of degree ≤ d
have at most `(2·d+1)^4` intersection points in `EuclideanSpace ℝ (Fin 2)`, as an
`encard` bound.

Proof:
1. Bridge from `PlaneCurveZeroSet` inequality to `evalPlaneZeroSet` inequality using
   `chartEquiv_image_planeCurveZeroSet` (since `chartEquiv` is injective, image is
   injective on sets, so equal images ↔ equal source sets).
2. Apply `not_associated_of_ne_evalPlaneZeroSet` to get `¬ Associated K₁ K₂`.
3. Apply `irreducible_pair_intersection_bound` (Bézout) at `d₁ = d₂ = d` to obtain
   `s.Finite` and `s.ncard ≤ (d + d + 1)^4`.
4. Note `d + d + 1 = 2·d + 1` by `omega`.
5. Convert via `Set.Finite.cast_ncard_eq` and `exact_mod_cast`. -/
lemma planeCurveZeroSet_inter_encard_le {d : ℕ} (K₁ K₂ : PlanePoly)
    (hirr₁ : Irreducible K₁) (hirr₂ : Irreducible K₂)
    (hd₁ : K₁.totalDegree ≤ d) (hd₂ : K₂.totalDegree ≤ d)
    (hne : PlaneCurveZeroSet K₁ ≠ PlaneCurveZeroSet K₂) :
    (PlaneCurveZeroSet K₁ ∩ PlaneCurveZeroSet K₂).encard ≤ ((2 * d + 1) ^ 4 : ℕ∞) := by
  -- Step 1: Derive evalPlaneZeroSet K₁ ≠ evalPlaneZeroSet K₂ from the PlaneCurveZeroSet
  -- inequality, using that chartEquiv '' is injective on sets.
  have hne_eval : evalPlaneZeroSet K₁ ≠ evalPlaneZeroSet K₂ := by
    intro heq
    apply hne
    have h1 := chartEquiv_image_planeCurveZeroSet K₁
    have h2 := chartEquiv_image_planeCurveZeroSet K₂
    exact Set.image_injective.mpr chartEquiv.injective (h1.trans (heq.trans h2.symm))
  -- Step 2: Apply Lemma A to get ¬ Associated K₁ K₂.
  have hnot : ¬ Associated K₁ K₂ := not_associated_of_ne_evalPlaneZeroSet K₁ K₂ hne_eval
  -- Step 3: Apply Bézout bound at d₁ = d₂ = d.
  have hbez := irreducible_pair_intersection_bound K₁ K₂ hirr₁ hirr₂ hd₁ hd₂ hnot
  obtain ⟨hfin, hncard⟩ := hbez
  -- Step 4: Note d + d + 1 = 2 * d + 1.
  have hexp : d + d + 1 = 2 * d + 1 := by omega
  rw [hexp] at hncard
  -- Step 5: Convert ncard to encard.
  -- hfin.cast_ncard_eq : ↑s.ncard = s.encard (as ℕ∞), so s.encard = ↑s.ncard.
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast hncard

end PachDeZeeuw.Algebraic
