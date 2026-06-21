/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc

/-!
# Coordinate-chart bridge `Point2 ≃ₜ ℝ × ℝ` (`chart-bridge`)

`docs/corollary24-decomposition-spec.md` §0, §4 FLAG `chart-bridge`.

The generic monotone graph decomposition for Edge B has two coordinate
representations of the same plane curve:

* `Point2 = EuclideanSpace ℝ (Fin 2)` (an L² space) hosts every Bézout /
  singularity finiteness bound — `PlaneCurveZeroSet`, `SingularPointSet`,
  `factor_intersection_bound`, `finite_singularities_of_irreducible_bound`.
* `ℝ × ℝ` hosts the per-arc analytic machinery — `evalPlane`, the per-arc
  lemma in `MonotoneArc.lean`, the `lc-bound` strip-compactness in
  `StripCompact.lean`.

These are the **same curve** under the canonical linear homeomorphism
`E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`, `x ↦ (x 0, x 1)`. This file
constructs `E` and the transport lemmas that move a `Point2`-side
finiteness/compactness fact to an `ℝ × ℝ`-side band/strip fact:

* `chartEquiv` — the homeomorphism `E`, assembled from
  `EuclideanSpace.equiv (Fin 2) ℝ` (a continuous linear equiv to `Fin 2 → ℝ`)
  and `Homeomorph.finTwoArrow` (`(Fin 2 → ℝ) ≃ₜ ℝ × ℝ`).
* `chartEquiv_apply` / `chartEquiv_fst` / `chartEquiv_snd` — the coordinate
  formulas `(E x) = (x 0, x 1)`.
* `eval_eq_evalPlane_chart` — the **intertwining**:
  `MvPolynomial.eval (fun i => x i) p = evalPlane p (E x)`.
* `chartEquiv_image_planeCurveZeroSet` — the **curve-set transport**:
  `E '' PlaneCurveZeroSet p = evalPlaneZeroSet p`.
* `chartEquiv_image_finite_iff` / `chartEquiv_image_isCompact_iff` and their
  forward forms — `E` (a homeomorphism) preserves `Set.Finite` and `IsCompact`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### The homeomorphism `E : Point2 ≃ₜ ℝ × ℝ` -/

/-- The coordinate-chart homeomorphism `E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`,
`x ↦ (x 0, x 1)`. Assembled from `EuclideanSpace.equiv (Fin 2) ℝ` (the L²
structure forgotten to the bare function `Fin 2 → ℝ`, a continuous linear
equivalence) composed with `Homeomorph.finTwoArrow`. -/
noncomputable def chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow

@[inherit_doc] scoped notation "E" => chartEquiv

/-- `E x = (x 0, x 1)`. -/
@[simp] theorem chartEquiv_apply (x : Point2) : chartEquiv x = (x 0, x 1) := rfl

/-- First coordinate of `E x` is `x 0`. -/
@[simp] theorem chartEquiv_fst (x : Point2) : (chartEquiv x).1 = x 0 := rfl

/-- Second coordinate of `E x` is `x 1`. -/
@[simp] theorem chartEquiv_snd (x : Point2) : (chartEquiv x).2 = x 1 := rfl

/-- The inverse `E.symm (a, b)` has first coordinate `a`. -/
@[simp] theorem chartEquiv_symm_apply_zero (z : ℝ × ℝ) :
    (chartEquiv.symm z) 0 = z.1 := rfl

/-- The inverse `E.symm (a, b)` has second coordinate `b`. -/
@[simp] theorem chartEquiv_symm_apply_one (z : ℝ × ℝ) :
    (chartEquiv.symm z) 1 = z.2 := rfl

/-! ### Intertwining of the two evaluations -/

/-- **Intertwining.** For any plane polynomial `p` and any `Point2` point `x`,
the `Point2`-side evaluation `eval (fun i => x i) p` equals the `ℝ × ℝ`-side
evaluation `evalPlane p` at the chart image `E x`. This is the pointwise bridge
that makes the two coordinate representations interchangeable; the seed is
`Bezout.lean:654`. -/
theorem eval_eq_evalPlane_chart (p : PlanePoly) (x : Point2) :
    MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x) := by
  unfold evalPlane
  refine congrArg (fun f => MvPolynomial.eval f p) ?_
  funext i
  fin_cases i <;> simp

/-! ### Curve-set transport -/

/-- **Curve-set transport.** The image of the `Point2`-side curve
`PlaneCurveZeroSet p` under the chart `E` is the `ℝ × ℝ`-side curve
`evalPlaneZeroSet p`. -/
theorem chartEquiv_image_planeCurveZeroSet (p : PlanePoly) :
    chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_evalPlaneZeroSet, ← eval_eq_evalPlane_chart]
    exact hx
  · intro hz
    refine ⟨chartEquiv.symm z, ?_, by simp⟩
    rw [mem_PlaneCurveZeroSet, eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply]
    exact hz

/-- The chart pulls the `ℝ × ℝ`-side curve back to the `Point2`-side curve:
`E ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p`. -/
theorem chartEquiv_preimage_evalPlaneZeroSet (p : PlanePoly) :
    chartEquiv ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p := by
  ext x
  rw [Set.mem_preimage, mem_evalPlaneZeroSet, mem_PlaneCurveZeroSet,
    eval_eq_evalPlane_chart]

/-! ### Preservation of finiteness and compactness -/

/-- `E` preserves finiteness: `(E '' s).Finite ↔ s.Finite`. -/
theorem chartEquiv_image_finite_iff {s : Set Point2} :
    (chartEquiv '' s).Finite ↔ s.Finite :=
  Set.finite_image_iff (chartEquiv.injective.injOn)

/-- Forward transport of finiteness across the chart. -/
theorem chartEquiv_image_finite {s : Set Point2} (hs : s.Finite) :
    (chartEquiv '' s).Finite :=
  hs.image _

/-- `E` preserves compactness: `IsCompact (E '' s) ↔ IsCompact s`. -/
theorem chartEquiv_image_isCompact_iff {s : Set Point2} :
    IsCompact (chartEquiv '' s) ↔ IsCompact s := by
  constructor
  · intro h
    have := h.image chartEquiv.symm.continuous
    rwa [← Set.image_comp, chartEquiv.symm_comp_self, Set.image_id] at this
  · intro h
    exact h.image chartEquiv.continuous

/-- Forward transport of compactness across the chart. -/
theorem chartEquiv_image_isCompact {s : Set Point2} (hs : IsCompact s) :
    IsCompact (chartEquiv '' s) :=
  hs.image chartEquiv.continuous

/-! ### First-coordinate intertwining

The decomposition cuts on the x-axis (`docs/corollary24-decomposition-spec.md`
§1.1), so it needs the chart to intertwine the first coordinate: a curve point's
`Point2`-side `x 0` equals its `ℝ × ℝ`-side `.1`. This is `chartEquiv_fst`, named
here for use through `E` on transported sets. -/

/-- The chart intertwines the first coordinate (x-projection): the `ℝ × ℝ`-side
first coordinate of `E x` is the `Point2`-side `x 0`. -/
theorem chartEquiv_intertwines_fst (x : Point2) : (chartEquiv x).1 = x 0 :=
  chartEquiv_fst x

/-- The x-projection of the `Point2`-side curve (read through the chart) equals
the `ℝ × ℝ`-side x-projection of the transported curve. The set of x-values is the
same in both charts. -/
theorem chartEquiv_xproj_image (p : PlanePoly) :
    (fun x : Point2 => (chartEquiv x).1) '' PlaneCurveZeroSet p
      = Prod.fst '' evalPlaneZeroSet p := by
  rw [← chartEquiv_image_planeCurveZeroSet, ← Set.image_comp]
  rfl

end PachDeZeeuw.Algebraic
