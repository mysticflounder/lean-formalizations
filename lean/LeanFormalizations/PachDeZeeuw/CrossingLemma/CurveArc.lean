/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma

/-!
# The connecting curve arc and its interior-disjointness (Edge B, export-4b)

This file realizes the structural foundation the Edge-B assembly needs to turn an
`export_4a_edge_is_arc` graph `χ` into a `CrossingLemma.SimpleCurveArc`, plus the
interior-disjointness facts (`docs/corollary24-E1E2-assembly-design.md` §4.3,
FLAG `export-4b`). It is the curve analogue of `segmentArc` and
`edgesOnLine_interior_disjoint` from `PachSharir/SzemerediTrotter.lean`.

* `curveArc χ p q hx hcont` — the `SimpleCurveArc` whose `param` reparametrizes
  `[0,1] → [p.1, q.1]` linearly and traces the graph `(x, χ x)`. Continuity is the
  reparametrization-composition idiom (`ContinuousOn.comp_continuous`), exactly as
  in `LocalArc.lean`; injectivity is read off the first coordinate alone (the
  strictly monotone reparametrization), which is *easier* than `segmentArc`'s
  (a graph is automatically injective in `x`, no degeneracy case).
* `endAnchor_curveArc_false/true` — the arc joins its declared endpoints `p`, `q`
  (the `ArcsJoinEndpoints` ingredient).
* `curveArc_interior_xproj` — every interior point is `(x, χ x)` with the `x`-value
  *strictly* between `p.1` and `q.1` (the curve analogue of `lineKey_of_mem_interior`,
  with the first coordinate playing `lineKey`'s role).
* `curveArc_interior_disjoint_of_disjoint_Ioo` — two arcs with disjoint open
  `x`-projections have disjoint interiors. This single lemma covers both the
  same-class consecutive-edge case (separated by `edgesOnSheet` sortedness) and the
  export-4b *different good interval* case (good intervals are disjoint).
* `export_4b_interior_disjoint` — the export-4b *same interval, different rank* case:
  over one good interval, two arcs of distinct sheet rank `j ≠ j'` cannot share an
  interior point, because the rank is constant along each arc
  (`sheetRank_const_of_continuous_onCurve`) and a shared point would force `j = j'`.

No new analysis: the analytic content is the landed
`sheetRank_const_of_continuous_onCurve`; the rest is reparametrization bookkeeping.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma

/-- **The connecting curve arc.** For a continuous graph `χ` on `[p.1, q.1]` with
`p.1 < q.1`, the `SimpleCurveArc` tracing `(x, χ x)` over a linear reparametrization
`[0,1] → [p.1, q.1]`. The endpoint matching `χ p.1 = p.2`, `χ q.1 = q.2` is *not*
required to build the arc (only to anchor its ends — see `endAnchor_curveArc_*`). -/
noncomputable def curveArc (χ : ℝ → ℝ) (p q : ℝ × ℝ) (hx : p.1 < q.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1)) : SimpleCurveArc where
  param := fun t => ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1,
                     χ ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1))
  cont := by
    have hmem : ∀ t : Set.Icc (0 : ℝ) 1,
        (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1 ∈ Set.Icc p.1 q.1 := by
      intro t
      obtain ⟨ht0, ht1⟩ := t.2
      exact ⟨by nlinarith [hx.le], by nlinarith [hx.le]⟩
    have hxof : Continuous
        (fun t : Set.Icc (0 : ℝ) 1 => (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1) := by
      fun_prop
    exact hxof.prodMk (hcont.comp_continuous hxof hmem)
  inj := by
    intro s t hst
    have h1 : (1 - (s : ℝ)) * p.1 + (s : ℝ) * q.1
            = (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1 := congrArg Prod.fst hst
    have hne : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    have hkey : (s : ℝ) * (q.1 - p.1) = (t : ℝ) * (q.1 - p.1) := by linear_combination h1
    exact Subtype.ext (mul_right_cancel₀ hne hkey)

/-- The `param` of `curveArc` evaluated explicitly. -/
@[simp] lemma curveArc_param (χ : ℝ → ℝ) (p q : ℝ × ℝ) (hx : p.1 < q.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1)) (t : Set.Icc (0 : ℝ) 1) :
    (curveArc χ p q hx hcont).param t
      = ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1,
         χ ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1)) := rfl

/-- **End `false` of `curveArc` is `p`** (when `χ` pins `p.1 ↦ p.2`). -/
@[simp] lemma endAnchor_curveArc_false (χ : ℝ → ℝ) (p q : ℝ × ℝ) (hx : p.1 < q.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1)) (hχp : χ p.1 = p.2) :
    endAnchor (curveArc χ p q hx hcont) false = p := by
  unfold endAnchor endParam
  simp only [Bool.false_eq_true, if_false, curveArc_param]
  ext <;> simp [hχp]

/-- **End `true` of `curveArc` is `q`** (when `χ` pins `q.1 ↦ q.2`). -/
@[simp] lemma endAnchor_curveArc_true (χ : ℝ → ℝ) (p q : ℝ × ℝ) (hx : p.1 < q.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1)) (hχq : χ q.1 = q.2) :
    endAnchor (curveArc χ p q hx hcont) true = q := by
  unfold endAnchor endParam
  simp only [if_true, curveArc_param]
  ext <;> simp [hχq]

/-- **Interior `x`-projection.** Every interior point of `curveArc χ p q hx hcont`
is `(x, χ x)` for some `x` *strictly* between `p.1` and `q.1`. The curve analogue of
`lineKey_of_mem_interior`: the first coordinate is the strictly-monotone key, so
interior points have key strictly inside the endpoint interval. -/
lemma curveArc_interior_xproj {χ : ℝ → ℝ} {p q : ℝ × ℝ} (hx : p.1 < q.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1)) {z : ℝ × ℝ}
    (hz : z ∈ interiorOfArc (curveArc χ p q hx hcont)) :
    p.1 < z.1 ∧ z.1 < q.1 ∧ z.2 = χ z.1 := by
  unfold interiorOfArc at hz
  simp only [Set.mem_image, Set.mem_setOf_eq, curveArc_param] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, hparam⟩ := hz
  -- `z.1 = (1-t)p.1 + t q.1`, `z.2 = χ z.1`.
  have hz1 : z.1 = (1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1 := by rw [← hparam]
  have hz2 : z.2 = χ ((1 - (t : ℝ)) * p.1 + (t : ℝ) * q.1) := by rw [← hparam]
  refine ⟨?_, ?_, ?_⟩
  · -- `z.1 - p.1 = t (q.1 - p.1) > 0`.
    rw [hz1]; nlinarith [ht0, hx]
  · -- `q.1 - z.1 = (1-t)(q.1 - p.1) > 0`.
    rw [hz1]; nlinarith [ht1, hx]
  · rw [hz2, ← hz1]

/-- **Disjoint `x`-projections ⟹ disjoint interiors.** Two `curveArc`s whose open
`x`-intervals `(p.1, q.1)`, `(p'.1, q'.1)` are disjoint have disjoint interiors: a
shared interior point would have its first coordinate in both open intervals.

This covers the same-class consecutive-edge case (consecutive `edgesOnSheet`
intervals are separated by sortedness) and the export-4b *different good interval*
case (distinct good intervals are disjoint). -/
lemma curveArc_interior_disjoint_of_disjoint_Ioo
    {χ χ' : ℝ → ℝ} {p q p' q' : ℝ × ℝ} (hx : p.1 < q.1) (hx' : p'.1 < q'.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1))
    (hcont' : ContinuousOn χ' (Set.Icc p'.1 q'.1))
    (hdisj : Disjoint (Set.Ioo p.1 q.1) (Set.Ioo p'.1 q'.1)) :
    Disjoint (interiorOfArc (curveArc χ p q hx hcont))
             (interiorOfArc (curveArc χ' p' q' hx' hcont')) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨hz1, hz2, _⟩ := curveArc_interior_xproj hx hcont hz
  obtain ⟨hz1', hz2', _⟩ := curveArc_interior_xproj hx' hcont' hz'
  exact (Set.disjoint_left.mp hdisj) ⟨hz1, hz2⟩ ⟨hz1', hz2'⟩

/-- **export-4b (same good interval, different sheet rank).** Over a single good
interval `(α, β)`, two connecting arcs of distinct sheet rank `j ≠ j'` have disjoint
interiors. A shared interior point `z` would lie on both arcs, so `χ z.1 = z.2 = χ' z.1`;
but the rank is *constant* along each arc (`sheetRank_const_of_continuous_onCurve`),
equal to `j` along `χ` and `j'` along `χ'`, forcing `j = j'`.

`Bad`-avoidance enters only through `hgood`; `Bézout` is *not* used (both arcs satisfy
the same `h`, and disjointness is from D3 sheet structure). -/
theorem export_4b_interior_disjoint (h : PlanePoly) {α β : ℝ} {j j' : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hjj' : j ≠ j')
    {χ χ' : ℝ → ℝ} {p q p' q' : ℝ × ℝ}
    (hx : p.1 < q.1) (hx' : p'.1 < q'.1)
    (hcont : ContinuousOn χ (Set.Icc p.1 q.1))
    (hcont' : ContinuousOn χ' (Set.Icc p'.1 q'.1))
    (hpα : α < p.1) (hqβ : q.1 < β) (hpα' : α < p'.1) (hqβ' : q'.1 < β)
    (hχp : χ p.1 = p.2) (hχp' : χ' p'.1 = p'.2)
    (hcurve : ∀ x ∈ Set.Icc p.1 q.1, evalPlane h (x, χ x) = 0)
    (hcurve' : ∀ x ∈ Set.Icc p'.1 q'.1, evalPlane h (x, χ' x) = 0)
    (hjrank : sheetRank h p.1 p.2 = j) (hj'rank : sheetRank h p'.1 p'.2 = j') :
    Disjoint (interiorOfArc (curveArc χ p q hx hcont))
             (interiorOfArc (curveArc χ' p' q' hx' hcont')) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨hz1, hz2, hzχ⟩ := curveArc_interior_xproj hx hcont hz
  obtain ⟨hz1', hz2', hzχ'⟩ := curveArc_interior_xproj hx' hcont' hz'
  -- `z.1 ∈ Icc p.1 q.1` and `z.1 ∈ Icc p'.1 q'.1`.
  have hzIcc : z.1 ∈ Set.Icc p.1 q.1 := ⟨hz1.le, hz2.le⟩
  have hzIcc' : z.1 ∈ Set.Icc p'.1 q'.1 := ⟨hz1'.le, hz2'.le⟩
  -- Rank is constant along each arc, anchored at the left endpoint.
  have hconst : sheetRank h z.1 (χ z.1) = sheetRank h p.1 (χ p.1) :=
    sheetRank_const_of_continuous_onCurve h hgood hpα hqβ hcont hcurve z.1 hzIcc
  have hconst' : sheetRank h z.1 (χ' z.1) = sheetRank h p'.1 (χ' p'.1) :=
    sheetRank_const_of_continuous_onCurve h hgood hpα' hqβ' hcont' hcurve' z.1 hzIcc'
  -- Anchor values: rank `j` along `χ`, rank `j'` along `χ'`.
  have hjval : sheetRank h z.1 (χ z.1) = j := by rw [hconst, hχp, hjrank]
  have hj'val : sheetRank h z.1 (χ' z.1) = j' := by rw [hconst', hχp', hj'rank]
  -- The shared point forces `χ z.1 = χ' z.1`, hence `j = j'`.
  have hχeq : χ z.1 = χ' z.1 := by rw [← hzχ, ← hzχ']
  exact hjj' (by rw [← hjval, hχeq, hj'val])

end PachDeZeeuw.Algebraic
