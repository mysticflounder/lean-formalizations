/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.Bezout

/-!
# Critical-point finiteness bound for real plane curves (`B-crit-lemma`)

This module discharges the `B-crit-lemma` obligation of Edge B's generic monotone
graph decomposition (`docs/corollary24-decomposition-spec.md`, §2.1, FLAG
`B-crit-lemma`).

For an irreducible plane curve `h : PlanePoly = MvPolynomial (Fin 2) ℝ` with
`totalDegree h ≤ d` and `pderiv 1 h ≠ 0` (the second-coordinate partial, i.e.
`∂_y`, nonzero — secured upstream by the generic rotation), the **double**
intersection

> `Z := PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h)`

is `Set.Finite` with `ncard ≤ (d+1)^5`. These are the *critical points* of the
curve for the `ℓ = x`-projection: curve points with a vertical (`∂_y h = 0`)
tangent. They subsume the singular points (`SingularPointSet h ⊆ Z`, since a
singular point additionally has `∂_x h = 0`), so the same factor-union + per-factor
`(d+1)^4` bound used by `finite_singularities_of_irreducible_bound`
(`Bezout.lean`) applies verbatim, with the triple intersection replaced by this
double one.

The **first-coordinate projection** `Crit_x(h) = (fun p : Point2 => p 0) '' Z`
(the critical x-values, staying on the `Point2 = EuclideanSpace ℝ (Fin 2)` side;
the bridge to `ℝ` is a separate node) is then finite with `ncard ≤ (d+1)^5` as the
image of a finite set.

## Proof structure

A direct clone of `finite_singularities_of_irreducible_bound`:

* `critPointSet_subset_partial_factor_union`: `Z ⊆ ⋃ k, (γ ∩ k)` over the
  normalized factors `k` of `pderiv 1 h`. This is `zeroSet_subset_normalizedFactor_union`
  applied to `pderiv 1 h` (no `∂_x` condition is consumed, unlike the singular
  case), intersected with the curve membership of `Z`.
* `factor_intersection_bound` gives `(γ ∩ k).ncard ≤ (d+1)^4` for each normalized
  factor `k` (not associated to `h` by `partial_factor_not_associated`).
* Summed over the `≤ d` factors: `Z.ncard ≤ d·(d+1)^4 ≤ (d+1)^5`.

No new analytic content; the only deviation from the singular-set lemma is the
subset lemma's target (double vs. triple intersection).
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace PachDeZeeuw.Algebraic

/-- The critical-point set of a plane polynomial for the `ℓ = x`-projection: curve
points with a vertical tangent, i.e. the **double** intersection of the curve with
the zero set of its `∂_y` partial (`pderiv` index `1`). Contains `SingularPointSet h`. -/
def CritPointSet (p : PlanePoly) : Set Point2 :=
  PlaneCurveZeroSet p ∩ PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) p)

/-- A critical point lies in the zero set of some normalized factor of `∂_y`. The
double-intersection analogue of `singularPointSet_subset_partial_factor_union`;
the `∂_x` condition of the singular case is simply absent here. -/
lemma critPointSet_subset_partial_factor_union
    (h : PlanePoly)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    CritPointSet h ⊆
      ⋃ k ∈ (UniqueFactorizationMonoid.normalizedFactors
          (MvPolynomial.pderiv (1 : Fin 2) h)).toFinset,
        PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
  classical
  intro z hz
  rw [CritPointSet, Set.mem_inter_iff] at hz
  obtain ⟨hz0, hz1⟩ := hz
  have hsubset := zeroSet_subset_normalizedFactor_union
      (p := MvPolynomial.pderiv (1 : Fin 2) h) hpi
  rcases Set.mem_iUnion.mp (hsubset hz1) with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hkmem, hzk⟩
  refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hkmem, ?_⟩⟩
  exact ⟨hz0, hzk⟩

/-- The critical points of an irreducible plane curve for the `ℓ = x`-projection are
finite with a degree-only bound `(d+1)^5`. A clone of
`finite_singularities_of_irreducible_bound` with the singular triple intersection
replaced by the critical double intersection `Z = γ ∩ {∂_y h = 0}`. The partial here
is fixed to `pderiv 1 h` (`∂_y`); its nonvanishing is the generic-rotation hypothesis. -/
theorem finite_critPointSet_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (CritPointSet h).Finite ∧
      (CritPointSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  let s : Multiset (MvPolynomial (Fin 2) ℝ) :=
    UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv (1 : Fin 2) h)
  have hsubset :
      CritPointSet h ⊆
        ⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
    simpa [s] using critPointSet_subset_partial_factor_union h hpi
  have hfactor_bound : ∀ k ∈ s.toFinset,
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
        (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
    intro k hk
    have hk' : k ∈ s := by
      simpa [s] using hk
    exact factor_intersection_bound h hh hdeg hpi hk'
      (partial_factor_not_associated h k hh hpi hk')
  have hfinite_union :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite := by
    exact Set.Finite.biUnion s.toFinset.finite_toSet (by
      intro k hk
      exact (hfactor_bound k hk).1)
  have hcard_union :
      (CritPointSet h).ncard ≤
        (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    exact Set.ncard_le_ncard hsubset hfinite_union
  have hcard_biUnion :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    simpa using
      Finset.set_ncard_biUnion_le s.toFinset
        (fun k => PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k)
  have hsum :
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        s.toFinset.card * (d + 1) ^ 4 := by
    have hsum' :
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact (hfactor_bound k hk).2
    calc
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := hsum'
      _ = s.toFinset.card * (d + 1) ^ 4 := by simp
  have hcard_s : s.toFinset.card ≤ d := by
    calc
      s.toFinset.card ≤ s.card := Multiset.toFinset_card_le _
      _ ≤ (MvPolynomial.pderiv (1 : Fin 2) h).totalDegree :=
        card_normalizedFactors_le_totalDegree (p := MvPolynomial.pderiv (1 : Fin 2) h) hpi
      _ ≤ h.totalDegree := totalDegree_pderiv_le h (1 : Fin 2)
      _ ≤ d := hdeg
  have hcard_mul :
      s.toFinset.card * (d + 1) ^ 4 ≤ d * (d + 1) ^ 4 := by
    exact Nat.mul_le_mul_right _ hcard_s
  have hpow : d * (d + 1) ^ 4 ≤ (d + 1) ^ 5 := by
    calc
      d * (d + 1) ^ 4 ≤ (d + 1) * (d + 1) ^ 4 := by
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)
      _ = (d + 1) ^ 5 := by
        ring_nf
  have hfinite : (CritPointSet h).Finite := hfinite_union.subset hsubset
  exact ⟨hfinite, le_trans hcard_union (le_trans hcard_biUnion (le_trans hsum (le_trans hcard_mul hpow)))⟩

/-- The double-intersection form of the critical-point bound, stated on the explicit
intersection `Z = PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h)` matching the
decomposition spec (§2.1) verbatim. Definitionally `CritPointSet h`. -/
theorem finite_doubleIntersection_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (PlaneCurveZeroSet h ∩
        PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h)).Finite ∧
      (PlaneCurveZeroSet h ∩
          PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h)).ncard ≤ (d + 1) ^ 5 :=
  finite_critPointSet_of_irreducible_bound h hh hdeg hpi

/-- The singular points sit inside the critical points (a singular point additionally
satisfies `∂_x h = 0`). This is why folding `B_sing` into `B_crit` is sound (spec §2.1). -/
lemma singularPointSet_subset_critPointSet (p : PlanePoly) :
    SingularPointSet p ⊆ CritPointSet p := by
  intro z hz
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz
  obtain ⟨⟨hz0, _hz1⟩, hz2⟩ := hz
  exact ⟨hz0, by simpa [PlaneCurveZeroSet] using hz2⟩

/-- The **first-coordinate projection** of the critical-point set — the critical
x-values `Crit_x(h)`, kept on the `Point2` side as `(fun p => p 0) '' Z`. Finite with
`ncard ≤ (d+1)^5`, as the image of a finite set; projection does not increase
cardinality. (The bridge from `(p ↦ p 0) '' Z` to a subset of `ℝ` is a separate
chart-bridge node — see `docs/corollary24-decomposition-spec.md` FLAG `chart-bridge`.) -/
theorem finite_critX_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    ((fun p : Point2 => p 0) '' CritPointSet h).Finite ∧
      ((fun p : Point2 => p 0) '' CritPointSet h).ncard ≤ (d + 1) ^ 5 := by
  obtain ⟨hfin, hbound⟩ := finite_critPointSet_of_irreducible_bound h hh hdeg hpi
  refine ⟨hfin.image _, ?_⟩
  calc
    ((fun p : Point2 => p 0) '' CritPointSet h).ncard
        ≤ (CritPointSet h).ncard := Set.ncard_image_le hfin
    _ ≤ (d + 1) ^ 5 := hbound

end PachDeZeeuw.Algebraic
