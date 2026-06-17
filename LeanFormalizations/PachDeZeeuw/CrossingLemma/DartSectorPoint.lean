/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RegionFaceBridge
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc

/-!
# The arc→`PolyArc` bridge

Provides `straightPolyArc` and `arcToPolyArc` — turning a straight graph arc
into a one-segment `PolyArc`.  These are reused by the Target-1 instantiation for
the bridge (`exists_twoSidedPartition_of_straightArc` expects a `PolyArc`).

The dart→sector-point map (§2) was removed (2026-06-16): the `Classical.choose`
region map cannot satisfy `PrefixStepCrosscutData.hinj`/`hfactor`; the region
family is forced to be `poolRegion`-derived, not freely chosen.

## What is proved here

* `straightPolyArc` and `arcToPolyArc` — proved **sorry-free**: the two
  no-self-crossing fields are vacuous at `numSegs = 1`, and `distinct` reduces to
  the endpoints being distinct.

100-char lines.  No new axioms beyond what the imports carry.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CrossingLemma.PlaneArcSeparation

variable (G : DrawnMultigraph)

/-! ## §1  The arc→`PolyArc` bridge (deliverable 3)

A straight graph arc is a single segment `[s, t]`.  As a `PolyArc` it has one
segment (`numSegs = 1`) and the two vertices `s, t`.  Its two no-self-crossing
fields are **vacuous** at `numSegs = 1` (`nonadjacent_disjoint` needs `i+1 < j`
with `i, j : Fin 1`, impossible; `consecutive_meet` needs `i+1 < 1` with
`i : Fin 1`, impossible), so the only genuine constructor obligation is
`distinct`, which for `![s, t]` is exactly `s ≠ t`. -/

/-- **The one-segment `PolyArc` of a straight segment `[s, t]`** with distinct
endpoints `hst : s ≠ t`.  `numSegs = 1`, `verts = ![s, t]`. -/
noncomputable def straightPolyArc (s t : Plane) (hst : s ≠ t) : PolyArc where
  numSegs := 1
  numSegs_pos := le_refl 1
  verts := ![s, t]
  distinct := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hst.symm]
  nonadjacent_disjoint := by
    intro i j hlt
    exact absurd hlt (by omega)
  consecutive_meet := by
    intro i h
    exact absurd h (by omega)

/-- The source vertex of `straightPolyArc s t hst` is `s`. -/
theorem straightPolyArc_src (s t : Plane) (hst : s ≠ t) :
    (straightPolyArc s t hst).src = s := by
  simp [PolyArc.src, straightPolyArc]

/-- The target vertex of `straightPolyArc s t hst` is `t`. -/
theorem straightPolyArc_tgt (s t : Plane) (hst : s ≠ t) :
    (straightPolyArc s t hst).tgt = t := by
  simp [PolyArc.tgt, straightPolyArc]

/-- The carrier of the one-segment arc is the closed segment `[s, t]`. -/
theorem straightPolyArc_carrier (s t : Plane) (hst : s ≠ t) :
    (straightPolyArc s t hst).carrier = segment ℝ s t := by
  rw [PolyArc.carrier]
  apply Set.eq_of_subset_of_subset
  · apply Set.iUnion_subset
    intro i
    fin_cases i
    simp [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt, straightPolyArc]
  · refine Set.subset_iUnion_of_subset ⟨0, (straightPolyArc s t hst).numSegs_pos⟩ ?_
    simp [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt, straightPolyArc]

/-- **The `PolyArc` of edge `e`** of a drawing whose arcs join their declared
endpoints (so the two declared endpoints are distinct, `hjoin`): the one-segment
arc on `G.endpoints e`. -/
noncomputable def arcToPolyArc (hjoin : G.ArcsJoinEndpoints) (e : Fin G.numEdges) :
    PolyArc :=
  straightPolyArc (G.endpoints e).1 (G.endpoints e).2
    (G.endpoints_ne_of_arcsJoinEndpoints hjoin e)

/-! ## §2  Complement nonempty: existence of a point off all arcs

The drawing complement `R₀ \ arcUnion` is nonempty because the arc union is a
finite union of compact sets, hence bounded; pick a point far away.  This is the
only geometric fact needed for the base case of the region-family induction
(one face at the tree prefix, all darts map to the same component).

Note: we do NOT build a per-dart sector-point map (`Classical.choose` would
collapse to a constant, breaking `PrefixStepCrosscutData.hinj`/`hfactor`).
The per-dart regions come from the inductive `poolRegion` construction. -/

/-- **Existence of a point in the drawing complement (R₀ = Set.univ).** -/
theorem exists_point_in_complement (m : ℕ) (hm : m ≤ G.numEdges) :
    ∃ p, p ∈ drawingComplementIn (G.prefixEdges m hm) Set.univ := by
  -- The R₀ parameter is carried for API compatibility; we ignore it.
  -- It suffices to find a point p ∉ arcUnion (then p ∈ R₀ \ arcUnion = drawingComplementIn).
  -- The proof uses that the arc union is a finite union of compact sets, hence bounded.
  have hcompacts : ∀ e : Fin m, IsCompact (arcSet (G.prefixEdges m hm) e) := by
    intro e
    rw [arcSet, ← Set.image_univ]
    exact (isCompact_univ).image ((G.prefixEdges m hm).arc e).cont
  have hunion_compact : IsCompact (arcUnion (G.prefixEdges m hm)) := by
    rw [arcUnion]
    exact isCompact_iUnion hcompacts
  have hbounded : Bornology.IsBounded (arcUnion (G.prefixEdges m hm)) :=
    hunion_compact.isBounded
  obtain ⟨R, hR⟩ : ∃ R : ℝ, arcUnion (G.prefixEdges m hm) ⊆
      Metric.closedBall (0 : ℝ × ℝ) R :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp hbounded
  -- Use a nonnegative radius
  let R' : ℝ := max R 0
  have hR' : arcUnion (G.prefixEdges m hm) ⊆ Metric.closedBall (0 : ℝ × ℝ) R' := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ × ℝ) R := hR hx
    rw [Metric.mem_closedBall] at hx' ⊢
    have : R ≤ R' := le_max_left _ _
    linarith
  let p : ℝ × ℝ := (R' + 1, 0)
  have hp_notin_ball : p ∉ Metric.closedBall (0 : ℝ × ℝ) R' := by
    rw [Metric.mem_closedBall]
    have hdist : dist p (0 : ℝ × ℝ) = R' + 1 := by
      have hR'nonneg : 0 ≤ R' := le_max_right _ _
      have hsum_pos : 0 ≤ R' + 1 := by linarith
      calc
        dist p (0 : ℝ × ℝ) = max (|(R' + 1) - (0 : ℝ)|) (|(0 : ℝ) - (0 : ℝ)|) := by
          simp [p, Prod.dist_eq]
        _ = max (|R' + 1|) 0 := by simp
        _ = |R' + 1| := by simp
        _ = R' + 1 := abs_of_nonneg hsum_pos
    rw [hdist]
    linarith
  have hp_notin_union : p ∉ arcUnion (G.prefixEdges m hm) := by
    intro hp
    apply hp_notin_ball
    exact hR' hp
  -- p ∈ Set.univ \ arcUnion = Set.univ \ arcUnion
  refine ⟨p, ?_, hp_notin_union⟩
  simp

end CrossingLemma
