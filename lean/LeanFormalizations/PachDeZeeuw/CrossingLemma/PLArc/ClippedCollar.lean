/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PLArc shard 7/7 — **ClippedCollar**: P5 (clipped collar) — containment of each
collar piece in the tapered tube, and the final clipped-collar assembly. The
last shard. Split out of `PLArc.lean`; see that
coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.CollarConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Disjointness
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Existence
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Preconnected
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.NegativeCollar

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! ### P5 (clipped collar) — piece containment in the tube

`Option A` (the chosen fix, 2026-06-03): instead of the unsatisfiable `hsub` (the *bare*
end caps do not fit the tapered tube — they poke outside `R` at the frontier endpoints),
P5 is reproved for `collarPlus`/`collarMinus` *as defined* (keeping the
`(taperedTube∖carrier) ∩` prefix).  Bands and sectors do fit the tube — their containment
is recorded here; the end caps stay clipped and are handled by a dedicated
preconnectedness lemma. -/

/-- **Clipped sector containment (positive side).**  Each clipped arm routes through its
carrier foot-point exactly like `bandStripPlus_subset_taperedTube`, but with an ASYMMETRIC
safe window.  The incoming arm (edge `i`, clipped `α < foot`) admits foot-points in
`[α/2, 1]`: the lower end follows from the clip (Lipschitz keeps `foot y > α − α/2 = α/2`),
the upper end is the interior shared vertex `verts (i+1)` (NEVER an arc endpoint, since
`0 < i+1 < numSegs`).  The outgoing arm (edge `i+1`, clipped `foot < 1−α`) admits
`[0, 1−α/2]`.  The OPEN window end is supplied by `footParam_mem_Icc_of_mem_segment`
(a carrier point has foot in `[0,1]`).  Unlike the false unclipped `sectorPlus_subset_taperedTube`,
no vertex-ball budget is needed — the clip keeps every foot-point off the tube-vanishing
arc endpoints. -/
theorem sectorPlusClipped_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (_hα : 0 < α)
    (hsmall_in : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hsmall_out : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * δ₀ ≤ α / 2)
    (hS_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 → y ∈ S)
    (hR_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 →
        δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hS_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → y ∈ S)
    (hR_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ := by
  intro z hz
  have h2 := hz.2
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at h2
  rcases h2 with ⟨hstrip, hfootz⟩ | ⟨hstrip, hfootz⟩
  · -- incoming arm: δ₀-close to edge `i` with `α < foot i`
    have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
    obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
    have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
      div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
    have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
        ≤ α / 2 :=
      le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
        (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg)
          hsmall_in)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hfy_seg : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (0 : ℝ) 1 :=
      footParam_mem_Icc_of_mem_segment (β.segTgt_ne_segSrc i) hyseg
    have hfy : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 :=
      ⟨by linarith, hfy_seg.2⟩
    have hyS : y ∈ S := hS_in y hyseg hfy
    have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 := hR_in y hyseg hfy
    rw [taperedTube]
    refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
    rw [Metric.mem_ball, min_eq_left hyR]
    exact hyz
  · -- outgoing arm: δ₀-close to edge `i+1` with `foot (i+1) < 1 − α`
    have hsegne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
      ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
    obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
    have hKnonneg : 0 ≤ (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) :=
      div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩)))
    have hb : |footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z
          - footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y|
        ≤ α / 2 :=
      le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩) y z)
        (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg)
          hsmall_out)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hfy_seg : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
        ∈ Set.Icc (0 : ℝ) 1 :=
      footParam_mem_Icc_of_mem_segment (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩) hyseg
    have hfy : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
        ∈ Set.Icc 0 (1 - α / 2) :=
      ⟨hfy_seg.1, by linarith⟩
    have hyS : y ∈ S := hS_out y hyseg hfy
    have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 := hR_out y hyseg hfy
    rw [taperedTube]
    refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
    rw [Metric.mem_ball, min_eq_left hyR]
    exact hyz

/-- **Clipped sector containment (negative side).**  Identical to the positive side: the
proof reads only the strip-union component `hz.2` (the vertex wedge is irrelevant to tube
containment).  See `sectorPlusClipped_subset_taperedTube`. -/
theorem sectorMinusClipped_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (_hα : 0 < α)
    (hsmall_in : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hsmall_out : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * δ₀ ≤ α / 2)
    (hS_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 → y ∈ S)
    (hR_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 →
        δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hS_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → y ∈ S)
    (hR_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ := by
  intro z hz
  have h2 := hz.2
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at h2
  rcases h2 with ⟨hstrip, hfootz⟩ | ⟨hstrip, hfootz⟩
  · have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
    obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
    have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
      div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
    have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
        ≤ α / 2 :=
      le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
        (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg)
          hsmall_in)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hfy_seg : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (0 : ℝ) 1 :=
      footParam_mem_Icc_of_mem_segment (β.segTgt_ne_segSrc i) hyseg
    have hfy : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 :=
      ⟨by linarith, hfy_seg.2⟩
    have hyS : y ∈ S := hS_in y hyseg hfy
    have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 := hR_in y hyseg hfy
    rw [taperedTube]
    refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
    rw [Metric.mem_ball, min_eq_left hyR]
    exact hyz
  · have hsegne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
      ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
    obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
    have hKnonneg : 0 ≤ (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) :=
      div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩)))
    have hb : |footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z
          - footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y|
        ≤ α / 2 :=
      le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩) y z)
        (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg)
          hsmall_out)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hfy_seg : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
        ∈ Set.Icc (0 : ℝ) 1 :=
      footParam_mem_Icc_of_mem_segment (β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩) hyseg
    have hfy : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
        ∈ Set.Icc 0 (1 - α / 2) :=
      ⟨hfy_seg.1, by linarith⟩
    have hyS : y ∈ S := hS_out y hyseg hfy
    have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 := hR_out y hyseg hfy
    rw [taperedTube]
    refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
    rw [Metric.mem_ball, min_eq_left hyR]
    exact hyz

/-- **Band containment (positive side).**  A positive band-strip point lies in the tapered
tube.  The strip certificate gives a carrier witness `y` within `δ₀` (sup metric) of `z`; the
Lipschitz bound on `footParam` (`abs_footParam_sub_le`) and the smallness hypothesis `hsmall`
keep `y`'s foot-parameter inside `(α/2, 1−α/2)`, so `y` is a *strictly interior* carrier point.
`hS` then places `y` in the spine `S`, and `hR` (only needed on the safe window, where it is
satisfiable even for the end edges) gives `δ₀ ≤ ½·infDist y Rᶜ`, so the tube ball at `y` has
radius `δ₀` and swallows `z`.  No sup-metric arg-min geometry is required. -/
theorem bandStripPlus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ := by
  intro z hz
  have hz1 : footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo α (1 - α) := hz.1.1
  have hstrip : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
  have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
      / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
  have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
      ≤ α / 2 :=
    le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
      (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg) hsmall)
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hfy_lo : α / 2 < footParam (β.segSrc i) (β.segTgt i) y := by linarith [hz1.1]
  have hfy_hi : footParam (β.segSrc i) (β.segTgt i) y < 1 - α / 2 := by linarith [hz1.2]
  have hyS : y ∈ S := hS y hyseg ⟨by linarith, by linarith⟩
  have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 :=
    hR y hyseg ⟨le_of_lt hfy_lo, le_of_lt hfy_hi⟩
  rw [taperedTube]
  refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
  rw [Metric.mem_ball, min_eq_left hyR]
  exact hyz

/-- **Band containment (negative side).**  Identical to the positive side: the proof uses only
the foot-parameter window and the strip certificate, not the side-functional sign. -/
theorem bandStripMinus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ := by
  intro z hz
  have hz1 : footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo α (1 - α) := hz.1.1
  have hstrip : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
  have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
      / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
  have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
      ≤ α / 2 :=
    le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
      (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg) hsmall)
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hfy_lo : α / 2 < footParam (β.segSrc i) (β.segTgt i) y := by linarith [hz1.1]
  have hfy_hi : footParam (β.segSrc i) (β.segTgt i) y < 1 - α / 2 := by linarith [hz1.2]
  have hyS : y ∈ S := hS y hyseg ⟨by linarith, by linarith⟩
  have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 :=
    hR y hyseg ⟨le_of_lt hfy_lo, le_of_lt hfy_hi⟩
  rw [taperedTube]
  refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
  rw [Metric.mem_ball, min_eq_left hyR]
  exact hyz

/-- **Band containment off the carrier (positive side).**

An open band-strip point cannot lie on the polygonal carrier: on its own edge the
strict sign condition contradicts `sideForm = 0`, on an adjacent edge the corner
confinement budgets `hadj_tgt` / `hadj_src` rule it out, and on a nonadjacent edge
the global strip-separation budget `hsep` does. -/
theorem bandStripPlus_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i : Fin β.numSegs) :
    bandStripPlus β α δ₀ i ⊆ (β.carrier)ᶜ := by
  intro z hz
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hki : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hkδ₀ : Metric.infDist z (β.segCarrier k) < δ₀ := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δ₀ := hδ₀
  have hiδ : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hki hδ₀sep
  have hkδ : Metric.infDist z (β.segCarrier k) < δsep := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δsep := hδsep
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · have hk1 : (k : ℕ) + 1 < β.numSegs := by
        have := i.isLt
        omega
      have hkeq : i = ⟨(k : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      exact hadj_src k hk1 z (by simpa [hkeq] using hz.1.1) hkδ₀ (by simpa [hkeq] using hki)
    · exact hsep k i hfar z hkδ hiδ
  · have hkeq : k = i := Fin.ext heq
    rw [hkeq, PolyArc.segCarrier] at hzk
    have hzero : sideForm (β.segSrc i) (β.segTgt i) z = 0 :=
      sideForm_eq_zero_of_mem_segment _ _ hzk
    have hpos : 0 < sideForm (β.segSrc i) (β.segTgt i) z := hz.1.2
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · have hi1 : (i : ℕ) + 1 < β.numSegs := by
        have := k.isLt
        omega
      have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzk
      exact hadj_tgt i hi1 z hz.1.1 hki (by simpa [hkeq] using hkδ₀)
    · exact hsep i k hfar z hiδ hkδ

/-- **Band containment off the carrier (negative side).** -/
theorem bandStripMinus_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i : Fin β.numSegs) :
    bandStripMinus β α δ₀ i ⊆ (β.carrier)ᶜ := by
  intro z hz
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hki : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hkδ₀ : Metric.infDist z (β.segCarrier k) < δ₀ := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δ₀ := hδ₀
  have hiδ : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hki hδ₀sep
  have hkδ : Metric.infDist z (β.segCarrier k) < δsep := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δsep := hδsep
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · have hk1 : (k : ℕ) + 1 < β.numSegs := by
        have := i.isLt
        omega
      have hkeq : i = ⟨(k : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      exact hadj_src k hk1 z (by simpa [hkeq] using hz.1.1) hkδ₀ (by simpa [hkeq] using hki)
    · exact hsep k i hfar z hkδ hiδ
  · have hkeq : k = i := Fin.ext heq
    rw [hkeq, PolyArc.segCarrier] at hzk
    have hzero : sideForm (β.segSrc i) (β.segTgt i) z = 0 :=
      sideForm_eq_zero_of_mem_segment _ _ hzk
    have hneg : sideForm (β.segSrc i) (β.segTgt i) z < 0 := hz.1.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · have hi1 : (i : ℕ) + 1 < β.numSegs := by
        have := k.isLt
        omega
      have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzk
      exact hadj_tgt i hi1 z hz.1.1 hki (by simpa [hkeq] using hkδ₀)
    · exact hsep i k hfar z hiδ hkδ

/-- **Clipped sector containment off the carrier (positive side).**

The CLIP closes the non-incident `k ∉ {i, i+1}` case the unclipped `sectorPlus_subset_compl_carrier`
leaves open.  A clipped point sits in ONE arm: the incoming arm (δ₀-thin to edge `i`, foot `> α`)
or the outgoing arm (δ₀-thin to edge `i+1`, foot `< 1−α`).  For `z` also on edge `k`:
* **Non-adjacent** (index distance of the arm's edge and `k` is `≥ 2`): `z` is `δsep`-close to both
  (`infDist z (segCarrier k) = 0`, the arm gives `< δ₀ ≤ δsep`) → `hsep`.
* **Adjacent** (incoming arm with `k = i−1`, or outgoing arm with `k = i+2`): the arm's edge and `k`
  share a vertex; the corner confinement `hconf` plus the Lipschitz budget `hLr` push the foot
  toward the shared vertex (`< α` for incoming via `footParam_lt_of_confined_src`, `> 1−α` for
  outgoing via `footParam_gt_of_confined_tgt`), contradicting the clip's margin.  Mirrors agent D's
  `disjoint_sectorPlusClipped_sectorMinusClipped_all` adjacent-corner geometry. -/
theorem sectorPlusClipped_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (_hα : 0 < α) (hδ₀ : 0 < δ₀) (hδsep : 0 < δsep) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (r : Fin β.numSegs → ℝ)
    (hconf : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs) {z : Plane},
      Metric.infDist z (β.segCarrier e) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(e : ℕ) + 1, he1⟩) < δ₀ →
      dist z (β.verts (Fin.succ e)) < r e)
    (hLr : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs),
      (|(β.segTgt e).1 - (β.segSrc e).1| + |(β.segTgt e).2 - (β.segSrc e).2|)
          / dotp (β.segTgt e - β.segSrc e) (β.segTgt e - β.segSrc e) * r e ≤ α ∧
      (|(β.segTgt ⟨(e : ℕ) + 1, he1⟩).1 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).1|
          + |(β.segTgt ⟨(e : ℕ) + 1, he1⟩).2 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).2|)
          / dotp (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩)
                 (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩) * r e ≤ α)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ (β.carrier)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  obtain ⟨hzV, harm⟩ := hz
  have hzU :
      z ∈ convexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
        ∪ reflexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
    rw [vertexPlus] at hzV
    split_ifs at hzV
    · exact Or.inl hzV
    · exact Or.inr hzV
  by_cases hki : (k : ℕ) = (i : ℕ)
  · have hkeq : k = i := Fin.ext hki
    rw [hkeq, PolyArc.segCarrier] at hzk
    exact (segment_av_subset_compl_sectors
      (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
  · by_cases hki1 : (k : ℕ) = (i : ℕ) + 1
    · have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext hki1
      rw [hkeq, PolyArc.segCarrier] at hzk
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      have hcs : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = β.segTgt i := by
        rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
      rw [hcs] at hzk
      exact (segment_vb_subset_compl_sectors
        (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
    · -- §9 UNION REWORK, CLIP-CLOSED.  `z` is on edge `k` (k ∉ {i, i+1}) → `infDist = 0`.
      have hk0 : Metric.infDist z (β.segCarrier k) = 0 := Metric.infDist_zero_of_mem hzk
      rcases harm with hin | hout
      · -- INCOMING arm: δ₀-thin to edge `i`, foot `> α`.
        obtain ⟨hiδ, hfoot⟩ := hin
        rw [Set.mem_setOf_eq] at hfoot
        by_cases hadj : (k : ℕ) + 1 = (i : ℕ)
        · -- ADJACENT: k = i−1.  Corner `e = k`, edges k and k+1 = i share verts(succ k) = segSrc i.
          have he1 : (k : ℕ) + 1 < β.numSegs := by have := i.isLt; omega
          have hki' : (⟨(k : ℕ) + 1, he1⟩ : Fin β.numSegs) = i := Fin.ext (by simpa using hadj)
          have hzkstrip : Metric.infDist z (β.segCarrier k) < δ₀ := by rw [hk0]; exact hδ₀
          have hiclose : Metric.infDist z (β.segCarrier ⟨(k : ℕ) + 1, he1⟩) < δ₀ := by
            rw [hki']; exact hiδ
          have hconf' : dist z (β.verts (Fin.succ k)) < r k := hconf k he1 hzkstrip hiclose
          -- segSrc i = verts(succ k): castSucc i = succ k as Fin (numSegs+1).
          have hsv : β.segSrc i = β.verts (Fin.succ k) := by
            have hidx : (Fin.castSucc i : Fin (β.numSegs + 1)) = Fin.succ k :=
              Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            rw [PolyArc.segSrc, hidx]
          have hne : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
          have hbud : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
              / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * r k ≤ α := by
            have := (hLr k he1).2; rwa [hki'] at this
          have hfoot_lt : footParam (β.segSrc i) (β.segTgt i) z < α :=
            footParam_lt_of_confined_src hne hsv hbud hconf'
          linarith
        · -- NON-ADJACENT: index distance of edges `i` and `k` is ≥ 2 → `hsep`.
          have hiclose : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hiδ hδ₀sep
          have hkclose : Metric.infDist z (β.segCarrier k) < δsep := by rw [hk0]; exact hδsep
          rcases lt_or_gt_of_ne hki with hlt | hgt
          · exact hsep k i (by omega) z hkclose hiclose
          · exact hsep i k (by omega) z hiclose hkclose
      · -- OUTGOING arm: δ₀-thin to edge `i+1`, foot `< 1−α`.
        obtain ⟨hi1δ, hfoot⟩ := hout
        rw [Set.mem_setOf_eq] at hfoot
        by_cases hadj : (k : ℕ) = (i : ℕ) + 2
        · -- ADJACENT: k = i+2.  Corner `e = i+1`, edges i+1 and (i+1)+1 = k share verts(succ(i+1)).
          have hival : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) = (i : ℕ) + 1 := rfl
          have he1 : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1 < β.numSegs := by
            rw [hival]; have := k.isLt; omega
          have hk' : (⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩ : Fin β.numSegs) = k :=
            Fin.ext (by simp; omega)
          have hcareq : β.segCarrier ⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩
              = β.segCarrier k := congrArg β.segCarrier hk'
          have hzkstrip : Metric.infDist z (β.segCarrier
              ⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩) < δ₀ := by
            rw [hcareq, hk0]; exact hδ₀
          have hconf' : dist z (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) <
              r ⟨(i : ℕ) + 1, hi1⟩ :=
            hconf ⟨(i : ℕ) + 1, hi1⟩ he1 hi1δ hzkstrip
          have hne : β.segTgt ⟨(i : ℕ) + 1, hi1⟩ ≠ β.segSrc ⟨(i : ℕ) + 1, hi1⟩ :=
            β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
          have htv : β.segTgt ⟨(i : ℕ) + 1, hi1⟩ = β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩) := rfl
          have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
              (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z :=
            footParam_gt_of_confined_tgt hne htv (hLr ⟨(i : ℕ) + 1, hi1⟩ he1).1 hconf'
          linarith
        · -- NON-ADJACENT: index distance of edges `i+1` and `k` is ≥ 2 → `hsep`.
          have hi1close : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δsep :=
            lt_of_lt_of_le hi1δ hδ₀sep
          have hkclose : Metric.infDist z (β.segCarrier k) < δsep := by rw [hk0]; exact hδsep
          have hkval1 : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) = (i : ℕ) + 1 := rfl
          rcases lt_or_gt_of_ne hki1 with hlt | hgt
          · exact hsep k ⟨(i : ℕ) + 1, hi1⟩ (by rw [hkval1]; omega) z hkclose hi1close
          · exact hsep ⟨(i : ℕ) + 1, hi1⟩ k (by rw [hkval1]; omega) z hi1close hkclose

/-- **Clipped sector containment off the carrier (negative side).**  See
`sectorPlusClipped_subset_compl_carrier`; the only difference is the `vertexMinus` τ-branch. -/
theorem sectorMinusClipped_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (_hα : 0 < α) (hδ₀ : 0 < δ₀) (hδsep : 0 < δsep) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (r : Fin β.numSegs → ℝ)
    (hconf : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs) {z : Plane},
      Metric.infDist z (β.segCarrier e) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(e : ℕ) + 1, he1⟩) < δ₀ →
      dist z (β.verts (Fin.succ e)) < r e)
    (hLr : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs),
      (|(β.segTgt e).1 - (β.segSrc e).1| + |(β.segTgt e).2 - (β.segSrc e).2|)
          / dotp (β.segTgt e - β.segSrc e) (β.segTgt e - β.segSrc e) * r e ≤ α ∧
      (|(β.segTgt ⟨(e : ℕ) + 1, he1⟩).1 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).1|
          + |(β.segTgt ⟨(e : ℕ) + 1, he1⟩).2 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).2|)
          / dotp (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩)
                 (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩) * r e ≤ α)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ (β.carrier)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  obtain ⟨hzV, harm⟩ := hz
  have hzU :
      z ∈ convexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
        ∪ reflexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
    rw [vertexMinus] at hzV
    split_ifs at hzV
    · exact Or.inr hzV
    · exact Or.inl hzV
  by_cases hki : (k : ℕ) = (i : ℕ)
  · have hkeq : k = i := Fin.ext hki
    rw [hkeq, PolyArc.segCarrier] at hzk
    exact (segment_av_subset_compl_sectors
      (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
  · by_cases hki1 : (k : ℕ) = (i : ℕ) + 1
    · have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext hki1
      rw [hkeq, PolyArc.segCarrier] at hzk
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      have hcs : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = β.segTgt i := by
        rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
      rw [hcs] at hzk
      exact (segment_vb_subset_compl_sectors
        (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
    · -- §9 UNION REWORK, CLIP-CLOSED.  `z` is on edge `k` (k ∉ {i, i+1}) → `infDist = 0`.
      have hk0 : Metric.infDist z (β.segCarrier k) = 0 := Metric.infDist_zero_of_mem hzk
      rcases harm with hin | hout
      · -- INCOMING arm: δ₀-thin to edge `i`, foot `> α`.
        obtain ⟨hiδ, hfoot⟩ := hin
        rw [Set.mem_setOf_eq] at hfoot
        by_cases hadj : (k : ℕ) + 1 = (i : ℕ)
        · -- ADJACENT: k = i−1.  Corner `e = k`, edges k and k+1 = i share verts(succ k) = segSrc i.
          have he1 : (k : ℕ) + 1 < β.numSegs := by have := i.isLt; omega
          have hki' : (⟨(k : ℕ) + 1, he1⟩ : Fin β.numSegs) = i := Fin.ext (by simpa using hadj)
          have hzkstrip : Metric.infDist z (β.segCarrier k) < δ₀ := by rw [hk0]; exact hδ₀
          have hiclose : Metric.infDist z (β.segCarrier ⟨(k : ℕ) + 1, he1⟩) < δ₀ := by
            rw [hki']; exact hiδ
          have hconf' : dist z (β.verts (Fin.succ k)) < r k := hconf k he1 hzkstrip hiclose
          have hsv : β.segSrc i = β.verts (Fin.succ k) := by
            have hidx : (Fin.castSucc i : Fin (β.numSegs + 1)) = Fin.succ k :=
              Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            rw [PolyArc.segSrc, hidx]
          have hne : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
          have hbud : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
              / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * r k ≤ α := by
            have := (hLr k he1).2; rwa [hki'] at this
          have hfoot_lt : footParam (β.segSrc i) (β.segTgt i) z < α :=
            footParam_lt_of_confined_src hne hsv hbud hconf'
          linarith
        · -- NON-ADJACENT: index distance of edges `i` and `k` is ≥ 2 → `hsep`.
          have hiclose : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hiδ hδ₀sep
          have hkclose : Metric.infDist z (β.segCarrier k) < δsep := by rw [hk0]; exact hδsep
          rcases lt_or_gt_of_ne hki with hlt | hgt
          · exact hsep k i (by omega) z hkclose hiclose
          · exact hsep i k (by omega) z hiclose hkclose
      · -- OUTGOING arm: δ₀-thin to edge `i+1`, foot `< 1−α`.
        obtain ⟨hi1δ, hfoot⟩ := hout
        rw [Set.mem_setOf_eq] at hfoot
        by_cases hadj : (k : ℕ) = (i : ℕ) + 2
        · -- ADJACENT: k = i+2.  Corner `e = i+1`, edges i+1 and (i+1)+1 = k share verts(succ(i+1)).
          have hival : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) = (i : ℕ) + 1 := rfl
          have he1 : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1 < β.numSegs := by
            rw [hival]; have := k.isLt; omega
          have hk' : (⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩ : Fin β.numSegs) = k :=
            Fin.ext (by simp; omega)
          have hcareq : β.segCarrier ⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩
              = β.segCarrier k := congrArg β.segCarrier hk'
          have hzkstrip : Metric.infDist z (β.segCarrier
              ⟨((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) + 1, he1⟩) < δ₀ := by
            rw [hcareq, hk0]; exact hδ₀
          have hconf' : dist z (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) <
              r ⟨(i : ℕ) + 1, hi1⟩ :=
            hconf ⟨(i : ℕ) + 1, hi1⟩ he1 hi1δ hzkstrip
          have hne : β.segTgt ⟨(i : ℕ) + 1, hi1⟩ ≠ β.segSrc ⟨(i : ℕ) + 1, hi1⟩ :=
            β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
          have htv : β.segTgt ⟨(i : ℕ) + 1, hi1⟩ = β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩) := rfl
          have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
              (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z :=
            footParam_gt_of_confined_tgt hne htv (hLr ⟨(i : ℕ) + 1, hi1⟩ he1).1 hconf'
          linarith
        · -- NON-ADJACENT: index distance of edges `i+1` and `k` is ≥ 2 → `hsep`.
          have hi1close : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δsep :=
            lt_of_lt_of_le hi1δ hδ₀sep
          have hkclose : Metric.infDist z (β.segCarrier k) < δsep := by rw [hk0]; exact hδsep
          have hkval1 : ((⟨(i : ℕ) + 1, hi1⟩ : Fin β.numSegs) : ℕ) = (i : ℕ) + 1 := rfl
          rcases lt_or_gt_of_ne hki1 with hlt | hgt
          · exact hsep k ⟨(i : ℕ) + 1, hi1⟩ (by rw [hkval1]; omega) z hkclose hi1close
          · exact hsep ⟨(i : ℕ) + 1, hi1⟩ k (by rw [hkval1]; omega) z hi1close hkclose

/-- **Band containment in the clipped collar ground set (positive side).** -/
theorem bandStripPlus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    {α δ₀ δsep : ℝ} (i : Fin β.numSegs)
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨bandStripPlus_subset_taperedTube β R S δ₀ α i hα hsmall hS hR hz,
    bandStripPlus_subset_compl_carrier β hδ₀ hδ₀sep hsep hadj_tgt hadj_src i hz⟩

/-- **Band containment in the clipped collar ground set (negative side).** -/
theorem bandStripMinus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    {α δ₀ δsep : ℝ} (i : Fin β.numSegs)
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨bandStripMinus_subset_taperedTube β R S δ₀ α i hα hsmall hS hR hz,
    bandStripMinus_subset_compl_carrier β hδ₀ hδ₀sep hsep hadj_tgt hadj_src i hz⟩

/-- **Clipped sector containment in the collar ground set (positive side).**  Combines the
clipped tube-containment (`sectorPlusClipped_subset_taperedTube`, window-style `S`/`R` data) with
the clipped off-carrier lemma (`sectorPlusClipped_subset_compl_carrier`, confinement budget).  The
union of the two lemmas' hypotheses; the collar-facing replacement for the unclipped
`sectorPlus_subset_taperedTube_diff_carrier`. -/
theorem sectorPlusClipped_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hsmall_in : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hsmall_out : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * δ₀ ≤ α / 2)
    (hS_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 → y ∈ S)
    (hR_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 →
        δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hS_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → y ∈ S)
    (hR_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → δ₀ ≤ Metric.infDist y Rᶜ / 2)
    {δsep : ℝ} (hδ₀ : 0 < δ₀) (hδsep : 0 < δsep) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (r : Fin β.numSegs → ℝ)
    (hconf : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs) {z : Plane},
      Metric.infDist z (β.segCarrier e) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(e : ℕ) + 1, he1⟩) < δ₀ →
      dist z (β.verts (Fin.succ e)) < r e)
    (hLr : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs),
      (|(β.segTgt e).1 - (β.segSrc e).1| + |(β.segTgt e).2 - (β.segSrc e).2|)
          / dotp (β.segTgt e - β.segSrc e) (β.segTgt e - β.segSrc e) * r e ≤ α ∧
      (|(β.segTgt ⟨(e : ℕ) + 1, he1⟩).1 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).1|
          + |(β.segTgt ⟨(e : ℕ) + 1, he1⟩).2 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).2|)
          / dotp (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩)
                 (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩) * r e ≤ α) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨sectorPlusClipped_subset_taperedTube β R S δ₀ α i hi1 hα hsmall_in hsmall_out
      hS_in hR_in hS_out hR_out hz,
    sectorPlusClipped_subset_compl_carrier β hα hδ₀ hδsep hδ₀sep hsep r hconf hLr i hi1 hz⟩

/-- **Clipped sector containment in the collar ground set (negative side).**  See
`sectorPlusClipped_subset_taperedTube_diff_carrier`. -/
theorem sectorMinusClipped_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hsmall_in : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hsmall_out : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
          + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
        / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
               (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * δ₀ ≤ α / 2)
    (hS_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 → y ∈ S)
    (hR_in : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) 1 →
        δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hS_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → y ∈ S)
    (hR_out : ∀ y ∈ β.segCarrier ⟨(i : ℕ) + 1, hi1⟩,
        footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) y
          ∈ Set.Icc 0 (1 - α / 2) → δ₀ ≤ Metric.infDist y Rᶜ / 2)
    {δsep : ℝ} (hδ₀ : 0 < δ₀) (hδsep : 0 < δsep) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (r : Fin β.numSegs → ℝ)
    (hconf : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs) {z : Plane},
      Metric.infDist z (β.segCarrier e) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(e : ℕ) + 1, he1⟩) < δ₀ →
      dist z (β.verts (Fin.succ e)) < r e)
    (hLr : ∀ (e : Fin β.numSegs) (he1 : (e : ℕ) + 1 < β.numSegs),
      (|(β.segTgt e).1 - (β.segSrc e).1| + |(β.segTgt e).2 - (β.segSrc e).2|)
          / dotp (β.segTgt e - β.segSrc e) (β.segTgt e - β.segSrc e) * r e ≤ α ∧
      (|(β.segTgt ⟨(e : ℕ) + 1, he1⟩).1 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).1|
          + |(β.segTgt ⟨(e : ℕ) + 1, he1⟩).2 - (β.segSrc ⟨(e : ℕ) + 1, he1⟩).2|)
          / dotp (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩)
                 (β.segTgt ⟨(e : ℕ) + 1, he1⟩ - β.segSrc ⟨(e : ℕ) + 1, he1⟩) * r e ≤ α) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨sectorMinusClipped_subset_taperedTube β R S δ₀ α i hi1 hα hsmall_in hsmall_out
      hS_in hR_in hS_out hR_out hz,
    sectorMinusClipped_subset_compl_carrier β hα hδ₀ hδsep hδ₀sep hsep r hconf hLr i hi1 hz⟩

/-- A positive vertex sector that lies in the clipped collar ground is contained
in the positive collar side.

This is the local sector-to-collar direction used by the crosscut side
classification: once the sliver budgets put the sector in
`taperedTube R S δ₀ \ β.carrier`, its defining positive-sector membership places
it in `collarPlus`. -/
theorem sectorPlus_subset_collarPlus_of_subset_ground (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hground : sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ collarPlus β R S δ₀ α ρ := by
  intro z hz
  refine ⟨hground hz, ?_⟩
  refine Or.inl (Or.inl (Or.inr ?_))
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi1, hz⟩⟩

/-- A negative vertex sector that lies in the clipped collar ground is contained
in the negative collar side. -/
theorem sectorMinus_subset_collarMinus_of_subset_ground (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hground : sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ collarMinus β R S δ₀ α ρ := by
  intro z hz
  refine ⟨hground hz, ?_⟩
  refine Or.inl (Or.inl (Or.inr ?_))
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi1, hz⟩⟩

/-- If the positive collar is assigned to a side `U`, then any positive vertex
sector already placed in the clipped collar ground is assigned to `U`. -/
theorem sectorPlus_subset_of_collarPlus_subset (β : PolyArc) (R S U : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hPlusU : collarPlus β R S δ₀ α ρ ⊆ U)
    (hground : sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ U :=
  (sectorPlus_subset_collarPlus_of_subset_ground β R S δ₀ α ρ i hi1 hground).trans
    hPlusU

/-- If the negative collar is assigned to a side `V`, then any negative vertex
sector already placed in the clipped collar ground is assigned to `V`. -/
theorem sectorMinus_subset_of_collarMinus_subset (β : PolyArc) (R S V : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hMinusV : collarMinus β R S δ₀ α ρ ⊆ V)
    (hground : sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ V :=
  (sectorMinus_subset_collarMinus_of_subset_ground β R S δ₀ α ρ i hi1 hground).trans
    hMinusV

/-- **Negative clipped-collar preconnectedness from sliver-budget end-cap inputs.**

This packages the full `P5⁻` assembly for `collarMinus`. The band and sector pieces
are put into the ground set using the clipped-containment lemmas above, while the two
negative end caps are supplied by the source/target sliver-budget preconnectedness
theorems. -/
theorem isPreconnected_collarMinus_of_sliver_budgets
    (β : PolyArc) (R S : Set Plane) {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3) (hα1 : α < 1)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected (collarMinus β R S δ₀ α ρ) := by
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  refine isPreconnected_collarMinus β R S ρ hα hα1 hturn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact bandStripMinus_subset_taperedTube_diff_carrier β R S i hδ₀ hδ₀sep
      hsep hadj_tgt hadj_src hα (hsmall i) (hSband i) (hRband i)
  · exact hsectorW
  · exact isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_sliver_budget
      β R S ρ hSrcSep hSrcSpine hSrcNear hδ₀ hρ0 hSrcRpos hSrcSliver
  · exact isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_sliver_budget
      β R S ρ hTgtSep hTgtSpine hTgtNear hδ₀ hρL hTgtRpos hTgtSliver
  · intro i hi1
    exact overlap_sectorMinusClipped_bandStripMinus_src β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (htgt i)
  · intro i hi1
    exact overlap_sectorMinusClipped_bandStripMinus_tgt β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (by simpa using hsrc ⟨(i : ℕ) + 1, hi1⟩)
  · exact overlap_endCapSrcMinus_bandStripMinus β ρ hδ₀ hα hα3
      (by simpa [PolyArc.firstSeg] using hsrc β.firstSeg)
  · have hlast : Fin.succ β.lastSeg = Fin.last β.numSegs := by
      apply Fin.ext
      have h := β.numSegs_pos
      simp [PolyArc.lastSeg, Fin.val_last]
      omega
    exact overlap_endCapTgtMinus_bandStripMinus β ρ hδ₀ hα hα3
      (by simpa [hlast] using htgt β.lastSeg)

/-- **Positive clipped-collar preconnectedness from sliver-budget end-cap inputs.**

This is the `P5⁺` companion to
`isPreconnected_collarMinus_of_sliver_budgets`: the band/sector pieces are placed
in the clipped ground set by the containment lemmas, and the two positive end caps
are supplied by the source/target sliver-budget preconnectedness theorems. -/
theorem isPreconnected_collarPlus_of_sliver_budgets
    (β : PolyArc) (R S : Set Plane) {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3) (hα1 : α < 1)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioo (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioo (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected (collarPlus β R S δ₀ α ρ) := by
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  refine isPreconnected_collarPlus β R S ρ hα hα1 hturn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact bandStripPlus_subset_taperedTube_diff_carrier β R S i hδ₀ hδ₀sep
      hsep hadj_tgt hadj_src hα (hsmall i) (hSband i) (hRband i)
  · exact hsectorW
  · exact isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_sliver_budget
      β R S ρ hSrcSep hSrcSpine hSrcNear hδ₀ hρ0 hSrcRpos hSrcSliver
  · exact isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_sliver_budget
      β R S ρ hTgtSep hTgtSpine hTgtNear hδ₀ hρL hTgtRpos hTgtSliver
  · intro i hi1
    exact overlap_sectorPlusClipped_bandStripPlus_src β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (htgt i)
  · intro i hi1
    exact overlap_sectorPlusClipped_bandStripPlus_tgt β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (by simpa using hsrc ⟨(i : ℕ) + 1, hi1⟩)
  · exact overlap_endCapSrcPlus_bandStripPlus β ρ hδ₀ hα hα3
      (by simpa [PolyArc.firstSeg] using hsrc β.firstSeg)
  · have hlast : Fin.succ β.lastSeg = Fin.last β.numSegs := by
      apply Fin.ext
      have h := β.numSegs_pos
      simp [PolyArc.lastSeg, Fin.val_last]
      omega
    exact overlap_endCapTgtPlus_bandStripPlus β ρ hδ₀ hα hα3
      (by simpa [hlast] using htgt β.lastSeg)


end CrossingLemma.PlaneArcSeparation
