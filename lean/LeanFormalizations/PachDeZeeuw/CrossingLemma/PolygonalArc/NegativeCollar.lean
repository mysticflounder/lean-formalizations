/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PolygonalArc shard 6/7 — **NegativeCollar**: the P5⁻ mirror of the positive side —
preconnectedness of the negative collar `collarMinus` and its band/sector
pieces. Split out of `PolygonalArc.lean`; see that coordinator module's doc for the
overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.CollarConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Disjointness
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Existence
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Preconnected

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! ### P5⁻ — the negative collar (mirror of the positive side) -/

/-- **Local overlap of the source-negative cap slices from slice nonemptiness.**

This is the negative-side analogue of
`local_overlap_endCapSrcPlus_of_slice_nonempty`: once every slice
`endCapSrcMinus ∩ ball (p c) (r c)` is nonempty on a chosen foot range,
continuity of the centre and radius functions makes nearby slices overlap
automatically. -/
theorem local_overlap_endCapSrcMinus_of_slice_nonempty
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices_Ioo
      (cap := endCapSrcMinus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Source-negative cap slice nonemptiness from the sliver budget.**

This is the negative-side companion to
`nonempty_endCapSrcPlus_slice_of_sliver_budget`: under the same source-endpoint
sliver inequality, sliding slightly back along the first edge and lifting a tiny
amount to the negative side produces a point in the slice. -/
theorem nonempty_endCapSrcMinus_slice_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρ0 : 0 < ρ 0)
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
        < ρ 0 + min δ₀
            (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    (endCapSrcMinus β ρ ∩ Metric.ball
      (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween : max 0 (c * dist s t - rad) < min (c * dist s t) (ρ 0) := by
    by_cases hcr : c * dist s t ≤ ρ 0
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ 0 < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ 0 := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρ0, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ 0 := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ 0 - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ 0 - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_nonneg hεpos.le]
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d (-ε) with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwsrc : dist w s < ρ 0 := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d (-ε)
      rw [abs_of_nonneg hdpos.le, hεabs] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ 0 - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ 0 := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d (-ε) c 0
      rw [sub_zero, hεabs] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr hwsrc, ?_⟩, hwside⟩
  show 0 < footParam s t w
  rw [hwfoot]
  exact hdpos

/-- **Source-negative cap slice nonemptiness on a full foot range.**

This packages `nonempty_endCapSrcMinus_slice_of_sliver_budget` over an interval
`Ioc 0 c_max`: if the radius function is positive there and each foot parameter
satisfies the source-endpoint sliver inequality, then every source-negative slice
in the range is nonempty. -/
theorem nonempty_endCapSrcMinus_slices_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapSrcMinus_slice_of_sliver_budget β R ρ hc.1 hρ0 ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the source-negative cap slices.**

This is the negative-side principal-foot overlap witness for
`isPreconnected_cap_inter_ball_cover`: consecutive slices share a common point
obtained by a tiny negative lift of the foot-`c` centre. -/
theorem local_overlap_endCapSrcMinus (β : PolygonalArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hclt⟩ := hc
  have hcle : c ≤ c_max := hclt.le
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolygonalArc.firstSeg]
    rw [hs, PolygonalArc.segSrc, hcast]
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hclt⟩
  set K := min (min δ₀ (I0 / 4)) (ρ 0 - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ 0 - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c (-ε) with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwball0 : dist w (β.verts 0) < ρ 0 := by
    rw [hv0]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c (-ε)
      rw [abs_of_nonneg hc0.le, hεabs] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ 0 := by nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapSrcMinus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, hwside⟩
    show 0 < footParam s t w
    rw [hwfoot]
    exact hc0
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c 0
      have hεabs' : |(-ε) - 0| = ε := by simpa using hεabs
      rw [sub_self, hεabs'] at h
      simp only [abs_zero, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c' 0
      rw [sub_zero, hεabs] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The source-negative end cap is exactly the union of its first-edge slice balls
once every tube witness near the source endpoint comes from the first edge in the
same foot window. -/
theorem taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapSrcMinus β ρ
      = ⋃ c ∈ Set.Ioo (0 : ℝ) c_max,
          endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) := by
  set s := β.segSrc β.firstSeg
  set t := β.segTgt β.firstSeg
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts 0) < ρ 0 + δ₀ := by
      have htri := dist_triangle p z (β.verts 0)
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioo (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by simpa [s, t] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped source-negative end cap is
preconnected once its tube witnesses are controlled by first-edge slices over that
same parameter window. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapSrcMinus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcMinus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible source-negative clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapSrcMinus_of_near_spine`, the
overlap input is supplied by slice nonemptiness on the chosen foot range, with
continuity handling the local-overlap step. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_slice_nonempty
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapSrcMinus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcMinus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A source-negative clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the foot range. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_sliver_budget
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  refine isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapSrcMinus_slices_of_sliver_budget β R ρ hδ₀ hρ0 hRpos hsliver

/-- **Local overlap of the target-negative cap slices from slice nonemptiness.**

The target endpoint is indexed by the reversed last edge, so the foot window is
again `Ioc 0 c_max`. Once every slice
`endCapTgtMinus ∩ ball (p c) (r c)` is nonempty on that range, continuity of the
centre and radius functions gives local overlap automatically. -/
theorem local_overlap_endCapTgtMinus_of_slice_nonempty
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices_Ioo
      (cap := endCapTgtMinus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Target-negative cap slice nonemptiness from the sliver budget.**

Viewed from the target endpoint, `endCapTgtMinus` is the source-positive cap on
the reversed last edge. Under the same sliver inequality, one slides slightly
back along that reversed edge and lifts a tiny amount to the positive side. -/
theorem nonempty_endCapTgtMinus_slice_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
        < ρ (Fin.last β.numSegs) + min δ₀
            (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    (endCapTgtMinus β ρ ∩ Metric.ball
      (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolygonalArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolygonalArc.lastSeg, Fin.val_last]
    omega
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween :
      max 0 (c * dist s t - rad) < min (c * dist s t) (ρ (Fin.last β.numSegs)) := by
    by_cases hcr : c * dist s t ≤ ρ (Fin.last β.numSegs)
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ (Fin.last β.numSegs) < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ (Fin.last β.numSegs) := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρL, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ (Fin.last β.numSegs) := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ (Fin.last β.numSegs) - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ (Fin.last β.numSegs) - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d ε with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwsrc : dist w s < ρ (Fin.last β.numSegs) := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d ε
      rw [abs_of_nonneg hdpos.le, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ (Fin.last β.numSegs) - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d ε c 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr (by simpa [hvL] using hwsrc), ?_⟩, ?_⟩
  · simpa [hs, ht] using (show footParam t s w < 1 by
      rw [footParam_swap_eq hts w, hwfoot]
      linarith)
  · simpa [hs, ht] using (show sideForm t s w < 0 by
      rw [sideForm_swap]
      linarith)

/-- **Target-negative cap slice nonemptiness on a full foot range.**

This is the interval package for
`nonempty_endCapTgtMinus_slice_of_sliver_budget` on the reversed last edge. -/
theorem nonempty_endCapTgtMinus_slices_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapTgtMinus_slice_of_sliver_budget β R ρ hc.1 hρL ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the target-negative cap slices.**

This is the target-endpoint principal-foot overlap witness, indexed by the
reversed last edge so that the parameter range is again `Ioc 0 c_max`. -/
theorem local_overlap_endCapTgtMinus (β : PolygonalArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hclt⟩ := hc
  have hcle : c ≤ c_max := hclt.le
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolygonalArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolygonalArc.lastSeg, Fin.val_last]
    omega
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hclt⟩
  set K := min (min δ₀ (I0 / 4)) (ρ (Fin.last β.numSegs) - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ (Fin.last β.numSegs) - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c ε with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwball0 : dist w (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) := by
    rw [hvL]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c ε
      rw [abs_of_nonneg hc0.le, abs_of_nonneg hεpos.le] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapTgtMinus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, ?_⟩
    · simpa [hs, ht] using (show footParam t s w < 1 by
        rw [footParam_swap_eq hts w, hwfoot]
        linarith)
    · simpa [hs, ht] using (show sideForm t s w < 0 by
        rw [sideForm_swap]
        linarith)
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c 0
      simp only [sub_self, abs_zero, sub_zero, abs_of_nonneg hεpos.le, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c' 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The target-negative end cap is the union of reversed-last-edge slice balls
once every tube witness near the target endpoint comes from the last edge in the
same reversed foot window. -/
theorem taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapTgtMinus β ρ
      = ⋃ c ∈ Set.Ioo (0 : ℝ) c_max,
          endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) := by
  set s := β.segTgt β.lastSeg
  set t := β.segSrc β.lastSeg
  have hts : t ≠ s := by
    simpa [s, t] using (β.segTgt_ne_segSrc β.lastSeg).symm
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) + δ₀ := by
      have htri := dist_triangle p z (β.verts (Fin.last β.numSegs))
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioo (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by
      simpa [s, t, PolygonalArc.segCarrier, segment_symm] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped target-negative end cap is
preconnected once its tube witnesses are controlled by reversed-last-edge slices
over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapTgtMinus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtMinus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible target-negative clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapTgtMinus_of_near_spine`, the
overlap step is supplied by slice nonemptiness on the reversed-last-edge foot
range, with continuity handling the local intersections. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_slice_nonempty
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapTgtMinus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtMinus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A target-negative clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the reversed-last-edge foot range. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_sliver_budget
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  refine isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapTgtMinus_slices_of_sliver_budget β R ρ hδ₀ hρL hRpos hsliver

/-- **Local overlap of the target-positive cap slices from slice nonemptiness.**

The target-positive cap is the source-negative cap on the reversed last edge.
Once every reversed-last-edge slice is nonempty, continuity again gives local
overlap automatically. -/
theorem local_overlap_endCapTgtPlus_of_slice_nonempty
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices_Ioo
      (cap := endCapTgtPlus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Target-positive cap slice nonemptiness from the sliver budget.**

Viewed from the target endpoint, `endCapTgtPlus` is the source-negative cap on
the reversed last edge: slide slightly back along that reversed edge, then lift a
tiny amount to the negative side. -/
theorem nonempty_endCapTgtPlus_slice_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
        < ρ (Fin.last β.numSegs) + min δ₀
            (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    (endCapTgtPlus β ρ ∩ Metric.ball
      (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolygonalArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolygonalArc.lastSeg, Fin.val_last]
    omega
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween :
      max 0 (c * dist s t - rad) < min (c * dist s t) (ρ (Fin.last β.numSegs)) := by
    by_cases hcr : c * dist s t ≤ ρ (Fin.last β.numSegs)
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ (Fin.last β.numSegs) < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ (Fin.last β.numSegs) := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρL, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ (Fin.last β.numSegs) := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ (Fin.last β.numSegs) - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ (Fin.last β.numSegs) - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_nonneg hεpos.le]
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d (-ε) with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwsrc : dist w s < ρ (Fin.last β.numSegs) := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d (-ε)
      rw [abs_of_nonneg hdpos.le, hεabs] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ (Fin.last β.numSegs) - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d (-ε) c 0
      rw [sub_zero, hεabs] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr (by simpa [hvL] using hwsrc), ?_⟩, ?_⟩
  · simpa [hs, ht] using (show footParam t s w < 1 by
      rw [footParam_swap_eq hts w, hwfoot]
      linarith)
  · simpa [hs, ht] using (show 0 < sideForm t s w by
      rw [sideForm_swap]
      linarith)

/-- **Target-positive cap slice nonemptiness on a full foot range.** -/
theorem nonempty_endCapTgtPlus_slices_of_sliver_budget
    (β : PolygonalArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapTgtPlus_slice_of_sliver_budget β R ρ hc.1 hρL ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the target-positive cap slices.**

This is the target-endpoint principal-foot overlap witness on the reversed last
edge, using a tiny negative lift of the foot-`c` centre. -/
theorem local_overlap_endCapTgtPlus (β : PolygonalArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hclt⟩ := hc
  have hcle : c ≤ c_max := hclt.le
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolygonalArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolygonalArc.lastSeg, Fin.val_last]
    omega
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hclt⟩
  set K := min (min δ₀ (I0 / 4)) (ρ (Fin.last β.numSegs) - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ (Fin.last β.numSegs) - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c (-ε) with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwball0 : dist w (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) := by
    rw [hvL]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c (-ε)
      rw [abs_of_nonneg hc0.le, hεabs] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapTgtPlus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, ?_⟩
    · simpa [hs, ht] using (show footParam t s w < 1 by
        rw [footParam_swap_eq hts w, hwfoot]
        linarith)
    · simpa [hs, ht] using (show 0 < sideForm t s w by
        rw [sideForm_swap]
        linarith)
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c 0
      have hεabs' : |(-ε) - 0| = ε := by simpa using hεabs
      rw [sub_self, hεabs'] at h
      simp only [abs_zero, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c' 0
      rw [sub_zero, hεabs] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The target-positive end cap is the union of reversed-last-edge slice balls
once every tube witness near the target endpoint comes from the last edge in the
same reversed foot window. -/
theorem taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapTgtPlus β ρ
      = ⋃ c ∈ Set.Ioo (0 : ℝ) c_max,
          endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) := by
  set s := β.segTgt β.lastSeg
  set t := β.segSrc β.lastSeg
  have hts : t ≠ s := by
    simpa [s, t] using (β.segTgt_ne_segSrc β.lastSeg).symm
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) + δ₀ := by
      have htri := dist_triangle p z (β.verts (Fin.last β.numSegs))
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioo (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by
      simpa [s, t, PolygonalArc.segCarrier, segment_symm] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped target-positive end cap is
preconnected once its tube witnesses are controlled by reversed-last-edge slices
over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapTgtPlus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtPlus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible target-positive clipped-cap preconnectedness theorem. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_slice_nonempty
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapTgtPlus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtPlus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A target-positive clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the reversed-last-edge foot range. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_sliver_budget
    (β : PolygonalArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  refine isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapTgtPlus_slices_of_sliver_budget β R ρ hδ₀ hρL hRpos hsliver

/-- The `i`-th chain link of the negative collar. -/
noncomputable def collarChainMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (δ₀ α : ℝ) (i : Fin β.numSegs) : Set Plane :=
  bandStripMinus β α δ₀ i
    ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
    ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ)
    ∪ (⋃ (_ : (i : ℕ) = 0), endCapSrcMinus β ρ)

theorem iUnion_collarChainMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ) :
    (⋃ i, collarChainMinus β ρ δ₀ α i)
      = (⋃ i, bandStripMinus β α δ₀ i)
        ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
        ∪ endCapSrcMinus β ρ ∪ endCapTgtMinus β ρ := by
  ext z
  simp only [collarChainMinus, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, (((hb | hs) | ht) | he)⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, hb⟩))
    · obtain ⟨hi1, hsec⟩ := hs; exact Or.inl (Or.inl (Or.inr ⟨i, hi1, hsec⟩))
    · exact Or.inr ht.2
    · exact Or.inl (Or.inr he.2)
  · rintro (((⟨i, hb⟩ | ⟨i, hi1, hs⟩) | hsrc) | htgt)
    · exact ⟨i, Or.inl (Or.inl (Or.inl hb))⟩
    · exact ⟨i, Or.inl (Or.inl (Or.inr ⟨hi1, hs⟩))⟩
    · exact ⟨β.firstSeg, Or.inr ⟨rfl, hsrc⟩⟩
    · refine ⟨β.lastSeg, Or.inl (Or.inr ⟨?_, htgt⟩)⟩
      have h := β.numSegs_pos
      have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
      omega

theorem isPreconnected_collarChainMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ)
    (hα : 0 < α) (hα1 : α < 1)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinusClipped β δ₀ α i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty)
    (hO3 : (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty)
    (i : Fin β.numSegs) : IsPreconnected (collarChainMinus β ρ δ₀ α i) := by
  rw [collarChainMinus]
  have hband : IsPreconnected (bandStripMinus β α δ₀ i) :=
    (convex_bandStripMinus β α δ₀ i).isPreconnected
  have hS : IsPreconnected (bandStripMinus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1) := by
    refine isPreconnected_union_opt hband ?_ ?_
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      exact isPreconnected_sectorMinusClipped β δ₀ α i hi1 hα hα1 (hturn i hi1)
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      obtain ⟨y, hy⟩ := hO1 i hi1
      exact ⟨y, hy.2, hy.1⟩
  have hST : IsPreconnected ((bandStripMinus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
      ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ) := by
    refine isPreconnected_union_opt hS ?_ ?_
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      exact (convex_endCapTgtMinus β ρ).isPreconnected
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      have hil : i = β.lastSeg := by
        apply Fin.ext
        have h := β.numSegs_pos
        have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
        have hi := i.isLt
        omega
      obtain ⟨y, hy⟩ := hO4
      exact ⟨y, Or.inl (by rw [hil]; exact hy.2), hy.1⟩
  refine isPreconnected_union_opt hST ?_ ?_
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    exact (convex_endCapSrcMinus β ρ).isPreconnected
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    have hif : i = β.firstSeg := by
      apply Fin.ext
      have hf : (β.firstSeg : ℕ) = 0 := rfl
      omega
    obtain ⟨y, hy⟩ := hO3
    exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), hy.1⟩

/-- **P5⁻ clipped-collar assembly.**  The negative collar is preconnected once the band strips
and vertex sectors lie in the ground set and the two clipped negative end caps are
preconnected. -/
theorem isPreconnected_collarMinus (β : PolygonalArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbandW : ∀ i : Fin β.numSegs,
      bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ))
    (hTgtPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinusClipped β δ₀ α i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty)
    (hO2 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinusClipped β δ₀ α i hi1 ∩ bandStripMinus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty)
    (hO3 : (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty) :
    IsPreconnected (collarMinus β R S δ₀ α ρ) := by
  set W : Set Plane := taperedTube R S δ₀ \ β.carrier
  have hchain_pre : ∀ i : Fin β.numSegs, IsPreconnected (W ∩ collarChainMinus β ρ δ₀ α i) := by
    intro i
    have hbandEq : W ∩ bandStripMinus β α δ₀ i = bandStripMinus β α δ₀ i := by
      exact Set.inter_eq_right.mpr (by simpa [W] using hbandW i)
    have hsectorEq :
        W ∩ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1
          = ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1 := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨hi1, hzsec⟩
        refine ⟨?_, Set.mem_iUnion.mpr ⟨hi1, hzsec⟩⟩
        simpa [W] using hsectorW i hi1 hzsec
    have hTgtEq :
        W ∩ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ
          = ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hztgt⟩
        exact ⟨hztgt.1, hzW, hztgt.2⟩
      · rintro ⟨hnl, hzW, hztgt⟩
        exact ⟨hzW, ⟨hnl, hztgt⟩⟩
    have hSrcEq :
        W ∩ ⋃ (_ : (i : ℕ) = 0), endCapSrcMinus β ρ
          = ⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcMinus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hzsrc⟩
        exact ⟨hzsrc.1, hzW, hzsrc.2⟩
      · rintro ⟨h0, hzW, hzsrc⟩
        exact ⟨hzW, ⟨h0, hzsrc⟩⟩
    have hchain :
        W ∩ collarChainMinus β ρ δ₀ α i
          = bandStripMinus β α δ₀ i
              ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
              ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ)
              ∪ (⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcMinus β ρ) := by
      rw [collarChainMinus]
      simp_rw [Set.inter_union_distrib_left]
      rw [hbandEq, hsectorEq, hTgtEq, hSrcEq]
    rw [hchain]
    have hbandPre : IsPreconnected (bandStripMinus β α δ₀ i) :=
      (convex_bandStripMinus β α δ₀ i).isPreconnected
    have hS : IsPreconnected (bandStripMinus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1) := by
      refine isPreconnected_union_opt hbandPre ?_ ?_
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        exact isPreconnected_sectorMinusClipped β δ₀ α i hi1 hα hα1 (hturn i hi1)
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        obtain ⟨y, hy⟩ := hO1 i hi1
        exact ⟨y, hy.2, hy.1⟩
    have hST : IsPreconnected ((bandStripMinus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
        ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ) := by
      refine isPreconnected_union_opt hS ?_ ?_
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        simpa [W] using hTgtPre
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        have hil : i = β.lastSeg := by
          apply Fin.ext
          have h := β.numSegs_pos
          have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
          have hi := i.isLt
          omega
        obtain ⟨y, hy⟩ := hO4
        have hyW : y ∈ W := by
          simpa [W, hil] using hbandW β.lastSeg hy.2
        exact ⟨y, Or.inl (by rw [hil]; exact hy.2), ⟨hyW, hy.1⟩⟩
    refine isPreconnected_union_opt hST ?_ ?_
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      simpa [W] using hSrcPre
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      have hif : i = β.firstSeg := by
        apply Fin.ext
        have hf : (β.firstSeg : ℕ) = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hO3
      have hyW : y ∈ W := by
        simpa [W, hif] using hbandW β.firstSeg hy.2
      exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), ⟨hyW, hy.1⟩⟩
  have hcollar : collarMinus β R S δ₀ α ρ = ⋃ i, W ∩ collarChainMinus β ρ δ₀ α i := by
    ext z
    constructor
    · rintro ⟨hzW, hzM⟩
      rw [← iUnion_collarChainMinus β ρ δ₀ α] at hzM
      rcases Set.mem_iUnion.mp hzM with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨hzW, hzi⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      refine ⟨hzi.1, ?_⟩
      rw [← iUnion_collarChainMinus β ρ δ₀ α]
      exact Set.mem_iUnion.mpr ⟨i, hzi.2⟩
  rw [hcollar]
  refine isPreconnected_iUnion_fin_chain _
    hchain_pre ?_
  intro i hi
  obtain ⟨y, hy⟩ := hO2 ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  have hyW : y ∈ W := by
    simpa [W] using hbandW ⟨(i : ℕ) + 1, hi⟩ hy.2
  refine ⟨y, ?_, ?_⟩
  · rw [collarChainMinus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨hi, hy.1⟩)))⟩
  · rw [collarChainMinus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inl hy.2))⟩

/-- **hO3⁻.** The negative source end cap meets band `firstSeg`. -/
theorem overlap_endCapSrcMinus_bandStripMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0) :
    (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (2 * α) (-ε) with hz
  have hfoot : footParam s t z = 2 * α := by rw [hz]; exact footParam_liftPlus hts (2 * α) (-ε)
  have hside : sideForm s t z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hP; nlinarith
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolygonalArc.firstSeg]
    rw [hs, PolygonalArc.segSrc, hcast]
  have hball : z ∈ Metric.ball (β.verts 0) (ρ 0) := by
    rw [Metric.mem_ball, hv0]
    have hd : dist z s ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t (2 * α) (-ε)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.firstSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier β.firstSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show 0 < footParam s t z; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO4⁻.** The negative target end cap meets band `lastSeg`. -/
theorem overlap_endCapTgtMinus_bandStripMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
      < ρ (Fin.last β.numSegs)) :
    (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty := by
  set s := β.segSrc β.lastSeg with hs
  set t := β.segTgt β.lastSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.lastSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (1 - 2 * α) (-ε) with hz
  have hfoot : footParam s t z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hts (1 - 2 * α) (-ε)
  have hside : sideForm s t z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hP; nlinarith
  have hvL : β.verts (Fin.last β.numSegs) = t := by
    rw [ht, PolygonalArc.segTgt]; congr 1
    apply Fin.ext; have h := β.numSegs_pos; simp [PolygonalArc.lastSeg, Fin.val_last]
    omega
  have hball : z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)) := by
    rw [Metric.mem_ball, hvL]
    have hd : dist z t ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_tgt_le s t (1 - 2 * α) (-ε)
      have he : |1 - (1 - 2 * α)| = 2 * α := by rw [show 1 - (1 - 2 * α) = 2 * α from by ring,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]
      rw [he, haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.lastSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier β.lastSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show footParam s t z < 1; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO1⁻.** The vertex sector at `verts (i+1)` meets band `i` (incoming, minus side). -/
theorem overlap_sectorMinus_bandStripMinus_src (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) (-ε) with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) (-ε)
  have hside : sideForm a v z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, abs_neg, hz, sideForm_liftPlus, abs_mul, abs_neg,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) (-ε)
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to incoming edge `i` ⇒ left (`stripSupport i`) disjunct of the
  -- union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inl hinf⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **hO2⁻.** The vertex sector at `verts (i+1)` meets band `i+1` (outgoing, minus side). -/
theorem overlap_sectorMinus_bandStripMinus_tgt (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) (-ε) with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) (-ε)
  have hside : sideForm v b z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_neg, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) (-ε)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to outgoing edge `i+1` ⇒ right (`stripSupport (i+1)`) disjunct of
  -- the union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inr hinf⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **Clipped hO1⁻.** The *clipped* vertex sector at `verts (i+1)` meets band `i` (incoming, minus
side).  Same witness as `overlap_sectorMinus_bandStripMinus_src`; foot-clip `α < footParam = 1 − 2α`
holds via `α < 1/3`. -/
theorem overlap_sectorMinusClipped_bandStripMinus_src (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorMinusClipped β δ₀ α i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) (-ε) with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) (-ε)
  have hside : sideForm a v z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, abs_neg, hz, sideForm_liftPlus, abs_mul, abs_neg,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) (-ε)
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION (clipped): incoming arm; foot-clip `α < footParam = 1 − 2α` holds via `hα3`.
  exact ⟨z, ⟨hmemV, Or.inl ⟨hinf,
      by show α < footParam (β.segSrc i) (β.segTgt i) z; rw [hfoot]; linarith⟩⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **Clipped hO2⁻.** The *clipped* vertex sector at `verts (i+1)` meets band `i+1` (outgoing, minus
side).  Same witness as `overlap_sectorMinus_bandStripMinus_tgt`; foot-clip `footParam = 2α < 1 − α`
holds via `α < 1/3`. -/
theorem overlap_sectorMinusClipped_bandStripMinus_tgt (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorMinusClipped β δ₀ α i hi1 ∩ bandStripMinus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) (-ε) with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) (-ε)
  have hside : sideForm v b z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_neg, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) (-ε)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION (clipped): outgoing arm; foot-clip `footParam = 2α < 1 − α` holds via `hα3`.
  have hclip : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z < 1 - α := by
    rw [hsvb, ← hb, hfoot]; linarith
  exact ⟨z, ⟨hmemV, Or.inr ⟨hinf, hclip⟩⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩


end CrossingLemma.PlaneArcSeparation
