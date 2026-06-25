/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PolygonalArc shard 4/7 — **Existence**: P4 (a scaled-normal witness off the first-edge
midpoint shows the collar is nonempty) and the P3 existence primitives (the
per-corner separation threshold and the global assembly). Split out of
`PolygonalArc.lean`; see that coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.CollarConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Disjointness

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! ### P4 (nonempty) — a scaled-normal witness off the first-edge midpoint.

Each collar side contains the midpoint of edge `0` pushed a tiny `ε` along the edge
normal: the push keeps the foot parameter at `1/2` (so the point is in the first
band, given `α < 1/2`), gives `sideForm` the chosen sign, and — with `ε·‖edge‖₁`
below the tube cap, the region clearance, and the separation to every other edge —
lands the point in `taperedTube ∖ carrier` close to edge `0`. -/

/-- Midpoint of the first edge (foot parameter `1/2`, on the first segment). -/
noncomputable def firstMid (β : PolygonalArc) : Plane :=
  (((β.segSrc β.firstSeg).1 + (β.segTgt β.firstSeg).1) / 2,
   ((β.segSrc β.firstSeg).2 + (β.segTgt β.firstSeg).2) / 2)

theorem firstMid_mem_segCarrier (β : PolygonalArc) :
    firstMid β ∈ β.segCarrier β.firstSeg := by
  rw [PolygonalArc.segCarrier]
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  refine Prod.ext ?_ ?_ <;>
    simp only [firstMid, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
      Prod.snd_add] <;> ring

theorem firstMid_footParam (β : PolygonalArc) :
    footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 / 2 := by
  have hP : dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
      (β.segTgt β.firstSeg - β.segSrc β.firstSeg) ≠ 0 :=
    (dotp_self_pos (β.segTgt_ne_segSrc β.firstSeg)).ne'
  rw [footParam]
  have hnum : dotp (firstMid β - β.segSrc β.firstSeg)
        (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
      = dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
          (β.segTgt β.firstSeg - β.segSrc β.firstSeg) / 2 := by
    simp only [dotp, firstMid, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hnum]; field_simp

theorem firstMid_notMem_segCarrier (β : PolygonalArc) {k : Fin β.numSegs} (hk : k ≠ β.firstSeg) :
    firstMid β ∉ β.segCarrier k := by
  intro hmem
  have hf0 : firstMid β ∈ segment ℝ (β.verts (Fin.castSucc β.firstSeg))
      (β.verts (Fin.succ β.firstSeg)) := by
    have h := firstMid_mem_segCarrier β
    rwa [PolygonalArc.segCarrier, PolygonalArc.segSrc, PolygonalArc.segTgt] at h
  have hfk : firstMid β ∈ segment ℝ (β.verts (Fin.castSucc k)) (β.verts (Fin.succ k)) := by
    rwa [PolygonalArc.segCarrier, PolygonalArc.segSrc, PolygonalArc.segTgt] at hmem
  have hk0 : (k : ℕ) ≠ 0 := by
    intro h; exact hk (Fin.ext (by simp [PolygonalArc.firstSeg, h]))
  rcases Nat.lt_or_ge 1 (k : ℕ) with hgt | hle
  · have hadj : (β.firstSeg : Fin β.numSegs).val + 1 < (k : ℕ) := by
      simp only [PolygonalArc.firstSeg]; omega
    exact (Set.disjoint_left.mp (β.nonadjacent_disjoint β.firstSeg k hadj)) hf0 hfk
  · have hk1 : (k : ℕ) = 1 := by omega
    have hlt : (β.firstSeg : Fin β.numSegs).val + 1 < β.numSegs := by
      simp only [PolygonalArc.firstSeg]; have := k.isLt; omega
    have hkeq : k = ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩ :=
      Fin.ext (by simp only [PolygonalArc.firstSeg, Fin.val_mk]; omega)
    have hcast : (Fin.castSucc ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩ : Fin (β.numSegs + 1))
        = Fin.succ β.firstSeg := Fin.ext (by simp [Fin.val_succ])
    have hfk' : firstMid β ∈ segment ℝ (β.verts (Fin.succ β.firstSeg))
        (β.verts (Fin.succ ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩)) := by
      rw [hkeq] at hfk; rwa [hcast] at hfk
    have hsingle : firstMid β ∈ ({β.verts (Fin.succ β.firstSeg)} : Set Plane) :=
      β.consecutive_meet β.firstSeg hlt ⟨hf0, hfk'⟩
    rw [Set.mem_singleton_iff] at hsingle
    have hfoot1 : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 := by
      rw [hsingle]
      exact footParam_tgt (β.segTgt_ne_segSrc β.firstSeg)
    have h12 := firstMid_footParam β
    rw [hfoot1] at h12; norm_num at h12

/-- **Uniform region clearance over a compact spine window.**

For a compact set `K` contained in an open region `R` (with nonempty complement),
the distance to the boundary `infDist y Rᶜ` is bounded below by a single positive
constant `d`, uniformly over `y ∈ K`.

This is the elementary compactness keystone shared by every `δ₀`-vs-`Rᶜ` budget of
the collar instantiation: the band foot-window certificate `hRband`, the end-cap
radius positivities `hSrcRpos`/`hTgtRpos`, the vertex-disk region budget `hρR`, and
`hmR` all need `δ₀ ≤ ½·infDist · Rᶜ` over a compact carrier window, and they are all
discharged by choosing `δ₀` below `d/2`.

Proof: `infDist · Rᶜ` is continuous (`continuous_infDist_pt`), so on the compact `K`
it attains a minimum at some `y₀ ∈ K` (extreme value theorem,
`IsCompact.exists_isMinOn`); since `y₀ ∈ K ⊆ R` and `Rᶜ` is closed, that minimum is
strictly positive (`IsClosed.notMem_iff_infDist_pos`).  The empty case returns `1`. -/
theorem exists_pos_infDist_compl_of_isCompact {R K : Set Plane}
    (hR : IsOpen R) (hRc : Rᶜ.Nonempty) (hK : IsCompact K) (hKR : K ⊆ R) :
    ∃ d : ℝ, 0 < d ∧ ∀ y ∈ K, d ≤ Metric.infDist y Rᶜ := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun y hy => absurd (hKe ▸ hy) (by simp)⟩
  · obtain ⟨y₀, hy₀K, hy₀min⟩ :=
      hK.exists_isMinOn hKne (Metric.continuous_infDist_pt (Rᶜ)).continuousOn
    have hpos : 0 < Metric.infDist y₀ Rᶜ :=
      (hR.isClosed_compl.notMem_iff_infDist_pos hRc).mp
        (fun h => h (hKR hy₀K))
    exact ⟨Metric.infDist y₀ Rᶜ, hpos, fun y hy => (isMinOn_iff.mp hy₀min) y hy⟩

/-- A single positive radius `B` below which a witness within `B` of `firstMid β` is
inside the tube cap, the region clearance, and the separation to every other edge. -/
theorem exists_firstMid_radius (β : PolygonalArc) (R : Set Plane) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    ∃ B : ℝ, 0 < B ∧ B ≤ δ₀ ∧ B ≤ Metric.infDist (firstMid β) Rᶜ / 2
      ∧ ∀ k : Fin β.numSegs, k ≠ β.firstSeg →
          B ≤ Metric.infDist (firstMid β) (β.segCarrier k) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun k => if k = β.firstSeg then 1 else Metric.infDist (firstMid β) (β.segCarrier k) with hf
  have hfpos : ∀ k, 0 < f k := by
    intro k; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact k).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc k, left_mem_segment ℝ _ _⟩).mp (firstMid_notMem_segCarrier β h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty := ⟨β.firstSeg, Finset.mem_univ _⟩
  set σ := Finset.univ.inf' hne f with hσ
  have hσpos : 0 < σ := by rw [hσ, Finset.lt_inf'_iff]; exact fun k _ => hfpos k
  refine ⟨min δ₀ (min (Metric.infDist (firstMid β) Rᶜ / 2) σ),
    lt_min hδ₀ (lt_min (by linarith) hσpos), min_le_left _ _,
    le_trans (min_le_right _ _) (min_le_left _ _), fun k hk => ?_⟩
  have hle : σ ≤ f k := Finset.inf'_le f (Finset.mem_univ k)
  have hfk : f k = Metric.infDist (firstMid β) (β.segCarrier k) := by
    simp only [hf]; rw [if_neg hk]
  rw [hfk] at hle
  exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hle

/-- The coordinate-free core: a point close to `firstMid β` (within the tube cap, the
region clearance, and every other edge's separation) and off the first edge's line is
in the ground set `taperedTube ∖ carrier` and is `< δ₀` from the first segment. -/
theorem firstMid_push_in_ground (β : PolygonalArc) (R S : Set Plane) {δ₀ : ℝ}
    (hmS : firstMid β ∈ S) {w : Plane}
    (htube : dist w (firstMid β) < δ₀)
    (hR : dist w (firstMid β) < Metric.infDist (firstMid β) Rᶜ / 2)
    (hsep : ∀ k : Fin β.numSegs, k ≠ β.firstSeg →
      dist w (firstMid β) < Metric.infDist (firstMid β) (β.segCarrier k))
    (hsf0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) w ≠ 0) :
    w ∈ taperedTube R S δ₀ \ β.carrier
      ∧ Metric.infDist w (β.segCarrier β.firstSeg) < δ₀ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [taperedTube]
    exact Set.mem_iUnion₂.mpr ⟨firstMid β, hmS, Metric.mem_ball.mpr (lt_min htube hR)⟩
  · rw [PolygonalArc.carrier, Set.mem_iUnion]
    rintro ⟨k, hk⟩
    by_cases hkf : k = β.firstSeg
    · subst hkf
      rw [PolygonalArc.segCarrier] at hk
      exact hsf0 (sideForm_eq_zero_of_mem_segment _ _ hk)
    · have htri : Metric.infDist (firstMid β) (β.segCarrier k)
          ≤ Metric.infDist w (β.segCarrier k) + dist (firstMid β) w :=
        Metric.infDist_le_infDist_add_dist
      rw [Metric.infDist_zero_of_mem hk, zero_add, dist_comm] at htri
      exact absurd (hsep k hkf) (not_lt.mpr htri)
  · exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem (firstMid_mem_segCarrier β)) htube

/-- **P4⁺ (nonempty).**  Needs the first-edge midpoint inside the spine `S` and
strictly interior to `R`, and `α < 1/2`. -/
theorem collarPlus_nonempty (β : PolygonalArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    (collarPlus β R S δ₀ α ρ).Nonempty := by
  obtain ⟨B, hBpos, hBδ, hBR, hBseg⟩ := exists_firstMid_radius β R hδ₀ hmR
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  set L := |t.1 - s.1| + |t.2 - s.2| with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; by_contra h; push Not at h
    have ha1 := abs_nonneg (t.1 - s.1); have ha2 := abs_nonneg (t.2 - s.2)
    exact hts (Prod.ext (by have := abs_eq_zero.mp (by linarith : |t.1 - s.1| = 0); linarith)
      (by have := abs_eq_zero.mp (by linarith : |t.2 - s.2| = 0); linarith))
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set ε := B / (L + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * L < B := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hLp1]; nlinarith
  set w : Plane := ((s.1 + t.1) / 2 - ε * (t.2 - s.2), (s.2 + t.2) / 2 + ε * (t.1 - s.1)) with hw
  have e1 : w.1 = (s.1 + t.1) / 2 - ε * (t.2 - s.2) := by rw [hw]
  have e2 : w.2 = (s.2 + t.2) / 2 + ε * (t.1 - s.1) := by rw [hw]
  have hm1 : (firstMid β).1 = (s.1 + t.1) / 2 := by rw [hs, ht]; rfl
  have hm2 : (firstMid β).2 = (s.2 + t.2) / 2 := by rw [hs, ht]; rfl
  have hdwm : dist w (firstMid β) ≤ ε * L := by
    rw [Prod.dist_eq, hm1, hm2, Real.dist_eq, Real.dist_eq, e1, e2,
      show (s.1 + t.1) / 2 - ε * (t.2 - s.2) - (s.1 + t.1) / 2 = -(ε * (t.2 - s.2)) from by ring,
      show (s.2 + t.2) / 2 + ε * (t.1 - s.1) - (s.2 + t.2) / 2 = ε * (t.1 - s.1) from by ring]
    simp only [abs_neg, abs_mul, abs_of_pos hεpos]
    rw [hLdef]
    apply max_le <;>
      nlinarith [mul_nonneg hεpos.le (abs_nonneg (t.1 - s.1)),
        mul_nonneg hεpos.le (abs_nonneg (t.2 - s.2))]
  have hdwmB : dist w (firstMid β) < B := lt_of_le_of_lt hdwm hεL
  have hsfw : sideForm s t w = ε * dotp (t - s) (t - s) := by
    simp only [sideForm, dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
  have hsfpos : 0 < sideForm s t w := by rw [hsfw]; exact mul_pos hεpos hP
  have hfoot : footParam s t w = 1 / 2 := by
    rw [footParam]
    have hnum : dotp (w - s) (t - s) = dotp (t - s) (t - s) / 2 := by
      simp only [dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hnum]; field_simp
  obtain ⟨hground, hinf⟩ := firstMid_push_in_ground β R S hmS
    (lt_of_lt_of_le hdwmB hBδ) (lt_of_lt_of_le hdwmB hBR)
    (fun k hk => lt_of_lt_of_le hdwmB (hBseg k hk)) hsfpos.ne'
  refine ⟨w, hground, Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩)))⟩
  rw [bandStripPlus, edgePlusMid]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [edgeBandMid, Set.mem_setOf_eq, ← hs, ← ht, hfoot, Set.mem_Ioo]
    constructor <;> linarith
  · show 0 < sideForm s t w
    exact hsfpos
  · show Metric.infDist w (β.segCarrier β.firstSeg) < δ₀
    exact hinf

/-- **P4⁻ (nonempty).** -/
theorem collarMinus_nonempty (β : PolygonalArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    (collarMinus β R S δ₀ α ρ).Nonempty := by
  obtain ⟨B, hBpos, hBδ, hBR, hBseg⟩ := exists_firstMid_radius β R hδ₀ hmR
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  set L := |t.1 - s.1| + |t.2 - s.2| with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; by_contra h; push Not at h
    have ha1 := abs_nonneg (t.1 - s.1); have ha2 := abs_nonneg (t.2 - s.2)
    exact hts (Prod.ext (by have := abs_eq_zero.mp (by linarith : |t.1 - s.1| = 0); linarith)
      (by have := abs_eq_zero.mp (by linarith : |t.2 - s.2| = 0); linarith))
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set ε := B / (L + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * L < B := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hLp1]; nlinarith
  set w : Plane := ((s.1 + t.1) / 2 + ε * (t.2 - s.2), (s.2 + t.2) / 2 - ε * (t.1 - s.1)) with hw
  have e1 : w.1 = (s.1 + t.1) / 2 + ε * (t.2 - s.2) := by rw [hw]
  have e2 : w.2 = (s.2 + t.2) / 2 - ε * (t.1 - s.1) := by rw [hw]
  have hm1 : (firstMid β).1 = (s.1 + t.1) / 2 := by rw [hs, ht]; rfl
  have hm2 : (firstMid β).2 = (s.2 + t.2) / 2 := by rw [hs, ht]; rfl
  have hdwm : dist w (firstMid β) ≤ ε * L := by
    rw [Prod.dist_eq, hm1, hm2, Real.dist_eq, Real.dist_eq, e1, e2,
      show (s.1 + t.1) / 2 + ε * (t.2 - s.2) - (s.1 + t.1) / 2 = ε * (t.2 - s.2) from by ring,
      show (s.2 + t.2) / 2 - ε * (t.1 - s.1) - (s.2 + t.2) / 2 = -(ε * (t.1 - s.1)) from by ring]
    simp only [abs_neg, abs_mul, abs_of_pos hεpos]
    rw [hLdef]
    apply max_le <;>
      nlinarith [mul_nonneg hεpos.le (abs_nonneg (t.1 - s.1)),
        mul_nonneg hεpos.le (abs_nonneg (t.2 - s.2))]
  have hdwmB : dist w (firstMid β) < B := lt_of_le_of_lt hdwm hεL
  have hsfw : sideForm s t w = -(ε * dotp (t - s) (t - s)) := by
    simp only [sideForm, dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
  have hsfneg : sideForm s t w < 0 := by
    rw [hsfw]; have := mul_pos hεpos hP; linarith
  have hfoot : footParam s t w = 1 / 2 := by
    rw [footParam]
    have hnum : dotp (w - s) (t - s) = dotp (t - s) (t - s) / 2 := by
      simp only [dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hnum]; field_simp
  obtain ⟨hground, hinf⟩ := firstMid_push_in_ground β R S hmS
    (lt_of_lt_of_le hdwmB hBδ) (lt_of_lt_of_le hdwmB hBR)
    (fun k hk => lt_of_lt_of_le hdwmB (hBseg k hk)) (ne_of_lt hsfneg)
  refine ⟨w, hground, Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩)))⟩
  rw [bandStripMinus, edgeMinusMid]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [edgeBandMid, Set.mem_setOf_eq, ← hs, ← ht, hfoot, Set.mem_Ioo]
    constructor <;> linarith
  · show sideForm s t w < 0
    exact hsfneg
  · show Metric.infDist w (β.segCarrier β.firstSeg) < δ₀
    exact hinf

/-! #### P3 existence — the per-corner threshold.

For each interior vertex (corner `c`), a single positive `δ` below which the corner's
band/band impossibility (both arms) and the two angle-free thinness inequalities all hold
at any width `δ₀ ≤ δ`.  Combines `exists_delta_corner_confine` (at radius `r = α/(1+L_c+
L_{c+1})`, so both Lipschitz budgets `L·r ≤ α` are met) with the `M/(K+1)` thresholds for
the `hδin`/`hδout` shapes (whose `sideForm` factor is `±cornerTurn ≠ 0`).  Stated totally
over `c` (vacuous when `c` is not a corner) so the global step can skolemize and minimise. -/
theorem exists_corner_delta (β : PolygonalArc) {α : ℝ} (hα : 0 < α)
    (hturn : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (c : Fin β.numSegs) :
    ∃ (δ r : ℝ), 0 < δ ∧ ∀ (hc1 : (c : ℕ) + 1 < β.numSegs) (δ₀ : ℝ), 0 < δ₀ → δ₀ ≤ δ →
      (∀ z : Plane, z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
        Metric.infDist z (β.segCarrier c) < δ₀ →
        Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False) ∧
      (∀ z : Plane,
        z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
        Metric.infDist z (β.segCarrier c) < δ₀ →
        Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False) ∧
      (|dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c))) ∧
      (|dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c))) ∧
      (∀ z : Plane, Metric.infDist z (β.segCarrier c) < δ₀ →
        Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ →
        dist z (β.verts (Fin.succ c)) < r) ∧
      (|(β.segTgt c).1 - (β.segSrc c).1| + |(β.segTgt c).2 - (β.segSrc c).2|)
          / dotp (β.segTgt c - β.segSrc c) (β.segTgt c - β.segSrc c) * r ≤ α ∧
      (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).1|
          + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).2|)
          / dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩)
                 (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩) * r ≤ α := by
  by_cases hc1 : (c : ℕ) + 1 < β.numSegs
  · have hva : β.segTgt c ≠ β.segSrc c := β.segTgt_ne_segSrc c
    have hcc1 : β.segTgt ⟨(c : ℕ) + 1, hc1⟩ ≠ β.segSrc ⟨(c : ℕ) + 1, hc1⟩ :=
      β.segTgt_ne_segSrc _
    have htt : β.segTgt ⟨(c : ℕ) + 1, hc1⟩ ≠ β.segTgt c := by
      rw [PolygonalArc.segTgt, PolygonalArc.segTgt]; intro h
      have hval := congrArg Fin.val (β.distinct h)
      simp only [Fin.val_succ] at hval; omega
    set Lc := (|(β.segTgt c).1 - (β.segSrc c).1| + |(β.segTgt c).2 - (β.segSrc c).2|)
        / dotp (β.segTgt c - β.segSrc c) (β.segTgt c - β.segSrc c) with hLcdef
    set Lc1 := (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).1|
          + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).2|)
        / dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩)
               (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩) with hLc1def
    have hLcpos : 0 < Lc := div_pos (segDir_l1_pos β c) (dotp_self_pos hva)
    have hLc1pos : 0 < Lc1 := div_pos (segDir_l1_pos β ⟨(c : ℕ) + 1, hc1⟩) (dotp_self_pos hcc1)
    set r := α / (1 + Lc + Lc1) with hrdef
    have hrden : (0 : ℝ) < 1 + Lc + Lc1 := by linarith
    have hrpos : 0 < r := div_pos hα hrden
    have hLcr : Lc * r ≤ α := by
      rw [hrdef, ← mul_div_assoc, div_le_iff₀ hrden]; nlinarith [hLcpos, hLc1pos, hα]
    have hLc1r : Lc1 * r ≤ α := by
      rw [hrdef, ← mul_div_assoc, div_le_iff₀ hrden]; nlinarith [hLcpos, hLc1pos, hα]
    obtain ⟨δconf, hδconfpos, hconf⟩ := exists_delta_corner_confine β c hc1 hrpos
    have hsf_in_ne : sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c) ≠ 0 := by
      have key : sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)
          = - cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) := by
        rw [cornerTurn, sideForm_swap, ← sideForm_cyclic]
      rw [key]; exact neg_ne_zero.mpr (hturn c hc1)
    have hsf_out_ne : sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0 :=
      hturn c hc1
    have hdotc : 0 < dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c) :=
      dotp_self_pos hva.symm
    have hdotc1 : 0 < dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
        (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c) := dotp_self_pos htt
    set Kin := |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
        * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) with hKindef
    set Min := |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
        * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)) with hMindef
    set Kout := |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
        * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
            + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) with hKoutdef
    set Mout := |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
        * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                   (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)) with hMoutdef
    have hKinnn : 0 ≤ Kin := by rw [hKindef]; positivity
    have hKoutnn : 0 ≤ Kout := by rw [hKoutdef]; positivity
    have hMinpos : 0 < Min := by
      rw [hMindef]; exact mul_pos (abs_pos.mpr hsf_in_ne) (mul_pos hα hdotc)
    have hMoutpos : 0 < Mout := by
      rw [hMoutdef]; exact mul_pos (abs_pos.mpr hsf_out_ne) (mul_pos hα hdotc1)
    have hKδin : Kin * (Min / (Kin + 1)) < Min := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < Kin + 1)]
      nlinarith [hMinpos, hKinnn]
    have hKδout : Kout * (Mout / (Kout + 1)) < Mout := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < Kout + 1)]
      nlinarith [hMoutpos, hKoutnn]
    refine ⟨min δconf (min (Min / (Kin + 1)) (Mout / (Kout + 1))), r,
      lt_min hδconfpos (lt_min (div_pos hMinpos (by linarith)) (div_pos hMoutpos (by linarith))),
      ?_⟩
    intro hc1' δ₀ h0 hle
    have hleconf : δ₀ ≤ δconf := le_trans hle (min_le_left _ _)
    have hlein : δ₀ ≤ Min / (Kin + 1) :=
      le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hleout : δ₀ ≤ Mout / (Kout + 1) :=
      le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hmid hzi hzi1
      refine not_mem_adjacent_band_strip β c hc1 (fun w hwi hwi1 =>
        hconf w (lt_of_lt_of_le hwi hleconf) (lt_of_lt_of_le hwi1 hleconf)) ?_ hmid hzi hzi1
      rw [← hLcdef]; exact hLcr
    · intro z hmid hzi hzi1
      refine not_mem_adjacent_band_strip_src β c hc1 (fun w hwi hwi1 =>
        hconf w (lt_of_lt_of_le hwi hleconf) (lt_of_lt_of_le hwi1 hleconf)) ?_ hmid hzi hzi1
      rw [← hLc1def]; exact hLc1r
    · rw [← hKindef, ← hMindef]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlein hKinnn) hKδin
    · rw [← hKoutdef, ← hMoutdef]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hleout hKoutnn) hKδout
    · intro z hzi hzi1
      exact hconf z (lt_of_lt_of_le hzi hleconf) (lt_of_lt_of_le hzi1 hleconf)
    · exact hLcr
    · exact hLc1r
  · exact ⟨1, 1, one_pos, fun h => absurd h hc1⟩

/-! #### P3 existence — the global assembly.

Picks concrete admissible parameters: a common `δ₀ = ρ₀` taken as half the minimum of the
per-corner thresholds, the non-adjacent separation `δsep`, the endpoint-edge gaps, and the
disk radius.  Every hypothesis family of `disjoint_collarPlus_collarMinus` is then below its
budget, so the two collar sides are disjoint. -/

/-- **The two collar sides can be made disjoint** by a concrete choice of `δ₀` and a
constant disk-radius `ρ`, for any narrowing width `α > 0`, provided the arc has no straight
corners (`hturn`). -/
theorem exists_collar_disjoint (β : PolygonalArc) (R S : Set Plane) {α : ℝ} (hα : 0 < α)
    (hturn : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0) :
    ∃ (δ₀ : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ), 0 < δ₀ ∧ (∀ p, 0 < ρ p) ∧
      Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
  classical
  choose δfun rfun hδfunpos hδfunprop using exists_corner_delta β hα hturn
  obtain ⟨δsep, hδseppos, hsep⟩ := exists_delta_nonadjacent_tube_sep β
  obtain ⟨ρ₀, hρ₀pos, hballs0⟩ := exists_pos_disk_radius β
  obtain ⟨dsrc, hdsrcpos, hsrcsep⟩ := exists_pos_src_edge_sep β
  obtain ⟨dtgt, hdtgtpos, htgtsep⟩ := exists_pos_tgt_edge_sep β
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set δcorner := Finset.univ.inf' hne δfun with hδcdef
  have hδcornerpos : 0 < δcorner := by
    rw [hδcdef, Finset.lt_inf'_iff]; exact fun c _ => hδfunpos c
  set LfirstSeg := (|(β.segTgt β.firstSeg).1 - (β.segSrc β.firstSeg).1|
      + |(β.segTgt β.firstSeg).2 - (β.segSrc β.firstSeg).2|)
      / dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
             (β.segTgt β.firstSeg - β.segSrc β.firstSeg) with hLfsdef
  set LlastSeg := (|(β.segTgt β.lastSeg).1 - (β.segSrc β.lastSeg).1|
      + |(β.segTgt β.lastSeg).2 - (β.segSrc β.lastSeg).2|)
      / dotp (β.segTgt β.lastSeg - β.segSrc β.lastSeg)
             (β.segTgt β.lastSeg - β.segSrc β.lastSeg) with hLlsdef
  have hLfspos : 0 < LfirstSeg :=
    div_pos (segDir_l1_pos β β.firstSeg) (dotp_self_pos (β.segTgt_ne_segSrc β.firstSeg))
  have hLlspos : 0 < LlastSeg :=
    div_pos (segDir_l1_pos β β.lastSeg) (dotp_self_pos (β.segTgt_ne_segSrc β.lastSeg))
  set M5 := min δcorner (min δsep (min (dsrc / 2) (min (dtgt / 2)
      (min ρ₀ (min (α / LfirstSeg) (α / LlastSeg)))))) with hM5def
  have hM5pos : 0 < M5 := by
    rw [hM5def]
    exact lt_min hδcornerpos (lt_min hδseppos
      (lt_min (by linarith) (lt_min (by linarith)
        (lt_min hρ₀pos (lt_min (div_pos hα hLfspos) (div_pos hα hLlspos))))))
  have h1 : M5 ≤ δcorner := min_le_left _ _
  have h2 : M5 ≤ δsep := le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : M5 ≤ dsrc / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : M5 ≤ dtgt / 2 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h5 : M5 ≤ ρ₀ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have h6 : M5 ≤ α / LfirstSeg := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have h7 : M5 ≤ α / LlastSeg := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))))
  refine ⟨M5 / 2, fun _ => M5 / 2, by linarith, fun _ => by linarith, ?_⟩
  have ht_δfun : ∀ c : Fin β.numSegs, M5 / 2 ≤ δfun c := by
    intro c
    have : δcorner ≤ δfun c := Finset.inf'_le δfun (Finset.mem_univ c)
    linarith
  have ht_pos : (0 : ℝ) < M5 / 2 := by linarith
  refine disjoint_collarPlus_collarMinus β R S (fun _ => M5 / 2) hα
    rfun
    (fun e he1 {z} hzi hzi1 =>
      (hδfunprop e he1 (M5 / 2) ht_pos (ht_δfun e)).2.2.2.2.1 z hzi hzi1)
    (fun e he1 => ⟨(hδfunprop e he1 (M5 / 2) ht_pos (ht_δfun e)).2.2.2.2.2.1,
      (hδfunprop e he1 (M5 / 2) ht_pos (ht_δfun e)).2.2.2.2.2.2⟩)
    (by
      rw [← hLfsdef]
      have hmul : M5 * LfirstSeg ≤ α := (le_div_iff₀ hLfspos).mp h6
      nlinarith [hLfspos, hM5pos, hmul])
    (by
      rw [← hLlsdef]
      have hmul : M5 * LlastSeg ≤ α := (le_div_iff₀ hLlspos).mp h7
      nlinarith [hLlspos, hM5pos, hmul])
    (by linarith)
    hsep
    (fun c hc1 z hmid hzi hzi1 =>
      (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).1 z hmid hzi hzi1)
    (fun c hc1 z hmid hzi hzi1 =>
      (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.1 z hmid hzi hzi1)
    hturn
    (fun c hc1 => (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.2.1)
    (fun c hc1 => (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.2.2.1)
    (fun p q hpq => (hballs0 p q hpq).mono
      (Metric.ball_subset_ball (by linarith)) (Metric.ball_subset_ball (by linarith)))
    (fun i hi => by have := hsrcsep i hi; linarith)
    (fun i hi => by have := htgtsep i hi; linarith)

/-! ### P5 (preconnected) — each collar piece is preconnected

The collar is a linear chain of pieces (end caps, band strips, vertex sectors).  Each
piece is preconnected: the band strips and end caps are **convex** (intersections of
half-planes — `footParam` and `sideForm` are both affine in `z` — with a ball and/or
the open `δ₀`-neighbourhood of a segment, which is convex by `Convex.thickening`); the
vertex sectors are `convexSector ∩ ball` (convex) or `reflexSector ∩ ball` (a union of
two convex half-plane∩ball pieces meeting at a scaled reflected point), hence
preconnected either way. -/

/-- `footParam s t` is affine in its evaluation point. -/
theorem footParam_affineComb_pt (s t x y : Plane) {a b : ℝ} (hab : a + b = 1) :
    footParam s t (a • x + b • y) = a * footParam s t x + b * footParam s t y := by
  have hb : b = 1 - a := by linarith
  subst hb
  have hnum : dotp ((a • x + (1 - a) • y) - s) (t - s)
      = a * dotp (x - s) (t - s) + (1 - a) * dotp (y - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  simp only [footParam]; rw [hnum, add_div, mul_div_assoc, mul_div_assoc]

/-- A *strict upper* foot half-plane `{z | c < footParam s t z}` is convex. -/
theorem convex_footParam_gt (s t : Plane) (c : ℝ) :
    Convex ℝ {z : Plane | c < footParam s t z} := by
  rintro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [footParam_affineComb_pt s t x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; simpa using hy
  · rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab; simpa using hx
    · nlinarith [mul_pos ha' (sub_pos.mpr hx), mul_pos hb' (sub_pos.mpr hy),
        (by rw [← add_mul, hab, one_mul] : a * c + b * c = c)]

/-- A *strict lower* foot half-plane `{z | footParam s t z < c}` is convex. -/
theorem convex_footParam_lt (s t : Plane) (c : ℝ) :
    Convex ℝ {z : Plane | footParam s t z < c} := by
  rintro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [footParam_affineComb_pt s t x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; simpa using hy
  · rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab; simpa using hx
    · nlinarith [mul_pos ha' (sub_pos.mpr hx), mul_pos hb' (sub_pos.mpr hy),
        (by rw [← add_mul, hab, one_mul] : a * c + b * c = c)]

/-- The narrowed edge band is convex (intersection of two foot half-planes). -/
theorem convex_edgeBandMid (s t : Plane) (α : ℝ) : Convex ℝ (edgeBandMid s t α) := by
  have e : edgeBandMid s t α
      = {z : Plane | α < footParam s t z} ∩ {z : Plane | footParam s t z < 1 - α} := by
    ext z; simp only [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_inter_iff]
  rw [e]; exact (convex_footParam_gt s t α).inter (convex_footParam_lt s t (1 - α))

/-- The positive narrowed band is convex. -/
theorem convex_edgePlusMid (s t : Plane) (α : ℝ) : Convex ℝ (edgePlusMid s t α) := by
  rw [edgePlusMid]
  refine (convex_edgeBandMid s t α).inter ?_
  have e : {z : Plane | 0 < sideForm s t z} = {z : Plane | (0:ℝ) < 1 * sideForm s t z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt s t 1 0

/-- The negative narrowed band is convex. -/
theorem convex_edgeMinusMid (s t : Plane) (α : ℝ) : Convex ℝ (edgeMinusMid s t α) := by
  rw [edgeMinusMid]
  refine (convex_edgeBandMid s t α).inter ?_
  have e : {z : Plane | sideForm s t z < 0} = {z : Plane | 1 * sideForm s t z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt s t 1 0

/-- The positive band strip is convex (positive band ∩ the open `δ₀`-neighbourhood of the
segment, which is the thickening of a convex set). -/
theorem convex_bandStripPlus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    Convex ℝ (bandStripPlus β α δ₀ i) := by
  rw [bandStripPlus]
  refine (convex_edgePlusMid _ _ _).inter ?_
  have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have e : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
         = Metric.thickening δ₀ (β.segCarrier i) := by
    ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
  rw [e]
  exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀

/-- The negative band strip is convex. -/
theorem convex_bandStripMinus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    Convex ℝ (bandStripMinus β α δ₀ i) := by
  rw [bandStripMinus]
  refine (convex_edgeMinusMid _ _ _).inter ?_
  have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have e : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
         = Metric.thickening δ₀ (β.segCarrier i) := by
    ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
  rw [e]
  exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀

/-- A convex sector intersected with any ball is preconnected (it is convex). -/
theorem isPreconnected_convexSector_inter_ball (a v b : Plane) (ρ : ℝ) :
    IsPreconnected (convexSector a v b ∩ Metric.ball v ρ) :=
  ((convex_convexSector a v b).inter (convex_ball v ρ)).isPreconnected

/-- A reflex sector intersected with a ball **centred at the apex** is preconnected: it is
the union of two convex half-plane∩ball pieces, which meet at a point obtained by scaling
the reflected point `3v − a − b` toward `v` (any positive scaling lands in both
half-planes; small scaling lands in the ball). -/
theorem isPreconnected_reflexSector_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (reflexSector a v b ∩ Metric.ball v ρ) := by
  rcases lt_or_ge 0 ρ with hρ | hρ
  swap
  · rw [Metric.ball_eq_empty.mpr hρ, Set.inter_empty]; exact isPreconnected_empty
  · have hset : reflexSector a v b ∩ Metric.ball v ρ
        = ({z | cornerTurn a v b * sideForm a v z < 0} ∩ Metric.ball v ρ)
          ∪ ({z | cornerTurn a v b * sideForm v b z < 0} ∩ Metric.ball v ρ) := by
      rw [reflexSector, Set.setOf_or, Set.union_inter_distrib_right]
    rw [hset]
    have hτ : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hcorner
    have hτ' : sideForm v b a ≠ 0 := by rw [← sideForm_cyclic a v b]; exact hτ
    set P : Plane := (3 : ℝ) • v - a - b with hPdef
    set ε : ℝ := (ρ / 2) / (dist P v + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    set pt : Plane := (1 - ε) • v + ε • P with hptdef
    have hptv : pt - v = ε • (P - v) := by rw [hptdef]; module
    have hdist : dist pt v < ρ := by
      have he : dist pt v = ε * dist P v := by
        rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
      rw [he, hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [dist_nonneg (x := P) (y := v), hρ]
    have hmemball : pt ∈ Metric.ball v ρ := Metric.mem_ball.mpr hdist
    have hsfa : sideForm a v pt = - (ε * sideForm a v b) := by
      rw [hptdef, sideForm_affineComb a v v P (by ring : (1 - ε) + ε = 1),
        sideForm_right_endpoint]
      have e : sideForm a v P = - sideForm a v b := by
        rw [hPdef]; simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; ring
    have hsfb : sideForm v b pt = - (ε * sideForm v b a) := by
      rw [hptdef, sideForm_affineComb v b v P (by ring : (1 - ε) + ε = 1),
        sideForm_left_endpoint]
      have e : sideForm v b P = - sideForm v b a := by
        rw [hPdef]; simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; ring
    have hA : cornerTurn a v b * sideForm a v pt < 0 := by
      rw [cornerTurn, hsfa]; nlinarith [mul_pos hεpos (mul_self_pos.mpr hτ)]
    have hB : cornerTurn a v b * sideForm v b pt < 0 := by
      rw [cornerTurn, hsfb, sideForm_cyclic a v b]
      nlinarith [mul_pos hεpos (mul_self_pos.mpr hτ')]
    exact IsPreconnected.union pt ⟨hA, hmemball⟩ ⟨hB, hmemball⟩
      ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter (convex_ball v ρ)).isPreconnected
      ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter (convex_ball v ρ)).isPreconnected

/-- The τ-selected positive sector intersected with a ball centred at the apex is
preconnected. -/
theorem isPreconnected_vertexPlus_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (vertexPlus a v b ∩ Metric.ball v ρ) := by
  rw [vertexPlus]; split_ifs
  · exact isPreconnected_convexSector_inter_ball a v b ρ
  · exact isPreconnected_reflexSector_inter_ball a v b hcorner ρ

/-- The τ-selected negative sector intersected with a ball centred at the apex is
preconnected. -/
theorem isPreconnected_vertexMinus_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (vertexMinus a v b ∩ Metric.ball v ρ) := by
  rw [vertexMinus]; split_ifs
  · exact isPreconnected_reflexSector_inter_ball a v b hcorner ρ
  · exact isPreconnected_convexSector_inter_ball a v b ρ

/-- The positive vertex sector is preconnected.

**UNION-tube note (region-face-bridge-plan §9, step 5).**  `sectorPlus β δ₀ i hi1 =
vertexPlus a v b ∩ (stripSupport i ∪ stripSupport (i+1))`.  `vertexPlus` is a convex cone at
`v = segTgt i`; each `stripSupport` is an open δ₀-neighbourhood of a segment through `v`.
The two strips both contain a punctured neighbourhood of `v` inside the cone, so the union
meets the cone in a connected set (star-shaped toward `v` along the cone; for `δ₀ ≤ 0` the
sector is empty, trivially preconnected, so no positivity hypothesis is needed).  GOAL:
`IsPreconnected (sectorPlus β δ₀ i hi1)`.  Likely route: for `δ₀ > 0` show the set is
star-connected to a basepoint near `v` in the cone; the old
`isPreconnected_vertexPlus_inter_ball` handled a single ball — here it is a union of two
strips, so reconstruct connectivity through the shared apex wedge. -/
theorem isPreconnected_sectorPlus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorPlus β δ₀ i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]
      exact hτ
    have hstripConv_i : Convex ℝ (stripSupport β δ₀ i) := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : stripSupport β δ₀ i = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_i1 : Convex ℝ (stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq :
          stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩
            = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact
        (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
          (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · set P : Plane := (3 : ℝ) • v - a - b with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i⟩ ⟨hptB, hptstrip_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i1⟩ ⟨hptB, hptstrip_i1⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector]
        exact Or.inl hptA
      rw [sectorPlus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
    · set P : Plane := a + b - v with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_pos hpos, convexSector]
        exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter hstripConv_i1).isPreconnected
      rw [sectorPlus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
  · rw [sectorPlus]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz
        simp at hz
    have hstrip_i1 :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) :=
          Metric.infDist_nonneg
        nlinarith
      · intro hz
        simp at hz
    rw [hstrip_i, hstrip_i1, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The negative vertex sector is preconnected.  See `isPreconnected_sectorPlus`. -/
theorem isPreconnected_sectorMinus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorMinus β δ₀ i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]
      exact hτ
    have hstripConv_i : Convex ℝ (stripSupport β δ₀ i) := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : stripSupport β δ₀ i = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_i1 : Convex ℝ (stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq :
          stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩
            = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact
        (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
          (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · set P : Plane := a + b - v with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le), convexSector]
        exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter hstripConv_i1).isPreconnected
      rw [sectorMinus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
    · set P : Plane := (3 : ℝ) • v - a - b with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_pos hpos, reflexSector]
        exact Or.inl hptA
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i⟩ ⟨hptB, hptstrip_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i1⟩ ⟨hptB, hptstrip_i1⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
      rw [sectorMinus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
  · rw [sectorMinus]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz
        simp at hz
    have hstrip_i1 :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) :=
          Metric.infDist_nonneg
        nlinarith
      · intro hz
        simp at hz
    rw [hstrip_i, hstrip_i1, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The clipped positive vertex sector is preconnected.  Mirrors `isPreconnected_sectorPlus`,
but each strip arm is intersected with a convex `footParam` half-plane that trims the FAR end of
the arm.  The apex hub `pt`, built near the shared vertex `v`, still lands in both clipped arms:
on edge `i` (vertex foot `1`) `footParam pt = 1 − ε·(1 − footParam P) > α`, and on edge `i+1`
(vertex foot `0`) `footParam pt = ε·footParam P < 1 − α`, for the (suitably small) apex weight
`ε`. -/
theorem isPreconnected_sectorPlusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α) (hα1 : α < 1)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorPlusClipped β δ₀ α i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    -- the outgoing edge's endpoints (its source IS the shared vertex `v`)
    set sj : Plane := β.segSrc ⟨(i : ℕ) + 1, hi1⟩ with hsj
    have hvj : sj = v := by
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      rw [hsj, PolygonalArc.segSrc, hidx, hv, PolygonalArc.segTgt]
    have hne_i : v ≠ a := β.segTgt_ne_segSrc i
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]; exact hτ
    -- convexity of the two foot half-planes (the new clip constraints)
    have hfootConv_i : Convex ℝ {z : Plane | α < footParam a v z} := convex_footParam_gt a v α
    have hfootConv_j : Convex ℝ {z : Plane | footParam sj b z < 1 - α} :=
      convex_footParam_lt sj b (1 - α)
    have hstripConv_i : Convex ℝ {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
          = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
      rw [hEq]; exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_j :
        Convex ℝ {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq : {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
          = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
      rw [hEq]
      exact (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
        (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    -- choose the apex direction `P` per branch; the apex weight `ε` is shared machinery
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · -- reflex `vertexPlus` branch: `P` reflects to keep `pt` on the reflex side
      set P : Plane := (3 : ℝ) • v - a - b with hP
      obtain ⟨ε, hεpos, hεstrip, hεfi, hεfj⟩ :
          ∃ ε : ℝ, 0 < ε ∧ ε * dist P v < δ₀ ∧
            ε * (1 - footParam a v P) < 1 - α ∧ ε * footParam sj b P < 1 - α := by
        set M : ℝ := |footParam a v P| + |footParam sj b P| + 1 with hM
        have hMpos : 0 < M := by
          have := abs_nonneg (footParam a v P); have := abs_nonneg (footParam sj b P)
          rw [hM]; linarith
        have hdpv : (0 : ℝ) ≤ dist P v := dist_nonneg
        have h1mα : (0 : ℝ) < 1 - α := by linarith
        have hdenpos : (0 : ℝ) < dist P v + M + 1 := by linarith
        have hμpos0 : (0 : ℝ) < min δ₀ (1 - α) := lt_min hδpos h1mα
        have hεpos0 : (0 : ℝ) < min δ₀ (1 - α) / (dist P v + M + 1) := div_pos hμpos0 hdenpos
        refine ⟨min δ₀ (1 - α) / (dist P v + M + 1), hεpos0, ?_, ?_, ?_⟩
        · rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 - α)) hdpv,
            mul_pos hδpos hMpos]
        · have h1 : (1 : ℝ) - footParam a v P ≤ M := by
            rw [hM]; have := neg_le_abs (footParam a v P); have := abs_nonneg (footParam sj b P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h1 hμpos0.le]
        · have h2 : footParam sj b P ≤ M := by
            rw [hM]; have := le_abs_self (footParam sj b P); have := abs_nonneg (footParam a v P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h2 hμpos0.le]
      have hptv : (1 - ε) • v + ε • P - v = ε • (P - v) := by module
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hpt, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq]; exact hεstrip
      have hptstrip_i : Metric.infDist pt (β.segCarrier i) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hv]; exact right_mem_segment ℝ _ _
      have hptstrip_j : Metric.infDist pt (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hb, ← hsj, hvj]; exact left_mem_segment ℝ _ _
      -- the apex satisfies the two foot clips
      have hfoot_i : α < footParam a v pt := by
        rw [hpt, footParam_affineComb_pt a v v P (by ring : (1 - ε) + ε = 1), footParam_tgt hne_i]
        nlinarith [hεfi]
      have hfoot_j : footParam sj b pt < 1 - α := by
        rw [hpt, footParam_affineComb_pt sj b v P (by ring : (1 - ε) + ε = 1), hvj,
          footParam_src, ← hvj]
        nlinarith [hεfj]
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa, cornerTurn]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb, cornerTurn,
          sideForm_cyclic a v b]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector]; exact Or.inl hptA
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} ∩ {z : Plane | α < footParam a v z})) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        refine IsPreconnected.union pt ⟨hptA, hptstrip_i, hfoot_i⟩ ⟨hptB, hptstrip_i, hfoot_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter
            (hstripConv_i.inter hfootConv_i)).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter
            (hstripConv_i.inter hfootConv_i)).isPreconnected
      have hpiece_j : IsPreconnected (vertexPlus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z : Plane | footParam sj b z < 1 - α})) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        refine IsPreconnected.union pt ⟨hptA, hptstrip_j, hfoot_j⟩ ⟨hptB, hptstrip_j, hfoot_j⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter
            (hstripConv_j.inter hfootConv_j)).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter
            (hstripConv_j.inter hfootConv_j)).isPreconnected
      rw [sectorPlusClipped, ← ha, ← hv, ← hb, ← hsj, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt ⟨hpt_vertex, hptstrip_i, hfoot_i⟩
        ⟨hpt_vertex, hptstrip_j, hfoot_j⟩ hpiece_i hpiece_j
    · -- convex `vertexPlus` branch
      set P : Plane := a + b - v with hP
      obtain ⟨ε, hεpos, hεstrip, hεfi, hεfj⟩ :
          ∃ ε : ℝ, 0 < ε ∧ ε * dist P v < δ₀ ∧
            ε * (1 - footParam a v P) < 1 - α ∧ ε * footParam sj b P < 1 - α := by
        set M : ℝ := |footParam a v P| + |footParam sj b P| + 1 with hM
        have hMpos : 0 < M := by
          have := abs_nonneg (footParam a v P); have := abs_nonneg (footParam sj b P)
          rw [hM]; linarith
        have hdpv : (0 : ℝ) ≤ dist P v := dist_nonneg
        have h1mα : (0 : ℝ) < 1 - α := by linarith
        have hdenpos : (0 : ℝ) < dist P v + M + 1 := by linarith
        have hμpos0 : (0 : ℝ) < min δ₀ (1 - α) := lt_min hδpos h1mα
        have hεpos0 : (0 : ℝ) < min δ₀ (1 - α) / (dist P v + M + 1) := div_pos hμpos0 hdenpos
        refine ⟨min δ₀ (1 - α) / (dist P v + M + 1), hεpos0, ?_, ?_, ?_⟩
        · rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 - α)) hdpv,
            mul_pos hδpos hMpos]
        · have h1 : (1 : ℝ) - footParam a v P ≤ M := by
            rw [hM]; have := neg_le_abs (footParam a v P); have := abs_nonneg (footParam sj b P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h1 hμpos0.le]
        · have h2 : footParam sj b P ≤ M := by
            rw [hM]; have := le_abs_self (footParam sj b P); have := abs_nonneg (footParam a v P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h2 hμpos0.le]
      have hptv : (1 - ε) • v + ε • P - v = ε • (P - v) := by module
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hpt, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq]; exact hεstrip
      have hptstrip_i : Metric.infDist pt (β.segCarrier i) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hv]; exact right_mem_segment ℝ _ _
      have hptstrip_j : Metric.infDist pt (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hb, ← hsj, hvj]; exact left_mem_segment ℝ _ _
      have hfoot_i : α < footParam a v pt := by
        rw [hpt, footParam_affineComb_pt a v v P (by ring : (1 - ε) + ε = 1), footParam_tgt hne_i]
        nlinarith [hεfi]
      have hfoot_j : footParam sj b pt < 1 - α := by
        rw [hpt, footParam_affineComb_pt sj b v P (by ring : (1 - ε) + ε = 1), hvj,
          footParam_src, ← hvj]
        nlinarith [hεfj]
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa, cornerTurn]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb, cornerTurn,
          sideForm_cyclic a v b]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_pos hpos, convexSector]; exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} ∩ {z : Plane | α < footParam a v z})) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter (hstripConv_i.inter hfootConv_i)).isPreconnected
      have hpiece_j : IsPreconnected (vertexPlus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z : Plane | footParam sj b z < 1 - α})) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter (hstripConv_j.inter hfootConv_j)).isPreconnected
      rw [sectorPlusClipped, ← ha, ← hv, ← hb, ← hsj, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt ⟨hpt_vertex, hptstrip_i, hfoot_i⟩
        ⟨hpt_vertex, hptstrip_j, hfoot_j⟩ hpiece_i hpiece_j
  · rw [sectorPlusClipped]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z; constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz; simp at hz
    have hstrip_j :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z; constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := Metric.infDist_nonneg
        nlinarith
      · intro hz; simp at hz
    rw [hstrip_i, hstrip_j, Set.empty_inter, Set.empty_inter, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The clipped negative vertex sector is preconnected.  See `isPreconnected_sectorPlusClipped`. -/
theorem isPreconnected_sectorMinusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α) (hα1 : α < 1)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorMinusClipped β δ₀ α i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    set sj : Plane := β.segSrc ⟨(i : ℕ) + 1, hi1⟩ with hsj
    have hvj : sj = v := by
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      rw [hsj, PolygonalArc.segSrc, hidx, hv, PolygonalArc.segTgt]
    have hne_i : v ≠ a := β.segTgt_ne_segSrc i
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]; exact hτ
    have hfootConv_i : Convex ℝ {z : Plane | α < footParam a v z} := convex_footParam_gt a v α
    have hfootConv_j : Convex ℝ {z : Plane | footParam sj b z < 1 - α} :=
      convex_footParam_lt sj b (1 - α)
    have hstripConv_i : Convex ℝ {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
          = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
      rw [hEq]; exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_j :
        Convex ℝ {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq : {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
          = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
      rw [hEq]
      exact (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
        (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · -- convex `vertexMinus` branch (`if_neg`)
      set P : Plane := a + b - v with hP
      obtain ⟨ε, hεpos, hεstrip, hεfi, hεfj⟩ :
          ∃ ε : ℝ, 0 < ε ∧ ε * dist P v < δ₀ ∧
            ε * (1 - footParam a v P) < 1 - α ∧ ε * footParam sj b P < 1 - α := by
        set M : ℝ := |footParam a v P| + |footParam sj b P| + 1 with hM
        have hMpos : 0 < M := by
          have := abs_nonneg (footParam a v P); have := abs_nonneg (footParam sj b P)
          rw [hM]; linarith
        have hdpv : (0 : ℝ) ≤ dist P v := dist_nonneg
        have h1mα : (0 : ℝ) < 1 - α := by linarith
        have hdenpos : (0 : ℝ) < dist P v + M + 1 := by linarith
        have hμpos0 : (0 : ℝ) < min δ₀ (1 - α) := lt_min hδpos h1mα
        have hεpos0 : (0 : ℝ) < min δ₀ (1 - α) / (dist P v + M + 1) := div_pos hμpos0 hdenpos
        refine ⟨min δ₀ (1 - α) / (dist P v + M + 1), hεpos0, ?_, ?_, ?_⟩
        · rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 - α)) hdpv,
            mul_pos hδpos hMpos]
        · have h1 : (1 : ℝ) - footParam a v P ≤ M := by
            rw [hM]; have := neg_le_abs (footParam a v P); have := abs_nonneg (footParam sj b P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h1 hμpos0.le]
        · have h2 : footParam sj b P ≤ M := by
            rw [hM]; have := le_abs_self (footParam sj b P); have := abs_nonneg (footParam a v P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h2 hμpos0.le]
      have hptv : (1 - ε) • v + ε • P - v = ε • (P - v) := by module
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hpt, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq]; exact hεstrip
      have hptstrip_i : Metric.infDist pt (β.segCarrier i) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hv]; exact right_mem_segment ℝ _ _
      have hptstrip_j : Metric.infDist pt (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hb, ← hsj, hvj]; exact left_mem_segment ℝ _ _
      have hfoot_i : α < footParam a v pt := by
        rw [hpt, footParam_affineComb_pt a v v P (by ring : (1 - ε) + ε = 1), footParam_tgt hne_i]
        nlinarith [hεfi]
      have hfoot_j : footParam sj b pt < 1 - α := by
        rw [hpt, footParam_affineComb_pt sj b v P (by ring : (1 - ε) + ε = 1), hvj,
          footParam_src, ← hvj]
        nlinarith [hεfj]
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa, cornerTurn]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb, cornerTurn,
          sideForm_cyclic a v b]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le), convexSector]; exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} ∩ {z : Plane | α < footParam a v z})) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter (hstripConv_i.inter hfootConv_i)).isPreconnected
      have hpiece_j : IsPreconnected (vertexMinus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z : Plane | footParam sj b z < 1 - α})) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter (hstripConv_j.inter hfootConv_j)).isPreconnected
      rw [sectorMinusClipped, ← ha, ← hv, ← hb, ← hsj, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt ⟨hpt_vertex, hptstrip_i, hfoot_i⟩
        ⟨hpt_vertex, hptstrip_j, hfoot_j⟩ hpiece_i hpiece_j
    · -- reflex `vertexMinus` branch (`if_pos`)
      set P : Plane := (3 : ℝ) • v - a - b with hP
      obtain ⟨ε, hεpos, hεstrip, hεfi, hεfj⟩ :
          ∃ ε : ℝ, 0 < ε ∧ ε * dist P v < δ₀ ∧
            ε * (1 - footParam a v P) < 1 - α ∧ ε * footParam sj b P < 1 - α := by
        set M : ℝ := |footParam a v P| + |footParam sj b P| + 1 with hM
        have hMpos : 0 < M := by
          have := abs_nonneg (footParam a v P); have := abs_nonneg (footParam sj b P)
          rw [hM]; linarith
        have hdpv : (0 : ℝ) ≤ dist P v := dist_nonneg
        have h1mα : (0 : ℝ) < 1 - α := by linarith
        have hdenpos : (0 : ℝ) < dist P v + M + 1 := by linarith
        have hμpos0 : (0 : ℝ) < min δ₀ (1 - α) := lt_min hδpos h1mα
        have hεpos0 : (0 : ℝ) < min δ₀ (1 - α) / (dist P v + M + 1) := div_pos hμpos0 hdenpos
        refine ⟨min δ₀ (1 - α) / (dist P v + M + 1), hεpos0, ?_, ?_, ?_⟩
        · rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 - α)) hdpv,
            mul_pos hδpos hMpos]
        · have h1 : (1 : ℝ) - footParam a v P ≤ M := by
            rw [hM]; have := neg_le_abs (footParam a v P); have := abs_nonneg (footParam sj b P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h1 hμpos0.le]
        · have h2 : footParam sj b P ≤ M := by
            rw [hM]; have := le_abs_self (footParam sj b P); have := abs_nonneg (footParam a v P)
            linarith
          rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
          nlinarith [mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 - α)) hMpos.le,
            mul_pos h1mα (show (0 : ℝ) < dist P v + 1 by linarith),
            mul_le_mul_of_nonneg_left h2 hμpos0.le]
      have hptv : (1 - ε) • v + ε • P - v = ε • (P - v) := by module
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hpt, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq]; exact hεstrip
      have hptstrip_i : Metric.infDist pt (β.segCarrier i) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hv]; exact right_mem_segment ℝ _ _
      have hptstrip_j : Metric.infDist pt (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolygonalArc.segCarrier, ← hb, ← hsj, hvj]; exact left_mem_segment ℝ _ _
      have hfoot_i : α < footParam a v pt := by
        rw [hpt, footParam_affineComb_pt a v v P (by ring : (1 - ε) + ε = 1), footParam_tgt hne_i]
        nlinarith [hεfi]
      have hfoot_j : footParam sj b pt < 1 - α := by
        rw [hpt, footParam_affineComb_pt sj b v P (by ring : (1 - ε) + ε = 1), hvj,
          footParam_src, ← hvj]
        nlinarith [hεfj]
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa, cornerTurn]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb, cornerTurn,
          sideForm_cyclic a v b]
        ring_nf; nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_pos hpos, reflexSector]; exact Or.inl hptA
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} ∩ {z : Plane | α < footParam a v z})) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or, Set.union_inter_distrib_right]
        refine IsPreconnected.union pt ⟨hptA, hptstrip_i, hfoot_i⟩ ⟨hptB, hptstrip_i, hfoot_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter
            (hstripConv_i.inter hfootConv_i)).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter
            (hstripConv_i.inter hfootConv_i)).isPreconnected
      have hpiece_j : IsPreconnected (vertexMinus a v b ∩
          ({z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z : Plane | footParam sj b z < 1 - α})) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or, Set.union_inter_distrib_right]
        refine IsPreconnected.union pt ⟨hptA, hptstrip_j, hfoot_j⟩ ⟨hptB, hptstrip_j, hfoot_j⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter
            (hstripConv_j.inter hfootConv_j)).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter
            (hstripConv_j.inter hfootConv_j)).isPreconnected
      rw [sectorMinusClipped, ← ha, ← hv, ← hb, ← hsj, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt ⟨hpt_vertex, hptstrip_i, hfoot_i⟩
        ⟨hpt_vertex, hptstrip_j, hfoot_j⟩ hpiece_i hpiece_j
  · rw [sectorMinusClipped]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z; constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz; simp at hz
    have hstrip_j :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z; constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := Metric.infDist_nonneg
        nlinarith
      · intro hz; simp at hz
    rw [hstrip_i, hstrip_j, Set.empty_inter, Set.empty_inter, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The positive source end cap is convex. -/
theorem convex_endCapSrcPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapSrcPlus β ρ) := by
  rw [endCapSrcPlus]
  refine ((convex_ball _ _).inter (convex_footParam_gt _ _ 0)).inter ?_
  have e : {z : Plane | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
         = {z : Plane | (0:ℝ) < 1 * sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt _ _ 1 0

/-- The negative source end cap is convex. -/
theorem convex_endCapSrcMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapSrcMinus β ρ) := by
  rw [endCapSrcMinus]
  refine ((convex_ball _ _).inter (convex_footParam_gt _ _ 0)).inter ?_
  have e : {z : Plane | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0}
         = {z : Plane | 1 * sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt _ _ 1 0

/-- The positive target end cap is convex. -/
theorem convex_endCapTgtPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapTgtPlus β ρ) := by
  rw [endCapTgtPlus]
  refine ((convex_ball _ _).inter (convex_footParam_lt _ _ 1)).inter ?_
  have e : {z : Plane | 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z}
         = {z : Plane | (0:ℝ) < 1 * sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt _ _ 1 0

/-- The negative target end cap is convex. -/
theorem convex_endCapTgtMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapTgtMinus β ρ) := by
  rw [endCapTgtMinus]
  refine ((convex_ball _ _).inter (convex_footParam_lt _ _ 1)).inter ?_
  have e : {z : Plane | sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0}
         = {z : Plane | 1 * sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt _ _ 1 0

/-! ### End caps are off-carrier

Each end cap is disjoint from the whole carrier.  Its `sideForm`-strict side excludes the
*incident* edge (whose points are collinear, `sideForm = 0`); a small-enough cap radius `ρ`
at the endpoint — bounded by the endpoint's distance to every *non-incident* edge — excludes
all other edges.  This turns the clipped end cap `(taperedTube ∖ carrier) ∩ endCap` into the
plain intersection `taperedTube ∩ endCap`, removing the carrier from the connectivity proof. -/

/-- The positive source end cap lies off the carrier, provided `ρ 0` is at most the distance
from `verts 0` to every non-incident edge. -/
theorem endCapSrcPlus_subset_compl_carrier (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolygonalArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hi0 : (i : ℕ) = 0
  · have hif : i = β.firstSeg := Fin.ext (by simp [PolygonalArc.firstSeg, hi0])
    have hz0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.firstSeg := hif ▸ hzi
      rw [PolygonalArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzball
    have hsp := hsep i hi0
    rw [dist_comm] at hb; linarith

/-- The negative source end cap lies off the carrier. -/
theorem endCapSrcMinus_subset_compl_carrier (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolygonalArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hi0 : (i : ℕ) = 0
  · have hif : i = β.firstSeg := Fin.ext (by simp [PolygonalArc.firstSeg, hi0])
    have hz0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.firstSeg := hif ▸ hzi
      rw [PolygonalArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzball
    have hsp := hsep i hi0
    rw [dist_comm] at hb; linarith

/-- The positive target end cap lies off the carrier, provided `ρ (last)` is at most the
distance from `verts last` to every non-incident edge. -/
theorem endCapTgtPlus_subset_compl_carrier (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolygonalArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hil : (i : ℕ) = β.numSegs - 1
  · have hif : i = β.lastSeg := Fin.ext (by simp [PolygonalArc.lastSeg, hil])
    have hz0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.lastSeg := hif ▸ hzi
      rw [PolygonalArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzball
    have hsp := hsep i hil
    rw [dist_comm] at hb; linarith

/-- The negative target end cap lies off the carrier. -/
theorem endCapTgtMinus_subset_compl_carrier (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolygonalArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hil : (i : ℕ) = β.numSegs - 1
  · have hif : i = β.lastSeg := Fin.ext (by simp [PolygonalArc.lastSeg, hil])
    have hz0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.lastSeg := hif ▸ hzi
      rw [PolygonalArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzball
    have hsp := hsep i hil
    rw [dist_comm] at hb; linarith


end CrossingLemma.PlaneArcSeparation
