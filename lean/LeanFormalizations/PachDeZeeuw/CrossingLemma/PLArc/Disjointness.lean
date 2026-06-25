/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PLArc shard 3/7 — **Disjointness**: the P3 pairwise-disjointness lemmas for the
collar cells (clean sign/same-locus cases, adjacent corner cases, band↔sector
glue, sector↔sector, end caps, the per-cell aggregators, and the master
assembly). Also defines `stripSupport` and `exists_pos_disk_radius`, used by the
later collar shards. Split out of `PLArc.lean`; see that coordinator module's
doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.CollarConstruction

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! #### P3 disjointness — the clean (sign / same-locus) cases.

The full `collarPlus ∩ collarMinus = ∅` is a case bash over which geometric locus each
side's witness comes from.  The cases needing no metric budget are collected first:
opposite-sign pieces on the *same* edge or *same* vertex contradict directly. -/

/-- A band-strip's positive and negative halves on the **same edge** are disjoint
(opposite `sideForm` signs). -/
theorem disjoint_bandStripPlus_bandStripMinus (β : PolyArc) (α δ₀ : ℝ)
    (i : Fin β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (bandStripMinus β α δ₀ i) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc i) (β.segTgt i) z := hzp.1.2
  have hm : sideForm (β.segSrc i) (β.segTgt i) z < 0 := hzm.1.2
  linarith

/-- A vertex sector's positive and negative halves at the **same vertex** are disjoint
(`disjoint_vertexPlus_vertexMinus`). -/
theorem disjoint_sectorPlus_sectorMinus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ i hi1) (sectorMinus β δ₀ i hi1) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  exact (Set.disjoint_left.mp
    (disjoint_vertexPlus_vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)))
    hzp.1 hzm.1

/-- The **strip support** of edge `i` at width `δ`: points within `δ` of the closed
segment.  Both `bandStrip±` sit inside the support at their own width `δ₀`. -/
def stripSupport (β : PolyArc) (δ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  {z | Metric.infDist z (β.segCarrier i) < δ}

theorem bandStripPlus_subset_stripSupport (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    bandStripPlus β α δ₀ i ⊆ stripSupport β δ₀ i :=
  fun _ hz => hz.2

theorem bandStripMinus_subset_stripSupport (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    bandStripMinus β α δ₀ i ⊆ stripSupport β δ₀ i :=
  fun _ hz => hz.2

/-- **Union form (2026-06-14).**  A `+` sector sits in the union of the strip supports of its
two incident edges `i` (incoming) and `i+1` (outgoing).  Under the δ₀-corner-tube-UNION
`sectorPlus`, a point is `δ₀`-close to *at least one* incident edge — it need not be close to
both — so the single-strip containments `⊆ stripSupport i` / `⊆ stripSupport (i+1)` of the
old intersection form are **false**; only this union containment holds.  Disjointness of a
sector from a *far* edge's strip now needs separation from *both* arms (4-way), and adjacent
disjointness uses the σ-sign lemmas, not strip separation. -/
theorem sectorPlus_subset_stripSupport_union (β : PolyArc) (δ₀ : ℝ) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorPlus β δ₀ i hi1 ⊆ stripSupport β δ₀ i ∪ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ :=
  fun _ hz => hz.2

/-- **Union form (2026-06-14).**  A `−` sector sits in the union of the strip supports of its
two incident edges.  See `sectorPlus_subset_stripSupport_union`. -/
theorem sectorMinus_subset_stripSupport_union (β : PolyArc) (δ₀ : ℝ) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorMinus β δ₀ i hi1 ⊆ stripSupport β δ₀ i ∪ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ :=
  fun _ hz => hz.2

theorem stripSupport_mono (β : PolyArc) {δ δ' : ℝ} (h : δ ≤ δ') (i : Fin β.numSegs) :
    stripSupport β δ i ⊆ stripSupport β δ' i :=
  fun _ hz => lt_of_lt_of_le hz h

/-- **Non-adjacent strip supports are disjoint**, once `δ` is below the non-adjacent
separation `exists_delta_nonadjacent_tube_sep`.  This kills every band↔band cross-overlap
between non-consecutive edges (regardless of sign). -/
theorem disjoint_stripSupport_nonadjacent (β : PolyArc) {δ : ℝ}
    (hsep : ∀ i j : Fin β.numSegs, (i : ℕ) + 1 < (j : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier i) < δ → Metric.infDist z (β.segCarrier j) < δ → False)
    (i j : Fin β.numSegs) (hij : (i : ℕ) + 1 < (j : ℕ)) :
    Disjoint (stripSupport β δ i) (stripSupport β δ j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact hsep i j hij z hzi hzj

/-! #### P3 disjointness — the adjacent corner cases.

These are where the angle-free estimate pays off.  Two adjacent edges `i, i+1` share the
vertex `v = verts (i+1) = segTgt i = segSrc (i+1)`.  The corner-confinement keystone
(`exists_delta_corner_confine`) says a point near *both* edge lines is within any chosen
`r` of `v`; the foot parameter is Lipschitz (`abs_footParam_sub_le`), so a point that close
to `v` has `footParam` on edge `i` close to `1` (the value at the shared vertex `= segTgt
i`) — contradicting membership in the narrowed mid-band `footParam < 1 − α`.  Hence no
point lies in edge `i`'s mid-band while also being within `δ₀` of edge `i+1`. -/

/-- **Adjacent band ↔ strip impossibility.**  A point in edge `i`'s narrowed mid-band that
is also within `δ₀` of both edge `i` and edge `i+1` is impossible, provided the corner
confinement at radius `r` holds at width `δ₀` and the Lipschitz budget `L_i · r ≤ α` is
met (`L_i = ‖edge_i‖₁ / ‖edge_i‖₂²` the foot-parameter Lipschitz constant). -/
theorem not_mem_adjacent_band_strip (β : PolyArc) {α δ₀ r : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hconf : ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ →
      dist z (β.verts (Fin.succ i)) < r)
    (hLr : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
            / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * r ≤ α)
    {z : Plane} (hmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α)
    (hzi : Metric.infDist z (β.segCarrier i) < δ₀)
    (hzi1 : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀) : False := by
  have hne : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hv : β.segTgt i = β.verts (Fin.succ i) := rfl
  have hfp_lt : footParam (β.segSrc i) (β.segTgt i) z < 1 - α := hmid.2
  have hconf' : dist z (β.verts (Fin.succ i)) < r := hconf z hzi hzi1
  have hft : footParam (β.segSrc i) (β.segTgt i) (β.segTgt i) = 1 := footParam_tgt hne
  have hlip := abs_footParam_sub_le hne (β.segTgt i) z
  rw [hft] at hlip
  set L := (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
            / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact div_pos (segDir_l1_pos β i) (dotp_self_pos hne)
  have hdist : dist (β.segTgt i) z = dist z (β.verts (Fin.succ i)) := by
    rw [hv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam (β.segSrc i) (β.segTgt i) z - 1| < α :=
    calc |footParam (β.segSrc i) (β.segTgt i) z - 1|
        ≤ L * dist z (β.verts (Fin.succ i)) := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf' hLpos
      _ ≤ α := hLr
  have := (abs_lt.mp hbound).1
  linarith

/-- **Adjacent band ↔ strip impossibility, outgoing arm.**  The mirror of
`not_mem_adjacent_band_strip` for a point in edge `(i+1)`'s narrowed mid-band that is also
within `δ₀` of both edges `i` and `i+1`.  Here the shared vertex is edge `(i+1)`'s *source*
(`footParam = 0`), so the Lipschitz budget uses edge `(i+1)`'s constant. -/
theorem not_mem_adjacent_band_strip_src (β : PolyArc) {α δ₀ r : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hconf : ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ →
      dist z (β.verts (Fin.succ i)) < r)
    (hLr : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
            + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
            / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
                   (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * r ≤ α)
    {z : Plane}
    (hmid : z ∈ edgeBandMid (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) α)
    (hzi : Metric.infDist z (β.segCarrier i) < δ₀)
    (hzi1 : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀) : False := by
  set k : Fin β.numSegs := ⟨(i : ℕ) + 1, hi1⟩ with hk
  have hne : β.segTgt k ≠ β.segSrc k := β.segTgt_ne_segSrc k
  have hidx : (Fin.castSucc k : Fin (β.numSegs + 1)) = Fin.succ i :=
    Fin.ext (by simp [Fin.val_succ, hk])
  have hsv : β.segSrc k = β.verts (Fin.succ i) := by rw [PolyArc.segSrc, hidx]
  have hfp_gt : α < footParam (β.segSrc k) (β.segTgt k) z := hmid.1
  have hconf' : dist z (β.verts (Fin.succ i)) < r := hconf z hzi hzi1
  have hfs : footParam (β.segSrc k) (β.segTgt k) (β.segSrc k) = 0 := footParam_src _ _
  have hlip := abs_footParam_sub_le hne (β.segSrc k) z
  rw [hfs, sub_zero] at hlip
  set L := (|(β.segTgt k).1 - (β.segSrc k).1| + |(β.segTgt k).2 - (β.segSrc k).2|)
            / dotp (β.segTgt k - β.segSrc k) (β.segTgt k - β.segSrc k) with hL
  have hLpos : 0 < L := div_pos (segDir_l1_pos β k) (dotp_self_pos hne)
  have hdist : dist (β.segSrc k) z = dist z (β.verts (Fin.succ i)) := by rw [hsv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam (β.segSrc k) (β.segTgt k) z| < α :=
    calc |footParam (β.segSrc k) (β.segTgt k) z|
        ≤ L * dist z (β.verts (Fin.succ i)) := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf' hLpos
      _ ≤ α := hLr
  have := (abs_lt.mp hbound).2
  linarith

/-! #### P3 disjointness — adjacent band ↔ sector (the corner glue).

Edge `i` is the **incoming** arm `a→v` of the corner `a = segSrc i, v = segTgt i,
b = segTgt (i+1)` at the shared vertex `v`.  On the band/disk overlap the angle-free
thinness `thin_of_infDist_incoming` feeds the corner glue `mem_vertex*_of_incoming`,
which pins the vertex-sector side to the band's `sideForm` sign — so a `+` band can only
meet the `+` sector, never the `−` one. -/

/-- On the incoming-arm band/disk overlap, a `sideForm > 0` point lands in the `+`
sector. -/
theorem bandStrip_incoming_mem_vertexPlus (β : PolyArc) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i)))
    {z : Plane} (hmid : footParam (β.segSrc i) (β.segTgt i) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier i) < δ₀)
    (hsf : 0 < sideForm (β.segSrc i) (β.segTgt i) z) :
    z ∈ vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
  have hva : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hP : 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt i) (β.segSrc i - β.segTgt i) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt i) (β.segSrc i) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt i) (β.segSrc i) = β.segCarrier i := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt i) (β.segSrc i)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc i) (v := β.segTgt i)
    (b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact mem_vertexPlus_of_incoming hτ hG hthin hsf

/-- On the incoming-arm band/disk overlap, a `sideForm < 0` point lands in the `−`
sector. -/
theorem bandStrip_incoming_mem_vertexMinus (β : PolyArc) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i)))
    {z : Plane} (hmid : footParam (β.segSrc i) (β.segTgt i) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier i) < δ₀)
    (hsf : sideForm (β.segSrc i) (β.segTgt i) z < 0) :
    z ∈ vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
  have hva : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hP : 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt i) (β.segSrc i - β.segTgt i) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt i) (β.segSrc i) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt i) (β.segSrc i) = β.segCarrier i := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt i) (β.segSrc i)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc i) (v := β.segTgt i)
    (b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact mem_vertexMinus_of_incoming hτ hG hthin hsf

/-- **Incident band⁺ ↔ sector⁻ disjointness (incoming arm).**  Edge `i` is the incoming
arm of the corner at `verts (i+1)`; its `+` band and the corner's `−` sector cannot meet. -/
theorem disjoint_bandStripPlus_sectorMinus_incoming (β : PolyArc)
    {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i))) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ i hi1) := by
  -- (`ρ` argument removed: the sector is now governed by the free `δ₀`)
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_incoming_mem_vertexPlus β i hi1 hα hτ hδ hzb.1.1.2 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hmem hzs.1

/-- **Incident band⁻ ↔ sector⁺ disjointness (incoming arm).** -/
theorem disjoint_bandStripMinus_sectorPlus_incoming (β : PolyArc)
    {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i))) :
    Disjoint (bandStripMinus β α δ₀ i) (sectorPlus β δ₀ i hi1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_incoming_mem_vertexMinus β i hi1 hα hτ hδ hzb.1.1.2 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hzs.1 hmem

/-! #### P3 disjointness — adjacent band ↔ sector (outgoing arm).

Edge `j+1` is the **outgoing** arm `v→b` of the corner `a = segSrc j, v = segTgt j,
b = segTgt (j+1)` at the shared vertex `v = segTgt j = segSrc (j+1)`.  The bridge
`segSrc (j+1) = segTgt j` (`hsv`, both `= verts (j+1)`) rewrites the band's edge
quantities into the corner's `v→b` arm, and `thin_of_infDist_outgoing` feeds
`mem_vertex*_of_outgoing`. -/

/-- On the outgoing-arm band/disk overlap, a `sideForm > 0` point lands in the `+`
sector. -/
theorem bandStrip_outgoing_mem_vertexPlus (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hmid : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hsf : 0 < sideForm (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z) :
    z ∈ vertexPlus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hmid hsf
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv (le_of_lt hmid) hstrip' hδ
  exact mem_vertexPlus_of_outgoing hτ hG hthin hsf

/-- On the outgoing-arm band/disk overlap, a `sideForm < 0` point lands in the `−`
sector. -/
theorem bandStrip_outgoing_mem_vertexMinus (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hmid : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hsf : sideForm (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 0) :
    z ∈ vertexMinus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hmid hsf
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv (le_of_lt hmid) hstrip' hδ
  exact mem_vertexMinus_of_outgoing hτ hG hthin hsf

/-- **Incident band⁺ ↔ sector⁻ disjointness (outgoing arm).**  Edge `j+1` is the outgoing
arm of the corner at `verts (j+1)`; its `+` band and the corner's `−` sector cannot meet. -/
theorem disjoint_bandStripPlus_sectorMinus_outgoing (β : PolyArc)
    {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j))) :
    Disjoint (bandStripPlus β α δ₀ ⟨(j : ℕ) + 1, hj1⟩) (sectorMinus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_outgoing_mem_vertexPlus β j hj1 hα hτ hδ hzb.1.1.1 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hmem hzs.1

/-- **Incident band⁻ ↔ sector⁺ disjointness (outgoing arm).** -/
theorem disjoint_bandStripMinus_sectorPlus_outgoing (β : PolyArc)
    {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j))) :
    Disjoint (bandStripMinus β α δ₀ ⟨(j : ℕ) + 1, hj1⟩) (sectorPlus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_outgoing_mem_vertexMinus β j hj1 hα hτ hδ hzb.1.1.1 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hzs.1 hmem

/-! #### P3 disjointness — sector ↔ sector and non-incident band ↔ sector.

These are pure separation cases (no corner glue).  Two sectors at *different* vertices
are separated once their balls are disjoint (a `ρ` budget).  A band on an edge `i` not
incident to the sector's vertex is separated by the non-adjacent edge separation: the
sector vertex `verts (j+1)` lies on *both* edges `j` and `j+1`, and a non-incident `i`
is non-adjacent to at least one of them. -/

/-- A point in the vertex ball at `verts (j+1)` is within that radius of **both** incident
edges `j` and `j+1` (the vertex is their shared endpoint). -/
theorem infDist_lt_of_mem_vertexBall (β : PolyArc) (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) {ρ' : ℝ} {z : Plane}
    (hz : z ∈ Metric.ball (β.verts (Fin.succ j)) ρ') :
    Metric.infDist z (β.segCarrier j) < ρ' ∧
      Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < ρ' := by
  have hd : dist z (β.verts (Fin.succ j)) < ρ' := Metric.mem_ball.mp hz
  have h1 : β.verts (Fin.succ j) = β.segTgt j := rfl
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have h2 : β.verts (Fin.succ j) = β.segSrc ⟨(j : ℕ) + 1, hj1⟩ := by rw [PolyArc.segSrc, hidx]
  refine ⟨?_, ?_⟩
  · calc Metric.infDist z (β.segCarrier j)
        ≤ dist z (β.segTgt j) := Metric.infDist_le_dist_of_mem (right_mem_segment ℝ _ _)
      _ = dist z (β.verts (Fin.succ j)) := by rw [h1]
      _ < ρ' := hd
  · calc Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)
        ≤ dist z (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) :=
          Metric.infDist_le_dist_of_mem (left_mem_segment ℝ _ _)
      _ = dist z (β.verts (Fin.succ j)) := by rw [h2]
      _ < ρ' := hd

/-- **Sector ↔ sector disjointness (different vertices).**  Reduces to disjointness of
the two vertex balls (a `ρ` budget). -/
theorem disjoint_sectorPlus_sectorMinus_diff (β : PolyArc) (δ₀ : ℝ)
    (j k : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) (hk1 : (k : ℕ) + 1 < β.numSegs)
    (hjj : Disjoint (stripSupport β δ₀ j) (stripSupport β δ₀ k))
    (hjk : Disjoint (stripSupport β δ₀ j) (stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩))
    (hj1k : Disjoint (stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) (stripSupport β δ₀ k))
    (hj1k1 : Disjoint (stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩)
                      (stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (sectorMinus β δ₀ k hk1) := by
  -- §9 UNION REWORK: under the union sector, `sectorPlus j ⊆ strip j ∪ strip (j+1)` and
  -- `sectorMinus k ⊆ strip k ∪ strip (k+1)`, so a single strip-disjointness is too weak;
  -- the 4-way strip-disjointness across {j,j+1}×{k,k+1} separates the two unions.
  have hUnion :
      Disjoint (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩)
        (stripSupport β δ₀ k ∪ stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩) :=
    Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_right.mpr ⟨hjj, hjk⟩,
       Set.disjoint_union_right.mpr ⟨hj1k, hj1k1⟩⟩
  exact hUnion.mono (sectorPlus_subset_stripSupport_union β δ₀ j hj1)
    (sectorMinus_subset_stripSupport_union β δ₀ k hk1)

/-- **Non-incident band ↔ sector disjointness.**  Edge `i` is not incident to the
sector's vertex `verts (j+1)` (`(i:ℕ) ∉ {j, j+1}`).  Reduces (via the strip support and
the vertex ball) to the non-adjacent edge separation at width `δ`, with `δ₀ ≤ δ` and
`ρ (j+1) ≤ δ`. -/
theorem disjoint_stripSupport_vertexBall_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ δ : ℝ} (i j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δ → Metric.infDist w (β.segCarrier b) < δ → False)
    (hδ₀ : δ₀ ≤ δ) (hρ : ρ (Fin.succ j) ≤ δ)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (stripSupport β δ₀ i) (Metric.ball (β.verts (Fin.succ j)) (ρ (Fin.succ j))) := by
  rw [Set.disjoint_left]
  intro z hzi hzb
  have hi : Metric.infDist z (β.segCarrier i) < δ := lt_of_lt_of_le hzi hδ₀
  obtain ⟨hjclose, hj1close⟩ := infDist_lt_of_mem_vertexBall β j hj1 hzb
  have hj : Metric.infDist z (β.segCarrier j) < δ := lt_of_lt_of_le hjclose hρ
  have hj1' : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ :=
    lt_of_lt_of_le hj1close hρ
  have hval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
  · exact hsep i j hlt z hi hj
  · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hval]; omega) z hi hj1'
  · exact hsep j i (by omega) z hj hi

/-- **Non-incident edge band ↔ `+` sector (δ₀-tube UNION model).**  Edge `i ∉ {j, j+1}`.
SIGNATURE REVISION (§9 union rework): restated for the `−` *band strip* on edge `i` (not the
raw strip support), and given the adjacent-corner band/strip impossibilities `hadj_tgt`/
`hadj_src`.  The sector meets BOTH arm strips `{j, j+1}`; for the arm non-adjacent to `i`,
`hsep` separates; for an arm adjacent to `i` (`i = j−1` shares corner `j−1`, or `i = j+2`
shares corner `j+1`), the band's interior foot kills the overlap via the corner glue. -/
theorem disjoint_stripSupport_sectorPlus_nonincident (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep → Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (bandStripMinus β α δ₀ i) (sectorPlus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hbandmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α := hzb.1.1
  have hzi : Metric.infDist z (β.segCarrier i) < δ₀ := hzb.2
  have hju : z ∈ stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩ :=
    sectorPlus_subset_stripSupport_union β δ₀ j hj1 hzs
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases hju with hzj | hzj1
  · -- z is δ₀-close to the incoming arm `j`
    rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
    · exact hsep i j hlt z (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj hδ₀sep)
    · -- i + 1 = j, so i and j are the arms of corner `i`; band on edge i = lower arm.
      have hc1 : (i : ℕ) + 1 < β.numSegs := by omega
      have hjeq : (⟨(i : ℕ) + 1, hc1⟩ : Fin β.numSegs) = j := Fin.ext (by simpa using heq)
      refine hadj_tgt i hc1 z hbandmid hzi ?_
      rw [hjeq]; exact hzj
    · -- j + 1 < i; nonadjacency direction j < i but here i adjacent to j is excluded by hij
      exact hsep j i (by omega) z (lt_of_lt_of_le hzj hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
  · -- z is δ₀-close to the outgoing arm `j+1`
    rcases lt_trichotomy ((i : ℕ) + 1) ((j : ℕ) + 1) with hlt | heq | hgt
    · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z
        (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj1 hδ₀sep)
    · -- i = j+1 excluded by hij1
      exact absurd (by omega : (i : ℕ) = (j : ℕ) + 1) hij1
    · rcases lt_trichotomy ((j : ℕ) + 1 + 1) (i : ℕ) with hlt2 | heq2 | hgt2
      · exact hsep ⟨(j : ℕ) + 1, hj1⟩ i (by rw [hjval]; omega) z
          (lt_of_lt_of_le hzj1 hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
      · -- i = (j+1)+1, so j+1 and i are arms of corner `j+1`; band on edge i = upper arm.
        have hieq : (⟨(j : ℕ) + 1 + 1, by omega⟩ : Fin β.numSegs) = i :=
          Fin.ext (by simpa using heq2)
        refine hadj_src ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z ?_ hzj1 ?_
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp; omega)
          rw [this]; exact hbandmid
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp; omega)
          rw [this]; exact hzi
      · -- j+1 < i < (j+1)+1 impossible
        omega

/-- **Non-incident edge band ↔ `−` sector (δ₀-tube UNION model).**  Sign-mirror of
`disjoint_stripSupport_sectorPlus_nonincident`; restated for the `+` band strip on edge `i`. -/
theorem disjoint_stripSupport_sectorMinus_nonincident (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep → Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hbandmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α := hzb.1.1
  have hzi : Metric.infDist z (β.segCarrier i) < δ₀ := hzb.2
  have hju : z ∈ stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩ :=
    sectorMinus_subset_stripSupport_union β δ₀ j hj1 hzs
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases hju with hzj | hzj1
  · rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
    · exact hsep i j hlt z (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj hδ₀sep)
    · have hc1 : (i : ℕ) + 1 < β.numSegs := by omega
      have hjeq : (⟨(i : ℕ) + 1, hc1⟩ : Fin β.numSegs) = j := Fin.ext (by simpa using heq)
      refine hadj_tgt i hc1 z hbandmid hzi ?_
      rw [hjeq]; exact hzj
    · exact hsep j i (by omega) z (lt_of_lt_of_le hzj hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
  · rcases lt_trichotomy ((i : ℕ) + 1) ((j : ℕ) + 1) with hlt | heq | hgt
    · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z
        (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj1 hδ₀sep)
    · exact absurd (by omega : (i : ℕ) = (j : ℕ) + 1) hij1
    · rcases lt_trichotomy ((j : ℕ) + 1 + 1) (i : ℕ) with hlt2 | heq2 | hgt2
      · exact hsep ⟨(j : ℕ) + 1, hj1⟩ i (by rw [hjval]; omega) z
          (lt_of_lt_of_le hzj1 hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
      · refine hadj_src ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z ?_ hzj1 ?_
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp; omega)
          rw [this]; exact hbandmid
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp; omega)
          rw [this]; exact hzi
      · omega

/-! #### P3 disjointness — end caps.

The endpoint pieces carry a single incident edge (`firstSeg`/`lastSeg`) and no corner, so
their `±` split is the lone `sideForm` sign.  Opposite-sign caps at the same endpoint, or a
cap against the opposite-sign band on its own edge, contradict directly; the two endpoint
caps are separated by their balls. -/

/-- Opposite-sign caps at the source endpoint are disjoint. -/
theorem disjoint_endCapSrcPlus_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Disjoint (endCapSrcPlus β ρ) (endCapSrcMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzp.2
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzm.2
  linarith

/-- Opposite-sign caps at the target endpoint are disjoint. -/
theorem disjoint_endCapTgtPlus_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Disjoint (endCapTgtPlus β ρ) (endCapTgtMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzp.2
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzm.2
  linarith

/-- The source `+` cap and the `−` band on its own edge (`firstSeg`) are disjoint
(opposite `sideForm` sign on the same edge). -/
theorem disjoint_endCapSrcPlus_bandStripMinus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ β.firstSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzc.2
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzb.1.2
  linarith

/-- The source `−` cap and the `+` band on its own edge are disjoint. -/
theorem disjoint_endCapSrcMinus_bandStripPlus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ β.firstSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzc.2
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzb.1.2
  linarith

/-- The target `+` cap and the `−` band on its own edge (`lastSeg`) are disjoint. -/
theorem disjoint_endCapTgtPlus_bandStripMinus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ β.lastSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzc.2
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzb.1.2
  linarith

/-- The target `−` cap and the `+` band on its own edge are disjoint. -/
theorem disjoint_endCapTgtMinus_bandStripPlus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ β.lastSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzc.2
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzb.1.2
  linarith

/-- The two endpoint caps are disjoint once their balls are (a `ρ` budget). -/
theorem disjoint_endCapSrc_endCapTgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hball : Disjoint (Metric.ball (β.verts 0) (ρ 0))
                      (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))) :
    Disjoint (endCapSrcPlus β ρ) (endCapTgtMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzs hzt
  exact (Set.disjoint_left.mp hball) hzs.1.1 hzt.1.1

/-- The other endpoint-cap cross pairing. -/
theorem disjoint_endCapSrcMinus_endCapTgtPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hball : Disjoint (Metric.ball (β.verts 0) (ρ 0))
                      (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))) :
    Disjoint (endCapSrcMinus β ρ) (endCapTgtPlus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzs hzt
  exact (Set.disjoint_left.mp hball) hzs.1.1 hzt.1.1

/-! #### P3 disjointness — end cap ↔ non-incident band, and end cap ↔ sector.

The remaining cross pairings.  An endpoint vertex `v` lies on its single incident edge only;
for any edge `i` not incident to `v` the vertex is at positive `infDist` from `segCarrier i`,
so a `ρ`-ball about `v` and a `δ₀`-strip about edge `i` are separated once the radii fit the
budget `ρ + δ₀ ≤ infDist v (segCarrier i)`.  End cap ↔ sector is pure ball disjointness
(`v ≠ verts (succ j)`). -/

/-- **Vertex ball ↔ strip support via an `infDist` budget.**  If the vertex `v` is at least
`ρ' + δ₀` from edge `i` (in `infDist`), the `ρ'`-ball about `v` misses edge `i`'s `δ₀`-strip
support.  `infDist` is `1`-Lipschitz, so a point within `ρ'` of `v` and within `δ₀` of the
edge would put `v` within `ρ' + δ₀` of the edge. -/
theorem disjoint_vertexBall_stripSupport_of_budget (β : PolyArc) {v : Plane} {ρ' δ₀ : ℝ}
    (i : Fin β.numSegs)
    (hbudget : ρ' + δ₀ ≤ Metric.infDist v (β.segCarrier i)) :
    Disjoint (Metric.ball v ρ') (stripSupport β δ₀ i) := by
  rw [Set.disjoint_left]
  intro z hzball hzs
  have hd : dist v z < ρ' := by rw [dist_comm]; exact Metric.mem_ball.mp hzball
  have hi : Metric.infDist z (β.segCarrier i) < δ₀ := hzs
  have htri : Metric.infDist v (β.segCarrier i)
      ≤ Metric.infDist z (β.segCarrier i) + dist v z :=
    Metric.infDist_le_infDist_add_dist
  linarith

/-- Source `+` cap ↔ `−` band on a non-incident edge (`i ≠ firstSeg`). -/
theorem disjoint_endCapSrcPlus_bandStripMinus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripMinus_subset_stripSupport β α δ₀ i)

/-- Source `−` cap ↔ `+` band on a non-incident edge (`i ≠ firstSeg`). -/
theorem disjoint_endCapSrcMinus_bandStripPlus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripPlus_subset_stripSupport β α δ₀ i)

/-- Target `+` cap ↔ `−` band on a non-incident edge (`i ≠ lastSeg`). -/
theorem disjoint_endCapTgtPlus_bandStripMinus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripMinus_subset_stripSupport β α δ₀ i)

/-- Target `−` cap ↔ `+` band on a non-incident edge (`i ≠ lastSeg`). -/
theorem disjoint_endCapTgtMinus_bandStripPlus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripPlus_subset_stripSupport β α δ₀ i)

/-- Source `+` cap ↔ a sector (different vertices: `verts 0 ≠ verts (succ j)`), a ball
budget. -/
theorem disjoint_endCapSrcPlus_sectorMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier j))
    (hbudget1 : ρ 0 + δ₀
      ≤ Metric.infDist (β.verts 0) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (endCapSrcPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: `sectorMinus j ⊆ stripSupport j ∪ stripSupport (j+1)`, so separate the
  -- cap-disk `ball(verts 0, ρ 0)` from BOTH arm strips via the two budgets.
  have hdisj :
      Disjoint (Metric.ball (β.verts 0) (ρ 0))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact hdisj.mono (fun _ hz => hz.1.1)
    (sectorMinus_subset_stripSupport_union β δ₀ j hj1)

/-- Target `+` cap ↔ a sector, an `infDist` budget. -/
theorem disjoint_endCapTgtPlus_sectorMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier j))
    (hbudget1 : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (endCapTgtPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: separate the tgt cap-disk from BOTH arm strips via the two budgets.
  have hdisj :
      Disjoint (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact hdisj.mono (fun _ hz => hz.1.1)
    (sectorMinus_subset_stripSupport_union β δ₀ j hj1)

/-- A sector ↔ source `−` cap, an `infDist` budget. -/
theorem disjoint_sectorPlus_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier j))
    (hbudget1 : ρ 0 + δ₀
      ≤ Metric.infDist (β.verts 0) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapSrcMinus β ρ) := by
  -- §9 UNION REWORK: separate the src cap-disk from BOTH arm strips, then flip sides.
  have hdisj :
      Disjoint (Metric.ball (β.verts 0) (ρ 0))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact (hdisj.mono (fun _ hz => hz.1.1)
    (sectorPlus_subset_stripSupport_union β δ₀ j hj1)).symm

/-- A sector ↔ target `−` cap, an `infDist` budget. -/
theorem disjoint_sectorPlus_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier j))
    (hbudget1 : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapTgtMinus β ρ) := by
  -- §9 UNION REWORK: separate the tgt cap-disk from BOTH arm strips, then flip sides.
  have hdisj :
      Disjoint (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact (hdisj.mono (fun _ hz => hz.1.1)
    (sectorPlus_subset_stripSupport_union β δ₀ j hj1)).symm

/-! #### P3 — the per-cell "all indices" lemmas.

Each of the following resolves one cell of the `collarPlus × collarMinus` disjointness grid
across *all* index pairs, doing its own index case analysis once.  The master assembly then
glues them via `Set.disjoint_union_*` / `Set.disjoint_iUnion_*`.

The band-adjacency content is bundled as `hadj_tgt`/`hadj_src` — exactly the conclusions of
`not_mem_adjacent_band_strip` / `not_mem_adjacent_band_strip_src` (the existence step feeds
those their corner confinement + Lipschitz budgets). -/

/-- **band⁺ ↔ band⁻, all index pairs.**  Same edge → sign clash; adjacent → the corner
impossibility (target arm if the `+` band is the lower edge, source arm if upper);
non-adjacent → the strip separation. -/
theorem disjoint_bandStripPlus_bandStripMinus_all (β : PolyArc) {α δ₀ δsep : ℝ}
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
    (i k : Fin β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (bandStripMinus β α δ₀ k) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · -- k = i+1 : plus band is the lower (target) arm
      have hk1 : (i : ℕ) + 1 < β.numSegs := by have := k.isLt; omega
      have hkeq : k = ⟨(i : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzm
      exact hadj_tgt i hk1 z hzp.1.1 hzp.2 hzm.2
    · exact hsep i k hfar z (lt_of_lt_of_le hzp.2 hδ₀sep) (lt_of_lt_of_le hzm.2 hδ₀sep)
  · have hik : i = k := Fin.ext heq
    rw [hik] at hzp
    have hp : 0 < sideForm (β.segSrc k) (β.segTgt k) z := hzp.1.2
    have hm : sideForm (β.segSrc k) (β.segTgt k) z < 0 := hzm.1.2
    linarith
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · -- i = k+1 : plus band is the upper (source) arm
      have hi1 : (k : ℕ) + 1 < β.numSegs := by have := i.isLt; omega
      have hieq : i = ⟨(k : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hieq] at hzp
      exact hadj_src k hi1 z hzp.1.1 hzm.2 hzp.2
    · exact hsep k i hfar z (lt_of_lt_of_le hzm.2 hδ₀sep) (lt_of_lt_of_le hzp.2 hδ₀sep)

/-- **band⁺ ↔ sector⁻, all index pairs.**  Incident (`i = j` incoming, `i = j+1` outgoing)
→ the corner glue; non-incident → strip/ball separation. -/
theorem disjoint_bandStripPlus_sectorMinus_all (β : PolyArc)
    {α δ₀ δsep : ℝ} (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
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
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ j hj1) := by
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have hijF : i = j := Fin.ext hij
    rw [hijF]
    exact disjoint_bandStripPlus_sectorMinus_incoming β j hj1 hα (hτ j hj1) (hδin j hj1)
  · by_cases hij1 : (i : ℕ) = (j : ℕ) + 1
    · have hieq : i = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hij1
      rw [hieq]
      exact disjoint_bandStripPlus_sectorMinus_outgoing β j hj1 hα (hτ j hj1) (hδout j hj1)
    · exact disjoint_stripSupport_sectorMinus_nonincident β hδ₀sep hsep hadj_tgt hadj_src
        i j hj1 hij hij1

/-- **sector⁺ ↔ band⁻, all index pairs.**  The sign-swapped mirror of the previous. -/
theorem disjoint_sectorPlus_bandStripMinus_all (β : PolyArc)
    {α δ₀ δsep : ℝ} (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
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
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ j hj1) (bandStripMinus β α δ₀ i) := by
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have hijF : i = j := Fin.ext hij
    rw [hijF]
    exact (disjoint_bandStripMinus_sectorPlus_incoming β j hj1 hα (hτ j hj1) (hδin j hj1)).symm
  · by_cases hij1 : (i : ℕ) = (j : ℕ) + 1
    · have hieq : i = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hij1
      rw [hieq]
      exact (disjoint_bandStripMinus_sectorPlus_outgoing β j hj1 hα (hτ j hj1)
        (hδout j hj1)).symm
    · exact (disjoint_stripSupport_sectorPlus_nonincident β hδ₀sep hsep hadj_tgt hadj_src
        i j hj1 hij hij1).symm

/-- **Source `+` cap ↔ band⁻, all band indices.**  Own edge → sign clash; else the
endpoint-edge budget. -/
theorem disjoint_endCapSrcPlus_bandStripMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = 0
  · have hieq : i = β.firstSeg := Fin.ext (hi.trans (rfl : (β.firstSeg : ℕ) = 0).symm)
    rw [hieq]; exact disjoint_endCapSrcPlus_bandStripMinus_self β ρ α δ₀
  · exact disjoint_endCapSrcPlus_bandStripMinus_nonincident β ρ i (hbudsrc i hi)

/-- **Source `−` cap ↔ band⁺, all band indices.** -/
theorem disjoint_endCapSrcMinus_bandStripPlus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = 0
  · have hieq : i = β.firstSeg := Fin.ext (hi.trans (rfl : (β.firstSeg : ℕ) = 0).symm)
    rw [hieq]; exact disjoint_endCapSrcMinus_bandStripPlus_self β ρ α δ₀
  · exact disjoint_endCapSrcMinus_bandStripPlus_nonincident β ρ i (hbudsrc i hi)

/-- **Target `+` cap ↔ band⁻, all band indices.** -/
theorem disjoint_endCapTgtPlus_bandStripMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = β.numSegs - 1
  · have hieq : i = β.lastSeg := Fin.ext (hi.trans (rfl : (β.lastSeg : ℕ) = β.numSegs - 1).symm)
    rw [hieq]; exact disjoint_endCapTgtPlus_bandStripMinus_self β ρ α δ₀
  · exact disjoint_endCapTgtPlus_bandStripMinus_nonincident β ρ i (hbudtgt i hi)

/-- **Target `−` cap ↔ band⁺, all band indices.** -/
theorem disjoint_endCapTgtMinus_bandStripPlus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = β.numSegs - 1
  · have hieq : i = β.lastSeg := Fin.ext (hi.trans (rfl : (β.lastSeg : ℕ) = β.numSegs - 1).symm)
    rw [hieq]; exact disjoint_endCapTgtMinus_bandStripPlus_self β ρ α δ₀
  · exact disjoint_endCapTgtMinus_bandStripPlus_nonincident β ρ i (hbudtgt i hi)

/-- `Fin.succ j ≠ Fin.last` when `j+1 < numSegs` (the sector vertex is interior). -/
private theorem succ_ne_last_of_lt (β : PolyArc) {j : Fin β.numSegs}
    (hj1 : (j : ℕ) + 1 < β.numSegs) : (Fin.succ j : Fin (β.numSegs + 1)) ≠ Fin.last β.numSegs := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_succ, Fin.val_last] at this
  omega

/-! #### P3 disjointness — clipped sector aggregators (collar-facing union model).

The clipped sectors `sectorPlusClipped`/`sectorMinusClipped` (grep their defs) trim each
strip arm by a `footParam` margin `α`, which is exactly what makes the SHARED-EDGE regime
(adjacent / gap-2 corners) tractable: the unclipped version is FALSE near the shared vertex,
but with the clip every shared-edge interaction acquires a two-sided foot bound `α < foot
< 1−α`, feeding the σ-sign reverse-glue (`vertexPlus_sideForm_outgoing_pos` /
`vertexMinus_sideForm_incoming_neg`).  The far/same-corner regimes transfer from the GREEN
unclipped lemmas via `Disjoint.mono` through the bridges
`sectorPlusClipped_subset_sectorPlus` / `sectorMinusClipped_subset_sectorMinus`. -/

/-- **Confinement → small foot at the source end.**  If the edge's source `s = w` and `z`
is within radius `r` of `w` (with the Lipschitz budget `Lₑ · r ≤ α`), then `z`'s foot on the
edge is `< α`.  This is `not_mem_adjacent_band_strip_src`'s estimate with the `edgeBandMid`
requirement dropped (only the source-end Lipschitz bound is used). -/
theorem footParam_lt_of_confined_src {s t w z : Plane} (hts : t ≠ s) {α r : ℝ}
    (hsv : s = w)
    (hLr : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * r ≤ α)
    (hconf : dist z w < r) : footParam s t z < α := by
  have hlip := abs_footParam_sub_le hts s z
  rw [footParam_src, sub_zero] at hlip
  set L := (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) with hL
  have hLpos : 0 < L := div_pos (by
    rcases lt_or_eq_of_le (add_nonneg (abs_nonneg (t.1 - s.1)) (abs_nonneg (t.2 - s.2)))
      with h | h
    · exact h
    · exfalso
      have h1 : t.1 - s.1 = 0 := abs_eq_zero.mp (by
        have := abs_nonneg (t.2 - s.2); linarith [abs_nonneg (t.1 - s.1)])
      have h2 : t.2 - s.2 = 0 := abs_eq_zero.mp (by
        have := abs_nonneg (t.1 - s.1); linarith [abs_nonneg (t.2 - s.2)])
      exact hts (Prod.ext (by linarith [sub_eq_zero.mp h1]) (by linarith [sub_eq_zero.mp h2])))
    (dotp_self_pos hts)
  have hdist : dist s z = dist z w := by rw [hsv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam s t z| < α :=
    calc |footParam s t z| ≤ L * dist z w := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf hLpos
      _ ≤ α := hLr
  exact (abs_lt.mp hbound).2

/-- **Confinement → large foot at the target end.**  If the edge's target `t = w` and `z`
is within radius `r` of `w` (with the Lipschitz budget `Lₑ · r ≤ α`), then `z`'s foot on the
edge is `> 1 − α`.  This is `not_mem_adjacent_band_strip`'s estimate with the `edgeBandMid`
requirement dropped (only the target-end Lipschitz bound is used). -/
theorem footParam_gt_of_confined_tgt {s t w z : Plane} (hts : t ≠ s) {α r : ℝ}
    (htv : t = w)
    (hLr : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * r ≤ α)
    (hconf : dist z w < r) : 1 - α < footParam s t z := by
  have hlip := abs_footParam_sub_le hts t z
  rw [footParam_tgt hts] at hlip
  set L := (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) with hL
  have hLpos : 0 < L := div_pos (by
    rcases lt_or_eq_of_le (add_nonneg (abs_nonneg (t.1 - s.1)) (abs_nonneg (t.2 - s.2)))
      with h | h
    · exact h
    · exfalso
      have h1 : t.1 - s.1 = 0 := abs_eq_zero.mp (by
        have := abs_nonneg (t.2 - s.2); linarith [abs_nonneg (t.1 - s.1)])
      have h2 : t.2 - s.2 = 0 := abs_eq_zero.mp (by
        have := abs_nonneg (t.1 - s.1); linarith [abs_nonneg (t.2 - s.2)])
      exact hts (Prod.ext (by linarith [sub_eq_zero.mp h1]) (by linarith [sub_eq_zero.mp h2])))
    (dotp_self_pos hts)
  have hdist : dist t z = dist z w := by rw [htv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam s t z - 1| < α :=
    calc |footParam s t z - 1| ≤ L * dist z w := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf hLpos
      _ ≤ α := hLr
  have := (abs_lt.mp hbound).1
  linarith

/-- **Shared-edge σ-sign, `+` outgoing.**  A `vertexPlus`-corner point `δ₀`-thin to the
corner's OUTGOING edge `j+1` with foot `≥ α` there lies strictly LEFT of that edge:
`0 < sideForm (segTgt j) (segTgt (j+1)) z`.  Mirrors `bandStrip_outgoing_mem_vertexPlus`'s
thinness chain but stops at the σ-sign (`vertexPlus_sideForm_outgoing_pos`). -/
theorem sideForm_pos_of_vertexPlus_outgoing (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hfoot : α ≤ footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hz : z ∈ vertexPlus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) :
    0 < sideForm (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hfoot
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv hfoot hstrip' hδ
  exact vertexPlus_sideForm_outgoing_pos hτ hG hthin hz

/-- **Shared-edge σ-sign, `−` incoming.**  A `vertexMinus`-corner point `δ₀`-thin to the
corner's INCOMING edge `k` with foot `< 1 − α` there lies strictly RIGHT of that edge:
`sideForm (segSrc k) (segTgt k) z < 0`.  Mirrors `bandStrip_incoming_mem_vertexMinus`'s
thinness chain but stops at the σ-sign (`vertexMinus_sideForm_incoming_neg`). -/
theorem sideForm_neg_of_vertexMinus_incoming (β : PolyArc) {α δ₀ : ℝ} (k : Fin β.numSegs)
    (hk1 : (k : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc k) (β.segTgt k) (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt k - β.segTgt ⟨(k : ℕ) + 1, hk1⟩) (β.segSrc k - β.segTgt k)|
            * (|(β.segSrc k).1 - (β.segTgt k).1| + |(β.segSrc k).2 - (β.segTgt k).2|) * δ₀
          < |sideForm (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) (β.segTgt k) (β.segSrc k)|
            * (α * dotp (β.segSrc k - β.segTgt k) (β.segSrc k - β.segTgt k)))
    {z : Plane} (hfoot : footParam (β.segSrc k) (β.segTgt k) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier k) < δ₀) :
    z ∈ vertexMinus (β.segSrc k) (β.segTgt k) (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) →
    sideForm (β.segSrc k) (β.segTgt k) z < 0 := by
  intro hz
  have hva : β.segTgt k ≠ β.segSrc k := β.segTgt_ne_segSrc k
  have hP : 0 < dotp (β.segTgt k - β.segSrc k) (β.segTgt k - β.segSrc k) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt k) (β.segSrc k - β.segTgt k) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt k) (β.segSrc k) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt k) (β.segSrc k) = β.segCarrier k := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt k) (β.segSrc k)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc k) (v := β.segTgt k)
    (b := β.segTgt ⟨(k : ℕ) + 1, hk1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact vertexMinus_sideForm_incoming_neg hτ hG hthin hz

/-- **Shared-edge σ-sign, `+` incoming.**  A `vertexPlus`-corner point `δ₀`-thin to the
corner's INCOMING edge `j` with foot `< 1 − α` there lies strictly LEFT of that edge:
`0 < sideForm (segSrc j) (segTgt j) z`.  Mirrors `bandStrip_incoming_mem_vertexPlus`'s
thinness chain but stops at the σ-sign (`vertexPlus_sideForm_incoming_pos`). -/
theorem sideForm_pos_of_vertexPlus_incoming (β : PolyArc) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i)))
    {z : Plane} (hmid : footParam (β.segSrc i) (β.segTgt i) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier i) < δ₀)
    (hz : z ∈ vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    0 < sideForm (β.segSrc i) (β.segTgt i) z := by
  have hva : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hP : 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt i) (β.segSrc i - β.segTgt i) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt i) (β.segSrc i) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt i) (β.segSrc i) = β.segCarrier i := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt i) (β.segSrc i)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc i) (v := β.segTgt i)
    (b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact vertexPlus_sideForm_incoming_pos hτ hG hthin hz

/-- **Shared-edge σ-sign, `−` outgoing.**  A `vertexMinus`-corner point `δ₀`-thin to the
corner's OUTGOING edge `j+1` with foot `≥ α` there lies strictly RIGHT of that edge:
`sideForm (segTgt j) (segTgt (j+1)) z < 0`.  Mirrors `bandStrip_outgoing_mem_vertexMinus`'s
thinness chain but stops at the σ-sign (`vertexMinus_sideForm_outgoing_neg`). -/
theorem sideForm_neg_of_vertexMinus_outgoing (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hfoot : α ≤ footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hz : z ∈ vertexMinus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) :
    sideForm (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 0 := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hfoot
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv hfoot hstrip' hδ
  exact vertexMinus_sideForm_outgoing_neg hτ hG hthin hz

/-- **TOP-PRIORITY clipped sector↔sector disjointness, all corner pairs.**  The clipped
positive sector at corner `j` and the clipped negative sector at corner `k` never meet.

Hypothesis regimes (mirroring the GREEN unclipped `disjoint_sectorPlus_sectorMinus_all`,
plus the clip-enabled shared-edge data):
* `hα` — clip margin positive;
* `hδ₀sep`/`hsep` — index-distance ≥ 2 strip separation (far corners);
* `hτ` — per-corner `cornerTurn ≠ 0` (σ-sign selector);
* `r`/`hconf`/`hLr` — adjacent-edge corner confinement radius, the confinement bound and the
  per-edge Lipschitz budgets `Lₑ · r ≤ α` (`not_mem_adjacent_band_strip*` shape);
* `hδout`/`hδin` — per-corner outgoing/incoming σ-thinness budgets
  (`bandStrip_outgoing_mem_vertexPlus` / `bandStrip_incoming_mem_vertexMinus` shape). -/
theorem disjoint_sectorPlusClipped_sectorMinusClipped_all (β : PolyArc) {α δ₀ δsep : ℝ}
    (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
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
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
        * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
            + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
      < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
        * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                   (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
        * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
      < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
        * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (j k : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) (hk1 : (k : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlusClipped β δ₀ α j hj1) (sectorMinusClipped β δ₀ α k hk1) := by
  -- δ₀-version of the strip separation, for the far-corner `Disjoint.mono` route.
  have hsep' : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δ₀ →
      Metric.infDist z (β.segCarrier b) < δ₀ → False :=
    fun a b hab z hza hzb => hsep a b hab z (lt_of_lt_of_le hza hδ₀sep)
      (lt_of_lt_of_le hzb hδ₀sep)
  -- Bridge: every clipped sector sits inside its unclipped sector.
  have hPsub := sectorPlusClipped_subset_sectorPlus β δ₀ α j hj1
  have hMsub := sectorMinusClipped_subset_sectorMinus β δ₀ α k hk1
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  have hkval : ((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) = (k : ℕ) + 1 := rfl
  rcases lt_trichotomy (j : ℕ) (k : ℕ) with hjk | hjkeq | hjk
  · -- j < k
    by_cases hfar : (j : ℕ) + 1 + 1 < (k : ℕ)
    · -- far corners: 4-way strip separation transfers via Disjoint.mono.
      refine Disjoint.mono hPsub hMsub ?_
      exact disjoint_sectorPlus_sectorMinus_diff β δ₀ j k hj1 hk1
        (disjoint_stripSupport_nonadjacent β hsep' j k (by omega))
        (disjoint_stripSupport_nonadjacent β hsep' j ⟨(k : ℕ) + 1, hk1⟩ (by rw [hkval]; omega))
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(j : ℕ) + 1, hj1⟩ k (by rw [hjval]; omega))
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(j : ℕ) + 1, hj1⟩ ⟨(k : ℕ) + 1, hk1⟩
          (by rw [hjval, hkval]; omega))
    · -- k ∈ {j+1, j+2}: clipped-direct, shared-edge σ-sign / corner confinement.
      have hkcases : (k : ℕ) = (j : ℕ) + 1 ∨ (k : ℕ) = (j : ℕ) + 2 := by omega
      rw [Set.disjoint_left]
      intro z hzp hzm
      rcases hkcases with hk1eq | hk2eq
      · -- k = j+1: corners SHARE edge j+1 (= k).
        have hkj : k = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hk1eq
        rcases hzp.2 with hA1 | hA2 <;> rcases hzm.2 with hB1 | hB2
        · -- (A1,B1): adjacent edges j, j+1 share verts(succ j); confine, foot on j+1 small.
          have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
            Fin.ext (by simp [Fin.val_succ])
          have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.verts (Fin.succ j) := by
            rw [PolyArc.segSrc, hidx]
          have hne : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segSrc ⟨(j : ℕ) + 1, hj1⟩ :=
            β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
          have hconf' : dist z (β.verts (Fin.succ j)) < r j :=
            hconf j hj1 hA1.1 (by rw [← hkj]; exact hB1.1)
          have hfoot_lt : footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < α :=
            footParam_lt_of_confined_src hne hsv (hLr j hj1).2 hconf'
          have hB1' : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z := by
            have := hB1.2; rwa [hkj] at this
          linarith
        · -- (A1,B2): edges j and j+2 at index distance 2 → hsep'.
          have hjF : ((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 2 := by
            rw [hkval]; omega
          exact hsep' j ⟨(k : ℕ) + 1, hk1⟩ (by rw [hjF]; omega) z hA1.1 hB2.1
        · -- (A2,B1): SHARED edge j+1, two-sided foot bound → σ-sign clash.
          have hB1' : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z := by
            have := hB1.2; rwa [hkj] at this
          have hpos : 0 < sideForm (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z :=
            sideForm_pos_of_vertexPlus_outgoing β j hj1 hα (hτ j hj1) (hδout j hj1)
              (le_of_lt hB1') hA2.1 hzp.1
          have hstripk : Metric.infDist z (β.segCarrier k) < δ₀ := by rw [hkj]; exact hA2.1
          have hneg : sideForm (β.segSrc k) (β.segTgt k) z < 0 :=
            sideForm_neg_of_vertexMinus_incoming β k hk1 hα (hτ k hk1) (hδin k hk1)
              (by rw [hkj]; exact hA2.2) hstripk hzm.1
          have hskeq : β.segSrc k = β.segTgt j := by
            have hidx : (Fin.castSucc k : Fin (β.numSegs + 1)) = Fin.succ j :=
              Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
          have htkeq : β.segTgt k = β.segTgt ⟨(j : ℕ) + 1, hj1⟩ := by rw [hkj]
          rw [hskeq, htkeq] at hneg
          linarith
        · -- (A2,B2): adjacent edges j+1, j+2 share verts(succ ⟨j+1⟩); foot on j+1 large.
          have hconf' : dist z (β.verts (Fin.succ ⟨(j : ℕ) + 1, hj1⟩)) <
              r ⟨(j : ℕ) + 1, hj1⟩ := by
            have hidxeq : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1,
                by rw [hjval]; omega⟩ : Fin β.numSegs) = ⟨(k : ℕ) + 1, hk1⟩ :=
              Fin.ext (by simp; omega)
            refine hconf ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) hA2.1 ?_
            rw [hidxeq]; exact hB2.1
          have hne : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segSrc ⟨(j : ℕ) + 1, hj1⟩ :=
            β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
          have htv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ = β.verts (Fin.succ ⟨(j : ℕ) + 1, hj1⟩) := rfl
          have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z :=
            footParam_gt_of_confined_tgt hne htv
              (hLr ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega)).1 hconf'
          have hA2'' : footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 1 - α := hA2.2
          linarith
      · -- k = j+2: corners share NO edge; only (A2,B1) is adjacent (edges j+1, j+2).
        rcases hzp.2 with hA1 | hA2 <;> rcases hzm.2 with hB1 | hB2
        · -- (A1,B1): edges j and j+2 → index distance 2 → hsep'.
          exact hsep' j k (by rw [hk2eq]; omega) z hA1.1 hB1.1
        · -- (A1,B2): edges j and j+3 → index distance 3 → hsep'.
          have hkF : ((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 3 := by
            rw [hkval]; omega
          exact hsep' j ⟨(k : ℕ) + 1, hk1⟩ (by rw [hkF]; omega) z hA1.1 hB2.1
        · -- (A2,B1): adjacent edges j+1, j+2 share verts(succ ⟨j+1⟩); foot on j+1 large.
          have hconf' : dist z (β.verts (Fin.succ ⟨(j : ℕ) + 1, hj1⟩)) <
              r ⟨(j : ℕ) + 1, hj1⟩ := by
            have hidxeq : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1,
                by rw [hjval]; omega⟩ : Fin β.numSegs) = k :=
              Fin.ext (by simp; omega)
            refine hconf ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) hA2.1 ?_
            rw [hidxeq]; exact hB1.1
          have hne : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segSrc ⟨(j : ℕ) + 1, hj1⟩ :=
            β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
          have htv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ = β.verts (Fin.succ ⟨(j : ℕ) + 1, hj1⟩) := rfl
          have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z :=
            footParam_gt_of_confined_tgt hne htv
              (hLr ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega)).1 hconf'
          have hA2'' : footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
              (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 1 - α := hA2.2
          linarith
        · -- (A2,B2): edges j+1 and j+3 → index distance 2 → hsep'.
          have hkF : ((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 3 := by
            rw [hkval]; omega
          exact hsep' ⟨(j : ℕ) + 1, hj1⟩ ⟨(k : ℕ) + 1, hk1⟩ (by rw [hjval, hkF]; omega) z
            hA2.1 hB2.1
  · -- j = k: same corner, vertexPlus ∩ vertexMinus = ∅ (transfers via Disjoint.mono).
    have hjkF : j = k := Fin.ext hjkeq
    subst hjkF
    exact Disjoint.mono hPsub hMsub (disjoint_sectorPlus_sectorMinus β δ₀ j hj1)
  · -- k < j
    by_cases hfar : (k : ℕ) + 1 + 1 < (j : ℕ)
    · -- far corners: 4-way strip separation transfers via Disjoint.mono.
      refine Disjoint.mono hPsub hMsub ?_
      exact disjoint_sectorPlus_sectorMinus_diff β δ₀ j k hj1 hk1
        (disjoint_stripSupport_nonadjacent β hsep' k j (by omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(k : ℕ) + 1, hk1⟩ j
          (by rw [hkval]; omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' k ⟨(j : ℕ) + 1, hj1⟩
          (by rw [hjval]; omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(k : ℕ) + 1, hk1⟩ ⟨(j : ℕ) + 1, hj1⟩
          (by rw [hjval, hkval]; omega)).symm
    · -- j ∈ {k+1, k+2}: clipped-direct, shared-edge σ-sign / corner confinement.
      have hjcases : (j : ℕ) = (k : ℕ) + 1 ∨ (j : ℕ) = (k : ℕ) + 2 := by omega
      rw [Set.disjoint_left]
      intro z hzp hzm
      rcases hjcases with hj1eq | hj2eq
      · -- j = k+1: corners SHARE edge k+1 (= j); it is corner j's INCOMING, corner k's OUTGOING.
        have hjk : j = ⟨(k : ℕ) + 1, hk1⟩ := Fin.ext hj1eq
        -- shared-vertex identities for the confinement combos.
        have hidxk : (Fin.castSucc ⟨(k : ℕ) + 1, hk1⟩ : Fin (β.numSegs + 1)) = Fin.succ k :=
          Fin.ext (by simp [Fin.val_succ])
        have hsvk : β.segSrc ⟨(k : ℕ) + 1, hk1⟩ = β.verts (Fin.succ k) := by
          rw [PolyArc.segSrc, hidxk]
        have hnek : β.segTgt ⟨(k : ℕ) + 1, hk1⟩ ≠ β.segSrc ⟨(k : ℕ) + 1, hk1⟩ :=
          β.segTgt_ne_segSrc ⟨(k : ℕ) + 1, hk1⟩
        rcases hzp.2 with hA1 | hA2 <;> rcases hzm.2 with hB1 | hB2
        · -- (A1,B1): SHARED edge j (= k+1): corner j `+` incoming, corner k `−` outgoing.
          -- A1 (corner j incoming, edge j): α < footParam(segSrc j)(segTgt j) z.
          -- B1 (corner k incoming, edge k): NOT shared — that's the other adjacency below.
          -- Wait: B1 is corner k INCOMING (edge k), A1 corner j INCOMING (edge j = k+1):
          -- edges k and k+1 are adjacent (share verts(succ k)).  Confine, foot on edge j small.
          have hconf' : dist z (β.verts (Fin.succ k)) < r k := hconf k hk1 hB1.1
            (by have := hA1.1; rwa [hjk] at this)
          have hfoot_lt : footParam (β.segSrc ⟨(k : ℕ) + 1, hk1⟩)
              (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) z < α :=
            footParam_lt_of_confined_src hnek hsvk (hLr k hk1).2 hconf'
          have hA1' : α < footParam (β.segSrc ⟨(k : ℕ) + 1, hk1⟩)
              (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) z := by
            have := hA1.2; rwa [hjk] at this
          linarith
        · -- (A1,B2): SHARED edge j (= k+1).  corner j `+` incoming, corner k `−` outgoing.
          -- A1 upper-half clip is on edge j incoming: α < footParam(segSrc j)(segTgt j) z.
          -- B2 (corner k outgoing, edge k+1 = j): footParam(segSrc(k+1))(segTgt(k+1)) z < 1−α.
          -- corner j `+`, incoming edge j, foot < 1−α (from B2) ⇒ sideForm(segSrc j)(segTgt j)>0.
          have hB2' : footParam (β.segSrc j) (β.segTgt j) z < 1 - α := by
            have := hB2.2; rwa [← hjk] at this
          have hpos : 0 < sideForm (β.segSrc j) (β.segTgt j) z :=
            sideForm_pos_of_vertexPlus_incoming β j hj1 hα (hτ j hj1) (hδin j hj1)
              hB2' hA1.1 hzp.1
          -- corner k `−`, outgoing edge k+1 = j, foot ≥ α (from A1) ⇒
          -- sideForm(segTgt k)(segTgt(k+1)) z < 0.
          have hA1' : α ≤ footParam (β.segSrc ⟨(k : ℕ) + 1, hk1⟩)
              (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) z := by
            have := hA1.2; rw [hjk] at this; exact le_of_lt this
          have hstripj : Metric.infDist z (β.segCarrier ⟨(k : ℕ) + 1, hk1⟩) < δ₀ := by
            have := hA1.1; rw [hjk] at this; exact this
          have hneg : sideForm (β.segTgt k) (β.segTgt ⟨(k : ℕ) + 1, hk1⟩) z < 0 :=
            sideForm_neg_of_vertexMinus_outgoing β k hk1 hα (hτ k hk1) (hδout k hk1)
              hA1' hstripj hzm.1
          -- segSrc j = segTgt k, segTgt j = segTgt(k+1): same sideForm, sign clash.
          have hsjeq : β.segSrc j = β.segTgt k := by
            have hidx : (Fin.castSucc j : Fin (β.numSegs + 1)) = Fin.succ k :=
              Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
            rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
          have htjeq : β.segTgt j = β.segTgt ⟨(k : ℕ) + 1, hk1⟩ := by rw [hjk]
          rw [hsjeq, htjeq] at hpos
          linarith
        · -- (A2,B1): edges j+1 and k → index distance 2 → hsep'.
          have hjF : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (k : ℕ) + 2 := by
            rw [hjval]; omega
          exact (hsep' k ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjF]; omega) z hB1.1 hA2.1)
        · -- (A2,B2): adjacent edges j+1, j (= k+1) share verts(succ ⟨k⟩? no): foot on edge j large.
          -- A2 (corner j outgoing, edge j+1): footParam(segSrc(j+1))(segTgt(j+1)) z < 1−α.
          -- B2 (corner k outgoing, edge k+1 = j): footParam(segSrc j)(segTgt j) z < 1−α.
          -- edges j and j+1 are adjacent (share verts(succ j) = verts(j+1)).
          -- On edge j (= corner k outgoing), segTgt j = verts(succ j) ⇒ foot > 1−α ⇒ ⊥ vs B2.
          have hconf' : dist z (β.verts (Fin.succ j)) < r j := by
            refine hconf j hj1 ?_ hA2.1
            -- z δ₀-thin to edge j: from B2 (corner k outgoing edge k+1 = j).
            have := hB2.1; rwa [← hjk] at this
          have hnej : β.segTgt j ≠ β.segSrc j := β.segTgt_ne_segSrc j
          have htvj : β.segTgt j = β.verts (Fin.succ j) := rfl
          have hfoot_gt : 1 - α < footParam (β.segSrc j) (β.segTgt j) z :=
            footParam_gt_of_confined_tgt hnej htvj (hLr j hj1).1 hconf'
          have hB2' : footParam (β.segSrc j) (β.segTgt j) z < 1 - α := by
            have := hB2.2; rwa [← hjk] at this
          linarith
      · -- j = k+2: corners share NO edge; only (A1,B2) is adjacent (edges k+1, k+2).
        rcases hzp.2 with hA1 | hA2 <;> rcases hzm.2 with hB1 | hB2
        · -- (A1,B1): edges j and k → index distance 2 → hsep'.
          exact hsep' k j (by rw [hj2eq]; omega) z hB1.1 hA1.1
        · -- (A1,B2): adjacent edges k+1, k+2 (= j) share verts(succ ⟨k+1⟩); foot on edge j small.
          -- A1 (corner j incoming, edge j = k+2): α < footParam(segSrc j)(segTgt j) z.
          -- B2 (corner k outgoing, edge k+1): footParam < 1−α.  edges k+1, k+2 adjacent.
          -- On edge j = k+2, segSrc j = verts(succ ⟨k+1⟩) ⇒ foot < α ⇒ ⊥ vs A1.
          set e2 : Fin β.numSegs := ⟨((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) + 1,
            by rw [hkval]; omega⟩ with he2
          have he2j : e2 = j := Fin.ext (by rw [he2]; simp; omega)
          have hsve2 : β.segSrc e2 = β.verts (Fin.succ ⟨(k : ℕ) + 1, hk1⟩) := by
            have hidx : (Fin.castSucc e2 : Fin (β.numSegs + 1)) = Fin.succ ⟨(k : ℕ) + 1, hk1⟩ :=
              Fin.ext (by rw [he2]; simp only [Fin.val_castSucc, Fin.val_succ])
            rw [PolyArc.segSrc, hidx]
          have hne2 : β.segTgt e2 ≠ β.segSrc e2 := β.segTgt_ne_segSrc e2
          have hconf' : dist z (β.verts (Fin.succ ⟨(k : ℕ) + 1, hk1⟩)) <
              r ⟨(k : ℕ) + 1, hk1⟩ := by
            refine hconf ⟨(k : ℕ) + 1, hk1⟩ (by rw [hkval]; omega) hB2.1 ?_
            rw [show (⟨((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) + 1,
              by rw [hkval]; omega⟩ : Fin β.numSegs) = e2 from rfl, he2j]; exact hA1.1
          have hfoot_lt : footParam (β.segSrc e2) (β.segTgt e2) z < α :=
            footParam_lt_of_confined_src hne2 hsve2
              (hLr ⟨(k : ℕ) + 1, hk1⟩ (by rw [hkval]; omega)).2 hconf'
          rw [he2j] at hfoot_lt
          have hA1' : α < footParam (β.segSrc j) (β.segTgt j) z := hA1.2
          linarith
        · -- (A2,B1): edges j+1 and k → index distance 3 → hsep'.
          have hjF : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (k : ℕ) + 3 := by
            rw [hjval]; omega
          exact hsep' k ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjF]; omega) z hB1.1 hA2.1
        · -- (A2,B2): edges j+1 and k+1 → index distance 2 → hsep'.
          have hjF : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (k : ℕ) + 3 := by
            rw [hjval]; omega
          exact hsep' ⟨(k : ℕ) + 1, hk1⟩ ⟨(j : ℕ) + 1, hj1⟩ (by rw [hkval, hjF]; omega) z
            hB2.1 hA2.1


/-! #### P3 disjointness — clipped cap ↔ sector aggregators.

The endpoint-incident degenerate sub-cases (`j = 0` for the source cap, `j+1 = numSegs−1`
for the target cap) are where the cap disk sits on the arc-endpoint edge that the unclipped
aggregator could not separate.  The clip's foot margin on that very edge keeps the clipped
arm away from the endpoint vertex (`footParam > α` at the source end, `< 1−α` at the target
end), and a disk-smallness budget `Lₑ · ρ ≤ α` (the same Lipschitz constant the corner
confinement uses) turns that into a contradiction with the cap disk's radius. -/

/-- **Source `+` cap ↔ clipped sector⁻, all sector indices.**  `j ≠ 0` transfers from the
GREEN leaf via `Disjoint.mono`; `j = 0`'s incoming arm (edge `0`, foot `> α`) is separated
from the cap disk by the disk-smallness budget `hball`, the outgoing arm (edge `1`) by the
edge-`1` `hbudsrc` budget. -/
theorem disjoint_endCapSrcPlus_sectorMinusClipped_all (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (_hα : 0 < α)
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hball : (|(β.segTgt β.firstSeg).1 - (β.segSrc β.firstSeg).1|
        + |(β.segTgt β.firstSeg).2 - (β.segSrc β.firstSeg).2|)
        / dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
               (β.segTgt β.firstSeg - β.segSrc β.firstSeg) * ρ 0 ≤ α)
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (endCapSrcPlus β ρ) (sectorMinusClipped β δ₀ α j hj1) := by
  by_cases hj0 : (j : ℕ) = 0
  · -- j = 0 = firstSeg: incoming arm IS edge 0 (carries verts 0); clip + disk-smallness.
    have hjfs : j = β.firstSeg := Fin.ext (by rw [hj0]; rfl)
    have hsv : β.segSrc β.firstSeg = β.verts 0 := by rw [PolyArc.segSrc, PolyArc.firstSeg]; rfl
    have hne : β.segTgt β.firstSeg ≠ β.segSrc β.firstSeg := β.segTgt_ne_segSrc β.firstSeg
    rw [Set.disjoint_left]
    intro z hzc hzs
    rcases hzs.2 with hIn | hOut
    · -- incoming arm (edge 0): α < footParam, but disk-smallness forces foot < α.
      have hdisk : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzc.1.1
      have hfoot_lt : footParam (β.segSrc j) (β.segTgt j) z < α := by
        rw [hjfs]
        exact footParam_lt_of_confined_src hne hsv hball hdisk
      have hfoot_gt : α < footParam (β.segSrc j) (β.segTgt j) z := hIn.2
      linarith
    · -- outgoing arm (edge 1 ≠ 0): the edge-1 budget separates the cap disk from the strip.
      have hbud1 := hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega)
      have hdisj := disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbud1
      exact (Set.disjoint_left.mp hdisj) hzc.1.1 hOut.1
  · -- j ≠ 0: every incident edge carries an hbudsrc budget; transfer from the GREEN leaf.
    refine Disjoint.mono (le_refl _) (sectorMinusClipped_subset_sectorMinus β δ₀ α j hj1) ?_
    exact disjoint_endCapSrcPlus_sectorMinus β ρ j hj1 (hbudsrc j hj0)
      (hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega))

/-- **Target `+` cap ↔ clipped sector⁻, all sector indices.**  `j+1 ≠ numSegs−1` transfers
from the GREEN leaf; `j+1 = numSegs−1 = lastSeg`'s outgoing arm (edge `lastSeg`, foot
`< 1−α`) is separated from the cap disk by the disk-smallness budget, the incoming arm by
the edge-`j` `hbudtgt` budget. -/
theorem disjoint_endCapTgtPlus_sectorMinusClipped_all (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (_hα : 0 < α)
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hball : (|(β.segTgt β.lastSeg).1 - (β.segSrc β.lastSeg).1|
        + |(β.segTgt β.lastSeg).2 - (β.segSrc β.lastSeg).2|)
        / dotp (β.segTgt β.lastSeg - β.segSrc β.lastSeg)
               (β.segTgt β.lastSeg - β.segSrc β.lastSeg) * ρ (Fin.last β.numSegs) ≤ α)
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (endCapTgtPlus β ρ) (sectorMinusClipped β δ₀ α j hj1) := by
  by_cases hjlast : (j : ℕ) + 1 = β.numSegs - 1
  · -- j+1 = numSegs-1 = lastSeg: outgoing arm IS edge lastSeg (carries verts last).
    have hj1fs : (⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) = β.lastSeg :=
      Fin.ext (by rw [PolyArc.lastSeg]; exact hjlast)
    have htv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
      rw [PolyArc.segTgt]; congr 1
      apply Fin.ext; simp only [Fin.val_succ, PolyArc.lastSeg, Fin.val_last]; omega
    have hne : β.segTgt β.lastSeg ≠ β.segSrc β.lastSeg := β.segTgt_ne_segSrc β.lastSeg
    rw [Set.disjoint_left]
    intro z hzc hzs
    rcases hzs.2 with hIn | hOut
    · -- incoming arm (edge j ≠ numSegs-1): the edge-j budget separates the cap disk.
      have hbudj := hbudtgt j (by omega)
      have hdisj := disjoint_vertexBall_stripSupport_of_budget β j hbudj
      exact (Set.disjoint_left.mp hdisj) hzc.1.1 hIn.1
    · -- outgoing arm (edge lastSeg): footParam < 1−α, but disk-smallness forces foot > 1−α.
      have hdisk : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
        Metric.mem_ball.mp hzc.1.1
      have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
          (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z := by
        rw [hj1fs]
        exact footParam_gt_of_confined_tgt hne htv hball hdisk
      have hfoot_lt : footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
          (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 1 - α := hOut.2
      linarith
  · -- j+1 ≠ numSegs-1: every incident edge carries an hbudtgt budget; transfer from leaf.
    refine Disjoint.mono (le_refl _) (sectorMinusClipped_subset_sectorMinus β δ₀ α j hj1) ?_
    refine disjoint_endCapTgtPlus_sectorMinus β ρ j hj1 (hbudtgt j (by omega)) ?_
    exact hbudtgt ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ β.numSegs - 1; exact hjlast)

/-- **Clipped sector⁺ ↔ source `−` cap, all sector indices.**  Mirror of
`disjoint_endCapSrcPlus_sectorMinusClipped_all` with the sides flipped. -/
theorem disjoint_sectorPlusClipped_endCapSrcMinus_all (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (_hα : 0 < α)
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hball : (|(β.segTgt β.firstSeg).1 - (β.segSrc β.firstSeg).1|
        + |(β.segTgt β.firstSeg).2 - (β.segSrc β.firstSeg).2|)
        / dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
               (β.segTgt β.firstSeg - β.segSrc β.firstSeg) * ρ 0 ≤ α)
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlusClipped β δ₀ α j hj1) (endCapSrcMinus β ρ) := by
  by_cases hj0 : (j : ℕ) = 0
  · have hjfs : j = β.firstSeg := Fin.ext (by rw [hj0]; rfl)
    have hsv : β.segSrc β.firstSeg = β.verts 0 := by rw [PolyArc.segSrc, PolyArc.firstSeg]; rfl
    have hne : β.segTgt β.firstSeg ≠ β.segSrc β.firstSeg := β.segTgt_ne_segSrc β.firstSeg
    rw [Set.disjoint_left]
    intro z hzs hzc
    rcases hzs.2 with hIn | hOut
    · have hdisk : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzc.1.1
      have hfoot_lt : footParam (β.segSrc j) (β.segTgt j) z < α := by
        rw [hjfs]; exact footParam_lt_of_confined_src hne hsv hball hdisk
      have hfoot_gt : α < footParam (β.segSrc j) (β.segTgt j) z := hIn.2
      linarith
    · have hbud1 := hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega)
      have hdisj := disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbud1
      exact (Set.disjoint_left.mp hdisj) hzc.1.1 hOut.1
  · refine Disjoint.mono (sectorPlusClipped_subset_sectorPlus β δ₀ α j hj1) (le_refl _) ?_
    exact disjoint_sectorPlus_endCapSrcMinus β ρ j hj1 (hbudsrc j hj0)
      (hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega))

/-- **Clipped sector⁺ ↔ target `−` cap, all sector indices.**  Mirror of
`disjoint_endCapTgtPlus_sectorMinusClipped_all` with the sides flipped. -/
theorem disjoint_sectorPlusClipped_endCapTgtMinus_all (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (_hα : 0 < α)
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hball : (|(β.segTgt β.lastSeg).1 - (β.segSrc β.lastSeg).1|
        + |(β.segTgt β.lastSeg).2 - (β.segSrc β.lastSeg).2|)
        / dotp (β.segTgt β.lastSeg - β.segSrc β.lastSeg)
               (β.segTgt β.lastSeg - β.segSrc β.lastSeg) * ρ (Fin.last β.numSegs) ≤ α)
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlusClipped β δ₀ α j hj1) (endCapTgtMinus β ρ) := by
  by_cases hjlast : (j : ℕ) + 1 = β.numSegs - 1
  · have hj1fs : (⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) = β.lastSeg :=
      Fin.ext (by rw [PolyArc.lastSeg]; exact hjlast)
    have htv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
      rw [PolyArc.segTgt]; congr 1
      apply Fin.ext; simp only [Fin.val_succ, PolyArc.lastSeg, Fin.val_last]; omega
    have hne : β.segTgt β.lastSeg ≠ β.segSrc β.lastSeg := β.segTgt_ne_segSrc β.lastSeg
    rw [Set.disjoint_left]
    intro z hzs hzc
    rcases hzs.2 with hIn | hOut
    · have hbudj := hbudtgt j (by omega)
      have hdisj := disjoint_vertexBall_stripSupport_of_budget β j hbudj
      exact (Set.disjoint_left.mp hdisj) hzc.1.1 hIn.1
    · have hdisk : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
        Metric.mem_ball.mp hzc.1.1
      have hfoot_gt : 1 - α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
          (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z := by
        rw [hj1fs]; exact footParam_gt_of_confined_tgt hne htv hball hdisk
      have hfoot_lt : footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩)
          (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 1 - α := hOut.2
      linarith
  · refine Disjoint.mono (sectorPlusClipped_subset_sectorPlus β δ₀ α j hj1) (le_refl _) ?_
    refine disjoint_sectorPlus_endCapTgtMinus β ρ j hj1 (hbudtgt j (by omega)) ?_
    exact hbudtgt ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ β.numSegs - 1; exact hjlast)
/-! #### P3 disjointness — the master assembly.

`collarPlus` and `collarMinus` share the ground set `taperedTube R S δ₀ \ carrier`, so their
disjointness reduces to the disjointness of their union-parts.  Expanding both `±` unions
into their four pieces (band strips, vertex sectors, source cap, target cap) gives a 4×4
grid; each of the sixteen cells is dispatched to one of the per-cell lemmas above. -/

/-- **The two collar sides are disjoint.**  Bundles the geometric admissibility of the
parameters: `hα` (narrowing width positive), `hsep`/`hδ₀sep`/`hρsep` (a non-adjacent
edge separation at width `δsep` dominating both `δ₀` and every disk radius), `hadj_tgt`/
`hadj_src` (the corner band/band impossibility at both adjacency orientations),
`hτ`/`hδin`/`hδout` (per-corner turn nonzero and the angle-free thinness thresholds),
`hballs` (pairwise-disjoint vertex/endpoint disks), and `hbudsrc`/`hbudtgt` (endpoint disks
separated from non-incident edges). -/
theorem disjoint_collarPlus_collarMinus (β : PolyArc) (R S : Set Plane) {δ₀ α δsep : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
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
    (hballSrc : (|(β.segTgt β.firstSeg).1 - (β.segSrc β.firstSeg).1|
        + |(β.segTgt β.firstSeg).2 - (β.segSrc β.firstSeg).2|)
        / dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
               (β.segTgt β.firstSeg - β.segSrc β.firstSeg) * ρ 0 ≤ α)
    (hballTgt : (|(β.segTgt β.lastSeg).1 - (β.segSrc β.lastSeg).1|
        + |(β.segTgt β.lastSeg).2 - (β.segSrc β.lastSeg).2|)
        / dotp (β.segTgt β.lastSeg - β.segSrc β.lastSeg)
               (β.segTgt β.lastSeg - β.segSrc β.lastSeg) * ρ (Fin.last β.numSegs) ≤ α)
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
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (hballs : ∀ p q : Fin (β.numSegs + 1), p ≠ q →
      Disjoint (Metric.ball (β.verts p) (ρ p)) (Metric.ball (β.verts q) (ρ q)))
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
  have h0last : (0 : Fin (β.numSegs + 1)) ≠ Fin.last β.numSegs := by
    intro h; have h2 := congrArg Fin.val h
    simp [Fin.val_last] at h2; have := β.numSegs_pos; omega
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hP := hzp.2
  have hM := hzm.2
  rcases hP with ((hp | hp) | hp) | hp
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_bandStripPlus_bandStripMinus_all β hδ₀sep hsep hadj_tgt hadj_src i k) hpi hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_bandStripPlus_sectorMinus_all β hα hδ₀sep hsep hadj_tgt hadj_src
          hτ hδin hδout i k hk1)
        hpi (sectorMinusClipped_subset_sectorMinus β δ₀ α k hk1 hmk)
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrcMinus_bandStripPlus_all β ρ hbudsrc i).symm hpi hm
    · exact Set.disjoint_left.mp
        (disjoint_endCapTgtMinus_bandStripPlus_all β ρ hbudtgt i).symm hpi hm
  · obtain ⟨j, hj1, hpj⟩ := Set.mem_iUnion₂.mp hp
    rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_sectorPlus_bandStripMinus_all β hα hδ₀sep hsep hadj_tgt hadj_src
          hτ hδin hδout k j hj1)
        (sectorPlusClipped_subset_sectorPlus β δ₀ α j hj1 hpj) hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_sectorPlusClipped_sectorMinusClipped_all β hα hδ₀sep hsep hτ r hconf hLr
          hδout hδin j k hj1 hk1) hpj hmk
    · exact Set.disjoint_left.mp
        (disjoint_sectorPlusClipped_endCapSrcMinus_all β ρ hα hbudsrc hballSrc j hj1) hpj hm
    · exact Set.disjoint_left.mp
        (disjoint_sectorPlusClipped_endCapTgtMinus_all β ρ hα hbudtgt hballTgt j hj1) hpj hm
  · rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapSrcPlus_bandStripMinus_all β ρ hbudsrc k) hp hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapSrcPlus_sectorMinusClipped_all β ρ hα hbudsrc hballSrc k hk1) hp hmk
    · exact Set.disjoint_left.mp (disjoint_endCapSrcPlus_endCapSrcMinus β ρ) hp hm
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrc_endCapTgt β ρ (hballs 0 (Fin.last β.numSegs) h0last)) hp hm
  · rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapTgtPlus_bandStripMinus_all β ρ hbudtgt k) hp hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapTgtPlus_sectorMinusClipped_all β ρ hα hbudtgt hballTgt k hk1) hp hmk
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrcMinus_endCapTgtPlus β ρ (hballs 0 (Fin.last β.numSegs) h0last)).symm
        hp hm
    · exact Set.disjoint_left.mp (disjoint_endCapTgtPlus_endCapTgtMinus β ρ) hp hm

/-! #### P3 existence — the separation primitives.

Three positive constants extracted from the (finite, simple) arc geometry: a common disk
radius making all vertex/endpoint disks pairwise disjoint, and the gaps from each endpoint
to its non-incident edges.  The master's `hballs`, `hbudsrc`, `hbudtgt` sit below these. -/

/-- A single positive disk radius `ρ₀` making the `numSegs+1` vertex disks pairwise
disjoint (one third of the minimal inter-vertex distance). -/
theorem exists_pos_disk_radius (β : PolyArc) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ p q : Fin (β.numSegs + 1), p ≠ q →
      Disjoint (Metric.ball (β.verts p) ρ₀) (Metric.ball (β.verts q) ρ₀) := by
  classical
  have hne : (Finset.univ : Finset (Fin (β.numSegs + 1))).offDiag.Nonempty := by
    refine ⟨(0, Fin.last β.numSegs),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩⟩
    intro h; have h2 := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at h2; have := β.numSegs_pos; omega
  set d := (Finset.univ.offDiag).inf' hne (fun pq => dist (β.verts pq.1) (β.verts pq.2)) with hd
  have hdpos : 0 < d := by
    rw [hd, Finset.lt_inf'_iff]
    intro pq hpq
    rw [Finset.mem_offDiag] at hpq
    exact dist_pos.mpr (fun h => hpq.2.2 (β.distinct h))
  refine ⟨d / 3, by linarith, ?_⟩
  intro p q hpq
  apply Metric.ball_disjoint_ball
  have hmem : (p, q) ∈ (Finset.univ : Finset (Fin (β.numSegs + 1))).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hpq⟩
  have hle : d ≤ dist (β.verts p) (β.verts q) := by
    rw [hd]; exact Finset.inf'_le (fun pq => dist (β.verts pq.1) (β.verts pq.2)) hmem
  linarith

/-- A positive gap `d` from the source endpoint `verts 0` to every non-incident edge. -/
theorem exists_pos_src_edge_sep (β : PolyArc) :
    ∃ d : ℝ, 0 < d ∧ ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      d ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun i => if (i : ℕ) = 0 then 1 else Metric.infDist (β.verts 0) (β.segCarrier i) with hf
  have hfpos : ∀ i, 0 < f i := by
    intro i; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact i).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc i, left_mem_segment ℝ _ _⟩).mp (β.src_notMem_segCarrier i h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne f with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hfpos i
  refine ⟨m, hmpos, fun i hi => ?_⟩
  have hle : m ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
  have hfi : f i = Metric.infDist (β.verts 0) (β.segCarrier i) := by
    simp only [hf]; rw [if_neg hi]
  rwa [hfi] at hle

/-- A positive gap `d` from the target endpoint `verts (last)` to every non-incident edge. -/
theorem exists_pos_tgt_edge_sep (β : PolyArc) :
    ∃ d : ℝ, 0 < d ∧ ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      d ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun i => if (i : ℕ) = β.numSegs - 1 then 1
      else Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) with hf
  have hfpos : ∀ i, 0 < f i := by
    intro i; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact i).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc i, left_mem_segment ℝ _ _⟩).mp (β.tgt_notMem_segCarrier i h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne f with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hfpos i
  refine ⟨m, hmpos, fun i hi => ?_⟩
  have hle : m ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
  have hfi : f i = Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
    simp only [hf]; rw [if_neg hi]
  rwa [hfi] at hle


end CrossingLemma.PlaneArcSeparation
