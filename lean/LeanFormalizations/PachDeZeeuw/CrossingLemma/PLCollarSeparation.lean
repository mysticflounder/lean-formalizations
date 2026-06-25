/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLAssembly
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DartSectorPoint

/-!
# Polygonal collar separation

This module specializes the abstract collar assembly theorem to the concrete
polygonal collar built in `PolygonalArc`.

It deliberately leaves the two genuinely geometric obligations explicit:

* `P5`: each collar side is preconnected.

The routine collar data already proved in `PolygonalArc` is wired in here: openness of
the collar sides, the `P2` union identity, the tapered tube facts, and nonemptiness
of the two sides.
-/

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

/-- **Polygonal collar separation.**

This is the `PolygonalArc` specialization of `exists_twoSidedPartition_of_collar`.
For a simply connected open region `R` and a polygonal crosscut carrier
`β.carrier`, a concrete collar `collarPlus β R S δ₀ α ρ` /
`collarMinus β R S δ₀ α ρ` gives a two-sided open partition of
`regionMinusArc R β.toSimpleArc` once the remaining non-formal collar
obligation `P5` (`hTp_pre`, `hTm_pre`) is supplied.

All other hypotheses are the already-formalized PL collar side conditions used by
`union_collarPlus_collarMinus`, `collarPlus_nonempty`,
`collarMinus_nonempty`, and `isPreconnected_taperedTube`. -/
theorem exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides
    (β : PolygonalArc) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V,
      IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V ∧
        collarPlus β R S δ₀ α ρ ⊆ U ∧
        collarMinus β R S δ₀ α ρ ⊆ V := by
  classical
  have hRc : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  have hT_pre : IsPreconnected (taperedTube R S δ₀) :=
    isPreconnected_taperedTube hR hRc hδ hSR hSpre ⟨firstMid β, hmS⟩
  have hpart :
      collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ =
        taperedTube R S δ₀ \ β.carrier :=
    union_collarPlus_collarMinus β R S hS_carrier hsrc0 hsrcL ρ hα hturn
      hband hsrc htgt hballV hballSrc hballTgt
  obtain ⟨U, V, hUV, hPlusU, hMinusV⟩ :=
    exists_twoSidedPartition_of_collar_with_collar_sides
    (R := R) (C := β.carrier) (T := taperedTube R S δ₀)
    (Tp := collarPlus β R S δ₀ α ρ) (Tm := collarMinus β R S δ₀ α ρ)
    hR hRsc β.isClosed_carrier (isOpen_taperedTube R S δ₀)
    (taperedTube_subset R S δ₀) hT_pre
    (isOpen_collarPlus β R S δ₀ α ρ) (isOpen_collarMinus β R S δ₀ α ρ)
    hdisj hpart hTp_pre hTm_pre
    (collarPlus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    (collarMinus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    hcover
  refine ⟨U, V, ?_, hPlusU, hMinusV⟩
  simpa [regionMinusArc, SimpleArc.carrier, β.range_toSimpleArc] using hUV

/-- **Polygonal collar separation, single-segment (`numSegs = 1`) — `sorry`-free.**

Weaker conclusion than `exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides`
(bare `∃ U V, IsTwoSidedPartition ...`, without the `collarPlus ⊆ U`/`collarMinus ⊆ V` witnesses),
but it routes the `P2` union identity through the `sorry`-free single-segment lemma
`union_collarPlus_collarMinus_of_numSegs_one` instead of the general
`union_collarPlus_collarMinus` (whose interior-vertex disk branch is sorried).  Every
other ingredient (`exists_twoSidedPartition_of_collar_with_collar_sides`,
`collarPlus_nonempty`, `isPreconnected_taperedTube`, …) is already `sorry`-free, so a
theorem feeding this entry point has a Lean-core-only axiom closure.  The vacuous
`hturn`/`hballV` binders are dropped (they only fed the general union lemma). -/
theorem exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides_of_numSegs_one
    (β : PolygonalArc) (h1 : β.numSegs = 1) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  classical
  have hRc : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  have hT_pre : IsPreconnected (taperedTube R S δ₀) :=
    isPreconnected_taperedTube hR hRc hδ hSR hSpre ⟨firstMid β, hmS⟩
  have hpart :
      collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ =
        taperedTube R S δ₀ \ β.carrier :=
    union_collarPlus_collarMinus_of_numSegs_one β h1 R S hS_carrier hsrc0 hsrcL ρ hα
      hband hsrc htgt hballSrc hballTgt
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_of_collar_with_collar_sides
    (R := R) (C := β.carrier) (T := taperedTube R S δ₀)
    (Tp := collarPlus β R S δ₀ α ρ) (Tm := collarMinus β R S δ₀ α ρ)
    hR hRsc β.isClosed_carrier (isOpen_taperedTube R S δ₀)
    (taperedTube_subset R S δ₀) hT_pre
    (isOpen_collarPlus β R S δ₀ α ρ) (isOpen_collarMinus β R S δ₀ α ρ)
    hdisj hpart hTp_pre hTm_pre
    (collarPlus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    (collarMinus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    hcover
  exact ⟨U, V, by simpa [regionMinusArc, SimpleArc.carrier, β.range_toSimpleArc] using hUV⟩

/-- **Polygonal collar separation.**

This is the `PolygonalArc` specialization of `exists_twoSidedPartition_of_collar`.
For a simply connected open region `R` and a polygonal crosscut carrier
`β.carrier`, a concrete collar `collarPlus β R S δ₀ α ρ` /
`collarMinus β R S δ₀ α ρ` gives a two-sided open partition of
`regionMinusArc R β.toSimpleArc` once the remaining non-formal collar
obligation `P5` (`hTp_pre`, `hTm_pre`) is supplied.

All other hypotheses are the already-formalized PL collar side conditions used by
`union_collarPlus_collarMinus`, `collarPlus_nonempty`,
`collarMinus_nonempty`, and `isPreconnected_taperedTube`. -/
theorem exists_twoSidedPartition_regionMinus_polygonalArc_of_collar
    (β : PolygonalArc) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides β ρ
      hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hmS hmR
      hturn hband hsrc htgt hballV hballSrc hballTgt hdisj hTp_pre hTm_pre hcover
  exact ⟨U, V, hUV⟩

/-- **Polygonal collar separation with `P5` discharged by sliver-budget collars.**

This is the `PolygonalArc` specialization of
`exists_twoSidedPartition_regionMinus_polygonalArc_of_collar` where the remaining
collar-connectivity obligation `P5` is supplied by the sliver-budget collar
theorems from `PolygonalArc`.  The explicit hypotheses are therefore the already-used
`P1`--`P4` collar data together with the band/sector containment budgets and the
source/target end-cap sliver-budget hypotheses on both signs. -/
theorem exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_of_sliver_budgets_with_collar_sides
    (β : PolygonalArc) {R S : Set Plane} {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2) (hα3 : α < 1 / 3)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
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
    (hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
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
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V,
      IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V ∧
        collarPlus β R S δ₀ α ρ ⊆ U ∧
        collarMinus β R S δ₀ α ρ ⊆ V := by
  have hα1 : α < 1 := by linarith
  refine exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides β ρ
    hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hmS hmR
    hturn hband hsrc htgt hballV hballSrc hballTgt hdisj ?_ ?_ hcover
  · exact isPreconnected_collarPlus_of_sliver_budgets β R S ρ hturn hδ hα hα3 hα1 hsectorWPlus
      hδ₀sep hsep hadj_tgt hadj_src hsmall hSband hRband
      hsrc htgt hSrcSep hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver
      hTgtSep hTgtSpine hTgtNear hρL hTgtRpos hTgtSliver
  · exact isPreconnected_collarMinus_of_sliver_budgets β R S ρ hturn hδ hα hα3 hα1 hsectorWMinus
      hδ₀sep hsep hadj_tgt hadj_src hsmall hSband hRband
      hsrc htgt hSrcSep hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver
      hTgtSep hTgtSpine hTgtNear hρL hTgtRpos hTgtSliver

/-- **Polygonal collar separation with `P5` discharged by sliver-budget collars.**

This is the `PolygonalArc` specialization of
`exists_twoSidedPartition_regionMinus_polygonalArc_of_collar` where the remaining
collar-connectivity obligation `P5` is supplied by the sliver-budget collar
theorems from `PolygonalArc`.  The explicit hypotheses are therefore the already-used
`P1`--`P4` collar data together with the band/sector containment budgets and the
source/target end-cap sliver-budget hypotheses on both signs. -/
theorem exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_of_sliver_budgets
    (β : PolygonalArc) {R S : Set Plane} {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2) (hα3 : α < 1 / 3)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
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
    (hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
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
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_of_sliver_budgets_with_collar_sides
      β ρ hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hα3 hmS hmR
      hturn hband hsrc htgt hballV hballSrc hballTgt hdisj hδ₀sep hsep
      hadj_tgt hadj_src hsmall hSband hRband hsectorWPlus hsectorWMinus hSrcSep
      hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver hTgtSep hTgtSpine hTgtNear
      hρL hTgtRpos hTgtSliver hcover
  exact ⟨U, V, hUV⟩

/-- **Positive single-segment collar lies on the positive side of the segment.**

For `β.numSegs = 1` the only band/end-cap pieces of `collarPlus` carry the
`0 < sideForm s t` half-plane test of the unique segment (`s = β.segSrc
β.firstSeg`, `t = β.segTgt β.firstSeg`); the vertex-sector union is empty.  Hence
every collar point is strictly on the positive side of the segment line. -/
theorem collarPlus_subset_pos_sideForm_of_numSegs_one
    (β : PolygonalArc) (h1 : β.numSegs = 1) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) :
    collarPlus β R S δ₀ α ρ ⊆
      {z | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z} := by
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolygonalArc.lastSeg, PolygonalArc.firstSeg]; omega
  rintro z ⟨-, hz2⟩
  rcases hz2 with ((hband | hsector) | hsrc) | htgt
  · -- band strip of the unique segment
    rcases Set.mem_iUnion.mp hband with ⟨i, hzi⟩
    have hieq : i = β.firstSeg := by
      apply Fin.ext; have := i.isLt; simp only [PolygonalArc.firstSeg]; omega
    subst hieq
    exact hzi.1.2
  · -- vertex-sector union: empty for a single segment
    rcases Set.mem_iUnion.mp hsector with ⟨i, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨hi1, -⟩
    have := i.isLt; omega
  · -- source end cap
    exact hsrc.2
  · -- target end cap
    have hh : (0 : ℝ) < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := htgt.2
    rwa [hlast] at hh

/-- **Negative single-segment collar lies on the negative side of the segment.**
See `collarPlus_subset_pos_sideForm_of_numSegs_one`. -/
theorem collarMinus_subset_neg_sideForm_of_numSegs_one
    (β : PolygonalArc) (h1 : β.numSegs = 1) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) :
    collarMinus β R S δ₀ α ρ ⊆
      {z | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0} := by
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolygonalArc.lastSeg, PolygonalArc.firstSeg]; omega
  rintro z ⟨-, hz2⟩
  rcases hz2 with ((hband | hsector) | hsrc) | htgt
  · rcases Set.mem_iUnion.mp hband with ⟨i, hzi⟩
    have hieq : i = β.firstSeg := by
      apply Fin.ext; have := i.isLt; simp only [PolygonalArc.firstSeg]; omega
    subst hieq
    exact hzi.1.2
  · rcases Set.mem_iUnion.mp hsector with ⟨i, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨hi1, -⟩
    have := i.isLt; omega
  · exact hsrc.2
  · have hh : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := htgt.2
    rwa [hlast] at hh

set_option maxHeartbeats 1600000 in
/-- **Two-sided partition for a single-segment polygonal crosscut.**

For a `PolygonalArc` `β` with exactly one segment (`β.numSegs = 1`) the collar
construction has no interior vertices, so there are no vertex sectors and the
endpoint-cap turn obstructions are vacuous.  The collar parameters `δ₀` and `ρ`
are chosen *internally* (a small `δ₀` controlled by the segment geometry and a
constant ball radius `ρ`), and disjointness of the two collar sides is proved
directly from the segment's `sideForm` sign, not from any multi-segment master
disjointness lemma.  All remaining hypotheses are the `δ₀`/`ρ`-free collar data
that the caller must supply.

The result is the bare two-sided partition (`P5`-discharged) obtained by handing
the internally chosen parameters to
`exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides_of_numSegs_one`. -/
theorem exists_twoSidedPartition_of_straightArc
    (β : PolygonalArc) (h1 : β.numSegs = 1) {R S : Set Plane} {α : ℝ}
    (hα : 0 < α) (hα3 : α < 1 / 3)
    {mR : ℝ} (hmRpos : 0 < mR)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hmS : firstMid β ∈ S)
    (hSband : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband_lb : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      mR ≤ Metric.infDist y Rᶜ)
    (hSrcSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear_L : ∀ p ∈ S,
      dist p (β.verts 0) < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) →
      p ∈ β.segCarrier β.firstSeg ∧
        0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∧
        dist p (β.verts 0) =
          footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p *
            dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hSrcRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hTgtSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear_L : ∀ p ∈ S,
      dist p (β.verts (Fin.last β.numSegs)) <
          dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) →
      p ∈ β.segCarrier β.lastSeg ∧
        0 < footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∧
        dist p (β.verts (Fin.last β.numSegs)) =
          footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p *
            dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg))
    (hTgtRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hcover : ∀ δ₀ : ℝ, 0 < δ₀ → R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  classical
  have hα2 : α < 1 / 2 := by linarith
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolygonalArc.lastSeg, PolygonalArc.firstSeg]; omega
  -- Segment data of the unique edge.
  set s : Plane := β.segSrc β.firstSeg with hs
  set t : Plane := β.segTgt β.firstSeg with ht
  set L : ℝ := dist s t with hL
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hLpos : 0 < L := dist_pos.mpr fun h => hts h.symm
  set dotpst : ℝ := dotp (t - s) (t - s) with hdotp
  have hdotppos : 0 < dotpst := dotp_self_pos hts
  set sum : ℝ := |t.1 - s.1| + |t.2 - s.2| with hsum
  have hsumpos : 0 < sum := by
    rw [hsum]
    have hcoord : t.1 - s.1 ≠ 0 ∨ t.2 - s.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hts (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
    rcases hcoord with h1' | h1'
    · have := abs_pos.mpr h1'; have := abs_nonneg (t.2 - s.2); linarith
    · have := abs_pos.mpr h1'; have := abs_nonneg (t.1 - s.1); linarith
  -- Internal δ₀ and ρ choices.  The `L * (1 - 3 * α) / 3` slot (tighter than the
  -- former `1 - 2 * α`) guarantees the open slice range `c_max = (ρval + δ₀)/L`
  -- stays inside the safe foot window `[α/2, 1 - α/2]`, where `hRband_lb` gives the
  -- per-slice depth used by the sliver budget.
  set δ₀ : ℝ := min (min (L * (1 - 3 * α) / 3) ((α / 2) * dotpst / sum)) (mR / 2) with hδ₀def
  have h13 : 0 < 1 - 3 * α := by linarith
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    refine lt_min (lt_min ?_ ?_) ?_
    · positivity
    · positivity
    · linarith
  have hδ₀_le1 : δ₀ ≤ L * (1 - 3 * α) / 3 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀_le2 : δ₀ ≤ (α / 2) * dotpst / sum := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀_le3 : δ₀ ≤ mR / 2 := min_le_right _ _
  have hδ₀_ltL : δ₀ < L * (1 - 2 * α) := by
    have hpos : 0 < L * (1 - 2 * α) := by have : 0 < 1 - 2 * α := by linarith
                                          positivity
    have hmono : L * (1 - 3 * α) / 3 ≤ L * (1 - 2 * α) := by nlinarith [hLpos, hα, h13]
    linarith [hδ₀_le1, hmono]
  set ρval : ℝ := (δ₀ + 2 * α * L + L) / 2 with hρval
  set ρ : Fin (β.numSegs + 1) → ℝ := fun _ => ρval with hρ
  have hbudget : δ₀ + 2 * α * L < ρval := by rw [hρval]; linarith [hδ₀_ltL]
  have hρLe : ρval ≤ L := by rw [hρval]; linarith [hδ₀_ltL]
  have hρNear : ρval + δ₀ ≤ L := by rw [hρval]; nlinarith [hδ₀_le1, hLpos, hα, h13]
  have hρpos : 0 < ρval := by rw [hρval]; nlinarith [hδ₀pos, hLpos, hα]
  -- Internal open slice range top: `c_max·L = ρval + δ₀` (the open-interval
  -- reconciliation of the cap-tube-witness reach and the strict sliver budget).
  set c_max : ℝ := (ρval + δ₀) / L with hc_max
  have hc_maxL : c_max * L = ρval + δ₀ := by rw [hc_max]; field_simp
  have hc_maxpos : 0 < c_max := by rw [hc_max]; positivity
  -- The slice range sits in the safe foot window, so `hRband_lb` applies on it.
  have hc_max_safe : c_max ≤ 1 - α / 2 := by
    rw [hc_max, div_le_iff₀ hLpos]; nlinarith [hδ₀_le1, hLpos, hα, h13]
  have hc_maxlt1 : c_max < 1 := by linarith [hc_max_safe, hα]
  -- `hsmall` for the unique edge.
  have hsmall_first :
      sum / dotpst * δ₀ ≤ α / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hdotppos]
    have hkey : sum * δ₀ ≤ sum * ((α / 2) * dotpst / sum) :=
      mul_le_mul_of_nonneg_left hδ₀_le2 hsumpos.le
    have hsimp : sum * ((α / 2) * dotpst / sum) = α / 2 * dotpst := by
      field_simp
    rw [hsimp] at hkey
    exact hkey
  -- The reusable single-edge facts that every index argument reduces to.
  have hfirst_dist : dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) = L := by rw [hL, hs, ht]
  have hidx : ∀ i : Fin β.numSegs, i = β.firstSeg := by
    intro i; apply Fin.ext; have := i.isLt; simp only [PolygonalArc.firstSeg]; omega
  -- Disjointness directly from the segment's `sideForm` sign.
  have hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
    rw [Set.disjoint_left]
    intro z hzP hzM
    have hP : 0 < sideForm s t z := by
      have := collarPlus_subset_pos_sideForm_of_numSegs_one β h1 R S δ₀ α ρ hzP
      rwa [← hs, ← ht] at this
    have hM : sideForm s t z < 0 := by
      have := collarMinus_subset_neg_sideForm_of_numSegs_one β h1 R S δ₀ α ρ hzM
      rwa [← hs, ← ht] at this
    linarith
  have hα1 : α < 1 := by linarith
  -- Shared `δ₀`/`ρ`-budget facts (the single edge collapses every indexed goal to one fact).
  have hmR : 0 < Metric.infDist (firstMid β) Rᶜ := by
    have hmem := firstMid_mem_segCarrier β
    have hfoot : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 / 2 :=
      firstMid_footParam β
    have hfootmem : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β)
        ∈ Set.Icc (α / 2) (1 - α / 2) := by
      rw [hfoot]; constructor <;> [linarith; linarith]
    have hlb := hRband_lb (firstMid β) hmem hfootmem
    linarith [hlb, hmRpos]
  have hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := by
    intro i
    rw [hidx i, ← hs, ← ht, ← hsum, ← hdotp]
    have hkey : sum * δ₀ ≤ α / 2 * dotpst := by
      have := hsmall_first
      rw [div_mul_eq_mul_div, div_le_iff₀ hdotppos] at this
      exact this
    nlinarith [hkey, hdotppos, hα]
  have hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i) := by
    intro i
    rw [hidx i, ← hs, ← ht]
    show δ₀ + 2 * α * dist s t < ρval
    rw [← hL]; linarith [hbudget]
  have htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i) := by
    intro i
    rw [hidx i, ← hs, ← ht]
    show δ₀ + 2 * α * dist s t < ρval
    rw [← hL]; linarith [hbudget]
  have hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    show ρval ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
    rw [hfirst_dist]; exact hρLe
  have hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) := by
    show ρval ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
    rw [hlast, hfirst_dist]; exact hρLe
  have hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δ₀ →
      Metric.infDist z (β.segCarrier b) < δ₀ → False :=
    fun a b hab z _ _ => absurd hab (by have := h1; have := b.isLt; omega)
  have hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False :=
    fun c hc1 z _ _ _ => absurd hc1 (by have := h1; omega)
  have hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False :=
    fun c hc1 z _ _ _ => absurd hc1 (by have := h1; omega)
  have hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2 := by
    intro i
    rw [hidx i, ← hs, ← ht, ← hsum, ← hdotp]
    exact hsmall_first
  have hSband' : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S := by
    intro i
    rw [hidx i, ← hs, ← ht]
    exact hSband
  have hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2 := by
    intro i y hy hfoot
    rw [hidx i] at hy hfoot
    rw [← hs, ← ht] at hfoot
    have hlb := hRband_lb y hy hfoot
    rw [hδ₀def]
    have : (mR / 2 : ℝ) ≤ Metric.infDist y Rᶜ / 2 := by linarith [hlb]
    calc min (min (L * (1 - 3 * α) / 3) (α / 2 * dotpst / sum)) (mR / 2)
        ≤ mR / 2 := min_le_right _ _
      _ ≤ Metric.infDist y Rᶜ / 2 := this
  have hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := by
    intro i hi0
    exact absurd (hidx i ▸ rfl : (i : ℕ) = 0) hi0
  -- `hSrcNear` at the cap reach `ρ 0 + δ₀ = c_max·L`.  A near-source spine point is a
  -- forward first-edge point with `dist = foot·L`, so `foot·L = dist < c_max·L` forces
  -- `foot < c_max` STRICTLY — the open foot range the Ioo cap cover needs.
  have hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max := by
    intro p hp hd
    have hdv : dist p (β.verts 0) < ρval + δ₀ := hd
    have hdL : dist p (β.verts 0) < L := by linarith [hdv, hρNear, hδ₀pos]
    obtain ⟨hpseg, hfootpos, hfooteq⟩ := hSrcNear_L p hp hdL
    refine ⟨hpseg, hfootpos, ?_⟩
    -- `foot · L = dist p src < ρval + δ₀ = c_max · L`, with `L > 0` ⇒ `foot < c_max`.
    -- (`hfooteq`'s distance factor is `dist s t`, folded to `L` by the `set`s.)
    have hfL : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p * L < c_max * L := by
      rw [hc_maxL]; linarith [hdv, hfooteq]
    exact lt_of_mul_lt_mul_right hfL hLpos.le
  have hSrcSliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2) := by
    intro c hc
    obtain ⟨hc0, hclt⟩ := hc
    show c * L < ρval + min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2)
    have hcLlt : c * L < ρval + δ₀ := by
      have := mul_lt_mul_of_pos_right hclt hLpos; rwa [hc_maxL] at this
    rcases lt_or_ge (c * L) ρval with hcase | hcase
    · -- inner slices: `c·L ≤ ρval < ρval + min(...)` (min > 0 from `hSrcRpos`).
      have hmin0 : (0 : ℝ) < min δ₀
          (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) := by
        refine lt_min hδ₀pos ?_
        have hRp := hSrcRpos c ⟨hc0, lt_trans hclt hc_maxlt1⟩
        linarith [hRp]
      linarith [hcase, hmin0]
    · -- outer slices: `c·L - ρval < δ₀` and `≤ mR/2 ≤ infDist/2`, so within `min(...)`.
      have hcsafe : c ∈ Set.Icc (α / 2) (1 - α / 2) := by
        refine ⟨?_, ?_⟩
        · -- `c·L > ρval > (L)/2 > (α/2)·L`, so `c > α/2`.
          have hρhalf : (α / 2) * L < ρval := by rw [hρval]; nlinarith [hδ₀pos, hLpos, hα]
          have : (α / 2) * L < c * L := by linarith [hcase, hρhalf]
          exact le_of_lt (lt_of_mul_lt_mul_right this hLpos.le)
        · linarith [hclt, hc_max_safe]
      -- depth at the foot-`c` point of the first edge via `hRband_lb`.
      have hmem : liftPlus s t c 0 ∈ β.segCarrier β.firstSeg :=
        ⟨1 - c, c, by linarith [hclt, hc_maxlt1], by linarith [hc0], by ring,
          (liftPlus_zero_eq_affineComb s t c).symm⟩
      have hfootc : footParam s t (liftPlus s t c 0) = c :=
        footParam_liftPlus hts c 0
      have hfootmem : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (liftPlus s t c 0)
          ∈ Set.Icc (α / 2) (1 - α / 2) := by rw [hfootc]; exact hcsafe
      have hdepth : mR ≤ Metric.infDist (liftPlus s t c 0) Rᶜ :=
        hRband_lb (liftPlus s t c 0) hmem hfootmem
      have hmineq : min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) = δ₀ := by
        apply min_eq_left; linarith [hdepth, hδ₀_le3]
      rw [hmineq]; exact hcLlt
  have hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
    intro i hi
    have : (i : ℕ) = 0 := hidx i ▸ rfl
    rw [this] at hi
    exact absurd (by have := h1; omega : (0 : ℕ) = β.numSegs - 1) hi
  have htgtdistL : dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) = L := by
    rw [hlast, dist_comm]
  have hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) c_max := by
    intro p hp hd
    have hdv : dist p (β.verts (Fin.last β.numSegs)) < ρval + δ₀ := hd
    have hsegdistL : dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) = L := by
      rw [dist_comm]; exact htgtdistL
    have hdL : dist p (β.verts (Fin.last β.numSegs)) <
        dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) := by
      rw [hsegdistL]; linarith [hdv, hρNear, hδ₀pos]
    obtain ⟨hpseg, hfootpos, hfooteq⟩ := hTgtNear_L p hp hdL
    refine ⟨hpseg, hfootpos, ?_⟩
    rw [htgtdistL] at hfooteq
    have hfL : footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p * L < c_max * L := by
      rw [hc_maxL]; linarith [hdv, hfooteq]
    exact lt_of_mul_lt_mul_right hfL hLpos.le
  have hTgtSliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2) := by
    intro c hc
    obtain ⟨hc0, hclt⟩ := hc
    rw [htgtdistL]
    show c * L < ρval + min δ₀
      (Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)
    have hcLlt : c * L < ρval + δ₀ := by
      have := mul_lt_mul_of_pos_right hclt hLpos; rwa [hc_maxL] at this
    rcases lt_or_ge (c * L) ρval with hcase | hcase
    · have hmin0 : (0 : ℝ) < min δ₀
          (Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2) := by
        refine lt_min hδ₀pos ?_
        have hRp := hTgtRpos c ⟨hc0, lt_trans hclt hc_maxlt1⟩
        linarith [hRp]
      linarith [hcase, hmin0]
    · -- outer slices: depth via `hRband_lb` on the reversed-edge foot point.
      have hcsafe1 : α / 2 ≤ c := by
        have hρhalf : (α / 2) * L < ρval := by rw [hρval]; nlinarith [hδ₀pos, hLpos, hα]
        have : (α / 2) * L < c * L := by linarith [hcase, hρhalf]
        exact le_of_lt (lt_of_mul_lt_mul_right this hLpos.le)
      have hcsafe2 : c ≤ 1 - α / 2 := by linarith [hclt, hc_max_safe]
      -- `liftPlus (segTgt lastSeg) (segSrc lastSeg) c 0` is the foot-`(1-c)` point of the
      -- forward edge `s→t`, hence its forward foot `1-c ∈ [α/2, 1-α/2]` lets `hRband_lb` apply.
      have hpt_eq : liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
          = liftPlus s t (1 - c) 0 := by
        rw [liftPlus_zero_eq_affineComb, liftPlus_zero_eq_affineComb, hlast,
          show (1 : ℝ) - (1 - c) = c from by ring, add_comm]
      have hmem' : liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
          ∈ β.segCarrier β.firstSeg := by
        rw [hpt_eq]
        exact ⟨1 - (1 - c), 1 - c, by linarith [hc0], by linarith [hclt, hc_maxlt1], by ring,
          (liftPlus_zero_eq_affineComb s t (1 - c)).symm⟩
      have hfootmem : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
          ∈ Set.Icc (α / 2) (1 - α / 2) := by
        rw [hpt_eq, footParam_liftPlus hts (1 - c) 0]
        exact ⟨by linarith [hcsafe2], by linarith [hcsafe1]⟩
      have hdepth : mR ≤ Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ :=
        hRband_lb _ hmem' hfootmem
      have hmineq : min δ₀
          (Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)
          = δ₀ := by
        apply min_eq_left; linarith [hdepth, hδ₀_le3]
      rw [hmineq]; exact hcLlt
  -- Restrict the caller's `Ioo 0 1` spine/depth data to the internal slice range
  -- `Ioo 0 c_max ⊆ Ioo 0 1` (since `c_max < 1`).
  have hsub : Set.Ioo (0 : ℝ) c_max ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Ioo_subset_Ioo le_rfl hc_maxlt1.le
  have hSrcSpine' : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S :=
    fun c hc => hSrcSpine c (hsub hc)
  have hSrcRpos' : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ :=
    fun c hc => hSrcRpos c (hsub hc)
  have hTgtSpine' : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S :=
    fun c hc => hTgtSpine c (hsub hc)
  have hTgtRpos' : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ :=
    fun c hc => hTgtRpos c (hsub hc)
  -- `P5` (preconnectedness) of each collar side, via the `sorry`-free sliver-budget
  -- collar theorems in `PolygonalArc` (no dependence on the sorried union lemma).
  have hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ) :=
    isPreconnected_collarPlus_of_sliver_budgets β R S ρ hturn hδ₀pos hα hα3 hα1
      hsectorWPlus (le_refl δ₀) hsep hadj_tgt hadj_src hsmall hSband' hRband hsrc htgt
      hSrcSep hSrcSpine' hSrcNear hρpos hSrcRpos' hSrcSliver hTgtSep hTgtSpine' hTgtNear
      hρpos hTgtRpos' hTgtSliver
  have hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ) :=
    isPreconnected_collarMinus_of_sliver_budgets β R S ρ hturn hδ₀pos hα hα3 hα1
      hsectorWMinus (le_refl δ₀) hsep hadj_tgt hadj_src hsmall hSband' hRband hsrc htgt
      hSrcSep hSrcSpine' hSrcNear hρpos hSrcRpos' hSrcSliver hTgtSep hTgtSpine' hTgtNear
      hρpos hTgtRpos' hTgtSliver
  -- Feed the `sorry`-free single-segment entry point.
  exact exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_with_collar_sides_of_numSegs_one
    β h1 ρ hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ₀pos hα hα2 hmS hmR
    hband hsrc htgt hballSrc hballTgt hdisj hTp_pre hTm_pre (hcover δ₀ hδ₀pos)

/-- **Lower bound on the distance to the complement of an open ball.**
For any `x` in a metric space, `r - dist x c ≤ infDist x (ball c r)ᶜ`.  Reason:
for any `z ∉ ball c r` we have `dist z c ≥ r`, and the triangle inequality gives
`dist z c ≤ dist z x + dist x c`, so `dist x z ≥ r - dist x c`. -/
private theorem infDist_ball_compl_lb {X : Type*} [MetricSpace X] (c : X) (r : ℝ)
    (x : X) (hne : (Metric.ball c r)ᶜ.Nonempty) :
    r - dist x c ≤ Metric.infDist x (Metric.ball c r)ᶜ := by
  rw [Metric.le_infDist hne]
  intro z hz
  have hzc : r ≤ dist z c := by
    rw [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hz; exact hz
  have htri : dist z c ≤ dist z x + dist x c := dist_triangle z x c
  rw [dist_comm x z]
  linarith

/-- **Obligation A: region construction + collar for a prefix-step straight arc.**
Builds the open ball `R = ball ((p₁+p₂)/2) (‖p₁p₂‖/2)` around the segment `p₁p₂`
— a simply-connected (convex) neighborhood of the open segment whose boundary
passes through both endpoints, so `p₁, p₂ ∉ R` — then applies the already-proved
`exists_twoSidedPartition_of_straightArc` to obtain a two-sided partition `U, V`
of the arc-complement.  The spine `S` is the whole open segment, and the collar
hypotheses are discharged exactly as in `exists_twoSidedPartition_unitSegment`,
with the `infDist`-to-`Rᶜ` bounds coming from `infDist_ball_compl_lb`. -/
theorem exists_twoSidedPartition_prefixStep
    (p₁ p₂ : ℝ × ℝ) (hne : p₁ ≠ p₂) :
    ∃ (R U V : Set (ℝ × ℝ)),
      IsOpen R ∧ IsSimplyConnected R ∧ p₁ ∈ Rᶜ ∧ p₂ ∈ Rᶜ ∧
      IsTwoSidedPartition
        (regionMinusArc R ((straightPolygonalArc p₁ p₂ hne).toSimpleArc)) U V := by
  classical
  set β := straightPolygonalArc p₁ p₂ hne with hβ
  have hβnum : β.numSegs = 1 := by rw [hβ]; simp [straightPolygonalArc]
  have hLpos : 0 < dist p₁ p₂ := dist_pos.mpr hne
  -- Segment data for the unique edge (mirrors `exists_twoSidedPartition_unitSegment`).
  have hverts0 : β.verts 0 = p₁ := by rw [hβ]; simp [straightPolygonalArc]
  have hvertsLast : β.verts (Fin.last β.numSegs) = p₂ := by
    show (straightPolygonalArc p₁ p₂ hne).verts
        (Fin.last (straightPolygonalArc p₁ p₂ hne).numSegs) = _
    simp [straightPolygonalArc, Fin.last]
  have hsrc : β.segSrc β.firstSeg = p₁ := by
    rw [hβ]; simp [straightPolygonalArc, PolygonalArc.segSrc, PolygonalArc.firstSeg, Fin.castSucc]
  have htgt : β.segTgt β.firstSeg = p₂ := by
    rw [hβ]; simp [straightPolygonalArc, PolygonalArc.segTgt, PolygonalArc.firstSeg, Fin.succ]
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolygonalArc.lastSeg, PolygonalArc.firstSeg, hβnum]
  have hsrcLast : β.segSrc β.lastSeg = p₁ := by rw [hlast]; exact hsrc
  have htgtLast : β.segTgt β.lastSeg = p₂ := by rw [hlast]; exact htgt
  have hcarr : β.carrier = segment ℝ p₁ p₂ := by
    rw [hβ]; exact straightPolygonalArc_carrier _ _ hne
  have hsegCarr : β.segCarrier β.firstSeg = segment ℝ p₁ p₂ := by
    rw [PolygonalArc.segCarrier, hsrc, htgt]
  have hsegCarrLast : β.segCarrier β.lastSeg = segment ℝ p₁ p₂ := by
    rw [hlast]; exact hsegCarr
  -- Region = open ball about the segment midpoint; spine = whole open segment.
  set c₀ : ℝ × ℝ := (1/2 : ℝ) • p₁ + (1/2 : ℝ) • p₂ with hc₀
  set R : Set (ℝ × ℝ) := Metric.ball c₀ (dist p₁ p₂ / 2) with hR_def
  set S : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | ∃ c : ℝ, c ∈ Set.Ioo (0:ℝ) 1 ∧ q = (1 - c) • p₁ + c • p₂} with hS_def
  set α : ℝ := 1/6 with hα_def
  set mR : ℝ := dist p₁ p₂ / 12 with hmR_def
  have hα_pos : (0:ℝ) < α := by rw [hα_def]; norm_num
  have hα_lt_third : α < 1/3 := by rw [hα_def]; norm_num
  have hmR_pos : 0 < mR := by rw [hmR_def]; positivity
  -- Geometry helpers: distances from a segment point to the center / endpoints.
  have hnv : ‖p₂ - p₁‖ = dist p₁ p₂ := by rw [← dist_eq_norm, dist_comm]
  have hsub_center : ∀ c : ℝ,
      ((1 - c) • p₁ + c • p₂) - c₀ = (c - 1/2) • (p₂ - p₁) := by
    intro c; rw [hc₀]; module
  have hdist_mid : ∀ c : ℝ,
      dist ((1 - c) • p₁ + c • p₂) c₀ = |c - 1/2| * dist p₁ p₂ := by
    intro c
    rw [dist_eq_norm, hsub_center c, norm_smul, Real.norm_eq_abs, hnv]
  have hdist_src : ∀ c : ℝ,
      dist ((1 - c) • p₁ + c • p₂) p₁ = |c| * dist p₁ p₂ := by
    intro c
    rw [dist_eq_norm, show (1 - c) • p₁ + c • p₂ - p₁ = c • (p₂ - p₁) by module,
      norm_smul, Real.norm_eq_abs, hnv]
  have hdist_p₁ : dist p₁ c₀ = dist p₁ p₂ / 2 := by
    rw [dist_eq_norm, hc₀,
      show p₁ - ((1/2:ℝ) • p₁ + (1/2:ℝ) • p₂) = (1/2:ℝ) • (p₁ - p₂) by module,
      norm_smul, Real.norm_eq_abs, show |(1/2:ℝ)| = 1/2 from by norm_num,
      show ‖p₁ - p₂‖ = dist p₁ p₂ from by rw [dist_eq_norm]]
    ring
  have hdist_p₂ : dist p₂ c₀ = dist p₁ p₂ / 2 := by
    rw [dist_eq_norm, hc₀,
      show p₂ - ((1/2:ℝ) • p₁ + (1/2:ℝ) • p₂) = (1/2:ℝ) • (p₂ - p₁) by module,
      norm_smul, Real.norm_eq_abs, show |(1/2:ℝ)| = 1/2 from by norm_num, hnv]
    ring
  have hmemR : ∀ c : ℝ,
      ((1 - c) • p₁ + c • p₂) ∈ R ↔ |c - 1/2| < 1/2 := by
    intro c
    rw [hR_def, Metric.mem_ball, hdist_mid c]
    constructor
    · intro h; nlinarith [h, hLpos, abs_nonneg (c - 1/2)]
    · intro h; nlinarith [h, hLpos, abs_nonneg (c - 1/2)]
  -- Orientation facts for `footParam`.
  have hts : p₂ ≠ p₁ := Ne.symm hne
  have hst : p₁ ≠ p₂ := hne
  have hfoot_c : ∀ c : ℝ, footParam p₁ p₂ ((1 - c) • p₁ + c • p₂) = c := fun c =>
    footParam_affineComb hts c
  have hfoot_tgt : ∀ c : ℝ, footParam p₂ p₁ ((1 - c) • p₁ + c • p₂) = 1 - c := by
    intro c
    have h := footParam_affineComb hst (1 - c)
    rw [show (1 - (1 - c)) • p₂ + (1 - c) • p₁ = (1 - c) • p₁ + c • p₂ by module] at h
    exact h
  -- Spine helpers.
  have hSpt : ∀ c : ℝ, c ∈ Set.Ioo (0:ℝ) 1 → ((1 - c) • p₁ + c • p₂) ∈ S :=
    fun c hc => ⟨c, hc, rfl⟩
  have hmem_seg : ∀ y : ℝ × ℝ, y ∈ segment ℝ p₁ p₂ →
      ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧ y = (1 - b) • p₁ + b • p₂ := by
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    exact ⟨b, hb, by linarith, by rw [show a = 1 - b by linarith]⟩
  have hseg_of_mem : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      ((1 - c) • p₁ + c • p₂) ∈ segment ℝ p₁ p₂ :=
    fun c hc0 hc1 => ⟨1 - c, c, by linarith, hc0, by ring, rfl⟩
  -- ============ IsOpen R, endpoints in Rᶜ ============
  have hR : IsOpen R := by rw [hR_def]; exact Metric.isOpen_ball
  have hsrc0 : β.verts 0 ∈ Rᶜ := by
    rw [hverts0, Set.mem_compl_iff, hR_def, Metric.mem_ball, hdist_p₁]
    exact lt_irrefl _
  have hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ := by
    rw [hvertsLast, Set.mem_compl_iff, hR_def, Metric.mem_ball, hdist_p₂]
    exact lt_irrefl _
  have hRcne : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  -- ============ IsSimplyConnected R ============
  have hRsc : IsSimplyConnected R := by
    have hC : ContractibleSpace R :=
      (convex_ball c₀ (dist p₁ p₂ / 2)).contractibleSpace
        ⟨c₀, by rw [Metric.mem_ball, dist_self]; linarith⟩
    exact SimplyConnectedSpace.ofContractible _
  -- ============ S ⊆ R, preconnected, ⊆ carrier, midpoint ============
  have hSR : S ⊆ R := by
    rintro q ⟨c, hc, rfl⟩
    rw [hmemR c, abs_lt]
    rcases hc with ⟨hc0, hc1⟩
    constructor <;> linarith
  have hSpre : IsPreconnected S := by
    have himg : S = (fun c : ℝ => (1 - c) • p₁ + c • p₂) '' Set.Ioo 0 1 := by
      ext q; constructor
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    rw [himg]; exact isPreconnected_Ioo.image _ (by fun_prop)
  have hS_carrier : S ⊆ β.carrier := by
    rw [hcarr]; rintro q ⟨c, hc, rfl⟩
    exact hseg_of_mem c (le_of_lt hc.1) (le_of_lt hc.2)
  have hmS : firstMid β ∈ S := by
    refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [firstMid, hsrc, htgt]
    ext <;> simp <;> ring
  -- ============ hSband ============
  have hSband : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Ioo (0 : ℝ) 1 →
      y ∈ S := by
    intro y hy hfoot
    rw [hsegCarr] at hy
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg y hy
    rw [hsrc, htgt, hfoot_c b] at hfoot
    exact hSpt b hfoot
  -- ============ hRband_lb (was `sorry`; now via `infDist_ball_compl_lb`) ============
  have hRband_lb : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈
        Set.Icc (α / 2) (1 - α / 2) →
      mR ≤ Metric.infDist y Rᶜ := by
    intro y hy hfoot
    rw [hsegCarr] at hy
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg y hy
    rw [hsrc, htgt, hfoot_c b] at hfoot
    rcases hfoot with ⟨hflo, hfhi⟩
    rw [hα_def] at hflo hfhi
    have hlb := infDist_ball_compl_lb c₀ (dist p₁ p₂ / 2) ((1 - b) • p₁ + b • p₂)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_mid b] at hlb
    have habs : |b - 1/2| ≤ 5/12 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hmR_def, hR_def]
    nlinarith [hlb, mul_le_mul_of_nonneg_right habs (le_of_lt hLpos), hLpos]
  -- ============ hSrcSpine ============
  have hSrcSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S := by
    intro c hc
    rw [hsrc, htgt, liftPlus_zero_eq_affineComb]
    exact hSpt c hc
  -- ============ hSrcNear_L ============
  have hSrcNear_L : ∀ p ∈ S,
      dist p (β.verts 0) < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) →
      p ∈ β.segCarrier β.firstSeg ∧
        0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∧
        dist p (β.verts 0) =
          footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p *
            dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    rintro p ⟨c, hc, rfl⟩ _
    rw [hsrc, htgt, hsegCarr, hverts0]
    refine ⟨hseg_of_mem c (le_of_lt hc.1) (le_of_lt hc.2), ?_, ?_⟩
    · rw [hfoot_c c]; exact hc.1
    · rw [hfoot_c c, hdist_src c, abs_of_pos hc.1]
  -- ============ hSrcRpos ============
  have hSrcRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ := by
    intro c hc
    rw [hsrc, htgt, liftPlus_zero_eq_affineComb]
    have hlb := infDist_ball_compl_lb c₀ (dist p₁ p₂ / 2) ((1 - c) • p₁ + c • p₂)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_mid c] at hlb
    have habs : |c - 1/2| < 1/2 := abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
    rw [hR_def]
    nlinarith [hlb, mul_lt_mul_of_pos_right habs hLpos]
  -- ============ hTgtSpine ============
  have hTgtSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S := by
    intro c hc
    rw [htgtLast, hsrcLast, liftPlus_zero_eq_affineComb,
      show (1 - c) • p₂ + c • p₁ = (1 - (1 - c)) • p₁ + (1 - c) • p₂ by module]
    exact hSpt (1 - c) ⟨by linarith [hc.2], by linarith [hc.1]⟩
  -- ============ hTgtNear_L ============
  have hTgtNear_L : ∀ p ∈ S,
      dist p (β.verts (Fin.last β.numSegs)) <
          dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) →
      p ∈ β.segCarrier β.lastSeg ∧
        0 < footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∧
        dist p (β.verts (Fin.last β.numSegs)) =
          footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p *
            dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) := by
    rintro p ⟨c, hc, rfl⟩ _
    rw [hsrcLast, htgtLast, hvertsLast, hsegCarrLast]
    refine ⟨hseg_of_mem c (le_of_lt hc.1) (le_of_lt hc.2), ?_, ?_⟩
    · rw [hfoot_tgt c]; linarith [hc.2]
    · rw [hfoot_tgt c, dist_affineComb_tgt (show (1 - c) + c = 1 by ring),
        abs_of_nonneg (show (0:ℝ) ≤ 1 - c by linarith [hc.2]), dist_comm p₂ p₁]
  -- ============ hTgtRpos ============
  have hTgtRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ := by
    intro c hc
    rw [htgtLast, hsrcLast, liftPlus_zero_eq_affineComb,
      show (1 - c) • p₂ + c • p₁ = (1 - (1 - c)) • p₁ + (1 - c) • p₂ by module]
    have hlb := infDist_ball_compl_lb c₀ (dist p₁ p₂ / 2)
      ((1 - (1 - c)) • p₁ + (1 - c) • p₂)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_mid (1 - c)] at hlb
    have habs : |(1 - c) - 1/2| < 1/2 := abs_lt.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
    rw [hR_def]
    nlinarith [hlb, mul_lt_mul_of_pos_right habs hLpos]
  -- ============ hcover ============
  have hcover : ∀ δ₀ : ℝ, 0 < δ₀ → R ∩ β.carrier ⊆ taperedTube R S δ₀ := by
    intro δ₀ hδ₀ z hz
    obtain ⟨hzR, hzC⟩ := hz
    rw [hcarr] at hzC
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg z hzC
    rw [hmemR b, abs_lt] at hzR
    have hzS : ((1 - b) • p₁ + b • p₂) ∈ S :=
      hSpt b ⟨by linarith [hzR.1], by linarith [hzR.2]⟩
    exact subset_taperedTube hR (by rw [hR_def] at hRcne; exact hRcne) hδ₀ hSR hzS
  -- ============ Assemble and apply ============
  obtain ⟨U, V, hpart⟩ :=
    exists_twoSidedPartition_of_straightArc β hβnum
      hα_pos hα_lt_third hmR_pos
      hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hmS hSband hRband_lb
      hSrcSpine hSrcNear_L hSrcRpos hTgtSpine hTgtNear_L hTgtRpos hcover
  exact ⟨R, U, V, hR, hRsc, hverts0 ▸ hsrc0, hvertsLast ▸ hsrcL, hpart⟩

/-- **Witness that `exists_twoSidedPartition_of_straightArc` is non-vacuous.**

For the concrete unit segment `[(0,0),(1,0)]`, the open sup-ball
`R = ball ((1/2,0)) (1/2)` (the open unit square `(0,1)×(-1/2,1/2)`) together with
the whole open segment as the spine `S` satisfies every collar hypothesis of
`exists_twoSidedPartition_of_straightArc`, so the two-sided partition of the
arc-complement exists. -/
theorem exists_twoSidedPartition_unitSegment :
    ∃ U V, IsTwoSidedPartition
      (regionMinusArc (Metric.ball ((1/2, 0) : ℝ × ℝ) (1/2))
        (straightPolygonalArc ((0,0) : ℝ × ℝ) ((1,0) : ℝ × ℝ)
          (by simp : ((0,0):ℝ×ℝ) ≠ (1,0))).toSimpleArc)
      U V := by
  classical
  -- The straight one-segment arc and its computed segment data.
  have hne : ((0,0):ℝ×ℝ) ≠ (1,0) := by simp
  let β := straightPolygonalArc ((0,0) : ℝ × ℝ) ((1,0) : ℝ × ℝ) hne
  have hβ : β = straightPolygonalArc ((0,0) : ℝ × ℝ) ((1,0) : ℝ × ℝ) hne := rfl
  have hβnum : β.numSegs = 1 := by rw [hβ]; simp [straightPolygonalArc]
  have hv0 : β.verts 0 = ((0,0) : ℝ × ℝ) := by
    rw [hβ]; simp [straightPolygonalArc]
  have hvL : β.verts (Fin.last β.numSegs) = ((1,0) : ℝ × ℝ) := by
    show (straightPolygonalArc ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) hne).verts
        (Fin.last (straightPolygonalArc ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) hne).numSegs) = _
    simp [straightPolygonalArc, Fin.last]
  have hsrc : β.segSrc β.firstSeg = ((0,0) : ℝ × ℝ) := by
    rw [hβ]; simp [straightPolygonalArc, PolygonalArc.segSrc, PolygonalArc.firstSeg, Fin.castSucc]
  have htgt : β.segTgt β.firstSeg = ((1,0) : ℝ × ℝ) := by
    rw [hβ]; simp [straightPolygonalArc, PolygonalArc.segTgt, PolygonalArc.firstSeg, Fin.succ]
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolygonalArc.lastSeg, PolygonalArc.firstSeg, hβnum]
  have hsrcLast : β.segSrc β.lastSeg = ((0,0) : ℝ × ℝ) := by rw [hlast]; exact hsrc
  have htgtLast : β.segTgt β.lastSeg = ((1,0) : ℝ × ℝ) := by rw [hlast]; exact htgt
  have hcarr : β.carrier = segment ℝ ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) := by
    rw [hβ]; exact straightPolygonalArc_carrier _ _ hne
  -- The region (open sup-ball = open unit square) and the spine (whole open segment).
  set R : Set (ℝ × ℝ) := Metric.ball ((1/2, 0) : ℝ × ℝ) (1/2) with hR_def
  set S : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | ∃ c : ℝ, c ∈ Set.Ioo (0:ℝ) 1 ∧
      q = ((1 - c) • ((0,0):ℝ×ℝ) + c • ((1,0):ℝ×ℝ))} with hS_def
  set α : ℝ := 1/6 with hα_def
  set mR : ℝ := 1/12 with hmR_def
  -- A segment point `(1-c)•(0,0)+c•(1,0)` equals `(c,0)`.
  have hpt : ∀ c : ℝ, ((1 - c) • ((0,0):ℝ×ℝ) + c • ((1,0):ℝ×ℝ)) = (c, 0) := by
    intro c; ext <;> simp
  -- `dist (c,0) (1/2,0) = |c - 1/2|`.
  have hdist_c : ∀ c : ℝ, dist ((c, 0) : ℝ × ℝ) ((1/2, 0) : ℝ × ℝ) = |c - 1/2| := by
    intro c
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp [abs_nonneg]
  -- `(c,0) ∈ R ↔ |c - 1/2| < 1/2`.
  have hmemR : ∀ c : ℝ, ((c, 0) : ℝ × ℝ) ∈ R ↔ |c - 1/2| < 1/2 := by
    intro c; rw [hR_def, Metric.mem_ball, hdist_c]
  -- Orientation facts for `footParam`.
  have hts : ((1,0):ℝ×ℝ) ≠ ((0,0):ℝ×ℝ) := by simp
  have hst : ((0,0):ℝ×ℝ) ≠ ((1,0):ℝ×ℝ) := hne
  -- The unique edge's carrier is the closed segment `[(0,0),(1,0)]`.
  have hsegCarr : β.segCarrier β.firstSeg = segment ℝ ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) := by
    rw [PolygonalArc.segCarrier, hsrc, htgt]
  -- `Rᶜ` is nonempty (the source endpoint lies in it).
  have hsrc0 : β.verts 0 ∈ Rᶜ := by
    rw [hv0, Set.mem_compl_iff]
    have : ((0,0):ℝ×ℝ) = ((0:ℝ), (0:ℝ)) := rfl
    rw [show ((0,0):ℝ×ℝ) = (((0:ℝ)), (0:ℝ)) from rfl, hmemR 0]
    norm_num
  have hRcne : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  -- `(c,0)` is in the closed segment when `c ∈ [0,1]`.
  have hseg_of_mem : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      ((c, 0) : ℝ × ℝ) ∈ segment ℝ ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) := by
    intro c hc0 hc1
    refine ⟨1 - c, c, by linarith, hc0, by ring, ?_⟩
    rw [hpt c]
  -- Inverse: any point of the closed segment is `(b,0)` for some `b ∈ [0,1]`.
  have hmem_seg : ∀ y : ℝ × ℝ, y ∈ segment ℝ ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) →
      ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧ y = (b, 0) := by
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    exact ⟨b, hb, by linarith, by ext <;> simp⟩
  -- A spine point `(c,0)`, `c ∈ (0,1)`, is in `S`.
  have hSpt : ∀ c : ℝ, c ∈ Set.Ioo (0:ℝ) 1 → ((c, 0) : ℝ × ℝ) ∈ S := by
    intro c hc; exact ⟨c, hc, by rw [hpt c]⟩
  -- footParam of a segment point `(c,0)` is `c`.
  have hfoot_c : ∀ c : ℝ,
      footParam ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) ((c, 0) : ℝ × ℝ) = c := by
    intro c
    have := footParam_affineComb hts c
    rw [hpt c] at this; exact this
  -- ============ H3: IsOpen R ============
  have hR : IsOpen R := Metric.isOpen_ball
  -- ============ H4: IsSimplyConnected R ============
  have hRsc : IsSimplyConnected R := by
    have hC : ContractibleSpace R :=
      (convex_ball ((1/2,0):ℝ×ℝ) (1/2)).contractibleSpace ⟨(1/2,0), by simp [Metric.mem_ball]⟩
    exact SimplyConnectedSpace.ofContractible _
  -- ============ H5,H6: endpoints in Rᶜ ============
  have hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ := by
    rw [hvL, Set.mem_compl_iff, show ((1,0):ℝ×ℝ) = (((1:ℝ)), (0:ℝ)) from rfl, hmemR 1]
    norm_num
  -- ============ H7: S ⊆ R ============
  have hSR : S ⊆ R := by
    rintro q ⟨c, hc, rfl⟩
    rw [hpt c, hmemR c]
    rcases hc with ⟨hc0, hc1⟩
    rw [abs_lt]; constructor <;> linarith
  -- ============ H8: IsPreconnected S ============
  have hSpre : IsPreconnected S := by
    have himg : S = (fun c : ℝ => ((1 - c) • ((0,0):ℝ×ℝ) + c • ((1,0):ℝ×ℝ))) '' Set.Ioo 0 1 := by
      ext q; constructor
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    rw [himg]
    exact isPreconnected_Ioo.image _ (by fun_prop)
  -- ============ H9: S ⊆ β.carrier ============
  have hS_carrier : S ⊆ β.carrier := by
    rw [hcarr]
    rintro q ⟨c, hc, rfl⟩
    exact ⟨1 - c, c, by linarith [hc.1, hc.2], le_of_lt hc.1, by ring, rfl⟩
  -- ============ H10: firstMid β ∈ S ============
  have hmS : firstMid β ∈ S := by
    have hmid : firstMid β = ((1/2 : ℝ), (0:ℝ)) := by
      rw [firstMid, hsrc, htgt]; norm_num
    rw [hmid]
    exact hSpt (1/2) ⟨by norm_num, by norm_num⟩
  -- ============ H11: hSband ============
  have hSband : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S := by
    intro y hy hfoot
    rw [hsegCarr] at hy
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg y hy
    rw [hsrc, htgt, hfoot_c b] at hfoot
    exact hSpt b hfoot
  -- ============ H12: hRband_lb ============
  have hRband_lb : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      mR ≤ Metric.infDist y Rᶜ := by
    intro y hy hfoot
    rw [hsegCarr] at hy
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg y hy
    rw [hsrc, htgt, hfoot_c b] at hfoot
    rcases hfoot with ⟨hflo, hfhi⟩
    -- α/2 = 1/12, 1 - α/2 = 11/12, so b ∈ [1/12, 11/12].
    have hblo : (1/12 : ℝ) ≤ b := by rw [hα_def] at hflo; linarith
    have hbhi : b ≤ (11/12 : ℝ) := by rw [hα_def] at hfhi; linarith
    have hlb := infDist_ball_compl_lb ((1/2,0):ℝ×ℝ) (1/2) ((b,0):ℝ×ℝ)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_c b] at hlb
    -- |b - 1/2| ≤ 5/12, so 1/2 - |b - 1/2| ≥ 1/12.
    have habs : |b - 1/2| ≤ 5/12 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hmR_def, hR_def]; linarith [hlb, habs]
  -- ============ H13: hSrcSpine ============
  have hSrcSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S := by
    intro c hc
    rw [hsrc, htgt, liftPlus_zero_eq_affineComb, hpt c]
    exact hSpt c hc
  -- ============ H14: hSrcNear_L ============
  have hSrcNear_L : ∀ p ∈ S,
      dist p (β.verts 0) < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) →
      p ∈ β.segCarrier β.firstSeg ∧
        0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∧
        dist p (β.verts 0) =
          footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p *
            dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    rintro p ⟨c, hc, rfl⟩ _
    rw [hpt c, hsrc, htgt, hsegCarr, hv0]
    refine ⟨hseg_of_mem c (le_of_lt hc.1) (le_of_lt hc.2), ?_, ?_⟩
    · rw [hfoot_c c]; exact hc.1
    · rw [hfoot_c c]
      -- dist (c,0) (0,0) = |c| = c ; dist (0,0) (1,0) = 1 ; c = c * 1.
      have hd1 : dist ((c,0):ℝ×ℝ) ((0,0):ℝ×ℝ) = c := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [sub_zero, abs_zero]
        rw [max_eq_left (abs_nonneg c), abs_of_pos hc.1]
      have hd2 : dist ((0,0):ℝ×ℝ) ((1,0):ℝ×ℝ) = 1 := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; norm_num
      rw [hd1, hd2]; ring
  -- ============ H15: hSrcRpos ============
  have hSrcRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ := by
    intro c hc
    rw [hsrc, htgt, liftPlus_zero_eq_affineComb, hpt c]
    have hlb := infDist_ball_compl_lb ((1/2,0):ℝ×ℝ) (1/2) ((c,0):ℝ×ℝ)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_c c] at hlb
    have habs : |c - 1/2| < 1/2 := abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
    rw [hR_def]; linarith [hlb, habs]
  -- Target-edge helpers: the reversed affine combination `(1-c)•(1,0)+c•(0,0) = (1-c,0)`.
  have hpt' : ∀ c : ℝ, ((1 - c) • ((1,0):ℝ×ℝ) + c • ((0,0):ℝ×ℝ)) = (1 - c, 0) := by
    intro c; ext <;> simp
  have hfoot' : ∀ c : ℝ,
      footParam ((1,0):ℝ×ℝ) ((0,0):ℝ×ℝ) ((1 - c, 0) : ℝ × ℝ) = c := by
    intro c
    have := footParam_affineComb hst c
    rw [hpt' c] at this; exact this
  -- ============ H16: hTgtSpine ============
  have hTgtSpine : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S := by
    intro c hc
    rw [htgtLast, hsrcLast, liftPlus_zero_eq_affineComb, hpt' c]
    -- (1-c, 0) ∈ S with spine param (1-c) ∈ (0,1).
    refine ⟨1 - c, ⟨by linarith [hc.2], by linarith [hc.1]⟩, ?_⟩
    rw [hpt (1 - c)]
  -- ============ H17: hTgtNear_L ============
  have hTgtNear_L : ∀ p ∈ S,
      dist p (β.verts (Fin.last β.numSegs)) <
          dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) →
      p ∈ β.segCarrier β.lastSeg ∧
        0 < footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∧
        dist p (β.verts (Fin.last β.numSegs)) =
          footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p *
            dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) := by
    rintro p ⟨d, hd, rfl⟩ _
    rw [hpt d, hvL, hlast, hsegCarr, htgt, hsrc]
    -- `(d,0) = (1 - (1-d), 0)`, so footParam (1,0) (0,0) (d,0) = 1 - d.
    have hfd : footParam ((1,0):ℝ×ℝ) ((0,0):ℝ×ℝ) ((d, 0) : ℝ × ℝ) = 1 - d := by
      have := hfoot' (1 - d)
      simpa using this
    refine ⟨hseg_of_mem d (le_of_lt hd.1) (le_of_lt hd.2), ?_, ?_⟩
    · rw [hfd]; linarith [hd.2]
    · rw [hfd]
      -- dist (d,0) (1,0) = |d-1| = 1-d ; dist (1,0) (0,0) = 1.
      have hd1 : dist ((d,0):ℝ×ℝ) ((1,0):ℝ×ℝ) = 1 - d := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [sub_self, abs_zero]
        rw [max_eq_left (abs_nonneg _), abs_of_nonpos (by linarith [hd.2])]; ring
      have hd2 : dist ((1,0):ℝ×ℝ) ((0,0):ℝ×ℝ) = 1 := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; norm_num
      rw [hd1, hd2]; ring
  -- ============ H18: hTgtRpos ============
  have hTgtRpos : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ := by
    intro c hc
    rw [htgtLast, hsrcLast, liftPlus_zero_eq_affineComb, hpt' c]
    have hlb := infDist_ball_compl_lb ((1/2,0):ℝ×ℝ) (1/2) ((1 - c,0):ℝ×ℝ)
      (by rw [hR_def] at hRcne; exact hRcne)
    rw [hdist_c (1 - c)] at hlb
    have habs : |(1 - c) - 1/2| < 1/2 := abs_lt.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
    rw [hR_def]; linarith [hlb, habs]
  -- ============ H19: hcover ============
  have hcover : ∀ δ₀ : ℝ, 0 < δ₀ → R ∩ β.carrier ⊆ taperedTube R S δ₀ := by
    intro δ₀ hδ₀ z hz
    obtain ⟨hzR, hzC⟩ := hz
    rw [hcarr] at hzC
    obtain ⟨b, hb0, hb1, rfl⟩ := hmem_seg z hzC
    -- z = (b,0) ∈ R forces b ∈ (0,1), hence z ∈ S; then z ∈ taperedTube.
    rw [hmemR b, abs_lt] at hzR
    have hzS : ((b, 0) : ℝ × ℝ) ∈ S := hSpt b ⟨by linarith [hzR.1], by linarith [hzR.2]⟩
    exact subset_taperedTube hR (by rw [hR_def] at hRcne; exact hRcne) hδ₀ hSR hzS
  -- ============ Assemble and apply ============
  obtain ⟨U, V, hpart⟩ :=
    exists_twoSidedPartition_of_straightArc β hβnum
      (show (0:ℝ) < α by rw [hα_def]; norm_num)
      (show α < 1 / 3 by rw [hα_def]; norm_num)
      (show (0:ℝ) < mR by rw [hmR_def]; norm_num)
      hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hmS hSband hRband_lb
      hSrcSpine hSrcNear_L hSrcRpos hTgtSpine hTgtNear_L hTgtRpos hcover
  exact ⟨U, V, hpart⟩

end CrossingLemma.PlaneArcSeparation
