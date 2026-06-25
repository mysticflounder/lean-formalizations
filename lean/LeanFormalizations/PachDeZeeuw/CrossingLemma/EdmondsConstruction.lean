/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RegionFaceBridge

/-!
# Concrete Edmonds-compatible assignment via prefix induction (Track A, Target 1)

This file builds the **combinatorial iteration** of the region↔face bridge: it
assembles an `EdmondsCompatible` dart→region assignment for every prefix
`G.prefixEdges n` of the drawing, by induction on the insertion order, from

* a single-face **base** (the spanning-tree prefix, `card Face = 1`, supplied by
  `DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder`,
  `RM:8990`), and
* one **per-cotree-step crosscut datum** `PrefixStepCrosscutData` per inserted
  edge, whose region-separation transports across the step by the *proven*
  `region_separates_prefixStep_sameFace_concrete` (`RegionFaceBridge.lean`).

The point of this file is the **iteration**: it reduces the global
`EdmondsCompatible.region_separates` clause (a statement over *all* darts of the
full residual map) to the strictly more granular *per-step* crosscut datum — one
cotree edge crosscutting one region — which is exactly what the planar geometry
(`PLCollarSeparation` / `exists_twoSidedPartition_of_polygonalArc`) supplies edge by
edge.  The `Nat.le_induction` harness here mirrors the planarity induction
`residualMap_isPlanar_prefix_of_insertions_from` (`RM:1779`) but carries
region-separation rather than `IsPlanar`.

## What is proved sorry-free here

* `PrefixStepCrosscutData`: the per-cotree-step abstract crosscut hypothesis
  bundle — exactly the inputs of `region_separates_prefixStep_sameFace_concrete`
  minus the predecessor co-faciality (which the induction *derives*) and the
  successor region assignment (which is the supplied region family).
* `regionSeparates_prefix_of_crosscut`: the **iteration** — region-separation at
  every prefix level, proved by `Nat.le_induction` from the card-1 base and the
  per-step crosscut data.  This is the genuine new content: the per-step
  transport is chained to the top.
* `edmondsCompatibleAtPrefix`: packages region-separation together with the
  (abstract) region family `dr`, its complement-component witness `hcomp`, and
  its face-constancy `hconst` into an `EdmondsCompatible` at every prefix level.

## What remains as named geometric obligations

The hypotheses `dr`, `hcomp`, `hconst`, `hcard1`, and `hstep` are the geometric
inputs.  `hcard1` is discharged by `RM:8990` on the spanning-tree prefix; `dr`
is intended to be `fun m hm d => regionAt (G.prefixEdges m hm) R₀ (dartAnchor …
d)`; `hcomp`/`hconst` are direct facts about that assignment; and each
`PrefixStepCrosscutData` is the cotree edge's two-sided partition realised as an
injective `poolRegion` (the concurrent PL-crosscut track, Target 2).  None of
these are imported here, keeping this file on the residual/combinatorial side of
the bridge.

100-char lines.  No new axioms beyond what the imports carry.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion
open CrossingLemma.PlaneArcSeparation

variable (G : DrawnMultigraph)

/-! ## §1  The per-cotree-step abstract crosscut datum

For one ordered prefix step `m → m+1` we package exactly the data consumed by
`region_separates_prefixStep_sameFace_concrete`, *except*:

* the predecessor co-faciality `hsame : facePerm.SameCycle c₁ c₂` — the induction
  **derives** it from the predecessor region-separation applied to `hregion`;
* the successor region assignment `dartRegion'` — supplied externally as the
  region family `drm1 = dr (m+1)`.

The fields `c₁, c₂, hc, hvertex, poolRegion, hinj, hfactor` are precisely the
geometric realisation of "the inserted edge crosscuts the single region whose
two splice corners are `c₁, c₂`, splitting it into the two sides realised
injectively by `poolRegion`". `hregion` is the abstract "both splice corners
face the same region before the crosscut". -/

/-- **Per-cotree-step crosscut datum** for the prefix step `m → m+1`.  The
abstract hypothesis bundle that the planar-geometry track supplies edge by edge;
its region-separation transports across the step via
`region_separates_prefixStep_sameFace_concrete`. -/
structure PrefixStepCrosscutData
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARRm : ArcsRotationRegular (G.prefixEdges m hm))
    (hARRm1 : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (drm1 : (Fin (m + 1) × Bool) → Set (ℝ × ℝ)) where
  /-- The two predecessor splice corners of the inserted edge. -/
  c₁ : Fin m × Bool
  /-- The two predecessor splice corners of the inserted edge. -/
  c₂ : Fin m × Bool
  /-- The corners are distinct. -/
  hc : c₁ ≠ c₂
  /-- **Abstract "same region before the crosscut".**  Both corners face the same
  predecessor region.  (Discharged geometrically: both splice corners lie on the
  closure of the single region the new edge crosscuts.) -/
  hregion : drm c₁ = drm c₂
  /-- The transported vertex-permutation splice identifying the successor residual
  map with the inserted-edge map. -/
  hvertex :
    (prefixStepDartEquiv m).permCongr
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).vertexPerm =
        (residualMap (G.prefixEdges (m + 1) hm') hARRm1).vertexPerm
  /-- The two sides of the crosscut, realised as plane regions on the split-pool
  classes of the inserted-edge face split. -/
  poolRegion :
    ({f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁} ⊕ Fin 2) → Set (ℝ × ℝ)
  /-- The two sides are genuinely distinct regions: `poolRegion` is injective. -/
  hinj : Function.Injective poolRegion
  /-- Each successor dart's region is the plane realisation of its split-pool
  class.  Stated for every co-faciality witness `hsame` (the induction supplies
  the one it derives; the value is independent of the witness by proof
  irrelevance of `SameCycle`). -/
  hfactor : ∀ (hsame : (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle c₁ c₂),
    ∀ d, drm1 d =
      poolRegion (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).Face_mk
          ((prefixStepDartEquiv m).symm d)))

/-! ## §2  The iteration — region-separation at every prefix level

`regionSeparates_prefix_of_crosscut` is the genuine content of Target 1: the
per-step transport (`region_separates_prefixStep_sameFace_concrete`) chained from
the single-face base to every prefix level via `Nat.le_induction`.  The induction
hypothesis is region-separation at level `m`; the step (i) derives the predecessor
co-faciality `hsame` of the inserted edge's corners from it, then (ii) transports
to level `m+1`. -/

/-- **Region-separation at every prefix level (the iteration).**

Given an ambient region `R₀`, a region family `dr` over the prefixes, a single-face
base at `start` (`hcard1`), and one `PrefixStepCrosscutData` per cotree step
(`hstep`), region-separation holds at every prefix level `n ≥ start`: two darts
with the same `dr`-region are `facePerm`-`SameCycle`.

This reduces the global Edmonds direction to the per-step crosscut data; the base
`hcard1` is supplied by the spanning-tree prefix (`RM:8990`). -/
theorem regionSeparates_prefix_of_crosscut
    (start : ℕ)
    (hARR : ∀ (m : ℕ) (hm : m ≤ G.numEdges), ArcsRotationRegular (G.prefixEdges m hm))
    (dr : ∀ (m : ℕ), m ≤ G.numEdges → (Fin m × Bool) → Set (ℝ × ℝ))
    (hcard1 : ∀ hstart : start ≤ G.numEdges,
      Fintype.card (residualMap (G.prefixEdges start hstart) (hARR start hstart)).Face = 1)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
      PrefixStepCrosscutData G m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
        (dr m (Nat.le_of_succ_le hm')) (dr (m + 1) hm'))
    (n : ℕ) (hstartn : start ≤ n) (hn : n ≤ G.numEdges)
    (d₁ d₂ : Fin n × Bool) (hregion : dr n hn d₁ = dr n hn d₂) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).facePerm.SameCycle d₁ d₂ := by
  -- Fully-quantified statement, proved by `Nat.le_induction` from `start`.
  have key : ∀ k, start ≤ k → ∀ (hk : k ≤ G.numEdges) (e₁ e₂ : Fin k × Bool),
      dr k hk e₁ = dr k hk e₂ →
      (residualMap (G.prefixEdges k hk) (hARR k hk)).facePerm.SameCycle e₁ e₂ := by
    intro k hk0
    refine Nat.le_induction ?base ?step k hk0
    · -- Base: the spanning-tree prefix has a single face, so *all* darts are
      -- co-facial — region-separation holds vacuously.
      intro hstartG e₁ e₂ _
      exact facePerm_sameCycle_of_card_face_eq_one (G.prefixEdges start hstartG)
        (hcard1 hstartG) e₁ e₂
    · -- Step: derive predecessor co-faciality `hsame` from the IH, then transport.
      intro m hstartm ih hm' e₁ e₂ hreg
      have data := hstep m hm' hstartm
      have hsame := ih (Nat.le_of_succ_le hm') data.c₁ data.c₂ data.hregion
      exact region_separates_prefixStep_sameFace_concrete G m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
        data.hc hsame data.hvertex (dr (m + 1) hm') data.poolRegion (data.hfactor hsame)
        data.hinj e₁ e₂ hreg
  exact key n hstartn hn d₁ d₂ hregion

/-! ## §3  Packaging into `EdmondsCompatible` at every prefix level

With region-separation in hand, an `EdmondsCompatible` for any prefix is the
region family `dr` plus its two direct geometric facts (`hcomp`: each region is a
genuine complement component; `hconst`: the region is `facePerm`-invariant). -/

/-- **Concrete `EdmondsCompatible` at every prefix level.**  Bundles the abstract
region family `dr` (intended `regionAt ∘ dartAnchor`), its complement-component
witness `hcomp`, its face-constancy `hconst`, and the iterated region-separation
`regionSeparates_prefix_of_crosscut` into an `EdmondsCompatible` for
`G.prefixEdges n`.  At `n = G.numEdges` (after transporting `prefixEdges` to `G`)
this is the Edmonds-compatible assignment for the full residual map. -/
def edmondsCompatibleAtPrefix
    (R₀ : Set (ℝ × ℝ)) (start : ℕ)
    (hARR : ∀ (m : ℕ) (hm : m ≤ G.numEdges), ArcsRotationRegular (G.prefixEdges m hm))
    (dr : ∀ (m : ℕ), m ≤ G.numEdges → (Fin m × Bool) → Set (ℝ × ℝ))
    (hcard1 : ∀ hstart : start ≤ G.numEdges,
      Fintype.card (residualMap (G.prefixEdges start hstart) (hARR start hstart)).Face = 1)
    (hcomp : ∀ (m : ℕ) (hm : m ≤ G.numEdges) (d : Fin m × Bool),
      ∃ p ∈ drawingComplementIn (G.prefixEdges m hm) R₀,
        dr m hm d = regionAt (G.prefixEdges m hm) R₀ p)
    (hconst : ∀ (m : ℕ) (hm : m ≤ G.numEdges) (d : Fin m × Bool),
      dr m hm ((residualMap (G.prefixEdges m hm) (hARR m hm)).facePerm d) = dr m hm d)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
      PrefixStepCrosscutData G m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
        (dr m (Nat.le_of_succ_le hm')) (dr (m + 1) hm'))
    (n : ℕ) (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    EdmondsCompatible (G.prefixEdges n hn) (hARR n hn) R₀ where
  dartRegion := dr n hn
  dartRegion_isComponent := hcomp n hn
  face_constant := hconst n hn
  region_separates := fun d₁ d₂ h =>
    regionSeparates_prefix_of_crosscut G start hARR dr hcard1 hstep n hstartn hn d₁ d₂ h

end CrossingLemma
