/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Foundations

/-!
# Szemerédi–Trotter — Rotation regularity & component setup (shard 2 of 5)

The straight-line incidence drawing has distinct endpoint angles at each vertex
(`straightLineIncidentAnglesDistinct`, raised heartbeat budget) hence is
`ArcsRotationRegular`; the straight-line crossing-free planar-layer definitions;
and the per-component drawing `stComponentDrawing` together with the
prefix-permute vertex-rotation setup.  Imports the `Foundations` shard.
-/

set_option linter.style.longLine false

namespace PachSharir.SzemerediTrotter

open scoped Classical
open CrossingLemma

set_option maxHeartbeats 800000

/-- The straight-line incidence drawing has injective endpoint-angle data at each
vertex, under the standing affine-line hypothesis on `L`. -/
theorem straightLineIncidentAnglesDistinct :
    StraightLineIncidentAnglesDistinct := by
  intro P L hL p hp e₁ he₁ e₂ he₂ hangle
  have he₁' : e₁ ∈ incidentEnds (stMultigraph P L) p := by simpa using he₁
  have he₂' : e₂ ∈ incidentEnds (stMultigraph P L) p := by simpa using he₂
  rcases e₁ with ⟨i₁, b₁⟩
  rcases e₂ with ⟨i₂, b₂⟩
  let ℓ := lineForEdge P L i₁
  have hline : ℓ = lineForEdge P L i₂ := by
    simpa [ℓ] using lineForEdge_eq_of_stMultigraph_incidentAngle_eq P L hL he₁' he₂' hangle
  have hℓ : IsAffineLine ℓ := hL _ (lineForEdge_mem P L i₁)
  have hi_pair :
      ((((allEdges P L)[i₁.val]).1.1, ((allEdges P L)[i₁.val]).1.2) : (ℝ × ℝ) × (ℝ × ℝ))
        ∈ edgesOnLine P ℓ := by
    simpa [ℓ] using allEdges_pair_mem_edgesOnLine_lineForEdge P L i₁
  have hj_pair :
      ((((allEdges P L)[i₂.val]).1.1, ((allEdges P L)[i₂.val]).1.2) : (ℝ × ℝ) × (ℝ × ℝ))
        ∈ edgesOnLine P ℓ := by
    simpa [ℓ, hline] using allEdges_pair_mem_edgesOnLine_lineForEdge P L i₂
  cases b₁ <;> cases b₂
  · have hp₁ : ((allEdges P L)[i₁.val].1).1 = p :=
      incidentEnds_source_eq (P := P) (L := L) (p := p) (i := i₁) he₁'
    have hp₂ : ((allEdges P L)[i₂.val].1).1 = p :=
      incidentEnds_source_eq (P := P) (L := L) (p := p) (i := i₂) he₂'
    have hi' : (p, ((allEdges P L)[i₁.val].1).2) ∈ edgesOnLine P ℓ := by
      simpa [hp₁] using hi_pair
    have hj' : (p, ((allEdges P L)[i₂.val].1).2) ∈ edgesOnLine P ℓ := by
      simpa [hp₂] using hj_pair
    have hq : ((allEdges P L)[i₁.val].1).2 = ((allEdges P L)[i₂.val].1).2 := by
      exact edgesOnLine_source_unique
        (P := P) (ℓ := ℓ)
        (p := p)
        (q₁ := ((allEdges P L)[i₁.val].1).2)
        (q₂ := ((allEdges P L)[i₂.val].1).2)
        hi' hj'
    have hbare : ((allEdges P L)[i₁.val]).1 = ((allEdges P L)[i₂.val]).1 := by
      exact Prod.ext (hp₁.trans hp₂.symm) hq
    have hfull : (allEdges P L)[i₁.val] = (allEdges P L)[i₂.val] := by
      apply PSigma.ext hbare
      exact proof_irrel_heq _ _
    have hidx : i₁ = i₂ := allEdges_getElem_inj P L hL hfull
    exact Prod.ext hidx rfl
  · have hp₁ : ((allEdges P L)[i₁.val].1).1 = p :=
      incidentEnds_source_eq (P := P) (L := L) (p := p) (i := i₁) he₁'
    have hp₂ : ((allEdges P L)[i₂.val].1).2 = p :=
      incidentEnds_target_eq (P := P) (L := L) (p := p) (i := i₂) he₂'
    have hsame := sameRay_of_stMultigraph_incidentAngle_eq P L p hangle
    have hq₁_ne := stMultigraph_incidentOppositeEndpoint_ne P L he₁'
    have hq₂_ne := stMultigraph_incidentOppositeEndpoint_ne P L he₂'
    have hpos₁ : lineKey ℓ p < lineKey ℓ (stMultigraph_incidentOppositeEndpoint P L (i₁, false)) := by
      simpa [stMultigraph_incidentOppositeEndpoint, hp₁] using mem_edgesOnLine_lineKey_lt hℓ hi_pair
    have hneg₂ : lineKey ℓ (stMultigraph_incidentOppositeEndpoint P L (i₂, true)) < lineKey ℓ p := by
      simpa [stMultigraph_incidentOppositeEndpoint, hp₂] using mem_edgesOnLine_lineKey_lt hℓ hj_pair
    exfalso
    exact not_sameRay_of_lineKey_opposite hℓ hq₁_ne.symm hq₂_ne.symm hsame hpos₁ hneg₂
  · have hp₁ : ((allEdges P L)[i₁.val].1).2 = p :=
      incidentEnds_target_eq (P := P) (L := L) (p := p) (i := i₁) he₁'
    have hp₂ : ((allEdges P L)[i₂.val].1).1 = p :=
      incidentEnds_source_eq (P := P) (L := L) (p := p) (i := i₂) he₂'
    have hsame := sameRay_of_stMultigraph_incidentAngle_eq P L p hangle
    have hq₁_ne := stMultigraph_incidentOppositeEndpoint_ne P L he₁'
    have hq₂_ne := stMultigraph_incidentOppositeEndpoint_ne P L he₂'
    have hneg₁ : lineKey ℓ (stMultigraph_incidentOppositeEndpoint P L (i₁, true)) < lineKey ℓ p := by
      simpa [stMultigraph_incidentOppositeEndpoint, hp₁] using mem_edgesOnLine_lineKey_lt hℓ hi_pair
    have hpos₂ : lineKey ℓ p < lineKey ℓ (stMultigraph_incidentOppositeEndpoint P L (i₂, false)) := by
      simpa [stMultigraph_incidentOppositeEndpoint, hp₂] using mem_edgesOnLine_lineKey_lt hℓ hj_pair
    have hsame' :
        SameRay ℝ (complexVec p (stMultigraph_incidentOppositeEndpoint P L (i₂, false)))
          (complexVec p (stMultigraph_incidentOppositeEndpoint P L (i₁, true))) := by
      simpa [SameRay.sameRay_comm] using hsame
    exfalso
    exact not_sameRay_of_lineKey_opposite hℓ hq₂_ne.symm hq₁_ne.symm hsame' hpos₂ hneg₁
  · have hp₁ : ((allEdges P L)[i₁.val].1).2 = p := by
      have hmem : ((stMultigraph P L).endpoints i₁).2 = p := by
        simpa [incidentEnds] using he₁'
      simpa [stMultigraph] using hmem
    have hp₂ : ((allEdges P L)[i₂.val].1).2 = p := by
      have hmem : ((stMultigraph P L).endpoints i₂).2 = p := by
        simpa [incidentEnds] using he₂'
      simpa [stMultigraph] using hmem
    have hi' : (((allEdges P L)[i₁.val].1).1, p) ∈ edgesOnLine P ℓ := by
      simpa [hp₁] using hi_pair
    have hj' : (((allEdges P L)[i₂.val].1).1, p) ∈ edgesOnLine P ℓ := by
      simpa [hp₂] using hj_pair
    have hsrc : ((allEdges P L)[i₁.val].1).1 = ((allEdges P L)[i₂.val].1).1 := by
      exact edgesOnLine_target_unique
        (P := P) (ℓ := ℓ)
        (p := p)
        (q₁ := ((allEdges P L)[i₁.val].1).1)
        (q₂ := ((allEdges P L)[i₂.val].1).1)
        hi' hj'
    have hbare : ((allEdges P L)[i₁.val]).1 = ((allEdges P L)[i₂.val]).1 := by
      exact Prod.ext hsrc (hp₁.trans hp₂.symm)
    have hfull : (allEdges P L)[i₁.val] = (allEdges P L)[i₂.val] := by
      apply PSigma.ext hbare
      exact proof_irrel_heq _ _
    have hidx : i₁ = i₂ := allEdges_getElem_inj P L hL hfull
    exact Prod.ext hidx rfl

/-- The straight-line incidence drawing satisfies `ArcsRotationRegular` under the
standing affine-line hypothesis on `L`. -/
theorem stMultigraph_arcsRotationRegular (P : Finset (ℝ × ℝ))
    (L : Finset (Set (ℝ × ℝ))) (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    ArcsRotationRegular (stMultigraph P L) :=
  stMultigraph_arcsRotationRegular_of_incidentAnglesDistinct
    straightLineIncidentAnglesDistinct P L hL

set_option maxHeartbeats 200000

/-! ### Straight-line local planar layer for the incidence graph -/

/-- **Straight-line crossing-free edge bound.**

This is the exact remaining planar step for the Szemerédi--Trotter incidence
graph, stated only for the straight-segment drawing `stMultigraph P L`: every
crossing-free surviving edge set over an induced vertex set `S` has at most
`3 |S|` edges.

Literature match: this is the `e ≤ 3n` weakening of the planar
`e ≤ 3n - 6` bound used in the ACNS/Leighton proof of the crossing lemma, and
Pach--Tóth, *A crossing lemma for multigraphs*, Lemma 2.1, specialized to the
straight-line topological graph built from the point-line incidence construction. -/
def StraightLineCrossingFreeEdgeBound : Prop :=
  ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
    (∀ ℓ ∈ L, IsAffineLine ℓ) →
    ∀ S : Finset (ℝ × ℝ), S ⊆ (stMultigraph P L).V →
      ∀ E : Finset (Fin (stMultigraph P L).numEdges),
        E ⊆ edgeSetOn (stMultigraph P L) S →
        NoCrossingPairsInEdgeSet (stMultigraph P L) E →
          E.card ≤ 3 * S.card

/-- **Straight-line crossing-free edge bound, nondegenerate form.**

This is the exact remaining planar obligation after the small vertex-set cases
are removed: for `3 ≤ |S|`, every crossing-free surviving edge set in the
straight-segment incidence graph has at most `3 |S|` edges. -/
def StraightLineCrossingFreeEdgeBoundLarge : Prop :=
  ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
    (∀ ℓ ∈ L, IsAffineLine ℓ) →
    ∀ S : Finset (ℝ × ℝ), S ⊆ (stMultigraph P L).V → 3 ≤ S.card →
      ∀ E : Finset (Fin (stMultigraph P L).numEdges),
        E ⊆ edgeSetOn (stMultigraph P L) S →
        NoCrossingPairsInEdgeSet (stMultigraph P L) E →
          E.card ≤ 3 * S.card

/-- **Straight-line crossing-free componentwise planarization.**

This is the geometry-to-Euler layer for the actual Szemerédi--Trotter incidence
graph: every crossing-free surviving edge set in `stMultigraph P L` decomposes
into components whose nondegenerate pieces admit genus-zero simple
planarizations.

Literature match: this is the componentwise form of the planar step in the
ACNS/Leighton crossing-lemma proof and of Pach--Tóth, *A crossing lemma for
multigraphs*, Lemma 2.1 / Corollary 2.2.  The numerical edge bound below is then
only Euler bookkeeping; the remaining topological content is exactly this
straight-line planarization assertion. -/
def StraightLineCrossingFreeComponentwisePlanarization : Prop :=
  ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
    (∀ ℓ ∈ L, IsAffineLine ℓ) →
    ∀ S : Finset (ℝ × ℝ), S ⊆ (stMultigraph P L).V →
      ∀ E : Finset (Fin (stMultigraph P L).numEdges),
        E ⊆ edgeSetOn (stMultigraph P L) S →
        NoCrossingPairsInEdgeSet (stMultigraph P L) E →
          ComponentwiseCrossingFreePlanarization (stMultigraph P L) S E

/-- The only remaining topological input for the straight-line incidence graph is
genus-zero residual-map planarity for connected crossing-free restricted drawings:
the local rotation witness is inherited from the ambient straight-line drawing. -/
theorem straightLineCrossingFreeComponentwisePlanarization_of_crossingFreeResidualMapPlanarityOfARR
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    StraightLineCrossingFreeComponentwisePlanarization := by
  intro P L hL S hS E hE hfree
  let G := stMultigraph P L
  refine ⟨(edgeSetSimpleGraph G S E).ConnectedComponent,
    (show Fintype (edgeSetSimpleGraph G S E).ConnectedComponent from
      SetLike.instFintype),
    edgeSetComponentVertexSet G, edgeSetComponentEdgeSet G hE, ?_, ?_, ?_, ?_⟩
  · exact edgeSetComponentEdgeSet_card_sum G hE
  · exact (edgeSetComponentVertexSet_card_sum (G := G) (S := S) (E := E)).le
  · intro C
    exact edgeSetComponentVertexSet_subset G C
  · intro C
    let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
      (stMultigraph_arcsJoinEndpoints P L) C
    refine ⟨hEc, ?_⟩
    intro hv
    let D := edgeSetDrawing G (edgeSetComponentVertexSet G C)
      (edgeSetComponentEdgeSet G hE C) hEc
    have hEc_sub : edgeSetComponentEdgeSet G hE C ⊆ E :=
      edgeSetComponentEdgeSet_subset_edges G hE C
    have hfreeC : NoCrossingPairsInEdgeSet G (edgeSetComponentEdgeSet G hE C) :=
      NoCrossingPairsInEdgeSet.mono G hEc_sub hfree
    have hDmult : ∀ p q, D.multiplicity p q ≤ 1 := by
      simpa [D] using edgeSetDrawing_multiplicity_le
        (G := G) (hE := hEc) (stMultigraph_multiplicity_le_one P L hL)
    have hDjoin : D.ArcsJoinEndpoints := by
      simpa [D] using edgeSetDrawing_arcsJoinEndpoints
        (G := G) (hE := hEc) (stMultigraph_arcsJoinEndpoints P L)
    have hDcross : CrossingFree D := by
      simpa [D] using edgeSetDrawing_crossingFree_of_noCrossingPairs
        (G := G) (hE := hEc) (stMultigraph_crossingsAreIndependent P L hL) hfreeC
    have hDconn : D.GraphConnected := by
      simpa [D, hEc] using edgeSetComponentDrawing_graphConnected
        (G := G) hE (stMultigraph_arcsJoinEndpoints P L) C
    have hDverts : 3 ≤ D.V.card := by
      simpa [D, edgeSetDrawing] using hv
    have hDsub : edgeSetComponentVertexSet G C ⊆ G.V := by
      intro p hpVc
      exact hS (edgeSetComponentVertexSet_subset G C hpVc)
    have hDarr : ArcsRotationRegular D := by
      exact edgeSetDrawing_arcsRotationRegular
        (G := G) (hE := hEc) hDsub (stMultigraph_arcsRotationRegular P L hL)
    have hDplanar : (residualMap D hDarr).IsPlanar :=
      hplanar D hDmult hDjoin hDcross hDconn hDverts hDarr
    have hplD : HasGenusZeroSimplePlanarization (abstractize D) := by
      exact has_genus_zero_simple_planarization_of_residual_map D hDarr hDjoin
        hDmult hDconn hDverts hDplanar
    simpa [D] using
      abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing
        (G := G) hplD

/-- The restricted straight-line drawing attached to one canonical connected
component of a crossing-free surviving edge set. This packages the component
bookkeeping so the remaining planar-map hypothesis can be stated directly for
the component drawing. -/
noncomputable def stComponentDrawing
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (S : Finset (ℝ × ℝ)) (E : Finset (Fin (stMultigraph P L).numEdges))
    (hE : E ⊆ edgeSetOn (stMultigraph P L) S)
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent) :
    DrawnMultigraph :=
  edgeSetDrawing (stMultigraph P L) (edgeSetComponentVertexSet (stMultigraph P L) C)
    (edgeSetComponentEdgeSet (stMultigraph P L) hE C)
    (edgeSetComponentEdgeSet_subset_edgeSetOn (stMultigraph P L) hE
      (stMultigraph_arcsJoinEndpoints P L) C)

/-- Canonical straight-line component drawings inherit the ambient straight-line
local rotation witness. This removes the arbitrary-drawing ARR obligation from
the Szemerédi--Trotter/grid-rich path: only genus-zero residual-map planarity
remains for the component map. -/
theorem stComponentDrawing_arcsRotationRegular
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent) :
    ArcsRotationRegular (stComponentDrawing P L S E hE C) := by
  let G := stMultigraph P L
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
    (stMultigraph_arcsJoinEndpoints P L) C
  have hDsub : edgeSetComponentVertexSet G C ⊆ G.V := by
    intro p hp
    exact hS (edgeSetComponentVertexSet_subset G C hp)
  simpa [stComponentDrawing, G, hEc] using
    edgeSetDrawing_arcsRotationRegular (G := G) (hE := hEc) hDsub
      (stMultigraph_arcsRotationRegular P L hL)

/-- The endpoint-direction angle family for a canonical straight-line component.

An edge of the component drawing is first transported back to the ambient
`stMultigraph` by `edgeSetDrawingEdge`; the angle is then the straight-segment
endpoint direction already used in `stMultigraph_arcsRotationRegular`.  The
extra radius argument is ignored so that this function can be used directly as
an ARR angle family. -/
noncomputable def stComponentDrawing_incidentAngle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (p : ℝ × ℝ) :
    (Fin (stComponentDrawing P L S E hE C).numEdges × Bool) → ℝ → ℝ :=
  fun e _ =>
    stMultigraph_incidentAngle P L p
      (edgeSetDrawingEdge (stMultigraph P L)
        (edgeSetComponentEdgeSet_subset_edgeSetOn (stMultigraph P L) hE
          (stMultigraph_arcsJoinEndpoints P L) C) e.1, e.2)

/-- First crossings in a canonical component are the same straight-segment
first crossings as in the ambient `stMultigraph`.

The angle on the left is deliberately the ambient endpoint-direction angle,
after transporting the component edge index by `edgeSetDrawingEdge`.  This is
the concrete geometric bridge needed by the residual-map insertion layer: the
component drawing has not acquired arbitrary local sectors; its darts still
enter endpoint neighborhoods along the original straight incidence segments. -/
lemma stComponentDrawing_firstCrossing_localRadius_angle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    {p : ℝ × ℝ}
    {e : Fin (stComponentDrawing P L S E hE C).numEdges × Bool}
    (he : e ∈ incidentEnds (stComponentDrawing P L S E hE C) p)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p) :
    ∃ t : Set.Icc (0 : ℝ) 1,
      IsFirstCrossing (stComponentDrawing P L S E hE C) p e r t ∧
      stComponentDrawing_incidentAngle P L C p e r =
        angleAt p (((stComponentDrawing P L S E hE C).arc e.1).param t) := by
  let G := stMultigraph P L
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
    (stMultigraph_arcsJoinEndpoints P L) C
  have heG :
      (edgeSetDrawingEdge G hEc e.1, e.2) ∈ incidentEnds G p := by
    have hiff := mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hEc)
      (p := p) (e := e)
    simpa [stComponentDrawing, G, hEc] using hiff.mp he
  obtain ⟨t, hfirst, hangle⟩ :=
    stMultigraph_firstCrossing_localRadius_angle P L heG hr0 hr
  refine ⟨t, ?_, ?_⟩
  · have hiff := edgeSetDrawing_isFirstCrossing_iff (G := G) (hE := hEc)
      (p := p) (e := e) (r := r) (t := t)
    simpa [stComponentDrawing, G, hEc] using hiff.mpr hfirst
  · simpa [stComponentDrawing_incidentAngle, stComponentDrawing, G, hEc] using hangle

/-- The endpoint-direction angle family is injective on incident component
darts.  This is the component form of `straightLineIncidentAnglesDistinct`,
transported through the canonical `edgeSetDrawingEdge` embedding. -/
lemma stComponentDrawing_incidentAngle_injOn
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    {p : ℝ × ℝ} {r : ℝ} :
    Set.InjOn (fun e => stComponentDrawing_incidentAngle P L C p e r)
      (incidentEnds (stComponentDrawing P L S E hE C) p :
        Set (Fin (stComponentDrawing P L S E hE C).numEdges × Bool)) := by
  let G := stMultigraph P L
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
    (stMultigraph_arcsJoinEndpoints P L) C
  intro e₁ he₁ e₂ he₂ hangle
  have he₁G : (edgeSetDrawingEdge G hEc e₁.1, e₁.2) ∈ incidentEnds G p := by
    have hiff := mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hEc)
      (p := p) (e := e₁)
    simpa [stComponentDrawing, G, hEc] using hiff.mp he₁
  have he₂G : (edgeSetDrawingEdge G hEc e₂.1, e₂.2) ∈ incidentEnds G p := by
    have hiff := mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hEc)
      (p := p) (e := e₂)
    simpa [stComponentDrawing, G, hEc] using hiff.mp he₂
  have hpG : p ∈ G.V := by
    have he := he₁G
    rw [incidentEnds, Finset.mem_filter] at he
    by_cases hb : e₁.2
    · have hp : (G.endpoints (edgeSetDrawingEdge G hEc e₁.1)).2 = p := by
        simpa [hb] using he.2
      simpa [← hp] using (G.endpoints_mem (edgeSetDrawingEdge G hEc e₁.1)).2
    · have hp : (G.endpoints (edgeSetDrawingEdge G hEc e₁.1)).1 = p := by
        simpa [hb] using he.2
      simpa [← hp] using (G.endpoints_mem (edgeSetDrawingEdge G hEc e₁.1)).1
  have hinjG := straightLineIncidentAnglesDistinct P L hL p hpG
  have hmap : (edgeSetDrawingEdge G hEc e₁.1, e₁.2) =
      (edgeSetDrawingEdge G hEc e₂.1, e₂.2) := by
    exact hinjG he₁G he₂G
      (by simpa [stComponentDrawing_incidentAngle, G, hEc] using hangle)
  have hidx : edgeSetDrawingEdge G hEc e₁.1 = edgeSetDrawingEdge G hEc e₂.1 :=
    congrArg (fun x : Fin G.numEdges × Bool => x.1) hmap
  have hb : e₁.2 = e₂.2 :=
    congrArg (fun x : Fin G.numEdges × Bool => x.2) hmap
  exact Prod.ext (edgeSetDrawingEdge_injective (G := G) (hE := hEc) hidx) hb

/-- The canonical component vertex rotation can be read from the explicit
straight endpoint-direction angle family.

This avoids depending on the particular angle function selected from the ARR
existential.  By `vertexRotation_eq_of_witness`, the component's canonical
rotation is the same rotation obtained by sorting incident darts by their
transported straight-segment endpoint directions on any sufficiently small
circle. -/
theorem stComponentDrawing_vertexRotation_eq_incidentAngle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    {p : ℝ × ℝ}
    (hp : p ∈ (stComponentDrawing P L S E hE C).V)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p) :
    vertexRotationAtRadius (stComponentDrawing P L S E hE C) p
        (stComponentDrawing_incidentAngle P L C p) r
        (endAngleKey_injective (stComponentDrawing P L S E hE C) p _ _
          (stComponentDrawing_incidentAngle_injOn P L hL C (p := p) (r := r))) =
      vertexRotation (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C) hp := by
  let G := stMultigraph P L
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
    (stMultigraph_arcsJoinEndpoints P L) C
  let D := stComponentDrawing P L S E hE C
  let hDarr := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  have hDjoin : D.ArcsJoinEndpoints := by
    simpa [D, stComponentDrawing, G, hEc] using edgeSetDrawing_arcsJoinEndpoints
      (G := G) (hE := hEc) (stMultigraph_arcsJoinEndpoints P L)
  refine vertexRotation_eq_of_witness D hDarr hDjoin hp ?_ ?_ ?_ hr0 hr
  · intro e he r hr0 hr
    obtain ⟨t, hfirst, hangle⟩ :=
      stComponentDrawing_firstCrossing_localRadius_angle P L C he hr0 hr
    exact ⟨t, hfirst, hangle⟩
  · intro r _hr0 _hr
    simpa [D] using stComponentDrawing_incidentAngle_injOn P L hL C (p := p) (r := r)
  · intro _e₁ _he₁ _e₂ _he₂ _r _hr0 _hr _r' _hr'0 _hr'
    rfl

/-- The straight endpoint-direction angle family on a permuted ordered prefix of
a canonical component drawing.

This is the angle family used by the residual-map insertion proofs after the
component edges have been reindexed by a literature order and truncated to a
prefix.  A prefix dart is cast to the permuted component, transported through
`π`, and then read by `stComponentDrawing_incidentAngle`. -/
noncomputable def stComponentDrawing_prefixPermuteIncidentAngle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ) (hm : m ≤ (stComponentDrawing P L S E hE C).numEdges)
    (p : ℝ × ℝ) :
    (Fin (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).numEdges ×
      Bool) → ℝ → ℝ :=
  fun e r => stComponentDrawing_incidentAngle P L C p (π (Fin.castLE hm e.1), e.2) r

/-- First crossings in a permuted ordered prefix of a canonical component are
still the first crossings of the underlying straight incidence segments. -/
lemma stComponentDrawing_prefixPermuteIncidentAngle_firstCrossing
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {m : ℕ} {hm : m ≤ (stComponentDrawing P L S E hE C).numEdges}
    {p : ℝ × ℝ}
    {e : Fin (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).numEdges ×
      Bool}
    (he : e ∈ incidentEnds (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
      m hm) p)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p) :
    ∃ t : Set.Icc (0 : ℝ) 1,
      IsFirstCrossing (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)
        p e r t ∧
      stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p e r =
        angleAt p (((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).arc
          e.1).param t) := by
  let D := stComponentDrawing P L S E hE C
  have heH : (Fin.castLE hm e.1, e.2) ∈ incidentEnds (D.permuteEdges π) p := by
    exact (mem_incidentEnds_prefixEdges_iff (G := D.permuteEdges π) (m := m) (hm := hm)).mp
      (by simpa [D] using he)
  have heD : (π (Fin.castLE hm e.1), e.2) ∈ incidentEnds D p := by
    exact (mem_incidentEnds_permuteEdges_iff (G := D) π).mp heH
  obtain ⟨t, hfirstD, hangle⟩ :=
    stComponentDrawing_firstCrossing_localRadius_angle P L C heD hr0 hr
  refine ⟨t, ?_, ?_⟩
  · have hfirstH : IsFirstCrossing (D.permuteEdges π) p (Fin.castLE hm e.1, e.2) r t := by
      exact (permuteEdges_isFirstCrossing_iff (G := D) π).mpr hfirstD
    have hfirstPrefix :=
      (prefixEdges_isFirstCrossing_iff (G := D.permuteEdges π) (m := m) (hm := hm)).mpr
        hfirstH
    simpa [D] using hfirstPrefix
  · simpa [stComponentDrawing_prefixPermuteIncidentAngle, D, DrawnMultigraph.prefixEdges,
      DrawnMultigraph.permuteEdges] using hangle

/-- The straight endpoint-direction angle family is injective on incident darts
of a permuted ordered prefix of a canonical component drawing. -/
lemma stComponentDrawing_prefixPermuteIncidentAngle_injOn
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {m : ℕ} {hm : m ≤ (stComponentDrawing P L S E hE C).numEdges}
    {p : ℝ × ℝ} {r : ℝ} :
    Set.InjOn (fun e => stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p e r)
      (incidentEnds (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p :
        Set (Fin (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).numEdges ×
          Bool)) := by
  let D := stComponentDrawing P L S E hE C
  intro e₁ he₁ e₂ he₂ hangle
  have he₁H : (Fin.castLE hm e₁.1, e₁.2) ∈ incidentEnds (D.permuteEdges π) p := by
    exact (mem_incidentEnds_prefixEdges_iff (G := D.permuteEdges π) (m := m) (hm := hm)).mp
      (by simpa [D] using he₁)
  have he₂H : (Fin.castLE hm e₂.1, e₂.2) ∈ incidentEnds (D.permuteEdges π) p := by
    exact (mem_incidentEnds_prefixEdges_iff (G := D.permuteEdges π) (m := m) (hm := hm)).mp
      (by simpa [D] using he₂)
  have he₁D : (π (Fin.castLE hm e₁.1), e₁.2) ∈ incidentEnds D p :=
    (mem_incidentEnds_permuteEdges_iff (G := D) π).mp he₁H
  have he₂D : (π (Fin.castLE hm e₂.1), e₂.2) ∈ incidentEnds D p :=
    (mem_incidentEnds_permuteEdges_iff (G := D) π).mp he₂H
  have hinjD := stComponentDrawing_incidentAngle_injOn P L hL (hE := hE) C
    (p := p) (r := r)
  have hmap : (π (Fin.castLE hm e₁.1), e₁.2) = (π (Fin.castLE hm e₂.1), e₂.2) := by
    exact hinjD he₁D he₂D
      (by simpa [stComponentDrawing_prefixPermuteIncidentAngle, D] using hangle)
  have hidxπ : π (Fin.castLE hm e₁.1) = π (Fin.castLE hm e₂.1) :=
    congrArg (fun x : Fin D.numEdges × Bool => x.1) hmap
  have hidx : e₁.1 = e₂.1 := by
    apply Fin.ext
    have hcast : Fin.castLE hm e₁.1 = Fin.castLE hm e₂.1 := π.injective hidxπ
    simpa using congrArg Fin.val hcast
  have hb : e₁.2 = e₂.2 :=
    congrArg (fun x : Fin D.numEdges × Bool => x.2) hmap
  exact Prod.ext hidx hb

/-- The vertex rotation of a permuted ordered prefix of a canonical component can
be read from the explicit straight endpoint-direction angle family.

This is the prefix-order version of
`stComponentDrawing_vertexRotation_eq_incidentAngle`, and is the rotation bridge
needed by residual-map prefix insertions. -/
theorem stComponentDrawing_prefixPermute_vertexRotation_eq_incidentAngle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {m : ℕ} {hm : m ≤ (stComponentDrawing P L S E hE C).numEdges}
    {p : ℝ × ℝ}
    (hp : p ∈ (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).V)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p) :
    vertexRotationAtRadius (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
        m hm) p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p) r
        (endAngleKey_injective
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r))) =
      vertexRotation (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)
        (prefixEdges_arcsRotationRegular ((stComponentDrawing P L S E hE C).permuteEdges π)
          m hm
          (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp := by
  let D := stComponentDrawing P L S E hE C
  let H := (D.permuteEdges π).prefixEdges m hm
  let hDarr := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  let hHarr := prefixEdges_arcsRotationRegular (D.permuteEdges π) m hm
    (permuteEdges_arrRotationRegular D π hDarr)
  have hDjoin : D.ArcsJoinEndpoints := by
    let G := stMultigraph P L
    let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
      (stMultigraph_arcsJoinEndpoints P L) C
    simpa [D, stComponentDrawing, G, hEc] using edgeSetDrawing_arcsJoinEndpoints
      (G := G) (hE := hEc) (stMultigraph_arcsJoinEndpoints P L)
  have hHjoin : H.ArcsJoinEndpoints := by
    simpa [H] using prefixEdges_arcsJoinEndpoints (D.permuteEdges π) m hm
      (permuteEdges_arcsJoinEndpoints D π hDjoin)
  refine vertexRotation_eq_of_witness H hHarr hHjoin (by simpa [H, D] using hp) ?_ ?_ ?_ hr0 hr
  · intro e he r hr0 hr
    obtain ⟨t, hfirst, hangle⟩ :=
      stComponentDrawing_prefixPermuteIncidentAngle_firstCrossing P L C π he hr0 hr
    exact ⟨t, hfirst, hangle⟩
  · intro r _hr0 _hr
    simpa [H, D] using
      stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
        (p := p) (r := r)
  · intro _e₁ _he₁ _e₂ _he₂ _r _hr0 _hr _r' _hr'0 _hr'
    rfl

/-- On a permuted ordered prefix of a canonical component, the explicit
straight-angle rotation agrees with the ARR rotation read at the canonical ARR
radius.

This is the radius-parametrized form of
`stComponentDrawing_prefixPermute_vertexRotation_eq_incidentAngle`.  It is the
convenient bridge for later cotree steps: hypotheses stated using
`vertexRotationAtRadius` and `arrAngle` can be transported to the explicit
straight endpoint-direction angles already formalized for the component
drawing. -/
theorem stComponentDrawing_prefixPermute_vertexRotationAtRadius_eq_arr
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {m : ℕ} {hm : m ≤ (stComponentDrawing P L S E hE C).numEdges}
    {p : ℝ × ℝ}
    (hp : p ∈ (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm).V)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p) :
    vertexRotationAtRadius
        (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p) r
        (endAngleKey_injective
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r))) =
      vertexRotationAtRadius
        (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p
        (arrAngle
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)
          (prefixEdges_arcsRotationRegular
            ((stComponentDrawing P L S E hE C).permuteEdges π) m hm
            (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
              (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
        (arrRadius
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)
          (prefixEdges_arcsRotationRegular
            ((stComponentDrawing P L S E hE C).permuteEdges π) m hm
            (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
              (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
        (endAngleKey_injective
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm) p _ _
          (arrAngle_injOn
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)
            (prefixEdges_arcsRotationRegular
              ((stComponentDrawing P L S E hE C).permuteEdges π) m hm
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp
            (arrRadius_pos
              (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm))
              (prefixEdges_arcsRotationRegular
                ((stComponentDrawing P L S E hE C).permuteEdges π) m hm
                (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
            le_rfl)) := by
  let D := stComponentDrawing P L S E hE C
  let H := (D.permuteEdges π).prefixEdges m hm
  let hDarr := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  let hHarr := prefixEdges_arcsRotationRegular (D.permuteEdges π) m hm
    (permuteEdges_arrRotationRegular D π hDarr)
  calc
    vertexRotationAtRadius H p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p) r
        (endAngleKey_injective H p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r)))
      = vertexRotation H hHarr hp :=
        stComponentDrawing_prefixPermute_vertexRotation_eq_incidentAngle
          P L hL hS (hE := hE) C π hp hr0 hr
    _ = vertexRotationAtRadius H p (arrAngle H hHarr hp) (arrRadius H hHarr hp)
          (endAngleKey_injective H p _ _
            (arrAngle_injOn H hHarr hp (arrRadius_pos (G := H) hHarr hp) le_rfl)) := by
          symm
          exact rotation_wellDefined H hHarr hp (arrRadius_pos (G := H) hHarr hp) le_rfl

end PachSharir.SzemerediTrotter
