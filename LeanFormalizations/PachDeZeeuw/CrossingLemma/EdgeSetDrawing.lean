/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemmaAmplification
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapPermuteEdges
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualPlanarization

/-!
# Restricted drawings for surviving edge sets

This module introduces the concrete drawn subgraph associated to a vertex subset
`S` and a surviving edge set `E ⊆ edgeSetOn G S`.

The edge set is enumerated with `Finset.equivFin E`, so the resulting object is a
plain `DrawnMultigraph` and can be fed to the residual-map machinery.  The
underlying abstract carrier is the same finite multigraph data as
`abstractizeEdgeSet G S E hE`; the transport lemmas here are the bookkeeping
needed before the genus-zero residual-map layer can be applied to edge subsets.
-/

namespace CrossingLemma

open CombinatorialMap

variable (G : DrawnMultigraph)

/-- The drawn subgraph supported on the vertex set `S` and the surviving edge
set `E`.  Edge indices are the canonical enumeration of `E` by
`Finset.equivFin`.  The crossing counter is set to `0`; the restricted object is
used here for its geometry and residual map, not as an independently well-drawn
crossing-lemma input. -/
noncomputable def edgeSetDrawing (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges))
    (hE : E ⊆ edgeSetOn G S) : DrawnMultigraph where
  V := S
  numEdges := E.card
  endpoints i := G.endpoints ((Finset.equivFin E).symm i : Fin G.numEdges)
  endpoints_mem i := by
    have he_mem : ((Finset.equivFin E).symm i : Fin G.numEdges) ∈ E :=
      ((Finset.equivFin E).symm i).2
    have he_on : ((Finset.equivFin E).symm i : Fin G.numEdges) ∈ edgeSetOn G S :=
      hE he_mem
    rw [edgeSetOn, Finset.mem_filter] at he_on
    exact he_on.2
  arc i := G.arc ((Finset.equivFin E).symm i : Fin G.numEdges)
  crossings := 0

/-- The edge of `G` represented by an edge index of `edgeSetDrawing`. -/
noncomputable def edgeSetDrawingEdge
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (i : Fin (edgeSetDrawing G S E hE).numEdges) : Fin G.numEdges :=
  ((Finset.equivFin E).symm i : Fin G.numEdges)

/-- The restricted drawing preserves the arc-endpoint condition. -/
theorem edgeSetDrawing_arcsJoinEndpoints
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hjoin : G.ArcsJoinEndpoints) :
    (edgeSetDrawing G S E hE).ArcsJoinEndpoints := by
  intro i
  exact hjoin ((Finset.equivFin E).symm i : Fin G.numEdges)

/-- Membership in `incidentEnds` for a restricted drawing is exactly membership in
the ambient drawing after transporting the edge index through
`Finset.equivFin E`. -/
theorem mem_incidentEnds_edgeSetDrawing_iff
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    {p : ℝ × ℝ} {e : Fin (edgeSetDrawing G S E hE).numEdges × Bool} :
    e ∈ incidentEnds (edgeSetDrawing G S E hE) p ↔
      (edgeSetDrawingEdge G hE e.1, e.2) ∈ incidentEnds G p := by
  cases e with
  | mk i b =>
      cases b
      · constructor <;> intro h
        · rw [incidentEnds, Finset.mem_filter] at h ⊢
          exact ⟨Finset.mem_univ _, by simpa [edgeSetDrawing, edgeSetDrawingEdge] using h.2⟩
        · rw [incidentEnds, Finset.mem_filter] at h ⊢
          exact ⟨Finset.mem_univ _, by simpa [edgeSetDrawing, edgeSetDrawingEdge] using h.2⟩
      · constructor <;> intro h
        · rw [incidentEnds, Finset.mem_filter] at h ⊢
          exact ⟨Finset.mem_univ _, by simpa [edgeSetDrawing, edgeSetDrawingEdge] using h.2⟩
        · rw [incidentEnds, Finset.mem_filter] at h ⊢
          exact ⟨Finset.mem_univ _, by simpa [edgeSetDrawing, edgeSetDrawingEdge] using h.2⟩

/-- The first-crossing predicate is unchanged when passing from the restricted
drawing to the ambient drawing along the canonical edge-index transport. -/
theorem edgeSetDrawing_isFirstCrossing_iff
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    {p : ℝ × ℝ} {e : Fin (edgeSetDrawing G S E hE).numEdges × Bool}
    {r : ℝ} {t : Set.Icc (0 : ℝ) 1} :
    IsFirstCrossing (edgeSetDrawing G S E hE) p e r t ↔
      IsFirstCrossing G p (edgeSetDrawingEdge G hE e.1, e.2) r t := by
  cases e with
  | mk i b =>
      cases b <;> simp [IsFirstCrossing, edgeSetDrawing, edgeSetDrawingEdge]

/-- The canonical edge-index transport from a restricted drawing back to the
ambient drawing is injective. -/
theorem edgeSetDrawingEdge_injective
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S} :
    Function.Injective (edgeSetDrawingEdge G hE) := by
  intro i j hij
  have hs : (Finset.equivFin E).symm i = (Finset.equivFin E).symm j := Subtype.ext hij
  exact (Finset.equivFin E).symm.injective hs

/-- `ArcsRotationRegular` is inherited by a restricted drawing: the witness radius
and angle function are read from the ambient drawing via the canonical
enumeration of the surviving edge set. -/
theorem edgeSetDrawing_arcsRotationRegular
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hS : S ⊆ G.V) (hARR : ArcsRotationRegular G) :
    ArcsRotationRegular (edgeSetDrawing G S E hE) := by
  let H := edgeSetDrawing G S E hE
  intro p hp
  have hpS : p ∈ S := by simpa [H, edgeSetDrawing] using hp
  have hpG : p ∈ G.V := hS hpS
  obtain ⟨rp, α, hrp, hfirst, hinj, hstable⟩ := hARR p hpG
  refine ⟨rp, fun e r => α (edgeSetDrawingEdge G hE e.1, e.2) r, hrp, ?_, ?_, ?_⟩
  · intro e he r hr0 hr
    have heG : (edgeSetDrawingEdge G hE e.1, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hE)).mp he
    obtain ⟨t, hcross, hangle⟩ := hfirst _ heG r hr0 hr
    refine ⟨t, ?_, ?_⟩
    · exact (edgeSetDrawing_isFirstCrossing_iff (G := G) (hE := hE)).mpr hcross
    · simpa [edgeSetDrawingEdge]
  · intro r hr0 hr e₁ he₁ e₂ he₂ heq
    have he₁G : (edgeSetDrawingEdge G hE e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hE)).mp he₁
    have he₂G : (edgeSetDrawingEdge G hE e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hE)).mp he₂
    have hmap :
        (edgeSetDrawingEdge G hE e₁.1, e₁.2) = (edgeSetDrawingEdge G hE e₂.1, e₂.2) :=
      hinj r hr0 hr he₁G he₂G heq
    have hidx : edgeSetDrawingEdge G hE e₁.1 = edgeSetDrawingEdge G hE e₂.1 := by
      exact congrArg Prod.fst hmap
    have hb : e₁.2 = e₂.2 := by
      injection hmap with _ hb
    exact Prod.ext (edgeSetDrawingEdge_injective (G := G) (hE := hE) hidx) hb
  · intro e₁ he₁ e₂ he₂ r hr0 hr r' hr'0 hr'
    have he₁G : (edgeSetDrawingEdge G hE e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hE)).mp he₁
    have he₂G : (edgeSetDrawingEdge G hE e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_edgeSetDrawing_iff (G := G) (hE := hE)).mp he₂
    simpa [edgeSetDrawingEdge] using
      hstable _ he₁G _ he₂G r hr0 hr r' hr'0 hr'

/-- Edge multiplicity in the restricted drawing is bounded by the multiplicity
in the original drawing. -/
theorem edgeSetDrawing_multiplicity_le
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    {M : ℕ} (hmult : ∀ p q, G.multiplicity p q ≤ M) :
    ∀ p q, (edgeSetDrawing G S E hE).multiplicity p q ≤ M := by
  classical
  intro p q
  unfold DrawnMultigraph.multiplicity
  set H := edgeSetDrawing G S E hE
  let f : Fin H.numEdges → Fin G.numEdges := fun i => ((Finset.equivFin E).symm i : Fin G.numEdges)
  have hmaps : Set.MapsTo f
      (↑((Finset.univ : Finset (Fin H.numEdges)).filter
        fun i => H.endpoints i = (p, q) ∨ H.endpoints i = (q, p)))
      (↑((Finset.univ : Finset (Fin G.numEdges)).filter
        fun i => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))) := by
    intro i hi
    have hi' : H.endpoints i = (p, q) ∨ H.endpoints i = (q, p) := by
      simpa using hi
    simpa [H, edgeSetDrawing, f] using hi'
  have hinj : (↑((Finset.univ : Finset (Fin H.numEdges)).filter
        fun i => H.endpoints i = (p, q) ∨ H.endpoints i = (q, p)) : Set (Fin H.numEdges)).InjOn f := by
    intro i _ j _ hij
    have hs : (Finset.equivFin E).symm i = (Finset.equivFin E).symm j := Subtype.ext hij
    exact (Finset.equivFin E).symm.injective hs
  have hcard_le :
      ((Finset.univ : Finset (Fin H.numEdges)).filter
        fun i => H.endpoints i = (p, q) ∨ H.endpoints i = (q, p)).card ≤
      ((Finset.univ : Finset (Fin G.numEdges)).filter
        fun i => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  exact hcard_le.trans (hmult p q)

/-- The independent-crossing condition is inherited by a restricted drawing. -/
theorem edgeSetDrawing_crossingsAreIndependent
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hcross : G.CrossingsAreIndependent) :
    (edgeSetDrawing G S E hE).CrossingsAreIndependent := by
  intro i j hij hnonempty
  let H := edgeSetDrawing G S E hE
  let f : Fin H.numEdges → Fin G.numEdges := fun i => ((Finset.equivFin E).symm i : Fin G.numEdges)
  have hfne : f i ≠ f j := by
    intro h
    have hs : (Finset.equivFin E).symm i = (Finset.equivFin E).symm j := Subtype.ext h
    exact hij ((Finset.equivFin E).symm.injective hs)
  have hnonemptyG :
      (interiorOfArc (G.arc (f i)) ∩ interiorOfArc (G.arc (f j))).Nonempty := by
    simpa [H, edgeSetDrawing, f] using hnonempty
  have hfour := hcross (f i) (f j) hfne hnonemptyG
  simpa [DrawnMultigraph.FourDistinctEndpoints, H, edgeSetDrawing, f] using hfour

/-- A restricted drawing on a crossing-free surviving edge set has zero true
crossings.  This is the drawing-level form of the literature deletion step:
after one edge is removed from every counted independent crossing pair, the
remaining topological graph is crossing-free. -/
theorem edgeSetDrawing_crossingCount_eq_zero
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hcross : G.CrossingsAreIndependent) (hfree : NoCrossingPairsInEdgeSet G E) :
    (edgeSetDrawing G S E hE).crossingCount = 0 := by
  classical
  let H := edgeSetDrawing G S E hE
  unfold DrawnMultigraph.crossingCount
  rw [Finset.card_eq_zero]
  apply Finset.ext
  intro ij
  simp only [Finset.notMem_empty, iff_false]
  intro hij
  rw [Finset.mem_filter] at hij
  have hlt : ij.1 < ij.2 := hij.2.1
  have hnonempty : (interiorOfArc (H.arc ij.1) ∩ interiorOfArc (H.arc ij.2)).Nonempty :=
    hij.2.2
  let e₁ : Fin G.numEdges := ((Finset.equivFin E).symm ij.1 : Fin G.numEdges)
  let e₂ : Fin G.numEdges := ((Finset.equivFin E).symm ij.2 : Fin G.numEdges)
  have he₁ : e₁ ∈ E := ((Finset.equivFin E).symm ij.1).2
  have he₂ : e₂ ∈ E := ((Finset.equivFin E).symm ij.2).2
  have hene : e₁ ≠ e₂ := by
    intro h
    have hs : (Finset.equivFin E).symm ij.1 = (Finset.equivFin E).symm ij.2 := Subtype.ext h
    exact (ne_of_lt hlt) ((Finset.equivFin E).symm.injective hs)
  have hnonemptyG :
      (interiorOfArc (G.arc e₁) ∩ interiorOfArc (G.arc e₂)).Nonempty := by
    simpa [H, edgeSetDrawing, e₁, e₂] using hnonempty
  by_cases hltE : e₁.val < e₂.val
  · have hp : (e₁, e₂) ∈ crossingPairs G := by
      rw [crossingPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hltE, hnonemptyG, hcross e₁ e₂ hene hnonemptyG⟩
    exact hfree (e₁, e₂) hp he₁ he₂
  · have hgtE : e₂.val < e₁.val := by
      have hle : e₂.val ≤ e₁.val := Nat.le_of_not_lt hltE
      exact Nat.lt_of_le_of_ne hle (fun hval => hene (Fin.ext hval.symm))
    have hnonemptyG' :
        (interiorOfArc (G.arc e₂) ∩ interiorOfArc (G.arc e₁)).Nonempty := by
      rwa [Set.inter_comm]
    have hp : (e₂, e₁) ∈ crossingPairs G := by
      rw [crossingPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgtE, hnonemptyG', hcross e₂ e₁ hene.symm hnonemptyG'⟩
    exact hfree (e₂, e₁) hp he₂ he₁

/-- A crossing-free restricted drawing with the crossing counter set to zero is
`WellDrawn`. -/
theorem edgeSetDrawing_wellDrawn_of_noCrossingPairs
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hcross : G.CrossingsAreIndependent) (hfree : NoCrossingPairsInEdgeSet G E) :
    (edgeSetDrawing G S E hE).WellDrawn := by
  unfold DrawnMultigraph.WellDrawn
  rw [edgeSetDrawing_crossingCount_eq_zero G hcross hfree]
  simp [edgeSetDrawing]

/-- A crossing-free surviving edge set gives a geometrically crossing-free
restricted drawing. -/
theorem edgeSetDrawing_crossingFree_of_noCrossingPairs
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hcross : G.CrossingsAreIndependent) (hfree : NoCrossingPairsInEdgeSet G E) :
    CrossingFree (edgeSetDrawing G S E hE) := by
  intro i j hij
  let H := edgeSetDrawing G S E hE
  let f : Fin H.numEdges → Fin G.numEdges :=
    fun i => ((Finset.equivFin E).symm i : Fin G.numEdges)
  have hfi : f i ∈ E := ((Finset.equivFin E).symm i).2
  have hfj : f j ∈ E := ((Finset.equivFin E).symm j).2
  have hfne : f i ≠ f j := by
    intro h
    have hs : (Finset.equivFin E).symm i = (Finset.equivFin E).symm j := Subtype.ext h
    exact hij ((Finset.equivFin E).symm.injective hs)
  have hdisj := disjoint_interiors_of_noCrossingPairsInEdgeSet G hcross hfree hfi hfj hfne
  simpa [H, edgeSetDrawing, f] using hdisj

/-! ### Canonical finite connected components of a surviving edge set -/

/-- The simple graph on the sampled vertex set `S` generated by a surviving edge
set `E`.  Parallel surviving edges are forgotten here; multiplicity is handled
separately by `PairMultiplicityBound`. -/
noncomputable def edgeSetSimpleGraph (S : Finset (ℝ × ℝ))
    (E : Finset (Fin G.numEdges)) : SimpleGraph ↥S where
  Adj p q :=
    p ≠ q ∧ ∃ e ∈ E,
      G.endpoints e = (p.1, q.1) ∨ G.endpoints e = (q.1, p.1)
  symm := by
    intro p q h
    rcases h with ⟨hpq, e, heE, hends | hends⟩
    · exact ⟨hpq.symm, e, heE, Or.inr hends⟩
    · exact ⟨hpq.symm, e, heE, Or.inl hends⟩
  loopless := ⟨by
    intro p h
    exact h.1 rfl⟩

/-- The component of `edgeSetSimpleGraph G S E` containing the first endpoint
of a surviving edge. -/
noncomputable def edgeSetComponentOf {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S) (e : ↥E) :
    (edgeSetSimpleGraph G S E).ConnectedComponent :=
  (edgeSetSimpleGraph G S E).connectedComponentMk
    ⟨(G.endpoints (e : Fin G.numEdges)).1, by
      have he_on : (e : Fin G.numEdges) ∈ edgeSetOn G S := hE e.2
      rw [edgeSetOn, Finset.mem_filter] at he_on
      exact he_on.2.1⟩

/-- The vertices of a canonical connected component, viewed again as points of
the plane. -/
noncomputable def edgeSetComponentVertexSet {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)}
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) : Finset (ℝ × ℝ) :=
  by
    classical
    exact ((Finset.univ : Finset ↥S).filter fun p => p ∈ C.supp).map
      ⟨Subtype.val, fun p q h => Subtype.ext h⟩

/-- Membership in the plane-valued vertex set of a canonical component. -/
theorem mem_edgeSetComponentVertexSet {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)}
    {C : (edgeSetSimpleGraph G S E).ConnectedComponent} {p : ↥S} :
    (p : ℝ × ℝ) ∈ edgeSetComponentVertexSet G C ↔ p ∈ C.supp := by
  classical
  simp [edgeSetComponentVertexSet]

/-- Canonical component vertex sets are subsets of the ambient sample `S`. -/
theorem edgeSetComponentVertexSet_subset {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)}
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) :
    edgeSetComponentVertexSet G C ⊆ S := by
  classical
  intro p hp
  rw [edgeSetComponentVertexSet, Finset.mem_map] at hp
  rcases hp with ⟨q, _hq, rfl⟩
  exact q.2

/-- The surviving edges whose first endpoint lies in a given canonical
component. -/
noncomputable def edgeSetComponentEdgeSet {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) :
    Finset (Fin G.numEdges) :=
  by
    classical
    exact ((Finset.univ : Finset ↥E).filter fun e => edgeSetComponentOf G hE e = C).map
      ⟨Subtype.val, fun e e' h => Subtype.ext h⟩

/-- The canonical edge set of a component is a subset of the original surviving
edge set. -/
theorem edgeSetComponentEdgeSet_subset_edges {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) :
    edgeSetComponentEdgeSet G hE C ⊆ E := by
  classical
  intro e he
  rw [edgeSetComponentEdgeSet, Finset.mem_map] at he
  rcases he with ⟨e', _he', rfl⟩
  exact e'.2

/-- `NoCrossingPairsInEdgeSet` is monotone under passing to a subset of edges. -/
theorem NoCrossingPairsInEdgeSet.mono {E F : Finset (Fin G.numEdges)}
    (hFE : F ⊆ E) (hfree : NoCrossingPairsInEdgeSet G E) :
    NoCrossingPairsInEdgeSet G F := by
  intro ij hij hi hj
  exact hfree ij hij (hFE hi) (hFE hj)

/-- A surviving edge connects two vertices in the same canonical component. -/
theorem edgeSetSimpleGraph_reachable_endpoints {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (hjoin : G.ArcsJoinEndpoints) (e : ↥E) :
    (edgeSetSimpleGraph G S E).Reachable
      ⟨(G.endpoints (e : Fin G.numEdges)).1, by
        have he_on : (e : Fin G.numEdges) ∈ edgeSetOn G S := hE e.2
        rw [edgeSetOn, Finset.mem_filter] at he_on
        exact he_on.2.1⟩
      ⟨(G.endpoints (e : Fin G.numEdges)).2, by
        have he_on : (e : Fin G.numEdges) ∈ edgeSetOn G S := hE e.2
        rw [edgeSetOn, Finset.mem_filter] at he_on
        exact he_on.2.2⟩ := by
  refine SimpleGraph.Adj.reachable ?_
  refine ⟨?_, e, e.2, Or.inl rfl⟩
  intro h
  exact DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e (congrArg Subtype.val h)

/-- The edge set of a canonical component is supported on that component's
vertex set. -/
theorem edgeSetComponentEdgeSet_subset_edgeSetOn {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (hjoin : G.ArcsJoinEndpoints)
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) :
    edgeSetComponentEdgeSet G hE C ⊆ edgeSetOn G (edgeSetComponentVertexSet G C) := by
  classical
  intro e he
  rw [edgeSetComponentEdgeSet, Finset.mem_map] at he
  rcases he with ⟨e', he', rfl⟩
  rw [Finset.mem_filter] at he'
  rw [edgeSetOn, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  let p₁ : ↥S := ⟨(G.endpoints (e' : Fin G.numEdges)).1, by
    have he_on : (e' : Fin G.numEdges) ∈ edgeSetOn G S := hE e'.2
    rw [edgeSetOn, Finset.mem_filter] at he_on
    exact he_on.2.1⟩
  let p₂ : ↥S := ⟨(G.endpoints (e' : Fin G.numEdges)).2, by
    have he_on : (e' : Fin G.numEdges) ∈ edgeSetOn G S := hE e'.2
    rw [edgeSetOn, Finset.mem_filter] at he_on
    exact he_on.2.2⟩
  have hp₁C : p₁ ∈ C.supp := by
    simpa [edgeSetComponentOf, p₁] using he'.2
  have hreach := edgeSetSimpleGraph_reachable_endpoints G hE hjoin e'
  have hp₂C : p₂ ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hp₁C ⊢
    rw [← hp₁C]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  constructor
  · exact (mem_edgeSetComponentVertexSet (G := G) (C := C) (p := p₁)).mpr hp₁C
  · exact (mem_edgeSetComponentVertexSet (G := G) (C := C) (p := p₂)).mpr hp₂C

/-- An adjacency whose left endpoint lies in a canonical component is represented
by an edge of that component's canonical edge set. -/
theorem exists_mem_edgeSetComponentEdgeSet_of_adj {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    {C : (edgeSetSimpleGraph G S E).ConnectedComponent} {p q : ↥S}
    (hpC : p ∈ C.supp) (hadj : (edgeSetSimpleGraph G S E).Adj p q) :
    ∃ e ∈ edgeSetComponentEdgeSet G hE C,
      G.endpoints e = ((p : ℝ × ℝ), (q : ℝ × ℝ)) ∨
        G.endpoints e = ((q : ℝ × ℝ), (p : ℝ × ℝ)) := by
  classical
  have hadj' := hadj
  rcases hadj with ⟨_hpq, e, heE, hends⟩
  refine ⟨e, ?_, hends⟩
  have he_on : e ∈ edgeSetOn G S := hE heE
  rw [edgeSetOn, Finset.mem_filter] at he_on
  let p₁ : ↥S := ⟨(G.endpoints e).1, he_on.2.1⟩
  have hp₁C : p₁ ∈ C.supp := by
    rcases hends with hforward | hbackward
    · have hp₁ : p₁ = p := by
        exact Subtype.ext (by simp [p₁, hforward])
      simpa [hp₁] using hpC
    · have hqC : q ∈ C.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hadj').mp hpC
      have hp₁ : p₁ = q := by
        exact Subtype.ext (by simp [p₁, hbackward])
      simpa [hp₁] using hqC
  rw [edgeSetComponentEdgeSet, Finset.mem_map]
  refine ⟨⟨e, heE⟩, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simpa [edgeSetComponentOf, p₁] using hp₁C⟩

/-- The restricted drawing on a canonical connected component is graph-connected. -/
theorem edgeSetComponentDrawing_graphConnected {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S)
    (hjoin : G.ArcsJoinEndpoints)
    (C : (edgeSetSimpleGraph G S E).ConnectedComponent) :
    (edgeSetDrawing G
      (edgeSetComponentVertexSet G C)
      (edgeSetComponentEdgeSet G hE C)
      (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C)).GraphConnected := by
  classical
  let H := edgeSetSimpleGraph G S E
  let Vc := edgeSetComponentVertexSet G C
  let Ec := edgeSetComponentEdgeSet G hE C
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C
  let D := edgeSetDrawing G Vc Ec hEc
  let R : ↥D.V → ↥D.V → Prop := fun a b =>
    ∃ e : Fin D.numEdges,
      ((D.endpoints e).1 = (a : ℝ × ℝ) ∧ (D.endpoints e).2 = (b : ℝ × ℝ)) ∨
      ((D.endpoints e).1 = (b : ℝ × ℝ) ∧ (D.endpoints e).2 = (a : ℝ × ℝ))
  change ∀ p q : ↥D.V, Relation.ReflTransGen R p q
  let toD : (p : ↥S) → p ∈ C.supp → ↥D.V := fun p hp =>
    ⟨(p : ℝ × ℝ), by
      change (p : ℝ × ℝ) ∈ Vc
      exact (mem_edgeSetComponentVertexSet (G := G) (C := C) (p := p)).mpr hp⟩
  have step_of_adj : ∀ {p q : ↥S} (hp : p ∈ C.supp)
      (hadj : H.Adj p q),
      R (toD p hp) (toD q ((SimpleGraph.ConnectedComponent.mem_supp_congr_adj C
        (by simpa [H] using hadj)).mp hp)) := by
    intro p q hp hadj
    have hq : q ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C (by simpa [H] using hadj)).mp hp
    obtain ⟨e, heEc, hends⟩ :=
      exists_mem_edgeSetComponentEdgeSet_of_adj G hE hp (by simpa [H] using hadj)
    let i : Fin D.numEdges := by
      change Fin Ec.card
      exact Finset.equivFin Ec ⟨e, heEc⟩
    refine ⟨i, ?_⟩
    rcases hends with hends | hends
    · left
      constructor <;> simp [D, edgeSetDrawing, Ec, i, hends, toD]
    · right
      constructor <;> simp [D, edgeSetDrawing, Ec, i, hends, toD]
  have walk_to_drawing : ∀ {p q : ↥S} (w : H.Walk p q)
      (hp : p ∈ C.supp) (hq : q ∈ C.supp),
      Relation.ReflTransGen R (toD p hp) (toD q hq) := by
    intro p q w
    induction w with
    | nil =>
        intro hp hq
        convert Relation.ReflTransGen.refl
    | cons hadj tail ih =>
        intro hp hr
        have hq : _ ∈ C.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C (by simpa [H] using hadj)).mp hp
        exact (Relation.ReflTransGen.single (step_of_adj hp hadj)).trans (ih hq hr)
  intro p q
  have hpVc : (p : ℝ × ℝ) ∈ Vc := by
    simp [D, edgeSetDrawing]
  have hqVc : (q : ℝ × ℝ) ∈ Vc := by
    simp [D, edgeSetDrawing]
  let pS : ↥S := ⟨(p : ℝ × ℝ), edgeSetComponentVertexSet_subset G C hpVc⟩
  let qS : ↥S := ⟨(q : ℝ × ℝ), edgeSetComponentVertexSet_subset G C hqVc⟩
  have hpC : pS ∈ C.supp :=
    (mem_edgeSetComponentVertexSet (G := G) (C := C) (p := pS)).mp hpVc
  have hqC : qS ∈ C.supp :=
    (mem_edgeSetComponentVertexSet (G := G) (C := C) (p := qS)).mp hqVc
  obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.reachable_of_mem_supp C hpC hqC
  simpa [pS, qS, toD, D, Vc] using walk_to_drawing w hpC hqC

/-- The canonical component edge sets partition `E` by cardinality. -/
theorem edgeSetComponentEdgeSet_card_sum {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} (hE : E ⊆ edgeSetOn G S) :
    E.card =
      ∑ C : (edgeSetSimpleGraph G S E).ConnectedComponent,
        (edgeSetComponentEdgeSet G hE C).card := by
  classical
  let H := edgeSetSimpleGraph G S E
  let f : ↥E → H.ConnectedComponent := edgeSetComponentOf G hE
  have hmaps : Set.MapsTo f (↑(Finset.univ : Finset ↥E))
      (↑(Finset.univ : Finset H.ConnectedComponent)) := by
    intro e _he
    exact Finset.mem_univ _
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at hfib
  have hfiber : ∀ C : H.ConnectedComponent,
      ((Finset.univ : Finset ↥E).filter fun e => f e = C).card =
        (edgeSetComponentEdgeSet G hE C).card := by
    intro C
    simp [edgeSetComponentEdgeSet, f]
  rw [← Fintype.card_coe E, hfib]
  convert Finset.sum_congr rfl (by intro C _; exact hfiber C)

/-- The canonical component vertex sets partition `S` by cardinality. -/
theorem edgeSetComponentVertexSet_card_sum {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin G.numEdges)} :
    (∑ C : (edgeSetSimpleGraph G S E).ConnectedComponent,
        (edgeSetComponentVertexSet G C).card) = S.card := by
  classical
  let H := edgeSetSimpleGraph G S E
  let f : ↥S → H.ConnectedComponent := H.connectedComponentMk
  have hmaps : Set.MapsTo f (↑(Finset.univ : Finset ↥S))
      (↑(Finset.univ : Finset H.ConnectedComponent)) := by
    intro p _hp
    exact Finset.mem_univ _
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at hfib
  have hfiber : ∀ C : H.ConnectedComponent,
      ((Finset.univ : Finset ↥S).filter fun p => f p = C).card =
        (edgeSetComponentVertexSet G C).card := by
    intro C
    simp [edgeSetComponentVertexSet, f, H]
  rw [← Fintype.card_coe S, hfib]
  convert Finset.sum_congr rfl (by intro C _; exact (hfiber C).symm)

/-- A genus-zero simple planarization witness for the restricted drawing
transfers to the existing surviving-edge-set carrier `abstractizeEdgeSet`.

The two carriers have the same vertex type `↥S`; their edge types differ only by
the canonical enumeration `Finset.equivFin E`, and the set of unordered endpoint
pairs is identical. -/
theorem abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing
    {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)} {hE : E ⊆ edgeSetOn G S}
    (hpl : HasGenusZeroSimplePlanarization (abstractize (edgeSetDrawing G S E hE))) :
    HasGenusZeroSimplePlanarization (abstractizeEdgeSet G S E hE) := by
  classical
  let H := edgeSetDrawing G S E hE
  rcases hpl with ⟨D, hD, Mp, hs, hc, hp, hv, hedge⟩
  refine ⟨D, hD, Mp, hs, hc, hp, ?_, ?_⟩
  · simpa [H, edgeSetDrawing, abstractize, abstractizeEdgeSet] using hv
  · have himage :
        Finset.univ.image (abstractizeEdgeSet G S E hE).edgeVerts =
          Finset.univ.image (abstractize H).edgeVerts := by
      apply Finset.ext
      intro uv
      constructor
      · intro huv
        obtain ⟨e, _he, huv_eq⟩ := Finset.mem_image.mp huv
        exact Finset.mem_image.mpr
          ⟨Finset.equivFin E e, Finset.mem_univ _, by
            rw [← huv_eq]
            simp [H, edgeSetDrawing, abstractize, abstractizeEdgeSet]⟩
      · intro huv
        obtain ⟨i, _hi, huv_eq⟩ := Finset.mem_image.mp huv
        exact Finset.mem_image.mpr
          ⟨(Finset.equivFin E).symm i, Finset.mem_univ _, by
            rw [← huv_eq]
            simp [H, edgeSetDrawing, abstractize, abstractizeEdgeSet]⟩
    rw [himage]
    exact hedge

/-- If every nondegenerate crossing-free restricted drawing has a genus-zero
simple planarization after forgetting to `abstractize`, then the large
crossing-free planarization hypothesis used by the amplification layer follows.

This is the bookkeeping bridge from the drawing-level restricted object
`edgeSetDrawing` back to the pre-existing `abstractizeEdgeSet` statement. -/
theorem independentSimpleCrossingFreePlanarizationLarge_of_edgeSetDrawing_planarization
    (hpl : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      G.CrossingsAreIndependent →
      G.WellDrawn →
      ∀ S : Finset (ℝ × ℝ), S ⊆ G.V → 3 ≤ S.card →
        ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
          NoCrossingPairsInEdgeSet G E →
            HasGenusZeroSimplePlanarization (abstractize (edgeSetDrawing G S E hE))) :
    IndependentSimpleCrossingFreePlanarizationLarge := by
  intro G hmult hjoin hcross hwd S hS hv E hE hfree
  exact abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing G
    (hpl G hmult hjoin hcross hwd S hS hv E hE hfree)

/-- Componentwise residual-map data owed for crossing-free restricted drawings.

This is the disconnected form of the residual-map endpoint.  A crossing-free
survivor `E` is decomposed into components `Ec i` supported on vertex sets
`Vc i`; for each nondegenerate component, the restricted drawing has a
rotation-regular connected residual map of genus zero.  The cardinality fields
are the finite bookkeeping needed to sum the component edge bounds. -/
def EdgeSetDrawingResidualMapComponentwisePlanarization : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), ∀ _hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          ∃ (ι : Type) (_ : Fintype ι), ∃ Vc : ι → Finset (ℝ × ℝ),
            ∃ Ec : ι → Finset (Fin G.numEdges),
              E.card = ∑ i, (Ec i).card ∧
              (∑ i, (Vc i).card) ≤ S.card ∧
              (∀ i, Vc i ⊆ S) ∧
              (∀ i, ∃ hEc : Ec i ⊆ edgeSetOn G (Vc i),
                3 ≤ (Vc i).card →
                  ∃ hARR : ArcsRotationRegular (edgeSetDrawing G (Vc i) (Ec i) hEc),
                    (edgeSetDrawing G (Vc i) (Ec i) hEc).GraphConnected ∧
                      (residualMap (edgeSetDrawing G (Vc i) (Ec i) hEc) hARR).IsPlanar)

/-- Residual-map data for the canonical components of a crossing-free surviving
edge set.

This specializes the componentwise residual-map obligation to the connected
components of the simple graph generated by the surviving edges.  It is the
faithful Lean form of the component decomposition used before applying
Pach--Tóth, *A crossing lemma for multigraphs*, Lemma 2.1 / Corollary 2.2. -/
def EdgeSetDrawingResidualMapCanonicalComponentPlanarization : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    (hjoin : G.ArcsJoinEndpoints) →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          ∀ C : (edgeSetSimpleGraph G S E).ConnectedComponent,
            3 ≤ (edgeSetComponentVertexSet G C).card →
              ∃ hARR : ArcsRotationRegular
                (edgeSetDrawing G
                  (edgeSetComponentVertexSet G C)
                  (edgeSetComponentEdgeSet G hE C)
                  (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C)),
                (edgeSetDrawing G
                  (edgeSetComponentVertexSet G C)
                  (edgeSetComponentEdgeSet G hE C)
                  (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C)).GraphConnected ∧
                (residualMap
                  (edgeSetDrawing G
                    (edgeSetComponentVertexSet G C)
                    (edgeSetComponentEdgeSet G hE C)
                    (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C))
                  hARR).IsPlanar

/-- Residual-map planarity data for the canonical components of a crossing-free
surviving edge set.

Compared with `EdgeSetDrawingResidualMapCanonicalComponentPlanarization`, this
does not ask for graph-connectedness: that is a finite graph-theoretic consequence
of using the canonical connected components and is supplied by
`edgeSetComponentDrawing_graphConnected`.  The remaining data are the genuine
drawing-to-map obligations: ARR and genus-zero residual-map planarity. -/
def EdgeSetDrawingResidualMapCanonicalComponentPlanarity : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    (hjoin : G.ArcsJoinEndpoints) →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          ∀ C : (edgeSetSimpleGraph G S E).ConnectedComponent,
            3 ≤ (edgeSetComponentVertexSet G C).card →
              ∃ hARR : ArcsRotationRegular
                (edgeSetDrawing G
                  (edgeSetComponentVertexSet G C)
                  (edgeSetComponentEdgeSet G hE C)
                  (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C)),
                (residualMap
                  (edgeSetDrawing G
                    (edgeSetComponentVertexSet G C)
                    (edgeSetComponentEdgeSet G hE C)
                    (edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C))
                  hARR).IsPlanar

/-- **Crossing-free residual-map planarity.**

This is the clean topological endpoint behind the planar-map/Euler step in
Pach--Tóth, *A crossing lemma for multigraphs*: a connected simple topological
graph drawn without crossings determines a genus-zero residual combinatorial
map. The formal statement packages the remaining drawing-to-map work as ARR
plus the Euler-form planarity assertion `M.eulerCharacteristic = 2`. -/
def CrossingFreeResidualMapPlanarity : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    CrossingFree G →
    G.GraphConnected →
    3 ≤ G.V.card →
      ∃ hARR : ArcsRotationRegular G, (residualMap G hARR).IsPlanar

/-- **Crossing-free local rotation regularity.**

This is the formal residue of the locally-starlike/tame-drawing part of
Pach--Tóth's topological setup: a connected simple crossing-free drawing has a
well-defined local cyclic order of incident edge-ends at every vertex.  The
present `DrawnMultigraph` carrier stores arbitrary simple continuous arcs, so
this is kept as an explicit theorem-surface rather than folded into the
definition of drawing. -/
def CrossingFreeArcsRotationRegular : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    CrossingFree G →
    G.GraphConnected →
    3 ≤ G.V.card →
      ArcsRotationRegular G

/-- **Crossing-free residual-map planarity once the rotation system is known.**

This is the genus-zero/Euler-map part of Pach--Tóth, *A crossing lemma for
multigraphs*, Lemma 2.1: after the local rotation system has been obtained, the
residual combinatorial map of a connected crossing-free simple topological
drawing is planar, i.e. has Euler characteristic `2`. -/
def CrossingFreeResidualMapPlanarityOfARR : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    CrossingFree G →
    G.GraphConnected →
    3 ≤ G.V.card →
    ∀ hARR : ArcsRotationRegular G,
      (residualMap G hARR).IsPlanar

/-- To prove crossing-free residual-map planarity, it is enough to prove it
after reindexing the edges by a convenient permutation depending on the drawing
and the chosen ARR witness.

This isolates the bookkeeping issue caused by canonical `Finset.equivFin`
enumerations: any future insertion-order or literature-faithful edge order may
be used to prove genus-zero residual-map planarity, then transported back to the
original drawing by `residualMap_isPlanar_permuteEdges_iff`. -/
theorem crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity
    (hperm : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      CrossingFree G →
      G.GraphConnected →
      3 ≤ G.V.card →
      ∀ hARR : ArcsRotationRegular G,
        ∃ π : Equiv.Perm (Fin G.numEdges),
          (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegular G π hARR)).IsPlanar) :
    CrossingFreeResidualMapPlanarityOfARR := by
  intro G hmult hjoin hcross hconn hv hARR
  obtain ⟨π, hplanarπ⟩ := hperm G hmult hjoin hcross hconn hv hARR
  exact (residualMap_isPlanar_permuteEdges_iff (G := G) π hjoin hARR).mp hplanarπ

/-- The faithful two-piece topological endpoint implies the bundled
crossing-free residual-map endpoint. -/
theorem crossingFreeResidualMapPlanarity_of_arr_planarity
    (hrot : CrossingFreeArcsRotationRegular)
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    CrossingFreeResidualMapPlanarity := by
  intro G hmult hjoin hcross hconn hv
  let hARR : ArcsRotationRegular G := hrot G hmult hjoin hcross hconn hv
  exact ⟨hARR, hplanar G hmult hjoin hcross hconn hv hARR⟩

/-- The ordered-insertion route implies crossing-free residual-map planarity.

This is the formal tree/cotree skeleton for the planar-map part of the
crossing-free endpoint: choose an edge order, provide ARR witnesses for all
ordered prefixes, and prove every step after the first edge is either a
leaf insertion or a same-face insertion of residual maps. -/
theorem crossingFreeResidualMapPlanarity_of_prefix_insertions
    (hinsert : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      CrossingFree G →
      G.GraphConnected →
      3 ≤ G.V.card →
        ∃ hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
          ArcsRotationRegular (G.prefixEdges m hm),
          ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), 1 ≤ m →
            ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
              (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')) :
    CrossingFreeResidualMapPlanarity := by
  intro G hmult hjoin hcross hconn hv
  obtain ⟨hARR, hstep⟩ := hinsert G hmult hjoin hcross hconn hv
  exact exists_residualMap_isPlanar_of_prefix_insertions_connected
    (G := G) hjoin hconn hv hARR hstep

set_option maxHeartbeats 800000 in
/-- The ordered-insertion route may be proved after reindexing the edges by a
convenient permutation.

This is the form closest to the usual literature proof: choose an edge order,
verify each prefix step is a leaf insertion or a same-face insertion in that
order, and then transport the resulting residual-map planarity back to the
original edge enumeration. -/
theorem crossingFreeResidualMapPlanarity_of_permuted_prefix_insertions
    (hinsert : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      CrossingFree G →
      G.GraphConnected →
      3 ≤ G.V.card →
        ∃ π : Equiv.Perm (Fin G.numEdges),
          ∃ hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
            ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm),
            ∀ (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges), 1 ≤ m →
              ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
                m (Nat.le_of_succ_le hm') hm'
                (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')) :
    CrossingFreeResidualMapPlanarity := by
  intro G hmult hjoin hcross hconn hv
  obtain ⟨π, hARRprefix, hstep⟩ := hinsert G hmult hjoin hcross hconn hv
  have hjoinπ : (G.permuteEdges π).ArcsJoinEndpoints :=
    permuteEdges_arcsJoinEndpoints (G := G) π hjoin
  have hconnπ : (G.permuteEdges π).GraphConnected :=
    (DrawnMultigraph.permuteEdges_graphConnected_iff G π).2 hconn
  have hvπ : 3 ≤ (G.permuteEdges π).V.card := by
    simpa [DrawnMultigraph.permuteEdges] using hv
  obtain ⟨hARRπ, hplanarπ⟩ :=
    exists_residualMap_isPlanar_of_prefix_insertions_connected
      (G := G.permuteEdges π) hjoinπ hconnπ hvπ hARRprefix hstep
  let H := (G.permuteEdges π).permuteEdges π.symm
  have hH : H = G := DrawnMultigraph.permuteEdges_symm G π
  let hARRH : ArcsRotationRegular H :=
    permuteEdges_arrRotationRegular (G.permuteEdges π) π.symm hARRπ
  have hplanarH : (residualMap H hARRH).IsPlanar := by
    exact (residualMap_isPlanar_permuteEdges_iff
      (G := G.permuteEdges π) π.symm hjoinπ hARRπ).2 hplanarπ
  refine ⟨hH ▸ hARRH, ?_⟩
  exact hH.rec hplanarH

/-- The clean crossing-free residual-map endpoint supplies the canonical
component planarity endpoint used by the deletion/amplification layer. -/
theorem edgeSetDrawingResidualMapCanonicalComponentPlanarity_of_crossingFree
    (hres : CrossingFreeResidualMapPlanarity) :
    EdgeSetDrawingResidualMapCanonicalComponentPlanarity := by
  intro G hmult hjoin hcross _hwd S _hS E hE hfree C hv
  let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C
  let D := edgeSetDrawing G (edgeSetComponentVertexSet G C)
    (edgeSetComponentEdgeSet G hE C) hEc
  have hEc_sub : edgeSetComponentEdgeSet G hE C ⊆ E :=
    edgeSetComponentEdgeSet_subset_edges G hE C
  have hfreeC : NoCrossingPairsInEdgeSet G (edgeSetComponentEdgeSet G hE C) :=
    NoCrossingPairsInEdgeSet.mono G hEc_sub hfree
  have hDmult : ∀ p q, D.multiplicity p q ≤ 1 := by
    simpa [D] using edgeSetDrawing_multiplicity_le (G := G) (hE := hEc) hmult
  have hDjoin : D.ArcsJoinEndpoints := by
    simpa [D] using edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc) hjoin
  have hDcross : CrossingFree D := by
    simpa [D] using edgeSetDrawing_crossingFree_of_noCrossingPairs
      (G := G) (hE := hEc) hcross hfreeC
  have hDconn : D.GraphConnected := by
    simpa [D, hEc] using edgeSetComponentDrawing_graphConnected G hE hjoin C
  have hDverts : 3 ≤ D.V.card := by
    simpa [D, edgeSetDrawing] using hv
  exact hres D hDmult hDjoin hDcross hDconn hDverts

/-- The split ARR + genus-zero endpoint supplies the canonical component
planarity endpoint used by the deletion/amplification layer. -/
theorem edgeSetDrawingResidualMapCanonicalComponentPlanarity_of_crossingFree_arr_planarity
    (hrot : CrossingFreeArcsRotationRegular)
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    EdgeSetDrawingResidualMapCanonicalComponentPlanarity :=
  edgeSetDrawingResidualMapCanonicalComponentPlanarity_of_crossingFree
    (crossingFreeResidualMapPlanarity_of_arr_planarity hrot hplanar)

/-- Canonical-component residual-map planarity gives the canonical-component
planarization endpoint because each canonical component drawing is
graph-connected. -/
theorem edgeSetDrawingResidualMapCanonicalComponentPlanarization_of_planarity
    (hres : EdgeSetDrawingResidualMapCanonicalComponentPlanarity) :
    EdgeSetDrawingResidualMapCanonicalComponentPlanarization := by
  intro G hmult hjoin hcross hwd S hS E hE hfree C hv
  obtain ⟨hARR, hplanar⟩ := hres G hmult hjoin hcross hwd S hS E hE hfree C hv
  exact ⟨hARR, edgeSetComponentDrawing_graphConnected G hE hjoin C, hplanar⟩

/-- Canonical-component residual-map data gives the componentwise residual-map
endpoint by taking the component index to be the connected components of the
surviving-edge simple graph. -/
theorem edgeSetDrawingResidualMapComponentwisePlanarization_of_canonical_components
    (hcanon : EdgeSetDrawingResidualMapCanonicalComponentPlanarization) :
    EdgeSetDrawingResidualMapComponentwisePlanarization := by
  intro G hmult hjoin hcross hwd S hS E hE hfree
  refine ⟨(edgeSetSimpleGraph G S E).ConnectedComponent, inferInstance,
    edgeSetComponentVertexSet G, edgeSetComponentEdgeSet G hE, ?_, ?_, ?_, ?_⟩
  · exact edgeSetComponentEdgeSet_card_sum G hE
  · exact (edgeSetComponentVertexSet_card_sum (G := G) (S := S) (E := E)).le
  · intro C
    exact edgeSetComponentVertexSet_subset G C
  · intro C
    let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE hjoin C
    refine ⟨hEc, ?_⟩
    intro hv
    exact hcanon G hmult hjoin hcross hwd S hS E hE hfree C hv

/-- Componentwise residual-map witnesses imply the componentwise crossing-free
planarization hypothesis used by the amplification layer. -/
theorem independentSimpleCrossingFreeComponentwisePlanarization_of_edgeSetDrawing_residualMap
    (hres : EdgeSetDrawingResidualMapComponentwisePlanarization) :
    IndependentSimpleCrossingFreeComponentwisePlanarization := by
  intro G hmult hjoin hcross hwd S hS E hE hfree
  obtain ⟨ι, hι, Vc, Ec, hEcard, hVsum, hVsub, hpieces⟩ :=
    hres G hmult hjoin hcross hwd S hS E hE hfree
  refine ⟨ι, hι, Vc, Ec, hEcard, hVsum, hVsub, ?_⟩
  intro i
  rcases hpieces i with ⟨hEc, hres_i⟩
  refine ⟨hEc, ?_⟩
  intro hv
  obtain ⟨hARR, hconn, hplanar⟩ := hres_i hv
  let H := edgeSetDrawing G (Vc i) (Ec i) hEc
  have hplH : HasGenusZeroSimplePlanarization (abstractize H) := by
    exact has_genus_zero_simple_planarization_of_residual_map H hARR
      (edgeSetDrawing_arcsJoinEndpoints G hjoin)
      (edgeSetDrawing_multiplicity_le G hmult)
      hconn
      (by simpa [H, edgeSetDrawing] using hv)
      hplanar
  exact abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing G hplH

/-- Residual-map data owed for every nondegenerate crossing-free restricted
drawing.

For each surviving edge set `E` on a vertex sample `S`, this asks for the
rotation-regular residual map of `edgeSetDrawing G S E hE` to be connected and
genus zero.  This is the residual-map version of the remaining drawing-to-faces
content before the Euler edge bound can be applied. -/
def EdgeSetDrawingResidualMapPlanarizationLarge : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V → 3 ≤ S.card →
      ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          ∃ hARR : ArcsRotationRegular (edgeSetDrawing G S E hE),
            (edgeSetDrawing G S E hE).GraphConnected ∧
              (residualMap (edgeSetDrawing G S E hE) hARR).IsPlanar

/-- To prove residual-map witnesses for every nondegenerate crossing-free
restricted drawing, it is enough to prove them after reindexing the surviving
edges by a convenient permutation depending on that restricted drawing and its
chosen ARR witness.

This is the restricted-drawing analogue of
`crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity`: the remaining
literature-faithful task may choose any insertion order on
`edgeSetDrawing G S E hE`, prove residual-map planarity there, and transport the
result back to the canonical `Finset.equivFin` enumeration. -/
theorem edgeSetDrawingResidualMapPlanarizationLarge_of_permuted_planarity
    (hperm : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      G.CrossingsAreIndependent →
      G.WellDrawn →
      ∀ S : Finset (ℝ × ℝ), S ⊆ G.V → 3 ≤ S.card →
        ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
          NoCrossingPairsInEdgeSet G E →
            ∃ hARR : ArcsRotationRegular (edgeSetDrawing G S E hE),
              (edgeSetDrawing G S E hE).GraphConnected ∧
                ∃ π : Equiv.Perm (Fin (edgeSetDrawing G S E hE).numEdges),
                  (residualMap
                    ((edgeSetDrawing G S E hE).permuteEdges π)
                    (permuteEdges_arrRotationRegular
                      (edgeSetDrawing G S E hE) π hARR)).IsPlanar) :
    EdgeSetDrawingResidualMapPlanarizationLarge := by
  intro G hmult hjoin hcross hwd S hS hv E hE hfree
  let H := edgeSetDrawing G S E hE
  have hpermH := hperm G hmult hjoin hcross hwd S hS hv E hE hfree
  rcases hpermH with ⟨hARR, hconn, π, hplanarπ⟩
  refine ⟨hARR, hconn, ?_⟩
  exact (residualMap_isPlanar_permuteEdges_iff
    (G := H) π (edgeSetDrawing_arcsJoinEndpoints G hjoin) hARR).mp hplanarπ

/-- Residual-map witnesses for every nondegenerate crossing-free restricted
drawing imply the large crossing-free planarization hypothesis.

The hypotheses expose the exact remaining residual-map tasks for the restricted
drawing `edgeSetDrawing G S E hE`: construct an `ArcsRotationRegular` witness,
show the residual map is connected as a graph map, and prove its genus-zero
planarity. The already-proved residual-map bookkeeping then supplies the
`HasGenusZeroSimplePlanarization` witness consumed by the Euler edge bound. -/
theorem independentSimpleCrossingFreePlanarizationLarge_of_edgeSetDrawing_residualMap
    (hres : EdgeSetDrawingResidualMapPlanarizationLarge) :
    IndependentSimpleCrossingFreePlanarizationLarge := by
  intro G hmult hjoin hcross hwd S hS hv E hE hfree
  let H := edgeSetDrawing G S E hE
  obtain ⟨hARR, hconn, hplanar⟩ := hres G hmult hjoin hcross hwd S hS hv E hE hfree
  have hplH : HasGenusZeroSimplePlanarization (abstractize H) := by
    exact has_genus_zero_simple_planarization_of_residual_map H hARR
      (edgeSetDrawing_arcsJoinEndpoints G hjoin)
      (edgeSetDrawing_multiplicity_le G hmult)
      hconn
      (by simpa [H, edgeSetDrawing] using hv)
      hplanar
  exact abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing G hplH

end CrossingLemma
