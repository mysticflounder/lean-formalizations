/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Foundations
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.RotationRegular
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.PrefixSplice
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.CanonicalComponent

/-!
# Szemerédi–Trotter — Conclusions & grid interface (shard 5 of 5)

The deduction chain `szemerediTrotter_of_*` packaging the incidence bound under
each available planar/crossing-lemma hypothesis, and the rich-line interface for
the grid `A × A` (`gridRichLine_of_*`).  Imports all four preceding shards
(linear chain).
-/

set_option linter.style.longLine false

namespace PachSharir.SzemerediTrotter

open scoped Classical
open CrossingLemma

/-- **Geometric genus-zero residual for the component straight-line drawing
(now derived combinatorially from the main theorem above).**

Previously this was an irreducible `sorry` (Euler `≥ 2` via Jordan content).
After de-circularizing the proof of
`straightLineCanonicalComponentResidualMapPlanarityOfARR`, this lemma is a
trivial corollary. -/
private theorem stComponentDrawing_residualMap_isPlanar_geometricResidual
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (hfree : NoCrossingPairsInEdgeSet (stMultigraph P L) E)
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (hv : 3 ≤ (edgeSetComponentVertexSet (stMultigraph P L) C).card) :
    (residualMap (stComponentDrawing P L S E hE C)
      (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).IsPlanar :=
  straightLineCanonicalComponentResidualMapPlanarityOfARR P L hL S hS E hE hfree C hv

/-- Componentwise genus-zero planarization for crossing-free straight-line
survivors gives the numerical straight-line crossing-free edge bound. -/
theorem straightLineCrossingFreeEdgeBound_of_componentwise_planarization
    (hpl : StraightLineCrossingFreeComponentwisePlanarization) :
    StraightLineCrossingFreeEdgeBound := by
  intro P L hL S hS E hE hfree
  exact edge_card_le_three_mul_vertices_of_componentwise_planarization
    (G := stMultigraph P L) (S := S) (E := E)
    (stMultigraph_multiplicity_le_one P L hL)
    (hpl P L hL S hS E hE hfree)

/-- Componentwise genus-zero planarization also gives the nondegenerate
straight-line crossing-free edge bound. -/
theorem straightLineCrossingFreeEdgeBoundLarge_of_componentwise_planarization
    (hpl : StraightLineCrossingFreeComponentwisePlanarization) :
    StraightLineCrossingFreeEdgeBoundLarge := by
  intro P L hL S hS _hv E hE hfree
  exact (straightLineCrossingFreeEdgeBound_of_componentwise_planarization hpl)
    P L hL S hS E hE hfree

/-- The nondegenerate straight-line crossing-free edge bound implies the full
straight-line crossing-free edge bound.  If `|S| ≤ 2`, multiplicity one injects
the surviving edge set into endpoint pairs in `S`, giving
`|E| ≤ |S|² ≤ 3 |S|`. -/
theorem straightLineCrossingFreeEdgeBound_of_large
    (hlarge : StraightLineCrossingFreeEdgeBoundLarge) :
    StraightLineCrossingFreeEdgeBound := by
  intro P L hL S hS E hE hfree
  by_cases hv : 3 ≤ S.card
  · exact hlarge P L hL S hS hv E hE hfree
  · have hsmall : S.card ≤ 2 := by omega
    have hEcard : E.card ≤ (edgeSetOn (stMultigraph P L) S).card :=
      Finset.card_le_card hE
    have hedgeSq := edgeSetOn_card_le_sq_of_multiplicity_one (stMultigraph P L) S
      (stMultigraph_multiplicity_le_one P L hL)
    calc
      E.card ≤ (edgeSetOn (stMultigraph P L) S).card := hEcard
      _ ≤ S.card ^ 2 := hedgeSq
      _ ≤ 3 * S.card := by nlinarith

/-- **Straight-line induced weak bound.**

For the straight-segment incidence graph, every induced vertex set satisfies
`edgesOn S ≤ crossingsOn S + 3 |S|`.  This is the deterministic
one-edge-per-crossing deletion step in the ACNS/Leighton proof, specialized to
`stMultigraph`. -/
def StraightLineInducedWeakBound : Prop :=
  ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
    (∀ ℓ ∈ L, IsAffineLine ℓ) →
    ∀ S : Finset (ℝ × ℝ), S ⊆ (stMultigraph P L).V →
      edgesOn (stMultigraph P L) S ≤ crossingsOn (stMultigraph P L) S + 3 * S.card

/-- The straight-line crossing-free edge bound gives the straight-line induced
weak bound by deleting one edge from every surviving crossing pair. -/
theorem straightLineInducedWeakBound_of_crossingFreeEdgeBound
    (hplanar : StraightLineCrossingFreeEdgeBound) :
    StraightLineInducedWeakBound := by
  intro P L hL S hS
  let G := stMultigraph P L
  have hdelete := edgesOn_le_remainingEdgeSet_card_add_crossingsOn G S
  have hrem := hplanar P L hL S hS
    (remainingEdgeSet G S)
    (remainingEdgeSet_subset_edgeSetOn G S)
    (remainingEdgeSet_noCrossingPairs G S)
  calc
    edgesOn G S ≤ (remainingEdgeSet G S).card + crossingsOn G S := hdelete
    _ ≤ 3 * S.card + crossingsOn G S := Nat.add_le_add_right hrem _
    _ = crossingsOn G S + 3 * S.card := by omega

/-- The straight-line induced weak bound implies the local averaged weak bound
for the straight-segment incidence graph. -/
theorem localWeakAveragedBound_stMultigraph_of_straightLineInducedWeakBound
    (hweak : StraightLineInducedWeakBound)
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    LocalSimpleWeakAveragedBound (stMultigraph P L) :=
  localSimpleWeakAveragedBound_of_inducedWeakBound
    (stMultigraph_arcsJoinEndpoints P L)
    (stMultigraph_wellDrawn P L hL)
    (hweak P L hL)

/-- The straight-line induced weak bound gives the cubed crossing inequality for
the straight-segment incidence graph in the high-edge regime. -/
theorem stMultigraph_crossingBound_of_straightLineInducedWeakBound
    (hweak : StraightLineInducedWeakBound)
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    (hthresh : 4 * (stMultigraph P L).V.card ≤ (stMultigraph P L).numEdges) :
    (stMultigraph P L).numEdges ^ 3 ≤
      64 * (stMultigraph P L).V.card ^ 2 * (stMultigraph P L).crossings :=
  simpleCrossingBound_of_localWeakAveragedBound
    (localWeakAveragedBound_stMultigraph_of_straightLineInducedWeakBound hweak P L hL)
    hthresh

/-- **Szemerédi--Trotter from the straight-line induced weak bound.**

This bypasses any arbitrary-drawing crossing lemma: the only remaining
geometric input is the local induced weak inequality for the actual
straight-segment incidence graph. -/
theorem szemerediTrotter_of_straightLineInducedWeakBound
    (hweak : StraightLineInducedWeakBound) :
    SzemerediTrotterStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro P L hL
  exact incidence_bound_of_crossingBound
    (incidences P L) P.card L.card (stMultigraph P L)
    (stMultigraph_card_V P L)
    (incidences_le_numEdges_add P L hL)
    (stMultigraph_crossings_le P L)
    (fun hthresh =>
      stMultigraph_crossingBound_of_straightLineInducedWeakBound hweak P L hL hthresh)

/-- **Szemerédi--Trotter from the straight-line crossing-free edge bound.** -/
theorem szemerediTrotter_of_straightLineCrossingFreeEdgeBound
    (hplanar : StraightLineCrossingFreeEdgeBound) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_straightLineInducedWeakBound
    (straightLineInducedWeakBound_of_crossingFreeEdgeBound hplanar)

/-- **Szemerédi--Trotter from the nondegenerate straight-line crossing-free edge
bound.** -/
theorem szemerediTrotter_of_straightLineCrossingFreeEdgeBoundLarge
    (hlarge : StraightLineCrossingFreeEdgeBoundLarge) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_straightLineCrossingFreeEdgeBound
    (straightLineCrossingFreeEdgeBound_of_large hlarge)

/-- **Szemerédi--Trotter from the straight-line componentwise planarization
layer.** -/
theorem szemerediTrotter_of_straightLineCrossingFreeComponentwisePlanarization
    (hpl : StraightLineCrossingFreeComponentwisePlanarization) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_straightLineCrossingFreeEdgeBound
    (straightLineCrossingFreeEdgeBound_of_componentwise_planarization hpl)

/-- **Szemerédi–Trotter**, conditional on the simple crossing lemma `hCL`.

Assembled from the Phase-1 combinatorial core `incidence_bound_of_crossingLemma`
and the geometric realization `stMultigraph` with its six discharged hypotheses
(`stMultigraph_card_V`, `stMultigraph_multiplicity_le_one`, `stMultigraph_arcsJoinEndpoints`,
`stMultigraph_wellDrawn`, `incidences_le_numEdges_add`, `stMultigraph_crossings_le`) — all
PROVEN sorry-free.
So this is Szemerédi–Trotter conditional on the simple crossing lemma alone; the
`hCL` hypothesis threads the crossing lemma at the type level (no `sorryAx`).

Axiom audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem szemerediTrotter_of_simpleCrossingLemma
    (hCL : SimpleCrossingLemmaStatement) :
    SzemerediTrotterStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro P L hL
  exact incidence_bound_of_crossingLemma hCL
    (incidences P L) P.card L.card (stMultigraph P L)
    (stMultigraph_card_V P L)
    (stMultigraph_multiplicity_le_one P L hL)
    (stMultigraph_arcsJoinEndpoints P L)
    (stMultigraph_wellDrawn P L hL)
    (incidences_le_numEdges_add P L hL)
    (stMultigraph_crossings_le P L)

/-- **Szemerédi–Trotter**, conditional on the independent-drawing simple
crossing lemma. This is the drawing-level layer matched to the
ACNS/Leighton `p^4` amplification, since `stMultigraph` has independent
crossings. -/
theorem szemerediTrotter_of_independentSimpleCrossingLemma
    (hCL : IndependentSimpleCrossingLemmaStatement) :
    SzemerediTrotterStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro P L hL
  exact incidence_bound_of_independentCrossingLemma hCL
    (incidences P L) P.card L.card (stMultigraph P L)
    (stMultigraph_card_V P L)
    (stMultigraph_multiplicity_le_one P L hL)
    (stMultigraph_arcsJoinEndpoints P L)
    (stMultigraph_crossingsAreIndependent P L hL)
    (stMultigraph_wellDrawn P L hL)
    (incidences_le_numEdges_add P L hL)
    (stMultigraph_crossings_le P L)

/-- **Szemerédi–Trotter**, conditional on the simple averaged weak crossing
bound. This is the faithful ACNS/Leighton random-subgraph layer specialized to
the simple graph surface used by the point-line construction. -/
theorem szemerediTrotter_of_simpleWeakAveragedBound
    (hweak : SimpleWeakAveragedBound) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_simpleCrossingLemma
    (simpleCrossingLemma_of_simpleWeakAveragedBound hweak)

/-- **Szemerédi–Trotter**, conditional on the independent simple averaged weak
bound. This is the closest current endpoint to the literal
ACNS/Leighton proof for the straight-line incidence graph. -/
theorem szemerediTrotter_of_independentSimpleWeakAveragedBound
    (hweak : IndependentSimpleWeakAveragedBound) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleCrossingLemma
    (independentSimpleCrossingLemma_of_independentSimpleWeakAveragedBound hweak)

/-- **Szemerédi–Trotter**, conditional on the independent simple induced weak
bound. This is the literature layering before Bernoulli averaging: for every
induced subdrawing, delete one edge per independent crossing and apply the
planar weak bound `e ≤ cr + 3v`. -/
theorem szemerediTrotter_of_independentSimpleInducedWeakBound
    (hweak : IndependentSimpleInducedWeakBound) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleWeakAveragedBound
    (independentSimpleWeakAveragedBound_of_inducedWeakBound hweak)

/-- **Szemerédi–Trotter**, conditional on the independent simple crossing-free
edge bound. This is the Pach--Tóth Corollary 2.2 layer: delete one edge from
each surviving crossing pair, then apply the planar edge bound to the
crossing-free remainder. -/
theorem szemerediTrotter_of_independentSimpleCrossingFreeEdgeBound
    (hplanar : IndependentSimpleCrossingFreeEdgeBound) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleInducedWeakBound
    (independentSimpleInducedWeakBound_of_crossingFreeEdgeBound hplanar)

/-- **Szemerédi–Trotter**, conditional on the componentwise independent simple
crossing-free planarization statement. This is the disconnected form of the
Pach--Tóth Lemma 2.1 planar step: decompose a crossing-free survivor into
connected components, apply the genus-zero simple edge bound on each
nondegenerate component, then sum. -/
theorem szemerediTrotter_of_independentSimpleCrossingFreeComponentwisePlanarization
    (hpl : IndependentSimpleCrossingFreeComponentwisePlanarization) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleCrossingFreeEdgeBound
    (independentSimpleCrossingFreeEdgeBound_of_componentwise_planarization hpl)

/-- **Szemerédi–Trotter**, conditional on componentwise residual-map witnesses
for crossing-free restricted drawings.  This is the residual-map-facing version
of the disconnected Pach--Tóth planar step. -/
theorem szemerediTrotter_of_edgeSetDrawingResidualMapComponentwisePlanarization
    (hres : EdgeSetDrawingResidualMapComponentwisePlanarization) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleCrossingFreeComponentwisePlanarization
    (independentSimpleCrossingFreeComponentwisePlanarization_of_edgeSetDrawing_residualMap hres)

/-- **Szemerédi–Trotter**, conditional on residual-map witnesses for the
canonical connected components of crossing-free restricted drawings. -/
theorem szemerediTrotter_of_edgeSetDrawingResidualMapCanonicalComponentPlanarization
    (hres : EdgeSetDrawingResidualMapCanonicalComponentPlanarization) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_edgeSetDrawingResidualMapComponentwisePlanarization
    (edgeSetDrawingResidualMapComponentwisePlanarization_of_canonical_components hres)

/-- **Szemerédi–Trotter**, conditional on ARR and residual-map planarity for the
canonical connected components of crossing-free restricted drawings.  The
component graph-connectedness side condition is proved by finite component
bookkeeping. -/
theorem szemerediTrotter_of_edgeSetDrawingResidualMapCanonicalComponentPlanarity
    (hres : EdgeSetDrawingResidualMapCanonicalComponentPlanarity) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_edgeSetDrawingResidualMapCanonicalComponentPlanarization
    (edgeSetDrawingResidualMapCanonicalComponentPlanarization_of_planarity hres)

/-- **Szemerédi–Trotter**, conditional on the clean crossing-free residual-map
planarity endpoint for connected simple topological graphs. -/
theorem szemerediTrotter_of_crossingFreeResidualMapPlanarity
    (hres : CrossingFreeResidualMapPlanarity) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_edgeSetDrawingResidualMapCanonicalComponentPlanarity
    (edgeSetDrawingResidualMapCanonicalComponentPlanarity_of_crossingFree hres)

/-- **Szemerédi–Trotter**, conditional on the split crossing-free topological
endpoint: local rotation regularity plus genus-zero residual-map planarity. -/
theorem szemerediTrotter_of_crossingFree_arr_planarity
    (hrot : CrossingFreeArcsRotationRegular)
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_crossingFreeResidualMapPlanarity
    (crossingFreeResidualMapPlanarity_of_arr_planarity hrot hplanar)

/-- **Szemerédi–Trotter**, conditional only on the genus-zero residual-map
planarity theorem once ARR is known: the straight-line incidence construction now
supplies the local rotation witness internally. -/
theorem szemerediTrotter_of_crossingFreeResidualMapPlanarityOfARR
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_straightLineCrossingFreeComponentwisePlanarization
    (straightLineCrossingFreeComponentwisePlanarization_of_crossingFreeResidualMapPlanarityOfARR
      hplanar)

/-- **Szemerédi–Trotter**, conditional on genus-zero residual-map planarity
after reindexing the edges of each connected crossing-free drawing by a
convenient permutation depending on the drawing and its ARR witness.

This is the exact bookkeeping reduction exposed by
`crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity`: future
insertion-order proofs may work in a literature-faithful edge order and then
transport planarity back to the original drawing. -/
theorem szemerediTrotter_of_crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity
    (hperm : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      CrossingFree G →
      G.GraphConnected →
      3 ≤ G.V.card →
      ∀ hARR : ArcsRotationRegular G,
        ∃ π : Equiv.Perm (Fin G.numEdges),
          (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegular G π hARR)).IsPlanar) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_crossingFreeResidualMapPlanarityOfARR
    (crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity hperm)

/-- **Szemerédi–Trotter**, conditional on a literature-order insertion proof for
the crossing-free residual-map endpoint.

This is the residual-map insertion form of Pach--Tóth, *A crossing lemma for
multigraphs*, Lemma 2.1: for each connected simple crossing-free drawing, choose
an edge order, supply ARR witnesses for all prefixes, and prove each successor
step is either a leaf insertion or a same-face insertion. -/
theorem szemerediTrotter_of_crossingFreeResidualMapPlanarity_of_permuted_prefix_insertions
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
    SzemerediTrotterStatement :=
  szemerediTrotter_of_crossingFreeResidualMapPlanarity
    (crossingFreeResidualMapPlanarity_of_permuted_prefix_insertions hinsert)

/-- **Szemerédi–Trotter**, conditional on the independent simple crossing-free
planarization statement. This exposes the remaining geometric content of the
ACNS/Leighton proof: crossing-free surviving edge sets admit genus-zero simple
planarizations, after which Euler gives the numerical edge bound. -/
theorem szemerediTrotter_of_independentSimpleCrossingFreePlanarization
    (hpl : IndependentSimpleCrossingFreePlanarization) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleCrossingFreeEdgeBound
    (independentSimpleCrossingFreeEdgeBound_of_planarization hpl)

/-- **Szemerédi–Trotter**, conditional on the nondegenerate independent simple
crossing-free planarization statement. This is the faithful planar layer used in
the literature: provide genus-zero simple planarizations only for `3 ≤ |S|`;
the `|S| ≤ 2` cases are handled by the multiplicity-one endpoint-pair
injection. -/
theorem szemerediTrotter_of_independentSimpleCrossingFreePlanarizationLarge
    (hpl : IndependentSimpleCrossingFreePlanarizationLarge) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_independentSimpleWeakAveragedBound
    (independentSimpleWeakAveragedBound_of_crossingFreePlanarizationLarge hpl)

/-- **Szemerédi–Trotter**, conditional on the bounded-multiplicity multigraph
crossing lemma. This compatibility wrapper specializes the multigraph statement
to `M = 1`, which is all the point-line construction uses. -/
theorem szemerediTrotter_of_crossingLemma
    (hCL : CrossingLemmaMultigraphStatement) :
    SzemerediTrotterStatement :=
  szemerediTrotter_of_simpleCrossingLemma
    (simpleCrossingLemma_of_multigraphCrossingLemma hCL)

/-! ## Rich-line interface for the grid `A × A`

The exact consequence of Szemerédi–Trotter the downstream needs (for **general**
`A ⊆ ℝ`): for the grid `P = A ×ˢ A`, the number of `k`-rich affine lines inside
any finite family `L` is `≲ |A|⁴ / k³`.  We state it rpow-free as
`k³ · #{rich} ≤ C · (|A|⁴ + k²·|A|²)`, which for `2 ≤ k ≤ |A|` is exactly
`#{rich} ≤ 2C · |A|⁴ / k³`.  Everything here is conditional on the crossing lemma,
inherited verbatim from `szemerediTrotter_of_crossingLemma`. -/

/-- The `k`-rich lines of the family `L` for the grid `A ×ˢ A`: those meeting the
grid in at least `k` points. -/
noncomputable def gridRichLines (A : Finset ℝ) (L : Finset (Set (ℝ × ℝ))) (k : ℕ) :
    Finset (Set (ℝ × ℝ)) :=
  L.filter fun ℓ => k ≤ ((A ×ˢ A).filter (fun p => p ∈ ℓ)).card

lemma gridRichLines_subset (A : Finset ℝ) (L : Finset (Set (ℝ × ℝ))) (k : ℕ) :
    gridRichLines A L k ⊆ L := Finset.filter_subset _ _

/-- **Grid rich-line bound** (rpow-free interface form), conditional on the
crossing lemma: for `P = A ×ˢ A` and any finite family `L` of affine lines,
`k³ · #{k-rich lines} ≤ C · (|A|⁴ + k²·|A|²)` for all `k ≥ 2`. -/
def GridRichLineStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (A : Finset ℝ) (L : Finset (Set (ℝ × ℝ))),
      (∀ ℓ ∈ L, IsAffineLine ℓ) → ∀ k : ℕ, 2 ≤ k →
        (k : ℝ) ^ 3 * ((gridRichLines A L k).card : ℝ)
          ≤ C * ((A.card : ℝ) ^ 4 + (k : ℝ) ^ 2 * (A.card : ℝ) ^ 2)

/-- **The arithmetic core.** From the Szemerédi–Trotter inequality
`k·X ≤ C·(s + N + X)` (where `s = N^{2/3}·X^{2/3}`, encoded via `s³ = N²·X²`) plus
the geometric cap `X ≤ N²`, derive `k³·X ≤ (64C³+4C)·(N² + k²N)`.  Pure real
arithmetic; the only nonlinear input is the cube `s³ = N²X²`. -/
lemma richline_arith {N X k C s : ℝ} (hN : 0 ≤ N) (hX : 0 ≤ X) (hk2 : 2 ≤ k)
    (hC1 : 1 ≤ C) (_hs0 : 0 ≤ s) (hs3 : s ^ 3 = N ^ 2 * X ^ 2) (hXN : X ≤ N ^ 2)
    (hST : k * X ≤ C * (s + N + X)) :
    k ^ 3 * X ≤ (64 * C ^ 3 + 4 * C) * (N ^ 2 + k ^ 2 * N) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hkpos : 0 < k := lt_of_lt_of_le two_pos hk2
  by_cases hX0 : X ≤ 0
  · have hXeq : X = 0 := le_antisymm hX0 hX
    rw [hXeq, mul_zero]
    have h1 : (0:ℝ) ≤ 64 * C ^ 3 + 4 * C := by nlinarith [hCpos, pow_pos hCpos 3]
    have h2 : (0:ℝ) ≤ N ^ 2 + k ^ 2 * N := by
      nlinarith [sq_nonneg N, mul_nonneg (sq_nonneg k) hN]
    exact mul_nonneg h1 h2
  · have hXpos : 0 < X := not_le.mp hX0
    by_cases hkb : 2 * C ≤ k
    · have hCX : C * X ≤ k / 2 * X :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hXpos)
      have hhalf : k / 2 * X ≤ C * s + C * N := by nlinarith [hST, hCX]
      by_cases hsN : N ≤ s
      · -- main regime: `s ≥ N`
        have h4 : k * X ≤ 4 * C * s := by
          nlinarith [hhalf, mul_le_mul_of_nonneg_left hsN (le_of_lt hCpos)]
        have hcube : (k * X) ^ 3 ≤ (4 * C * s) ^ 3 :=
          pow_le_pow_left₀ (mul_nonneg (le_of_lt hkpos) hX) h4 3
        have hexp : (k * X) ^ 3 = k ^ 3 * X * X ^ 2 := by ring
        have hrhs : (4 * C * s) ^ 3 = 64 * C ^ 3 * N ^ 2 * X ^ 2 := by
          have hexp2 : (4 * C * s) ^ 3 = 64 * C ^ 3 * s ^ 3 := by ring
          rw [hexp2, hs3]; ring
        rw [hexp, hrhs] at hcube
        have hx2 : (0:ℝ) < X ^ 2 := by positivity
        have hmain : k ^ 3 * X ≤ 64 * C ^ 3 * N ^ 2 := by
          have h := hcube
          rw [show (64:ℝ) * C ^ 3 * N ^ 2 * X ^ 2 = (64 * C ^ 3 * N ^ 2) * X ^ 2 by ring,
            show k ^ 3 * X * X ^ 2 = (k ^ 3 * X) * X ^ 2 by ring] at h
          exact le_of_mul_le_mul_right h hx2
        nlinarith [hmain, mul_nonneg (mul_nonneg (le_of_lt hCpos) (sq_nonneg k)) hN,
          mul_nonneg (mul_nonneg (le_of_lt (pow_pos hCpos 3)) (sq_nonneg k)) hN,
          mul_nonneg (le_of_lt hCpos) (sq_nonneg N)]
      · -- low regime: `s < N`
        have hsN' : s < N := not_le.mp hsN
        have hkX : k * X ≤ 4 * C * N := by
          nlinarith [hhalf, mul_le_mul_of_nonneg_left (le_of_lt hsN') (le_of_lt hCpos)]
        nlinarith [mul_le_mul_of_nonneg_left hkX (sq_nonneg k),
          mul_nonneg (mul_nonneg (le_of_lt (pow_pos hCpos 3)) (sq_nonneg k)) hN,
          mul_nonneg (le_of_lt hCpos) (sq_nonneg N),
          mul_nonneg (le_of_lt (pow_pos hCpos 3)) (sq_nonneg N)]
    · -- small `k`: `k < 2C`, fall back to the geometric cap `X ≤ N²`
      push Not at hkb
      have hk3 : k ^ 3 ≤ 8 * C ^ 3 := by
        have h := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * C - k)
          (by positivity : (0:ℝ) ≤ 4 * C ^ 2 + 2 * C * k + k ^ 2)
        nlinarith [h]
      have e1 : k ^ 3 * X ≤ k ^ 3 * N ^ 2 :=
        mul_le_mul_of_nonneg_left hXN (by positivity)
      have e2 : k ^ 3 * N ^ 2 ≤ 8 * C ^ 3 * N ^ 2 :=
        mul_le_mul_of_nonneg_right hk3 (sq_nonneg N)
      nlinarith [e1, e2, mul_nonneg (le_of_lt (pow_pos hCpos 3)) (sq_nonneg N),
        mul_nonneg (le_of_lt hCpos) (sq_nonneg N),
        mul_nonneg (mul_nonneg (le_of_lt (pow_pos hCpos 3)) (sq_nonneg k)) hN,
        mul_nonneg (mul_nonneg (le_of_lt hCpos) (sq_nonneg k)) hN]

/-- **Geometric cap.** Distinct affine lines, each meeting the grid `A ×ˢ A` in
`≥ k ≥ 2` points, inject into ordered pairs of grid points (two points determine
a line), so there are at most `|A ×ˢ A|² = |A|⁴` of them. -/
lemma gridRichLines_card_le (A : Finset ℝ) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) {k : ℕ} (hk : 2 ≤ k) :
    (gridRichLines A L k).card ≤ A.card ^ 4 := by
  classical
  have hpair : ∀ ℓ : Set (ℝ × ℝ), ∃ pq : (ℝ × ℝ) × (ℝ × ℝ),
      ℓ ∈ gridRichLines A L k →
        pq.1 ∈ A ×ˢ A ∧ pq.2 ∈ A ×ˢ A ∧ pq.1 ∈ ℓ ∧ pq.2 ∈ ℓ ∧ pq.1 ≠ pq.2 := by
    intro ℓ
    by_cases hℓ : ℓ ∈ gridRichLines A L k
    · have h1 : 1 < ((A ×ˢ A).filter (fun p => p ∈ ℓ)).card := by
        have := (Finset.mem_filter.mp hℓ).2; omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
      exact ⟨(a, b), fun _ => ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp hb).1,
        (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, hab⟩⟩
    · exact ⟨default, fun h => absurd h hℓ⟩
  choose f hf using hpair
  have hcardt : A.card ^ 4 = ((A ×ˢ A) ×ˢ (A ×ˢ A)).card := by
    rw [Finset.card_product, Finset.card_product]; ring
  rw [hcardt]
  apply Finset.card_le_card_of_injOn f
  · intro ℓ hℓ
    obtain ⟨h1, h2, _, _, _⟩ := hf ℓ hℓ
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  · intro ℓ₁ h₁ ℓ₂ h₂ hfeq
    rw [Finset.mem_coe] at h₁ h₂
    by_contra hne
    obtain ⟨_, _, hp₁, hq₁, hpq₁⟩ := hf ℓ₁ h₁
    obtain ⟨_, _, hp₂, hq₂, _⟩ := hf ℓ₂ h₂
    have ha₁ : IsAffineLine ℓ₁ := hL ℓ₁ (gridRichLines_subset A L k h₁)
    have ha₂ : IsAffineLine ℓ₂ := hL ℓ₂ (gridRichLines_subset A L k h₂)
    have hsub := encard_inter_le_one_of_lines ha₁ ha₂ hne
    have hpI : (f ℓ₁).1 ∈ ℓ₁ ∩ ℓ₂ := ⟨hp₁, by rw [hfeq]; exact hp₂⟩
    have hqI : (f ℓ₁).2 ∈ ℓ₁ ∩ ℓ₂ := ⟨hq₁, by rw [hfeq]; exact hq₂⟩
    exact hpq₁ (hsub hpI hqI)

/-- **The grid rich-line bound from Szemerédi–Trotter.** Combines the incidence
form with the geometric cap to expose the exact interface
`k³·#{rich} ≤ C·(|A|⁴ + k²|A|²)`. -/
theorem gridRichLine_of_szemerediTrotter (hSTstmt : SzemerediTrotterStatement) :
    GridRichLineStatement := by
  obtain ⟨C, hCpos, hST⟩ := hSTstmt
  refine ⟨64 * (C + 1) ^ 3 + 4 * (C + 1), by positivity, ?_⟩
  intro A L hL k hk
  set D := C + 1 with hD
  have hC1 : (1:ℝ) ≤ D := by rw [hD]; linarith
  have hge : (k : ℝ) * ((gridRichLines A L k).card : ℝ)
      ≤ (incidences (A ×ˢ A) (gridRichLines A L k) : ℝ) := by
    rw [incidences_eq_sum, Nat.cast_sum,
      show (k : ℝ) * ((gridRichLines A L k).card : ℝ)
          = ∑ _ℓ ∈ gridRichLines A L k, (k : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul]; ring]
    apply Finset.sum_le_sum
    intro ℓ hℓ
    have hk' : k ≤ ((A ×ˢ A).filter (fun p => p ∈ ℓ)).card := (Finset.mem_filter.mp hℓ).2
    exact_mod_cast hk'
  have hP : ((A ×ˢ A).card : ℝ) = (A.card : ℝ) ^ 2 := by
    rw [Finset.card_product]; push_cast; ring
  have hST_D : (incidences (A ×ˢ A) (gridRichLines A L k) : ℝ) ≤
      D * (((A ×ˢ A).card : ℝ) ^ ((2:ℝ)/3)
            * ((gridRichLines A L k).card : ℝ) ^ ((2:ℝ)/3)
          + ((A ×ˢ A).card : ℝ) + ((gridRichLines A L k).card : ℝ)) := by
    have hsub : ∀ ℓ ∈ gridRichLines A L k, IsAffineLine ℓ :=
      fun ℓ hℓ => hL ℓ (gridRichLines_subset A L k hℓ)
    have h := hST (A ×ˢ A) (gridRichLines A L k) hsub
    have hnn : (0:ℝ) ≤ ((A ×ˢ A).card : ℝ) ^ ((2:ℝ)/3)
            * ((gridRichLines A L k).card : ℝ) ^ ((2:ℝ)/3)
          + ((A ×ˢ A).card : ℝ) + ((gridRichLines A L k).card : ℝ) := by positivity
    exact le_trans h (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hnn)
  rw [hP] at hST_D
  set s := ((A.card : ℝ) ^ 2) ^ ((2:ℝ)/3)
            * ((gridRichLines A L k).card : ℝ) ^ ((2:ℝ)/3) with hs_def
  have hcomb : (k : ℝ) * ((gridRichLines A L k).card : ℝ)
      ≤ D * (s + (A.card : ℝ) ^ 2 + ((gridRichLines A L k).card : ℝ)) :=
    le_trans hge hST_D
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hs3 : s ^ 3 = ((A.card : ℝ) ^ 2) ^ 2 * ((gridRichLines A L k).card : ℝ) ^ 2 := by
    rw [hs_def, mul_pow]
    congr 1
    · rw [← Real.rpow_natCast (((A.card : ℝ) ^ 2) ^ ((2:ℝ)/3)) 3,
        ← Real.rpow_mul (by positivity)]; norm_num
    · rw [← Real.rpow_natCast (((gridRichLines A L k).card : ℝ) ^ ((2:ℝ)/3)) 3,
        ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hk2R : (2:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hXN : ((gridRichLines A L k).card : ℝ) ≤ ((A.card : ℝ) ^ 2) ^ 2 := by
    have hnat := gridRichLines_card_le A L hL hk
    calc ((gridRichLines A L k).card : ℝ) ≤ ((A.card ^ 4 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((A.card : ℝ) ^ 2) ^ 2 := by push_cast; ring
  have harith := richline_arith (N := (A.card : ℝ) ^ 2)
    (X := ((gridRichLines A L k).card : ℝ)) (k := (k : ℝ)) (C := D) (s := s)
    (by positivity) (Nat.cast_nonneg _) hk2R hC1 hs0 hs3 hXN hcomb
  calc (k : ℝ) ^ 3 * ((gridRichLines A L k).card : ℝ)
      ≤ (64 * D ^ 3 + 4 * D) * (((A.card : ℝ) ^ 2) ^ 2 + (k : ℝ) ^ 2 * (A.card : ℝ) ^ 2) :=
        harith
    _ = (64 * D ^ 3 + 4 * D) * ((A.card : ℝ) ^ 4 + (k : ℝ) ^ 2 * (A.card : ℝ) ^ 2) := by ring

/-- **The grid rich-line bound, conditional on the straight-line induced weak
bound for the incidence graph.** -/
theorem gridRichLine_of_straightLineInducedWeakBound
    (hweak : StraightLineInducedWeakBound) :
    GridRichLineStatement :=
  gridRichLine_of_szemerediTrotter
    (szemerediTrotter_of_straightLineInducedWeakBound hweak)

/-- **The grid rich-line bound, conditional on the straight-line crossing-free
edge bound for the incidence graph.** -/
theorem gridRichLine_of_straightLineCrossingFreeEdgeBound
    (hplanar : StraightLineCrossingFreeEdgeBound) :
    GridRichLineStatement :=
  gridRichLine_of_straightLineInducedWeakBound
    (straightLineInducedWeakBound_of_crossingFreeEdgeBound hplanar)

/-- **The grid rich-line bound, conditional on the nondegenerate straight-line
crossing-free edge bound for the incidence graph.** -/
theorem gridRichLine_of_straightLineCrossingFreeEdgeBoundLarge
    (hlarge : StraightLineCrossingFreeEdgeBoundLarge) :
    GridRichLineStatement :=
  gridRichLine_of_straightLineCrossingFreeEdgeBound
    (straightLineCrossingFreeEdgeBound_of_large hlarge)

/-- **The grid rich-line bound, conditional on straight-line componentwise
genus-zero planarization for crossing-free survivors.** -/
theorem gridRichLine_of_straightLineCrossingFreeComponentwisePlanarization
    (hpl : StraightLineCrossingFreeComponentwisePlanarization) :
    GridRichLineStatement :=
  gridRichLine_of_straightLineCrossingFreeEdgeBound
    (straightLineCrossingFreeEdgeBound_of_componentwise_planarization hpl)

/-- **The grid rich-line bound, conditional on the simple crossing lemma.** -/
theorem gridRichLine_of_simpleCrossingLemma (hCL : SimpleCrossingLemmaStatement) :
    GridRichLineStatement :=
  gridRichLine_of_szemerediTrotter (szemerediTrotter_of_simpleCrossingLemma hCL)

/-- **The grid rich-line bound, conditional on the independent-drawing simple
crossing lemma.** -/
theorem gridRichLine_of_independentSimpleCrossingLemma
    (hCL : IndependentSimpleCrossingLemmaStatement) :
    GridRichLineStatement :=
  gridRichLine_of_szemerediTrotter
    (szemerediTrotter_of_independentSimpleCrossingLemma hCL)

/-- **The grid rich-line bound, conditional on the simple averaged weak crossing
bound.** This is now the closest conditional endpoint to the literature proof of
the simple crossing lemma: it remains only to prove the ACNS/Leighton averaged
weak inequality. -/
theorem gridRichLine_of_simpleWeakAveragedBound
    (hweak : SimpleWeakAveragedBound) :
    GridRichLineStatement :=
  gridRichLine_of_simpleCrossingLemma
    (simpleCrossingLemma_of_simpleWeakAveragedBound hweak)

/-- **The grid rich-line bound, conditional on the independent simple averaged
weak crossing bound.** This is the closest current conditional endpoint to the
literal ACNS/Leighton proof for the straight-line incidence graph. -/
theorem gridRichLine_of_independentSimpleWeakAveragedBound
    (hweak : IndependentSimpleWeakAveragedBound) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleCrossingLemma
    (independentSimpleCrossingLemma_of_independentSimpleWeakAveragedBound hweak)

/-- **The grid rich-line bound, conditional on the independent simple induced
weak bound.** This exposes the exact remaining local planar-deletion obligation
needed by the ACNS/Leighton proof. -/
theorem gridRichLine_of_independentSimpleInducedWeakBound
    (hweak : IndependentSimpleInducedWeakBound) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleWeakAveragedBound
    (independentSimpleWeakAveragedBound_of_inducedWeakBound hweak)

/-- **The grid rich-line bound, conditional on the independent simple
crossing-free edge bound.** This is the theorem surface immediately before the
remaining geometric/Euler planarization obligation. -/
theorem gridRichLine_of_independentSimpleCrossingFreeEdgeBound
    (hplanar : IndependentSimpleCrossingFreeEdgeBound) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleInducedWeakBound
    (independentSimpleInducedWeakBound_of_crossingFreeEdgeBound hplanar)

/-- **The grid rich-line bound, conditional on the componentwise independent
simple crossing-free planarization statement.** This is the faithful
disconnected planar endpoint for the literature layering before the remaining
drawing-to-component-planar-map construction. -/
theorem gridRichLine_of_independentSimpleCrossingFreeComponentwisePlanarization
    (hpl : IndependentSimpleCrossingFreeComponentwisePlanarization) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleCrossingFreeEdgeBound
    (independentSimpleCrossingFreeEdgeBound_of_componentwise_planarization hpl)

/-- **The grid rich-line bound, conditional on componentwise residual-map
witnesses for crossing-free restricted drawings.** This is the corrected
residual-map-facing endpoint: connected residual maps are required only for the
components of the crossing-free survivor. -/
theorem gridRichLine_of_edgeSetDrawingResidualMapComponentwisePlanarization
    (hres : EdgeSetDrawingResidualMapComponentwisePlanarization) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleCrossingFreeComponentwisePlanarization
    (independentSimpleCrossingFreeComponentwisePlanarization_of_edgeSetDrawing_residualMap hres)

/-- **The grid rich-line bound, conditional on residual-map witnesses for the
canonical connected components of crossing-free restricted drawings.** -/
theorem gridRichLine_of_edgeSetDrawingResidualMapCanonicalComponentPlanarization
    (hres : EdgeSetDrawingResidualMapCanonicalComponentPlanarization) :
    GridRichLineStatement :=
  gridRichLine_of_edgeSetDrawingResidualMapComponentwisePlanarization
    (edgeSetDrawingResidualMapComponentwisePlanarization_of_canonical_components hres)

/-- **The grid rich-line bound, conditional on ARR and residual-map planarity for
the canonical connected components of crossing-free restricted drawings.** -/
theorem gridRichLine_of_edgeSetDrawingResidualMapCanonicalComponentPlanarity
    (hres : EdgeSetDrawingResidualMapCanonicalComponentPlanarity) :
    GridRichLineStatement :=
  gridRichLine_of_edgeSetDrawingResidualMapCanonicalComponentPlanarization
    (edgeSetDrawingResidualMapCanonicalComponentPlanarization_of_planarity hres)

/-- **The grid rich-line bound, conditional on the clean crossing-free
residual-map planarity endpoint for connected simple topological graphs.** -/
theorem gridRichLine_of_crossingFreeResidualMapPlanarity
    (hres : CrossingFreeResidualMapPlanarity) :
    GridRichLineStatement :=
  gridRichLine_of_edgeSetDrawingResidualMapCanonicalComponentPlanarity
    (edgeSetDrawingResidualMapCanonicalComponentPlanarity_of_crossingFree hres)

/-- **The grid rich-line bound, conditional on the split crossing-free
topological endpoint: local rotation regularity plus genus-zero residual-map
planarity.** -/
theorem gridRichLine_of_crossingFree_arr_planarity
    (hrot : CrossingFreeArcsRotationRegular)
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    GridRichLineStatement :=
  gridRichLine_of_crossingFreeResidualMapPlanarity
    (crossingFreeResidualMapPlanarity_of_arr_planarity hrot hplanar)

/-- **The grid rich-line bound**, conditional only on the genus-zero residual-map
planarity theorem once ARR is known: the straight-line incidence construction
supplies the local rotation witness internally. -/
theorem gridRichLine_of_crossingFreeResidualMapPlanarityOfARR
    (hplanar : CrossingFreeResidualMapPlanarityOfARR) :
    GridRichLineStatement :=
  gridRichLine_of_straightLineCrossingFreeComponentwisePlanarization
    (straightLineCrossingFreeComponentwisePlanarization_of_crossingFreeResidualMapPlanarityOfARR
      hplanar)

/-- **The grid rich-line bound**, conditional on genus-zero residual-map
planarity after reindexing the edges of each connected crossing-free drawing by
a convenient permutation depending on the drawing and its ARR witness.

This is the ST-level expression of the remaining ordered-edge topological task:
prove residual-map planarity in a chosen insertion order, then transport it
back to the canonical drawing by
`crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity`. -/
theorem gridRichLine_of_crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity
    (hperm : ∀ (G : DrawnMultigraph),
      (∀ p q, G.multiplicity p q ≤ 1) →
      G.ArcsJoinEndpoints →
      CrossingFree G →
      G.GraphConnected →
      3 ≤ G.V.card →
      ∀ hARR : ArcsRotationRegular G,
        ∃ π : Equiv.Perm (Fin G.numEdges),
          (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegular G π hARR)).IsPlanar) :
    GridRichLineStatement :=
  gridRichLine_of_crossingFreeResidualMapPlanarityOfARR
    (crossingFreeResidualMapPlanarityOfARR_of_permuted_planarity hperm)

/-- **The grid rich-line bound**, conditional on a literature-order insertion
proof for the crossing-free residual-map endpoint.

This is the current sharp endpoint for discharging `GridRichLineStatement`
through the planar-map/Euler argument in Pach--Tóth: construct a convenient
edge order for each connected simple crossing-free drawing and verify the
leaf/same-face residual-map insertion witnesses for all prefixes. -/
theorem gridRichLine_of_crossingFreeResidualMapPlanarity_of_permuted_prefix_insertions
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
    GridRichLineStatement :=
  gridRichLine_of_crossingFreeResidualMapPlanarity
    (crossingFreeResidualMapPlanarity_of_permuted_prefix_insertions hinsert)

/-- **The grid rich-line bound, conditional on the independent simple
crossing-free planarization statement.** This is the current faithful endpoint
for the literature layering before the remaining drawing-to-planar-map
construction. -/
theorem gridRichLine_of_independentSimpleCrossingFreePlanarization
    (hpl : IndependentSimpleCrossingFreePlanarization) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleCrossingFreeEdgeBound
    (independentSimpleCrossingFreeEdgeBound_of_planarization hpl)

/-- **The grid rich-line bound, conditional on the nondegenerate independent
simple crossing-free planarization statement.** This is the corrected
literature-facing endpoint for the planar step: the genus-zero witness is needed
only when the sampled vertex set has at least three points. -/
theorem gridRichLine_of_independentSimpleCrossingFreePlanarizationLarge
    (hpl : IndependentSimpleCrossingFreePlanarizationLarge) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleWeakAveragedBound
    (independentSimpleWeakAveragedBound_of_crossingFreePlanarizationLarge hpl)

/-- **The grid rich-line bound, conditional on residual-map witnesses for every
nondegenerate crossing-free restricted drawing.** This is the current
residual-map-facing endpoint: supplying `EdgeSetDrawingResidualMapPlanarizationLarge`
closes the crossing-free planar layer, then the already-formalized
ACNS/Leighton averaging and Szemerédi--Trotter/grid argument finish the bound. -/
theorem gridRichLine_of_edgeSetDrawingResidualMapPlanarizationLarge
    (hres : EdgeSetDrawingResidualMapPlanarizationLarge) :
    GridRichLineStatement :=
  gridRichLine_of_independentSimpleCrossingFreePlanarizationLarge
    (independentSimpleCrossingFreePlanarizationLarge_of_edgeSetDrawing_residualMap hres)

/-- **The grid rich-line bound, conditional on residual-map witnesses for every
nondegenerate crossing-free restricted drawing after a convenient edge
reindexing.** This is the restricted-drawing permutation form of the remaining
residual-map task: prove genus-zero residual-map planarity in a literature-faithful
insertion order on each `edgeSetDrawing`, then transport back to the canonical
enumeration with
`edgeSetDrawingResidualMapPlanarizationLarge_of_permuted_planarity`. -/
theorem gridRichLine_of_edgeSetDrawingResidualMapPlanarizationLarge_of_permuted_planarity
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
    GridRichLineStatement :=
  gridRichLine_of_edgeSetDrawingResidualMapPlanarizationLarge
    (edgeSetDrawingResidualMapPlanarizationLarge_of_permuted_planarity hperm)

/-- **The grid rich-line bound, conditional on the bounded-multiplicity multigraph
crossing lemma.** Compatibility wrapper over
`gridRichLine_of_simpleCrossingLemma`. -/
theorem gridRichLine_of_crossingLemma (hCL : CrossingLemmaMultigraphStatement) :
    GridRichLineStatement :=
  gridRichLine_of_simpleCrossingLemma
    (simpleCrossingLemma_of_multigraphCrossingLemma hCL)


end PachSharir.SzemerediTrotter
