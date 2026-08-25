/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

-- Statement + amplification:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemmaAmplification
-- Local IFT arc (Proposition L, Edge-B GO brick):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc
-- Per-arc interval-clopen single-ψ analytic atoms (Edge-B, conditional on the band):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MonotoneArc
-- Vertical-strip compactness over a leading-coefficient-nonzero interval (Edge-B, lc-bound):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.StripCompact
-- Shared cut-set / fibre vocabulary for the decomposition assembly (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs
-- Infinity-cut: topological asymptote set ⊆ {lc_y=0}, finite, U_∞ ≤ d (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.InfinityCut
-- Good-locus components: finite S ⊆ ℝ ⟹ Sᶜ a finite disjoint ⋃ of open intervals (Edge-B, D1c):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.GoodLocusComponents
-- D1 finiteness: Bad h = Crit_x ∪ InfRoot_x finite (B-crit transported + infroot root-set) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD1
-- D2 band + compact strip on each good interval, composed with LEAF A → single-ψ arc (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD2
-- D3 sheet-count: fibre finite + ncard locally constant = constant on a good interval (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount
-- export-3: connecting-arc glue (decomp_arc_on_good + endpoint_pin) for the E1 pairing (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ConnectingArc
-- Fibrewise sheet rank invariant along a continuation arc — the E1 same-rank pairing datum (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetRank
-- Per-sheet incident-point bookkeeping (pointsOnSheet/edgesOnSheet, curve port of edgesOnLine) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetEdges
-- Shear substitution + curve-preservation coherence (generic-rotation WLOG step 1) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear
-- export-4a: each consecutive edgesOnSheet pair is a pinned connecting arc (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeArc
-- curveArc + export-4b interior-disjointness (SimpleCurveArc from a graph; disjoint sheets/intervals) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CurveArc
-- generic-rotation step 2: per-curve bad-shear-scalar set is finite (∂_y ≠ 0 off finitely many s) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearPartialY
-- generic-rotation: irreducibility is preserved by the shear (AlgEquiv transfer) (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearIrreducible
-- generic-rotation step 4: exists_good_shear — finite-avoidance glue picking one good scalar (Edge-B):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearExists
-- Edge-B endgame: M-tolerant incidence bound from CrossingLemmaMultigraphStatement (multiplicity ≤ M):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MultigraphIncidenceEndgame
-- Edge-B E1 inputs: bad-x fibre bound (≤ d) + |Bad h| ≤ (d+1)^5+d (def-independent cut-set cardinalities):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.BadPointBounds
-- Edge-B drawn multigraph: edgeBMultigraph def + arc field + glue (card_V, numEdges_eq_sum) (curve port of stMultigraph):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultigraph
-- Edge-B WellDrawn discharge (vi): crossingCount ≤ M·|Γ|² (same-curve disjoint + cross-curve ≤M-per-pair injection):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBWellDrawn
-- Edge-B ArcsJoinEndpoints discharge (v): lift EdgeBEdge.arc_endAnchor over the global edge index:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBArcsJoin
-- Edge-B multiplicity discharge (iv): multiplicity ≤ M from the point–point 2-DOF clause (countP, ≤1-per-curve):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultiplicity
-- Edge-B E1 discharge (iii): incidenceCount ≤ numEdges + c(d)·|Γ| (good-x coverage + bad-x fibre bound):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBE1
-- Edge-B top-level output: edgeB_crossingInput — composes the 6 discharges + M-form endgame → C(d,M) incidence bound:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCrossingInput
-- Edge-B downstream node (component-reduce): edgeB_crossingInput_2dof — TwoDegreesOfFreedom + InjOn ⇒ hpp/hcc bridge:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBComponentReduce
-- Edge-B downstream node (shear-apply): edgeB_crossingInput_unsheared — removes the ∂_y≠0 precondition via exists_good_shear:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBShearApply
-- Edge-B downstream node (chart-bridge): edgeB_crossingInput_euclidean — transports the bound to EuclideanSpace ℝ (Fin 2) via chartEquiv:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBChartBridge
-- Edge-B corollary-lift support (Lemma A): not_associated_of_ne_evalPlaneZeroSet — distinct real zero sets ⇒ ¬Associated (dedup engine):
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBDedup
-- Combinatorial-map / Euler machinery:
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
import LeanFormalizations.Combinatorics.CombinatorialMap.EulerBound
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLCover
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLAssembly
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLCollarSeparation
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound
-- Drawing -> abstract bridge + residual map:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.Abstractize
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMap
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapPermuteEdges
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualPlanarization
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeSetDrawing
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RotationCoherence
-- Region<->face (Edmonds) bridge + concrete EdmondsCompatible iteration:
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RegionFaceBridge
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdmondsConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DartSectorPoint

/-!
# The multigraph crossing-lemma development

Mathlib-only aggregator for the bounded-multiplicity crossing-lemma statement,
its conditional amplification, and the drawing-to-combinatorial-map infrastructure.
This is **not yet a self-contained proof**: `crossingLemma_of_weakBound` proves
`CrossingLemmaMultigraphStatement` from the literature-backed statement-surface
`WeakAveragedBound`, but no theorem in this library currently produces that hypothesis.
The separate drawing-to-map/topology path also retains labelled `sorry` obligations.

Consumed by the `pdz` project (distinct distances on algebraic curves) to
state the crossing input to its incidence bound. The exact weak averaged formula is
from Tóth, _Generalizations of the Crossing Lemma_, Theorem 7 (arXiv v1:
Theorem 0.3.1), <https://arxiv.org/abs/2509.14074>.

The sorry-free public Lean development `wpegden/crossing-consequences` formalizes
the simple-graph vertex-sampling argument and locally derives the denominator-`64`
simple bound. It does not formalize the bounded-multiplicity parallel-class thinning,
so it is not a producer for `WeakAveragedBound`.
-/
