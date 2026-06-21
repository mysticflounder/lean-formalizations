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
-- Combinatorial-map / Euler machinery:
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
import LeanFormalizations.Combinatorics.CombinatorialMap.EulerBound
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc
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
# The multigraph crossing lemma

Self-contained formalization of the crossing inequality (Székely /
Ajtai–Chvátal–Newborn–Szemerédi, multigraph form), proved via combinatorial
maps and the planar Euler bound. Depends only on Mathlib.

Consumed by the `pdz` project (distinct distances on algebraic curves) to
discharge its incidence bound. The public surface is the frozen crossing
inequality statement plus its proof.
-/
