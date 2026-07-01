/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

-- Combinatorics / additive combinatorics
import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers
import LeanFormalizations.Combinatorics.Additive.BSGEnergyToGraph
import LeanFormalizations.Combinatorics.Additive.ThreeAPFreeOfNoThreeCollinear

-- Combinatorics / combinatorial maps + planar edge bound (complete, axiom-clean)
import LeanFormalizations.Combinatorics.CombinatorialMap
import LeanFormalizations.Combinatorics.SimpleGraph.TreeOrder

-- Combinatorics / unit-distance elimination-order counting (complete, axiom-clean)
import LeanFormalizations.Combinatorics.UnitDistance.Counting

-- Euclidean geometry
-- Planar general-position primitives (ℝ², Set.Triplewise, NonTrilinear,
-- distinctDistances, InGeneralPosition): formal-conjectures originals (Apache 2.0,
-- absent from mathlib) consumed by the ESGK base layer below.
import LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition
import LeanFormalizations.Geometry.Euclidean.IsometryClassification
-- Odd-n emptiness of the Cayley equal-distance variety (gauged cyclic Cayley
-- design ℓ(i,j)=i+j on ZMod n): work in progress, headline theorem currently
-- `sorry`-scoped into the n≥17 analytic case and the n∈{7,...,15} finite
-- case (see module docstring). Formalization of erdos-98's
-- docs/problem-98-klow-odd-cayley-emptiness-2026-06-25.md.
import LeanFormalizations.Geometry.Euclidean.CayleyDesignEmptiness
-- Near Enemy Theorem for Bisector Energy: full chain from generic-projection
-- algebra and sphere-slice rigidity to the unconditional existence theorem
-- (complete, axiom-clean). Canonical home; consumed by erdos-98 as a lake dep.
import LeanFormalizations.Geometry.Euclidean.NearEnemyTheorem

-- Convex geometry: line-slices of convex sets + a simple convex polygon model
-- (complete, axiom-clean)
import LeanFormalizations.Geometry.Convex.LineSlice
import LeanFormalizations.Geometry.Convex.SimpleConvexPolygon

-- Elekes–Sharir / Pach–de Zeeuw adjacent generic lemmas (L1–L5): two-pinned
-- chord curve, component split, ruling skewness exclusion, ω-rank collapse,
-- affine-graph conic normal form. Linear-algebra/quadratic-form cores are
-- proven; the algebraic-geometry-heavy statement L2 carries explicitly-listed
-- `sorry`s. The L1 file now only contains the determinant identities. See
-- README for the per-lemma triage.
import LeanFormalizations.Geometry.ElekesSharir.OmegaRankCollapse
import LeanFormalizations.Geometry.ElekesSharir.ConicNormalForm
import LeanFormalizations.Geometry.ElekesSharir.RulingSkewness
import LeanFormalizations.Geometry.ElekesSharir.ChordCurve

-- Dumitrescu's isosceles-triangle counting bound (circumscribed case),
-- complete and axiom-clean: for a finite planar set that is nonempty,
-- non-collinear, convex-independent, and has ≥3 points on its minimum
-- enclosing circle, `iCount A ≤ (11·|A|² − 18·|A|)/12` (Dumitrescu 2006,
-- eq. (5); cap-decomposition method of Fox–Pach). Headline theorem
-- `IsoscelesCounting.iCount_le_of_convexIndep_circumscribed` in
-- `CGN/CGN8.lean`; importing it pulls the full dependency closure. Extracted
-- from the erdos-97-96 project (problem-specific lower-bound / K4 / descent
-- machinery deliberately NOT ported).
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN8

-- Elekes–Sharir / Guth–Katz reduction layer (base, sorry-free): the energy
-- identity, dyadic richness-level decomposition, ES-GK ledger existence, the
-- Cauchy–Schwarz bridge, and the elementary (E1)/(E2) O(n³) energy ceiling.
-- The open extremal-energy target M(n) and the D7.2 strengthening program are
-- research work and are deliberately NOT imported. Declarations in `namespace
-- Esgk`. Imported from the sibling esgk-on3 repo.
import LeanFormalizations.ElekesSharirGuthKatz

-- Pach–de Zeeuw program: distinct distances on algebraic curves, and the
-- paper-faithful inputs it reduces to. Mostly statement-surfaces / work in
-- progress with `sorry`; see README for the per-module VERIFIED/PARTIAL triage.
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.CriticalPointBound
import LeanFormalizations.PachDeZeeuw.MilnorThom
import LeanFormalizations.PachDeZeeuw.CurveSymmetries
import LeanFormalizations.PachDeZeeuw.AlgebraicPrelim
import LeanFormalizations.PachDeZeeuw.CrossingLemma
import LeanFormalizations.PachDeZeeuw.PachSharir
import LeanFormalizations.PachDeZeeuw.ComponentSplit
import LeanFormalizations.PachDeZeeuw.ChartBridge
import LeanFormalizations.PachDeZeeuw
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly

-- General linear group: the invertible diagonal matrix (Bryan Wang) and the 2×2
-- unipotent element plus the generic 2×2 matrix/determinant identities used in
-- Hecke double-coset arguments (Adam McKenna). Salvaged from the FLT good-prime
-- Hecke-operator decomposition; mathlib-staging, complete and axiom-clean.
import LeanFormalizations.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import LeanFormalizations.LinearAlgebra.Matrix.GeneralLinearGroup.Hecke
