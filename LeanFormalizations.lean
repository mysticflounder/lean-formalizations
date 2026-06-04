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

-- Combinatorics / unit-distance elimination-order counting (complete, axiom-clean)
import LeanFormalizations.Combinatorics.UnitDistance.Counting

-- Euclidean geometry
import LeanFormalizations.Geometry.Euclidean.IsometryClassification
-- Near Enemy Theorem for Bisector Energy: generic-projection algebra +
-- sphere-slice rigidity (complete, axiom-clean); canonical home of the
-- module also mirrored in the erdos-98 repo.
import LeanFormalizations.Geometry.Euclidean.NearEnemyTheorem

-- Convex geometry: line-slices of convex sets + a simple convex polygon model
-- (complete, axiom-clean)
import LeanFormalizations.Geometry.Convex.LineSlice
import LeanFormalizations.Geometry.Convex.SimpleConvexPolygon

-- Pach–de Zeeuw program: distinct distances on algebraic curves, and the
-- paper-faithful inputs it reduces to. Mostly statement-surfaces / work in
-- progress with `sorry`; see README for the per-module VERIFIED/PARTIAL triage.
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.MilnorThom
import LeanFormalizations.PachDeZeeuw.CurveSymmetries
import LeanFormalizations.PachDeZeeuw.AlgebraicPrelim
import LeanFormalizations.PachDeZeeuw.CrossingLemma
import LeanFormalizations.PachDeZeeuw.PachSharir
import LeanFormalizations.PachDeZeeuw
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly

-- Vendored, frozen Erdős problem statements (verbatim from formal-conjectures,
-- Apache 2.0) hosted for cross-version reference; see LeanFormalizations.FormalConjectures.
import LeanFormalizations.FormalConjectures
