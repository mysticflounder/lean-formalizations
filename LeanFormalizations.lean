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
-- proven; the algebraic-geometry-heavy statements (L1 curve step, L2) carry
-- explicitly-listed `sorry`s. See README for the per-lemma triage.
import LeanFormalizations.Geometry.ElekesSharir.OmegaRankCollapse
import LeanFormalizations.Geometry.ElekesSharir.ConicNormalForm
import LeanFormalizations.Geometry.ElekesSharir.RulingSkewness
import LeanFormalizations.Geometry.ElekesSharir.ChordCurve

-- Pach–de Zeeuw program: distinct distances on algebraic curves, and the
-- paper-faithful inputs it reduces to. Mostly statement-surfaces / work in
-- progress with `sorry`; see README for the per-module VERIFIED/PARTIAL triage.
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.MilnorThom
import LeanFormalizations.PachDeZeeuw.CurveSymmetries
import LeanFormalizations.PachDeZeeuw.AlgebraicPrelim
import LeanFormalizations.PachDeZeeuw.CrossingLemma
import LeanFormalizations.PachDeZeeuw.PachSharir
import LeanFormalizations.PachDeZeeuw.ComponentSplit
import LeanFormalizations.PachDeZeeuw
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly

-- Vendored, frozen Erdős problem statements (verbatim from formal-conjectures,
-- Apache 2.0) hosted for cross-version reference; see LeanFormalizations.FormalConjectures.
import LeanFormalizations.FormalConjectures
