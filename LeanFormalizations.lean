/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

-- Combinatorics / additive combinatorics
import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers
import LeanFormalizations.Combinatorics.Additive.BSGEnergyToGraph

-- Combinatorics / combinatorial maps + planar edge bound (complete, axiom-clean)
import LeanFormalizations.Combinatorics.CombinatorialMap

-- Combinatorics / unit-distance elimination-order counting (complete, axiom-clean)
import LeanFormalizations.Combinatorics.UnitDistance.Counting

-- Euclidean geometry
import LeanFormalizations.Geometry.Euclidean.IsometryClassification

-- Convex geometry: line-slices of convex sets + a simple convex polygon model
-- (complete, axiom-clean)
import LeanFormalizations.Geometry.Convex.LineSlice
import LeanFormalizations.Geometry.Convex.SimpleConvexPolygon

-- Pach–de Zeeuw: Bézout finite-intersection (Theorem 2.1, existential form) and
-- its algebraic prelims. Complete, axiom-clean. The rest of the Pach–de Zeeuw
-- distinct-distances program (crossing lemma, Pach–Sharir, incidence assembly,
-- the reduction chain) is `sorry`-backed WIP and lives on the `wip-pachdezeeuw`
-- branch, not on `main`.
import LeanFormalizations.PachDeZeeuw.AlgebraicPrelim
import LeanFormalizations.PachDeZeeuw.Bezout
