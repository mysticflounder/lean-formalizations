/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound
import LeanFormalizations.Combinatorics.CombinatorialMap.EulerBound
import LeanFormalizations.Combinatorics.CombinatorialMap.DualProperties
import LeanFormalizations.Combinatorics.CombinatorialMap.VertexGraph
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion

/-!
# Combinatorial maps and the planar (multi)graph edge bound

A standalone, mathlib-only library of combinatorial-map results, complete and
axiom-clean (`[propext, Classical.choice, Quot.sound]`):

* `Basic` — the combinatorial-map carrier (vertex/edge/face permutations,
  Euler characteristic, planarity).
* `PlanarEdgeBound` — the simple-graph edge bound `e ≤ 3v − 6` from Euler's
  formula, and its multiplicity lift `e ≤ M·(3v − 6)`.
* `EulerBound` — a connected combinatorial map has Euler characteristic `≤ 2`.
* `DualProperties` — connectedness and planarity are preserved by duality.
* `VertexGraph` — vertex/face adjacency graphs and their spanning trees.
* `EdgeInsertion` — the orbit-count engine for edge insertion.
-/
