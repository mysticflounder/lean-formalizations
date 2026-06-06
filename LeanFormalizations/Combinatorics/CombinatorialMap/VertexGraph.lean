/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.DualProperties
import LeanFormalizations.Combinatorics.SimpleGraph.TreeOrder

/-!
# Vertex and face adjacency graphs for combinatorial maps

This file adds the simple-graph adjacency surfaces needed for tree-cotree
arguments on combinatorial maps:

* `vertexGraph` connects two map vertices when some map edge has those vertices
  as its endpoint pair;
* `faceGraph` is the same construction on the dual map, so it connects dual
  vertices, i.e. original faces that share an edge.

The connectedness theorem is the only ingredient used immediately by the
crossing-lemma development; the spanning-tree corollaries are the bridge to
later edge-order extraction.
-/

set_option linter.style.longLine false

namespace CombinatorialMap

open scoped BigOperators

variable {D : Type*} {M : CombinatorialMap D}

/-- The vertex adjacency graph of a combinatorial map: two vertices are adjacent
when some map edge has exactly that pair of vertices as its endpoints.  Loops are
discarded at the graph level, so this is a simple graph. -/
def vertexGraph (M : CombinatorialMap D) : SimpleGraph M.Vertex where
  Adj p q :=
    p ≠ q ∧ ∃ e : M.Edge, Edge.ends (M := M) e = s(p, q)
  symm := by
    intro p q hpq
    rcases hpq with ⟨hne, e, he⟩
    exact ⟨hne.symm, e, by
      calc
        Edge.ends (M := M) e = s(p, q) := he
        _ = s(q, p) := Sym2.eq_swap⟩
  loopless := ⟨fun p hp => hp.1 rfl⟩

/-- The face adjacency graph of a combinatorial map: the vertex graph of the
dual map. This lives on the dual vertex type, which is canonically the face
type of the original map. -/
abbrev faceGraph (M : CombinatorialMap D) : SimpleGraph M.dual.Vertex :=
  (M.dual).vertexGraph

/-- A connected combinatorial map has a connected vertex adjacency graph. -/
theorem vertexGraph_connected [Fintype D] [Nonempty M.Vertex]
    (hconn : M.Connected) :
    (M.vertexGraph).Connected := by
  classical
  refine { preconnected := ?_, nonempty := ‹Nonempty M.Vertex› }
  intro p q
  obtain ⟨d, rfl⟩ := Quotient.exists_rep p
  obtain ⟨d', rfl⟩ := Quotient.exists_rep q
  have hstep :
      ∀ a b : D,
        (b = M.vertexPerm a ∨ b = M.vertexPerm⁻¹ a ∨ b = M.edgePerm a) →
        Relation.ReflTransGen (M.vertexGraph.Adj) (M.Vertex_mk a) (M.Vertex_mk b) := by
    intro a b hab
    rcases hab with rfl | rfl | rfl
    · simpa [vertexMk_vertexPerm] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (M.vertexGraph.Adj) (M.Vertex_mk a) (M.Vertex_mk a))
    ·
      have h : M.Vertex_mk (Equiv.symm M.vertexPerm a) = M.Vertex_mk a := by
        simpa using vertexMk_vertexPerm_inv (M := M) a
      simpa [h] using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (M.vertexGraph.Adj) (M.Vertex_mk a) (M.Vertex_mk a))
    · by_cases hsame : M.Vertex_mk a = M.Vertex_mk (M.edgePerm a)
      · simpa [hsame] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen (M.vertexGraph.Adj) (M.Vertex_mk a) (M.Vertex_mk a))
      · exact Relation.ReflTransGen.single
          ⟨hsame, ⟨M.Edge_mk a, by simpa [vertexGraph] using (Edge.ends_mk (M := M) a)⟩⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.lift' M.Vertex_mk hstep (hconn d d')

/-- A connected combinatorial map has a connected face adjacency graph. -/
theorem faceGraph_connected [Fintype D] [Nonempty M.Vertex]
    (hconn : M.Connected) :
    (M.faceGraph).Connected := by
  classical
  have hD : Nonempty D := by
    rcases ‹Nonempty M.Vertex› with ⟨v⟩
    obtain ⟨d, rfl⟩ := Quotient.exists_rep v
    exact ⟨d⟩
  letI : Nonempty M.dual.Vertex := ⟨M.dual.Vertex_mk (Classical.choice hD)⟩
  simpa [faceGraph] using
    (vertexGraph_connected (M := M.dual)
      (by simpa using (dual_connected_iff (M := M)).2 hconn))

/-- Every connected combinatorial map determines a spanning tree on its
vertices, viewed as a simple graph. -/
theorem exists_vertexGraph_spanningTree [Fintype D] [Nonempty M.Vertex]
    (hconn : M.Connected) :
    ∃ T ≤ M.vertexGraph, T.IsTree := by
  exact SimpleGraph.Connected.exists_isTree_le
    (G := M.vertexGraph) (vertexGraph_connected (M := M) hconn)

/-- Every connected combinatorial map determines a spanning tree on its faces,
viewed through the dual map. -/
theorem exists_faceGraph_spanningTree [Fintype D] [Nonempty M.Vertex]
    (hconn : M.Connected) :
    ∃ T ≤ M.faceGraph, T.IsTree := by
  exact SimpleGraph.Connected.exists_isTree_le
    (G := M.faceGraph) (faceGraph_connected (M := M) hconn)

end CombinatorialMap
