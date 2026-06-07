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

/-- A chosen edge witnessing a face-graph adjacency. This is the dual-side
analogue of `vertexGraphEdge` and is the basic selector used when turning a
spanning tree on faces into concrete map-edge data. -/
noncomputable def faceGraphEdge (M : CombinatorialMap D)
    {p q : M.dual.Vertex} (h : (M.faceGraph).Adj p q) : M.dual.Edge :=
  Classical.choose h.2

/-- The chosen dual edge really witnesses the face adjacency. -/
@[simp] theorem faceGraphEdge_spec (M : CombinatorialMap D)
    {p q : M.dual.Vertex} (h : (M.faceGraph).Adj p q) :
    Edge.ends (M := M.dual) (faceGraphEdge (M := M) h) = s(p, q) := by
  exact Classical.choose_spec h.2

/-- Swapping the face endpoints does not change the chosen dual edge. -/
@[simp] theorem faceGraphEdge_symm (M : CombinatorialMap D)
    {p q : M.dual.Vertex} (h : (M.faceGraph).Adj p q) :
    faceGraphEdge (M := M) (M.faceGraph.symm h) = faceGraphEdge (M := M) h := by
  rcases h with ⟨hne, e, he⟩
  simp [faceGraphEdge, Sym2.eq_swap]

/-- Equal chosen face-adjacency edges determine the same face pair. -/
theorem faceGraphEdge_eq (M : CombinatorialMap D)
    {p q r s : M.dual.Vertex}
    (h₁ : (M.faceGraph).Adj p q) (h₂ : (M.faceGraph).Adj r s)
    (heq : faceGraphEdge (M := M) h₁ = faceGraphEdge (M := M) h₂) :
    s(p, q) = s(r, s) := by
  simpa [faceGraphEdge_spec] using congrArg (Edge.ends (M := M.dual)) heq

/-- The edge quotient of a combinatorial map is canonically identified with the
edge quotient of its dual. This is the transport needed to turn face-graph data
into original edge indices when building tree/cotree orders. -/
noncomputable def dualEdgeEquiv (M : CombinatorialMap D) : M.dual.Edge ≃ M.Edge where
  toFun := Quotient.map' id (by
    intro x y h
    exact (Equiv.Perm.sameCycle_inv.mp h))
  invFun := Quotient.map' id (by
    intro x y h
    exact (Equiv.Perm.sameCycle_inv.mpr h))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => rfl
  right_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => rfl

/-- Equal transported face-adjacency edges determine the same face pair. -/
theorem faceGraphEdge_dualEquiv_eq (M : CombinatorialMap D)
    {p q r s : M.dual.Vertex}
    (h₁ : (M.faceGraph).Adj p q) (h₂ : (M.faceGraph).Adj r s)
    (heq : dualEdgeEquiv M (faceGraphEdge (M := M) h₁) =
      dualEdgeEquiv M (faceGraphEdge (M := M) h₂)) :
    s(p, q) = s(r, s) := by
  exact faceGraphEdge_eq (M := M) h₁ h₂ ((dualEdgeEquiv M).injective heq)

/-- A leaf-insertion order on a spanning tree of the face graph determines a
concrete original edge injection. This is the dual-side bridge used by the
ordered prefix insertion route: the same parent-edge order that enumerates tree
edges on the primal vertex graph also enumerates cotree edges on the dual side. -/
theorem exists_faceEdgeInjection_of_leafOrder
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph) (_hT : T.IsTree)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card M.dual.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → M.Edge, Function.Injective f := by
  classical
  refine ⟨fun i =>
    dualEdgeEquiv M
      (faceGraphEdge (M := M) (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)), ?_⟩
  intro i j hij
  let a_i : M.dual.Vertex := l[i.1 + 1]'(by omega)
  let b_i : M.dual.Vertex := parent (i.1 + 1) (by omega) (by omega)
  let a_j : M.dual.Vertex := l[j.1 + 1]'(by omega)
  let b_j : M.dual.Vertex := parent (j.1 + 1) (by omega) (by omega)
  have hAdj_i : (M.faceGraph).Adj a_i b_i := by
    exact hTsub (by simpa [a_i, b_i] using (hparent (i.1 + 1) (by omega) (by omega)).2)
  have hAdj_j : (M.faceGraph).Adj a_j b_j := by
    exact hTsub (by simpa [a_j, b_j] using (hparent (j.1 + 1) (by omega) (by omega)).2)
  have hEq : dualEdgeEquiv M (faceGraphEdge (M := M) hAdj_i) =
      dualEdgeEquiv M (faceGraphEdge (M := M) hAdj_j) := by
    simpa [a_i, b_i, a_j, b_j] using hij
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    exact faceGraphEdge_dualEquiv_eq (M := M) hAdj_i hAdj_j hEq
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- A leaf-insertion order on a spanning tree of the face graph determines an
edge permutation that moves those cotree edges into the initial segment of the
ambient edge order. This is the dual permutation-level bridge used by the
ordered prefix insertion route. -/
theorem exists_faceEdgePermutation_of_leafOrder
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph) (hT : T.IsTree)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card M.dual.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ hk : l.length - 1 ≤ Fintype.card M.Edge,
      ∃ f : Fin (l.length - 1) → M.Edge,
        Function.Injective f ∧
          ∃ π : Equiv.Perm M.Edge,
            ∀ i : Fin (l.length - 1), π (f i) = (Fintype.equivFin M.Edge).symm (Fin.castLE hk i) := by
  classical
  rcases
      exists_faceEdgeInjection_of_leafOrder
        (M := M) (T := T) hTsub hT hl_nodup hl_len parent hparent with
    ⟨f, hf⟩
  have hk : l.length - 1 ≤ Fintype.card M.Edge := by
    simpa using Fintype.card_le_of_injective f hf
  let e : M.Edge ≃ Fin (Fintype.card M.Edge) := Fintype.equivFin M.Edge
  have hf' : Function.Injective (fun i : Fin (l.length - 1) => e (f i)) := fun _ _ h =>
    hf (e.injective h)
  obtain ⟨σ, hσ⟩ := SimpleGraph.Equiv.Perm.exists_map_fin_castLE hk (fun i => e (f i)) hf'
  let π : Equiv.Perm M.Edge := e.trans (σ.trans e.symm)
  refine ⟨hk, f, hf, π, ?_⟩
  intro i
  simp [π, e, hσ]

end CombinatorialMap
