/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.DualProperties
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
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

The combinatorial-map model follows Lando--Zvonkin, §1.3.3: darts carry the
vertex rotation `σ`, the edge involution `α`, and the face permutation `φ`.  The
tree/cotree edge-order bridge follows the standard planar-map statement that a
spanning tree in the primal map has complementary dual edges forming a spanning
cotree; see Erickson, *Tree-Cotree Decompositions*, Corollary "spanning tree
⇌ spanning cotree".
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

/-- A chosen edge witnessing a vertex-graph adjacency.

This is the primal-side selector used when turning a spanning tree on vertices
into concrete map-edge data.  It is the map-theoretic analogue of choosing the
edge across a dual face adjacency in a tree-cotree decomposition. -/
noncomputable def vertexGraphEdge (M : CombinatorialMap D)
    {p q : M.Vertex} (h : (M.vertexGraph).Adj p q) : M.Edge :=
  Classical.choose h.2

/-- The chosen primal edge really witnesses the vertex adjacency. -/
@[simp] theorem vertexGraphEdge_spec (M : CombinatorialMap D)
    {p q : M.Vertex} (h : (M.vertexGraph).Adj p q) :
    Edge.ends (M := M) (vertexGraphEdge (M := M) h) = s(p, q) := by
  exact Classical.choose_spec h.2

/-- Swapping the vertex endpoints does not change the chosen primal edge. -/
@[simp] theorem vertexGraphEdge_symm (M : CombinatorialMap D)
    {p q : M.Vertex} (h : (M.vertexGraph).Adj p q) :
    vertexGraphEdge (M := M) (M.vertexGraph.symm h) = vertexGraphEdge (M := M) h := by
  rcases h with ⟨hne, e, he⟩
  simp [vertexGraphEdge, Sym2.eq_swap]

/-- Equal chosen vertex-adjacency edges determine the same vertex pair. -/
theorem vertexGraphEdge_eq (M : CombinatorialMap D)
    {p q r s : M.Vertex}
    (h₁ : (M.vertexGraph).Adj p q) (h₂ : (M.vertexGraph).Adj r s)
    (heq : vertexGraphEdge (M := M) h₁ = vertexGraphEdge (M := M) h₂) :
    s(p, q) = s(r, s) := by
  simpa [vertexGraphEdge_spec] using congrArg (Edge.ends (M := M)) heq

/-- A leaf-insertion order on a spanning tree of the vertex graph determines a
concrete original edge injection.

This is the primal half of the tree/cotree edge-order bridge: parent edges in a
tree insertion order are represented by actual map edges, and distinct parent
edges give distinct map edges. -/
theorem exists_vertexEdgeInjection_of_leafOrder
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.vertexGraph) (_hT : T.IsTree)
    {l : List M.Vertex}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card M.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → M.Edge, Function.Injective f := by
  classical
  refine ⟨fun i =>
    vertexGraphEdge (M := M) (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2), ?_⟩
  intro i j hij
  let a_i : M.Vertex := l[i.1 + 1]'(by omega)
  let b_i : M.Vertex := parent (i.1 + 1) (by omega) (by omega)
  let a_j : M.Vertex := l[j.1 + 1]'(by omega)
  let b_j : M.Vertex := parent (j.1 + 1) (by omega) (by omega)
  have hAdj_i : (M.vertexGraph).Adj a_i b_i := by
    exact hTsub (by simpa [a_i, b_i] using (hparent (i.1 + 1) (by omega) (by omega)).2)
  have hAdj_j : (M.vertexGraph).Adj a_j b_j := by
    exact hTsub (by simpa [a_j, b_j] using (hparent (j.1 + 1) (by omega) (by omega)).2)
  have hEq : vertexGraphEdge (M := M) hAdj_i =
      vertexGraphEdge (M := M) hAdj_j := by
    simpa [a_i, b_i, a_j, b_j] using hij
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    exact vertexGraphEdge_eq (M := M) hAdj_i hAdj_j hEq
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- A leaf-insertion order on a spanning tree of the vertex graph determines an
edge permutation that moves those tree edges into the initial segment of the
ambient edge order. This is the primal permutation-level bridge used by the
ordered prefix insertion route. -/
theorem exists_vertexEdgePermutation_of_leafOrder
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.vertexGraph) (hT : T.IsTree)
    {l : List M.Vertex}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card M.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
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
      exists_vertexEdgeInjection_of_leafOrder
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

/-- The Euler-count half of the spanning-tree/spanning-cotree complement
statement.

If a planar map has a full vertex leaf order, then the number of edges left
after the `|V|-1` primal tree edges is exactly `|V(M.dual)|-1`, the edge count of
a dual spanning tree.  The remaining topological work is to identify those
remaining edges with a connected acyclic dual subgraph. -/
theorem card_edge_sub_vertexTreeLeafOrder_eq_card_dualVertex_sub_one
    (M : CombinatorialMap D) [Fintype D]
    (hV : 1 ≤ Fintype.card M.Vertex) (hplanar : M.IsPlanar)
    {l : List M.Vertex} (hl_len : l.length = Fintype.card M.Vertex) :
    Fintype.card M.Edge - (l.length - 1) = Fintype.card M.dual.Vertex - 1 := by
  have hdual : Fintype.card M.dual.Vertex = Fintype.card M.Face :=
    card_dual_vertex (M := M)
  have hplanar' : (Fintype.card M.Vertex : ℤ) - (Fintype.card M.Edge : ℤ) +
      (Fintype.card M.Face : ℤ) = 2 := hplanar
  omega

/-- The von Staudt edge count in the exact list-length form used by the
tree-first/cotree-second edge order.

For a planar map, a full primal vertex tree contributes `|V|-1` edges and a
full dual vertex tree contributes `|V(M.dual)|-1` edges; together these account
for all map edges.  The separate complement theorem must still identify the
second block with the complementary dual spanning tree. -/
theorem card_vertexTreeLeafOrder_add_dualVertexLeafOrder_eq_card_edge
    (M : CombinatorialMap D) [Fintype D]
    (hV : 1 ≤ Fintype.card M.Vertex) (hVdual : 1 ≤ Fintype.card M.dual.Vertex)
    (hplanar : M.IsPlanar)
    {l : List M.Vertex} (hl_len : l.length = Fintype.card M.Vertex)
    {lDual : List M.dual.Vertex}
    (hlDual_len : lDual.length = Fintype.card M.dual.Vertex) :
    (l.length - 1) + (lDual.length - 1) = Fintype.card M.Edge := by
  have hdual : Fintype.card M.dual.Vertex = Fintype.card M.Face :=
    card_dual_vertex (M := M)
  have hplanar' : (Fintype.card M.Vertex : ℤ) - (Fintype.card M.Edge : ℤ) +
      (Fintype.card M.Face : ℤ) = 2 := hplanar
  omega

/-- Assemble disjoint primal-tree and cotree edge injections into one edge
permutation with consecutive tree/cotree blocks.

This is the finite witness layer behind the tree-first/cotree-second order in
the literature.  It assumes the two concrete edge injections are already known
to be disjoint; the remaining complement theorem must provide that disjointness
for the primal spanning tree and complementary dual spanning tree. -/
theorem exists_edgePermutation_of_disjoint_vertex_dual_leafOrder_edges
    (M : CombinatorialMap D) [Fintype D]
    (hV : 1 ≤ Fintype.card M.Vertex) (hVdual : 1 ≤ Fintype.card M.dual.Vertex)
    (hplanar : M.IsPlanar)
    {l : List M.Vertex} (hl_len : l.length = Fintype.card M.Vertex)
    {lDual : List M.dual.Vertex}
    (hlDual_len : lDual.length = Fintype.card M.dual.Vertex)
    (f : Fin (l.length - 1) → M.Edge)
    (g : Fin (lDual.length - 1) → M.Edge)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g)) :
    ∃ hblock : (l.length - 1) + (lDual.length - 1) ≤ Fintype.card M.Edge,
      ∃ π : Equiv.Perm M.Edge,
        (∀ i : Fin (l.length - 1),
          π (f i) =
            (Fintype.equivFin M.Edge).symm
              (Fin.castLE hblock (Fin.castAdd (lDual.length - 1) i))) ∧
          (∀ j : Fin (lDual.length - 1),
            π (g j) =
              (Fintype.equivFin M.Edge).symm
                (Fin.castLE hblock (Fin.natAdd (l.length - 1) j))) := by
  classical
  have hcard := card_vertexTreeLeafOrder_add_dualVertexLeafOrder_eq_card_edge
    (M := M) hV hVdual hplanar hl_len hlDual_len
  let hblock : (l.length - 1) + (lDual.length - 1) ≤ Fintype.card M.Edge := by
    rw [hcard]
  obtain ⟨π, hπf, hπg⟩ :=
    SimpleGraph.Equiv.Perm.exists_map_fintype_twoBlocks
      (α := M.Edge) hblock f g hf hg hdisj
  exact ⟨hblock, π, hπf, hπg⟩

/-- Assemble disjoint primal-tree and cotree edge injections into one edge
permutation whose block positions evaluate to the chosen edges.

This is the inverse-convention companion to
`exists_edgePermutation_of_disjoint_vertex_dual_leafOrder_edges`. It is the form
used when a permutation is read as an ordered edge list: the edge at a block
position is the value of the permutation at that position. -/
theorem exists_edgePositionPermutation_of_disjoint_vertex_dual_leafOrder_edges
    (M : CombinatorialMap D) [Fintype D]
    (hV : 1 ≤ Fintype.card M.Vertex) (hVdual : 1 ≤ Fintype.card M.dual.Vertex)
    (hplanar : M.IsPlanar)
    {l : List M.Vertex} (hl_len : l.length = Fintype.card M.Vertex)
    {lDual : List M.dual.Vertex}
    (hlDual_len : lDual.length = Fintype.card M.dual.Vertex)
    (f : Fin (l.length - 1) → M.Edge)
    (g : Fin (lDual.length - 1) → M.Edge)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g)) :
    ∃ hblock : (l.length - 1) + (lDual.length - 1) ≤ Fintype.card M.Edge,
      ∃ π : Equiv.Perm M.Edge,
        (∀ i : Fin (l.length - 1),
          π ((Fintype.equivFin M.Edge).symm
              (Fin.castLE hblock (Fin.castAdd (lDual.length - 1) i))) = f i) ∧
          (∀ j : Fin (lDual.length - 1),
            π ((Fintype.equivFin M.Edge).symm
                (Fin.castLE hblock (Fin.natAdd (l.length - 1) j))) = g j) := by
  classical
  have hcard := card_vertexTreeLeafOrder_add_dualVertexLeafOrder_eq_card_edge
    (M := M) hV hVdual hplanar hl_len hlDual_len
  let hblock : (l.length - 1) + (lDual.length - 1) ≤ Fintype.card M.Edge := by
    rw [hcard]
  obtain ⟨π, hπf, hπg⟩ :=
    SimpleGraph.Equiv.Perm.exists_twoBlocks_map_fintype
      (α := M.Edge) hblock f g hf hg hdisj
  exact ⟨hblock, π, hπf, hπg⟩

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

/-- A face-graph adjacency selects a concrete original edge and the two original
face classes on its sides.

This unwraps the dual-edge selector into the dart-permutation language used by
tree-cotree arguments: the chosen dual edge is represented by a dart `d`, and
its two dual endpoints are the original face classes of `d` and the opposite
dart `edgePerm d`. -/
theorem exists_dart_faceGraphEdge_faces (M : CombinatorialMap D)
    {p q : M.dual.Vertex} (h : (M.faceGraph).Adj p q) :
    ∃ d : D,
      dualEdgeEquiv M (faceGraphEdge (M := M) h) = M.Edge_mk d ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M p, dualVertexEquivFace M q) := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep (faceGraphEdge (M := M) h)
  refine ⟨d, ?_, ?_⟩
  · rw [← hd]
    rfl
  · have hends := faceGraphEdge_spec (M := M) h
    rw [← hd, Edge.ends_mk] at hends
    have hmap :
        s(dualVertexEquivFace M (M.dual.Vertex_mk d),
            dualVertexEquivFace M (M.dual.Vertex_mk (M.dual.edgePerm d))) =
          s(dualVertexEquivFace M p, dualVertexEquivFace M q) := by
      simpa only [Sym2.map_mk] using congrArg (Sym2.map (dualVertexEquivFace M)) hends
    have hedge : M.edgePerm⁻¹ d = M.edgePerm d := by
      rw [show M.edgePerm⁻¹ = M.edgePerm from
        M.edgePerm_involutive.symm_eq_self_of_involutive]
    have hdual_edge : M.dual.edgePerm d = M.edgePerm d := by
      change M.edgePerm⁻¹ d = M.edgePerm d
      exact hedge
    calc
      s(M.Face_mk d, M.Face_mk (M.edgePerm d))
          = s(dualVertexEquivFace M (M.dual.Vertex_mk d),
              dualVertexEquivFace M (M.dual.Vertex_mk (M.edgePerm d))) := by
            rfl
      _ = s(dualVertexEquivFace M (M.dual.Vertex_mk d),
              dualVertexEquivFace M (M.dual.Vertex_mk (M.dual.edgePerm d))) := by
            rw [hdual_edge]
      _ = s(dualVertexEquivFace M p, dualVertexEquivFace M q) := hmap

/-- In a same-face insertion, the newly inserted primal edge is a dual edge
between the two newly split faces.

In the dart-permutation model of Lando--Zvonkin, §1.3.3, inserting an edge
through one face splits the corresponding `facePerm` cycle.  The two darts of
the new edge are incident to the two resulting faces, so in the dual face graph
the new edge witnesses adjacency of the two split-face vertices.  This is the
local dual-edge fact used by the tree-cotree decomposition layer. -/
theorem insertedEdgeMap_faceGraph_adj_new_edge
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    ((EdgeInsertion.insertedEdgeMap M c₁ c₂).faceGraph).Adj
      ((EdgeInsertion.insertedEdgeMap M c₁ c₂).dual.Vertex_mk
        (EdgeInsertion.dartA : D ⊕ Fin 2))
      ((EdgeInsertion.insertedEdgeMap M c₁ c₂).dual.Vertex_mk
        (EdgeInsertion.dartB : D ⊕ Fin 2)) := by
  classical
  let N : CombinatorialMap (D ⊕ Fin 2) := EdgeInsertion.insertedEdgeMap M c₁ c₂
  refine ⟨?hne, ⟨N.dual.Edge_mk (EdgeInsertion.dartA : D ⊕ Fin 2), ?hends⟩⟩
  · intro h
    have hface : N.Face_mk (EdgeInsertion.dartA : D ⊕ Fin 2) =
        N.Face_mk (EdgeInsertion.dartB : D ⊕ Fin 2) := by
      have h' := congrArg (dualVertexEquivFace (EdgeInsertion.insertedEdgeMap M c₁ c₂)) h
      simpa [N] using h'
    have himg := congrArg (EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame) hface
    rw [EdgeInsertion.insertedFaceSplitPoolEquiv_mk_dartA_right M c₁ c₂ hc hsame,
      EdgeInsertion.insertedFaceSplitPoolEquiv_mk_dartB_left M c₁ c₂ hc hsame] at himg
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    exact h10 (Sum.inr.inj himg)
  · simpa [N, faceGraph, CombinatorialMap.dual, EdgeInsertion.insertedEdgeMap,
      EdgeInsertion.insEdgePerm, EdgeInsertion.dartA, EdgeInsertion.dartB]
      using (Edge.ends_mk (M := N.dual) (EdgeInsertion.dartA : D ⊕ Fin 2))

/-- The concrete original edge selected by the parent edge at step `i` of a
leaf-insertion order on a spanning tree of the face graph.

This is the cotree-side analogue of a primal tree parent edge.  The selected
edge is a dual edge of `M.dual`, transported back to an original edge of `M`;
this is the finite edge witness used in the tree-cotree decomposition of a
planar map. -/
noncomputable def faceEdgeOfLeafOrder
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : M.Edge :=
  dualEdgeEquiv M
    (faceGraphEdge (M := M) (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2))

/-- The cotree parent edge selected by `faceEdgeOfLeafOrder` has a dart whose
two incident original faces are the new dual-tree vertex and its chosen earlier
parent, up to the unordered endpoint convention of `Sym2`. -/
theorem faceEdgeOfLeafOrder_spec
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrder T hTsub parent hparent i = M.Edge_mk d ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M (l[i.1 + 1]'(by omega)),
            dualVertexEquivFace M (parent (i.1 + 1) (by omega) (by omega))) := by
  exact exists_dart_faceGraphEdge_faces (M := M)
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- Cotree parent edges selected from a face-tree leaf order are distinct. -/
theorem faceEdgeOfLeafOrder_injective
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (M.faceEdgeOfLeafOrder T hTsub parent hparent) := by
  classical
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
    simpa [faceEdgeOfLeafOrder, a_i, b_i, a_j, b_j] using hij
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    exact faceGraphEdge_dualEquiv_eq (M := M) hAdj_i hAdj_j hEq
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- A leaf-insertion order on a spanning tree of the face graph determines a
concrete original edge injection. This is the dual-side bridge used by the
ordered prefix insertion route: the same parent-edge order that enumerates tree
edges on the primal vertex graph also enumerates cotree edges on the dual side. -/
theorem exists_faceEdgeInjection_of_leafOrder
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph) (_hT : T.IsTree)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup) (_hl_len : l.length = Fintype.card M.dual.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → M.Edge, Function.Injective f := by
  classical
  exact ⟨M.faceEdgeOfLeafOrder T hTsub parent hparent,
    M.faceEdgeOfLeafOrder_injective T hTsub hl_nodup parent hparent⟩

/-- The cotree edge selected by reading a dual leaf-insertion order backwards.

For the tree-cotree insertion order, the dual tree is naturally peeled by
leaves: earlier cotree insertions separate leaves, while the unpeeled suffix
remains in the unsplit face.  This selector keeps the same parent-edge data as
`faceEdgeOfLeafOrder`, but indexes it by `Fin.rev`. -/
noncomputable def faceEdgeOfLeafOrderReverse
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : M.Edge :=
  M.faceEdgeOfLeafOrder T hTsub parent hparent (Fin.rev i)

/-- The reverse cotree selector is the same face-adjacency edge as
`faceEdgeOfLeafOrder`, at the reversed index. -/
theorem faceEdgeOfLeafOrderReverse_spec
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderReverse T hTsub parent hparent i = M.Edge_mk d ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega)),
            dualVertexEquivFace M
              (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) := by
  simpa [faceEdgeOfLeafOrderReverse] using
    M.faceEdgeOfLeafOrder_spec T hTsub parent hparent (Fin.rev i)

/-- Reversing a dual leaf-insertion order preserves injectivity of the selected
cotree edges. -/
theorem faceEdgeOfLeafOrderReverse_injective
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (M.faceEdgeOfLeafOrderReverse T hTsub parent hparent) := by
  intro i j hij
  have hrev : Fin.rev i = Fin.rev j :=
    M.faceEdgeOfLeafOrder_injective T hTsub hl_nodup parent hparent
      (by simpa [faceEdgeOfLeafOrderReverse] using hij)
  exact Fin.rev_injective hrev

/-- A reverse dual leaf order gives an injective family of cotree edges. This is
the finite selector for the cotree block in the tree-first/cotree-second order. -/
theorem exists_faceEdgeInjection_of_leafOrderReverse
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj] (hTsub : T ≤ M.faceGraph) (_hT : T.IsTree)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup) (_hl_len : l.length = Fintype.card M.dual.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → M.Edge, Function.Injective f := by
  exact ⟨M.faceEdgeOfLeafOrderReverse T hTsub parent hparent,
    M.faceEdgeOfLeafOrderReverse_injective T hTsub hl_nodup parent hparent⟩

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
