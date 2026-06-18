/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.Combinatorics.CombinatorialMap.DualProperties
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
import LeanFormalizations.Combinatorics.SimpleGraph.TreeOrder
import Mathlib.GroupTheory.Perm.Cycle.Concrete

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

namespace Fin

/-- Consecutive reverse indices are consecutive in the opposite direction. -/
theorem val_eq_succ_val_of_rev_val_add_two_eq_rev_val_add_one
    {n : ℕ} {i j : Fin n}
    (h : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1) :
    j.1 = i.1 + 1 := by
  simp [Fin.rev] at h ⊢
  omega

/-- Block-offset form of
`Fin.val_eq_succ_val_of_rev_val_add_two_eq_rev_val_add_one`. -/
theorem add_val_eq_add_succ_val_of_rev_val_add_two_eq_rev_val_add_one
    {n a : ℕ} {i j : Fin n}
    (h : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1) :
    a + j.1 = a + i.1 + 1 := by
  have hj : j.1 = i.1 + 1 :=
    val_eq_succ_val_of_rev_val_add_two_eq_rev_val_add_one h
  omega

end Fin

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

/-- Darts in the same vertex class are connected by `vertexPerm` steps.

Since `Vertex_mk` is the quotient by `vertexPerm` cycles, equality of vertex
classes means that one dart is a positive power of `vertexPerm` applied to the
other.  Hence the combinatorial-map one-step relation reaches between them
without using any `edgePerm` step. -/
theorem reflTransGen_of_eq_vertex_mk [Fintype D] {a b : D}
    (h : M.Vertex_mk a = M.Vertex_mk b) :
    Relation.ReflTransGen
      (fun x y ↦ y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x) a b := by
  have hsc : M.vertexPerm.SameCycle a b := Quotient.eq''.mp h
  obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
  have hpow :
      ∀ n : ℕ,
        Relation.ReflTransGen
          (fun x y ↦ y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x)
          a ((M.vertexPerm ^ n) a) := by
    intro n
    induction n with
    | zero =>
        simpa using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen
              (fun x y ↦ y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x)
              a a)
    | succ n ih =>
        refine ih.tail ?_
        left
        simp [pow_succ', Equiv.Perm.mul_apply]
  simpa [hn] using hpow n

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

/-- The chosen primal edge across a vertex adjacency admits an orientation whose
tail is the first endpoint and whose head is the second.

An edge class is the two-dart orbit of `edgePerm`, so after choosing any dart
representative of `vertexGraphEdge h` we may flip by `edgePerm` if needed to
orient it from `p` to `q`. -/
theorem vertexGraphEdge_spec_oriented (M : CombinatorialMap D)
    {p q : M.Vertex} (h : (M.vertexGraph).Adj p q) :
    ∃ d : D,
      vertexGraphEdge (M := M) h = M.Edge_mk d ∧
        M.Vertex_mk d = p ∧
        M.Vertex_mk (M.edgePerm d) = q := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep (vertexGraphEdge (M := M) h)
  have hends : s(M.Vertex_mk d, M.Vertex_mk (M.edgePerm d)) = s(p, q) := by
    have hends' := vertexGraphEdge_spec (M := M) h
    rw [← hd, Edge.ends_mk] at hends'
    exact hends'
  rw [Sym2.eq_iff] at hends
  rcases hends with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact ⟨d, by simp [hd], hleft, hright⟩
  · refine ⟨M.edgePerm d, ?_, ?_, ?_⟩
    · have hedge :
          M.Edge_mk (M.edgePerm d) = M.Edge_mk d := by
        exact (M.edge_mk_eq_iff (M.edgePerm d) d).2
          ((M.sameCycle_edgePerm_iff d (M.edgePerm d)).2 (Or.inr rfl))
      exact hd ▸ hedge.symm
    · exact hright
    · rw [M.edgePerm_involutive d]
      exact hleft

/-- A connected vertex adjacency graph already implies that the combinatorial
map itself is connected.

Every vertex-graph edge is represented by an original dart.  Starting from a
chosen representative of the source vertex, we move within that vertex cycle to
the dart of the edge, cross the edge by one `edgePerm` step, and then move
within the target vertex cycle.  Lifting a vertex-graph path in this way gives
the combinatorial-map connectivity relation. -/
theorem connected_of_vertexGraph_connected [Fintype D]
    (hconn : (M.vertexGraph).Connected) :
    M.Connected := by
  classical
  let R : D → D → Prop :=
    fun x y ↦ y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x
  have hadj :
      ∀ {p q : M.Vertex}, (M.vertexGraph).Adj p q →
        Relation.ReflTransGen R (Quotient.out p) (Quotient.out q) := by
    intro p q hpq
    obtain ⟨d, _hd, hd_left, hd_right⟩ := M.vertexGraphEdge_spec_oriented hpq
    have hstart :
        Relation.ReflTransGen R (Quotient.out p) d :=
      M.reflTransGen_of_eq_vertex_mk
        (show M.Vertex_mk (Quotient.out p) = M.Vertex_mk d from
          calc
            M.Vertex_mk (Quotient.out p) = p := Quotient.out_eq p
            _ = M.Vertex_mk d := hd_left.symm)
    have hedge : Relation.ReflTransGen R d (M.edgePerm d) := by
      exact Relation.ReflTransGen.single (Or.inr (Or.inr rfl))
    have hend :
        Relation.ReflTransGen R (M.edgePerm d) (Quotient.out q) :=
      M.reflTransGen_of_eq_vertex_mk
        (show M.Vertex_mk (M.edgePerm d) = M.Vertex_mk (Quotient.out q) from
          calc
            M.Vertex_mk (M.edgePerm d) = q := hd_right
            _ = M.Vertex_mk (Quotient.out q) := (Quotient.out_eq q).symm)
    exact hstart.trans (hedge.trans hend)
  have hreach :
      ∀ {p q : M.Vertex},
        Relation.ReflTransGen (M.vertexGraph.Adj) p q →
          Relation.ReflTransGen R (Quotient.out p) (Quotient.out q) := by
    intro p q hpq
    induction hpq with
    | refl =>
        exact Relation.ReflTransGen.refl
    | tail _ hpq ih =>
        exact ih.trans (hadj hpq)
  intro a b
  have hstart :
      Relation.ReflTransGen R a (Quotient.out (M.Vertex_mk a)) :=
    M.reflTransGen_of_eq_vertex_mk (h := (Quotient.out_eq (M.Vertex_mk a)).symm)
  have hmid :
      Relation.ReflTransGen R (Quotient.out (M.Vertex_mk a))
        (Quotient.out (M.Vertex_mk b)) := by
    have hreachV := hconn.preconnected (M.Vertex_mk a) (M.Vertex_mk b)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreachV
    exact hreach hreachV
  have hend :
      Relation.ReflTransGen R (Quotient.out (M.Vertex_mk b)) b :=
    M.reflTransGen_of_eq_vertex_mk (h := Quotient.out_eq (M.Vertex_mk b))
  exact hstart.trans (hmid.trans hend)

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

/-- If every edge other than `d` incident to the vertex of `d` identifies the
same face label on its two sides, then `d` does as well.

This is the local vertex-cycle step behind the spanning-tree/spanning-cotree
complement theorem.  Around a leaf of the remaining primal tree, every other
incident edge is already known to preserve the current face label, so the last
remaining tree edge preserves it too. -/
theorem face_label_eq_of_mem_vertexPerm_toList_of_forall_same_vertex_other_edge
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    {β : Type*} (label : M.Face → β) {d x : D}
    (hloop : M.Vertex_mk (M.edgePerm d) ≠ M.Vertex_mk d)
    (hx : x ∈ Equiv.Perm.toList M.vertexPerm d)
    (hother : ∀ y : D, M.Vertex_mk y = M.Vertex_mk d →
      M.Edge_mk y ≠ M.Edge_mk d →
      label (M.Face_mk y) = label (M.Face_mk (M.edgePerm y))) :
    label (M.Face_mk x) = label (M.Face_mk d) := by
  classical
  set L : List D := Equiv.Perm.toList M.vertexPerm d with hL
  have hx' : x ∈ L := by simpa [hL] using hx
  have hsupp : d ∈ M.vertexPerm.support := by
    exact (Equiv.Perm.mem_toList_iff.mp (by simpa [hL] using hx')).2
  have hvertex_pow : ∀ n : ℕ, M.Vertex_mk ((M.vertexPerm ^ n) d) = M.Vertex_mk d := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, vertexMk_vertexPerm, ih]
  have hlabel_pow :
      ∀ n : ℕ, ∀ hn : n < L.length,
        label (M.Face_mk (L[n]'hn)) = label (M.Face_mk d) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hzero : L[0]'hn = d := by
          simpa [hL] using
            Equiv.Perm.toList_getElem_zero (p := M.vertexPerm) (x := d) hsupp
        simp [hzero]
    | succ n ih =>
        intro hn
        have hn' : n < L.length := by omega
        have hprev := ih hn'
        let y : D := L[n.succ]'hn
        have hy : y = (M.vertexPerm ^ n.succ) d := by
          simpa [hL, y] using
            Equiv.Perm.getElem_toList (p := M.vertexPerm) (x := d) n.succ hn
        have hy_vertex : M.Vertex_mk y = M.Vertex_mk d := by
          rw [hy]
          exact hvertex_pow n.succ
        have hy_ne : y ≠ d := by
          intro hyd
          have hnodup := Equiv.Perm.nodup_toList (p := M.vertexPerm) (x := d)
          have hlen_pos : 0 < L.length := by
            simpa [hL] using
              Equiv.Perm.length_toList_pos_of_mem_support (p := M.vertexPerm) (x := d) hsupp
          have hzero : L[0]'hlen_pos = d := by
            simpa [hL] using
              Equiv.Perm.toList_getElem_zero (p := M.vertexPerm) (x := d) hsupp
          have hsucc : L[n.succ]'hn = d := by
            simp [y, hyd]
          have hidx :
              (0 : ℕ) = n.succ := by
            exact (List.Nodup.getElem_inj_iff hnodup
              (i := 0) (hi := hlen_pos) (j := n.succ) (hj := hn)).1 (hzero.trans hsucc.symm)
          omega
        have hy_edge_ne : M.Edge_mk y ≠ M.Edge_mk d := by
          intro hE
          have hsc : M.edgePerm.SameCycle d y := (M.edge_mk_eq_iff y d).mp hE
          rcases (M.sameCycle_edgePerm_iff d y).mp hsc with hyd | hyd
          · exact hy_ne hyd
          · exact hloop (by simpa [hyd] using hy_vertex)
        have hstep :
            label (M.Face_mk y) = label (M.Face_mk (M.edgePerm y)) :=
          hother y hy_vertex hy_edge_ne
        have hpred : M.vertexPerm⁻¹ y = L[n]'hn' := by
          simpa [hy, hL, pow_succ', Equiv.Perm.mul_apply] using
            (Equiv.Perm.getElem_toList (p := M.vertexPerm) (x := d) n hn').symm
        have hface :
            M.Face_mk (M.edgePerm y) = M.Face_mk (L[n]'hn') := by
          calc
            M.Face_mk (M.edgePerm y)
                = M.Face_mk (M.facePerm (M.edgePerm y)) := by
                    rw [faceMk_facePerm]
            _ = M.Face_mk (M.vertexPerm⁻¹ y) := by
                  rw [vertexPerm_inv_eq_facePerm_edgePerm]
            _ = M.Face_mk (L[n]'hn') := by rw [hpred]
        calc
          label (M.Face_mk (L[n.succ]'hn))
              = label (M.Face_mk y) := by rfl
          _ = label (M.Face_mk (M.edgePerm y)) := hstep
          _ = label (M.Face_mk (L[n]'hn')) := by rw [hface]
          _ = label (M.Face_mk d) := hprev
  obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp hx'
  rw [← hxn]
  exact hlabel_pow n hn

/-- A face label can be transported along any initial segment of the vertex
cycle of `d` provided each dart on that segment identifies the same label on
its two sides.

This is the directional form of
`face_label_eq_of_mem_vertexPerm_toList_of_forall_same_vertex_other_edge`. It
only needs the label-preservation hypothesis on the visited prefix of
`Equiv.Perm.toList M.vertexPerm d`, rather than on the entire vertex class. -/
theorem face_label_eq_of_getElem_vertexPerm_toList_of_forall_edge_face_label_eq_on_prefix
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    {β : Type*} (label : M.Face → β) {d : D}
    (n : ℕ) (hn : n < (Equiv.Perm.toList M.vertexPerm d).length)
    (hstep : ∀ k : ℕ,
      (hk0 : 0 < k) →
      (hk : k < (Equiv.Perm.toList M.vertexPerm d).length) →
      k ≤ n →
      label (M.Face_mk ((Equiv.Perm.toList M.vertexPerm d)[k]'hk)) =
        label (M.Face_mk (M.edgePerm ((Equiv.Perm.toList M.vertexPerm d)[k]'hk)))) :
    label (M.Face_mk ((Equiv.Perm.toList M.vertexPerm d)[n]'hn)) =
      label (M.Face_mk d) := by
  classical
  set L : List D := Equiv.Perm.toList M.vertexPerm d with hL
  change label (M.Face_mk (L[n]'hn)) = label (M.Face_mk d)
  have hmem : L[n]'hn ∈ Equiv.Perm.toList M.vertexPerm d := by
    rw [← hL]
    exact List.getElem_mem (l := L) (n := n) hn
  have hsupp : d ∈ M.vertexPerm.support := by
    exact (Equiv.Perm.mem_toList_iff.mp hmem).2
  have hlabel_prefix :
      ∀ m : ℕ, ∀ hm : m < L.length, m ≤ n →
        label (M.Face_mk (L[m]'hm)) = label (M.Face_mk d) := by
    intro m
    induction m with
    | zero =>
        intro hm _hmle
        have hzero : L[0]'hm = d := by
          simpa [hL] using
            Equiv.Perm.toList_getElem_zero (p := M.vertexPerm) (x := d) hsupp
        simp [hzero]
    | succ m ih =>
        intro hm hmle
        have hm' : m < L.length := by omega
        have hmle' : m ≤ n := by omega
        have hprev := ih hm' hmle'
        have hcur :
            label (M.Face_mk (L[m.succ]'hm)) =
              label (M.Face_mk (M.edgePerm (L[m.succ]'hm))) := by
          exact hstep m.succ (Nat.succ_pos _) hm hmle
        have hpow_succ :
            L[m.succ]'hm = (M.vertexPerm ^ m.succ) d := by
          simpa [hL] using
            Equiv.Perm.getElem_toList (p := M.vertexPerm) (x := d) m.succ hm
        have hpred : M.vertexPerm⁻¹ (L[m.succ]'hm) = L[m]'hm' := by
          calc
            M.vertexPerm⁻¹ (L[m.succ]'hm)
                = (M.vertexPerm ^ m) d := by
                    rw [hpow_succ, pow_succ', Equiv.Perm.mul_apply]
                    exact M.vertexPerm.symm_apply_apply ((M.vertexPerm ^ m) d)
            _ = L[m]'hm' := by
                  simpa [hL] using
                    (Equiv.Perm.getElem_toList (p := M.vertexPerm) (x := d) m hm').symm
        have hface :
            M.Face_mk (M.edgePerm (L[m.succ]'hm)) = M.Face_mk (L[m]'hm') := by
          calc
            M.Face_mk (M.edgePerm (L[m.succ]'hm))
                = M.Face_mk (M.facePerm (M.edgePerm (L[m.succ]'hm))) := by
                    rw [faceMk_facePerm]
            _ = M.Face_mk (M.vertexPerm⁻¹ (L[m.succ]'hm)) := by
                  rw [vertexPerm_inv_eq_facePerm_edgePerm]
            _ = M.Face_mk (L[m]'hm') := by rw [hpred]
        calc
          label (M.Face_mk (L[m.succ]'hm))
              = label (M.Face_mk (M.edgePerm (L[m.succ]'hm))) := hcur
          _ = label (M.Face_mk (L[m]'hm')) := by rw [hface]
          _ = label (M.Face_mk d) := hprev
  exact hlabel_prefix n hn le_rfl

/-- A face label can be transported to any dart in the same vertex class once
every other incident edge at that vertex preserves the label across its two
sides.

This is the quotient-level form of
`face_label_eq_of_mem_vertexPerm_toList_of_forall_same_vertex_other_edge`: the
input is equality in `Vertex_mk`, which is the form produced naturally by
residual-map anchor comparisons. -/
theorem face_label_eq_of_eq_vertex_mk_of_forall_same_vertex_other_edge
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    {β : Type*} (label : M.Face → β) {d x : D}
    (hloop : M.Vertex_mk (M.edgePerm d) ≠ M.Vertex_mk d)
    (hxv : M.Vertex_mk x = M.Vertex_mk d)
    (hother : ∀ y : D, M.Vertex_mk y = M.Vertex_mk d →
      M.Edge_mk y ≠ M.Edge_mk d →
      label (M.Face_mk y) = label (M.Face_mk (M.edgePerm y))) :
    label (M.Face_mk x) = label (M.Face_mk d) := by
  by_cases hxd : x = d
  · simp [hxd]
  · have hsc : M.vertexPerm.SameCycle d x := Quotient.eq''.mp hxv.symm
    have hsupp : d ∈ M.vertexPerm.support := by
      rw [Equiv.Perm.mem_support]
      intro hfix
      have hfixx : d = x := Equiv.Perm.SameCycle.eq_of_left hsc hfix
      exact hxd hfixx.symm
    have hx : x ∈ Equiv.Perm.toList M.vertexPerm d :=
      (Equiv.Perm.mem_toList_iff).2 ⟨hsc, hsupp⟩
    exact
      M.face_label_eq_of_mem_vertexPerm_toList_of_forall_same_vertex_other_edge
        label hloop hx hother

/-- If every edge other than `d` incident to the vertex of `d` identifies the
same face label on its two sides, then `d` does as well.

This is the local vertex-cycle step behind the spanning-tree/spanning-cotree
complement theorem.  Around a leaf of the remaining primal tree, every other
incident edge is already known to preserve the current face label, so the last
remaining tree edge preserves it too. -/
theorem edge_face_label_eq_of_forall_same_vertex_other_edge
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    {β : Type*} (label : M.Face → β) {d : D}
    (hloop : M.Vertex_mk (M.edgePerm d) ≠ M.Vertex_mk d)
    (hother : ∀ x : D, M.Vertex_mk x = M.Vertex_mk d →
      M.Edge_mk x ≠ M.Edge_mk d →
      label (M.Face_mk x) = label (M.Face_mk (M.edgePerm x))) :
    label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  by_cases hfix : M.vertexPerm d = d
  · have hface :
        M.Face_mk (M.edgePerm d) = M.Face_mk d := by
      calc
        M.Face_mk (M.edgePerm d)
            = M.Face_mk (M.facePerm (M.edgePerm d)) := by
                rw [faceMk_facePerm]
        _ = M.Face_mk (M.vertexPerm⁻¹ d) := by
              rw [vertexPerm_inv_eq_facePerm_edgePerm]
        _ = M.Face_mk d := by
              have hfix' : M.vertexPerm⁻¹ d = d := by
                apply M.vertexPerm.injective
                simp [hfix]
              rw [hfix']
    rw [hface]
  · set L : List D := Equiv.Perm.toList M.vertexPerm d with hL
    have hsupp : d ∈ M.vertexPerm.support := by
      simpa [Equiv.Perm.mem_support] using hfix
    have hlen_pos : 0 < L.length := by
      simpa [hL] using
        Equiv.Perm.length_toList_pos_of_mem_support (p := M.vertexPerm) (x := d) hsupp
    have hlast_lt : L.length - 1 < L.length := by
      omega
    have hlast_label :
        label (M.Face_mk (L[L.length - 1]'hlast_lt)) = label (M.Face_mk d) := by
      let hmem : L[L.length - 1]'hlast_lt ∈ Equiv.Perm.toList M.vertexPerm d := by
        rw [← hL]
        exact List.getElem_mem (l := L) (n := L.length - 1) hlast_lt
      exact
        M.face_label_eq_of_mem_vertexPerm_toList_of_forall_same_vertex_other_edge
          label hloop hmem hother
    have hcycle : (M.vertexPerm ^ L.length) d = d := by
      simpa [hL] using
        (Equiv.Perm.pow_mod_card_support_cycleOf_self_apply
          (f := M.vertexPerm) (n := L.length) (x := d)).symm
    have hlast_apply : M.vertexPerm (L[L.length - 1]'hlast_lt) = d := by
      have hlast_pow :
          L[L.length - 1]'hlast_lt = (M.vertexPerm ^ (L.length - 1)) d := by
        simpa [hL] using
          Equiv.Perm.getElem_toList (p := M.vertexPerm) (x := d) (L.length - 1) hlast_lt
      rw [hlast_pow]
      calc
        M.vertexPerm ((M.vertexPerm ^ (L.length - 1)) d)
            = (M.vertexPerm ^ ((L.length - 1) + 1)) d := by
                simp [pow_succ', Equiv.Perm.mul_apply]
        _ = (M.vertexPerm ^ L.length) d := by
              rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)]
        _ = d := hcycle
    have hlast_inv : L[L.length - 1]'hlast_lt = M.vertexPerm⁻¹ d := by
      apply M.vertexPerm.injective
      simpa using hlast_apply
    have hlast_face :
        M.Face_mk (L[L.length - 1]'hlast_lt) = M.Face_mk (M.edgePerm d) := by
      rw [hlast_inv, vertexPerm_inv_eq_facePerm_edgePerm, faceMk_facePerm]
    have hfinal :
        label (M.Face_mk (M.edgePerm d)) = label (M.Face_mk d) := by
      calc
        label (M.Face_mk (M.edgePerm d))
            = label (M.Face_mk (L[L.length - 1]'hlast_lt)) := by rw [hlast_face]
        _ = label (M.Face_mk d) := hlast_label
    exact hfinal.symm

/-- If a face label is constant across every non-tree edge, then it is constant
across every selected tree edge of a primal leaf-insertion order.

This is the reverse-induction heart of the planar tree/cotree complement
argument.  At the current leaf-order vertex `l[k]`, any incident selected tree
edge other than the current parent edge comes from a later leaf-order step; an
earlier selected tree edge has both endpoints in the prefix `take k` and hence
cannot be incident to `l[k]`.  Therefore the local vertex-cycle lemma upgrades
the complement-edge label invariant to the current tree edge, and decreasing
induction propagates that to the whole primal tree block. -/
theorem vertexLeafOrder_edge_face_label_eq_of_not_mem_range
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.vertexGraph)
    {l : List M.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (f : Fin (l.length - 1) → M.Edge)
    (hf : ∀ i : Fin (l.length - 1),
      f i =
        vertexGraphEdge (M := M)
          (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2))
    {β : Type*} (label : M.Face → β)
    (hcomp : ∀ d : D,
      M.Edge_mk d ∉ Set.range f →
      label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d))) :
    ∀ i : Fin (l.length - 1), ∃ d : D,
      f i = M.Edge_mk d ∧
        label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ hk : k < l.length, ∀ hkpos : 0 < k,
      ∃ d : D,
        f ⟨k - 1, by omega⟩ = M.Edge_mk d ∧
          label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d))
  have hP : ∀ k : ℕ, P k := by
    refine Nat.strong_decreasing_induction ?_ ?_
    · refine ⟨l.length, ?_⟩
      intro m hm hm_lt
      omega
    · intro k ih hk hkpos
      let i : Fin (l.length - 1) := ⟨k - 1, by omega⟩
      have hi_succ : i.1 + 1 = k := by
        dsimp [i]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
      have hAdj :
          (M.vertexGraph).Adj (l[k]'hk) (parent k hkpos hk) := by
        exact hTsub (hparent k hkpos hk).2
      obtain ⟨d, hd, hd_left, hd_right⟩ :=
        M.vertexGraphEdge_spec_oriented
          (hTsub (hparent k hkpos hk).2)
      have hfi : f i = M.Edge_mk d := by
        have hfi0 : f i =
            vertexGraphEdge (M := M)
              (hTsub (hparent k hkpos hk).2) := by
          simpa [hi_succ] using hf i
        exact hfi0.trans hd
      have hloop : M.Vertex_mk (M.edgePerm d) ≠ M.Vertex_mk d := by
        simpa [hd_left, hd_right] using hAdj.1.symm
      refine ⟨d, hfi, ?_⟩
      apply M.edge_face_label_eq_of_forall_same_vertex_other_edge label hloop
      intro x hx_vertex hx_edge_ne
      by_cases hxcomp : M.Edge_mk x ∉ Set.range f
      · exact hcomp x hxcomp
      · push Not at hxcomp
        rcases hxcomp with ⟨j, hj⟩
        have hj_step_pos : 0 < j.1 + 1 := by omega
        have hj_step_lt : j.1 + 1 < l.length := by omega
        have hj_ne : j ≠ i := by
          intro hji
          apply hx_edge_ne
          calc
            M.Edge_mk x = f j := hj.symm
            _ = f i := by rw [hji]
            _ = M.Edge_mk d := hfi
        by_cases hj_lt : j.1 + 1 < k
        · have hpair_short :
              s(M.Vertex_mk x, M.Vertex_mk (M.edgePerm x)) =
                s(l[j.1 + 1]'hj_step_lt,
                  parent (j.1 + 1) hj_step_pos hj_step_lt) := by
            calc
              s(M.Vertex_mk x, M.Vertex_mk (M.edgePerm x))
                  = Edge.ends (M := M) (M.Edge_mk x) := by
                      rw [Edge.ends_mk]
              _ = Edge.ends (M := M) (f j) := by rw [hj]
              _ = Edge.ends (M := M)
                    (vertexGraphEdge (M := M)
                      (hTsub (hparent (j.1 + 1) hj_step_pos hj_step_lt).2)) := by
                        rw [hf j]
              _ = s(l[j.1 + 1]'hj_step_lt,
                    parent (j.1 + 1) hj_step_pos hj_step_lt) := by
                      exact
                        vertexGraphEdge_spec (M := M)
                          (hTsub (hparent (j.1 + 1) hj_step_pos hj_step_lt).2)
          have hprefix_mem :
              l[j.1 + 1]'hj_step_lt ∈ (l.take k).toFinset := by
            rw [List.mem_toFinset]
            have htake : j.1 + 1 < (l.take k).length := by
              rw [List.length_take]
              omega
            have hget :
                (l.take k)[j.1 + 1]'htake = l[j.1 + 1]'hj_step_lt := by
              exact (List.getElem_take' (xs := l) (i := j.1 + 1) (j := k) hj_step_lt hj_lt).symm
            exact List.mem_of_getElem hget
          have hparent_mem :
              parent (j.1 + 1) hj_step_pos hj_step_lt ∈ (l.take k).toFinset := by
            rw [List.mem_toFinset]
            have hpar_short :
                parent (j.1 + 1) hj_step_pos hj_step_lt ∈ l.take (j.1 + 1) := by
              simpa [List.mem_toFinset] using (hparent (j.1 + 1) hj_step_pos hj_step_lt).1
            obtain ⟨r, hr_short, hr_val⟩ := List.mem_iff_getElem.mp hpar_short
            have hr_short' : r < j.1 + 1 := by
              have : r < (l.take (j.1 + 1)).length := hr_short
              rw [List.length_take] at this
              omega
            have hr_long : r < k := by omega
            have hrl : r < l.length := by omega
            have hpar_eq :
                parent (j.1 + 1) hj_step_pos hj_step_lt = l[r]'hrl := by
              have hget :
                  l[r]'hrl = (l.take (j.1 + 1))[r]'hr_short := by
                exact List.getElem_take' (xs := l) (i := r) (j := j.1 + 1) hrl hr_short'
              exact (hget.trans hr_val).symm
            have htake : r < (l.take k).length := by
              rw [List.length_take]
              omega
            have hget :
                (l.take k)[r]'htake = l[r]'hrl := by
              exact (List.getElem_take' (xs := l) (i := r) (j := k) hrl hr_long).symm
            simpa [hpar_eq] using List.mem_of_getElem hget
          have hpair_ne :
              s(l[j.1 + 1]'hj_step_lt,
                parent (j.1 + 1) hj_step_pos hj_step_lt) ≠
                s(l[k]'hk, M.Vertex_mk (M.edgePerm x)) := by
            exact SimpleGraph.sym2_ne_getElem_parent_of_mem_take_nodup
              hl_nodup (hk := hk) (parent := M.Vertex_mk (M.edgePerm x))
              hprefix_mem hparent_mem
          have hpair_x :
              s(M.Vertex_mk x, M.Vertex_mk (M.edgePerm x)) =
                s(l[k]'hk, M.Vertex_mk (M.edgePerm x)) := by
            rw [hx_vertex, hd_left]
          exact (hpair_ne (hpair_short.symm.trans hpair_x)).elim
        · have hj_gt : k < j.1 + 1 := by
            have hj_ne_nat : j.1 + 1 ≠ k := by
              intro hEq
              apply hj_ne
              apply Fin.ext
              omega
            have hj_ge : k ≤ j.1 + 1 := by omega
            exact lt_of_le_of_ne hj_ge hj_ne_nat.symm
          obtain ⟨d', hd', hlabel'⟩ := ih (j.1 + 1) hj_gt (by omega) (by omega)
          have hj_idx : (⟨j.1 + 1 - 1, by omega⟩ : Fin (l.length - 1)) = j := by
            apply Fin.ext
            exact Nat.succ_sub_one j.1
          have hd'' : f j = M.Edge_mk d' := by
            simpa [hj_idx] using hd'
          have hE : M.Edge_mk x = M.Edge_mk d' := by
            calc
              M.Edge_mk x = f j := hj.symm
              _ = M.Edge_mk d' := hd''
          exact M.edge_face_label_eq_of_edge_mk_eq label hE hlabel'
  intro i
  exact hP (i.1 + 1) (by omega) (by omega)

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

/-- The face adjacency graph carried by a chosen set of original edge classes.

Two dual vertices are adjacent when some original edge in `S` has those faces
on its two sides.  This is the graph-theoretic surface for the complementary
cotree side of a planar tree/cotree decomposition: later, `S` will be the set
of edges not used by the primal spanning tree. -/
def faceGraphOnEdgeSet (M : CombinatorialMap D) (S : Set M.Edge) :
    SimpleGraph M.dual.Vertex where
  Adj p q :=
    p ≠ q ∧ ∃ e : M.dual.Edge, dualEdgeEquiv M e ∈ S ∧ Edge.ends (M := M.dual) e = s(p, q)
  symm := by
    intro p q hpq
    rcases hpq with ⟨hne, e, heS, he⟩
    exact ⟨hne.symm, e, heS, by
      calc
        Edge.ends (M := M.dual) e = s(p, q) := he
        _ = s(q, p) := Sym2.eq_swap⟩
  loopless := ⟨fun p hp => hp.1 rfl⟩

/-- A face adjacency carried by `S` is in particular an ordinary face
adjacency. -/
theorem faceGraphOnEdgeSet_le_faceGraph (M : CombinatorialMap D) (S : Set M.Edge) :
    M.faceGraphOnEdgeSet S ≤ M.faceGraph := by
  intro p q hpq
  rcases hpq with ⟨hne, e, _heS, he⟩
  exact ⟨hne, e, he⟩

/-- A chosen edge witnessing a face adjacency carried by `S`. -/
noncomputable def faceGraphOnEdgeSetEdge (M : CombinatorialMap D) (S : Set M.Edge)
    {p q : M.dual.Vertex} (h : (M.faceGraphOnEdgeSet S).Adj p q) : M.dual.Edge :=
  Classical.choose h.2

/-- The chosen carried face adjacency really uses an edge from `S`. -/
@[simp] theorem faceGraphOnEdgeSetEdge_mem (M : CombinatorialMap D) (S : Set M.Edge)
    {p q : M.dual.Vertex} (h : (M.faceGraphOnEdgeSet S).Adj p q) :
    dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S h) ∈ S := by
  exact (Classical.choose_spec h.2).1

/-- The chosen carried face adjacency really witnesses the given face pair. -/
@[simp] theorem faceGraphOnEdgeSetEdge_spec (M : CombinatorialMap D) (S : Set M.Edge)
    {p q : M.dual.Vertex} (h : (M.faceGraphOnEdgeSet S).Adj p q) :
    Edge.ends (M := M.dual) (faceGraphOnEdgeSetEdge (M := M) S h) = s(p, q) := by
  exact (Classical.choose_spec h.2).2

/-- Swapping the face endpoints does not change the chosen carried dual edge. -/
@[simp] theorem faceGraphOnEdgeSetEdge_symm (M : CombinatorialMap D) (S : Set M.Edge)
    {p q : M.dual.Vertex} (h : (M.faceGraphOnEdgeSet S).Adj p q) :
    faceGraphOnEdgeSetEdge (M := M) S ((M.faceGraphOnEdgeSet S).symm h) =
      faceGraphOnEdgeSetEdge (M := M) S h := by
  rcases h with ⟨hne, e, heS, he⟩
  simp [faceGraphOnEdgeSetEdge, Sym2.eq_swap]

/-- Equal chosen carried face-adjacency edges determine the same face pair. -/
theorem faceGraphOnEdgeSetEdge_eq (M : CombinatorialMap D) (S : Set M.Edge)
    {p q r s : M.dual.Vertex}
    (h₁ : (M.faceGraphOnEdgeSet S).Adj p q) (h₂ : (M.faceGraphOnEdgeSet S).Adj r s)
    (heq : faceGraphOnEdgeSetEdge (M := M) S h₁ =
      faceGraphOnEdgeSetEdge (M := M) S h₂) :
    s(p, q) = s(r, s) := by
  simpa [faceGraphOnEdgeSetEdge_spec] using congrArg (Edge.ends (M := M.dual)) heq

/-- Equal transported carried edges determine the same face pair. -/
theorem faceGraphOnEdgeSetEdge_dualEquiv_eq (M : CombinatorialMap D) (S : Set M.Edge)
    {p q r s : M.dual.Vertex}
    (h₁ : (M.faceGraphOnEdgeSet S).Adj p q) (h₂ : (M.faceGraphOnEdgeSet S).Adj r s)
    (heq : dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S h₁) =
      dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S h₂)) :
    s(p, q) = s(r, s) := by
  exact faceGraphOnEdgeSetEdge_eq (M := M) S h₁ h₂ ((dualEdgeEquiv M).injective heq)

/-- A carried face adjacency selects a concrete original edge in `S` and the
two original face classes on its sides. -/
theorem exists_dart_faceGraphOnEdgeSetEdge_faces (M : CombinatorialMap D) (S : Set M.Edge)
    {p q : M.dual.Vertex} (h : (M.faceGraphOnEdgeSet S).Adj p q) :
    ∃ d : D,
      dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S h) = M.Edge_mk d ∧
        M.Edge_mk d ∈ S ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M p, dualVertexEquivFace M q) := by
  obtain ⟨d, hd⟩ := Quotient.exists_rep (faceGraphOnEdgeSetEdge (M := M) S h)
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [← hd]
    rfl
  · have hmem := faceGraphOnEdgeSetEdge_mem (M := M) S h
    rw [← hd] at hmem
    simpa using hmem
  · have hends := faceGraphOnEdgeSetEdge_spec (M := M) S h
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

/-- The dual graph carried by the complement of a primal tree block is
connected.

Fix a primal leaf-insertion order and the corresponding selected tree edges
`f`.  If two faces are separated by a complementary edge, they are adjacent in
`faceGraphOnEdgeSet {e | e ∉ Set.range f}` and therefore lie in the same
connected component.  The previous reverse-induction theorem upgrades this
component-label equality from complementary edges to the selected tree edges as
well.  Hence every edge of the full face graph preserves the component label,
and connectedness of the full face graph forces the carried dual graph to have a
single connected component. This is Erickson's spanning-tree/complementary
spanning-cotree connectivity statement in the Lando--Zvonkin dart model. -/
theorem faceGraphOnEdgeSet_connected_of_not_mem_range_vertexLeafOrder
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.vertexGraph) (hT : T.IsTree)
    {l : List M.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (f : Fin (l.length - 1) → M.Edge)
    (hf : ∀ i : Fin (l.length - 1),
      f i =
        vertexGraphEdge (M := M)
          (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)) :
    (M.faceGraphOnEdgeSet {e | e ∉ Set.range f}).Connected := by
  classical
  let S : Set M.Edge := {e | e ∉ Set.range f}
  let Gc : SimpleGraph M.dual.Vertex := M.faceGraphOnEdgeSet S
  let labelFace : M.Face → Gc.ConnectedComponent :=
    fun φ => Gc.connectedComponentMk ((dualVertexEquivFace M).symm φ)
  have hcompFace : ∀ d : D,
      M.Edge_mk d ∈ S →
      labelFace (M.Face_mk d) = labelFace (M.Face_mk (M.edgePerm d)) := by
    intro d hdS
    dsimp [labelFace]
    by_cases hface : M.Face_mk d = M.Face_mk (M.edgePerm d)
    · rw [hface]
    · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      refine ⟨?_, M.dual.Edge_mk d, ?_, ?_⟩
      · intro hEq
        apply hface
        exact congrArg (dualVertexEquivFace M) hEq
      · change M.Edge_mk d ∈ S
        exact hdS
      · have hdual_edge : M.dual.edgePerm d = M.edgePerm d := by
          change M.edgePerm⁻¹ d = M.edgePerm d
          rw [show M.edgePerm⁻¹ = M.edgePerm from
            M.edgePerm_involutive.symm_eq_self_of_involutive]
        have hleft :
            (dualVertexEquivFace M).symm (M.Face_mk d) = M.dual.Vertex_mk d := by
          apply (dualVertexEquivFace M).injective
          simp
        have hright :
            (dualVertexEquivFace M).symm (M.Face_mk (M.edgePerm d)) =
              M.dual.Vertex_mk (M.edgePerm d) := by
          apply (dualVertexEquivFace M).injective
          simp
        rw [hleft, hright]
        simpa [hdual_edge] using (Edge.ends_mk (M := M.dual) d)
  have htreeLabel :=
    M.vertexLeafOrder_edge_face_label_eq_of_not_mem_range
      T hTsub hl_nodup parent hparent f hf labelFace
      (by intro d hdS; exact hcompFace d hdS)
  have hadj_full :
      ∀ ⦃u v : M.dual.Vertex⦄, (M.faceGraph).Adj u v →
        Gc.connectedComponentMk u = Gc.connectedComponentMk v := by
    intro u v huv
    obtain ⟨d, _hdE, hfaces⟩ := M.exists_dart_faceGraphEdge_faces huv
    have hdlabel :
        labelFace (M.Face_mk d) = labelFace (M.Face_mk (M.edgePerm d)) := by
      by_cases hdS : M.Edge_mk d ∉ Set.range f
      · exact hcompFace d hdS
      · push Not at hdS
        rcases hdS with ⟨j, hj⟩
        obtain ⟨d', hd', hlabel'⟩ := htreeLabel j
        have hE : M.Edge_mk d = M.Edge_mk d' := by
          calc
            M.Edge_mk d = f j := hj.symm
            _ = M.Edge_mk d' := hd'
        exact M.edge_face_label_eq_of_edge_mk_eq labelFace hE hlabel'
    rw [Sym2.eq_iff] at hfaces
    rcases hfaces with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa [labelFace, hu, hv] using hdlabel
    · simpa [labelFace, hu, hv] using hdlabel.symm
  have hVconn : (M.vertexGraph).Connected := hT.connected.mono hTsub
  have hMconn : M.Connected := M.connected_of_vertexGraph_connected hVconn
  letI : Nonempty M.Vertex := hVconn.nonempty
  have hfaceConn : (M.faceGraph).Connected := M.faceGraph_connected hMconn
  exact {
    preconnected := by
      intro u v
      have hEq :
          Gc.connectedComponentMk u = Gc.connectedComponentMk v :=
        SimpleGraph.Connected.apply_eq_of_forall_adj (G := M.faceGraph)
          hfaceConn hadj_full u v
      exact SimpleGraph.ConnectedComponent.eq.mp hEq
    nonempty := hfaceConn.nonempty
  }

/-- A carried dual-face adjacency selects a concrete complementary edge.

This unwraps an edge of `faceGraphOnEdgeSet S` into an actual dual edge whose
original edge class lies in `S` and whose dual endpoints are exactly the given
unordered face pair. -/
theorem exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet
    (M : CombinatorialMap D) (S : Set M.Edge)
    {z : Sym2 M.dual.Vertex}
    (hz : z ∈ (M.faceGraphOnEdgeSet S).edgeSet) :
    ∃ e : M.dual.Edge, dualEdgeEquiv M e ∈ S ∧ Edge.ends (M := M.dual) e = z := by
  induction z using Sym2.inductionOn with
  | hf p q =>
      have hAdj : (M.faceGraphOnEdgeSet S).Adj p q := by
        simpa using hz
      exact ⟨faceGraphOnEdgeSetEdge (M := M) S hAdj,
        faceGraphOnEdgeSetEdge_mem (M := M) S hAdj,
        faceGraphOnEdgeSetEdge_spec (M := M) S hAdj⟩

/-- The carried dual graph on `S` injects into the original edge set `S`.

Each simple dual adjacency chooses one concrete original edge in `S`. Two
different carried dual adjacencies cannot choose the same original edge,
because that would force the same unordered pair of dual face endpoints. -/
noncomputable def faceGraphOnEdgeSet_edgeSetToEdge
    (M : CombinatorialMap D) (S : Set M.Edge) :
    (M.faceGraphOnEdgeSet S).edgeSet → {e : M.Edge // e ∈ S} :=
  fun e => ⟨dualEdgeEquiv M (Classical.choose
      (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e.2)),
    (Classical.choose_spec
      (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e.2)).1⟩

/-- The chosen original-edge map from carried dual adjacencies is injective. -/
theorem faceGraphOnEdgeSet_edgeSetToEdge_injective
    (M : CombinatorialMap D) (S : Set M.Edge) :
    Function.Injective (faceGraphOnEdgeSet_edgeSetToEdge (M := M) S) := by
  intro e₁ e₂ h
  apply Subtype.ext
  have hEdge :
      Classical.choose (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₁.2) =
        Classical.choose (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₂.2) := by
    apply (dualEdgeEquiv M).injective
    simpa [faceGraphOnEdgeSet_edgeSetToEdge] using congrArg Subtype.val h
  have hEnds₁ := (Classical.choose_spec
      (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₁.2)).2
  have hEnds₂ := (Classical.choose_spec
      (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₂.2)).2
  calc
    e₁.1 = Edge.ends (M := M.dual)
        (Classical.choose (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₁.2)) := by
          simpa using hEnds₁.symm
    _ = Edge.ends (M := M.dual)
        (Classical.choose (exists_dualEdge_of_mem_faceGraphOnEdgeSet_edgeSet (M := M) S e₂.2)) := by
          rw [hEdge]
    _ = e₂.1 := by
          simpa using hEnds₂

/-- In a planar map, the full complementary dual graph of a primal spanning tree
is itself a spanning tree.

This is Erickson's spanning-tree/complementary-spanning-cotree theorem in the
combinatorial-map layer. The earlier connectivity theorem gives dual
connectedness on complementary edges; Euler counting forces that carried dual
graph to have exactly `|F|-1` edges, hence it is acyclic as well. -/
theorem faceGraphOnEdgeSet_isTree_of_not_mem_range_vertexLeafOrder
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    (hV : 1 ≤ Fintype.card M.Vertex) (hplanar : M.IsPlanar)
    (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.vertexGraph) (hT : T.IsTree)
    {l : List M.Vertex} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card M.Vertex)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (f : Fin (l.length - 1) → M.Edge)
    (hf : ∀ i : Fin (l.length - 1),
      f i =
        vertexGraphEdge (M := M)
          (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)) :
    (M.faceGraphOnEdgeSet {e | e ∉ Set.range f}).IsTree := by
  classical
  let S : Set M.Edge := {e | e ∉ Set.range f}
  let Gc : SimpleGraph M.dual.Vertex := M.faceGraphOnEdgeSet S
  have hconn : Gc.Connected :=
    M.faceGraphOnEdgeSet_connected_of_not_mem_range_vertexLeafOrder
      T hTsub hT hl_nodup parent hparent f hf
  have hf_inj : Function.Injective f := by
    intro i j hij
    let a_i : M.Vertex := l[i.1 + 1]'(by omega)
    let b_i : M.Vertex := parent (i.1 + 1) (by omega) (by omega)
    let a_j : M.Vertex := l[j.1 + 1]'(by omega)
    let b_j : M.Vertex := parent (j.1 + 1) (by omega) (by omega)
    have hAdj_i : (M.vertexGraph).Adj a_i b_i := by
      exact hTsub (by simpa [a_i, b_i] using
        (hparent (i.1 + 1) (by omega) (by omega)).2)
    have hAdj_j : (M.vertexGraph).Adj a_j b_j := by
      exact hTsub (by simpa [a_j, b_j] using
        (hparent (j.1 + 1) (by omega) (by omega)).2)
    have hEq : vertexGraphEdge (M := M) hAdj_i =
        vertexGraphEdge (M := M) hAdj_j := by
      calc
        vertexGraphEdge (M := M) hAdj_i = f i := (hf i).symm
        _ = f j := hij
        _ = vertexGraphEdge (M := M) hAdj_j := hf j
    have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
      exact vertexGraphEdge_eq (M := M) hAdj_i hAdj_j hEq
    exact SimpleGraph.IsTree.parentEdgeMap_injective
      (G := T) (l := l) hl_nodup parent hparent hsym2
  have hrange : Set.ncard (Set.range f) = l.length - 1 := by
    simpa using Set.ncard_range_of_injective hf_inj
  have hS : S.ncard = Fintype.card M.dual.Vertex - 1 := by
    have hScard : S.ncard = Nat.card M.Edge - (l.length - 1) := by
      change (Set.range f)ᶜ.ncard = Nat.card M.Edge - (l.length - 1)
      rw [Set.ncard_compl, hrange]
    have hcount :=
      M.card_edge_sub_vertexTreeLeafOrder_eq_card_dualVertex_sub_one hV hplanar hl_len
    rw [Nat.card_eq_fintype_card] at hScard
    omega
  have hedge_le : Nat.card Gc.edgeSet ≤ S.ncard := by
    have hedge_le' : Fintype.card Gc.edgeSet ≤ Fintype.card {e : M.Edge // e ∈ S} :=
      Fintype.card_le_of_injective
        (faceGraphOnEdgeSet_edgeSetToEdge (M := M) S)
        (faceGraphOnEdgeSet_edgeSetToEdge_injective (M := M) S)
    have hedge_le'' : Nat.card Gc.edgeSet ≤ Fintype.card {e : M.Edge // e ∈ S} := by
      simpa [Nat.card_eq_fintype_card] using hedge_le'
    have hSubtype : Fintype.card {e : M.Edge // e ∈ S} = S.ncard := by
      exact Set.fintypeCard_eq_ncard (s := S)
    exact hedge_le''.trans (by simp [hSubtype])
  have hVdual : 1 ≤ Fintype.card M.dual.Vertex := by
    have hpos : 0 < Fintype.card M.dual.Vertex :=
      Fintype.card_pos_iff.mpr hconn.nonempty
    omega
  apply (SimpleGraph.isTree_iff_connected_and_card (G := Gc)).2
  refine ⟨hconn, le_antisymm ?_ hconn.card_vert_le_card_edgeSet_add_one⟩
  calc
    Nat.card Gc.edgeSet + 1 ≤ S.ncard + 1 := Nat.add_le_add_right hedge_le 1
    _ = Fintype.card M.dual.Vertex := by
      rw [hS]
      omega
    _ = Nat.card M.dual.Vertex := Nat.card_eq_fintype_card.symm

/-- The complement of a primal tree block contains a dual spanning tree.

Once the carried dual graph on complementary edges is known to be connected,
`exists_isTree_le` extracts an explicit spanning tree inside it.  This is the
tree side of Erickson's spanning-tree/complementary-spanning-cotree
correspondence, in the exact edge-set form consumed by the residual-map
permutation layer. -/
theorem exists_faceGraphOnEdgeSet_spanningTree_of_not_mem_range_vertexLeafOrder
    (M : CombinatorialMap D) [Fintype D] [DecidableEq D]
    (T : SimpleGraph M.Vertex)
    [DecidableEq M.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.vertexGraph) (hT : T.IsTree)
    {l : List M.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (f : Fin (l.length - 1) → M.Edge)
    (hf : ∀ i : Fin (l.length - 1),
      f i =
        vertexGraphEdge (M := M)
          (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)) :
    ∃ Tface ≤ M.faceGraphOnEdgeSet {e | e ∉ Set.range f}, Tface.IsTree := by
  exact SimpleGraph.Connected.exists_isTree_le
    (G := M.faceGraphOnEdgeSet {e | e ∉ Set.range f})
    (M.faceGraphOnEdgeSet_connected_of_not_mem_range_vertexLeafOrder
      T hTsub hT hl_nodup parent hparent f hf)

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

/-- The concrete original edge selected from a leaf-insertion order on a face
graph carried by a chosen edge set.

This is the complementary-cotree selector needed later in the planar
tree/cotree decomposition: the selected dual-tree edge is represented by an
actual original edge known a priori to lie in `S`. -/
noncomputable def faceEdgeOfLeafOrderOnEdgeSet
    (M : CombinatorialMap D) (S : Set M.Edge)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : M.Edge :=
  dualEdgeEquiv M
    (faceGraphOnEdgeSetEdge (M := M) S
      (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2))

/-- The carried cotree parent edge selected by `faceEdgeOfLeafOrderOnEdgeSet`
lies in `S` and has the expected two face endpoints. -/
theorem faceEdgeOfLeafOrderOnEdgeSet_spec
    (M : CombinatorialMap D) (S : Set M.Edge)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderOnEdgeSet S T hTsub parent hparent i = M.Edge_mk d ∧
        M.Edge_mk d ∈ S ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M (l[i.1 + 1]'(by omega)),
            dualVertexEquivFace M (parent (i.1 + 1) (by omega) (by omega))) := by
  exact exists_dart_faceGraphOnEdgeSetEdge_faces (M := M) S
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- Carried cotree parent edges selected from a face-tree leaf order are
distinct. -/
theorem faceEdgeOfLeafOrderOnEdgeSet_injective
    (M : CombinatorialMap D) (S : Set M.Edge)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (M.faceEdgeOfLeafOrderOnEdgeSet S T hTsub parent hparent) := by
  classical
  intro i j hij
  let a_i : M.dual.Vertex := l[i.1 + 1]'(by omega)
  let b_i : M.dual.Vertex := parent (i.1 + 1) (by omega) (by omega)
  let a_j : M.dual.Vertex := l[j.1 + 1]'(by omega)
  let b_j : M.dual.Vertex := parent (j.1 + 1) (by omega) (by omega)
  have hAdj_i : (M.faceGraphOnEdgeSet S).Adj a_i b_i := by
    exact hTsub (by simpa [a_i, b_i] using (hparent (i.1 + 1) (by omega) (by omega)).2)
  have hAdj_j : (M.faceGraphOnEdgeSet S).Adj a_j b_j := by
    exact hTsub (by simpa [a_j, b_j] using (hparent (j.1 + 1) (by omega) (by omega)).2)
  have hEq :
      dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S hAdj_i) =
        dualEdgeEquiv M (faceGraphOnEdgeSetEdge (M := M) S hAdj_j) := by
    simpa [faceEdgeOfLeafOrderOnEdgeSet, a_i, b_i, a_j, b_j] using hij
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    exact faceGraphOnEdgeSetEdge_dualEquiv_eq (M := M) S hAdj_i hAdj_j hEq
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- The carried cotree edge selected by reading a dual leaf-insertion order
backwards. -/
noncomputable def faceEdgeOfLeafOrderOnEdgeSetReverse
    (M : CombinatorialMap D) (S : Set M.Edge)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : M.Edge :=
  M.faceEdgeOfLeafOrderOnEdgeSet S T hTsub parent hparent (Fin.rev i)

/-- The reverse carried cotree selector stays in `S` and has the reversed
leaf-parent face pair. -/
theorem faceEdgeOfLeafOrderOnEdgeSetReverse_spec
    (M : CombinatorialMap D) (S : Set M.Edge)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent i = M.Edge_mk d ∧
        M.Edge_mk d ∈ S ∧
        s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
          s(dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega)),
            dualVertexEquivFace M
              (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) := by
  simpa [faceEdgeOfLeafOrderOnEdgeSetReverse] using
    M.faceEdgeOfLeafOrderOnEdgeSet_spec S T hTsub parent hparent (Fin.rev i)

/-- Reverse carried cotree selectors are injective. -/
theorem faceEdgeOfLeafOrderOnEdgeSetReverse_injective
    (M : CombinatorialMap D) (S : Set M.Edge)
    [Fintype D] [DecidableEq D] (T : SimpleGraph M.dual.Vertex)
    [DecidableEq M.dual.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ M.faceGraphOnEdgeSet S)
    {l : List M.dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (M.faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent) := by
  intro i j hij
  apply Fin.rev_injective
  exact M.faceEdgeOfLeafOrderOnEdgeSet_injective S T hTsub hl_nodup parent hparent hij

/-- Oriented endpoint form of `faceEdgeOfLeafOrder_spec`.

The chosen cotree edge has the new dual-tree vertex and its earlier parent as
the two original face endpoints, in one of the two dart orientations.  This is
the orientation-sensitive witness needed when turning a dual-tree edge into the
two predecessor corners of a same-face residual insertion. -/
theorem faceEdgeOfLeafOrder_spec_cases
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
        ((M.Face_mk d =
            dualVertexEquivFace M (l[i.1 + 1]'(by omega)) ∧
          M.Face_mk (M.edgePerm d) =
            dualVertexEquivFace M (parent (i.1 + 1) (by omega) (by omega))) ∨
        (M.Face_mk d =
            dualVertexEquivFace M (parent (i.1 + 1) (by omega) (by omega)) ∧
          M.Face_mk (M.edgePerm d) =
            dualVertexEquivFace M (l[i.1 + 1]'(by omega)))) := by
  obtain ⟨d, hedge, hfaces⟩ :=
    M.faceEdgeOfLeafOrder_spec T hTsub parent hparent i
  refine ⟨d, hedge, ?_⟩
  rw [Sym2.eq_iff] at hfaces
  exact hfaces

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

/-- Oriented endpoint form of `faceEdgeOfLeafOrderReverse_spec`.

The reverse cotree selector has the reversed dual leaf-order vertex and its
earlier parent as the two original face endpoints, in one of the two dart
orientations. -/
theorem faceEdgeOfLeafOrderReverse_spec_cases
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
        ((M.Face_mk d =
            dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega)) ∧
          M.Face_mk (M.edgePerm d) =
            dualVertexEquivFace M
              (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) ∨
        (M.Face_mk d =
            dualVertexEquivFace M
              (parent ((Fin.rev i).1 + 1) (by omega) (by omega)) ∧
          M.Face_mk (M.edgePerm d) =
            dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega)))) := by
  simpa [faceEdgeOfLeafOrderReverse] using
    M.faceEdgeOfLeafOrder_spec_cases T hTsub parent hparent (Fin.rev i)

/-- The unpeeled dual prefix for a reverse cotree step is connected.

Reading the cotree block backwards peels leaves from the dual tree.  At reverse
step `i`, the still-unpeeled dual vertices are the prefix ending at the original
leaf-insertion vertex indexed by `Fin.rev i`; this induced prefix is connected
because every non-root vertex has its chosen parent earlier in the leaf order. -/
theorem faceEdgeOfLeafOrderReverse_unpeeled_prefix_connected
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    (T.induce
      {x : M.dual.Vertex | x ∈ (l.take ((Fin.rev i).1 + 2)).toFinset}).Connected := by
  exact SimpleGraph.connected_induce_take_of_leaf_insertion_parent
    (G := T) parent hparent ((Fin.rev i).1 + 2) (by omega) (by omega)

/-- A label constant across every edge of the unpeeled dual prefix is constant
on that whole prefix.

This is the graph-to-face bookkeeping form used by the cotree layer.  The label
will later be instantiated by the current split-face side of a residual prefix;
the edge hypothesis says each unpeeled dual edge has endpoints on the same
current side, and connectedness makes all unpeeled vertices share that side. -/
theorem faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : M.dual.Vertex → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v → label u = label v)
    {u v : M.dual.Vertex}
    (hu : u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset)
    (hv : v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset) :
    label u = label v := by
  let S : Set M.dual.Vertex :=
    {x : M.dual.Vertex | x ∈ (l.take ((Fin.rev i).1 + 2)).toFinset}
  have hconn : (T.induce S).Connected := by
    simpa [S] using
      M.faceEdgeOfLeafOrderReverse_unpeeled_prefix_connected T parent hparent i
  exact SimpleGraph.Connected.apply_eq_of_forall_adj (G := T.induce S)
    (f := fun x : ↥S => label x.1) hconn
    (by
      intro a b hab
      have habT : T.Adj a.1 b.1 := by
        simpa [S, SimpleGraph.induce_adj] using hab
      exact hadj a.2 b.2 habT)
    ⟨u, hu⟩ ⟨v, hv⟩

/-- A label is constant on the next unpeeled reverse-cotree prefix when the only
possible edge-local obstruction is the just-peeled leaf-parent edge.

This is the map-facing form of the reverse leaf-peeling invariant for the
spanning cotree side of a tree-cotree decomposition: at reverse step `i`, the
next unpeeled prefix is `take ((Fin.rev i).1 + 1)`, and every edge internal to
that prefix is distinct from the leaf-parent edge selected at step `i`.  Thus
connectedness of the next prefix propagates any label that is constant across
all non-peeled internal edges.  The dual-graph language follows the
spanning-tree/spanning-cotree convention in Erickson, §10.5. -/
theorem faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_apply_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : M.dual.Vertex → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label u = label v)
    {u v : M.dual.Vertex}
    (hu : u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset)
    (hv : v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset) :
    label u = label v := by
  exact SimpleGraph.reverse_leafOrder_prefix_apply_eq_of_forall_adj_ne_current_parent
    (G := T) (l := l) hl_nodup parent hparent i label
    (by
      intro u v hu hv huv hne
      exact hadj hu hv huv hne)
    hu hv

/-- Face-label version of
`faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_apply_eq_of_forall_adj_ne_current_parent`.

The label is read on original faces via the canonical dual-vertex/face
equivalence, matching the dart-permutation model of maps in Lando--Zvonkin,
§1.3.3. -/
theorem faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_face_label_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : M.Face → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v))
    {u v : M.dual.Vertex}
    (hu : u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset)
    (hv : v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset) :
    label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v) := by
  exact
    M.faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_apply_eq_of_forall_adj_ne_current_parent
      T hl_nodup parent hparent i
      (fun u => label (dualVertexEquivFace M u))
      (by
        intro u v hu hv huv hne
        exact hadj hu hv huv hne)
      hu hv

/-- Label equality for the two endpoint faces of a reverse cotree leaf edge,
assuming the label is constant across every edge of the unpeeled dual prefix. -/
theorem faceEdgeOfLeafOrderReverse_leaf_parent_label_eq_of_forall_adj
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : M.dual.Vertex → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v → label u = label v) :
    label (l[(Fin.rev i).1 + 1]'(by omega)) =
      label (parent ((Fin.rev i).1 + 1) (by omega) (by omega)) := by
  let r : ℕ := (Fin.rev i).1
  have hleaf_mem : l[r + 1]'(by omega) ∈ (l.take (r + 2)).toFinset := by
    rw [List.mem_toFinset]
    have htake : r + 1 < (l.take (r + 2)).length := by
      rw [List.length_take]
      omega
    have hget : (l.take (r + 2))[r + 1]'htake = l[r + 1]'(by omega) := by
      exact (List.getElem_take' (xs := l) (i := r + 1) (j := r + 2)
        (by omega) (by omega)).symm
    exact List.mem_of_getElem hget
  have hpar_mem :
      parent (r + 1) (by omega) (by omega) ∈ (l.take (r + 2)).toFinset := by
    have hshort_fin :
        parent (r + 1) (by omega) (by omega) ∈ (l.take (r + 1)).toFinset :=
      (hparent (r + 1) (by omega) (by omega)).1
    have hshort : parent (r + 1) (by omega) (by omega) ∈ l.take (r + 1) := by
      simpa [List.mem_toFinset] using hshort_fin
    obtain ⟨t, ht_short, htval⟩ := List.mem_iff_getElem.mp hshort
    have htlt : t < r + 1 := by
      have : t < (l.take (r + 1)).length := ht_short
      rw [List.length_take] at this
      omega
    have htl : t < l.length := by omega
    have hpar_eq : parent (r + 1) (by omega) (by omega) = l[t]'htl := by
      have hget : l[t]'htl = (l.take (r + 1))[t]'ht_short := by
        exact List.getElem_take' (xs := l) (i := t) (j := r + 1) htl htlt
      exact (hget.trans htval).symm
    rw [List.mem_toFinset]
    have ht_long : t < (l.take (r + 2)).length := by
      rw [List.length_take]
      omega
    have hget_long :
        (l.take (r + 2))[t]'ht_long = parent (r + 1) (by omega) (by omega) := by
      have hget : l[t]'htl = (l.take (r + 2))[t]'ht_long := by
        exact List.getElem_take' (xs := l) (i := t) (j := r + 2) htl (by omega)
      exact hget.symm.trans hpar_eq.symm
    exact List.mem_of_getElem hget_long
  simpa [r] using
    M.faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj
      T parent hparent i label (by simpa [r] using hadj)
      (by simpa [r] using hleaf_mem) (by simpa [r] using hpar_mem)

/-- Label equality for the two original faces incident to the reverse cotree
edge selected at a leaf-peeling step.

This is the dart-level form of the tree-cotree label invariant: in the reverse
dual leaf order, if a face label is constant along every edge of the still
unpeeled dual prefix, then the concrete cotree edge selected at the current
step has equal labels on its two incident original faces. -/
theorem faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : M.Face → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v → label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderReverse T hTsub parent hparent i = M.Edge_mk d ∧
        label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  obtain ⟨d, hedge, hfaces⟩ :=
    M.faceEdgeOfLeafOrderReverse_spec_cases T hTsub parent hparent i
  have hlabel :
      label (dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega))) =
        label (dualVertexEquivFace M
          (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) := by
    exact M.faceEdgeOfLeafOrderReverse_leaf_parent_label_eq_of_forall_adj
      T parent hparent i (fun u => label (dualVertexEquivFace M u))
      (by
        intro u v hu hv huv
        exact hadj hu hv huv)
  refine ⟨d, hedge, ?_⟩
  rcases hfaces with ⟨hd, hedgePerm⟩ | ⟨hd, hedgePerm⟩
  · calc
      label (M.Face_mk d)
          = label (dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega))) := by rw [hd]
      _ = label (dualVertexEquivFace M
            (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) := hlabel
      _ = label (M.Face_mk (M.edgePerm d)) := by rw [hedgePerm]
  · calc
      label (M.Face_mk d)
          = label (dualVertexEquivFace M
            (parent ((Fin.rev i).1 + 1) (by omega) (by omega))) := by rw [hd]
      _ = label (dualVertexEquivFace M (l[(Fin.rev i).1 + 1]'(by omega))) := hlabel.symm
      _ = label (M.Face_mk (M.edgePerm d)) := by rw [hedgePerm]

/-- Label equality for the next reverse-cotree edge after a leaf-peeling step.

Suppose step `i` has just peeled the leaf-parent edge, and `j` is an index whose
unpeeled prefix is the next prefix, i.e.
`(Fin.rev j).1 + 2 = (Fin.rev i).1 + 1`.  If the only edge-local obstruction to
the label invariant on that next prefix is the peeled leaf-parent edge, then the
concrete reverse cotree edge selected at `j` has equal labels on its two
incident original faces.  This is the constructor-facing cotree-edge form of
the spanning cotree leaf-peeling step in Erickson, §10.5. -/
theorem faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    {β : Type*} (label : M.Face → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderReverse T hTsub parent hparent j = M.Edge_mk d ∧
        label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  exact
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj
      T hTsub parent hparent j label
      (by
        have htake :
            (l.take ((Fin.rev j).1 + 2)).toFinset =
              (l.take ((Fin.rev i).1 + 1)).toFinset := by
          rw [hprefix]
        intro u v hu hv huv
        exact
          M.faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_face_label_eq_of_forall_adj_ne_current_parent
            T hl_nodup parent hparent i label hadj
            (by exact htake ▸ hu) (by exact htake ▸ hv))

/-- Representative-invariant label equality for the next reverse-cotree edge.

Suppose step `i` has just peeled the current reverse leaf-parent edge and `j`
selects the next unpeeled prefix.  If a face label is constant on every
non-peeled edge inside that prefix, then every dart representative of the
selected reverse-cotree edge has equal labels on its two incident original
faces.

This is the dart-representative form of the same Lando--Zvonkin
permutational-map fact as
`faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj_ne_current_parent`:
an edge class is the two-dart `α`-orbit, so a label equality proved for one
representative transfers to any representative of that edge class. -/
theorem faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    {β : Type*} (label : M.Face → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v))
    (d : D)
    (hd :
      M.Edge_mk d =
        M.faceEdgeOfLeafOrderReverse T hTsub parent hparent j) :
    label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  obtain ⟨d₀, hedge, hlabel₀⟩ :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj_ne_current_parent
      T hTsub hl_nodup parent hparent i j hprefix label hadj
  have hE : M.Edge_mk d = M.Edge_mk d₀ := by
    exact hd.trans hedge
  exact M.edge_face_label_eq_of_edge_mk_eq label hE hlabel₀

/-- Representative-invariant label equality for any dart whose incident face
pair is the next reverse-cotree parent pair.

This is the face-pair version of
`faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`:
the transport depends only on the unordered pair of dual endpoints prescribed by
the leaf-peeling step, not on the specific selector representative of that edge
class. -/
theorem faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [DecidableEq M.dual.Vertex]
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    {β : Type*} (label : M.Face → β)
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v))
    (d : D)
    (hd :
      s(M.Face_mk d, M.Face_mk (M.edgePerm d)) =
        s(dualVertexEquivFace M (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace M
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega)))) :
    label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  obtain ⟨d₀, hedge, hfaces₀⟩ :=
    M.faceEdgeOfLeafOrderReverse_spec T hTsub parent hparent j
  have hlabel₀ :
      label (M.Face_mk d₀) = label (M.Face_mk (M.edgePerm d₀)) :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
      T hTsub hl_nodup parent hparent i j hprefix label hadj d₀ hedge.symm
  exact M.edge_face_label_eq_of_face_pair_eq label (hd.trans hfaces₀.symm) hlabel₀

/-- Split-face label equality for the reverse cotree edge selected at a
leaf-peeling step.

This specializes the reverse cotree label transport to the face split created
by inserting an edge through one face.  If a face label agrees, on every
original face representative, with the corresponding value of
`insertedFaceSplitPoolEquiv`, and that label is constant across every edge of
the unpeeled dual prefix, then the concrete reverse cotree edge selected at the
current step has equal split-pool labels on its two old incident faces. -/
theorem faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] [DecidableEq M.dual.Vertex]
    (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (label : M.Face → ({f : M.Face // f ≠ M.Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : D,
      label (M.Face_mk d) =
        EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
          ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d)))
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v → label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderReverse T hTsub parent hparent i = M.Edge_mk d ∧
        EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d)) =
          EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk
              (Sum.inl (M.edgePerm d))) := by
  obtain ⟨d, hedge, hlabel_edge⟩ :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj
      T hTsub parent hparent i label hadj
  refine ⟨d, hedge, ?_⟩
  calc
    EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_edge
    _ = EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

/-- Split-pool equality for the next reverse-cotree edge after a leaf-peeling
same-face insertion.

This is the split-face quotient form of
`faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj_ne_current_parent`:
the selected next reverse cotree edge has equal `insertedFaceSplitPoolEquiv`
labels on its two old incident faces once the split label is locally constant
on every edge internal to the next unpeeled prefix except the just-peeled
leaf-parent edge.  The terminology is the spanning cotree side of the
tree-cotree decomposition in Erickson, §10.5, expressed in the
dart-permutation model of Lando--Zvonkin, §1.3.3. -/
theorem faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj_ne_current_parent
    (M : CombinatorialMap D)
    [Fintype D] [DecidableEq D] [DecidableEq M.dual.Vertex]
    (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph M.dual.Vertex) (hTsub : T ≤ M.faceGraph)
    {l : List M.dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → M.dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : M.Face → ({f : M.Face // f ≠ M.Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : D,
      label (M.Face_mk d) =
        EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
          ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d)))
    (hadj : ∀ ⦃u v : M.dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace M u) = label (dualVertexEquivFace M v)) :
    ∃ d : D,
      M.faceEdgeOfLeafOrderReverse T hTsub parent hparent j = M.Edge_mk d ∧
        EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d)) =
          EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk
              (Sum.inl (M.edgePerm d))) := by
  obtain ⟨d, hedge, hlabel_edge⟩ :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj_ne_current_parent
      T hTsub hl_nodup parent hparent i j hprefix label hadj
  refine ⟨d, hedge, ?_⟩
  calc
    EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_edge
    _ = EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((EdgeInsertion.insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

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
