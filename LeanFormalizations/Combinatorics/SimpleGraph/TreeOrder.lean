/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Leaf lemmas for finite simple trees

This helper module packages the small tree facts needed by the later
tree-first / leaf-insertion induction:

* a finite nontrivial tree has a degree-one vertex;
* degree one is equivalent to having a unique neighbor;
* removing a degree-one vertex from a tree leaves a tree.

The statements are standard `SimpleGraph` lemmas in mathlib style and stay
axiom-free.
-/

namespace SimpleGraph

theorem IsTree.exists_degree_eq_one {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Nontrivial V] (h : G.IsTree) :
    ∃ v : V, G.degree v = 1 := by
  have hmin : G.minDegree = 1 := h.minDegree_eq_one_of_nontrivial
  classical
  have hnonempty : (Finset.univ : Finset V).Nonempty := by simp
  obtain ⟨v, hv, hle⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun v : V => G.degree v) hnonempty
  have hdegmin : G.degree v = G.minDegree := by
    apply le_antisymm
    · exact le_minDegree_of_forall_le_degree G (G.degree v) (by
        intro x
        exact hle x (by simp))
    · exact G.minDegree_le_degree v
  refine ⟨v, ?_⟩
  rw [hmin] at hdegmin
  exact hdegmin

/-- A finite nontrivial tree has a leaf, i.e. a vertex with a unique neighbor. -/
theorem IsTree.exists_leaf {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Nontrivial V] (h : G.IsTree) :
    ∃ v : V, ∃! w, G.Adj v w := by
  rcases SimpleGraph.IsTree.exists_degree_eq_one G h with ⟨v, hv⟩
  exact ⟨v, (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hv⟩

/-- Removing a degree-one vertex from a tree leaves a tree. -/
theorem IsTree.induce_compl_singleton_of_degree_eq_one {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {v : V} (h : G.IsTree) (hdeg : G.degree v = 1) :
    (G.induce {v}ᶜ).IsTree := by
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one h.connected hdeg
  · exact h.isAcyclic.induce {v}ᶜ

/-- A finite nontrivial tree admits a leaf whose removal leaves a tree. -/
theorem IsTree.exists_leaf_and_induce {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Nontrivial V] (h : G.IsTree) :
    ∃ v : V, G.degree v = 1 ∧ (G.induce {v}ᶜ).IsTree := by
  rcases SimpleGraph.IsTree.exists_degree_eq_one G h with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  exact SimpleGraph.IsTree.induce_compl_singleton_of_degree_eq_one G h hv

/-- A finite nontrivial tree admits a leaf whose removal drops the edge count by one. -/
theorem IsTree.exists_leaf_and_induce_card_edgeFinset_pred {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nontrivial V] (h : G.IsTree) :
    ∃ v : V, G.degree v = 1 ∧ ((G.induce {v}ᶜ).IsTree ∧
      (G.induce {v}ᶜ).edgeFinset.card = G.edgeFinset.card - 1) := by
  rcases SimpleGraph.IsTree.exists_leaf_and_induce G h with ⟨v, hvdeg, hvtree⟩
  refine ⟨v, hvdeg, hvtree, ?_⟩
  calc
    (G.induce {v}ᶜ).edgeFinset.card = (G.deleteIncidenceSet v).edgeFinset.card := by
      simpa using (SimpleGraph.card_edgeFinset_induce_compl_singleton G v)
    _ = G.edgeFinset.card - G.degree v := by
      simpa using (SimpleGraph.card_edgeFinset_deleteIncidenceSet G v)
    _ = G.edgeFinset.card - 1 := by rw [hvdeg]

/-- A finite connected graph that is not a tree has a non-bridge edge whose
deletion preserves connectedness. This is the edge-choice point for the
non-tree phase of a recursive tree/cotree decomposition. -/
theorem Connected.exists_nonbridge_edge_delete_connected {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hconn : G.Connected) (hnot : ¬ G.IsTree) :
    ∃ x y : V, G.Adj x y ∧ ¬ G.IsBridge s(x, y) ∧ (G.deleteEdges {s(x, y)}).Connected := by
  have hnotacyc : ¬ G.IsAcyclic := by
    intro hacyc
    exact hnot ⟨hconn, hacyc⟩
  have hne : ∃ x y : V, G.Adj x y ∧ ¬ G.IsBridge s(x, y) := by
    by_contra hcontra
    have hall : ∀ ⦃x y : V⦄, G.Adj x y → G.IsBridge s(x, y) := by
      intro x y hxy
      by_contra hbridge
      exact hcontra ⟨x, y, hxy, hbridge⟩
    exact hnotacyc ((isAcyclic_iff_forall_adj_isBridge).2 hall)
  rcases hne with ⟨x, y, hxy, hbridge⟩
  exact ⟨x, y, hxy, hbridge, hconn.connected_delete_edge_of_not_isBridge hbridge⟩

/-- The finite set underlying a mapped list is the image of the underlying
finite set. -/
theorem List.toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp [List.mem_toFinset, Finset.mem_image]

/-- Inducing on a subset of an induced graph is isomorphic to inducing on the
corresponding subset of the ambient graph. -/
noncomputable def induceInduceIso {V : Type*} (G : SimpleGraph V) (s : Set V)
    (t : Set ↥s) :
    (SimpleGraph.induce t (SimpleGraph.induce s G)) ≃g
      SimpleGraph.induce {x : V | ∃ h : x ∈ s, ⟨x, h⟩ ∈ t} G := by
  refine ⟨Equiv.subtypeSubtypeEquivSubtypeExists (p := fun x : V => x ∈ s)
      (q := fun x : ↥s => x ∈ t), ?_⟩
  intro a b
  constructor <;> intro h
  · simpa [SimpleGraph.induce_adj,
      Equiv.subtypeSubtypeEquivSubtypeExists_apply_coe] using h
  · simpa [SimpleGraph.induce_adj,
      Equiv.subtypeSubtypeEquivSubtypeExists_apply_coe] using h

/-- Treehood is preserved when an induced graph is re-expressed as an induced
graph on the ambient vertex set. -/
theorem induceInduce_isTree_iff {V : Type*} (G : SimpleGraph V) (s : Set V)
    (t : Set ↥s) :
    (SimpleGraph.induce t (SimpleGraph.induce s G)).IsTree ↔
      (SimpleGraph.induce {x : V | ∃ h : x ∈ s, ⟨x, h⟩ ∈ t} G).IsTree := by
  exact SimpleGraph.Iso.isTree_iff (induceInduceIso G s t)

/-- Connectedness is preserved when an induced graph is re-expressed as an
induced graph on the ambient vertex set. -/
theorem induceInduce_isConnected_iff {V : Type*} (G : SimpleGraph V) (s : Set V)
    (t : Set ↥s) :
    (SimpleGraph.induce t (SimpleGraph.induce s G)).Connected ↔
      (SimpleGraph.induce {x : V | ∃ h : x ∈ s, ⟨x, h⟩ ∈ t} G).Connected := by
  exact SimpleGraph.Iso.connected_iff (induceInduceIso G s t)

/-- Treehood is unchanged by inducing on the full vertex set. -/
theorem induceUniv_isTree_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.induce Set.univ G).IsTree ↔ G.IsTree := by
  exact SimpleGraph.Iso.isTree_iff (SimpleGraph.induceUnivIso G)

/-- Connectedness is unchanged by inducing on the full vertex set. -/
theorem induceUniv_isConnected_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.induce Set.univ G).Connected ↔ G.Connected := by
  exact SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso G)

/-- The complement of a singleton subset has cardinality one less than the
ambient finite type. -/
theorem card_compl_singleton {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := by
  have h1 : Fintype.card ↥({v} : Set V) = 1 := by
    convert Fintype.card_subtype_eq (y := v) using 1
  rw [Fintype.card_compl_set, h1]

/-- A finite tree can be peeled one leaf at a time: there is an ordering of the
vertices such that every nontrivial prefix removal leaves a tree. This is the
vertex-order version of the leaf-removal induction used later for tree-first
and tree-cotree style arguments. -/
theorem IsTree.exists_leaf_removal_order_aux {V : Type*} (n : ℕ) :
    ∀ (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V],
      Fintype.card V = n + 1 → G.IsTree →
        ∃ l : List V,
          l.Nodup ∧ l.length = n + 1 ∧
          ∀ k : ℕ, k < l.length →
            (G.induce {x : V | x ∉ (l.take k).toFinset}).IsTree
  := by
    induction n generalizing V with
    | zero =>
        intro G _instFintype _instDecEq _instDecRel _instNonempty hcard htree
        have hcard1 : Fintype.card V = 1 := by simpa using hcard
        rcases (Classical.choice (show Nonempty V from inferInstance)) with v
        refine ⟨[v], ?_, ?_, ?_⟩
        · simp
        · simp
        · intro k hk
          have hk0 : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
          subst hk0
          have hset : ({x : V | x ∉ (∅ : Finset V)} : Set V) = Set.univ := by
            ext x
            simp
          have hiso : G.induce {x : V | x ∉ (∅ : Finset V)} ≃g G.induce (Set.univ : Set V) := by
            rw [hset]
          exact (SimpleGraph.Iso.isTree_iff hiso).mpr ((induceUniv_isTree_iff (G := G)).2 htree)
    | succ n ih =>
        intro G _instFintype _instDecEq _instDecRel _instNonempty hcard htree
        have hnontriv : Nontrivial V := by
          apply Fintype.one_lt_card_iff_nontrivial.mp
          have hpos : 1 < Fintype.card V := by omega
          exact hpos
        rcases SimpleGraph.IsTree.exists_leaf_and_induce_card_edgeFinset_pred G htree with
          ⟨v, hvdeg, hHtree, hcardH⟩
        let H : SimpleGraph ↥({v}ᶜ : Set V) := G.induce {v}ᶜ
        have hcardH' : Fintype.card ↥({v}ᶜ : Set V) = n + 1 := by
          rw [card_compl_singleton, hcard]
          omega
        have ihH :
            ∃ l : List ↥({v}ᶜ : Set V),
              l.Nodup ∧ l.length = n + 1 ∧
              ∀ k : ℕ, k < l.length →
                (H.induce {x : ↥({v}ᶜ : Set V) | x ∉ (List.take k l).toFinset}).IsTree := by
          have hcardH'' : Fintype.card ↥({v}ᶜ : Set V) = n + 1 := by
            simpa using hcardH'
          exact ih (G := H)
            hcardH''
            (by simpa [H] using hHtree)
        rcases ihH with ⟨l, hl_nodup, hl_len, hl_tree⟩
        refine ⟨v :: l.map Subtype.val, ?_, ?_, ?_⟩
        · have hnot : v ∉ l.map Subtype.val := by
            intro hv'
            rcases List.mem_map.mp hv' with ⟨u, hu, hu'⟩
            exact u.2 hu'
          exact List.Nodup.cons hnot (List.Nodup.map Subtype.val_injective hl_nodup)
        · simp [hl_len]
        · intro k hk
          cases k with
          | zero =>
              have hset0 : ({x : V | x ∉ (∅ : Finset V)} : Set V) = Set.univ := by
                ext x
                simp
              have hiso0 : G.induce {x : V | x ∉ (∅ : Finset V)} ≃g G.induce (Set.univ : Set V) := by
                rw [hset0]
              exact (SimpleGraph.Iso.isTree_iff hiso0).mpr ((induceUniv_isTree_iff (G := G)).2 htree)
          | succ k =>
              have hk' : k < l.length := by
                have hlen : k.succ < l.length + 1 := by simpa [hl_len] using hk
                exact Nat.lt_of_succ_lt_succ hlen
              have hIH := hl_tree k hk'
              have hambient :
                  (G.induce {x : V | ∃ hx : x ∈ ({v}ᶜ : Set V),
                    ⟨x, hx⟩ ∉ (List.take k l).toFinset}).IsTree := by
                simpa [H] using
                  (induceInduce_isTree_iff (G := G) ({v}ᶜ)
                    {x : ↥({v}ᶜ : Set V) | x ∉ (List.take k l).toFinset}).1 hIH
              have hset' : ∀ x : V,
                  x ∈ {x : V | ∃ hx : x ∈ ({v}ᶜ : Set V),
                    ⟨x, hx⟩ ∉ (List.take k l).toFinset} ↔
                  x ∈ {x : V | x ∉ (v :: List.take k (List.map Subtype.val l)).toFinset} := by
                intro x
                by_cases hxv : x = v
                · subst hxv
                  simp [List.mem_toFinset]
                · have hleft :
                      x ∈ {x : V | ∃ hx : x ∈ ({v}ᶜ : Set V),
                        ⟨x, hx⟩ ∉ (List.take k l).toFinset} ↔
                        ⟨x, hxv⟩ ∉ (List.take k l).toFinset := by
                    constructor
                    · intro hx
                      rcases hx with ⟨hx, hxnot⟩
                      simpa using hxnot
                    · intro hxnot
                      exact ⟨hxv, hxnot⟩
                  have hmem_bridge :
                      ⟨x, hxv⟩ ∈ List.take k l ↔ x ∈ List.take k (List.map Subtype.val l) := by
                    constructor
                    · intro hsub
                      simpa [List.map_take] using
                        (List.mem_map.mpr ⟨⟨x, hxv⟩, hsub, rfl⟩ :
                          x ∈ List.map Subtype.val (List.take k l))
                    · intro hxmem
                      have hxmem' : x ∈ List.map Subtype.val (List.take k l) := by
                        simpa [List.map_take] using hxmem
                      rw [List.mem_map] at hxmem'
                      rcases hxmem' with ⟨u, hu, huv⟩
                      have hu_eq : u = ⟨x, hxv⟩ := by
                        ext
                        exact huv
                      simpa [hu_eq] using hu
                  have htail :
                      ⟨x, hxv⟩ ∉ (List.take k l).toFinset ↔
                        x ∉ (List.take k (List.map Subtype.val l)).toFinset := by
                    rw [List.mem_toFinset, List.mem_toFinset]
                    exact not_congr hmem_bridge
                  have hright :
                      x ∈ {x : V | x ∉ (v :: List.take k (List.map Subtype.val l)).toFinset} ↔
                        x ∉ (List.take k (List.map Subtype.val l)).toFinset := by
                    simp [List.mem_toFinset, hxv]
                  exact hleft.trans (htail.trans hright.symm)
              have hset :
                  ({x : V | ∃ hx : x ∈ ({v}ᶜ : Set V),
                    ⟨x, hx⟩ ∉ (List.take k l).toFinset} : Set V)
                    = {x : V | x ∉ (v :: List.take k (List.map Subtype.val l)).toFinset} := by
                exact Set.ext hset'
              have hiso :
                  G.induce {x : V | ∃ hx : x ∈ ({v}ᶜ : Set V),
                    ⟨x, hx⟩ ∉ (List.take k l).toFinset}
                    ≃g G.induce {x : V | x ∉ (v :: List.take k (List.map Subtype.val l)).toFinset} := by
                rw [hset]
              exact (SimpleGraph.Iso.isTree_iff hiso).mp hambient

/-- A finite tree admits a vertex order whose successive prefix removals leave
trees. -/
theorem IsTree.exists_leaf_removal_order {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (h : G.IsTree) :
    ∃ l : List V,
      l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ k : ℕ, k < l.length →
        (G.induce {x : V | x ∉ (l.take k).toFinset}).IsTree := by
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hcard : Fintype.card V = (Fintype.card V - 1) + 1 := by
    simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos hpos).symm
  have haux := (IsTree.exists_leaf_removal_order_aux (V := V) (n := Fintype.card V - 1)
    G hcard h)
  rcases haux with ⟨l, hl_nodup, hl_len, hl_tree⟩
  refine ⟨l, hl_nodup, ?_, hl_tree⟩
  omega

/-- A finite tree admits a vertex order whose successive prefix removals leave
trees, and every non-final vertex is a leaf in the tree remaining at its removal
step. This is the form needed to choose an actual edge at each step of a future
insertion-order proof. -/
private theorem IsTree.exists_leaf_removal_order_with_leaves_aux {V : Type*} (n : ℕ) :
    ∀ (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V],
      Fintype.card V = n + 1 → G.IsTree →
        ∃ l : List V,
          l.Nodup ∧ l.length = n + 1 ∧
          ∀ k : ℕ, (hk : k + 1 < l.length) →
            ∃! w : V, w ∉ (l.take k).toFinset ∧ G.Adj (l[k]'(by omega)) w := by
  induction n generalizing V with
  | zero =>
      intro G _instFintype _instDecEq _instDecRel _instNonempty hcard htree
      have hcard1 : Fintype.card V = 1 := by omega
      rcases (Classical.choice (show Nonempty V from inferInstance)) with v
      refine ⟨[v], ?_, ?_, ?_⟩
      · simp
      · simp
      · intro k hk
        simp at hk
  | succ n ih =>
      intro G _instFintype _instDecEq _instDecRel _instNonempty hcard htree
      have hnontriv : Nontrivial V := by
        apply Fintype.one_lt_card_iff_nontrivial.mp
        have hpos : 1 < Fintype.card V := by omega
        exact hpos
      rcases SimpleGraph.IsTree.exists_leaf_and_induce_card_edgeFinset_pred G htree with
        ⟨v, hvdeg, hHtree, hcardH⟩
      let H : SimpleGraph ↥({v}ᶜ : Set V) := G.induce {v}ᶜ
      have hcardH' : Fintype.card ↥({v}ᶜ : Set V) = n + 1 := by
        rw [card_compl_singleton, hcard]
        omega
      have ihH :
          ∃ l : List ↥({v}ᶜ : Set V),
            l.Nodup ∧ l.length = n + 1 ∧
            ∀ k : ℕ, (hk : k + 1 < l.length) →
              ∃! w : ↥({v}ᶜ : Set V), w ∉ (l.take k).toFinset ∧ H.Adj (l[k]'(by omega)) w := by
        exact ih (G := H) hcardH' (by simpa [H] using hHtree)
      rcases ihH with ⟨l, hl_nodup, hl_len, hl_leaf⟩
      refine ⟨v :: l.map Subtype.val, ?_, ?_, ?_⟩
      · have hnot : v ∉ l.map Subtype.val := by
          intro hv'
          rcases List.mem_map.mp hv' with ⟨u, hu, hu'⟩
          exact u.2 hu'
        exact List.Nodup.cons hnot (List.Nodup.map Subtype.val_injective hl_nodup)
      · simp [hl_len]
      · intro k hk
        cases k with
        | zero =>
            simpa using (SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := G) (v := v)).mp hvdeg
        | succ k =>
            have hk' : k + 1 < l.length := by
              simpa [hl_len] using hk
            have huniq := hl_leaf k hk'
            rcases huniq with ⟨w, hw, huniq⟩
            rcases hw with ⟨hw_not, hw_adj⟩
            refine ⟨w.1, ?_, ?_⟩
            · exact ⟨by
                intro hmem
                rw [List.mem_toFinset] at hmem
                have hw_ne_v : w.1 ≠ v := by
                  intro hwv
                  simpa [hwv] using w.2
                simp [hw_ne_v] at hmem
                have hmem'' : w.1 ∈ List.map Subtype.val (List.take k l) := by
                  simpa [List.map_take] using hmem
                rw [List.mem_map] at hmem''
                rcases hmem'' with ⟨u, hu, huv⟩
                have hu_eq : u = w := by
                  ext
                  simpa using huv
                have hmem' : w ∈ (List.take k l).toFinset := by
                  simpa [hu_eq, List.mem_toFinset] using hu
                exact hw_not hmem'
              , by
                simpa [H, SimpleGraph.induce_adj, List.getElem_map] using hw_adj⟩
            · intro z hz
              rcases hz with ⟨hz_not, hz_adj⟩
              have hz_ne_v : z ≠ v := by
                intro hzv
                subst hzv
                simp [List.mem_toFinset] at hz_not
              let z' : ↥({v}ᶜ : Set V) := ⟨z, hz_ne_v⟩
              have hz_tail : z' ∉ (List.take k l).toFinset := by
                intro hmem
                rw [List.mem_toFinset] at hmem
                have hmem' : z ∈ List.map Subtype.val (List.take k l) := by
                  exact List.mem_map.mpr ⟨z', hmem, rfl⟩
                have hzmap : z ∈ (List.take k (List.map Subtype.val l)).toFinset := by
                  rw [List.mem_toFinset]
                  simpa [List.map_take] using hmem'
                have hzcons : z ∈ (v :: List.take k (List.map Subtype.val l)).toFinset := by
                  simpa [List.mem_toFinset, hz_ne_v] using hzmap
                exact hz_not hzcons
              have hz_adj' : H.Adj (l[k]'(by omega)) z' := by
                simpa [H, SimpleGraph.induce_adj, List.getElem_map] using hz_adj
              have hEq : z' = w := huniq z' ⟨hz_tail, hz_adj'⟩
              exact congrArg Subtype.val hEq

/-- A finite tree admits a vertex order whose successive prefix removals leave
trees. -/
theorem IsTree.exists_leaf_removal_order_with_leaves {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (h : G.IsTree) :
    ∃ l : List V,
      l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ k : ℕ, (hk : k + 1 < l.length) →
        ∃! w : V, w ∉ (l.take k).toFinset ∧ G.Adj (l[k]'(by omega)) w := by
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hcard : Fintype.card V = (Fintype.card V - 1) + 1 := by
    simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos hpos).symm
  have haux := (IsTree.exists_leaf_removal_order_with_leaves_aux (V := V) (n := Fintype.card V - 1)
    G hcard h)
  rcases haux with ⟨l, hl_nodup, hl_len, hl_leaf⟩
  refine ⟨l, hl_nodup, ?_, hl_leaf⟩
  omega

/-- A finite tree admits an insertion order: there is an ordering of the
vertices such that every non-initial vertex has a unique neighbor among the
earlier vertices.  This is the reverse of the leaf-removal order above and is
the shape used by later tree-first insertion arguments. -/
theorem IsTree.exists_leaf_insertion_order {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (h : G.IsTree) :
    ∃ l : List V,
      l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
        ∃! w : V, w ∈ (l.take k).toFinset ∧ G.Adj (l[k]'hk') w := by
  classical
  rcases SimpleGraph.IsTree.exists_leaf_removal_order_with_leaves G h with
    ⟨l0, hl0_nodup, hl0_len, hl0_leaf⟩
  refine ⟨l0.reverse, ?_, ?_, ?_⟩
  · simpa using (List.nodup_reverse.mpr hl0_nodup)
  · simpa using hl0_len
  · intro k hk hk'
    let i : ℕ := l0.length - 1 - k
    have hklen : k < l0.length := by
      simpa [List.length_reverse] using hk'
    have hi : i + 1 < l0.length := by
      dsimp [i]
      omega
    have hi' : i < l0.length := by omega
    have hget :
        (l0.reverse)[k]'(by simpa [List.length_reverse] using hk') =
          l0[i]'hi' := by
      simpa [i] using
        (List.get_reverse' (l := l0) (n := ⟨k, by simpa [List.length_reverse] using hk'⟩)
          (by dsimp [i]; omega))
    have hfull : ∀ x : V, x ∈ l0 := by
      intro x
      have hcardto : l0.toFinset.card = Fintype.card V := by
        rw [List.toFinset_card_of_nodup hl0_nodup, hl0_len]
      have hsub : l0.toFinset ⊆ (Finset.univ : Finset V) := by
        intro y hy
        simpa using hy
      have hcardle : (Finset.univ : Finset V).card ≤ l0.toFinset.card := by
        rw [Finset.card_univ, hcardto]
      have hfin : l0.toFinset = (Finset.univ : Finset V) := by
        exact Finset.eq_of_subset_of_card_le hsub hcardle
      have hx : x ∈ l0.toFinset := by
        simpa [hfin]
      simpa [List.mem_toFinset] using hx
    have hstep := hl0_leaf i (by dsimp [i]; omega)
    rcases hstep with ⟨w, hw, huniq⟩
    have hw_not_take : w ∉ l0.take i := by
      simpa [List.mem_toFinset] using hw.1
    have hw_adj : G.Adj (l0[i]'hi') w := by
      simpa [hget] using hw.2
    have hw_mem : w ∈ l0 := hfull w
    have hw_drop : w ∈ l0.drop (i + 1) := by
      have hw_drop_i : w ∈ l0.drop i := by
        have happend : w ∈ l0.take i ++ l0.drop i := by
          simpa [List.take_append_drop] using hw_mem
        rw [List.mem_append] at happend
        exact Or.resolve_left happend hw_not_take
      have hdrop_eq : l0.drop i = l0.get ⟨i, hi'⟩ :: l0.drop (i + 1) := by
        simpa using (List.cons_get_drop_succ (l := l0) (n := ⟨i, hi'⟩)).symm
      have hw_drop_cons : w ∈ l0.get ⟨i, hi'⟩ :: l0.drop (i + 1) := by
        rw [hdrop_eq] at hw_drop_i
        exact hw_drop_i
      rw [List.mem_cons] at hw_drop_cons
      cases hw_drop_cons with
      | inl hEq =>
          exfalso
          exact (G.ne_of_adj hw_adj) hEq.symm
      | inr htail =>
          exact htail
    have hw_rtake : w ∈ l0.rtake k := by
      have hlen : l0.length - k = i + 1 := by
        dsimp [i]
        omega
      simpa [List.rtake, hlen] using hw_drop
    refine ⟨w, ?_, ?_⟩
    · have hw_take : w ∈ (l0.reverse).take k := by
        simpa [List.rtake_eq_reverse_take_reverse, List.mem_reverse] using hw_rtake
      exact ⟨by simpa [List.mem_toFinset] using hw_take, by simpa [hget] using hw.2⟩
    · intro z hz
      have hz_rtake : z ∈ l0.rtake k := by
        simpa [List.rtake_eq_reverse_take_reverse, List.mem_reverse] using hz.1
      have hlen : l0.length - k = i + 1 := by
        dsimp [i]
        omega
      have hz_drop : z ∈ l0.drop (i + 1) := by
        simpa [List.rtake, hlen] using hz_rtake
      have hz_drop_i : z ∈ l0.drop i := by
        have hz_drop1 : z ∈ List.drop 1 (l0.drop i) := by
          simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hz_drop
        exact List.mem_of_mem_drop hz_drop1
      have hnodup_split : (l0.take i ++ l0.drop i).Nodup := by
        simpa [List.take_append_drop] using hl0_nodup
      have hdisj : (l0.take i).Disjoint (l0.drop i) := List.Nodup.disjoint hnodup_split
      have hz_not_take : z ∉ l0.take i := by
        intro hz_take
        exact hdisj hz_take hz_drop_i
      have hz_adj : G.Adj (l0[i]'hi') z := by
        simpa [hget] using hz.2
      have hz_not_take_fin : z ∉ (l0.take i).toFinset := by
        simpa [List.mem_toFinset] using hz_not_take
      have huniq' := huniq z ⟨hz_not_take_fin, hz_adj⟩
      exact huniq'

/-- A finite tree admits a leaf-insertion order together with a chosen earlier
neighbor for each non-initial vertex. This packages the unique-neighbor data as
a function, which is the form needed for later edge-order extraction. -/
theorem IsTree.exists_leaf_insertion_order_with_parent {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (h : G.IsTree) :
    ∃ l : List V,
      l.Nodup ∧ l.length = Fintype.card V ∧
      ∃ parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → V,
        ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
          parent k hk hk' ∈ (l.take k).toFinset ∧
            G.Adj (l[k]'hk') (parent k hk hk') ∧
            ∀ z : V, z ∈ (l.take k).toFinset ∧ G.Adj (l[k]'hk') z →
              z = parent k hk hk' := by
  classical
  rcases SimpleGraph.IsTree.exists_leaf_insertion_order G h with
    ⟨l, hl_nodup, hl_len, hl_unique⟩
  refine ⟨l, hl_nodup, hl_len, ?_⟩
  refine ⟨fun k hk hk' => Classical.choose (hl_unique k hk hk').exists, ?_⟩
  intro k hk hk'
  have hspec := (hl_unique k hk hk').exists
  have hchoose : Classical.choose hspec ∈ (l.take k).toFinset ∧
      G.Adj (l[k]'hk') (Classical.choose hspec) := by
    simpa using Classical.choose_spec hspec
  refine ⟨hchoose.1, hchoose.2, ?_⟩
  intro z hz
  exact ExistsUnique.unique (hl_unique k hk hk') hz hchoose

/-- The parent-edge map associated to a leaf-insertion order is injective.

This is the combinatorial core behind turning a tree-order into an explicit
edge enumeration. The result only needs that each non-initial vertex has some
earlier neighbor; uniqueness of the earlier neighbor is not used here. -/
theorem IsTree.parentEdgeMap_injective {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {l : List V}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧ G.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (fun i : Fin (l.length - 1) =>
      s(l[i.1 + 1], parent (i.1 + 1) (by omega) (by omega))) := by
  classical
  intro i j hij
  let f : Fin (l.length - 1) → Sym2 V :=
    fun k => s(l[k.1 + 1], parent (k.1 + 1) (by omega) (by omega))
  have hcontra : ∀ {a b : Fin (l.length - 1)}, a.1 < b.1 → f a = f b → False := by
    intro a b hab hEq
    have hbmem : l[b.1 + 1] ∈ f b := by
      simp [f]
    have hmem : l[b.1 + 1] ∈ f a := by
      have hEq' : f a = f b := hEq
      simpa [hEq'] using hbmem
    rw [Sym2.mem_iff] at hmem
    rcases hmem with hmem | hmem
    · have ha : a.1 + 1 < l.length := by omega
      have hb : b.1 + 1 < l.length := by omega
      have hEqIdx : a.1 + 1 = b.1 + 1 := by
        exact (List.Nodup.getElem_inj_iff hl_nodup (i := a.1 + 1) (hi := ha)
            (j := b.1 + 1) (hj := hb)).1 hmem.symm
      omega
    · have ha : a.1 + 1 < l.length := by omega
      have hb : b.1 + 1 < l.length := by omega
      have hmeml : l[b.1 + 1] ∈ l := by
        simpa using (List.mem_of_getElem (l := l) (i := b.1 + 1) (h := hb) rfl)
      have hnot : l[b.1 + 1] ∉ (l.take (a.1 + 1)).toFinset := by
        intro hmemtake
        rw [List.mem_toFinset] at hmemtake
        have hidxlt : l.idxOf (l[b.1 + 1]) < a.1 + 1 := by
          exact (List.mem_take_iff_idxOf_lt (l := l) (a := l[b.1 + 1]) hmeml).1 hmemtake
        have hidxeq : l.idxOf (l[b.1 + 1]) = b.1 + 1 := by
          simpa using (hl_nodup.idxOf_getElem (i := b.1 + 1) hb)
        omega
      have hparmem : parent (a.1 + 1) (by omega) (by omega) ∈ (l.take (a.1 + 1)).toFinset := by
        exact (hparent (a.1 + 1) (by omega) (by omega)).1
      have hmemtake : l[b.1 + 1] ∈ (l.take (a.1 + 1)).toFinset := by
        simpa [hmem] using hparmem
      exact hnot hmemtake
  by_cases hlt : i.1 < j.1
  · exact False.elim (hcontra hlt hij)
  · by_cases hgt : j.1 < i.1
    · exact False.elim (hcontra hgt hij.symm)
    · have heq : i.1 = j.1 := by omega
      exact Fin.ext heq

/-- The parent-edge map associated to a leaf-insertion order is a bijection onto
the edge finset. Together with the vertex-order helper above, this is the
bridge from tree order data to an explicit edge enumeration. -/
theorem IsTree.parentEdgeMap_bijective {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h : G.IsTree) {l : List V}
    (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧ G.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Bijective (fun i : Fin (l.length - 1) =>
      (⟨s(l[i.1 + 1], parent (i.1 + 1) (by omega) (by omega)),
        by
          have h0 : 0 < i.1 + 1 := by omega
          have hlt : i.1 + 1 < l.length := by omega
          simpa [SimpleGraph.mem_edgeSet] using
            (hparent (i.1 + 1) h0 hlt).2⟩ : ↥G.edgeFinset)) := by
  classical
  let f : Fin (l.length - 1) → ↥G.edgeFinset :=
    fun i => (⟨s(l[i.1 + 1], parent (i.1 + 1) (by omega) (by omega)),
      by
        have h0 : 0 < i.1 + 1 := by omega
        have hlt : i.1 + 1 < l.length := by omega
        simpa [SimpleGraph.mem_edgeSet] using
          (hparent (i.1 + 1) h0 hlt).2⟩ : ↥G.edgeFinset)
  have hinj : Function.Injective f := by
    intro i j hij
    have hsym2 : s(l[i.1 + 1], parent (i.1 + 1) (by omega) (by omega)) =
        s(l[j.1 + 1], parent (j.1 + 1) (by omega) (by omega)) := by
      exact congrArg Subtype.val hij
    exact parentEdgeMap_injective (G := G) (l := l) hl_nodup parent hparent hsym2
  have hcard : Fintype.card (Fin (l.length - 1)) = Fintype.card ↥G.edgeFinset := by
    rw [Fintype.card_fin, Fintype.card_coe]
    have htreecard := SimpleGraph.IsTree.card_edgeFinset (G := G) h
    omega
  have hequiv : Fin (l.length - 1) ≃ ↥G.edgeFinset := Fintype.equivOfCardEq hcard
  have hsurj : Function.Surjective f := by
    exact (Finite.injective_iff_surjective_of_equiv hequiv).mp hinj
  change Function.Bijective f
  exact ⟨hinj, hsurj⟩

/-- A concrete edge-order equivalence obtained from a tree's parent data. -/
noncomputable def IsTree.parentEdgeEquiv {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (h : G.IsTree) {l : List V}
    (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧ G.Adj (l[k]'hk') (parent k hk hk')) :
    Fin (l.length - 1) ≃ ↥G.edgeFinset :=
  Equiv.ofBijective
    (fun i : Fin (l.length - 1) =>
      (⟨s(l[i.1 + 1], parent (i.1 + 1) (by omega) (by omega)),
        by
          have h0 : 0 < i.1 + 1 := by omega
          have hlt : i.1 + 1 < l.length := by omega
          simpa [SimpleGraph.mem_edgeSet] using
            (hparent (i.1 + 1) h0 hlt).2⟩ : ↥G.edgeFinset))
    (IsTree.parentEdgeMap_bijective (G := G) (h := h) (l := l) hl_nodup hl_len parent hparent)

/-- Any injective map `Fin k → Fin n` can be extended to a permutation of
`Fin n` that sends its image to the initial segment `Fin.castLE hk`. -/
theorem Equiv.Perm.exists_map_fin_castLE {k n : ℕ} (hk : k ≤ n)
    (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin k, σ (f i) = Fin.castLE hk i := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f (Fin.castLE hk) hf
    (Fin.castLE_injective hk)
  exact ⟨σ, hσ⟩

end SimpleGraph
