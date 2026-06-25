/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 6/6 — **SimplicityConnectivity**: the two top-level
EU-witness results — (A) `residualMap_isSimple` and (B) `residualMap_connected`
— assembled from the prefix-step machinery. Split out of
`ResidualMapProperties.lean`; see that coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepCore
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepBulk
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.SameFaceInsertion
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.CotreeBlockStep

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

/-! ## (A) Simplicity. -/

/-- The residual edge `e` has endpoint vertex-classes the residual vertices of
its two anchors `(G.endpoints e).1` and `(G.endpoints e).2`. -/
theorem residualMap_edge_ends (hARR : ArcsRotationRegular G)
    (e : Fin G.numEdges) :
    Edge.ends ((residualMap G hARR).Edge_mk (e, false))
      = s((residualMap G hARR).Vertex_mk (e, false),
          (residualMap G hARR).Vertex_mk (e, true)) := by
  rw [Edge.ends_mk,
    show (residualMap G hARR).edgePerm (e, false) = (e, true) by
      simp [residualMap_edgePerm_apply]]

/-- **(A) `residualMap_isSimple`.** Under no-loops and no-parallel-edges
hypotheses on the drawing `G`, the residual combinatorial map is simple. -/
theorem residualMap_isSimple (hARR : ArcsRotationRegular G)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e') :
    (residualMap G hARR).IsSimple := by
  classical
  -- Anchors of the two ends of edge `e`.
  have hanchor0 : ∀ e : Fin G.numEdges, dartAnchor G (e, false) = (G.endpoints e).1 := by
    intro e; rfl
  have hanchor1 : ∀ e : Fin G.numEdges, dartAnchor G (e, true) = (G.endpoints e).2 := by
    intro e; rfl
  constructor
  · -- No loops: no residual edge is a diagonal.
    intro edge
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    rcases d with ⟨e, b⟩
    -- The ends of edge `e` have anchors `(G.endpoints e).1 ≠ (G.endpoints e).2`,
    -- so their residual vertex classes differ.
    have hne : (residualMap G hARR).Vertex_mk (e, false)
        ≠ (residualMap G hARR).Vertex_mk (e, true) := by
      rw [Ne, residualMap_vertexMk_eq_iff, hanchor0, hanchor1]
      exact hloop e
    -- `Edge_mk (e,b) = Edge_mk (e,false)`.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]
          exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    change ¬ (Edge.ends ((residualMap G hARR).Edge_mk (e, b))).IsDiag
    rw [hedge, residualMap_edge_ends]
    rw [Sym2.mk_isDiag_iff]
    exact hne
  · -- No parallel edges: `Edge.ends` injective.
    intro edge edge' hends
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    obtain ⟨d', rfl⟩ := Quotient.exists_rep edge'
    rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    -- Reduce both to the `false`-end representative.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    have hedge' : (residualMap G hARR).Edge_mk (e', b')
        = (residualMap G hARR).Edge_mk (e', false) := by
      cases b' with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    -- It suffices to show `(e,false)` and `(e',false)` are the same edge.
    suffices hgoal : (residualMap G hARR).Edge_mk (e, false)
        = (residualMap G hARR).Edge_mk (e', false) by
      change (residualMap G hARR).Edge_mk (e, b) = (residualMap G hARR).Edge_mk (e', b')
      rw [hedge, hedge', hgoal]
    -- From the endpoint-pair injectivity.
    have hends : Edge.ends ((residualMap G hARR).Edge_mk (e, b))
        = Edge.ends ((residualMap G hARR).Edge_mk (e', b')) := hends
    rw [hedge, hedge', residualMap_edge_ends, residualMap_edge_ends] at hends
    -- `hends` : `s(V e.1, V e.2) = s(V e'.1, V e'.2)` as residual vertex classes.
    -- We split on the two ways the unordered pair can match.
    rw [Sym2.eq_iff] at hends
    -- In either case, anchors of edge `e` are a permutation of anchors of `e'`.
    have key : s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- false↦false, true↦true
        rw [Sym2.eq_iff]; left
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor0] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor1] at h2
        exact ⟨h1, h2⟩
      · -- false↦true, true↦false
        rw [Sym2.eq_iff]; right
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor1] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor0] at h2
        exact ⟨h1, h2⟩
    have : e = e' := hpar e e' key
    subst this
    rfl

/-! ## (B) Connectivity. -/

/-- Graph-connectivity of the underlying drawing: any two vertices of `G.V` are
joined by an edge-walk, where an edge `e` connects its two endpoints. Mirrors the
combinatorial map's `Connected`. -/
def DrawnMultigraph.GraphConnected (G : DrawnMultigraph) : Prop :=
  ∀ p q : ↥G.V, Relation.ReflTransGen
    (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q

/-- The vertex adjacency graph of a drawing: two listed vertices are adjacent if
some drawn edge joins them as its declared endpoint pair. This is the simple
graph underlying the drawing's endpoint relation. -/
def DrawnMultigraph.vertexGraph (G : DrawnMultigraph)
    (hjoin : G.ArcsJoinEndpoints) : SimpleGraph ↥G.V where
  Adj p q :=
    ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ))
  symm := by
    intro p q hpq
    rcases hpq with ⟨e, h⟩
    rcases h with h | h
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  loopless := ⟨fun p hp => by
    rcases hp with ⟨e, h⟩
    rcases h with h | h
    · have hloop : (G.endpoints e).1 = (G.endpoints e).2 := by
        simpa using h.1.trans h.2.symm
      exact (DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e) hloop
    · have hloop : (G.endpoints e).1 = (G.endpoints e).2 := by
        simpa using h.1.trans h.2.symm
      exact (DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e) hloop⟩

/-- Under incident coverage, the residual map's vertex graph is exactly the
drawing's endpoint graph.

The equivalence `residualMapVertexEquivOfIncident` identifies each residual
vertex class with its anchor in `G.V`, and each residual edge class is still
represented by the same drawn edge.  Hence vertex adjacencies in the residual
map are precisely the drawing-edge adjacencies on the listed vertices. -/
noncomputable def residualMapVertexGraphIsoOfIncident
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    (residualMap G hARR).vertexGraph ≃g G.vertexGraph hjoin := by
  let e : (residualMap G hARR).Vertex ≃ ↥G.V :=
    residualMapVertexEquivOfIncident G hARR hincident
  refine ⟨e, ?_⟩
  intro u v
  constructor
  · intro huv
    rcases huv with ⟨edge, hedge⟩
    have hne : u ≠ v := by
      intro huv_eq
      have hloop : (G.vertexGraph hjoin).Adj (e u) (e u) := by
        exact ⟨edge, by simpa [huv_eq] using hedge⟩
      exact ((G.vertexGraph hjoin).ne_of_adj hloop) rfl
    refine ⟨hne, (residualMap G hARR).Edge_mk (edge, false), ?_⟩
    rcases hedge with hdir | hswap
    · have hu : (residualMap G hARR).Vertex_mk (edge, false) = u := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hdir.1
      have hv : (residualMap G hARR).Vertex_mk (edge, true) = v := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hdir.2
      rw [residualMap_edge_ends]
      rw [hu, hv]
    · have hu : (residualMap G hARR).Vertex_mk (edge, false) = v := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hswap.1
      have hv : (residualMap G hARR).Vertex_mk (edge, true) = u := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hswap.2
      calc
        Edge.ends ((residualMap G hARR).Edge_mk (edge, false))
            = s(v, u) := by rw [residualMap_edge_ends, hu, hv]
        _ = s(u, v) := Sym2.eq_swap
  · intro huv
    rcases huv with ⟨_hne, ⟨edge, hedge⟩⟩
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    rcases d with ⟨edge, b⟩
    cases b
    · refine ⟨edge, ?_⟩
      have hpair :
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
            ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩) =
            s(e u, e v) := by
        simpa only [e, residualMapVertexEquivOfIncident_apply_vertex_mk, dartAnchor,
          residualMap_edgePerm_apply, Sym2.map_mk] using congrArg (Sym2.map e) hedge
      rw [Sym2.eq_iff] at hpair
      rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
      · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
    · refine ⟨edge, ?_⟩
      have hpair :
          s(⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩,
            ⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩) =
            s(e u, e v) := by
        simpa only [e, residualMapVertexEquivOfIncident_apply_vertex_mk, dartAnchor,
          residualMap_edgePerm_apply, Sym2.map_mk] using congrArg (Sym2.map e) hedge
      have hpair' :
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
            ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩) =
            s(e u, e v) := by
        calc
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
              ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩)
              =
            s(⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩,
              ⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩) := Sym2.eq_swap
          _ = s(e u, e v) := hpair
      rw [Sym2.eq_iff] at hpair'
      rcases hpair' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
      · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩

/-- The drawing's vertex adjacency graph is connected exactly when the drawing
is connected in the `GraphConnected` sense. -/
theorem DrawnMultigraph.vertexGraph_connected
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints) (hconn : G.GraphConnected)
    [Nonempty ↥G.V] :
    (G.vertexGraph hjoin).Connected := by
  refine { preconnected := fun p q => ?_, nonempty := ‹Nonempty ↥G.V› }
  rw [SimpleGraph.reachable_iff_reflTransGen]
  simpa [DrawnMultigraph.vertexGraph] using hconn p q

/-- Every connected drawing determines a spanning tree on its listed vertices.
This is the combinatorial bridge needed for tree-first edge-order arguments. -/
theorem DrawnMultigraph.exists_vertexGraph_spanningTree
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints) (hconn : G.GraphConnected)
    [Nonempty ↥G.V] :
    ∃ T ≤ G.vertexGraph hjoin, T.IsTree := by
  exact SimpleGraph.Connected.exists_isTree_le
    (G := G.vertexGraph hjoin) (G.vertexGraph_connected hjoin hconn)

/-- Under multiplicity `≤ 1`, a vertex-graph adjacency determines a unique
actual drawing edge. This is the edge-level bridge needed to turn a spanning
tree on the drawing's vertex graph into a concrete edge order. -/
theorem DrawnMultigraph.vertexGraph_adj_unique_edge
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) :
    ∃! e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ)) := by
  classical
  change ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ)) at h
  rcases h with ⟨e, he⟩
  refine ⟨e, he, ?_⟩
  intro e' he'
  by_contra hne
  let s : Finset (Fin G.numEdges) :=
    Finset.univ.filter
      (fun i : Fin G.numEdges =>
        G.endpoints i = ((p : ℝ × ℝ), (q : ℝ × ℝ)) ∨
          G.endpoints i = ((q : ℝ × ℝ), (p : ℝ × ℝ)))
  have he_mem : e ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [s, Prod.ext_iff] using he⟩
  have he'_mem : e' ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [s, Prod.ext_iff] using he'⟩
  have hlt : 1 < s.card := by
    rw [Finset.one_lt_card]
    exact ⟨e, he_mem, e', he'_mem, fun hEq => hne hEq.symm⟩
  have hm : s.card ≤ 1 := by
    simpa [s, DrawnMultigraph.multiplicity] using hmult p q
  omega

/-- The chosen drawing edge witnessing a vertex-graph adjacency. -/
noncomputable def DrawnMultigraph.vertexGraphEdge
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) : Fin G.numEdges :=
  Classical.choose (ExistsUnique.exists
    (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h))

/-- The chosen edge really witnesses the adjacency. -/
@[simp] theorem DrawnMultigraph.vertexGraphEdge_spec
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) :
    ((G.endpoints (G.vertexGraphEdge hjoin hmult h)).1 = (p : ℝ × ℝ) ∧
        (G.endpoints (G.vertexGraphEdge hjoin hmult h)).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints (G.vertexGraphEdge hjoin hmult h)).1 = (q : ℝ × ℝ) ∧
        (G.endpoints (G.vertexGraphEdge hjoin hmult h)).2 = (p : ℝ × ℝ)) := by
  exact Classical.choose_spec
    (ExistsUnique.exists (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h))

/-- Any edge witnessing the adjacency is equal to the chosen one. -/
theorem DrawnMultigraph.vertexGraphEdge_eq
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} {e : Fin G.numEdges}
    (h : (G.vertexGraph hjoin).Adj p q)
    (he :
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ))) :
    e = G.vertexGraphEdge hjoin hmult h := by
  exact (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h).unique he
    (G.vertexGraphEdge_spec hjoin hmult h)

/-- The concrete drawing edge selected by the parent edge at step `i` of a
leaf-insertion order on a spanning tree of the drawing's vertex graph. -/
noncomputable def DrawnMultigraph.treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : Fin G.numEdges :=
  G.vertexGraphEdge hjoin hmult
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- The parent edge selected by `treeEdgeOfLeafOrder` joins the new vertex at
position `i + 1` to its chosen earlier parent, in one of the two endpoint
orientations carried by the drawing. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_spec
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ((G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).1 =
        (l[i.1 + 1]'(by omega) : ℝ × ℝ) ∧
      (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).2 =
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)) ∨
    ((G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).1 =
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ) ∧
      (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).2 =
        (l[i.1 + 1]'(by omega) : ℝ × ℝ)) := by
  exact G.vertexGraphEdge_spec hjoin hmult
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- A parent edge selected at an earlier leaf-order step is not incident to a
later leaf-order vertex. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_not_mem_incidentEnds_later
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {j i : Fin (l.length - 1)} (hji : j.1 < i.1) (b : Bool) :
    (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j, b) ∉
      incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
  classical
  intro hmem
  have hnot_later :
      l[i.1 + 1]'(by omega) ∉ (l.take (j.1 + 1)).toFinset :=
    list_getElem_not_mem_take_of_nodup hl_nodup
      (i := i.1 + 1) (n := j.1 + 1) (hi := by omega) (hn := by omega)
  have hparmem :
      parent (j.1 + 1) (by omega) (by omega) ∈ (l.take (j.1 + 1)).toFinset :=
    (hparent (j.1 + 1) (by omega) (by omega)).1
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent j
  rcases hspec with hspec | hspec
  · cases b
    · have hfirst :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).1 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          l[j.1 + 1]'(by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.1.symm.trans hfirst)
      have hidx :
          j.1 + 1 = i.1 + 1 :=
        (List.Nodup.getElem_inj_iff hl_nodup
          (i := j.1 + 1) (hi := by omega)
          (j := i.1 + 1) (hj := by omega)).1 hsub
      omega
    · have hsecond :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).2 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          parent (j.1 + 1) (by omega) (by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.2.symm.trans hsecond)
      exact hnot_later (by simpa [hsub] using hparmem)
  · cases b
    · have hfirst :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).1 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          parent (j.1 + 1) (by omega) (by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.1.symm.trans hfirst)
      exact hnot_later (by simpa [hsub] using hparmem)
    · have hsecond :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).2 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          l[j.1 + 1]'(by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.2.symm.trans hsecond)
      have hidx :
          j.1 + 1 = i.1 + 1 :=
        (List.Nodup.getElem_inj_iff hl_nodup
          (i := j.1 + 1) (hi := by omega)
          (j := i.1 + 1) (hj := by omega)).1 hsub
      omega

/-- The parent edge selected at leaf-order step `i` is incident to the listed new
vertex `l[i+1]`. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ b : Bool,
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i, b) ∈
        incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
  classical
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  rcases hspec with hspec | hspec
  · exact ⟨false, by simp [incidentEnds, hspec.1]⟩
  · exact ⟨true, by simp [incidentEnds, hspec.2]⟩

/-- The parent edge selected at leaf-order step `i` is incident to the chosen
earlier parent. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_mem_incidentEnds_parent
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ b : Bool,
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i, b) ∈
        incidentEnds G (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ) := by
  classical
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  rcases hspec with hspec | hspec
  · exact ⟨true, by simp [incidentEnds, hspec.2]⟩
  · exact ⟨false, by simp [incidentEnds, hspec.1]⟩

/-- A parent edge selected by a vertex-tree leaf-insertion order gives the
corresponding residual-map leaf insertion witness once that edge is the new last
edge of the ordered prefix.

The remaining hypotheses are the genuine prefix-order incidence facts: the
listed leaf vertex has no predecessor-prefix dart, while its chosen parent
already has one. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hedge :
      Fin.castLE hm' (Fin.last m) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm) (l[i.1 + 1]'(by omega) : ℝ × ℝ))
    (hold : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (G.prefixEdges m hm)
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ))
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  classical
  let q : ℝ × ℝ := (l[i.1 + 1]'(by omega) : ℝ × ℝ)
  let p : ℝ × ℝ := (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  have hend :
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = q) ∨
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = q ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p) := by
    rcases hspec with hspec | hspec
    · right
      constructor
      · simpa [DrawnMultigraph.prefixEdges, q, hedge] using hspec.1
      · simpa [DrawnMultigraph.prefixEdges, p, hedge] using hspec.2
    · left
      constructor
      · simpa [DrawnMultigraph.prefixEdges, p, hedge] using hspec.1
      · simpa [DrawnMultigraph.prefixEdges, q, hedge] using hspec.2
  have hqp : q ≠ p := by
    intro hEq
    have hAdj : T.Adj (l[i.1 + 1]'(by omega)) (parent (i.1 + 1) (by omega) (by omega)) :=
      (hparent (i.1 + 1) (by omega) (by omega)).2
    exact hAdj.ne (Subtype.ext (by simpa [q, p] using hEq))
  exact exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints
    (G := G) m hm hm' (p := p) (q := q) hend hqp
    (by
      intro e
      simpa [q] using hleaf e)
    (by simpa [p] using hold)
    hjoin hARR hARR'

/-- A permuted tree-prefix step is a residual-map leaf insertion.

Suppose the edge permutation places the parent edges selected from the
leaf-insertion order in the initial edge positions. At position `i`, with
`1 ≤ i`, all earlier prefix edges are selected at earlier tree-order positions:
the listed new vertex `l[i+1]` has no predecessor dart, while its chosen parent
already has a predecessor dart. Hence the actual prefix step of the permuted
drawing is the leaf insertion specified by
`exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints`. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (i : Fin (l.length - 1)) (hi : 1 ≤ i.1)
    (hm : i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges i.1 hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (i.1 + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π) i.1 hm hm' hARR hARR' := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let q : ℝ × ℝ := (l[i.1 + 1]'(by omega) : ℝ × ℝ)
  let p : ℝ × ℝ := (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)
  have hlast :
      π (Fin.castLE hm' (Fin.last i.1)) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i := by
    have hcast :
        (Fin.castLE hm' (Fin.last i.1) : Fin G.numEdges) = Fin.castLE hk i := by
      apply Fin.ext
      rfl
    simpa [hcast] using hπ i
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  have hend :
      (((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).1 = p ∧
        ((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).2 = q) ∨
      (((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).1 = q ∧
        ((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).2 = p) := by
    rcases hspec with hspec | hspec
    · right
      constructor
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, q, hlast]
          using hspec.1
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, p, hlast]
          using hspec.2
    · left
      constructor
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, p, hlast]
          using hspec.1
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, q, hlast]
          using hspec.2
  have hqp : q ≠ p := by
    intro hEq
    have hAdj : T.Adj (l[i.1 + 1]'(by omega)) (parent (i.1 + 1) (by omega) (by omega)) :=
      (hparent (i.1 + 1) (by omega) (by omega)).2
    exact hAdj.ne (Subtype.ext (by simpa [q, p] using hEq))
  have hleaf : ∀ e : Fin i.1 × Bool,
      e ∉ incidentEnds (H.prefixEdges i.1 hm) q := by
    rintro ⟨e, b⟩ he
    let j : Fin (l.length - 1) := ⟨e.1, by omega⟩
    have hcast :
        (Fin.castLE hm e : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have heH : (Fin.castLE hm e, b) ∈ incidentEnds H q :=
      (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mp he
    have heG : (π (Fin.castLE hm e), b) ∈ incidentEnds G q :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp (by simpa [H] using heH)
    have hnot :
        (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j, b) ∉
          incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) :=
      G.treeEdgeOfLeafOrder_not_mem_incidentEnds_later hjoin hmult T hTsub
        hl_nodup parent hparent (j := j) (i := i) e.2 b
    exact hnot (by simpa [q, hcast, hπ j] using heG)
  have hold : ∃ e : Fin i.1 × Bool, e ∈ incidentEnds (H.prefixEdges i.1 hm) p := by
    have hparent_mem :
        parent (i.1 + 1) (by omega) (by omega) ∈
          (l.take (i.1 + 1)).toFinset :=
      (hparent (i.1 + 1) (by omega) (by omega)).1
    obtain ⟨k, hklt, hk_l, hkval⟩ :=
      exists_getElem_of_mem_take_toFinset hparent_mem
    by_cases hk0 : k = 0
    · let j : Fin (l.length - 1) := ⟨0, by omega⟩
      let e0 : Fin i.1 := ⟨0, by omega⟩
      have hparent_one_mem :
          parent 1 (by omega) (by omega) ∈ (l.take 1).toFinset :=
        (hparent 1 (by omega) (by omega)).1
      obtain ⟨k₁, hk₁lt, hk₁_l, hk₁val⟩ :=
        exists_getElem_of_mem_take_toFinset hparent_one_mem
      have hk₁0 : k₁ = 0 := by omega
      have hparent_one :
          parent 1 (by omega) (by omega) = l[0]'(by omega) := by
        simpa [hk₁0] using hk₁val.symm
      have hparent_current :
          parent (i.1 + 1) (by omega) (by omega) = l[0]'(by omega) := by
        simpa [hk0] using hkval.symm
      obtain ⟨b, hb⟩ :=
        G.treeEdgeOfLeafOrder_mem_incidentEnds_parent hjoin hmult T hTsub parent hparent j
      refine ⟨(e0, b), ?_⟩
      have hcast :
          (Fin.castLE hm e0 : Fin G.numEdges) = Fin.castLE hk j := by
        apply Fin.ext
        rfl
      have hpos_edge :
          π (Fin.castLE hm e0) =
            G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
        rw [hcast]
        exact hπ j
      have hbG : (π (Fin.castLE hm e0), b) ∈ incidentEnds G p := by
        simpa [p, hpos_edge, j, hparent_one, hparent_current] using hb
      have hbH : (Fin.castLE hm e0, b) ∈ incidentEnds H p :=
        (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
      exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mpr hbH
    · let j : Fin (l.length - 1) := ⟨k - 1, by omega⟩
      let epos : Fin i.1 := ⟨k - 1, by omega⟩
      obtain ⟨b, hb⟩ :=
        G.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex hjoin hmult T hTsub parent hparent j
      refine ⟨(epos, b), ?_⟩
      have hcast :
          (Fin.castLE hm epos : Fin G.numEdges) = Fin.castLE hk j := by
        apply Fin.ext
        rfl
      have hpos_edge :
          π (Fin.castLE hm epos) =
            G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
        rw [hcast]
        exact hπ j
      have hk_succ : k - 1 + 1 = k := by omega
      have hbG : (π (Fin.castLE hm epos), b) ∈ incidentEnds G p := by
        simpa [p, hpos_edge, j, hk_succ, hkval] using hb
      have hbH : (Fin.castLE hm epos, b) ∈ incidentEnds H p :=
        (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
      exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mpr hbH
  exact exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints
    (G := H) i.1 hm hm' (p := p) (q := q) hend hqp hleaf hold
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin) hARR hARR'

/-- The full permuted tree prefix is incident to every listed drawing vertex.

For the root vertex, the first selected parent edge is incident to it.  For any
later listed vertex, the selected parent edge from its own insertion step is
incident to it.  Transport through `permuteEdges` and `prefixEdges` converts
these selected original edges into darts of the full tree prefix. -/
theorem DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges) :
    ∀ p : ↥G.V, ∃ d : Fin (l.length - 1) × Bool,
      d ∈ incidentEnds ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
        (p : ℝ × ℝ) := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  intro p
  have hp_mem : p ∈ l :=
    list_mem_of_nodup_length_eq_card hl_nodup hl_len p
  obtain ⟨k, hk_l, hkval⟩ := List.mem_iff_getElem.mp hp_mem
  by_cases hk0 : k = 0
  · let j : Fin (l.length - 1) := ⟨0, by omega⟩
    let e0 : Fin (l.length - 1) := ⟨0, by omega⟩
    have hparent_one_mem :
        parent 1 (by omega) (by omega) ∈ (l.take 1).toFinset :=
      (hparent 1 (by omega) (by omega)).1
    obtain ⟨k₁, hk₁lt, hk₁_l, hk₁val⟩ :=
      exists_getElem_of_mem_take_toFinset hparent_one_mem
    have hk₁0 : k₁ = 0 := by omega
    have hparent_one :
        parent 1 (by omega) (by omega) = l[0]'(by omega) := by
      simpa [hk₁0] using hk₁val.symm
    have hp_root : p = l[0]'(by omega) := by
      simpa [hk0] using hkval.symm
    obtain ⟨b, hb⟩ :=
      G.treeEdgeOfLeafOrder_mem_incidentEnds_parent hjoin hmult T hTsub parent hparent j
    refine ⟨(e0, b), ?_⟩
    have hcast :
        (Fin.castLE hm e0 : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have hpos_edge :
        π (Fin.castLE hm e0) =
          G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
      rw [hcast]
      exact hπ j
    have hbG : (π (Fin.castLE hm e0), b) ∈ incidentEnds G (p : ℝ × ℝ) := by
      simpa [hpos_edge, j, hparent_one, hp_root] using hb
    have hbH : (Fin.castLE hm e0, b) ∈ incidentEnds H (p : ℝ × ℝ) :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
    exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := l.length - 1) (hm := hm)).mpr hbH
  · let j : Fin (l.length - 1) := ⟨k - 1, by omega⟩
    let epos : Fin (l.length - 1) := ⟨k - 1, by omega⟩
    obtain ⟨b, hb⟩ :=
      G.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex hjoin hmult T hTsub parent hparent j
    refine ⟨(epos, b), ?_⟩
    have hcast :
        (Fin.castLE hm epos : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have hpos_edge :
        π (Fin.castLE hm epos) =
          G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
      rw [hcast]
      exact hπ j
    have hk_succ : k - 1 + 1 = k := by omega
    have hbG : (π (Fin.castLE hm epos), b) ∈ incidentEnds G (p : ℝ × ℝ) := by
      simpa [hpos_edge, j, hk_succ, hkval] using hb
    have hbH : (Fin.castLE hm epos, b) ∈ incidentEnds H (p : ℝ × ℝ) :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
    exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := l.length - 1) (hm := hm)).mpr hbH

/-- Incidence supplied by the full permuted tree prefix is still available in
every longer prefix. -/
theorem DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    {m : ℕ}
    (hmTree : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (htree_m : l.length - 1 ≤ m) :
    ∀ p : ↥G.V, ∃ d : Fin m × Bool,
      d ∈ incidentEnds ((G.permuteEdges π).prefixEdges m hm)
        (p : ℝ × ℝ) := by
  intro p
  have htree :=
    G.incidentCoverage_permuted_treePrefix_of_leafOrder
      hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hmTree p
  exact exists_mem_incidentEnds_prefixEdges_of_le
    (G := G.permuteEdges π) hmTree hm htree_m htree

/-- The residual map of the full permuted tree prefix has one vertex class for
each listed drawing vertex. -/
theorem DrawnMultigraph.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (l.length - 1) hm)) :
    Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Vertex =
      Fintype.card ↥G.V := by
  exact residualMap_vertex_card_of_incident
    (G := (G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR
    (by
      intro p
      exact G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm p)

/-- In the full permuted tree prefix, the residual-map edge count is one less
than its vertex count. -/
theorem DrawnMultigraph.residualMap_edge_card_eq_vertex_card_sub_one_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (l.length - 1) hm)) :
    Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Edge =
      Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Vertex - 1 := by
  rw [residualMap_edge_card]
  rw [G.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
    hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR]
  simp [DrawnMultigraph.prefixEdges, Fintype.card_coe, hl_len]

/-- The residual map of the full permuted tree prefix is planar.

This is the formal tree-prefix half of the tree/cotree proof: the first edge is
the one-edge planar base case, and every later tree edge is inserted by the
actual leaf-step witness
`exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder`. -/
theorem DrawnMultigraph.residualMap_isPlanar_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
      (hARR (l.length - 1) hm)).IsPlanar := by
  let H : DrawnMultigraph := G.permuteEdges π
  exact residualMap_isPlanar_prefix_of_insertions_to
    (G := H) 1 (l.length - 1) hARR
    (by
      intro h1
      exact residualMap_prefix_one_isPlanar
        (G := H) h1 (hARR 1 h1)
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
    (by
      intro m hm' hm_start hm_tree
      let i : Fin (l.length - 1) := ⟨m, by omega⟩
      exact G.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
        hjoin hmult T hTsub hl_nodup parent hparent hπ i hm_start
        (Nat.le_of_succ_le hm') hm' (hARR m (Nat.le_of_succ_le hm'))
        (hARR (m + 1) hm'))
    (by omega) hm

/-- The full permuted tree prefix has exactly one residual face.

This is the one-face predecessor needed for the first cotree/same-face
insertion: the tree prefix is planar and has `|E| = |V| - 1`. -/
theorem DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    Fintype.card
      (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
        (hARR (l.length - 1) hm)).Face = 1 := by
  let H : DrawnMultigraph := G.permuteEdges π
  let hARRtree : ArcsRotationRegular (H.prefixEdges (l.length - 1) hm) :=
    hARR (l.length - 1) hm
  have hplanar :
      (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).IsPlanar := by
    simpa [H, hARRtree] using
      G.residualMap_isPlanar_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  have hcard :
      Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Edge =
        Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Vertex - 1 := by
    simpa [H, hARRtree] using
      G.residualMap_edge_card_eq_vertex_card_sub_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARRtree
  have hV : 1 ≤ Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Vertex := by
    rw [G.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
      hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARRtree]
    rw [← hl_len]
    omega
  exact CombinatorialMap.card_face_eq_one_of_isPlanar_of_card_edge_eq_card_vertex_sub_one
    (M := residualMap (H.prefixEdges (l.length - 1) hm) hARRtree) hV hplanar hcard

/-- The first edge after the permuted tree prefix is a same-face insertion.

After the spanning-tree prefix has been inserted, the predecessor residual map
has one face.  Therefore any next edge whose endpoints are listed drawing
vertices has its two predecessor endpoint corners in that same face; the local
same-face constructor supplies the actual
`ResidualMapPrefixStepInsertion.sameFace` witness. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (l.length - 1) hm hm'
      (hARR (l.length - 1) hm) (hARR ((l.length - 1) + 1) hm') := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let m : ℕ := l.length - 1
  let p₁ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
  let p₂ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
  have hp₁ : p₁ ∈ H.V := by
    simpa [p₁, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).1
  have hp₂ : p₂ ∈ H.V := by
    simpa [p₂, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).2
  have hne :
      ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠
        ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 :=
    DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints
      (prefixEdges_arcsJoinEndpoints (G := H) (m + 1) hm'
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
      (Fin.last m)
  have hold₁ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₁ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₁, by simpa [H] using hp₁⟩
    simpa [H, m] using hcov
  have hold₂ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₂ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₂, by simpa [H] using hp₂⟩
    simpa [H, m] using hcov
  have hface :
      Fintype.card (residualMap (H.prefixEdges m hm) (hARR m hm)).Face = 1 := by
    simpa [H, m] using
      G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one
    (G := H) m hm hm'
    (p₁ := p₁) (p₂ := p₂)
    (by rfl) (by rfl)
    (by simpa [p₁, p₂] using hne.symm)
    (by simpa [p₁, p₂] using hne)
    hp₁ hp₂ hold₁ hold₂
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
    (hARR m hm) (hARR (m + 1) hm') hface

/-- Explicit same-face data for the first edge after the permuted tree prefix.

After the spanning-tree prefix has been inserted, the predecessor residual map
has one face. Therefore the next edge comes with concrete predecessor corners
and the corresponding `insertedEdgeMap` vertex splice, not just an abstract
same-face insertion witness. This is the base cotree witness needed before the
later face-pair cotree block can iterate. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_permuted_treePrefix_next
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    Nonempty (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
      (l.length - 1) hm hm'
      (hARR (l.length - 1) hm) (hARR ((l.length - 1) + 1) hm')) := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let m : ℕ := l.length - 1
  let p₁ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
  let p₂ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
  have hp₁ : p₁ ∈ H.V := by
    simpa [p₁, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).1
  have hp₂ : p₂ ∈ H.V := by
    simpa [p₂, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).2
  have hne :
      ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠
        ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 :=
    DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints
      (prefixEdges_arcsJoinEndpoints (G := H) (m + 1) hm'
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
      (Fin.last m)
  have hold₁ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₁ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₁, by simpa [H] using hp₁⟩
    simpa [H, m] using hcov
  have hold₂ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₂ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₂, by simpa [H] using hp₂⟩
    simpa [H, m] using hcov
  have hface :
      Fintype.card (residualMap (H.prefixEdges m hm) (hARR m hm)).Face = 1 := by
    simpa [H, m] using
      G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  exact exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_card_face_eq_one
    (G := H) m hm hm'
    (p₁ := p₁) (p₂ := p₂)
    (by rfl) (by rfl)
    (by simpa [p₁, p₂] using hne.symm)
    (by simpa [p₁, p₂] using hne)
    hp₁ hp₂ hold₁ hold₂
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
    (hARR m hm) (hARR (m + 1) hm') hface

/-- A later selected residual edge has a same-face insertion witness once the
current split-pool equality is known and the spanning-tree prefix is already in
place.

This is the tree-first transport step for arbitrary later residual edges.  The
only geometric/combinatorial input beyond the current split-pool equality is
that the predecessor prefix already contains the full spanning-tree block, so
endpoint incidence for both full-map anchors comes from
`incidentCoverage_permuted_treePrefix_of_leafOrder_of_le`. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (m : ℕ)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (htree_le : lvertex.length - 1 ≤ m + 1)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular
      ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
        s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (m + 1) hm' hm'' hARR' hARR'' := by
  have hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ) := by
    intro p
    exact
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm' htree_le p
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hcoverage hsplit

/-- Explicit same-face data for a later selected residual edge once the current
split-pool equality is known and the spanning-tree prefix is already in place.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq`.
The spanning-tree prefix supplies endpoint incidence for the full-map anchors in
every later predecessor prefix, so the remaining input is exactly the local
current split-pool equality. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (m : ℕ)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (htree_le : lvertex.length - 1 ≤ m + 1)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular
      ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
        s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (m + 1) hm' hm'' hARR' hARR'') := by
  have hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ) := by
    intro p
    exact
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm' htree_le p
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hcoverage hsplit

/-- The first edge after the tree prefix is a same-face insertion.

This is the tree-prefix base case of the residual-map insertion route: after the
spanning-tree block is in place, the next edge is handled by the existing
`exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next`
constructor. -/
theorem DrawnMultigraph.prefixStepInsertion_of_treePrefix_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (_hsplit :
      ∀ (m : ℕ)
        (hm : m ≤ (G.permuteEdges π).numEdges)
        (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
        (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges),
        lvertex.length - 1 ≤ m + 1 →
        ∀ d : Fin G.numEdges × Bool,
        π (Fin.castLE hm'' (Fin.last (m + 1))) =
          residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) →
        ∀ (s₁ s₂ : Fin m × Bool)
          (hs : s₁ ≠ s₂)
          (hsame :
            (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)).facePerm.SameCycle
              s₁ s₂),
        ∀ {p₁ p₂ : ℝ × ℝ}
          (hpnew₁ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).1 = p₁)
          (hpnew₂ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).2 = p₂)
          (hpother₁ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).2 ≠ p₁)
          (hpother₂ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).1 ≠ p₂),
          ((p₁ = dartAnchor G d ∧
              p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
            (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
              p₂ = dartAnchor G d)) →
          (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
          (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
          ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
            (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
            c₁.1 ≠ c₂.1 →
            vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
                (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₁)
                (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₁)
                (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  p₁ _ _
                  (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    (hARR ((m + 1) + 1) hm'') hp₁
                    (arrRadius_pos
                      (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                      (hARR ((m + 1) + 1) hm'') hp₁) le_rfl))
                ((incident_ends_prefix_step_endpoint_old_equiv
                  (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
              incident_ends_prefix_step_endpoint_new_dart
                (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
            vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
                (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₂)
                (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₂)
                (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  p₂ _ _
                  (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    (hARR ((m + 1) + 1) hm'') hp₂
                    (arrRadius_pos
                      (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                      (hARR ((m + 1) + 1) hm'') hp₂) le_rfl))
                ((incident_ends_prefix_step_endpoint_old_equiv
                  (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
              incident_ends_prefix_step_endpoint_new_dart
                (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)) s₁ s₂ hs hsame
                ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm))
                  s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
              insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)) s₁ s₂ hs hsame
                ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm))
                  s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)))
    (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges) (_hmpos : 1 ≤ m)
    (hma : m = lvertex.length - 1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      m (Nat.le_of_succ_le hm') hm' (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm') := by
  simpa [hma] using
    (G.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next
      hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
      parentVertex hparentVertex hπtree hmTree
      (by simpa [hma] using hm') hARR)
/-- A later reverse-cotree block position has the actual same-face insertion
witness once the local same-face corner equality is known.

The old-endpoint incidence hypotheses are discharged from the already-inserted
spanning-tree prefix, transported monotonically to the current predecessor
prefix. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block_of_treePrefix_incidence
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    {a : ℕ}
    (Tface : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTface_sub : Tface ≤ (residualMap G hARRG).faceGraph)
    {lface : List (residualMap G hARRG).dual.Vertex}
    (parentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      parentFace k hk hk' ∈ (lface.take k).toFinset ∧
        Tface.Adj (lface[k]'hk') (parentFace k hk hk'))
    (hblock : a + (lface.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (lface.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            Tface hTface_sub parentFace hparentFace j))
    (j : Fin (lface.length - 1))
    (htree_le : lvertex.length - 1 ≤ a + j.1)
    (hm : a + j.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm'))
    (hface : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' true hpnew₂ →
          (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₁.1 =
            (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + j.1) hm hm' hARR hARR' := by
  let H : DrawnMultigraph := G.permuteEdges π
  have hmTree : lvertex.length - 1 ≤ H.numEdges := by
    simpa [H, DrawnMultigraph.permuteEdges] using hktree
  have hold₁ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G d) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G d, dartAnchor_mem G d⟩
  have hold₂ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G ((residualMap G hARRG).edgePerm d)) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G ((residualMap G hARRG).edgePerm d),
          dartAnchor_mem G ((residualMap G hARRG).edgePerm d)⟩
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block
      π hjoin hARRG Tface hTface_sub parentFace hparentFace hblock hπcotree
      j hm hm' hARR hARR' hold₁ hold₂ hface

theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block_of_treePrefix_incidence
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    {a : ℕ}
    (S : Set (residualMap G hARRG).Edge)
    (Tface : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTface_sub : Tface ≤ (residualMap G hARRG).faceGraphOnEdgeSet S)
    {lface : List (residualMap G hARRG).dual.Vertex}
    (parentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      parentFace k hk hk' ∈ (lface.take k).toFinset ∧
        Tface.Adj (lface[k]'hk') (parentFace k hk hk'))
    (hblock : a + (lface.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (lface.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
            S Tface hTface_sub parentFace hparentFace j))
    (j : Fin (lface.length - 1))
    (htree_le : lvertex.length - 1 ≤ a + j.1)
    (hm : a + j.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm'))
    (hface : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S Tface hTface_sub parentFace hparentFace j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' true hpnew₂ →
          (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₁.1 =
            (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + j.1) hm hm' hARR hARR' := by
  let H : DrawnMultigraph := G.permuteEdges π
  have hmTree : lvertex.length - 1 ≤ H.numEdges := by
    simpa [H, DrawnMultigraph.permuteEdges] using hktree
  have hold₁ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G d) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G d, dartAnchor_mem G d⟩
  have hold₂ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G ((residualMap G hARRG).edgePerm d)) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G ((residualMap G hARRG).edgePerm d),
          dartAnchor_mem G ((residualMap G hARRG).edgePerm d)⟩
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block
      π hjoin hARRG S Tface hTface_sub parentFace hparentFace hblock hπcotree
      j hm hm' hARR hARR' hold₁ hold₂ hface

/-- Parent edges selected from a leaf-insertion order are distinct. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_injective
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent) := by
  classical
  intro i j hij
  let a_i : ↥G.V := l[i.1 + 1]'(by omega)
  let b_i : ↥G.V := parent (i.1 + 1) (by omega) (by omega)
  let a_j : ↥G.V := l[j.1 + 1]'(by omega)
  let b_j : ↥G.V := parent (j.1 + 1) (by omega) (by omega)
  have hAdj_i : (G.vertexGraph hjoin).Adj a_i b_i := by
    exact hTsub (by simpa [a_i, b_i] using (hparent (i.1 + 1) (by omega) (by omega)).2)
  have hAdj_j : (G.vertexGraph hjoin).Adj a_j b_j := by
    exact hTsub (by simpa [a_j, b_j] using (hparent (j.1 + 1) (by omega) (by omega)).2)
  have hspec_i := G.vertexGraphEdge_spec hjoin hmult hAdj_i
  have hspec_j := G.vertexGraphEdge_spec hjoin hmult hAdj_j
  have hEq : G.vertexGraphEdge hjoin hmult hAdj_i =
      G.vertexGraphEdge hjoin hmult hAdj_j := by
    simpa [DrawnMultigraph.treeEdgeOfLeafOrder, a_i, b_i, a_j, b_j] using hij
  rw [hEq] at hspec_i
  have hpair :
      (a_i, b_i) = (a_j, b_j) ∨ (a_i, b_i) = (b_j, a_j) := by
    cases hspec_i with
    | inl hspec_i =>
        cases hspec_j with
        | inl hspec_j =>
            left
            have h1 : a_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            have h2 : b_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            exact Prod.ext h1 h2
        | inr hspec_j =>
            right
            have h1 : a_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            have h2 : b_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            exact Prod.ext h1 h2
    | inr hspec_i =>
        cases hspec_j with
        | inl hspec_j =>
            right
            have h1 : a_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            have h2 : b_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            exact Prod.ext h1 h2
        | inr hspec_j =>
            left
            have h1 : a_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            have h2 : b_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            exact Prod.ext h1 h2
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    rcases hpair with hpair | hpair
    · exact congrArg (fun x : ↥G.V × ↥G.V => s(x.1, x.2)) hpair
    · calc
        s(a_i, b_i) = s(b_j, a_j) := congrArg (fun x : ↥G.V × ↥G.V => s(x.1, x.2)) hpair
        _ = s(a_j, b_j) := Sym2.eq_swap
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- A leaf-insertion order on a spanning tree of the vertex graph selects a
distinct drawing edge for each non-root vertex, namely the tree edge to its
chosen earlier parent. -/
theorem DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (_hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (_hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → Fin G.numEdges, Function.Injective f := by
  exact ⟨G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent,
    G.treeEdgeOfLeafOrder_injective hjoin hmult T hTsub hl_nodup parent hparent⟩

/-- A leaf-insertion order on a spanning tree of the vertex graph determines an
edge permutation that moves those tree edges into the initial segment of the
ambient edge order. This is the permutation-level bridge used by the ordered
prefix insertion route. -/
theorem DrawnMultigraph.exists_treeEdgePermutation_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ hk : l.length - 1 ≤ G.numEdges,
      ∃ f : Fin (l.length - 1) → Fin G.numEdges,
        Function.Injective f ∧
          ∃ π : Equiv.Perm (Fin G.numEdges),
            ∀ i : Fin (l.length - 1), π (f i) = Fin.castLE hk i := by
  classical
  rcases
      DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
        (G := G) hjoin hmult T hTsub hT hl_nodup hl_len parent hparent with
    ⟨f, hf⟩
  have hk : l.length - 1 ≤ G.numEdges := by
    simpa using Fintype.card_le_of_injective f hf
  obtain ⟨π, hπ⟩ := SimpleGraph.Equiv.Perm.exists_map_fin_castLE hk f hf
  exact ⟨hk, f, hf, π, hπ⟩

/-- A leaf-insertion order on a spanning tree of the vertex graph determines an
edge permutation whose initial positions are exactly those tree edges.

This is the prefix-order convention used by `DrawnMultigraph.permuteEdges`: the
edge at new position `i` is the old edge `π i`. -/
theorem DrawnMultigraph.exists_treeEdgePositionPermutation_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ hk : l.length - 1 ≤ G.numEdges,
      ∃ f : Fin (l.length - 1) → Fin G.numEdges,
        Function.Injective f ∧
          ∃ π : Equiv.Perm (Fin G.numEdges),
            ∀ i : Fin (l.length - 1), π (Fin.castLE hk i) = f i := by
  classical
  rcases
      DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
        (G := G) hjoin hmult T hTsub hT hl_nodup hl_len parent hparent with
    ⟨f, hf⟩
  have hk : l.length - 1 ≤ G.numEdges := by
    simpa using Fintype.card_le_of_injective f hf
  obtain ⟨π, hπ⟩ := SimpleGraph.Equiv.Perm.exists_castLE_map_fin hk f hf
  exact ⟨hk, f, hf, π, hπ⟩

/-- A primal tree leaf order yields a dual spanning tree on the residual face
graph carried by the complement of those tree edges.

The tree edges are first transported to the residual map via incident coverage,
so the complementary-dual connectivity theorem from `VertexGraph.lean` applies
to the same primal tree block used by the ordered prefix insertion layer. -/
theorem DrawnMultigraph.exists_faceGraphOnEdgeSet_spanningTree_of_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARR : ArcsRotationRegular G)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V} (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    ∃ Tface ≤ (residualMap G hARR).faceGraphOnEdgeSet
      {e | residualMapEdgeEquiv G hARR e ∉
        Set.range (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent)},
      Tface.IsTree := by
  classical
  let M := residualMap G hARR
  let eV : M.Vertex ≃ ↥G.V := residualMapVertexEquivOfIncident G hARR hincident
  let T' : SimpleGraph M.Vertex := {
    Adj := fun u v => T.Adj (eV u) (eV v)
    symm := by
      intro u v huv
      exact T.symm huv
    loopless := ⟨fun u huv => (T.ne_of_adj huv) rfl⟩
  }
  have hT'iso : T' ≃g T := by
    refine ⟨eV, ?_⟩
    intro u v
    change T.Adj (eV u) (eV v) ↔ T.Adj (eV u) (eV v)
    exact Iff.rfl
  have hT'tree : T'.IsTree := by
    exact (SimpleGraph.Iso.isTree_iff hT'iso).2 hT
  have hT'sub : T' ≤ M.vertexGraph := by
    intro u v huv
    exact (residualMapVertexGraphIsoOfIncident G hjoin hARR hincident).map_rel_iff'.1
      (hTsub huv)
  let l' : List M.Vertex := l.map eV.symm
  have hl'_nodup : l'.Nodup := by
    exact hl_nodup.map eV.symm.injective
  have hl'_len : l'.length = Fintype.card M.Vertex := by
    rw [List.length_map, hl_len]
    symm
    exact residualMap_vertex_card_of_incident (G := G) hARR hincident
  let parent' : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l'.length) → M.Vertex :=
    fun k hk hk' => eV.symm (parent k hk (by simpa [l'] using hk'))
  have hparent' : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l'.length) →
      parent' k hk hk' ∈ (l'.take k).toFinset ∧
        T'.Adj (l'[k]'hk') (parent' k hk hk') := by
    intro k hk hk'
    have hk0 : k < l.length := by
      simpa [l'] using hk'
    have hmem0 : parent k hk hk0 ∈ (l.take k).toFinset :=
      (hparent k hk hk0).1
    have hadj0 : T.Adj (l[k]'hk0) (parent k hk hk0) :=
      (hparent k hk hk0).2
    have hmem_list : parent k hk hk0 ∈ l.take k := by
      simpa [List.mem_toFinset] using hmem0
    have hmem_map : eV.symm (parent k hk hk0) ∈ (l.take k).map eV.symm := by
      exact List.mem_map.mpr ⟨parent k hk hk0, hmem_list, rfl⟩
    have htake : (l.take k).map eV.symm = l'.take k := by
      simp [l']
    have hmem' : parent' k hk hk' ∈ (l'.take k).toFinset := by
      rw [← htake, List.mem_toFinset]
      simpa [parent'] using hmem_map
    have hget : l'[k]'hk' = eV.symm (l[k]'hk0) := by
      simp [l']
    refine ⟨hmem', ?_⟩
    change T.Adj (eV (l'[k]'hk')) (eV (parent' k hk hk'))
    simpa [parent', hget] using hadj0
  let f' : Fin (l'.length - 1) → M.Edge := fun i =>
    M.Edge_mk
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent
        ⟨i.1, by simpa [l'] using i.isLt⟩, false)
  have hf' : ∀ i : Fin (l'.length - 1),
      f' i =
        CombinatorialMap.vertexGraphEdge (M := M)
          (hT'sub (hparent' (i.1 + 1) (by omega) (by omega)).2) := by
    intro i
    let i0 : Fin (l.length - 1) := ⟨i.1, by simpa [l'] using i.isLt⟩
    have hi_pos : 0 < i.1 + 1 := by omega
    have hi0_lt : i0.1 + 1 < l.length := by
      have hi0_lt' : i0.1 < l.length - 1 := i0.isLt
      omega
    have hi'_lt : i.1 + 1 < l'.length := by
      simpa [l', i0] using hi0_lt
    have htree_spec :=
      G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i0
    have hpar :
        ∀ e e' : Fin G.numEdges,
          s((G.endpoints e).1, (G.endpoints e).2)
            = s((G.endpoints e').1, (G.endpoints e').2) → e = e' := by
      classical
      intro e e' hends
      by_contra hne
      let p := (G.endpoints e).1
      let q := (G.endpoints e).2
      have he_mem : e ∈ Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inl rfl⟩
      have he'_ends : G.endpoints e' = (p, q) ∨ G.endpoints e' = (q, p) := by
        rw [Sym2.eq_iff] at hends
        rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · left
          exact Prod.ext h₁.symm h₂.symm
        · right
          exact Prod.ext h₂.symm h₁.symm
      have he'_mem : e' ∈ Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, he'_ends⟩
      have htwo : 1 < (Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card := by
        rw [Finset.one_lt_card]
        exact ⟨e, he_mem, e', he'_mem, hne⟩
      have hone : (Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card
          ≤ 1 := by
        simpa [DrawnMultigraph.multiplicity, p, q] using hmult p q
      omega
    have hsimple : M.IsSimple := by
      refine residualMap_isSimple (G := G) hARR
        (fun e => DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e)
        hpar
    have hends_tree :
        Edge.ends (M := M) (f' i) =
          s(l'[(i.1 + 1)]'hi'_lt,
            parent' (i.1 + 1) hi_pos hi'_lt) := by
      rw [Edge.ends_mk, Sym2.eq_iff]
      rcases htree_spec with hdir | hswap
      · left
        constructor
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                false)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).1 := by
                    simp [M, eV, dartAnchor]
            _ = (l[i0.1 + 1]'hi0_lt : ℝ × ℝ) := hdir.1
            _ = (eV (l'[(i.1 + 1)]'hi'_lt) : ℝ × ℝ) := by
                have hget :
                    l'[(i.1 + 1)]'hi'_lt = eV.symm (l[i0.1 + 1]'hi0_lt) := by
                  simp [l', i0]
                simp [hget]
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                true)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).2 := by
                    simp [M, eV, dartAnchor]
            _ = (parent (i0.1 + 1) hi_pos hi0_lt : ℝ × ℝ) := hdir.2
            _ = (eV (parent' (i.1 + 1) hi_pos hi'_lt) : ℝ × ℝ) := by
                simp [parent', i0]
      · right
        constructor
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                false)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).1 := by
                    simp [M, eV, dartAnchor]
            _ = (parent (i0.1 + 1) hi_pos hi0_lt : ℝ × ℝ) := hswap.1
            _ = (eV (parent' (i.1 + 1) hi_pos hi'_lt) : ℝ × ℝ) := by
                simp [parent', i0]
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                true)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).2 := by
                    simp [M, eV, dartAnchor]
            _ = (l[i0.1 + 1]'hi0_lt : ℝ × ℝ) := hswap.2
            _ = (eV (l'[(i.1 + 1)]'hi'_lt) : ℝ × ℝ) := by
                have hget :
                    l'[(i.1 + 1)]'hi'_lt = eV.symm (l[i0.1 + 1]'hi0_lt) := by
                  simp [l', i0]
                simp [hget]
    have hends_sel :
        Edge.ends (M := M)
          (CombinatorialMap.vertexGraphEdge (M := M)
            (hT'sub (hparent' (i.1 + 1) hi_pos hi'_lt).2)) =
          s(l'[(i.1 + 1)]'hi'_lt,
            parent' (i.1 + 1) hi_pos hi'_lt) := by
      simp
    exact hsimple.2 (hends_tree.trans hends_sel.symm)
  obtain ⟨Tface, hTface_sub, hTface_tree⟩ :=
    CombinatorialMap.exists_faceGraphOnEdgeSet_spanningTree_of_not_mem_range_vertexLeafOrder
      (M := M) T' hT'sub hT'tree hl'_nodup parent' hparent' f' hf'
  refine ⟨Tface, ?_, hTface_tree⟩
  intro u v huv
  rcases hTface_sub huv with ⟨hne, e, he_old, hends⟩
  refine ⟨hne, e, ?_, hends⟩
  change residualMapEdgeEquiv G hARR (dualEdgeEquiv M e) ∉
    Set.range (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent)
  intro hmem
  apply he_old
  rcases hmem with ⟨i0, hi0⟩
  let i : Fin (l'.length - 1) := ⟨i0.1, by simp [l']⟩
  refine ⟨i, ?_⟩
  apply (residualMapEdgeEquiv G hARR).injective
  calc
    residualMapEdgeEquiv G hARR (f' i)
        = G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0 := by
            simp [M, f', i]
    _ = residualMapEdgeEquiv G hARR (dualEdgeEquiv M e) := hi0

/-- A connected drawing with at least two listed vertices has no isolated listed
vertex: every `p : G.V` has an incident dart. -/
theorem incidentCoverage_of_graphConnected_of_two_le
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ) := by
  classical
  intro p
  have hcard' : 1 < Fintype.card ↥G.V := by omega
  rcases Finset.exists_mem_ne
      (s := (Finset.univ : Finset ↥G.V)) hcard' p with
    ⟨q, _hqmem, hqne⟩
  have hpath := hconn p q
  rw [Relation.ReflTransGen.cases_head_iff] at hpath
  rcases hpath with hpq | ⟨r, hstep, _hrq⟩
  · exact False.elim (hqne hpq.symm)
  rcases hstep with ⟨e, hforward | hbackward⟩
  · refine ⟨(e, false), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hforward.1⟩
  · refine ⟨(e, true), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hbackward.2⟩

/-- A connected drawing with at least two listed vertices has at least one edge. -/
theorem one_le_numEdges_of_graphConnected_of_two_le
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    1 ≤ G.numEdges := by
  have hnonempty : Nonempty ↥G.V := by
    rw [← Fintype.card_pos_iff]
    omega
  let p : ↥G.V := Classical.choice hnonempty
  obtain ⟨d, _hd⟩ := incidentCoverage_of_graphConnected_of_two_le G hconn hcard p
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le d.1.val) d.1.isLt)

/-- A connected simple drawing admits the literature's tree-first / carried
cotree-second edge order.

Starting from a spanning tree of the drawing's vertex graph, choose a
leaf-insertion order and extract its concrete drawing edges. The complementary
carried dual face graph on the residual map then has a spanning tree; choosing
its reverse leaf order gives the cotree block. The theorem returns the actual
ordered edge permutation whose initial block is the primal tree order and whose
second block is the carried reverse-cotree order. -/
theorem DrawnMultigraph.exists_treeCotreePositionPermutation_of_graphConnected
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    [DecidableEq (residualMap G hARRG).dual.Vertex] :
    ∃ (Tvertex : SimpleGraph ↥G.V),
      ∃ hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin,
        Tvertex.IsTree ∧
          ∃ lvertex : List ↥G.V,
            lvertex.Nodup ∧
            lvertex.length = Fintype.card ↥G.V ∧
            ∃ parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V,
              ∃ hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
                  parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
                    Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'),
                ∃ Tface : SimpleGraph (residualMap G hARRG).dual.Vertex,
                  ∃ hTface_sub : Tface ≤ (residualMap G hARRG).faceGraphOnEdgeSet
                      {e | residualMapEdgeEquiv G hARRG e ∉
                        Set.range (G.treeEdgeOfLeafOrder hjoin hmult Tvertex
                          hTvertex_sub parentVertex hparentVertex)},
                    Tface.IsTree ∧
                      ∃ lface : List (residualMap G hARRG).dual.Vertex,
                        lface.Nodup ∧
                        lface.length = Fintype.card (residualMap G hARRG).dual.Vertex ∧
                        ∃ parentFace :
                            ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
                              (residualMap G hARRG).dual.Vertex,
                          ∃ hparentFace :
                              ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
                                parentFace k hk hk' ∈ (lface.take k).toFinset ∧
                                  Tface.Adj (lface[k]'hk') (parentFace k hk hk'),
                            ∃ hblock :
                                (lvertex.length - 1) + (lface.length - 1) ≤ G.numEdges,
                              ∃ π : Equiv.Perm (Fin G.numEdges),
                                (∀ i : Fin (lvertex.length - 1),
                                  π (Fin.castLE hblock (Fin.castAdd (lface.length - 1) i)) =
                                    G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
                                      parentVertex hparentVertex i) ∧
                                (∀ j : Fin (lface.length - 1),
                                  π (Fin.castLE hblock (Fin.natAdd (lvertex.length - 1) j)) =
                                    residualMapEdgeEquiv G hARRG
                                      ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
                                        {e | residualMapEdgeEquiv G hARRG e ∉
                                          Set.range (G.treeEdgeOfLeafOrder hjoin hmult Tvertex
                                            hTvertex_sub parentVertex hparentVertex)}
                                        Tface hTface_sub parentFace hparentFace j)) := by
  classical
  have hcardV2 : 2 ≤ Fintype.card ↥G.V := by
    rw [Fintype.card_coe]
    omega
  have hnonemptyV : Nonempty ↥G.V := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨Tvertex, hTvertex_sub, hTvertex_tree⟩ :=
    G.exists_vertexGraph_spanningTree hjoin hconn
  obtain ⟨lvertex, hlvertex_nodup, hlvertex_len, parentVertex, hparentVertex_full⟩ :=
    SimpleGraph.IsTree.exists_leaf_insertion_order_with_parent
      (G := Tvertex) hTvertex_tree
  have hparentVertex :
      ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
        parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
          Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk') := by
    intro k hk hk'
    exact ⟨(hparentVertex_full k hk hk').1, (hparentVertex_full k hk hk').2.1⟩
  have hincident :
      ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
        d ∈ incidentEnds G (p : ℝ × ℝ) :=
    incidentCoverage_of_graphConnected_of_two_le (G := G) hconn hcardV2
  obtain ⟨Tface, hTface_sub, hTface_tree⟩ :=
    G.exists_faceGraphOnEdgeSet_spanningTree_of_treeEdgeOfLeafOrder
      hjoin hmult hARRG Tvertex hTvertex_sub hTvertex_tree
      hlvertex_nodup hlvertex_len parentVertex hparentVertex hincident
  letI : Nonempty (residualMap G hARRG).dual.Vertex := hTface_tree.connected.nonempty
  obtain ⟨lface, hlface_nodup, hlface_len, parentFace, hparentFace_full⟩ :=
    SimpleGraph.IsTree.exists_leaf_insertion_order_with_parent
      (G := Tface) hTface_tree
  have hparentFace :
      ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
        parentFace k hk hk' ∈ (lface.take k).toFinset ∧
          Tface.Adj (lface[k]'hk') (parentFace k hk hk') := by
    intro k hk hk'
    exact ⟨(hparentFace_full k hk hk').1, (hparentFace_full k hk hk').2.1⟩
  let f : Fin (lvertex.length - 1) → Fin G.numEdges :=
    G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub parentVertex hparentVertex
  have hf : Function.Injective f :=
    G.treeEdgeOfLeafOrder_injective hjoin hmult Tvertex hTvertex_sub
      hlvertex_nodup parentVertex hparentVertex
  let g : Fin (lface.length - 1) → Fin G.numEdges := fun j =>
    residualMapEdgeEquiv G hARRG
      ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub parentFace hparentFace j)
  have hg : Function.Injective g := by
    intro i j hij
    apply
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_injective
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub hlface_nodup parentFace hparentFace
    exact (residualMapEdgeEquiv G hARRG).injective hij
  have hdisj : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    intro x hxf hxg
    rcases hxg with ⟨j, rfl⟩
    obtain ⟨d, hedge, hmem, _hfaces⟩ :=
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_spec
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub parentFace hparentFace j
    have hnot : d.1 ∉ Set.range f := by
      simpa [residualMapEdgeEquiv_edge_mk] using hmem
    have hgj : g j = d.1 := by
      dsimp [g]
      rw [hedge]
      simp
    rw [hgj] at hxf
    exact hnot hxf
  have hblock :
      (lvertex.length - 1) + (lface.length - 1) ≤ G.numEdges := by
    let hsum :
        Sum (Fin (lvertex.length - 1)) (Fin (lface.length - 1)) →
          Fin G.numEdges :=
      fun x => Sum.elim f g x
    have hsum_injective : Function.Injective hsum := by
      intro x y hxy
      cases x <;> cases y
      · simp [hsum] at hxy ⊢
        exact hf hxy
      · exfalso
        exact (Set.disjoint_left.mp hdisj) ⟨_, rfl⟩ ⟨_, hxy.symm⟩
      · exfalso
        exact (Set.disjoint_left.mp hdisj) ⟨_, hxy.symm⟩ ⟨_, rfl⟩
      · simp [hsum] at hxy ⊢
        exact hg hxy
    simpa [hsum] using Fintype.card_le_of_injective hsum hsum_injective
  obtain ⟨π, hπtree, hπcotree⟩ :=
    G.exists_edgePositionPermutation_of_tree_faceEdgeOfLeafOrderOnEdgeSetReverse
      hARRG f hf Tface hTface_sub hlface_nodup parentFace hparentFace hblock
  refine ⟨Tvertex, hTvertex_sub, hTvertex_tree, lvertex, hlvertex_nodup,
    hlvertex_len, parentVertex, hparentVertex, Tface, hTface_sub, hTface_tree,
    lface, hlface_nodup, hlface_len, parentFace, hparentFace, hblock, π, ?_, ?_⟩
  · intro i
    simpa [f] using hπtree i
  · intro j
    simpa [f, g] using hπcotree j

/-- Face count is preserved under a `CombinatorialMap.Iso`. -/
theorem card_face_of_iso {D D' : Type*} [Fintype D] [Fintype D']
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (f : CombinatorialMap.Iso M M') :
    Fintype.card M'.Face = Fintype.card M.Face := by
  have hface : f.toEquiv.permCongr M.facePerm = M'.facePerm := f.permCongr_facePerm
  simpa [CombinatorialMap.Face, hface] using
    Fintype.card_congr (quotientSameCycleEquivOfPermCongr f.toEquiv M.facePerm)

/-- Face count after a same-face prefix step insertion: face count increases by one. -/
theorem card_face_residualMap_prefixStep_sameFace
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool) (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex : (prefixStepDartEquiv m).permCongr
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    Fintype.card (residualMap (G.prefixEdges (m + 1) hm') hARR').Face =
      Fintype.card (residualMap (G.prefixEdges m hm) hARR).Face + 1 := by
  let M : CombinatorialMap (Fin m × Bool) := residualMap (G.prefixEdges m hm) hARR
  let M' : CombinatorialMap (Fin (m + 1) × Bool) := residualMap (G.prefixEdges (m + 1) hm') hARR'
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  have hFinserted : Fintype.card (insertedEdgeMap M c₁ c₂).Face =
      Fintype.card M.Face + 1 :=
    (card_face_insertedEdgeMap M c₁ c₂ hc).1 hsame
  have hiso : Fintype.card (insertedEdgeMap M c₁ c₂).Face =
      Fintype.card M'.Face :=
    (card_face_of_iso iso).symm
  rw [hiso] at hFinserted
  simpa [M, M'] using hFinserted

/-- Face count after a leaf prefix step insertion: face count is unchanged. -/
theorem card_face_residualMap_prefixStep_leaf
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (b : Bool) (c : Fin m × Bool)
    (hvertex : (prefixStepDartEquiv m).permCongr
      (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    Fintype.card (residualMap (G.prefixEdges (m + 1) hm') hARR').Face =
      Fintype.card (residualMap (G.prefixEdges m hm) hARR).Face := by
  let M : CombinatorialMap (Fin m × Bool) := residualMap (G.prefixEdges m hm) hARR
  let M' : CombinatorialMap (Fin (m + 1) × Bool) := residualMap (G.prefixEdges (m + 1) hm') hARR'
  have hFleaf : Fintype.card M'.Face = Fintype.card M.Face := by
    cases b with
    | false =>
      let iso := insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
        (G := G) m hm hm' hARR hARR' false c hvertex
      have hcard : Fintype.card (insertedLeafEdgeMap M c).Face =
          Fintype.card M.Face := card_face_insertedLeafEdgeMap M c
      have hiso : Fintype.card M'.Face =
          Fintype.card (insertedLeafEdgeMap M c).Face := by
        simpa [M', insertedLeafEdgeMapAt_false] using card_face_of_iso iso
      calc
        Fintype.card M'.Face = Fintype.card (insertedLeafEdgeMap M c).Face := hiso
        _ = Fintype.card M.Face := hcard
    | true =>
      let iso := insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
        (G := G) m hm hm' hARR hARR' true c hvertex
      let e : (Fin m × Bool ⊕ Fin 2) ≃ (Fin m × Bool ⊕ Fin 2) :=
        (Equiv.refl (Fin m × Bool)).sumCongr (Equiv.swap (0 : Fin 2) 1)
      have hvertex' :
          e.permCongr (insertedLeafEdgeMap M c).vertexPerm =
            (insertedLeafEdgeMapAt M c true).vertexPerm := by
        simpa [e] using leafDartSwap_permCongr_insertedLeafVertexPerm (M := M) c
      have hedge' :
          e.permCongr (insertedLeafEdgeMap M c).edgePerm =
            (insertedLeafEdgeMapAt M c true).edgePerm := by
        simpa [e] using leafDartSwap_permCongr_insertedLeafEdgePerm (M := M)
      let swapIso : CombinatorialMap.Iso (insertedLeafEdgeMap M c)
          (insertedLeafEdgeMapAt M c true) :=
        isoOfPermCongrOfVertexEdge e hvertex' hedge'
      have hFleafSwap : Fintype.card (insertedLeafEdgeMapAt M c true).Face =
          Fintype.card (insertedLeafEdgeMap M c).Face :=
        card_face_of_iso swapIso
      have hcard : Fintype.card (insertedLeafEdgeMap M c).Face =
          Fintype.card M.Face := card_face_insertedLeafEdgeMap M c
      calc
        Fintype.card M'.Face = Fintype.card (insertedLeafEdgeMapAt M c true).Face :=
          card_face_of_iso iso
        _ = Fintype.card (insertedLeafEdgeMap M c).Face := hFleafSwap
        _ = Fintype.card M.Face := hcard
  simpa [M, M'] using hFleaf

/-- Face count through prefix insertions: induction from a starting level.
Given insertion witnesses at every step from `start` onward with a base face count
of 1 at `start`, and assuming all steps after `start` are same-face insertions
(not leaf), the face count at any later prefix level `n` is 1 plus the number of
steps from `start` to `n`. -/
theorem card_face_residualMap_of_prefix_insertions_from
    (start : ℕ) (hstartG : start ≤ G.numEdges)
    (hARR : ∀ (m : ℕ) (hm : m ≤ G.numEdges),
      ArcsRotationRegular (G.prefixEdges m hm))
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (hcardStart : Fintype.card
      (residualMap (G.prefixEdges start hstartG) (hARR start hstartG)).Face = 1)
    (hall_sameFace : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (hsm : start ≤ m),
      ∃ c₁ c₂ hc hsame hvertex,
        hstep m hm' hsm = ResidualMapPrefixStepInsertion.sameFace c₁ c₂ hc hsame hvertex)
    (n : ℕ) (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    Fintype.card (residualMap (G.prefixEdges n hn) (hARR n hn)).Face = 1 + (n - start) := by
  -- The G.prefixEdges at identical m with different bound proofs are equal (proof irrelevance).
  have hprefix_eq (m : ℕ) (hm hm' : m ≤ G.numEdges) : G.prefixEdges m hm = G.prefixEdges m hm' :=
    congrArg (fun (h : m ≤ G.numEdges) => G.prefixEdges m h) (Subsingleton.elim hm hm')
  let P (k : ℕ) : Prop :=
    ∀ (hk : k ≤ G.numEdges),
      Fintype.card (residualMap (G.prefixEdges k hk) (hARR k hk)).Face = 1 + (k - start)
  have hbase : P start := by
    intro hk'
    have heqG : G.prefixEdges start hk' = G.prefixEdges start hstartG := hprefix_eq start hk' hstartG
    have hcardCopy : Fintype.card (residualMap (G.prefixEdges start hk') (hARR start hk')).Face =
        Fintype.card (residualMap (G.prefixEdges start hstartG) (hARR start hstartG)).Face := by
      cases heqG
      rfl
    rw [hcardCopy, hcardStart, Nat.sub_self, add_zero]
  have hstep' : ∀ (k : ℕ), start ≤ k → P k → P (k + 1) := by
    intro k hsk hPk hk'
    have hk : k ≤ G.numEdges := Nat.le_of_succ_le hk'
    have hFk := hPk hk
    have hdata := hstep k hk' hsk
    rcases hall_sameFace k hk' hsk with ⟨c₁, c₂, hc, hsame, hvertex, _hcase⟩
    have hcard_same := card_face_residualMap_prefixStep_sameFace G k hk hk'
      (hARR k hk) (hARR (k + 1) hk') c₁ c₂ hc hsame hvertex
    rw [hcard_same, hFk]
    omega
  exact Nat.le_induction hbase hstep' n hstartn hn

/-- Connected drawings with at least three listed vertices satisfy the
nonempty-edge hypothesis needed by the ordered insertion induction. Thus
prefix-step insertion witnesses for every step after the first edge produce a
planar residual map for the full drawing. -/
theorem exists_residualMap_isPlanar_of_prefix_insertions_connected
    (hjoin : G.ArcsJoinEndpoints)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), 1 ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')) :
    ∃ hARRG : ArcsRotationRegular G, (residualMap G hARRG).IsPlanar :=
  exists_residualMap_isPlanar_of_prefix_insertions (G := G)
    (one_le_numEdges_of_graphConnected_of_two_le (G := G) hconn (by
      rw [Fintype.card_coe]
      omega))
    hjoin hARR hstep

/-- The residual one-step reachability relation. -/
private def resStep (hARR : ArcsRotationRegular G) :
    Fin G.numEdges × Bool → Fin G.numEdges × Bool → Prop :=
  fun a b => b = (residualMap G hARR).vertexPerm a
    ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
    ∨ b = (residualMap G hARR).edgePerm a

/-- A `vertexPerm`-power step is reachable by `ReflTransGen` of the residual step
relation (both natural- and inverse-power directions). -/
theorem reflTransGen_of_vertexPerm_zpow (hARR : ArcsRotationRegular G)
    (k : ℤ) (a : Fin G.numEdges × Bool) :
    Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ k) a) := by
  -- Reduce to natural powers in both directions.
  have hnat : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (n + 1)) a
            = (residualMap G hARR).vertexPerm (((residualMap G hARR).vertexPerm ^ n) a) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inl rfl)
  have hneg : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ (-(m : ℤ))) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (-(↑(n + 1) : ℤ))) a
            = (residualMap G hARR).vertexPerm⁻¹ (((residualMap G hARR).vertexPerm ^ (-(n : ℤ))) a) := by
          rw [show (-(↑(n + 1) : ℤ)) = (-1) + (-(n : ℤ)) by push_cast; ring,
            zpow_add, Equiv.Perm.mul_apply, zpow_neg_one]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inr (Or.inl rfl))
  rcases le_total 0 k with hk | hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast]; exact hnat m a
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hneg m a

/-- **Within-vertex reachability.** Any two darts with the same anchor are joined
by `ReflTransGen` of the residual step relation. -/
theorem reflTransGen_of_same_anchor (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) (h : dartAnchor G d = dartAnchor G d') :
    Relation.ReflTransGen (resStep G hARR) d d' := by
  have hsc : (residualMap G hARR).vertexPerm.SameCycle d d' := by
    have : (residualMap G hARR).Vertex_mk d = (residualMap G hARR).Vertex_mk d' :=
      (residualMap_vertexMk_eq_iff G hARR d d').mpr h
    rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq''] at this
    exact this
  obtain ⟨k, hk⟩ := hsc
  have := reflTransGen_of_vertexPerm_zpow G hARR k d
  rwa [hk] at this

/-- **Edge bridge.** The two ends of edge `e` are joined by a single residual
`edgePerm` step. -/
theorem reflTransGen_edge_bridge (hARR : ArcsRotationRegular G) (e : Fin G.numEdges) :
    Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) := by
  refine Relation.ReflTransGen.single (Or.inr (Or.inr ?_))
  simp [residualMap_edgePerm_apply]

/-- The residual step relation matches the `Connected` definition's step. -/
theorem resStep_eq_connectedStep (hARR : ArcsRotationRegular G)
    (a b : Fin G.numEdges × Bool) :
    resStep G hARR a b ↔
      (b = (residualMap G hARR).vertexPerm a
        ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
        ∨ b = (residualMap G hARR).edgePerm a) := Iff.rfl

/-- **(B) `residualMap_connected`.** Under graph-connectivity of `G`, the residual
combinatorial map is connected. -/
theorem residualMap_connected (hARR : ArcsRotationRegular G)
    (hconn : G.GraphConnected) :
    (residualMap G hARR).Connected := by
  classical
  -- We prove `ReflTransGen (resStep)` between any two darts, then convert.
  suffices hmain : ∀ d d' : Fin G.numEdges × Bool,
      Relation.ReflTransGen (resStep G hARR) d d' by
    intro d d'
    exact hmain d d'
  intro d d'
  -- Step 1: connect `d` to the `false`-end of its own edge `(d.1, false)`,
  -- and `d'` to `(d'.1, false)`; then connect anchors via graph walk.
  -- Anchors of d and d' lie in G.V.
  set pa : ↥G.V := ⟨dartAnchor G d, dartAnchor_mem G d⟩ with hpa
  set pb : ↥G.V := ⟨dartAnchor G d', dartAnchor_mem G d'⟩ with hpb
  -- Reachability between two darts whose anchors are joined by a graph walk:
  -- prove a general lemma by induction on the walk.
  have lift : ∀ (p q : ↥G.V),
      Relation.ReflTransGen
        (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
          ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
          ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q →
      ∀ (x : Fin G.numEdges × Bool), dartAnchor G x = (p : ℝ × ℝ) →
        ∀ (y : Fin G.numEdges × Bool), dartAnchor G y = (q : ℝ × ℝ) →
          Relation.ReflTransGen (resStep G hARR) x y := by
    intro p q hwalk
    induction hwalk with
    | refl =>
        intro x hx y hy
        exact reflTransGen_of_same_anchor G hARR x y (by rw [hx, hy])
    | @tail b c _hpb hbc ih =>
        intro x hx y hy
        obtain ⟨e, hcase⟩ := hbc
        rcases hcase with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · -- endpoints e = (b, c): use end `false` at anchor b, `true` at anchor c.
          have hf : dartAnchor G (e, false) = (b : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (c : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, false) :=
            ih x hx (e, false) hf
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) :=
            reflTransGen_edge_bridge G hARR e
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, true) y :=
            reflTransGen_of_same_anchor G hARR (e, true) y (by rw [ht, hy])
          exact (step1.trans step2).trans step3
        · -- endpoints e = (c, b): use end `false` at anchor c, `true` at anchor b.
          have hf : dartAnchor G (e, false) = (c : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (b : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, true) :=
            ih x hx (e, true) ht
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, true) (e, false) :=
            Relation.ReflTransGen.single (Or.inr (Or.inr (by simp [residualMap_edgePerm_apply])))
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, false) y :=
            reflTransGen_of_same_anchor G hARR (e, false) y (by rw [hf, hy])
          exact (step1.trans step2).trans step3
  exact lift pa pb (hconn pa pb) d rfl d' rfl

/-- A connected drawing with at least one edge determines a spanning tree on the
vertices of its residual map. -/
theorem residualMap_exists_vertexGraph_spanningTree
    (hARR : ArcsRotationRegular G) (hconn : G.GraphConnected) (hnum : 0 < G.numEdges) :
    ∃ T ≤ (residualMap G hARR).vertexGraph, T.IsTree := by
  letI : Nonempty (residualMap G hARR).Vertex := by
    refine ⟨(residualMap G hARR).Vertex_mk (⟨0, hnum⟩, false)⟩
  exact CombinatorialMap.exists_vertexGraph_spanningTree
    (M := residualMap G hARR)
    (by simpa using residualMap_connected G hARR hconn)

/-- A connected drawing with at least one edge determines a spanning tree on the
faces of its residual map. -/
theorem residualMap_exists_faceGraph_spanningTree
    (hARR : ArcsRotationRegular G) (hconn : G.GraphConnected) (hnum : 0 < G.numEdges) :
    ∃ T ≤ (residualMap G hARR).faceGraph, T.IsTree := by
  letI : Nonempty (residualMap G hARR).Vertex := by
    refine ⟨(residualMap G hARR).Vertex_mk (⟨0, hnum⟩, false)⟩
  exact CombinatorialMap.exists_faceGraph_spanningTree
    (M := residualMap G hARR)
    (by simpa using residualMap_connected G hARR hconn)


end CrossingLemma
