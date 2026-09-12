/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

/-!
# Abstractize: forgetful map to the abstract multigraph

The forgetful map from a plane drawing
(`DrawnMultigraph`) to the abstract finite multigraph (`AbstractPlanarizedMultigraph`)
consumed by the EU planar edge bound, with its cardinality identities.

Axiom status: this file is sorry-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace CrossingLemma

/-- Forgetful map: discard the drawing data of a `DrawnMultigraph`, retaining
only the finite multigraph carrier (vertex subtype, edge index type, unordered
endpoint pairs) that the EU planar edge bound consumes. -/
def abstractize (G : DrawnMultigraph) : AbstractPlanarizedMultigraph where
  Vertex := ↥G.V
  Edge := Fin G.numEdges
  vertexFintype := FinsetCoe.fintype G.V
  edgeFintype := Fin.fintype _
  edgeVerts e :=
    s(⟨(G.endpoints e).1, (G.endpoints_mem e).1⟩,
      ⟨(G.endpoints e).2, (G.endpoints_mem e).2⟩)

/-- The abstract vertex count equals the drawing's vertex-set cardinality. -/
theorem abstractize_vertex_card (G : DrawnMultigraph) :
    Fintype.card (abstractize G).Vertex = G.V.card := by
  simp only [abstractize]
  exact Fintype.card_coe G.V

/-- The abstract edge count equals the drawing's edge count. -/
theorem abstractize_edge_card (G : DrawnMultigraph) :
    Fintype.card (abstractize G).Edge = G.numEdges := by
  simp only [abstractize]
  exact Fintype.card_fin G.numEdges

/-- Multiplicity-transfer bridge: a uniform drawing-multiplicity cap `M` on
every ordered pair `(p, q)` transfers to the abstract `PairMultiplicityBound`. -/
theorem abstractize_pairMultiplicityBound (G : DrawnMultigraph) (M : ℕ)
    (hmult : ∀ p q, G.multiplicity p q ≤ M) :
    PairMultiplicityBound (abstractize G) M := by
  classical
  -- Reduce the unordered pair to a representative `s(a, b)`.
  refine fun uv => ?_
  refine Sym2.ind (fun a b => ?_) uv
  -- The abstract fiber over `s(a, b)` is in bijection (via the identity on
  -- `Fin G.numEdges`) with the drawing's edges between `a.val` and `b.val`.
  -- Establish the two filter predicates agree pointwise.
  have hpred : ∀ e : Fin G.numEdges,
      ((abstractize G).edgeVerts e = s(a, b)) ↔
        (G.endpoints e = (a.val, b.val) ∨ G.endpoints e = (b.val, a.val)) := by
    intro e
    let ea : (abstractize G).Vertex := ⟨(G.endpoints e).1, (G.endpoints_mem e).1⟩
    let eb : (abstractize G).Vertex := ⟨(G.endpoints e).2, (G.endpoints_mem e).2⟩
    change s(ea, eb) = s(a, b) ↔ _
    constructor
    · intro h
      rcases (@Sym2.eq_iff _ ea eb a b).mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        apply Prod.ext
        · exact congrArg Subtype.val ha
        · exact congrArg Subtype.val hb
      · right
        apply Prod.ext
        · exact congrArg Subtype.val ha
        · exact congrArg Subtype.val hb
    · intro h
      apply (@Sym2.eq_iff _ ea eb a b).mpr
      rcases h with h | h
      · left
        constructor
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · apply Subtype.ext
          exact congrArg Prod.snd h
      · right
        constructor
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · apply Subtype.ext
          exact congrArg Prod.snd h
  -- Rewrite the abstract fiber filter to the drawing-multiplicity filter.
  have hcard :
      (Finset.univ.filter
        fun e : (abstractize G).Edge =>
          (abstractize G).edgeVerts e = s(a, b)).card
        =
      ((Finset.univ : Finset (Fin G.numEdges)).filter
        fun i : Fin G.numEdges =>
          G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card := by
    apply Finset.card_bij (fun e _ => (⟨e.val, e.isLt⟩ : Fin G.numEdges))
    · intro e he
      let e' : Fin G.numEdges := ⟨e.val, e.isLt⟩
      rw [Finset.mem_filter] at he ⊢
      have hee : (show Fin G.numEdges from e) = e' := by
        apply Fin.ext
        rfl
      have hEdge : (abstractize G).edgeVerts e = (abstractize G).edgeVerts e' := by
        rfl
      exact ⟨he.1, (hpred e').mp (by rw [← hEdge]; exact he.2)⟩
    · intro e₁ _ e₂ _ h
      exact congrArg (fun e : Fin G.numEdges => (⟨e.val, e.isLt⟩ : (abstractize G).Edge)) h
    · intro e he
      let e' : (abstractize G).Edge := ⟨e.val, e.isLt⟩
      rw [Finset.mem_filter] at he
      have he' : e' ∈ Finset.univ.filter
          (fun i : (abstractize G).Edge => (abstractize G).edgeVerts i = s(a, b)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hpred e).mpr he.2⟩
      exact ⟨e', he', by apply Fin.ext; rfl⟩
  -- The drawing-multiplicity filter is exactly `G.multiplicity a.val b.val`.
  have hmulteq :
      (Finset.univ.filter
        fun i : Fin G.numEdges =>
          G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card
        = G.multiplicity a.val b.val := by
    rw [DrawnMultigraph.multiplicity]
  have huniv :
      (@Finset.univ (abstractize G).Edge (abstractize G).edgeFintype) =
        (Finset.univ : Finset (Fin G.numEdges)) := by
    change (Finset.univ : Finset (Fin G.numEdges)) = Finset.univ
    rfl
  have hfilter :
      (@Finset.univ (abstractize G).Edge (abstractize G).edgeFintype).filter
          (fun e => (abstractize G).edgeVerts e = s(a, b)) =
        (Finset.univ : Finset (Fin G.numEdges)).filter
          (fun e => (abstractize G).edgeVerts e = s(a, b)) := by
    rw [huniv]
  rw [hfilter] at hcard
  rw [hfilter]
  exact (hcard.trans hmulteq).le.trans (hmult a.val b.val)

end CrossingLemma
