/-
The forgetful map from a plane drawing
(`DrawnMultigraph`) to the abstract finite multigraph (`AbstractPlanarizedMultigraph`)
consumed by the EU planar edge bound, with its cardinality identities.

NO-AXIOM: this file is sorry-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

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
    simp only [abstractize, Sym2.eq_iff, Prod.ext_iff, Subtype.ext_iff]
  -- Rewrite the abstract fiber filter to the drawing-multiplicity filter.
  have hcard :
      (Finset.univ.filter
        fun e : Fin G.numEdges =>
          (abstractize G).edgeVerts e = s(a, b)).card
        =
      (Finset.univ.filter
        fun i : Fin G.numEdges =>
          G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card := by
    apply Finset.card_bij (fun e _ => e)
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, (hpred e).mp he.2⟩
    · intro e₁ _ e₂ _ h
      exact h
    · intro e he
      rw [Finset.mem_filter] at he
      exact ⟨e, by rw [Finset.mem_filter]; exact ⟨he.1, (hpred e).mpr he.2⟩, rfl⟩
  -- The drawing-multiplicity filter is exactly `G.multiplicity a.val b.val`.
  have hmulteq :
      (Finset.univ.filter
        fun i : Fin G.numEdges =>
          G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card
        = G.multiplicity a.val b.val := by
    rw [DrawnMultigraph.multiplicity]
  exact (hcard.trans hmulteq).le.trans (hmult a.val b.val)

end CrossingLemma
