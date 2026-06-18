/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.Geometry.Convex.SimpleConvexPolygon

/-!
# Unit-distance elimination-order counting

The classical degeneracy / elimination-order argument applied to unit distances:
if, in some index order, every point sees at most `k` unit-distance neighbors
*later* in the order, then the number of unordered unit-distance pairs is at
most `n * k` (linear in the number of points).

* `unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le` /
  `UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_mul` — the
  elimination-order bound for an indexed family `Fin n → ℝ × ℝ`.
* `unitDirectedPairFinset_card_le_mul_of_neighbor_card_le` /
  `unitPairIndexFinset_card_le_mul_of_neighbor_card_le` — the (weaker) uniform
  degree-bound forms via directed handshaking.
* `SimpleConvexPolygon.*` — the same bounds re-expressed for the concrete
  `SimpleConvexPolygon` model, indexing by the listed vertex order.

This is a standard combinatorial-geometry counting argument, not new
mathematics.
-/

open Finset


/-- Unit-distance neighbors of an indexed point. -/
noncomputable def unitNeighborFinset {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => dist (p i) (p j) = 1

/-- Unit-distance neighbors that appear later in the chosen index order. -/
noncomputable def unitForwardNeighborFinset {n : ℕ} (p : Fin n → ℝ × ℝ) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact (unitNeighborFinset p i).filter fun j => i.val < j.val

/--
An elimination-order certificate for unit distances in an indexed finite point
family.  The index order is the deletion order; the field says each point sees
at most `k` unit-distance neighbors that have not yet been deleted.
-/
def UnitDistanceEliminationOrder {n : ℕ} (p : Fin n → ℝ × ℝ) (k : ℕ) : Prop :=
  ∀ i, (unitForwardNeighborFinset p i).card ≤ k

/-- Directed unit-distance incidences, represented as dependent pairs. -/
noncomputable def unitDirectedPairFinset {n : ℕ} (p : Fin n → ℝ × ℝ) :
    Finset (Σ _i : Fin n, Fin n) :=
  Finset.univ.sigma fun i => unitNeighborFinset p i

/--
Unordered unit-distance index pairs, represented by their increasing
orientation `i.val < j.val`.
-/
noncomputable def unitPairIndexFinset {n : ℕ} (p : Fin n → ℝ × ℝ) :
    Finset (Σ _i : Fin n, Fin n) := by
  classical
  exact (unitDirectedPairFinset p).filter fun ij => ij.1.val < ij.2.val

/-- The unordered pair set is the sigma of later unit-neighbors. -/
theorem unitPairIndexFinset_eq_sigma_forward {n : ℕ} (p : Fin n → ℝ × ℝ) :
    unitPairIndexFinset p =
      Finset.univ.sigma (fun i => unitForwardNeighborFinset p i) := by
  classical
  ext ij
  simp [unitPairIndexFinset, unitDirectedPairFinset, unitNeighborFinset,
    unitForwardNeighborFinset]

/-- Exact count of unordered unit-distance pairs by later-neighbor fibers. -/
theorem unitPairIndexFinset_card_eq_sum_forwardNeighbor_card
    {n : ℕ} (p : Fin n → ℝ × ℝ) :
    (unitPairIndexFinset p).card =
      ∑ i : Fin n, (unitForwardNeighborFinset p i).card := by
  classical
  rw [unitPairIndexFinset_eq_sigma_forward]
  simp [Finset.card_sigma]

/--
Elimination-order reduction for unit distances.

If, in the chosen index order, every point has at most `k` unit-distance
neighbors later in the order, then the number of unordered unit-distance pairs
is at most `n * k`.
-/
theorem unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hforward : ∀ i, (unitForwardNeighborFinset p i).card ≤ k) :
    (unitPairIndexFinset p).card ≤ n * k := by
  classical
  rw [unitPairIndexFinset_card_eq_sum_forwardNeighbor_card]
  calc
    ∑ i : Fin n, (unitForwardNeighborFinset p i).card ≤ ∑ _i : Fin n, k := by
      exact sum_le_sum (fun i _hi => hforward i)
    _ = n * k := by
      simp

/-- Elimination-order certificate form of
`unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le`. -/
theorem UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_mul
    {n k : ℕ} {p : Fin n → ℝ × ℝ}
    (horder : UnitDistanceEliminationOrder p k) :
    (unitPairIndexFinset p).card ≤ n * k :=
  unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le p horder

/--
Directed handshaking reduction for unit distances.

If every point has at most `k` unit-distance neighbors, then the number of
directed unit-distance incidences is at most `n * k`.
-/
theorem unitDirectedPairFinset_card_le_mul_of_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hdeg : ∀ i, (unitNeighborFinset p i).card ≤ k) :
    (unitDirectedPairFinset p).card ≤ n * k := by
  classical
  simp [unitDirectedPairFinset, Finset.card_sigma]
  calc
    ∑ i : Fin n, (unitNeighborFinset p i).card ≤ ∑ _i : Fin n, k := by
      exact sum_le_sum (fun i _hi => hdeg i)
    _ = n * k := by
      simp

/--
Global linear-count reduction for unordered unit-distance pairs.

The unordered pair count is bounded by the directed incidence count, and the
directed incidence count is bounded by the uniform neighbor bound.
-/
theorem unitPairIndexFinset_card_le_mul_of_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hdeg : ∀ i, (unitNeighborFinset p i).card ≤ k) :
    (unitPairIndexFinset p).card ≤ n * k := by
  classical
  exact le_trans (card_filter_le _ _)
    (unitDirectedPairFinset_card_le_mul_of_neighbor_card_le p hdeg)

namespace SimpleConvexPolygon

/-- Unit-distance neighbors of an indexed polygon vertex. -/
noncomputable def unitNeighborFinset (P : SimpleConvexPolygon (ℝ × ℝ))
    (i : Fin P.vertices.length) : Finset (Fin P.vertices.length) :=
  _root_.unitNeighborFinset (fun j => P.vertices.get j) i

/-- Later unit-distance neighbors of an indexed polygon vertex. -/
noncomputable def unitForwardNeighborFinset (P : SimpleConvexPolygon (ℝ × ℝ))
    (i : Fin P.vertices.length) : Finset (Fin P.vertices.length) :=
  _root_.unitForwardNeighborFinset (fun j => P.vertices.get j) i

/-- Elimination-order certificate for the listed order of a concrete polygon. -/
def UnitDistanceEliminationOrder (P : SimpleConvexPolygon (ℝ × ℝ)) (k : ℕ) : Prop :=
  _root_.UnitDistanceEliminationOrder
    (fun j : Fin P.vertices.length => P.vertices.get j) k

/-- Unordered unit-distance index pairs among the listed polygon vertices. -/
noncomputable def unitPairIndexFinset (P : SimpleConvexPolygon (ℝ × ℝ)) :
    Finset (Σ _i : Fin P.vertices.length, Fin P.vertices.length) :=
  _root_.unitPairIndexFinset (fun j => P.vertices.get j)

/--
Polygon-facing elimination-order reduction.

If every listed vertex has at most `k` unit-distance neighbors later in the
chosen vertex order, then the total number of unordered unit-distance pairs is
at most `vertices.length * k`.
-/
theorem unitPairIndexFinset_card_le_length_mul_of_forward_neighbor_card_le
    (P : SimpleConvexPolygon (ℝ × ℝ)) {k : ℕ}
    (hforward : ∀ i, (P.unitForwardNeighborFinset i).card ≤ k) :
    P.unitPairIndexFinset.card ≤ P.vertices.length * k := by
  simpa [SimpleConvexPolygon.unitForwardNeighborFinset,
    SimpleConvexPolygon.unitPairIndexFinset] using
    unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
      (p := fun j : Fin P.vertices.length => P.vertices.get j) hforward

/-- Polygon-facing elimination-order certificate form of the linear count. -/
theorem UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_length_mul
    {P : SimpleConvexPolygon (ℝ × ℝ)} {k : ℕ}
    (horder : P.UnitDistanceEliminationOrder k) :
    P.unitPairIndexFinset.card ≤ P.vertices.length * k :=
  P.unitPairIndexFinset_card_le_length_mul_of_forward_neighbor_card_le horder

/--
Polygon-facing global linear-count reduction.

A uniform bound on unit-distance neighbors at each listed vertex gives a
linear bound for all unordered unit-distance pairs among the listed vertices.
-/
theorem unitPairIndexFinset_card_le_length_mul_of_neighbor_card_le
    (P : SimpleConvexPolygon (ℝ × ℝ)) {k : ℕ}
    (hdeg : ∀ i, (P.unitNeighborFinset i).card ≤ k) :
    P.unitPairIndexFinset.card ≤ P.vertices.length * k := by
  simpa [SimpleConvexPolygon.unitNeighborFinset,
    SimpleConvexPolygon.unitPairIndexFinset] using
    unitPairIndexFinset_card_le_mul_of_neighbor_card_le
      (p := fun j : Fin P.vertices.length => P.vertices.get j) hdeg

end SimpleConvexPolygon
