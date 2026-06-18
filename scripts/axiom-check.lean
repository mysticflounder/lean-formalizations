import LeanFormalizations

/-
Release gate: every theorem the README advertises as axiom-clean must depend on
ONLY Lean/mathlib core axioms (`propext`, `Classical.choice`, `Quot.sound`;
`Lean.ofReduceBool`/`Lean.ofReduceNat` are tolerated under the project's
`native_decide` policy). No `sorryAx`, no custom axioms.

This file is the canonical published list from README.md "Reproduce the
verification". `scripts/check-axioms.sh` runs it and asserts the output is clean.
Keep this list in sync with the README's ✅ VERIFIED claims.
-/

-- Balog–Szemerédi–Gowers
#print axioms Finset.balog_szemeredi_gowers_asymmetric
#print axioms Finset.balog_szemeredi_gowers_symmetric
#print axioms Finset.balog_szemeredi_gowers_asymmetric_explicit

-- 2D two-point isometry classification
#print axioms EuclideanGeometry.twoPoint_isometry_ncard_le_two
#print axioms EuclideanGeometry.twoPoint_isometry_set_finite

-- Near Enemy Theorem
#print axioms NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
#print axioms NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport

-- no-3-collinear ⟹ 3-AP-free
#print axioms threeAPFree_of_forall_not_collinear

-- Real-algebraic-geometry core + Bézout
#print axioms PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound
#print axioms PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry
#print axioms PachDeZeeuw.Algebraic.bezout

-- Combinatorial maps + planar edge bound
#print axioms CombinatorialMap.card_edge_le_three_card_vertex_sub_six
#print axioms CombinatorialMap.eulerCharacteristic_le_two
#print axioms CombinatorialMap.dual_isPlanar_iff

-- Convex slicing + simple convex polygon
#print axioms convex_line_intersection_isPreconnected
#print axioms strictlyConvex_boundary_no_three_collinear
#print axioms SimpleConvexPolygon.collinear_vertices_cyclicInterval

-- Tree-order helpers
#print axioms SimpleGraph.IsTree.exists_leaf_insertion_order
#print axioms SimpleGraph.IsTree.parentEdgeEquiv

-- Unit-distance elimination-order counting
#print axioms unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le

-- GL matrix identities
#print axioms Matrix.GeneralLinearGroup.diagonal
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent
#print axioms Matrix.GeneralLinearGroup.GL2.upper_unipotent_mul_matrix
#print axioms Matrix.GeneralLinearGroup.GL2.swap_mul_matrix
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent_det_eq_one
#print axioms Matrix.GeneralLinearGroup.GL2.swap_det_eq_neg_one
