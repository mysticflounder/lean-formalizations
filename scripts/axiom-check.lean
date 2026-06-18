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
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent_def
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent_inv
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent_mul
#print axioms Matrix.GeneralLinearGroup.GL2.upper_unipotent_mul_matrix
#print axioms Matrix.GeneralLinearGroup.GL2.swap_mul_matrix
#print axioms Matrix.GeneralLinearGroup.GL2.unipotent_det_eq_one
#print axioms Matrix.GeneralLinearGroup.GL2.swap_det_eq_neg_one

-- ───────────────────────────────────────────────────────────────────────────
-- Extended coverage: the remaining theorems the README's "Verified content ✅"
-- section names as axiom-clean (beyond the headline recipe above). These cover
-- standalone lemmas that no headline above transitively depends on.
-- ───────────────────────────────────────────────────────────────────────────

-- Energy → popular-difference-graph connector (BSGEnergyToGraph)
#print axioms Finset.energy_to_popular_graph

-- Elekes–Sharir generic lemmas: L4 rank–nullity collapse (OmegaRankCollapse)
#print axioms ElekesSharir.finrank_ker_functional_ge
#print axioms ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three
#print axioms ElekesSharir.pullback_nondegenerate
-- L5 conic normal form (ConicNormalForm)
#print axioms ElekesSharir.quadraticPart_eq
#print axioms ElekesSharir.dotProduct_mulVec_self_eq_zero_iff
#print axioms ElekesSharir.quadraticPart_vanishes_iff
-- L3 ruling skewness (RulingSkewness)
#print axioms ElekesSharir.intersect_or_parallel_of_dist2_eq
#print axioms ElekesSharir.intersect_or_parallel_of_isometryGraph
#print axioms ElekesSharir.atMostOneLine_of_skewRuling_isometryGraph
-- L1 two-pinned chord curve (ChordCurve)
#print axioms ElekesSharir.twoPinnedDet_affine
#print axioms ElekesSharir.twoPinnedDet_eq_const_add_linear

-- Real-algebraic-geometry core, additional headlines (AlgebraicPrelim)
#print axioms PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime
#print axioms PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound
#print axioms PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree
#print axioms PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree

-- Combinatorial-map duality + multiplicity edge bound (DualProperties / PlanarEdgeBound)
#print axioms CombinatorialMap.dual_connected_iff
#print axioms CombinatorialMap.connected_dual_iff
#print axioms planar_multigraph_edge_bound

-- Convex slicing, additional headlines (LineSlice / SimpleConvexPolygon)
#print axioms convex_line_slice_ordConnected
#print axioms chord_in_frontier_of_collinear_boundary_triple

-- Unit-distance elimination-order counting, polygon restatement (Counting)
#print axioms UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_mul

-- Tree-order prefix-connectedness + label transport (TreeOrder)
#print axioms SimpleGraph.connected_induce_take_of_leaf_insertion_parent
#print axioms SimpleGraph.Connected.apply_eq_of_forall_adj
