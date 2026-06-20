import Solution

/-
Comparator axiom audit. Prints the `#print axioms` closure for every theorem in
`Solution.lean` that the comparator config lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer (or CI) see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} — no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (the project uses no `native_decide`).

The 19 theorems live in the shared `Headline` namespace in `Solution.lean`, so
the comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/axiom-audit.lean
-/

#print axioms Headline.bsg_asymmetric
#print axioms Headline.bsg_symmetric
#print axioms Headline.bsg_asymmetric_explicit
#print axioms Headline.energy_to_popular_graph
#print axioms Headline.twoPoint_isometry_ncard_le_two
#print axioms Headline.twoPoint_isometry_set_finite
#print axioms Headline.threeAPFree_of_forall_not_collinear
#print axioms Headline.convex_line_intersection_isPreconnected
#print axioms Headline.strictlyConvex_boundary_no_three_collinear
#print axioms Headline.chord_in_frontier_of_collinear_boundary_triple
#print axioms Headline.collinear_vertices_cyclicInterval
#print axioms Headline.tree_exists_leaf_insertion_order
#print axioms Headline.connected_induce_take_of_leaf_insertion_parent
#print axioms Headline.connected_apply_eq_of_forall_adj
#print axioms Headline.finrank_ker_functional_ge
#print axioms Headline.finrank_ker_ge_two_of_finrank_eq_three
#print axioms Headline.pullback_nondegenerate
#print axioms Headline.quadraticPart_eq
#print axioms Headline.dotProduct_mulVec_self_eq_zero_iff
#print axioms Headline.quadraticPart_vanishes_iff
#print axioms Headline.two_mul_pairCount_le_bisectorEnergy
#print axioms Headline.bisectorEnergy_eq_of_bisectorInjective
#print axioms Headline.unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
#print axioms Headline.ncard_coeff_roots_le_totalDegree
#print axioms Headline.resultant_ne_zero_of_isRelPrime_primitive_curry
#print axioms Headline.resultant_ne_zero_of_fraction_coprime
#print axioms Headline.fiber_ncard_le_max_totalDegree
#print axioms Headline.zeroCurry_nonvertical_pair_intersection_bound
#print axioms Headline.coeffline_nonvertical_pair_intersection_bound
#print axioms Headline.bezout
#print axioms Headline.twoPinnedDet_affine
#print axioms Headline.twoPinnedDet_eq_const_add_linear
#print axioms Headline.intersect_or_parallel_of_dist2_eq
#print axioms Headline.intersect_or_parallel_of_isometryGraph
#print axioms Headline.atMostOneLine_of_skewRuling_isometryGraph
#print axioms Headline.energy_lower_bound_of_few_distances
#print axioms Headline.gp_config_nonempty
#print axioms Headline.orderedMultiplicity_le_three_mul
#print axioms Headline.distanceEnergy_le_three_mul_cube
#print axioms Headline.numDistances_ge_of_ceiling
#print axioms Headline.all_configs_lower_bound_to_hIndexed_lower_bound
#print axioms Headline.distanceEnergy_eq_sum_energyAtLevel
#print axioms Headline.elekes_sharir_guth_katz_decomposition
