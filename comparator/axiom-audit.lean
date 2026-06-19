import Solution

/-
Comparator axiom audit. Prints the `#print axioms` closure for every theorem in
`Solution.lean` that the comparator config lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer (or CI) see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} — no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (the project uses no `native_decide`).

Run: lake env lean comparator/axiom-audit.lean
-/

#print axioms Solution.bsg_asymmetric
#print axioms Solution.bsg_symmetric
#print axioms Solution.bsg_asymmetric_explicit
#print axioms Solution.energy_to_popular_graph
#print axioms Solution.twoPoint_isometry_ncard_le_two
#print axioms Solution.twoPoint_isometry_set_finite
#print axioms Solution.threeAPFree_of_forall_not_collinear
#print axioms Solution.convex_line_intersection_isPreconnected
#print axioms Solution.strictlyConvex_boundary_no_three_collinear
#print axioms Solution.chord_in_frontier_of_collinear_boundary_triple
#print axioms Solution.tree_exists_leaf_insertion_order
#print axioms Solution.connected_induce_take_of_leaf_insertion_parent
#print axioms Solution.connected_apply_eq_of_forall_adj
#print axioms Solution.finrank_ker_functional_ge
#print axioms Solution.finrank_ker_ge_two_of_finrank_eq_three
#print axioms Solution.pullback_nondegenerate
#print axioms Solution.quadraticPart_eq
#print axioms Solution.dotProduct_mulVec_self_eq_zero_iff
#print axioms Solution.quadraticPart_vanishes_iff
