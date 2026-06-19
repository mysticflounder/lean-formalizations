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
#print axioms Headline.tree_exists_leaf_insertion_order
#print axioms Headline.connected_induce_take_of_leaf_insertion_parent
#print axioms Headline.connected_apply_eq_of_forall_adj
#print axioms Headline.finrank_ker_functional_ge
#print axioms Headline.finrank_ker_ge_two_of_finrank_eq_three
#print axioms Headline.pullback_nondegenerate
#print axioms Headline.quadraticPart_eq
#print axioms Headline.dotProduct_mulVec_self_eq_zero_iff
#print axioms Headline.quadraticPart_vanishes_iff
