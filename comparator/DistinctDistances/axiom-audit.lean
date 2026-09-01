import DistinctDistances.Solution

/-
Comparator axiom audit for the Elekes-Sharir distinct-distances program group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/DistinctDistances/axiom-audit.lean
-/

#print axioms Headline.finrank_ker_functional_ge
#print axioms Headline.finrank_ker_ge_two_of_finrank_eq_three
#print axioms Headline.pullback_nondegenerate
#print axioms Headline.quadraticPart_eq
#print axioms Headline.dotProduct_mulVec_self_eq_zero_iff
#print axioms Headline.quadraticPart_vanishes_iff
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
