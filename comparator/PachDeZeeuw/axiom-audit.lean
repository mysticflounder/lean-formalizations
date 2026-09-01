import PachDeZeeuw.Solution

/-
Comparator axiom audit for the Pach-de Zeeuw / Bezout finite-intersection layer group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/PachDeZeeuw/axiom-audit.lean
-/

#print axioms Headline.ncard_coeff_roots_le_totalDegree
#print axioms Headline.resultant_ne_zero_of_isRelPrime_primitive_curry
#print axioms Headline.resultant_ne_zero_of_fraction_coprime
#print axioms Headline.fiber_ncard_le_max_totalDegree
#print axioms Headline.zeroCurry_nonvertical_pair_intersection_bound
#print axioms Headline.coeffline_nonvertical_pair_intersection_bound
#print axioms Headline.bezout
