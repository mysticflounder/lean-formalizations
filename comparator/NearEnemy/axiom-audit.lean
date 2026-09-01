import NearEnemy.Solution

/-
Comparator axiom audit for the Near Enemy bisector energy group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/NearEnemy/axiom-audit.lean
-/

#print axioms Headline.two_mul_pairCount_le_bisectorEnergy
#print axioms Headline.bisectorEnergy_eq_of_bisectorInjective
#print axioms Headline.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
#print axioms Headline.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
