import Isometry2D.Solution

/-
Comparator axiom audit for the 2D two-point isometry classification group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/Isometry2D/axiom-audit.lean
-/

#print axioms Headline.twoPoint_isometry_ncard_le_two
#print axioms Headline.twoPoint_isometry_set_finite
