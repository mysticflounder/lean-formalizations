import TreeOrder.Solution

/-
Comparator axiom audit for the Tree order group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/TreeOrder/axiom-audit.lean
-/

#print axioms Headline.tree_exists_leaf_insertion_order
#print axioms Headline.connected_induce_take_of_leaf_insertion_parent
#print axioms Headline.connected_apply_eq_of_forall_adj
