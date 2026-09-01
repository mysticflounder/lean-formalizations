import PlanarMaps.Solution

/-
Comparator axiom audit for the Combinatorial maps and the planar edge bound group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/PlanarMaps/axiom-audit.lean
-/

#print axioms Headline.eulerCharacteristic_le_two
#print axioms Headline.card_edge_le_three_card_vertex_sub_six
#print axioms Headline.dual_isPlanar_iff
#print axioms Headline.dual_connected_iff
#print axioms Headline.connected_dual_iff
#print axioms Headline.planar_multigraph_edge_bound
