import ConvexSlicing.Solution

/-
Comparator axiom audit for the Convex slicing and its two consumers group. Prints the `#print axioms` closure
for every theorem this group's `config.json` lists in `theorem_names`. The
comparator itself enforces `permitted_axioms` during its run; this file lets a
reviewer or CI see the closure directly. Every report must be a subset of
{propext, Classical.choice, Quot.sound} -- no `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` (this group uses no `native_decide`, so it is absent here).

The theorems live in the shared `Headline` namespace in `Solution.lean`, so the
comparator finds them under the same qualified names listed in `config.json`.

Run: lake env lean comparator/ConvexSlicing/axiom-audit.lean
-/

#print axioms Headline.convex_line_intersection_isPreconnected
#print axioms Headline.strictlyConvex_boundary_no_three_collinear
#print axioms Headline.chord_in_frontier_of_collinear_boundary_triple
#print axioms Headline.convex_line_slice_ordConnected
#print axioms Headline.collinear_vertices_cyclicInterval
#print axioms Headline.iCount_le_of_convexIndep_circumscribed
