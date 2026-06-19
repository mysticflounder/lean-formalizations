/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Challenge
import Solution

/-!
# Conformance.lean — local statement-identity check

This file is the project's own offline mirror of what the comparator verifies:
that for every headline theorem, the `Challenge` (mathlib-only `sorry` stub) and
the `Solution` (real project proof) state the **identical** proposition.

For each name `X`, the check is

```
example : @Challenge.X = @Solution.X := rfl
```

`@Challenge.X` has type `T₁` and `@Solution.X` has type `T₂`. For the equality
`@Challenge.X = @Solution.X` to be even well-typed, `T₁` and `T₂` must unify — so
if the two signatures differed, this file would fail to elaborate. When they
agree, both sides are proofs of the same `Prop`, and Lean's definitional proof
irrelevance closes the goal by `rfl`. Hence: **this file compiles iff all 19
challenge/solution statements match exactly.** Any future drift breaks the build.

(Run together with `scripts/check-axioms.sh`, which audits the `#print axioms`
closure of the underlying project theorems.)
-/

example : @Challenge.bsg_asymmetric = @Solution.bsg_asymmetric := rfl
example : @Challenge.bsg_symmetric = @Solution.bsg_symmetric := rfl
example : @Challenge.bsg_asymmetric_explicit = @Solution.bsg_asymmetric_explicit := rfl
example : @Challenge.energy_to_popular_graph = @Solution.energy_to_popular_graph := rfl
example : @Challenge.twoPoint_isometry_ncard_le_two = @Solution.twoPoint_isometry_ncard_le_two := rfl
example : @Challenge.twoPoint_isometry_set_finite = @Solution.twoPoint_isometry_set_finite := rfl
example : @Challenge.threeAPFree_of_forall_not_collinear = @Solution.threeAPFree_of_forall_not_collinear := rfl
example : @Challenge.convex_line_intersection_isPreconnected = @Solution.convex_line_intersection_isPreconnected := rfl
example : @Challenge.strictlyConvex_boundary_no_three_collinear = @Solution.strictlyConvex_boundary_no_three_collinear := rfl
example : @Challenge.chord_in_frontier_of_collinear_boundary_triple = @Solution.chord_in_frontier_of_collinear_boundary_triple := rfl
example : @Challenge.tree_exists_leaf_insertion_order = @Solution.tree_exists_leaf_insertion_order := rfl
example : @Challenge.connected_induce_take_of_leaf_insertion_parent = @Solution.connected_induce_take_of_leaf_insertion_parent := rfl
example : @Challenge.connected_apply_eq_of_forall_adj = @Solution.connected_apply_eq_of_forall_adj := rfl
example : @Challenge.finrank_ker_functional_ge = @Solution.finrank_ker_functional_ge := rfl
example : @Challenge.finrank_ker_ge_two_of_finrank_eq_three = @Solution.finrank_ker_ge_two_of_finrank_eq_three := rfl
example : @Challenge.pullback_nondegenerate = @Solution.pullback_nondegenerate := rfl
example : @Challenge.quadraticPart_eq = @Solution.quadraticPart_eq := rfl
example : @Challenge.dotProduct_mulVec_self_eq_zero_iff = @Solution.dotProduct_mulVec_self_eq_zero_iff := rfl
example : @Challenge.quadraticPart_vanishes_iff = @Solution.quadraticPart_vanishes_iff := rfl
