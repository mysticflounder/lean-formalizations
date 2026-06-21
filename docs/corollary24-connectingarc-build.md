# ConnectingArc build record

**File:** `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/ConnectingArc.lean`
**Build command:** `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.ConnectingArc`
**Build result:** green (8484 jobs, 3.7 s for the new module)
**Date:** 2026-06-21

## Theorems

### `reach_of_some_continuation`

Role: given a connecting arc χ from (xP,yP) to (xQ,yQ), every continuous
on-curve graph ψ starting at (xP,yP) must reach yQ at xQ.  This is
`endpoint_pin_of_connectingGraph` with the existential witness destructured —
no new content.

### `export_3_connecting_arc`

Role: given the reach predicate `hreach` (discharged downstream by sheet-rank),
`decomp_arc_on_good`'s arc is pinned at both ends, producing the full
connecting-arc existential consumed by the E1 assembly.  No new content.

## Axiom closures

```
'PachDeZeeuw.Algebraic.reach_of_some_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.export_3_connecting_arc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both theorems are PROVEN over the two landed leaves (`endpoint_pin_of_connectingGraph`
from `SheetCount.lean` and `decomp_arc_on_good` from `DecompositionD2.lean`) with no new
mathematical content and no `sorry`, `native_decide`, `unsafe`, or custom axioms.
