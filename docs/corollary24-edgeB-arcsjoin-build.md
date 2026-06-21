# Edge-B `ArcsJoinEndpoints` build record (task #43, discharge v)

**File:** `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBArcsJoin.lean`
**Namespace:** `PachDeZeeuw.Algebraic` (`open CrossingLemma`)
**Status:** PROVEN, sorry-free, axiom-clean.
**Toolchain:** Lean 4 v4.30.0, mathlib v4.30.0.

Curve analogue of `stMultigraph_arcsJoinEndpoints`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:975`).

## Shipped signature

```lean
theorem edgeBMultigraph_arcsJoinEndpoints
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).ArcsJoinEndpoints
```

## Proof

```lean
intro i
exact EdgeBEdge.arc_endAnchor ((allCurveEdges d P Γ)[i])
```

`DrawnMultigraph.ArcsJoinEndpoints` unfolds to: for each `i : Fin G.numEdges`,
`endAnchor (G.arc i) false = (G.endpoints i).1 ∧ endAnchor (G.arc i) true = (G.endpoints i).2`.
By the `edgeBMultigraph` definition, `G.arc i = ((allCurveEdges d P Γ)[i]).arc` and
`G.endpoints i = ((allCurveEdges d P Γ)[i]).e` (definitionally). So the goal reduces
to `EdgeBEdge.arc_endAnchor ((allCurveEdges d P Γ)[i])`, which is already proven in
`EdgeBMultigraph.lean` (line 119).

## Gate results

- **Build:** `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBArcsJoin` →
  `Build completed successfully (8495 jobs)`, warning-free.
- **Axiom closure:** `#print axioms edgeBMultigraph_arcsJoinEndpoints` →
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom axioms.
- **Forbidden-token scan:** no `sorry`, `native_decide`, `unsafe`,
  `@[implemented_by]`, `@[extern]`, or `axiom` in the file.

## Landed leaf consumed

| Leaf | File | Role |
|---|---|---|
| `EdgeBEdge.arc_endAnchor` (line 119) | `EdgeBMultigraph.lean` | per-edge anchor fact lifted to the multigraph |
| `edgeBMultigraph`, `allCurveEdges` | `EdgeBMultigraph.lean` | definitions the index unfolds through |
