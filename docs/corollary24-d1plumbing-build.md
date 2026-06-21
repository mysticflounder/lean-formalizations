# Corollary 24 — Edge B, D1 finiteness plumbing (`Bad h` finite)

Build record for `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/DecompositionD1.lean`
(namespace `PachDeZeeuw.Algebraic`). Discharges the `D1-finiteness` obligation of Edge B's
generic monotone graph decomposition: the cut set `Bad h = Crit_x h ∪ InfRoot_x h` of a
plane curve is finite.

Status: **all three target lemmas PROVEN, sorry-free.** Module builds green with
`./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD1`. No
`sorry`/`admit`/`native_decide`/custom axioms. Every delivered declaration's kernel axiom
closure is exactly `[propext, Classical.choice, Quot.sound]`.

## Worktree provenance note

The orchestrator created this worktree from `bc3da64` (StripCompact tip). The four stated
dependencies (`DecompositionDefs`, `InfinityCut`, `CriticalPointBound`, `ChartBridge`) were
committed to `main` afterward in `34b13ec..4136f74`, so they were absent from the worktree
base. Since the worktree branch was a strict ancestor of `main` (merge-base == HEAD, no
local divergence), it was fast-forwarded to `main` (`4136f74`) to bring those dependencies
in — a zero-conflict fast-forward, no parent-project files touched. Only
`lean/.../DecompositionD1.lean` and this doc are new.

## Targets — verbatim final signatures

### (1) `decomp_D1_infroot_finite` — PROVEN

```lean
theorem decomp_D1_infroot_finite (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfRoot_x h).Finite
```

`InfRoot_x h = {x | MvPolynomial.eval (·↦x) (yLeadCoeff h) = 0}` is, by definition, the set
`InfinityCut.lean`'s `finite_yLeadCoeff_zeroSet h hlc` proves finite. The proof is that term
directly (the two sets are definitionally identical), so this is a one-liner. Hypotheses:
`yLeadCoeff h ≠ 0` (as in B-`U_∞`).

### (2) `decomp_D1_crit_finite` — PROVEN

```lean
theorem decomp_D1_crit_finite
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Crit_x h).Finite
```

Hypotheses match `finite_critX_of_irreducible_bound` (B-crit) exactly: `Irreducible h`,
`h.totalDegree ≤ d` (`d` autobound), `pderiv 1 h ≠ 0`.

Load-bearing content is the set equality, proven as a standalone lemma:

```lean
theorem critX_eq_image_critPointSet (h : PlanePoly) :
    Crit_x h = (fun p : Point2 => p 0) '' CritPointSet h
```

- `Crit_x h = {x | ∃ y, evalPlane h (x,y) = 0 ∧ partialY h (x,y) = 0}` (`ℝ×ℝ` chart).
- `CritPointSet h = PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h)` (`Point2` chart).
- Bridge facts used (`ChartBridge.lean`): `eval_eq_evalPlane_chart p x : eval (·↦x i) p =
  evalPlane p (chartEquiv x)`; `chartEquiv_apply x : chartEquiv x = (x 0, x 1)`;
  `chartEquiv_symm_apply_zero z : (chartEquiv.symm z) 0 = z.1`;
  `Homeomorph.apply_symm_apply`.
- Pivot identity proven here: `partialY_eq_evalPlane_pderiv h z : partialY h z =
  evalPlane (pderiv 1 h) z` — `rfl` (both unfold to
  `eval (fun i => if i = 0 then z.1 else z.2) (pderiv 1 h)`). This is what lets the chart
  intertwining (stated for `evalPlane`) reach the `partialY` half of `Crit_x`.
- `⊇`: from `p ∈ CritPointSet h` build `y := p 1`; `chartEquiv p = (p 0, p 1)` carries the
  two `Point2`-side `eval = 0` facts to `evalPlane h (p 0, p 1) = 0` and
  `partialY h (p 0, p 1) = 0`.
- `⊆`: from `(x,y)` with the curve + tangent conditions build `p := chartEquiv.symm (x,y)`;
  `chartEquiv p = (x,y)` and `p 0 = x`, so `p ∈ CritPointSet h` and `x = p 0`.

`.Finite` then follows from `(finite_critX_of_irreducible_bound h hh hdeg hpi).1`.

### (3) `decomp_D1_bad_finite` — PROVEN (only B-crit hypotheses; `yLeadCoeff ≠ 0` derived)

```lean
theorem decomp_D1_bad_finite
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).Finite
```

`Bad h = Crit_x h ∪ InfRoot_x h`, so this is `Set.Finite.union` of (2) and (1). The
`yLeadCoeff h ≠ 0` input to (1) is **not** a separate hypothesis — it is discharged from
B-crit's `pderiv 1 h ≠ 0` via the helper:

```lean
theorem yLeadCoeff_ne_zero_of_partialY_ne_zero (h : PlanePoly)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    yLeadCoeff h ≠ 0
```

Chain: `pderiv 1 h ≠ 0 ⟹ h ≠ 0` (`pderiv 1 0 = 0`) `⟹ rename swap2 h ≠ 0`
(`MvPolynomial.rename_injective` with `swap2 = ![1,0]` injective)
`⟹ Curry1 h = finSuccEquiv ℝ 1 (rename swap2 h) ≠ 0` (`finSuccEquiv` injective)
`⟹ yLeadCoeff h = (Curry1 h).leadingCoeff ≠ 0` (`Polynomial.leadingCoeff_ne_zero`).

So `decomp_D1_bad_finite` ends up taking **exactly B-crit's hypotheses** — the preferred
outcome in the task. No residual `yLeadCoeff h ≠ 0` obligation is left on the headline lemma.

## `#print axioms` (verbatim build output)

```
'PachDeZeeuw.Algebraic.decomp_D1_infroot_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.critX_eq_image_critPointSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.decomp_D1_crit_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.yLeadCoeff_ne_zero_of_partialY_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.decomp_D1_bad_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.partialY_eq_evalPlane_pderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(The `yLeadCoeff_ne_zero_of_partialY_ne_zero` line wraps across terminal lines in raw `lake`
output; its axiom multiset is the same `[propext, Classical.choice, Quot.sound]`.) The
`#print axioms` commands were run by transiently appending them to the module, capturing
output, then removed; the shipped file contains only the six declarations.

## Auxiliary declarations in the module (also PROVEN, same axiom closure)

- `partialY_eq_evalPlane_pderiv` — `partialY h z = evalPlane (pderiv 1 h) z` (`rfl`).
- `critX_eq_image_critPointSet` — the chart set equality (content of (2)).
- `yLeadCoeff_ne_zero_of_partialY_ne_zero` — the helper for (3).

## Build command

```
./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD1
# → Build completed successfully (8485 jobs).
```

(Worktree had an empty mathlib cache; `lake exe cache get` was run once to populate the
~8283 precompiled oleans before the first build.)

## Scope

Only `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/DecompositionD1.lean` (new) and this
doc were written. No aggregator/import wiring was edited (the orchestrator wires imports). No
commit, no push.
