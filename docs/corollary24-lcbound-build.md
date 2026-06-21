# `lc-bound` build record — vertical-strip compactness over a leading-coefficient-nonzero interval

Author: Adam McKenna (adam-apple@flounder.net)
Date: 2026-06-20
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`

**Status: CLOSED.** The single hardest sub-obligation of Edge B's generic monotone
graph decomposition (`docs/corollary24-decomposition-spec.md`, FLAG `lc-bound`,
§2.3, §3.3) is proven, sorry-free and axiom-clean.

File: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/StripCompact.lean`
Wired via: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean` (aggregator import).

---

## 1. The final statement

```lean
namespace PachDeZeeuw.Algebraic

/-- The vertical strip of the curve over `[xP, xQ]`. -/
def strip (h : PlanePoly) (xP xQ : ℝ) : Set (ℝ × ℝ) :=
  {xy : ℝ × ℝ | xy.1 ∈ Set.Icc xP xQ ∧ evalPlane h xy = 0}

/-- **`lc-bound` (main).** On the compact interval `[xP, xQ]` where the leading
coefficient in `y`, `a_D(x) = lc_y(h)(x)`, is nonzero throughout, the vertical strip
is bounded, hence (being closed) compact. -/
theorem isCompact_strip (h : PlanePoly) {xP xQ : ℝ}
    (hlc : ∀ x ∈ Set.Icc xP xQ, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    IsCompact (strip h xP xQ)
```

### Representation of "view `h` as a polynomial in `y` / `a_D ≠ 0`"

`evalPlane` uses index `0` for `x`, index `1` for `y`. `MvPolynomial.finSuccEquiv ℝ 1`
extracts variable `0`, so `h` is first renamed along `swap2 = ![1, 0]` to put `y`
(variable `1`) outermost:

```lean
def swap2 : Fin 2 → Fin 2 := ![1, 0]
noncomputable def Curry1 (h : PlanePoly) : Polynomial (MvPolynomial (Fin 1) ℝ) :=
  MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.rename swap2 h)          -- h as ℝ[x][Y]
noncomputable def yLeadCoeff (h : PlanePoly) : MvPolynomial (Fin 1) ℝ :=
  (Curry1 h).leadingCoeff                                              -- a_D = lc_y(h)
noncomputable def Specialized1 (x : ℝ) (h : PlanePoly) : Polynomial ℝ :=
  (Curry1 h).map (MvPolynomial.eval (fun _ : Fin 1 => x))             -- slice q_x ∈ ℝ[Y]
```

The hypothesis `hlc` is the **genuine** leading-coefficient condition: `a_D(x) ≠ 0`
for all `x ∈ [xP, xQ]`, with `a_D = (Curry1 h).leadingCoeff` the leading coefficient
of `h` in `y`. It is not weakened to "the slice is nonzero" (which would be strictly
weaker: a lower coefficient could survive while `a_D` vanishes). When `a_D ≡ 0` on the
interval (e.g. `h = 0`, or `h ∈ ℝ[x]` with no `y`, or at a vertical asymptote) the
hypothesis correctly fails, so the lemma is silent there — exactly the asymptote
case the `U_∞` term handles.

The faithfulness of the representation is confirmed semantically (EMPIRICALLY VERIFIED,
single concrete instance, kernel-checked): for `h = x·y − 1` (the `xy = 1` hyperbola,
spec §2.2), `Specialized1 x h` evaluates to `x·Y − 1`, the right univariate-in-`y`
polynomial; its `y`-leading coefficient is `x = lc_y(xy−1)`.

---

## 2. Axiom report

`#print axioms` against the built olean (full project build, 8504 jobs):

```
'PachDeZeeuw.Algebraic.isCompact_strip'             depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.isClosed_strip'              depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.exists_uniform_y_bound'      depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.cauchyBound_le_cauchyDom'    depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.continuousOn_cauchyDom'      depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.eval_specialized1'           depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.leadingCoeff_specialized1'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three Lean core axioms. No `sorryAx`, no custom axioms, no
`Lean.ofReduceBool` / `native_decide`. The file is lint-clean (zero warnings under a
standalone `lean` elaboration).

---

## 3. Proof structure

On `[xP, xQ]` the slice `q_x(Y) := Specialized1 x h` is a real univariate polynomial
with `Polynomial.eval y q_x = evalPlane h (x, y)` (`eval_specialized1`), so curve
points over `x` are exactly the real roots of `q_x`. Where `a_D(x) ≠ 0`, `q_x` has
`natDegree = (Curry1 h).natDegree =: D` and is nonzero
(`specialized1_natDegree_and_ne_zero`), with leadingCoeff `= a_D(x)`
(`leadingCoeff_specialized1`).

1. **Per-slice Cauchy bound.** Each real root `y` of `q_x` satisfies
   `‖y‖ < cauchyBound q_x` (`Polynomial.IsRoot.norm_lt_cauchyBound`).

2. **Continuous uniform domination.** Define
   `cauchyDom h x := (∑_{i<D} ‖a_i(x)‖) / ‖a_D(x)‖ + 1`. Since `sup ≤ sum` for the
   coefficient norms, `(cauchyBound q_x : ℝ) ≤ cauchyDom h x`
   (`cauchyBound_le_cauchyDom`). Each `x ↦ a_i(x)` is continuous (a real univariate
   polynomial read through the in-repo `XCoeffEquiv`), so `cauchyDom h` is continuous
   on the interval where `a_D ≠ 0` (`continuousOn_cauchyDom`).

3. **Uniform `y`-bound.** `cauchyDom h` is continuous on the compact `[xP, xQ]`, hence
   bounded above by some `B` (`IsCompact.bddAbove_image`). Every curve point `(x, y)`
   over `[xP, xQ]` then has `|y| < cauchyBound q_x ≤ cauchyDom h x ≤ B`
   (`exists_uniform_y_bound`).

4. **Bounded + closed ⟹ compact.** The strip sits inside the box
   `[xP, xQ] ×ˢ [−B, B]`, so it is bounded; it is closed as `γ` intersected with the
   closed slab `{p.1 ∈ [xP, xQ]}` (`isClosed_strip`, using the in-repo
   `isClosed_evalPlaneZeroSet`). Heine–Borel in finite dimension
   (`Metric.isCompact_of_isClosed_isBounded`) gives compactness.

This single lemma discharges both `D2b` (the per-arc lemma's compact-strip input `hK`)
and the `uinf-containment` bound, as the spec anticipated (§3.3).

---

## 4. Mathlib bricks used vs assembled

### Used directly from mathlib v4.30 (no assembly)

| Brick | Handle |
|---|---|
| Cauchy root bound (monic / general) | `Polynomial.cauchyBound`, `Polynomial.IsRoot.norm_lt_cauchyBound` (`Mathlib/Analysis/Polynomial/CauchyBound.lean`) |
| degree / leadingCoeff preserved under `map` when leadingCoeff survives | `Polynomial.natDegree_map_of_leadingCoeff_ne_zero`, `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero` |
| `MvPolynomial` → univariate bridge | `MvPolynomial.eval_eq_eval_mv_eval'`, `MvPolynomial.eval_rename`, `MvPolynomial.finSuccEquiv` |
| `coeff` under `map` | `Polynomial.coeff_map` |
| continuity of univariate polynomial eval | `Polynomial.continuous` |
| finite-set continuity / sup | `continuousOn_finsetSum`, `Finset.sup_le`, `Finset.single_le_sum` |
| compact ⟹ bounded image | `IsCompact.bddAbove_image`, `isCompact_Icc` |
| Heine–Borel (finite dim) | `Metric.isCompact_of_isClosed_isBounded` |
| bounded box | `Bornology.IsBounded.prod`, `Metric.isBounded_Icc`, `IsBounded.subset` |
| NNReal ↔ ℝ coercion | `NNReal.coe_sum`, `coe_nnnorm`, `zero_le'` |

The spec flagged the "monic polynomial ⟹ all roots in the ball of radius
`1 + max|coeff|`" lemma as *partial — assemblable from `Polynomial.Monic` + a
coefficient-norm estimate*. **It exists verbatim in v4.30**:
`Polynomial.IsRoot.norm_lt_cauchyBound` (Daniel Weber, 2024), valid over any
`NormedDivisionRing` (so directly over `ℝ`; the complex version was not needed). No
hand-assembly of the root bound was required.

### In-repo bricks reused (not reinvented)

| Brick | Location |
|---|---|
| `evalPlane`, `PlanePoly` | `Bezout.lean`, `AlgebraicPrelim.lean` |
| `evalPlaneZeroSet`, `isClosed_evalPlaneZeroSet` | `MonotoneArc.lean` (curve closedness) |
| `XCoeffEquiv`, `coeffEval`, `coeffEval_eq_eval_XCoeffEquiv` | `AlgebraicPrelim.lean` (coeff-ring ↔ ℝ[x] identification, used for coefficient continuity) |

### Assembled (small standalone lemmas in this file)

The `Curry1` / `Specialized1` presentation and the four algebraic bridges
(`eval_specialized1`, `coeff_specialized1`, `specialized1_natDegree_and_ne_zero`,
`leadingCoeff_specialized1`), `cauchyDom` and its continuity/domination, and the
`exists_uniform_y_bound` → `isCompact_strip` assembly. No single mathlib lemma
packages the strip-compactness statement; this file is that packaging.

---

## 5. Build / verification notes

- Verified by a full `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma`
  (post-merge file set: parent's `MonotoneArc`/`LocalArc` sources + this file):
  `Build completed successfully (8504 jobs)`. The only warnings are pre-existing
  lint warnings in `PLCollarSeparation.lean`, unrelated to this file.
- Worktree note: the worktree was branched from a commit predating
  `MonotoneArc.lean` / `LocalArc.lean`; those sources live in the merge target
  (parent), which is strictly ahead. The aggregator edit reproduces the parent's
  import block plus a single `StripCompact` line, so the merge is a clean superset.
  All standalone elaboration of this file used the parent's built oleans (the exact
  merge-target dependency set).

---

## 6. Classification

| Claim | Status |
|---|---|
| `isCompact_strip` (and all helper lemmas) | **PROVEN** (Lean, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`) |
| `Specialized1` / `yLeadCoeff` faithfully represent the `y`-slice and `lc_y(h)` | **PROVEN** (`eval_specialized1`); leading-coeff identity for `h = xy−1` **EMPIRICALLY VERIFIED** (one kernel-checked instance) |
| Cauchy root bound available in mathlib v4.30 as a packaged statement | **PROVEN-present** (`Polynomial.IsRoot.norm_lt_cauchyBound`, used directly) |
