# `uinf-containment` build record — the infinity-cut set `Inf_x(h)` and its containment in `{lc_y(h)=0}`

Author: Adam McKenna (adam-apple@flounder.net)
Date: 2026-06-20
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`
Worktree base: `bc3da64` (parent `main`).

**Status: CLOSED.** The `U_∞` term of Edge B's generic monotone graph decomposition
(`docs/corollary24-decomposition-spec.md`, §2.3, FLAG `uinf-containment`) is proven,
sorry-free and axiom-clean. It builds directly on the already-landed `lc-bound`
strip-compactness lemma (`StripCompact.lean`).

File: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/InfinityCut.lean`
Wired via: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean` (aggregator import,
next to `StripCompact`).

---

## 1. The `Inf_x` definition

```lean
namespace PachDeZeeuw.Algebraic

/-- `c ∈ InfX h` iff the curve `{evalPlane h = 0}` has a vertical asymptote at `x = c`:
for every closeness `δ > 0` and every height `M`, there is a curve point `(x, y)` with
`|x − c| < δ` and `|y| > M`. -/
def InfX (h : PlanePoly) : Set ℝ :=
  {c : ℝ | ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
      ∃ x y : ℝ, |x - c| < δ ∧ M < |y| ∧ evalPlane h (x, y) = 0}
```

**Justification it captures "vertical asymptote at `c`" (PROVEN faithful).** This is the
spec §2.3 topological definition verbatim — "for every `R > 0` and every `δ > 0` there is
`(x,y) ∈ γ` with `|x − c| < δ` and `|y| > R`", with `R = M`. It says: every neighborhood
`(c − δ, c + δ)` of `c` carries curve points of arbitrarily large `|y|`, i.e. the strip
over every neighborhood of `c` is unbounded in `y` — exactly a branch escaping to
`y = ±∞` as `x → c`. The faithfulness is witnessed concretely (see §4): for the hyperbola
`xy = 1` the asymptote value `0` is provably in `InfX`.

The chosen form uses an explicit existential over `(x, y)` rather than a filter/limit
statement: it is the lightest Lean encoding that (i) is the doc's definition unchanged and
(ii) plugs straight into the `exists_uniform_y_bound` contradiction (a single curve point
exceeding the uniform bound suffices).

## 2. The containment (`uinf-containment`, PROVEN)

```lean
/-- Every vertical-asymptote x-value of the curve is a root of `lc_y(h)`. -/
theorem InfX_subset_yLeadCoeff_zeroSet (h : PlanePoly) :
    InfX h ⊆ {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}
```

Proof by contrapositive on the foundational `StripCompact.lean` machinery, no extra
analytic content:

1. If `lc_y(h)(c) ≠ 0`, the continuous map `x ↦ lc_y(h)(x)` (`continuous_evalCoeff`) is
   nonzero on a whole **closed** interval `[c − ε, c + ε]`
   (`exists_closedInterval_yLeadCoeff_ne_zero`: nonvanishing locus is open via
   `isOpen_ne.preimage`, contains a metric ball `Metric.mem_nhds_iff`, halve the radius).
2. `exists_uniform_y_bound h (xP := c-ε) (xQ := c+ε)` then gives a single `B` with
   `|y| ≤ B` for every curve point over `[c − ε, c + ε]`.
3. Instantiate the asymptote condition at `δ = ε`, `M = B`: it yields a curve point with
   `|x − c| < ε` (hence `x ∈ [c − ε, c + ε]`) and `B < |y|`, contradicting `|y| ≤ B`.

Supporting lemma signature:

```lean
theorem exists_closedInterval_yLeadCoeff_ne_zero (h : PlanePoly) {c : ℝ}
    (hc : MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc (c - ε) (c + ε),
        MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0
```

## 3. Finiteness and the degree bounds (PROVEN, under `yLeadCoeff h ≠ 0`)

The bounding set is the real-root set of the univariate polynomial
`XCoeffEquiv (yLeadCoeff h) ∈ ℝ[X]` (the `AlgebraicPrelim.XCoeffEquiv` bridge
`MvPolynomial (Fin 1) ℝ ≃+* ℝ[X]`, already used in `StripCompact.lean`).

```lean
theorem yLeadCoeff_zeroSet_eq_isRoot (h : PlanePoly) :
    {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}
      = {c : ℝ | (XCoeffEquiv (yLeadCoeff h)).IsRoot c}          -- coeffEval_eq_eval_XCoeffEquiv

theorem finite_yLeadCoeff_zeroSet (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}.Finite
    -- Polynomial.finite_setOf_isRoot, nonzero via RingEquiv.map_eq_zero_iff

theorem ncard_yLeadCoeff_zeroSet_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    {c | … = 0}.ncard ≤ (XCoeffEquiv (yLeadCoeff h)).natDegree
    -- {c | IsRoot p c} = ↑p.roots.toFinset; Set.ncard_coe_finset, Multiset.toFinset_card_le, card_roots'

theorem finite_InfX (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) : (InfX h).Finite

theorem ncard_InfX_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfX h).ncard ≤ (XCoeffEquiv (yLeadCoeff h)).natDegree
```

**Coarse `≤ totalDegree h` bound (the spec's `U_∞(d) ≤ d`).** The polynomial's own degree
is further bounded by `totalDegree h`:

```lean
theorem totalDegree_yLeadCoeff_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (yLeadCoeff h).totalDegree ≤ h.totalDegree
    -- MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le on the y-leading coeff;
    -- totalDegree_rename_le both ways for the (involutive) swap2 = ![1,0]

theorem natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (XCoeffEquiv (yLeadCoeff h)).natDegree ≤ h.totalDegree
    -- (XCoeffEquiv r).natDegree = degreeOf 0 r ≤ totalDegree r (in-repo calc shape), then above

theorem ncard_InfX_le_totalDegree (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfX h).ncard ≤ h.totalDegree
```

So `U_∞(d) := (InfX h).ncard ≤ totalDegree h ≤ d` (PROVEN), matching spec §2.3 / §2 Final
count.

**The `yLeadCoeff h ≠ 0` hypothesis is kept honest.** If `h ∈ ℝ[x]` carries no `y` then
`lc_y(h) = 0`, the containment target is all of `ℝ`, and there is no degree bound. That
case is excluded upstream by the generic-rotation step (spec §1.4); the finiteness lemmas
correctly take `yLeadCoeff h ≠ 0` as an explicit hypothesis. The containment
`InfX_subset_yLeadCoeff_zeroSet` itself needs **no** hypothesis (it holds vacuously /
correctly when `lc_y = 0`, since then the target is all of ℝ).

## 4. Faithfulness witness (PROVEN, spec §2.2)

```lean
/-- For the hyperbola `xy = 1` (`h = X₀·X₁ − 1`), the asymptote x-value `0` lies in
`InfX h`: the branch `y = 1/x` over `x → 0⁺` escapes to `+∞`. -/
theorem mem_InfX_hyperbola : (0 : ℝ) ∈ InfX (MvPolynomial.X 0 * MvPolynomial.X 1 - 1)
```

For any `δ > 0` and `M`, the witness `x = min (δ/2) (1/(max M 0 + 1))`, `y = 1/x` satisfies
`|x| < δ`, `|y| > M`, and `x·(1/x) − 1 = 0`. Combined with `InfX_subset_yLeadCoeff_zeroSet`
and `lc_y(xy−1) = X` (whose only root is `0`), this pins `InfX (X₀·X₁ − 1) = {0}` exactly —
the corrected `Bad`-cut producing the two monotone branches `x < 0`, `x > 0` that the naive
`#crit + #sing + 1` count misses (spec §2.2).

## 5. Verification

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.InfinityCut` —
  green, 0 warnings from this file. Aggregator
  `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma` — green (8505 jobs).
- `#print axioms` for all 11 declarations (`InfX_subset_yLeadCoeff_zeroSet`, `finite_InfX`,
  `ncard_InfX_le`, `ncard_InfX_le_totalDegree`, `totalDegree_yLeadCoeff_le`,
  `natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree`, `finite_yLeadCoeff_zeroSet`,
  `ncard_yLeadCoeff_zeroSet_le`, `exists_closedInterval_yLeadCoeff_ne_zero`,
  `yLeadCoeff_zeroSet_eq_isRoot`, `mem_InfX_hyperbola`):
  **`[propext, Classical.choice, Quot.sound]`**. No `sorryAx`, no `native_decide`/
  `Lean.ofReduceBool`, no custom axioms.
- Job count: each isolated module build replays the 8480 dependency jobs and elaborates
  this one file (~4–5 s wall); aggregator build is 8505 jobs.

## 6. Status table

| Object | Status | Basis |
|---|---|---|
| `InfX` definition = spec §2.3 topological asymptote set | **definition** (faithful) | verbatim, `R = M`; witnessed by §4 |
| `InfX_subset_yLeadCoeff_zeroSet` (`uinf-containment`) | **PROVEN** | contrapositive on `exists_uniform_y_bound` (`StripCompact.lean`) |
| `finite_InfX`, `ncard_InfX_le` | **PROVEN** (needs `yLeadCoeff h ≠ 0`) | `Polynomial.finite_setOf_isRoot`, `card_roots'` via `XCoeffEquiv` |
| `ncard_InfX_le_totalDegree` (`U_∞(d) ≤ d`) | **PROVEN** (needs `yLeadCoeff h ≠ 0`) | `degreeOf_le_totalDegree` + `totalDegree_coeff_finSuccEquiv_add_le` |
| `mem_InfX_hyperbola` (`xy=1` witness) | **PROVEN** | explicit `(x, 1/x)` witness |

This discharges FLAG `uinf-containment` (spec §4). Note: prior to this build the spec
labeled the containment **CONJECTURED** (complete proof sketch) and the bounding-set
finiteness **PROVEN-trivial**; both are now PROVEN in Lean.
