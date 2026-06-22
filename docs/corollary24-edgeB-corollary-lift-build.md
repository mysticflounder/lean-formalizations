# Corollary 24 / Theorem 2.3 — Edge-B corollary lift build record

Node: `edgeB-corollary-lift`. File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBCorollaryLift.lean`
(namespace `PachDeZeeuw.Algebraic`). Toolchain `leanprover/lean4:v4.30.0`, mathlib
`v4.30.0`.

This node assembles the landed unsheared Edge-B incidence bound
(`edgeB_crossingInput_unsheared`, `EdgeBShearApply.lean`) into the paper-faithful
`PachSharir.Theorem23Statement`, reducing it to **exactly two stated `sorry`
obligations** and proving everything else. Design: `docs/corollary24-hinj-discharge-analysis.md`
(the `deduped_pp` / R-2 residuals are the §5.2 obligations R-3 and R-2).

The route uses `edgeB_crossingInput_unsheared` directly (curve family
`Γ₀ : Finset PlanePoly` with the `hpp₀`/`hcc₀` clauses over `evalPlaneZeroSet`),
NOT `edgeB_crossingInput_2dof` — so `hinj`/`EdgeBCurve` packaging is avoided
entirely; the deduplicated factor family already has zero-set-distinct members.

## The two `sorry` obligations (verbatim signatures — the fill interface)

### Obligation R-3 — `deduped_pp` (point–point cover count)

```lean
theorem deduped_pp {F : Finset PlanePoly} {d M : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    (P' : Finset (ℝ × ℝ))
    (hpp_orig : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (F.filter (fun f => p ∈ evalPlaneZeroSet f ∧ q ∈ evalPlaneZeroSet f)).card ≤ M)
    {p q : ℝ × ℝ} (hp : p ∈ P') (hq : q ∈ P') (hpq : p ≠ q) :
    ((dedupFactors F).filter
        (fun h => p ∈ evalPlaneZeroSet h ∧ q ∈ evalPlaneZeroSet h)).card ≤ M * d
```

Intended proof (design §4.2 / FLAG `deduped-point-point-clause`): each deduped set
`evalPlaneZeroSet h` through both `p, q` comes from an irreducible factor of some
original `f ∈ F` whose locus contains `p, q`, which forces `p, q ∈ evalPlaneZeroSet f`
(factor locus ⊆ product locus). Bound by a **sum/biUnion over the `≤ M` original
curves through both points** (`hpp_orig`), each contributing `≤ d` factor zero sets
(`card_normalizedFactors_le_totalDegree ≤ totalDegree ≤ d`). MUST be phrased as a
cover (`Finset.card_le_card_of_subset` into a biUnion, `Finset.card_biUnion_le`), NOT
an injection into `F` — distinct original curves can share a deduped set.

### Obligation R-2 — `origIncidence_le_deduped` (finite-locus incidence translation)

```lean
theorem origIncidence_le_deduped {F : Finset PlanePoly} {d M : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    (P' : Finset (ℝ × ℝ))
    (hcc : ∀ f₁ ∈ F, ∀ f₂ ∈ F, evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ →
      (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard ≤ (M : ℕ∞)) :
    incidenceCount P' (F.image (fun f => evalPlaneZeroSet f))
      ≤ incidenceCount P' (zeroSets F)
        + finiteLocusConst d * (F.image (fun f => evalPlaneZeroSet f)).card
```

with `finiteLocusConst d := d * (d + 1) ^ 5` and
`zeroSets F := (allFactors F).image (fun h => evalPlaneZeroSet h)`.

**The `hcc` hypothesis (original-family curve–curve clause) is essential, not optional.**
The math-professor R-2 paper proof (`docs/corollary24-incidence-translation.md` §2, §8)
showed by a 145,703-world finite-model stress test that the inequality is FALSE without
it: two distinct original curves sharing an infinite-locus component would make one point
incident to all of them, so the original count is unbounded by the deduped count + a
degree-only term. The unique-ownership argument — an infinite deduped set lies in at most
one original curve, since two distinct originals sharing an infinite set would force
`(γ₁ ∩ γ₂).encard = ⊤ > M`, violating 2-DOF — is what makes the original→deduped incidence
injection injective. The original `Theorem23Statement` 2-DOF curve–curve clause supplies
`hcc` (transported through `chartEquiv` in `theorem23_of_crossingLemma`).

Intended proof (design §5.2 R-2 / FLAG `finite-locus incidence correction`,
`docs/corollary24-incidence-translation.md` §3–§7): an injection from original incidences
into (deduped incidences) ⊔ (finite-locus exceptions); infinite-branch injectivity from
`hcc` (unique ownership), finite branch bounded per-curve by the LANDED real-AG leaves
`finite_singularities_of_irreducible_bound` (`(SingularPointSet h).ncard ≤ (d+1)^5`),
`finite_zeroSet_subset_singularities`, `nonsingular_point_has_infinite_zeroSet`
(`Bezout.lean`), plus one new char-0 leaf `exists_pderiv_ne_zero_of_one_le_totalDegree`
(constructible; `docs/corollary24-incidence-translation.md` §6). NO real Nullstellensatz /
real radical / determinacy lemma is needed.

## What is PROVEN (sorry-free) in this file

All of the following are complete, `sorry`-free, and verified by `#print axioms` to
depend on exactly `[propext, Classical.choice, Quot.sound]` (the three core axioms —
no `sorryAx`, no custom axioms):

**Step 1 — representation (deduplicated factor family).**
- `allFactors`, `mem_allFactors`, `allFactors_irreducible`, `allFactors_degree_le`,
  `allFactors_one_le_degree` — the deduped irreducible normalized factors of `F`, each
  irreducible of total degree in `[1, d]`.
- `zeroSets`, `mem_zeroSets`; `pickFactor`, `pickFactor_mem`,
  `evalPlaneZeroSet_pickFactor` — the classical section of `evalPlaneZeroSet` over the
  factors (right inverse on `zeroSets F`).
- `dedupFactors`, `mem_dedupFactors`, `dedupFactors_subset_allFactors`,
  `image_evalPlaneZeroSet_dedupFactors` (`Γ₀.image evalPlaneZeroSet = zeroSets F`),
  `dedupFactors_zeroSet_injOn` (distinct members have distinct zero sets — by
  construction, no real-AG determinacy), `dedupFactors_irreducible`,
  `dedupFactors_degree_le`, `dedupFactors_one_le_degree`.
- `dedupFactors_card_le_allFactors`, `allFactors_card_le` (`≤ d·|F|` via
  `card_normalizedFactors_le_totalDegree` + `Finset.card_biUnion_le`),
  `dedupFactors_card_le` (`|Γ₀| ≤ d·|F|`).

**Step 2 — curve–curve clause.**
- `dedupFactors_inter_encard_le` — distinct deduped factors meet in `≤ (2d+1)^4` points
  (`encard`): distinct zero sets ⟹ `not_associated_of_ne_evalPlaneZeroSet` (Lemma A,
  landed) ⟹ `planeCurveZeroSet_inter_encard_le` (Bézout, landed), chart-transported
  through `chartEquiv` (`chartEquiv_image_planeCurveZeroSet`, `Set.image_inter`,
  `chartEquiv.injective.encard_image`).

**Constants + closing arithmetic.**
- `dedupMult d M := max ((2d+1)^4) (M*d)`, `dedupMult_pos`.
- `finiteLocusConst d := d*(d+1)^5`.
- `liftConst d M` (the real lift constant), `edgeBCrossingConst_pos`, `liftConst_pos`.
- `absorb_to_F` — the rpow/monotonicity absorption folding `|Γ₀| ≤ d·|F|` (as `d^{2/3}`)
  and the additive finite-locus term into `liftConst d M` times the `|F|`-shaped term.
- `term_le_boundTerm` — the `|F|`-shaped term is `≤ 3·incidenceBoundTerm` (given
  `|F| ≤ |Γ|`).

**Engine + top theorem (carry only the two stated sorries).**
- `edgeB_origFamily_bound` — the `ℝ × ℝ`-side engine: for a defining-poly family `F`,
  bounds `incidenceCount P' (F.image evalPlaneZeroSet)` by
  `liftConst d M · (|P'|^{2/3}·|F|^{2/3} + |P'| + |F|)`. Composes
  `edgeB_crossingInput_unsheared` on `dedupFactors F` (with the internally-proven
  `hcc₀` and the `deduped_pp`-sourced `hpp₀`), the R-2 translation, the cardinality
  bounds, and `absorb_to_F`. Axiom closure `[propext, sorryAx, Classical.choice,
  Quot.sound]` — `sorryAx` only via `deduped_pp`/`origIncidence_le_deduped`.
- `theorem23_of_crossingLemma (hCL : CrossingLemmaMultigraphStatement) :
  PachSharir.Theorem23Statement` — the top theorem. Chart-transports the Euclidean
  inputs to `ℝ × ℝ` (`P' := P.image chartEquiv`, defining-poly family `F` chosen
  injectively per original curve so `F.image PlaneCurveZeroSet = Γ` and
  `PlaneCurveZeroSet` is injective on `F`), transports the incidence count
  (`incidenceCount_equiv_eq`), supplies `hpp_orig` from the original
  `TwoDegreesOfFreedom` point–point clause (card-matched through the
  `PlaneCurveZeroSet` bijection `F ↔ Γ`), runs the engine, and closes with
  `term_le_boundTerm`. The constant is `C := 3 · liftConst d M`. Axiom closure
  `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` only via the two
  obligations.

The closing real-arithmetic (rpow exponent manipulation, absorbing the additive
finite-locus term and the `d·|F|` factor into one constant) is FULLY CLOSED
(`absorb_to_F` + `term_le_boundTerm` + the final `calc`); it is NOT a third `sorry`.

## Axiom closure (`#print axioms`)

Verified via a temporary `#print axioms` probe module (since removed; not in the build
graph):

- Every sorry-free declaration listed under "Step 1", "Step 2", "Constants + closing
  arithmetic" above: `[propext, Classical.choice, Quot.sound]`.
- `edgeB_origFamily_bound`, `theorem23_of_crossingLemma`:
  `[propext, sorryAx, Classical.choice, Quot.sound]` (`sorryAx` enters only through the
  two stated obligations `deduped_pp` and `origIncidence_le_deduped`).

## Build command and output

Built standalone (NOT wired into the public aggregator
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean`, which stays green):

```
$ ./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCorollaryLift
…
⚠ [8535/8535] Built LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCorollaryLift
warning: …/EdgeBCorollaryLift.lean:301:8: declaration uses `sorry`
warning: …/EdgeBCorollaryLift.lean:322:8: declaration uses `sorry`
Build completed successfully (8535 jobs).
```

Green except the two stated `sorry`s (lines 301 = `deduped_pp`, 322 =
`origIncidence_le_deduped`). No named `axiom`, no `native_decide`, no lint warnings
from the file. The two pre-`sorry` warnings are the only ones from this module.

## Dependencies reused (all landed)

- `edgeB_crossingInput_unsheared` (`EdgeBShearApply.lean`) — the unsheared Edge-B bound.
- `not_associated_of_ne_evalPlaneZeroSet` (Lemma A), `planeCurveZeroSet_inter_encard_le`
  (deduped_cc / Bézout) (`EdgeBDedup.lean`).
- `chartEquiv`, `chartEquiv_image_planeCurveZeroSet`,
  `chartEquiv_preimage_evalPlaneZeroSet`, `eval_eq_evalPlane_chart` (`ChartBridge.lean`).
- `incidenceCount_equiv_eq` (`EdgeBChartBridge.lean`).
- `card_normalizedFactors_le_totalDegree`, `normalized_factor_irreducible`,
  `normalized_factor_totalDegree_pos`, `normalized_factor_degree_le` (`AlgebraicPrelim.lean`).
- `edgeBCrossingConst`, `cConst_pos` (`EdgeBCrossingInput.lean`);
  `multigraphIncidenceConst` (`MultigraphIncidenceEndgame.lean`).

Conditional throughout on the parked `CrossingLemma.CrossingLemmaMultigraphStatement`
(kept as the hypothesis `hCL`, never discharged — Route-C).
