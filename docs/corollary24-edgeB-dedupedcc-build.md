# Build record: `deduped_cc` (planeCurveZeroSet_inter_encard_le)

**File:** `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBDedup.lean`
**Namespace:** `PachDeZeeuw.Algebraic`
**Status:** PROVEN (axiom-clean build passed)

## Lemma statement

```lean
lemma planeCurveZeroSet_inter_encard_le {d : ℕ} (K₁ K₂ : PlanePoly)
    (hirr₁ : Irreducible K₁) (hirr₂ : Irreducible K₂)
    (hd₁ : K₁.totalDegree ≤ d) (hd₂ : K₂.totalDegree ≤ d)
    (hne : PlaneCurveZeroSet K₁ ≠ PlaneCurveZeroSet K₂) :
    (PlaneCurveZeroSet K₁ ∩ PlaneCurveZeroSet K₂).encard ≤ ((2 * d + 1) ^ 4 : ℕ∞)
```

## Mathlib and landed lemmas used

| Name | Source | Role |
|------|--------|------|
| `PachDeZeeuw.Algebraic.irreducible_pair_intersection_bound` | `lean/LeanFormalizations/PachDeZeeuw/Bezout.lean:371` | Bézout bound: `Finite ∧ ncard ≤ (d₁+d₂+1)^4` |
| `PachDeZeeuw.Algebraic.not_associated_of_ne_evalPlaneZeroSet` | `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBDedup.lean` (Lemma A) | `evalPlaneZeroSet K₁ ≠ evalPlaneZeroSet K₂ → ¬ Associated K₁ K₂` |
| `PachDeZeeuw.Algebraic.chartEquiv_image_planeCurveZeroSet` | `lean/LeanFormalizations/PachDeZeeuw/ChartBridge.lean:97` | `chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p` |
| `Homeomorph.injective` (via `chartEquiv.injective`) | mathlib | injectivity of `chartEquiv : Point2 ≃ₜ ℝ × ℝ` |
| `Set.image_injective.mpr` | mathlib | image under injective map is injective on sets |
| `Set.Finite.cast_ncard_eq` (`Mathlib.Data.Set.Card`) | mathlib | `↑s.ncard = s.encard` for finite sets |
| `exact_mod_cast` | mathlib tactic | discharge `↑s.ncard ≤ ↑((2*d+1)^4)` from `ℕ` bound |

**Key encard↔ncard cast:** `Set.Finite.cast_ncard_eq : s.Finite → ↑s.ncard = s.encard`
(`Mathlib/Data/Set/Card.lean:590`)

## Proof outline

1. From `PlaneCurveZeroSet K₁ ≠ PlaneCurveZeroSet K₂`, derive
   `evalPlaneZeroSet K₁ ≠ evalPlaneZeroSet K₂` via image injectivity under
   `chartEquiv` and `chartEquiv_image_planeCurveZeroSet`.
2. Apply Lemma A (`not_associated_of_ne_evalPlaneZeroSet`) to get `¬ Associated K₁ K₂`.
3. Apply `irreducible_pair_intersection_bound` at `d₁ = d₂ = d`, obtaining
   `hfin : s.Finite` and `hncard : s.ncard ≤ (d + d + 1)^4`.
4. Rewrite `d + d + 1 = 2 * d + 1` by `omega`.
5. Rewrite via `hfin.cast_ncard_eq.symm` (goal becomes `↑s.ncard ≤ ((2*d+1)^4 : ℕ∞)`)
   then close with `exact_mod_cast hncard`.

## Build job count

8480 jobs (full project build through EdgeBDedup). EdgeBDedup elaboration: ~8 s.

## Axiom check (`#print axioms`)

```
'PachDeZeeuw.Algebraic.planeCurveZeroSet_inter_encard_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'PachDeZeeuw.Algebraic.not_associated_of_ne_evalPlaneZeroSet' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`, no custom axioms.

## Worktree branch and commit

Branch: `worktree-agent-a381e475600cd9db4`
Commit: (see git log after commit)
