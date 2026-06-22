# Corollary 24 — Edge-B Euclidean transport (`EdgeBChartBridge.lean`)

Author: Adam McKenna (orchestrator, written + validated inline on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open scoped Classical; open CrossingLemma PachSharir`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBChartBridge.lean`.

Status: **PROVEN, sorry-free, axiom-clean.** `#print axioms edgeB_crossingInput_euclidean`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`, no
custom axioms). Same closure for `incidenceCount_equiv_eq`.

## Scope

This node transports the landed `edgeB_crossingInput` (which works in `ℝ × ℝ` with
`evalPlaneZeroSet` curve sets) to a version where:

- the point set is `P : Finset (EuclideanSpace ℝ (Fin 2))`,
- each curve is the Euclidean zero set `{x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0}`.

The transport uses the landed homeomorphism `chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`
(`ChartBridge.lean`) and its intertwiner `eval_eq_evalPlane_chart`.

## Shipped signatures (exact)

```lean
theorem incidenceCount_equiv_eq {α β ι : Type*} [DecidableEq (Set α)] [DecidableEq (Set β)]
    [DecidableEq β]
    (e : α ≃ β)
    (P : Finset α) (Γ : Finset ι) (f : ι → Set β) :
    incidenceCount P (Γ.image (fun H => e ⁻¹' f H)) =
      incidenceCount (P.image e) (Γ.image f)

theorem edgeB_crossingInput_euclidean
    (hCL : CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H =>
        p ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0} ∧
        q ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0})).card ≤ M)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₁.1 = 0} ∩
       {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₂.1 = 0}).encard ≤ (M : ℕ∞)) :
    (incidenceCount P (Γ.image (fun H =>
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0})) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ))
```

## Proof structure

### `incidenceCount_equiv_eq` (key helper)

Given a bijection `e : α ≃ β`, the incidence count of `P` against
`Γ.image(fun H => e⁻¹'(f H))` equals that of `P.image e` against `Γ.image f`.

The proof proceeds via `incidenceCount_eq_sum`:

1. Observe `Γ.image(fun H => e⁻¹'(f H)) = (Γ.image f).image(e⁻¹'·)` (extensionally,
   proven by `ext s; simp [Finset.mem_image]`).

2. Key injectivity: `t₁, t₂ : Set β, e⁻¹' t₁ = e⁻¹' t₂ → t₁ = t₂`. Proof:
   `congrArg (e '' ·)` + `Set.image_preimage_eq _ e.surjective` on both sides.

3. Apply `Finset.sum_image` (requires injectivity of `t ↦ e⁻¹' t` on `Γ.image f`,
   which holds by step 2) to rewrite
   `Σ_{s ∈ (Γ.image f).image(e⁻¹'·)} |P ∩ s|  =  Σ_{t ∈ Γ.image f} |P ∩ e⁻¹' t|`.

4. Termwise equality: `|P ∩ e⁻¹' t| = |(P.image e) ∩ t|`.
   The map `e` sends `P.filter(·∈e⁻¹' t)` bijectively to `(P.image e).filter(·∈t)`;
   injectivity gives `Finset.card_image_of_injective`; surjectivity of the map
   uses `Finset.mem_image` in both directions.

### `edgeB_crossingInput_euclidean`

1. Set `P' := P.image chartEquiv`.

2. **Intertwiner lemma**: `{x : Point2 | eval(fun i => xi) H.1 = 0} = chartEquiv⁻¹'(evalPlaneZeroSet H.1)`.
   Proved by `ext x; simp [Set.mem_setOf_eq, Set.mem_preimage, mem_evalPlaneZeroSet, eval_eq_evalPlane_chart]`.

3. **Incidence count transport** (`hcount_eq`):
   Rewrite Euclidean curve family as `Γ.image(fun H => chartEquiv⁻¹'(evalPlaneZeroSet H.1))`
   via `Finset.image_congr`, then apply `incidenceCount_equiv_eq chartEquiv.toEquiv`.

4. **Transport `hpp`** to `hpp'` over `P'`: unfold `P' = P.image chartEquiv`, extract
   pre-images `p₀, q₀ ∈ P` with `p = chartEquiv p₀`, `q = chartEquiv q₀`, use
   `eval_eq_evalPlane_chart` to rewrite the filter predicate.

5. **Transport `hcc`** to `hcc'` over `ℝ×ℝ` sets:
   - `{x : Point2 | eval ... Hi.1 = 0} = PlaneCurveZeroSet Hi.1` (by `rfl`).
   - `{z : ℝ×ℝ | evalPlane Hi.1 z = 0} = evalPlaneZeroSet Hi.1` (by `ext; simp [mem_evalPlaneZeroSet]`).
   - Rewrite via `chartEquiv_image_planeCurveZeroSet`: `evalPlaneZeroSet Hi.1 = chartEquiv '' PlaneCurveZeroSet Hi.1`.
   - `Set.image_inter chartEquiv.injective` combines the two image sets.
   - `Function.Injective.encard_image chartEquiv.injective` transports `encard ≤ M`.

6. **Apply `edgeB_crossingInput`** at `P'`, using `Finset.card_image_of_injective` to verify
   `P'.card = P.card`.

## Intertwiner lemmas consumed from `ChartBridge.lean`

| Lemma | Statement |
|-------|-----------|
| `eval_eq_evalPlane_chart` | `MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x)` |
| `chartEquiv_image_planeCurveZeroSet` | `chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p` |
| `chartEquiv.injective` | `chartEquiv` is injective |
| `chartEquiv.surjective` | `chartEquiv` is surjective (via `e.surjective` in `incidenceCount_equiv_eq`) |

## Gate results

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBChartBridge` →
  `Build completed successfully (8527 jobs).` — no warnings or errors from this file.
  (Existing pre-landing warnings in PLCollarSeparation, SzemerediTrotter, etc. are unrelated.)
- `#print axioms edgeB_crossingInput_euclidean` = `[propext, Classical.choice, Quot.sound]`.
- `#print axioms incidenceCount_equiv_eq` = `[propext, Classical.choice, Quot.sound]`.
- No `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `axiom` in file.

## Boundary (what this does NOT do — downstream nodes)

- The `hpp`/`hcc` hypotheses are still in the `PlanePoly`/`evalPlane` form (not `TwoDegreesOfFreedom`).
  The `TwoDegreesOfFreedom → (hpp, hcc)` conversion (with zero-set injectivity on `Γ`) is a separate
  downstream node.
- Conditional on the parked `CrossingLemmaMultigraphStatement`.
- Does not handle the `D>2`/`e>1` lift or the shear application — those are separate downstream nodes.

PROVEN. No CONJECTURED / EMPIRICALLY-VERIFIED / HEURISTIC content.
