# Corollary 24 — Edge-B component reduce (`EdgeBComponentReduce.lean`)

Author: Adam McKenna
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open CrossingLemma`, `open scoped Classical`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBComponentReduce.lean`.

Status: **PROVEN, sorry-free, axiom-clean.** `#print axioms edgeB_crossingInput_2dof`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`, no
custom axioms). The conditional `hCL : CrossingLemmaMultigraphStatement` is carried as a
HYPOTHESIS, not discharged, so it does not appear in the axiom closure — exactly as in
the landed `edgeB_crossingInput`.

## Scope (the `edgeB-component-reduce` bridge node, design §5.3)

`edgeB_crossingInput_2dof` is the `TwoDegreesOfFreedom`-input surface of the landed
`edgeB_crossingInput` (`EdgeBCrossingInput.lean`). It concludes the SAME Pach–Sharir
incidence bound with the SAME constant `edgeBCrossingConst d M = 64·M·cConst d`, but takes
the paper-faithful `PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M`
(`h2dof`) plus one explicit injectivity hypothesis (`hinj`) IN PLACE OF the `hpp`/`hcc`
clauses that `edgeB_crossingInput` consumes directly. The proof derives `hpp` and `hcc`
from `h2dof + hinj`, then applies `edgeB_crossingInput`. PURE COMPOSITION over
`edgeB_crossingInput` + the `TwoDegreesOfFreedom` definition; no new analysis.

## Shipped signature (exact)

```lean
theorem edgeB_crossingInput_2dof
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hinj : Set.InjOn (fun H : EdgeBCurve d => evalPlaneZeroSet H.1) ↑Γ)
    (h2dof : PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M) :
    (PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ))
```

`hinj` binder note: the lambda is annotated `fun H : EdgeBCurve d => …`. Without the domain
annotation the binder elaborates before `↑Γ` pins the domain, and `H.1` (the `Σ'` projection)
fails to resolve (`Invalid projection: Type of H is not known`). The annotated form is
definitionally the same map as the (unannotated) one inside `Γ.image (…)`, so `set f := …`
folds both `hinj` and `h2dof` onto the single atom `f`.

## The chosen `hinj` and why it is minimal/correct

`hinj : Set.InjOn (fun H : EdgeBCurve d => evalPlaneZeroSet H.1) ↑Γ` — the zero-set map
`f := H ↦ evalPlaneZeroSet H.1` is injective on the carrier family `Γ`. This is the
WEAKEST single hypothesis that makes BOTH `hpp` and `hcc` follow from `h2dof`:

* **`hcc` needs it.** `hcc` ranges over distinct carrier indices `H₁ ≠ H₂ ∈ Γ`, but
  `h2dof.1` (curve–curve) ranges over the DEDUPLICATED image family `Γ.image f` and never
  compares an element with itself. To fire `h2dof.1` on the pair `(f H₁, f H₂)` we need
  `f H₁ ≠ f H₂`, i.e. `InjOn` (contrapositive). Without it, `H₁ ≠ H₂` with `f H₁ = f H₂`
  an INFINITE curve forces `hcc` to demand `(f H₁ ∩ f H₂).encard = (f H₁).encard ≤ M`, which
  is false — exactly the obstruction recorded in the `EdgeBCrossingInput.lean` scoping note.
  The weakest fix that lets the `h2dof.1` clause fire on every distinct index pair is
  `H₁ ≠ H₂ → f H₁ ≠ f H₂`, which is `Set.InjOn f ↑Γ`.
* **`hpp` needs it.** `hpp` bounds the INDEX count `Γ.filter (p,q on H).card`; `h2dof.2`
  (point–point) bounds the ZERO-SET count `(Γ.image f).filter (p,q ∈ γ).card`. `f` carries
  the filtered index subset `s ⊆ Γ` into the filtered image subset `t`
  (`Finset.mem_image_of_mem`), and `hinj.mono` (subset `s ⊆ Γ`) gives `InjOn f ↑s`, so
  `Finset.card_le_card_of_injOn` yields `s.card ≤ t.card ≤ M`. Two distinct indices through
  `p, q` with the SAME zero set would collapse to one image element and the index count
  could exceed the deduplicated count; `hinj` forbids exactly that. (`hpp` already needs full
  `InjOn` on the filtered subset, so no weaker-than-`InjOn` variant buys anything.)

Plain `Set.InjOn` is therefore the cleanest hypothesis discharging both. A weaker pairwise
disjunction ("distinct indices have distinct zero sets OR meet in `≤ M` points") would
suffice for `hcc` alone but not simplify `hpp`, so it is not adopted.

## The bridge proof

`set f := fun H => evalPlaneZeroSet H.1`; `obtain ⟨h2cc, h2pp⟩ := h2dof`.

* `hcc`: `intro H₁ hH₁ H₂ hH₂ hne`; `hZne : f H₁ ≠ f H₂ := fun h => hne (hinj hH₁ hH₂ h)`;
  `exact h2cc (f H₁) (mem_image_of_mem f hH₁) (f H₂) (mem_image_of_mem f hH₂) hZne`. The
  goal's `{z | evalPlane H₁.1 z = 0}` is `f H₁` up to `rfl` (`evalPlaneZeroSet` unfolds to
  the set-builder, `LocalArc.lean:48`), so `exact` closes by defeq.
* `hpp`: `set s := Γ.filter (…)`, `set t := (Γ.image f).filter (fun γ => p ∈ γ ∧ q ∈ γ)`;
  `hMaps : MapsTo f ↑s ↑t` by `Finset.coe_filter` + `mem_image_of_mem`; `hInj : InjOn f ↑s`
  by `hinj.mono` (the `Finset.coe_filter` subset `s ⊆ Γ`); then
  `Finset.card_le_card_of_injOn f hMaps hInj : s.card ≤ t.card` and `h2pp p hp q hq hpq :
  t.card ≤ M` compose by `le_trans`. `open scoped Classical` makes the `set t` filter use the
  same `DecidablePred` instance as `TwoDegreesOfFreedom`'s, so `t.card ≤ M := h2pp …`
  type-checks (`t` unifies with `h2pp`'s RHS filter Finset).
* Close: `exact edgeB_crossingInput hCL d M hM P Γ hpp hcc`.

## The real-field subtlety (why an injectivity hypothesis is genuinely required)

The map `H ↦ evalPlaneZeroSet H.1` is NOT injective on `EdgeBCurve d` in general. Three
families of collisions over ℝ:

1. **Associates.** `h` and `c·h` (`c ≠ 0`) are distinct `PlanePoly` carriers but have the
   same zero set; both can be irreducible-up-to-units.
2. **Empty real zero set.** `x²+1` and `x²+2` are distinct irreducible real polynomials, both
   with EMPTY real zero set, hence the SAME zero set `∅`.
3. **Coinciding finite real zero sets.** Distinct irreducible real polynomials whose real zero
   sets are finite can coincide as point sets.

For collision (1)/(3) with an INFINITE shared curve, `hcc` would demand a finite
self-intersection of the whole curve, which is false; a `.image`-deduplicated
`TwoDegreesOfFreedom` clause cannot supply that (`h2dof ⇏ hcc`). So an injectivity-type
hypothesis is unavoidable. The injectivity holds precisely for carriers with INFINITE real
zero set (where the real zero set is Zariski-dense in the complex curve and so determines the
irreducible polynomial up to scalar); the finite/empty-zero-set irreducible factors are the
exceptions, and they carry only finitely many real incidences.

## Landed leaves consumed

- `edgeB_crossingInput` (`EdgeBCrossingInput.lean`) — the composition target.
- `PachSharir.TwoDegreesOfFreedom`, `PachSharir.incidenceCount` (`Theorem23.lean`).
- `EdgeBCurve`, `evalPlaneZeroSet`, `edgeBCrossingConst`, `cConst`
  (`EdgeBMultigraph.lean`, `LocalArc.lean`, `EdgeBCrossingInput.lean`).
- mathlib: `Finset.card_le_card_of_injOn`, `Finset.mem_image_of_mem`, `Finset.coe_filter`,
  `Set.InjOn.mono`, `Set.mem_setOf_eq`, `le_trans`.

## New local content

- `edgeB_crossingInput_2dof` — the `TwoDegreesOfFreedom`-input bridge: derive `hpp`/`hcc`
  from `h2dof + hinj`, then apply `edgeB_crossingInput`.

No new analysis. Pure glue over the landed `edgeB_crossingInput` + elementary Finset/InjOn
combinatorics.

## Gate results

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBComponentReduce`
  → `Build completed successfully (8527 jobs).` The new file built `✔ … EdgeBComponentReduce
  (20s)` with NO diagnostics attributable to it. The only build warnings are pre-existing
  (the parked `PLCollarSeparation.lean` `unusedSimpArgs` linter hits and the line-case
  `SzemerediTrotter.lean:4533` `sorry`), off this proof's closure — confirmed by the clean
  axiom check below.
- `#print axioms edgeB_crossingInput_2dof` = `[propext, Classical.choice, Quot.sound]`
  (verified in a transient `/tmp/ax.lean` via `lake env lean`). `hCL` is NOT in the closure.
- No `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `axiom` /
  `#print` in shipped code.
- Aggregator `CrossingLemma.lean` NOT edited (imports wired at merge time, per task scope).

## SECONDARY — how `hinj` is discharged downstream (classification)

The downstream node reduces a single degree-`≤d` carrier to its normalized irreducible
factors and keeps only the geometrically relevant ones:

1. **PROVEN-AVAILABLE (mathlib).** `MvPolynomial (Fin 2) ℝ` is a UFD, so
   `UniqueFactorizationMonoid.normalizedFactors` gives, for each carrier, a multiset of
   normalized prime (= irreducible) factors, deduplicated up to associates by normalization
   (`normalizedFactors`, `factors_eq_normalizedFactors`,
   `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors`). Discarding factors with
   `∂_y = 0` and factors with finite/empty real zero set is a finite filtering step, also
   constructible (`decomp_D1_bad_finite` already supplies the `∂_y ≠ 0` carrier predicate).
   Collisions of type (1) — associates — are removed by normalization. CLASSIFICATION:
   PROVEN-CONSTRUCTIBLE from mathlib (no new analysis), modulo wiring.

2. **NAMED OBLIGATION (NOT in mathlib).** The load-bearing step — *distinct normalized
   irreducible real factors with INFINITE real zero set have DISTINCT zero sets*, i.e. an
   irreducible `f ∈ ℝ[x,y]` with `Z_ℝ(f)` infinite is determined up to scalar by `Z_ℝ(f)` —
   is a real-algebraic-geometry fact mathlib does NOT have. The complex Nullstellensatz
   (`vanishingIdeal_zeroLocus_eq_radical`, `Mathlib.RingTheory.Nullstellensatz`) needs an
   ALGEBRAICALLY CLOSED field and does not transfer to ℝ (over ℝ, `x²+y²` vanishes only at
   the origin, `x²+1` nowhere — Hilbert's Nullstellensatz fails). The correct tool is the REAL
   Nullstellensatz / real radical, and `grep` over `.lake/packages/mathlib/Mathlib/` finds
   ZERO files mentioning `realRadical`/`RealRadical`/`RealNullstellensatz` (checked
   2026-06-21). CLASSIFICATION: **named downstream obligation**
   `edgeB-zeroset-injectivity-real` — NOT fabricated here. It is the only non-mathlib step
   between `h2dof` and `hinj`. CONJECTURED true (standard real-algebraic geometry: an
   irreducible real polynomial whose real zero set has dimension `1` is, up to a real scalar,
   the unique reduced equation of that curve), but it has no Lean proof and no mathlib lemma.

## Boundary (what this does NOT do — downstream nodes)

- Conditional on the parked `CrossingLemmaMultigraphStatement` (carried as `hCL`), exactly as
  `edgeB_crossingInput`.
- Works in the `ℝ × ℝ` chart over post-shear irreducible carriers `EdgeBCurve d` with `h2dof`
  + `hinj` supplied. Discharging `hinj` (the factor reduction + the named real-determinacy
  obligation above), the shear application, the `EuclideanSpace`/arbitrary-degree lift, and the
  `D>2`/`e>1` step remain the separate downstream nodes of design §5.3.

PROVEN. The bridge inequality is fully formalized; `hinj` is an explicit hypothesis. The only
CONJECTURED / not-in-mathlib content is the SECONDARY downstream discharge of `hinj`, classified
above as the named obligation `edgeB-zeroset-injectivity-real`.
