# Corollary 24 — Discharging `hinj` by zero-set deduplication: analysis

Author: math-professor (analysis)
Date: 2026-06-21
Toolchain context: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespaces
`PachDeZeeuw.Algebraic`, `PachSharir`.

## 0. What was investigated

The bridge `edgeB_crossingInput_2dof` (`EdgeBComponentReduce.lean`, LANDED, axiom-clean)
concludes the Pach–Sharir incidence bound from

- `h2dof : PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M`, and
- `hinj : Set.InjOn (fun H : EdgeBCurve d => evalPlaneZeroSet H.1) ↑Γ`.

The `edgeB-component-reduce` node reported that discharging `hinj` at the polynomial level
needs a real-determinacy lemma absent from mathlib (an irreducible `f ∈ ℝ[x,y]` with infinite
real zero set is determined up to a real scalar by `Z_ℝ(f)`), which it named
`edgeB-zeroset-injectivity-real`. The complex Nullstellensatz
(`vanishingIdeal_zeroLocus_eq_radical`, `Mathlib.RingTheory.Nullstellensatz`) requires
`IsAlgClosed` and does not transfer to ℝ. I confirmed by `grep` over
`.lake/packages/mathlib/` (2026-06-21) that there is **no** `realRadical` / `RealRadical` /
`RealNullstellensatz` and no `edgeB_zeroset_injectivity_real` anywhere in the tree.

The candidate resolution: build `Γ` (the `Finset (EdgeBCurve d)` fed to
`edgeB_crossingInput_2dof`) by **deduplicating irreducible components by their zero set** —
form the `Finset (Set (ℝ × ℝ))` of distinct component zero sets, then pick one defining
`EdgeBCurve` per distinct set via a classical section. Then `hinj` holds by construction.

This document evaluates the three questions that decide whether this works.

## 1. Definitions and notation (self-contained)

- `PlanePoly := MvPolynomial (Fin 2) ℝ` (`AlgebraicPrelim.lean:1516`).
- `Point2 := EuclideanSpace ℝ (Fin 2)` (`AlgebraicPrelim.lean:22`).
- `evalPlane h : ℝ × ℝ → ℝ`, `xy ↦ eval (i ↦ if i=0 then xy.1 else xy.2) h` (`Bezout.lean:451`).
- `evalPlaneZeroSet h := {xy : ℝ × ℝ | evalPlane h xy = 0}` (`LocalArc.lean:48`). This is the
  carrier the target `Γ.image (…)` ranges over.
- `PlaneCurveZeroSet p := {x : Point2 | eval (i ↦ x i) p = 0}` (`AlgebraicPrelim.lean:118`). This
  is the carrier the **landed Bézout** machinery is stated on.
- `chartEquiv : Point2 ≃ₜ ℝ × ℝ` (`ChartBridge.lean:56`), a homeomorphism, with
  `chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p` (`ChartBridge.lean:97`) and
  `chartEquiv ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p` (`ChartBridge.lean:112`).
- `EdgeBCurve d := Σ' h : PlanePoly, Irreducible h ∧ h.totalDegree ≤ d ∧ pderiv 1 h ≠ 0`
  (`EdgeBMultigraph.lean:63`).
- `TwoDegreesOfFreedom P Γ M` (`Theorem23.lean:45`): (cc) `∀ γ₁ ≠ γ₂ ∈ Γ, (γ₁ ∩ γ₂).encard ≤ M`;
  (pp) `∀ p₁ ≠ p₂ ∈ P, #{γ ∈ Γ : p₁,p₂ ∈ γ} ≤ M`.

**Landed Bézout leaves (signatures read this session from `Bezout.lean`):**

- `irreducible_pair_intersection_bound` (`Bezout.lean:371`): for `Irreducible h`,
  `Irreducible k`, `h.totalDegree ≤ d₁`, `k.totalDegree ≤ d₂`, **`¬ Associated h k`**:
  `(PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧ (…).ncard ≤ (d₁ + d₂ + 1)^4`.
- `factor_intersection_bound` (`Bezout.lean:1028`): the same, for `k` a normalized factor of a
  nonzero partial derivative; bound `(d+1)^4`.
- `nonsingular_point_has_infinite_zeroSet` (`Bezout.lean:726`): if `z ∈ PlaneCurveZeroSet h` and
  `∂₀h(z) ≠ 0 ∨ ∂₁h(z) ≠ 0`, then `(PlaneCurveZeroSet h).Infinite`.
- `finite_zeroSet_subset_singularities` (`Bezout.lean:738`): if `(PlaneCurveZeroSet h).Finite`,
  then `PlaneCurveZeroSet h ⊆ SingularPointSet h`.

mathlib facts I rely on: `Set.Infinite.encard_eq : s.Infinite → s.encard = ⊤`
(`Mathlib/Data/Set/Card.lean:97`); `Finset.card_le_card_of_injOn`; `Set.ncard_le_ncard`.

## 2. The crux that the candidate must clear (state this up front)

`irreducible_pair_intersection_bound` is keyed on **`¬ Associated h k`**, *not* on
`Z_ℝ(h) ≠ Z_ℝ(k)`. Over ℝ these are NOT the same condition. The two are related by exactly one
implication, and the candidate must use only that direction:

> **Lemma A (the only safe direction). Status: PROVEN.** If `h, k` are nonzero with
> `evalPlaneZeroSet h ≠ evalPlaneZeroSet k` (equivalently `PlaneCurveZeroSet h ≠ PlaneCurveZeroSet k`,
> via `chartEquiv`), then `¬ Associated h k`.
>
> *Proof.* Contrapositive. If `Associated h k`, then `k = u·h` for a unit `u ∈ ℝ[x,y]`. Units of
> `ℝ[x,y]` are exactly the nonzero constants (`ℝ` is a field, so `MvPolynomial.isUnit_iff`), so
> `k = c·h` with `c ≠ 0`. Then `eval z k = c·(eval z h)`, so `eval z k = 0 ↔ eval z h = 0`,
> i.e. `PlaneCurveZeroSet h = PlaneCurveZeroSet k`; transport by `chartEquiv` gives
> `evalPlaneZeroSet h = evalPlaneZeroSet k`. ∎

The **converse is false**: there exist non-associated irreducibles with the same real zero set.
EMPIRICALLY VERIFIED witnesses (scratch `/tmp/realalg_check.py`, exact, not random):

- *Empty real locus.* `x²+1` and `x²+2`: both irreducible over `ℝ[x,y]`, both `Z_ℝ = ∅`,
  not associated. (Collision type observed in the build doc.)
- *Finite nonempty real locus.* `x²+y²` and `2x²+y²`: both irreducible over `ℝ[x,y]`, both
  `Z_ℝ = {(0,0)}`, not associated (no scalar `c` has `c = 2` and `c = 1`). Confirmed by computing
  the real loci.

Lemma A is the direction the candidate **does** need (distinct sets ⟹ non-associated ⟹ Bézout
applies), so the false converse is not an obstruction *to Question 2*. But the false converse is
**precisely** the reason `hinj` cannot be proved at the polynomial level without real AG: two
non-associated irreducibles can map to the SAME zero set, so the zero-set map is genuinely
non-injective on `EdgeBCurve d`. The candidate sidesteps this by never claiming polynomial-level
injectivity — it deduplicates the *image* and chooses a section. Whether that fully avoids the
real-AG lemma is Question 3, answered below.

## 3. Question 1 — does 2-DOF on the original curves forbid a shared infinite component?

**Restated claim to check.** If two distinct original curves `γ₁ ≠ γ₂` (each
`evalPlaneZeroSet f_i`, the family 2-DOF with multiplicity `M`) shared an irreducible component
`C` with infinite real zero set, then `C ⊆ γ₁ ∩ γ₂`, so `(γ₁ ∩ γ₂).encard = ⊤ > M`, contradicting
the curve–curve clause. Hence no infinite-real-locus component is shared across distinct original
curves.

> **Proposition 1 (the shared-infinite-component exclusion). Status: PROVEN (modulo the
> set-theoretic membership facts below, all elementary).**
>
> Let `f₁, f₂` define `γ_i = evalPlaneZeroSet f_i`, with `γ₁ ≠ γ₂` both in the 2-DOF family, and
> let `C` be an irreducible factor common to `f₁` and `f₂` with `evalPlaneZeroSet C` infinite.
> Then `evalPlaneZeroSet C ⊆ γ₁` and `⊆ γ₂` (a factor's zero set is contained in the product's
> zero set: `eval z C = 0 ⟹ eval z (f_i) = 0`, since `f_i = C · (rest)`). So
> `evalPlaneZeroSet C ⊆ γ₁ ∩ γ₂`, and `(γ₁ ∩ γ₂)` is infinite, whence
> `(γ₁ ∩ γ₂).encard = ⊤` (`Set.Infinite.encard_eq`). The curve–curve clause requires
> `(γ₁ ∩ γ₂).encard ≤ (M : ℕ∞) < ⊤`, contradiction. ∎

**This is correct.** I verified the only nontrivial input — "a factor's zero set is contained in
the product's zero set" — is immediate: `f_i = C · g_i` in `ℝ[x,y]`, so `eval z f_i = (eval z C)·(eval z g_i)`,
and `eval z C = 0 ⟹ eval z f_i = 0`. The `encard = ⊤` step is the landed mathlib
`Set.Infinite.encard_eq`. No real AG is used here.

**The real-vs-complex subtlety, addressed explicitly.** The claim is correctly scoped to
components with **infinite real zero set**. The argument fails for finite/empty-real-locus
components, and it must — those components do NOT carry the contradiction:

- A shared component `C` with `Z_ℝ(C)` finite contributes only finitely many real points to
  `γ₁ ∩ γ₂`, so 2-DOF does not exclude it. Two distinct original real curves CAN share an
  irreducible factor whose real locus is finite (e.g. `f₁ = (x²+y²)·u`, `f₂ = (x²+y²)·v` with
  `u, v` distinct; the shared `x²+y²` has `Z_ℝ = {(0,0)}`). 2-DOF is satisfied as long as the
  *total* real intersection is `≤ M`.
- A shared component with `Z_ℝ(C) = ∅` (e.g. `x²+1`) contributes nothing to the real loci at all.

So **Proposition 1 only excludes shared components with INFINITE real locus**, and that is exactly
the class for which a contradiction is available. This is the correct and complete statement;
the build doc's phrasing ("no infinite component is shared across distinct original curves") is
accurate.

**The second half of Question 1 — "are infinite-real-locus components the only ones carrying > M
incidences?"** This is the load-bearing subtlety, and the honest answer is more delicate than the
candidate's framing.

> **Observation 1a. Status: PROVEN.** A component with finite real zero set carries at most
> `|Z_ℝ(C)|` real incidences, a finite number. It cannot by itself produce `> M` incidences with a
> *single other curve* via the curve–curve clause **once it is deduplicated**, but it CAN inflate
> the per-point multiplicity and the component count. The real content is in Question 2, not here.

The clean statement that survives: *for the curve–curve clause*, only infinite-real-locus shared
components threaten the bound, and Proposition 1 excludes them across distinct **original** curves.
But finite-real-locus components are not harmless for the **point–point** clause or for the
**within-curve** pair count — those are handled by Bézout in Question 2, not by Proposition 1.

## 4. Question 2 — the multiplicity `M'` of the deduplicated component family

### 4.1 The construction (made precise)

Fix the input: `P : Finset (ℝ × ℝ)` and a finite family of original curves
`Γ₀ : Finset (Set (ℝ × ℝ))`, each `γ ∈ Γ₀` equal to `evalPlaneZeroSet f_γ` for a chosen nonzero
`f_γ` of total degree `≤ d` (the `IsAlgebraicCurveDefinedBy`/`IsPlaneAlgebraicCurveOfDegreeLE`
input, post-chart, post-shear). The construction:

1. For each `γ`, factor `f_γ` into normalized irreducible factors
   (`UniqueFactorizationMonoid.normalizedFactors`, `ℝ[x,y]` a UFD), keep the factors `C` with
   `pderiv 1 C ≠ 0` (so each kept `C` is an `EdgeBCurve d` carrier; note
   `C.totalDegree ≤ f_γ.totalDegree ≤ d` by `normalized_factor_degree_le`-style facts already used
   in `factor_intersection_bound`). Call the kept multiset `Fac(γ)`.
2. Form the finite set of **distinct component zero sets**
   `𝒵 := (⋃_{γ ∈ Γ₀} Fac(γ)).image (fun C => evalPlaneZeroSet C) : Finset (Set (ℝ × ℝ))`.
3. For each `S ∈ 𝒵`, choose one carrier `H_S : EdgeBCurve d` with `evalPlaneZeroSet H_S.1 = S`
   (classical section over the nonempty fibre). Set `Γ := 𝒵.image (fun S => H_S)` — equivalently,
   the image of the section. Then `(fun H => evalPlaneZeroSet H.1) ∘ section = id` on `𝒵`, so
   `Set.InjOn (fun H => evalPlaneZeroSet H.1) ↑Γ` holds **by construction**.

> **CLAIM (construction-level injectivity). Status: PROVEN-modulo {classical section
> bookkeeping}.** `hinj` is definitional for `Γ` so built: the section is a right inverse of the
> zero-set map on its image, so the map is injective on the section's image. No determinacy of
> *which* polynomial is chosen is needed — any carrier with the right zero set works, and the
> section commits to one. This is the candidate's central correct insight.

### 4.2 Establishing `TwoDegreesOfFreedom P (Γ.image …) M'`

The deduplicated family's zero-set image is exactly `𝒵`. Take two distinct sets `C₁ ≠ C₂ ∈ 𝒵`.
They arise as `evalPlaneZeroSet K₁`, `evalPlaneZeroSet K₂` for irreducible carriers `K₁, K₂` (the
chosen sections, or any preimages). By Lemma A, `C₁ ≠ C₂ ⟹ ¬ Associated K₁ K₂`. Two cases:

- **Different original curves OR same curve — uniformly via Bézout.** Regardless of provenance,
  `K₁, K₂` are irreducible, degree `≤ d`, and **non-associated** (Lemma A). So
  `irreducible_pair_intersection_bound K₁ K₂ … (¬Associated)` gives
  `(PlaneCurveZeroSet K₁ ∩ PlaneCurveZeroSet K₂).ncard ≤ (d + d + 1)^4 = (2d+1)^4` and finiteness.
  Transport by `chartEquiv` (a homeomorphism; `chartEquiv_image_finite_iff` and the image
  commutes with `∩`): `(C₁ ∩ C₂).Finite` and `(C₁ ∩ C₂).ncard ≤ (2d+1)^4`. For a finite set,
  `encard = ncard` (cast), so `(C₁ ∩ C₂).encard ≤ ((2d+1)^4 : ℕ∞)`.

This is **cleaner than the candidate's two-case split**: I do not need to know whether `C₁, C₂`
came from the same or different original curves. Lemma A reduces the curve–curve clause to a
single Bézout application, because **the dedup-by-zero-set already guarantees non-associated
carriers** for any distinct image pair. The candidate's "different curves ⟹ `⊆ γ_i ∩ γ_j` ≤ M"
sub-case is *not needed* for the curve–curve clause and in fact would give the weaker bound `M`;
Bézout gives the uniform `(2d+1)^4`.

> **Proposition 2 (curve–curve clause of the deduped family). Status: PROVEN-modulo {landed
> `irreducible_pair_intersection_bound`, `chartEquiv` transport, Lemma A, finite-encard cast}.**
> Any two distinct `C₁ ≠ C₂ ∈ 𝒵` satisfy `(C₁ ∩ C₂).encard ≤ ((2d+1)^4 : ℕ∞)`.

The **point–point clause** is the one place the original `M` and the component blow-up combine:

> **Proposition 3 (point–point clause of the deduped family). Status: CONJECTURED-constructible;
> the constant is the genuine subtlety.** For distinct `p₁, p₂ ∈ P`, the number of deduped
> component sets `C ∈ 𝒵` with `p₁, p₂ ∈ C` is `≤ M · d`.
>
> *Argument.* A deduped set `C ∈ 𝒵` containing both points is the zero set of an irreducible
> factor of some original `f_γ`. A factor of `f_γ` with `p₁, p₂` on its locus forces `p₁, p₂ ∈ γ`
> (factor locus ⊆ product locus, as in Prop 1). The original point–point clause (pp of `h2dof₀`,
> the 2-DOF for `Γ₀`) bounds the number of **original** curves through `p₁, p₂` by `M`. Each
> original `f_γ` has `≤ d` irreducible factors (degree `≤ d`, each factor degree `≥ 1`), hence
> contributes `≤ d` distinct component zero sets. So the number of deduped sets through both
> points is `≤ M · d`.

There is a **gap to flag** in Proposition 3: distinct original curves may share a *deduped* set
`C` (when they share a factor with the same zero set), so the map "deduped set through `p₁,p₂`" →
"original curve through `p₁,p₂`" is not injective into `Γ₀`, and the naive count overcounts in the
wrong direction. The correct bound goes the other way: each deduped set arises from **at least
one** original curve through both points, and we are counting deduped sets, so we bound
`#{deduped sets through both} ≤ Σ_{γ through both} #{factors of γ} ≤ M · d`. The "≥ one original"
direction is what makes the sum an upper bound; sharing only helps (fewer distinct sets). So the
bound `M·d` is correct as an **upper** bound, but the argument must be phrased as a sum over
original curves, not an injection. **This is genuine combinatorics, not bookkeeping — it needs a
`Finset.card_le` via a surjection/cover argument.** Marked CONJECTURED-constructible; see FLAG.

### 4.3 The resulting `M'` and the blow-up

Combining Propositions 2 and 3:

> **`M' := max((2d+1)^4, M·d)`.** Status: CONJECTURED-constructible (PROVEN for the curve–curve
> half, Prop 2; CONJECTURED-constructible for the point–point half, Prop 3).

- Curve–curve multiplicity: `(2d+1)^4` (Bézout, landed; depends on `d` only, NOT on `M`).
- Point–point multiplicity: `M·d` (original `M` times the `≤ d` components per curve).
- So `M' = max((2d+1)^4, M·d)`, a polynomial in `d` times `M`. With the crude `bezout` constant
  `(2d+1)^8` (also landed) one would get `M' = max((2d+1)^8, M·d)`; the sharper
  `irreducible_pair_intersection_bound` gives `(2d+1)^4`.

**Incidence / constant blow-up.** The deduped family `Γ` has at most `d · |Γ₀|` curves (each
original curve contributes `≤ d` components; sharing reduces this). Feeding `Γ` (with `hinj` and
`TwoDegreesOfFreedom … M'`) into `edgeB_crossingInput_2dof` yields

```
incidenceCount P (Γ.image …) ≤ edgeBCrossingConst d M' · (|P|^{2/3}·|Γ|^{2/3} + |P| + |Γ|)
```

with `edgeBCrossingConst d M' = 64·M'·cConst d` (`EdgeBCrossingInput.lean:65`). Translating back to
the **original** incidence count and original `|Γ₀|`:

- `incidenceCount P (Γ₀.image …) ≤ d · incidenceCount P (Γ.image …)` is the wrong direction; the
  correct relation is that each original incidence `(p, γ)` with `p ∈ γ` over an infinite-locus
  factor maps to an incidence with that factor's deduped set, but a point can be on a finite-locus
  factor only. So `incidenceCount(P, Γ₀) ≤ incidenceCount(P, Γ)` up to the **finite-locus
  correction** discussed in §5 — this is NOT simply a factor of `d`, and is a separate accounting.
- `|Γ| ≤ d·|Γ₀|`, so `|Γ|^{2/3} ≤ d^{2/3}·|Γ₀|^{2/3}` and `|Γ| ≤ d·|Γ₀|`.

> **Net constant blow-up (for the curve-incidence portion). Status: CONJECTURED-constructible.**
> The Corollary-24 constant becomes `C(d, M) := 64 · max((2d+1)^4, M·d) · cConst d · d`, where the
> trailing `· d` absorbs `|Γ| ≤ d·|Γ₀|` into the `incidenceBoundTerm`. All factors are polynomial
> in `d` and linear in `M`, which `Corollary24Statement`'s `∀ d M, ∃ C` ordering permits. The
> finite-locus incidence correction (§5) adds a further `+ poly(d)·|Γ₀|` additive term, also
> absorbable.

## 5. Question 3 — what still requires real algebraic geometry?

### 5.1 The candidate's central claim is correct: `hinj` itself needs no real AG

> **Proposition 4. Status: PROVEN.** Deduplicating by zero set discharges `hinj` for the deduped
> family `Γ` with **zero** appeal to `edgeB-zeroset-injectivity-real`. The classical section is a
> right inverse of the zero-set map on `𝒵`, so injectivity is the elementary fact "a function with
> a right inverse on a set is injective on the image of that right inverse." We never need to
> decide, for two given polynomials, whether their zero sets are equal — we work with the
> set-image `𝒵` directly and pick representatives. The missing real-determinacy lemma is genuinely
> avoided.

This is the right resolution of the original obstruction. `edgeB-zeroset-injectivity-real`
("irreducible `f` with infinite `Z_ℝ(f)` is determined up to scalar by `Z_ℝ(f)`") was needed only
to prove *polynomial-level* injectivity (distinct kept factors ⟹ distinct zero sets). The dedup
strategy makes that statement irrelevant: it allows distinct polynomials to collapse to the same
zero set and simply keeps one. **`edgeB-zeroset-injectivity-real` is not needed.**

### 5.2 But three residual obligations remain — none is the avoided real-determinacy lemma

The candidate's claim "no real AG beyond landed Bézout + 2-DOF" is **almost** right. Forming `𝒵`
and the section does not reintroduce determinacy, but two *different* real-flavored facts surface,
plus one accounting subtlety.

**(R-1) Forming `𝒵 : Finset (Set (ℝ × ℝ))` needs `DecidableEq (Set (ℝ × ℝ))` — discharged by
`Classical.dec`, NOT a determinacy lemma. Status: PROVEN-available.** `Finset.image` into a type
with `DecidableEq` is fine under `open scoped Classical` (the line template and
`EdgeBComponentReduce.lean` already do this for `Finset (Set …)`). No decidability of set equality
is *computed*; it is supplied classically. **This does NOT secretly reintroduce determinacy** — the
dedup is a classical `Finset.image`, and the resulting `Finset` is a well-defined mathematical
object whether or not equality is decidable. Confirmed: `incidenceCount`/`TwoDegreesOfFreedom` are
already `noncomputable` over `Finset (Set α)` with `open scoped Classical`.

**(R-2) The finite-locus components carry real incidences that the multigraph route does NOT
count, and must be accounted separately. Status: CONJECTURED-constructible; this is the genuine
residual, and it IS partly real-AG-flavored.** This is the subtlety Question 1 flagged and the
candidate underweights. The Edge-B multigraph is built from `EdgeBCurve` carriers and counts
incidences over **good intervals / sheets**, which presupposes the curve carries a 1-dimensional
arc near incident points (the implicit-function `LocalArc` machinery needs `∂ ≠ 0` at a point with
`Z` infinite). An irreducible `EdgeBCurve` carrier with **finite** real zero set (e.g. `x²+y²`,
which has `pderiv 1 = 2y ≠ 0` as a polynomial yet `Z_ℝ = {(0,0)}`) contributes points that:

- are NOT on any infinite sheet (the implicit-function arc does not exist there — the point is
  isolated in `Z_ℝ`), so they fall in the "bad-x" / leftover accounting, AND
- can still be incident points of `P`.

So the deduped family `Γ` may contain carriers whose real locus is finite, and the incidence
count `incidenceCount P (Γ.image …)` includes those finite-locus incidences. The Edge-B endgame
bounds them through the E1 bad-point accounting (`edgeB_incidence_le_numEdges_add`, the `c d · |Γ|`
slack, which is degree-only). **PROVEN-available that finitely many such points exist per curve**
(`finite_zeroSet_subset_singularities` + `finite_singularities_of_irreducible_bound`:
`(SingularPointSet h).ncard ≤ (d+1)^5`, `Bezout.lean:1085`). What is **CONJECTURED-constructible**
is that the *original* curve incidence count `incidenceCount(P, Γ₀)` is bounded by the deduped
count plus this finite-locus correction — the translation between the two families. This is real
accounting work, but it uses only **landed** real-AG (`finite_singularities_of_irreducible_bound`,
`nonsingular_point_has_infinite_zeroSet`), NOT the missing `edgeB-zeroset-injectivity-real`.

**(R-3) Proposition 3's point–point count is a cover argument, not an injection. Status:
CONJECTURED-combinatorial.** As noted in §4.2, the bound `#{deduped sets through both p₁,p₂} ≤ M·d`
must be phrased as a sum over the `≤ M` original curves through both points, each contributing
`≤ d` factor-zero-sets, because distinct original curves can share a deduped set. This is
`Finset.card`-cover combinatorics over landed `normalizedFactors` cardinality bounds; no real AG.

### 5.3 Verdict on Question 3

> **`edgeB-zeroset-injectivity-real` is genuinely AVOIDED by the dedup strategy.** Status: PROVEN
> (Proposition 4). The minimal *real-algebraic* residual is **R-2** (the finite-locus incidence
> correction), and it is dischargeable from **landed** leaves
> (`finite_singularities_of_irreducible_bound`, `nonsingular_point_has_infinite_zeroSet`,
> `finite_zeroSet_subset_singularities`) — it does NOT need a real Nullstellensatz / real radical /
> determinacy lemma. The remaining residuals are combinatorial (R-3) or classical-logic
> bookkeeping (R-1). **No new not-in-mathlib real-AG lemma is required.**

This is a strict improvement over the `edgeB-component-reduce` build doc's SECONDARY classification,
which listed `edgeB-zeroset-injectivity-real` as "the only non-mathlib step between `h2dof` and
`hinj`." Under the dedup strategy that step is removed; what replaces it is R-2/R-3, both
constructible from landed material.

## 6. Where the candidate's framing needs correction (precise list)

1. **Question 2's two-case split is unnecessary for the curve–curve clause.** The candidate
   proposes "different curves ⟹ `⊆ γ_i ∩ γ_j` ≤ M" and "same curve ⟹ Bézout." In fact Lemma A
   makes **every** distinct deduped pair non-associated, so a **single** Bézout application
   (`irreducible_pair_intersection_bound`) handles both, giving the uniform `(2d+1)^4` (better than
   `M` for the cross-curve case). The "different curves ⟹ ≤ M" route is correct but weaker and not
   needed.

2. **The point–point multiplicity is `M·d`, and the count is a cover, not an injection.** The
   candidate's "the count blows up by ≤ d" is the right magnitude, but the argument direction must
   be a sum over original curves (R-3), because deduped-set-sharing across original curves breaks
   injectivity into `Γ₀`.

3. **Finite-real-locus components are not negligible (R-2).** The candidate's Question 1 framing
   ("infinite real zero set components are the only ones carrying > M real incidences") is correct
   *for the curve–curve clause* but does not address that finite-locus irreducible carriers still
   appear in `Γ`, still carry `P`-incidences, and need the E1 bad-point accounting. This is the
   genuine residual, and the candidate's "no real AG beyond Bézout + 2-DOF" is true only because
   the needed real-AG (`finite_singularities_of_irreducible_bound`) is already landed.

4. **`M'` does NOT depend on `M` through the curve–curve clause.** The curve–curve multiplicity is
   `(2d+1)^4` (degree-only); `M` enters only through the point–point clause as `M·d`. So
   `M' = max((2d+1)^4, M·d)`. The candidate's `M' = max(M, B(d))` undercounts the point–point
   factor (it should be `M·d`, not `M`).

## 7. What uses finiteness / structural assumptions (stated explicitly)

- **Finiteness of `Γ₀`, `P`** — used throughout; `𝒵` is a finite image, the section is over finite
  fibres.
- **`ℝ[x,y]` is a UFD** — for `normalizedFactors` (PROVEN-available, mathlib).
- **`ℝ` is a field** — for `MvPolynomial.isUnit_iff` (units = nonzero constants), the engine of
  Lemma A.
- **`chartEquiv` is a homeomorphism** — for transporting finiteness/cardinality of intersections
  between `Point2` (Bézout's carrier) and `ℝ × ℝ` (the target carrier).
- **2-DOF on the ORIGINAL family `Γ₀`** — supplies the `≤ M` point–point bound feeding Prop 3.
  Note: the input 2-DOF is on `Γ₀` (the original `IsAlgebraicCurveDefinedBy` curves), and the
  output 2-DOF is on the deduped component family `𝒵`. These are different families; the analysis
  is precisely the transfer between them.
- **No use of**: real Nullstellensatz, real radical, polynomial-level zero-set injectivity,
  decidability of real set equality (classical only).

## FLAG FOR IMPLEMENTER

The `edgeB-component-reduce` / `edgeB-corollary-lift` nodes should discharge `hinj` and produce
`TwoDegreesOfFreedom (deduped) M'` via the following Lean lemmas. **`edgeB-zeroset-injectivity-real`
is NOT needed** — do not attempt to prove or assume a real Nullstellensatz/real radical lemma.

```
FLAG FOR IMPLEMENTER: associated-of-ne-zeroset   [Lemma A; the engine; LOW risk]
  lemma not_associated_of_ne_evalPlaneZeroSet (h k : PlanePoly) (hh : h ≠ 0) (hk : k ≠ 0)
      (hne : evalPlaneZeroSet h ≠ evalPlaneZeroSet k) : ¬ Associated h k
  Proof: contrapositive; Associated ⟹ k = c·h, c ≠ 0 (MvPolynomial.isUnit_iff over the field ℝ);
    eval z k = c·eval z h ⟹ zero sets equal; transport by chartEquiv (or argue directly on
    evalPlaneZeroSet via evalPlane being eval). REUSE: MvPolynomial.isUnit_iff,
    ChartBridge.chartEquiv_image_planeCurveZeroSet (or none — direct).
  Risk: LOW. Pure ring/eval algebra.

FLAG FOR IMPLEMENTER: dedup-section + hinj-by-construction   [Proposition 4; LOW-MED risk]
  Build Γ : Finset (EdgeBCurve d) as 𝒵.image (section), where
    𝒵 := (kept-factors).image (fun C => evalPlaneZeroSet C.1) : Finset (Set (ℝ × ℝ)),
    section S := Classical.choose (proof that S ∈ 𝒵 has an EdgeBCurve preimage).
  Then hinj : Set.InjOn (fun H => evalPlaneZeroSet H.1) ↑Γ is
    Function.LeftInverse ⟹ InjOn on the image (the section is a right inverse of the zero-set map
    on 𝒵). REUSE: Classical.choose/choose_spec, Set.InjOn, Function.LeftInverse.injOn-style.
  open scoped Classical for DecidableEq (Set (ℝ × ℝ)) (R-1; no determinacy computed).
  Risk: LOW-MED (the section bookkeeping; the math is trivial).

FLAG FOR IMPLEMENTER: deduped-curve-curve-clause   [Proposition 2; LOW-MED risk; the Bézout step]
  lemma deduped_cc (C₁ C₂ ∈ 𝒵) (hne : C₁ ≠ C₂) : (C₁ ∩ C₂).encard ≤ ((2*d+1)^4 : ℕ∞)
  Proof: pick irreducible carriers K₁,K₂ with Zset = C₁,C₂; Lemma A ⟹ ¬Associated K₁ K₂;
    irreducible_pair_intersection_bound K₁ K₂ (deg ≤ d, deg ≤ d) (¬Assoc) gives
    (PlaneCurveZeroSet K₁ ∩ PlaneCurveZeroSet K₂).ncard ≤ (d+d+1)^4 and Finite; transport ∩ and
    finiteness by chartEquiv (chartEquiv_image_finite_iff; image commutes with ∩ on injective map);
    finite ⟹ encard = ncard (Set.encard_coe_eq_coe_finsetCard / Set.Finite.encard_eq_coe_toFinset_card).
  REUSE (ALL LANDED): irreducible_pair_intersection_bound (Bezout.lean:371),
    ChartBridge.chartEquiv_image_planeCurveZeroSet / _preimage_ / _finite_iff (ChartBridge.lean),
    Lemma A (above). Note (2d+1)^4 is degree-only — independent of M.
  Risk: LOW-MED. The only subtlety is the chartEquiv ∩-transport and the finite-encard cast.

FLAG FOR IMPLEMENTER: deduped-point-point-clause   [Proposition 3; MED risk; cover combinatorics]
  lemma deduped_pp (p₁ p₂ ∈ P) (hne : p₁ ≠ p₂) :
      (𝒵.filter (fun C => p₁ ∈ C ∧ p₂ ∈ C)).card ≤ M * d
  Proof: each deduped set C through both points is evalPlaneZeroSet of a kept factor of some
    original f_γ; that forces p₁,p₂ ∈ γ (factor locus ⊆ product locus). Bound by a SUM over the
    original curves through both points (≤ M by the ORIGINAL pp clause of h2dof₀) of the factor
    count per curve (≤ d, since deg ≤ d and each factor deg ≥ 1). This is a Finset.card-cover
    argument (Finset.card_le_card_of_subset into a biUnion; Finset.card_biUnion_le), NOT an
    injection into Γ₀ (distinct curves may share a deduped set). REUSE: the original
    TwoDegreesOfFreedom point–point clause on Γ₀; UniqueFactorizationMonoid.normalizedFactors
    cardinality vs totalDegree (a factor-count ≤ degree bound — check mathlib has
    Multiset.card normalizedFactors ≤ … or derive from degree additivity).
  Risk: MED. The cover direction is the trap; do NOT phrase as an injection.

FLAG FOR IMPLEMENTER: finite-locus incidence correction   [R-2; MED risk; the genuine residual]
  The deduped family Γ may contain irreducible carriers with FINITE real zero set (e.g. x²+y²,
    pderiv 1 ≠ 0 yet Z_R finite). Their P-incidences are bounded but are NOT counted by the
    sheet/good-interval route. Lemma: per such carrier, |{p ∈ P : p ∈ Z_R(C)}| ≤ |Z_R(C)| ≤
    (d+1)^5 (finite_singularities_of_irreducible_bound, since a finite zero set ⊆ singular set).
  This feeds the E1 bad-point accounting (edgeB_incidence_le_numEdges_add already absorbs a
    degree-only c d · |Γ| slack). REUSE (ALL LANDED): finite_zeroSet_subset_singularities
    (Bezout.lean:738), finite_singularities_of_irreducible_bound (Bezout.lean:1085),
    nonsingular_point_has_infinite_zeroSet (Bezout.lean:726). NO real Nullstellensatz needed.
  Risk: MED. This is the accounting the candidate underweights; it is real-AG-flavored but LANDED.

FLAG FOR IMPLEMENTER: assemble TwoDegreesOfFreedom (deduped) M'   [glue; LOW risk]
  M' := max ((2*d+1)^4) (M * d).
  TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M' from deduped_cc + deduped_pp
    by le_trans into the max. Then apply edgeB_crossingInput_2dof with hinj (by construction) +
    this h2dof. REUSE: edgeB_crossingInput_2dof (EdgeBComponentReduce.lean, LANDED).
  Risk: LOW.
```

**Minimal genuine residual obligation, stated unambiguously:** the missing real-determinacy lemma
`edgeB-zeroset-injectivity-real` is **avoided entirely** by deduplicating the image and choosing a
classical section (Proposition 4). The smallest *new* obligations are: (i) Lemma A (ring algebra,
LOW); (ii) the point–point cover count `M·d` (combinatorics, MED); (iii) the finite-locus
incidence correction R-2 (real-AG-flavored but dischargeable from **landed**
`finite_singularities_of_irreducible_bound`). **No not-in-mathlib real algebraic geometry lemma is
needed.**

## What next (ranked hardest-first)

1. **R-2 finite-locus incidence correction (MED, the real residual).** Establish that the
   *original* curve incidence count is bounded by the *deduped* count plus a degree-only
   finite-locus term. This is the step the candidate underweights; it is the only real-AG-flavored
   work, and it must be checked that the Edge-B E1 slack (`edgeB_incidence_le_numEdges_add`) truly
   absorbs the finite-locus points (carriers with finite `Z_ℝ` may stress the bad-point accounting
   differently than the design's good-x/bad-x split assumes). **Do this first** — if the E1
   accounting does not cover finite-locus carriers, the whole route needs the original→deduped
   incidence translation rebuilt, and that is the hardest part.

2. **`deduped-point-point-clause` (MED).** The `M·d` cover argument. The trap is phrasing it as an
   injection into `Γ₀` (wrong: deduped sets can be shared). Phrase as a sum/biUnion over the `≤ M`
   original curves through both points. Needs a `Multiset.card normalizedFactors ≤ deg` style fact;
   verify it exists in mathlib or derive from degree additivity.

3. **`deduped-curve-curve-clause` (LOW-MED).** Single Bézout application via Lemma A; the only
   friction is `chartEquiv` intersection-transport and the finite→encard cast. All leaves landed.

4. **Lemma A `not_associated_of_ne_evalPlaneZeroSet` (LOW).** Ring/eval algebra over the field ℝ.

5. **`dedup-section` + `hinj`-by-construction (LOW-MED).** Classical section bookkeeping; the math
   is a one-line left-inverse-implies-injective.

6. **Assembly into `TwoDegreesOfFreedom (deduped) M'` + apply `edgeB_crossingInput_2dof` (LOW).**
   Pure glue; `M' = max((2d+1)^4, M·d)`.

**Single hardest sub-brick:** R-2 (the finite-locus incidence correction) — it is the only step
that touches the original→deduped incidence translation and the one the candidate's framing
glosses. It is constructible from landed leaves, but its scope (does E1 absorb finite-locus
carriers?) must be confirmed before committing to the route.
