# Corollary 24 — the incidence-translation lemma (R-2), complete paper proof

Author: math-professor (analysis)
Date: 2026-06-21
Toolchain context: `leanprover/lean4` per repo `lean-toolchain`; mathlib pinned in
`.lake/packages/mathlib`. Namespaces `PachDeZeeuw.Algebraic`, `PachSharir`.

## 0. What was investigated

The residual flagged as **R-2** in `docs/corollary24-hinj-discharge-analysis.md` §5.2:
the translation that bounds the incidence count of the **original** curve family by the
incidence count of the **deduplicated irreducible-component** family plus a degree-only
additive correction. The hinj-discharge doc establishes the dedup construction, Lemma A
(landed as `not_associated_of_ne_evalPlaneZeroSet`), and the curve–curve clause (landed as
`planeCurveZeroSet_inter_encard_le`) but does **not** write R-2 out. This document writes it
out, corrects the naive form (which is false without an explicit 2-DOF hypothesis), states the
exact Lean lemma in the `evalPlaneZeroSet` / `ℝ × ℝ` carrier consumed by
`edgeB_crossingInput_unsheared`, and gives a step-by-step proof skeleton citing landed leaves.

**Headline result (Theorem 1, §4).** With `K(d) = d · (d+1)^5`,
```
incidenceCount P (Γ.image evalPlaneZeroSet) ≤ incidenceCount P 𝒵 + K(d) · |Γ|.
```
PROVEN as a paper argument modulo one named, constructible sub-obligation
(`exists_pderiv_ne_zero_of_one_le_totalDegree`, §6, a char-0 mathlib fact) and the routine
Lean bookkeeping itemized in §7.

**The avoided lemma.** No step requires `edgeB-zeroset-injectivity-real` (that an irreducible
`f` with infinite `Z_ℝ(f)` is determined up to scalar by `Z_ℝ(f)`). §5 proves this explicitly:
the injection recovers the *owning original curve* from an infinite deduped set, which needs only
the **2-DOF curve–curve clause** (`Set.Infinite.encard_eq` + the landed
`planeCurveZeroSet_inter_encard_le`), never determinacy of the *polynomial*.

## 1. Definitions and notation (self-contained)

- `PlanePoly := MvPolynomial (Fin 2) ℝ` (`AlgebraicPrelim.lean:1516`). UFD; `ℝ` a field.
- `Point2 := EuclideanSpace ℝ (Fin 2)` (`AlgebraicPrelim.lean:22`).
- `evalPlane h : ℝ × ℝ → ℝ`, `xy ↦ MvPolynomial.eval (i ↦ if i = 0 then xy.1 else xy.2) h`
  (`Bezout.lean:451`). This is `MvPolynomial.eval (coords xy)`, a ring homomorphism in `h`.
- `evalPlaneZeroSet h := {xy : ℝ × ℝ | evalPlane h xy = 0}` (`LocalArc.lean:48`); membership iff
  `evalPlane h xy = 0` (`mem_evalPlaneZeroSet`, `LocalArc.lean:51`). **This is the carrier the
  target `edgeB_crossingInput_unsheared` and `Γ.image (…)` range over.**
- `PlaneCurveZeroSet p := {x : Point2 | MvPolynomial.eval (i ↦ x i) p = 0}`
  (`AlgebraicPrelim.lean:118`). The carrier the landed Bézout machinery is stated on.
- `chartEquiv : Point2 ≃ₜ ℝ × ℝ` (`ChartBridge.lean:56`), a homeomorphism, with
  `chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p` (`chartEquiv_image_planeCurveZeroSet`,
  `ChartBridge.lean:97`) and `chartEquiv ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p`
  (`chartEquiv_preimage_evalPlaneZeroSet`, `ChartBridge.lean:111`), and finiteness transport
  `chartEquiv_image_finite_iff` (`ChartBridge.lean:120`).
- `incidenceCount P Γ := ((P ×ˢ Γ).filter (fun pγ => pγ.1 ∈ pγ.2)).card` (`Theorem23.lean:38`).
  Double-counting form `incidenceCount P S = ∑ γ ∈ S, (P.filter (· ∈ γ)).card`
  (`incidenceCount_eq_sum`, `EdgeBE1.lean:416`). **Note: the sum is over the elements of `S` —
  i.e. over the *deduplicated set-image*, not over a multiset of polynomials.**
- `TwoDegreesOfFreedom P Γ M` (`Theorem23.lean:45`): curve–curve clause `(cc)`
  `∀ γ₁ ≠ γ₂ ∈ Γ, (γ₁ ∩ γ₂).encard ≤ (M : ℕ∞)`; point–point clause `(pp)`
  `∀ p₁ ≠ p₂ ∈ P, (Γ.filter (p₁ ∈ · ∧ p₂ ∈ ·)).card ≤ M`.

**Input data for R-2 (made precise).**

- `P : Finset (ℝ × ℝ)`.
- `Γ : Finset (Set (ℝ × ℝ))` — the **original** curve family, every `γ ∈ Γ` an
  `evalPlaneZeroSet f_γ` for a chosen `f_γ : PlanePoly` with `f_γ ≠ 0`, `totalDegree f_γ ≤ d`.
  (In the surface statement `Theorem23Statement`, `γ` is `IsPlaneAlgebraicCurveOfDegreeLE d`, i.e.
  `∃ f ≠ 0, totalDegree f ≤ d, γ = Z(f)` on `Point2`; transported through `chartEquiv` to
  `ℝ × ℝ`. The R-2 lemma is stated on the `ℝ × ℝ` side; the `chartEquiv` transport of the
  hypotheses is a separate, routine glue step, §7.)
- `𝒵 : Finset (Set (ℝ × ℝ)) := allFactors.image evalPlaneZeroSet`, where
  `allFactors : Finset PlanePoly` is the **deduplicated** (by polynomial, via `Finset.image`/
  `Multiset.toFinset`) set of normalized irreducible factors of all the `f_γ`, each factor
  satisfying `Irreducible` and `1 ≤ totalDegree ≤ d`.

**`TwoDegreesOfFreedom P Γ M` is assumed on the ORIGINAL family `Γ`** (curve–curve and
point–point both). R-2 does **not** consume the deduped family's 2-DOF; that is established
separately (`planeCurveZeroSet_inter_encard_le` for `cc`; the `M·d` cover count for `pp`,
hinj-discharge doc §4.2 Prop 3 / R-3). R-2 uses **only the curve–curve clause of the original
2-DOF**, and uses it solely through the unique-ownership fact (Proposition 2 below).

**Landed leaves cited (signatures read this session):**

- `not_associated_of_ne_evalPlaneZeroSet` (`EdgeBDedup.lean:39`): `evalPlaneZeroSet h ≠
  evalPlaneZeroSet k → ¬ Associated h k`. PROVEN, axiom-clean per file.
- `planeCurveZeroSet_inter_encard_le` (`EdgeBDedup.lean:83`): distinct irreducible degree-≤d
  `K₁ K₂` with `PlaneCurveZeroSet K₁ ≠ PlaneCurveZeroSet K₂` meet in encard `≤ (2d+1)^4`. (Not
  used by R-2 directly; the *infinite-locus uniqueness* uses the raw `encard ≤ M` clause.)
- `finite_zeroSet_subset_singularities` (`Bezout.lean:738`): `(PlaneCurveZeroSet h).Finite →
  PlaneCurveZeroSet h ⊆ SingularPointSet h`. **No partial-derivative hypothesis.**
- `finite_singularities_of_irreducible_bound` (`Bezout.lean:1085`): for `Irreducible h`,
  `totalDegree h ≤ d`, **`pderiv i h ≠ 0` for some `i`**: `(SingularPointSet h).Finite ∧
  (SingularPointSet h).ncard ≤ (d+1)^5`.
- `nonsingular_point_has_infinite_zeroSet` (`Bezout.lean:726`): `z ∈ PlaneCurveZeroSet h`,
  `∂₀h(z) ≠ 0 ∨ ∂₁h(z) ≠ 0` ⟹ `(PlaneCurveZeroSet h).Infinite`.
- `card_normalizedFactors_le_totalDegree` (`AlgebraicPrelim.lean:1456`):
  `(normalizedFactors p).card ≤ p.totalDegree`.
- `normalized_factor_irreducible` (`AlgebraicPrelim.lean:1394`),
  `normalized_factor_totalDegree_pos` (`AlgebraicPrelim.lean:1401`),
  `normalized_factor_degree_le` (`AlgebraicPrelim.lean:1479`).
- mathlib: `Set.Infinite.encard_eq : s.Infinite → s.encard = ⊤`; `Finset.card_le_card_of_injOn`;
  `Set.ncard_le_ncard`; `MvPolynomial.eval` is multiplicative (`map_mul`).

The Edge-B target this feeds:

- `edgeB_crossingInput_unsheared` (`EdgeBShearApply.lean:115`): for arbitrary
  `Γ₀ : Finset PlanePoly` with `∀ h ∈ Γ₀, Irreducible h ∧ totalDegree h ≤ d ∧ 1 ≤ totalDegree h`
  and the original-family 2-DOF clauses on `Γ₀`'s zero sets, bounds
  `incidenceCount P (Γ₀.image evalPlaneZeroSet) ≤ edgeBCrossingConst d M · (…)`. **The shear and
  the `pderiv 1 ≠ 0` arrangement happen INSIDE this leaf** (via `exists_good_shear`,
  `ShearExists.lean:110`), so R-2 — which produces the `Finset PlanePoly` `allFactors` — runs
  *before* the shear and never itself needs `pderiv 1 ≠ 0`. Only the finite-locus bound (§6) needs
  a nonzero partial, and that is a per-factor existential discharged independently.

## 2. The load-bearing fact: 2-DOF gives unique ownership of infinite deduped sets

This is the fact the task names as load-bearing, stated at the **zero-set level**, and it is what
makes the injection (§3) injective on the infinite branch.

> **Proposition 2 (unique ownership). Status: PROVEN** (modulo the elementary membership facts,
> all of which are landed).
>
> Let `S ∈ 𝒵` with `S` infinite (`S.Infinite`). Suppose `S ⊆ γ₁` and `S ⊆ γ₂` for
> `γ₁, γ₂ ∈ Γ` with `γ₁ ≠ γ₂`. Then this contradicts `TwoDegreesOfFreedom P Γ M` (`cc` clause).
> Consequently, among the original curves `γ ∈ Γ`, at most **one** contains `S`.
>
> *Proof.* From `S ⊆ γ₁` and `S ⊆ γ₂`, `S ⊆ γ₁ ∩ γ₂`, so `γ₁ ∩ γ₂` is infinite
> (`Set.Infinite.mono`). Hence `(γ₁ ∩ γ₂).encard = ⊤` (`Set.Infinite.encard_eq`). The `cc` clause
> gives `(γ₁ ∩ γ₂).encard ≤ (M : ℕ∞)`, and `(M : ℕ∞) < ⊤`, contradiction. ∎

No real algebraic geometry is used: the only inputs are `S ⊆ γᵢ`, `S.Infinite`, and the `encard`
clause. In particular `edgeB-zeroset-injectivity-real` is **not** invoked — we never recover the
*polynomial* `C` from `S`; we recover only the *owning original curve* `γ`, and only because the
2-DOF intersection bound forbids two distinct curves from sharing an infinite set.

This is exactly the hypothesis my finite-model stress test (§8) identified as necessary and
sufficient: with unique ownership of infinite loci enforced, the translation inequality holds
across 145,703 finite worlds; without it, explicit counterexamples appear (a curve `γ₁ ⊋ S` and a
curve `γ₂ = S` both owning an infinite `S` overcount the LHS). **The naive form of R-2 without
the 2-DOF hypothesis is FALSE** — this is the correction to the expected argument: the hypothesis
must be threaded explicitly.

## 3. The injection

### 3.1 Sectioning the original family

`incidenceCount P (Γ.image evalPlaneZeroSet)` sums over the **distinct** sets in
`Γ.image evalPlaneZeroSet`. Wait — in the R-2 statement `Γ` is already a `Finset (Set (ℝ × ℝ))`
of curves, so `Γ.image evalPlaneZeroSet` is not literally what appears. The precise LHS is
`incidenceCount P Γ` where each `γ ∈ Γ` carries a chosen defining polynomial. To make the
injection well-typed we work with the polynomial layer:

- Let `polyOf : Γ → PlanePoly` be a chosen section assigning to each original curve `γ ∈ Γ` a
  defining polynomial `f_γ` with `f_γ ≠ 0`, `totalDegree f_γ ≤ d`, `evalPlaneZeroSet f_γ = γ`
  (exists by the `IsPlaneAlgebraicCurveOfDegreeLE`/`ℝ × ℝ`-transported hypothesis; classical
  `choose`). Because `γ` is itself the zero set, the section is just "remember the witness."

Then `incidenceCount P Γ = ∑_{γ ∈ Γ} |{p ∈ P : p ∈ γ}|` and `γ = evalPlaneZeroSet f_γ`, so the
incidence pairs are `{(p, γ) : γ ∈ Γ, p ∈ P, p ∈ evalPlaneZeroSet f_γ}`.

### 3.2 Per-incidence component selection

Fix an incidence `(p, γ)`, `p ∈ evalPlaneZeroSet f_γ`. Since
`f_γ = ∏ C ∈ normalizedFactors f_γ, C` (up to a unit; `prod_normalizedFactors`) and
`evalPlane (∏ C) p = ∏ (evalPlane C p)` (ring-hom multiplicativity of
`MvPolynomial.eval (coords p)`, i.e. `map_prod`), we have
`evalPlane f_γ p = 0 ⟹ ∃ C ∈ normalizedFactors f_γ, evalPlane C p = 0`
(`Finset.prod_eq_zero_iff` / `Multiset.prod_eq_zero_iff`). This is the landed
`zeroSet_subset_normalizedFactor_union` (`AlgebraicPrelim.lean:1487`), transported to `ℝ × ℝ`:
**`p` lies on the zero set of some irreducible factor `C` of `f_γ`.** Each such `C` is in
`allFactors` (it is a normalized irreducible factor of some `f_γ`), so `evalPlaneZeroSet C ∈ 𝒵`.

Partition the factors of `f_γ` by whether their real zero set is infinite:

- **Infinite branch.** If *some* factor `C` of `f_γ` with `p ∈ evalPlaneZeroSet C` has
  `(evalPlaneZeroSet C).Infinite`: choose the canonical such `C` (see §3.3 for well-definedness)
  and map `(p, γ) ↦ (p, evalPlaneZeroSet C)`. Target is a **deduped incidence**: a pair
  `(p, S)` with `S ∈ 𝒵`, `p ∈ S` (since `p ∈ evalPlaneZeroSet C = S`).
- **Finite branch.** Otherwise every factor `C` of `f_γ` with `p ∈ evalPlaneZeroSet C` has
  `(evalPlaneZeroSet C)` finite. Then `p` is a **special point** of `γ`: `p ∈
  evalPlaneZeroSet f_γ` and `p` lies on no infinite factor of `f_γ`. Tag `(p, γ)` as a
  **finite-locus exception** `(γ, p)`.

The map `Φ : {original incidences} → {deduped incidences} ⊔ {finite-locus exceptions}` is
`Φ(p, γ) = inl (p, evalPlaneZeroSet C)` on the infinite branch, `inr (γ, p)` on the finite branch.

### 3.3 (a) Well-definedness of the canonical infinite-component choice

When `p` lies on **multiple** infinite factors `C, C'` of one `f_γ` (e.g. a node of `γ` where two
infinite branches cross), the target on the infinite branch must be a single, well-defined deduped
set. Two correct resolutions, either suffices:

1. **Choose by a fixed linear order.** Equip `normalizedFactors f_γ` (a finite multiset, hence a
   finite set after `toFinset`) with `Finset.min'`/`Classical` choice on the nonempty subset
   `{C : C factor of f_γ, p ∈ Z(C), Z(C) infinite}`. The choice depends only on `(p, γ)`, so `Φ`
   is a function. **Injectivity (§3.4) does not depend on which infinite factor is chosen** — it
   uses only that the chosen `S = Z(C)` is infinite and `S ⊆ γ` (which holds for *every* factor's
   zero set, `Z(C) ⊆ Z(f_γ) = γ`). PROVEN that the choice set is nonempty on the infinite branch
   (by branch hypothesis) and that any choice lands in `𝒵` with `p ∈ S` and `S` infinite.
2. **Choose by the set, not the polynomial.** Map instead to the canonical element of `𝒵`: among
   `{S ∈ 𝒵 : p ∈ S, S infinite, S ⊆ γ}` (nonempty on the infinite branch), pick by `Finset`
   choice. This is even cleaner for injectivity because the target lives natively in `𝒵`.

Either way `Φ` is total and well-defined; resolution (2) is recommended for the Lean port (the
target is already a `𝒵`-element, no polynomial round-trip).

### 3.4 (b) Injectivity

> **Proposition 3 (injectivity of `Φ`). Status: PROVEN** modulo Proposition 2 and the elementary
> facts above.
>
> `Φ` is injective.

*Proof.* `inl` and `inr` images are disjoint by the sum-type tag, so it suffices to show `Φ` is
injective on each branch.

**Infinite branch (injective).** Suppose `Φ(p₁, γ₁) = inl (p, S)` and `Φ(p₂, γ₂) = inl (p, S)`
with the same target. Then `p₁ = p = p₂` (the first coordinate is preserved by `Φ`). It remains to
show `γ₁ = γ₂`. By construction `S` is infinite, `S ∈ 𝒵`, and `S ⊆ γ₁` and `S ⊆ γ₂` (the chosen
factor `C` has `Z(C) = S ⊆ Z(f_{γᵢ}) = γᵢ`). By **Proposition 2** (unique ownership), at most one
original curve contains the infinite set `S`; hence `γ₁ = γ₂`. So `(p₁, γ₁) = (p₂, γ₂)`. ∎(infinite)

**Finite branch (cannot be folded in; bounded separately).** Here `Φ(p, γ) = inr (γ, p)`, which
records the *original curve* `γ` itself, so the finite branch is **injective by construction** (the
target literally is `(γ, p)`). The reason the finite branch must be a *separate* tag rather than
routed into the deduped incidences is the failure of injectivity that *would* occur if we mapped
`(p, γ) ↦ (p, Z(C))` for a finite factor `C`:

> **Obstruction (finite-locus sharing). Status: EMPIRICALLY VERIFIED (explicit witness, §8).**
> Distinct original curves `γ₁ ≠ γ₂` can share a finite-locus irreducible factor with the *same*
> zero set. Concretely `f₁ = (x²+y²)·A`, `f₂ = (x²+y²)·B` with `A ≠ B` irreducible of infinite
> distinct loci. Then `Z(x²+y²) = {(0,0)}` is finite and contained in both `γ₁` and `γ₂`. The
> point `p = (0,0)` is on a finite factor of both. If routed into the deduped target, both
> `(p, γ₁)` and `(p, γ₂)` map to `(p, {(0,0)})` — a **collision**. So the finite branch is not
> injective into the deduped incidences and must be tagged by the original curve and **counted
> separately**.

Note Proposition 2 does **not** rescue the finite branch: it forbids shared *infinite* sets only;
`{(0,0)}` is finite, and 2-DOF permits two original curves to meet in finitely many points. ∎

### 3.5 The cardinality inequality from the injection

`Φ` injective gives
```
|{original incidences}| ≤ |{deduped incidences}| + |{finite-locus exceptions}|.
```
- `|{original incidences}| = incidenceCount P Γ` (= LHS; §3.1).
- `|{deduped incidences}| = |{(p, S) : S ∈ 𝒵, p ∈ P, p ∈ S}| = incidenceCount P 𝒵` (the target's
  `inl` part is a *subset* of all deduped incidences, so `|inl image| ≤ incidenceCount P 𝒵`).
- `|{finite-locus exceptions}| = ∑_{γ ∈ Γ} |{p ∈ P : p special for γ}| ≤ ∑_{γ ∈ Γ} K(d) =
  K(d) · |Γ|` (the per-curve special-point bound, §4/§6).

Hence `incidenceCount P Γ ≤ incidenceCount P 𝒵 + K(d) · |Γ|`. ∎

**Why the injection (not a per-curve refinement).** `incidenceCount P Γ` and `incidenceCount P 𝒵`
are both sums over **distinct sets** (image collapse on both sides). A naive "each original curve's
incidences refine into its components' incidences" miscounts because the same deduped set can be
shared across original curves on *both* branches. The injection routes each *original incidence
pair* to a *distinct* target, which is what the `Finset.card_le_card_of_injOn` argument needs; the
counting is correct precisely because the infinite-branch targets are made distinct by unique
ownership and the finite-branch targets carry the original-curve tag.

## 4. The per-curve finite-locus bound and `K(d)`

> **Proposition 4 (per-curve special-point bound). Status: PROVEN** modulo
> `exists_pderiv_ne_zero_of_one_le_totalDegree` (§6) and the membership facts.
>
> For each `γ ∈ Γ` with defining `f_γ` (`f_γ ≠ 0`, `totalDegree f_γ ≤ d`), the set of special
> points of `γ` has `≤ d · (d+1)^5` elements. Hence `K(d) = d · (d+1)^5`.

*Proof.* A special point `p` of `γ` lies on `evalPlaneZeroSet f_γ` and on **no infinite** factor of
`f_γ`. By §3.2, `p` lies on some factor `C`; since `p` is on no infinite factor, the witnessing `C`
has `(evalPlaneZeroSet C)` **finite**. So the special points are contained in
`⋃_{C finite factor of f_γ} evalPlaneZeroSet C`.

Bound each finite factor's locus. Fix a factor `C` with `(evalPlaneZeroSet C)` finite. Then
`(PlaneCurveZeroSet C)` is finite (`chartEquiv_image_finite_iff`, transporting finiteness across the
homeomorphism). `C` is `Irreducible` with `1 ≤ totalDegree C ≤ d` (`normalized_factor_irreducible`,
`normalized_factor_totalDegree_pos`, `normalized_factor_degree_le`). By
`exists_pderiv_ne_zero_of_one_le_totalDegree` (§6), `∃ i, pderiv i C ≠ 0`. Then
`finite_singularities_of_irreducible_bound C (irr) (deg ≤ d) (pderiv i ≠ 0)` gives
`(SingularPointSet C).ncard ≤ (d+1)^5`, and `finite_zeroSet_subset_singularities C (finite locus)`
gives `PlaneCurveZeroSet C ⊆ SingularPointSet C`, so
`(PlaneCurveZeroSet C).ncard ≤ (SingularPointSet C).ncard ≤ (d+1)^5` (`Set.ncard_le_ncard`,
finiteness from the singular bound). Transport back: `(evalPlaneZeroSet C).ncard ≤ (d+1)^5`
(`chartEquiv` is a bijection; `Set.ncard_image_of_injective`).

`f_γ` has `≤ d` factors: `card (normalizedFactors f_γ) ≤ totalDegree f_γ ≤ d`
(`card_normalizedFactors_le_totalDegree`). The special points lie in the union of `≤ d` finite
loci, each of `ncard ≤ (d+1)^5`, so
`|special points of γ| ≤ d · (d+1)^5` (`Set.ncard_biUnion_le` / `Finset.card_biUnion_le` plus the
per-set bound; the union is finite as a finite union of finite sets). ∎

**Tightness of `K(d)`.** The argument gives exactly `d · (d+1)^5`. It is not claimed minimal: it is
the product of the landed factor-count bound (`≤ d`) and the landed singular-set bound
(`≤ (d+1)^5`). A point on multiple finite factors is counted once per containing factor in the
`biUnion` sum, so the true count is `≤ |⋃ finite loci|`, possibly smaller; `d · (d+1)^5` is a safe
upper bound and is degree-only, which is all the assembly needs. This **matches the task's target
`K(d) = d · (d+1)^5`.**

> **(c), restated and discharged.** "`p` on only finite components ⟹ `p` in this special set" is
> immediate from the definition of *special point* (§3.2): the finite branch fires exactly when
> every factor through `p` has finite locus, which is the membership in `⋃ finite loci` used above.
> "Each finite component's locus has `≤ (d+1)^5` points; `≤ d` components ⟹ `≤ d·(d+1)^5`" is
> Proposition 4. The only non-immediate input is the nonzero partial, isolated as §6.

## 5. (d) Cardinality facts and the avoided real-determinacy lemma

> **(d) Is `|𝒵| ≤ d·|Γ|` needed inside R-2? Status: PROVEN — NO.**
>
> R-2 as stated (the incidence inequality) needs **no** cardinality bound on `𝒵`. The RHS term is
> `incidenceCount P 𝒵`, not `|𝒵|`. The bound `|𝒵| ≤ d · |Γ|` (each `f_γ` has `≤ d` factors;
> dedup only shrinks) is needed by the **final assembly** to convert the `edgeB_crossingInput_
> unsheared` output (stated in `|allFactors| = |𝒵|`) back into a bound in `|Γ|`, via
> `|allFactors| ≤ d · |Γ|` so `|allFactors|^{2/3} ≤ d^{2/3} |Γ|^{2/3}` and `|allFactors| ≤ d|Γ|`.
> That is a separate glue lemma (FLAG, §7), **not part of R-2**.

> **Confirmation that no step needs `edgeB-zeroset-injectivity-real`. Status: PROVEN.**
>
> Inventory of every step that touches "infinite real zero set":
> - §2 Proposition 2 (unique ownership): uses `Set.Infinite.encard_eq` + the 2-DOF `cc` clause.
>   Recovers the *owning curve* `γ`, never the polynomial. **No determinacy.**
> - §3.2 component selection: uses `zeroSet_subset_normalizedFactor_union` (factor locus ⊆ product
>   locus) and the branch split infinite/finite. Both are membership/finiteness facts. **No
>   determinacy.**
> - §3.4 infinite-branch injectivity: from `(p, S)` with `S` infinite recovers `γ` by Proposition
>   2. Crucially it does **not** recover `C` (the factor); distinct factors with the same infinite
>   locus would be fine — they collapse to the same `S ∈ 𝒵`, and `S` still has a unique owning
>   `γ`. **This is exactly the step where the determinacy lemma would have been needed at the
>   polynomial level, and it is sidestepped.**
> - §4 finite bound: uses `finite_singularities_of_irreducible_bound`,
>   `finite_zeroSet_subset_singularities`, `nonsingular_point_has_infinite_zeroSet` (via §6) — all
>   landed real-AG, none a Nullstellensatz/real-radical/determinacy statement.
>
> **`edgeB-zeroset-injectivity-real` is genuinely avoided.** No step requires that an irreducible
> `f` with infinite `Z_ℝ(f)` is determined up to scalar by `Z_ℝ(f)`. If a future refactor tried to
> make the injection recover the *factor polynomial* `C` from `S`, it would reintroduce the
> determinacy obligation; the proof above is written specifically to recover only the *curve* `γ`,
> which the 2-DOF intersection bound supplies without determinacy.

## 6. The one named sub-obligation: nonzero partial of a positive-degree factor

> **Sub-obligation. Status: CONSTRUCTIBLE from char-0 mathlib (NEEDS-MATHLIB-DERIVATION, not a
> ready-made lemma).**
>
> ```
> lemma exists_pderiv_ne_zero_of_one_le_totalDegree (C : PlanePoly) (hC : 1 ≤ C.totalDegree) :
>     ∃ i : Fin 2, MvPolynomial.pderiv i C ≠ 0
> ```

*Why it is needed.* `finite_singularities_of_irreducible_bound` (`Bezout.lean:1085`) requires
`pderiv i C ≠ 0` for some `i`. A finite-locus factor `C` is irreducible with `1 ≤ totalDegree`,
but the irreducibility/degree fields of `EdgeBCurve` are **not yet** in play at the R-2 layer (R-2
runs pre-shear, on `allFactors : Finset PlanePoly`), so the nonzero partial must be produced here.

*Why it is true and constructible.* Over a field of characteristic 0, a polynomial with **all**
partial derivatives zero is a constant (`totalDegree = 0`). Contrapositive of `hC`. The mathlib
pieces are present (verified by grep over `.lake/packages/mathlib` this session):
- `MvPolynomial.totalDegree_eq_zero_iff_eq_C` (`Degrees.lean:590`): `totalDegree p = 0 ↔ p = C a`.
- `MvPolynomial.pderiv_C` (a constant's partial is 0) and `pderiv_monomial_single`
  (`PDeriv.lean:107`): differentiating the single-variable monomial `X i ^ n` gives `n • X i^(n-1)`,
  nonzero for `n ≥ 1` in char 0.
- `MvPolynomial.totalDegree_eq_zero_iff_eq_C` together with: if `pderiv i C = 0` for all `i`, then
  `C` has no variable appearing with positive degree (the leading monomial in any present variable
  would differentiate to nonzero in char 0), forcing `C = C a`, i.e. `totalDegree C = 0`.

A clean derivation: if `∀ i, pderiv i C = 0`, then `C ∈ ⋂ ker(pderiv i)`. In char 0 over a field,
`ker(pderiv i) = {p : i ∉ p.vars}`-supported, and `⋂_i {i ∉ vars} = (vars = ∅) = {C = C a}`
(`MvPolynomial.totalDegree_eq_zero_iff_eq_C`, `vars`-emptiness). The char-0 input is that `pderiv i
(X i ^ n · m) ≠ 0` for `n ≥ 1` (the coefficient `n` is a unit), i.e. no cancellation; this is
`pderiv_monomial_single` + `CharZero`/`Nat.cast_ne_zero`.

**This is the only mathlib-side derivation R-2 requires beyond the landed leaves.** It is a standard
char-0 fact; estimated as a short Lean lemma (a few lines via `vars` + `pderiv_monomial_single`).
Mark **NEEDS-MATHLIB-DERIVATION** (constructible; not a missing deep theorem). It is **emphatically
not** `edgeB-zeroset-injectivity-real`.

*Alternative that avoids §6 entirely (FLAG, lower priority).* If the assembly is restructured so
R-2 runs **after** the shear — i.e. on the *sheared* `allFactors` whose carriers are full
`EdgeBCurve d` with the `pderiv 1 ≠ 0` field baked in (`EdgeBMultigraph.lean:64`) — then the
nonzero partial is the structure field `H.2.2.2` and §6 is discharged for free. This is a design
choice for the orchestrator: either (i) keep R-2 pre-shear and prove §6, or (ii) reorder so R-2 is
post-shear and read off `pderiv 1 ≠ 0`. Option (ii) couples R-2 to the shear; option (i) keeps R-2
independent at the cost of the §6 lemma. **Recommend (i)** — §6 is cheap and keeps R-2 a clean
polynomial-layer statement matching `edgeB_crossingInput_unsheared`'s `Finset PlanePoly` input.

## 7. Exact Lean lemma statement and proof skeleton

Carrier: `ℝ × ℝ`, curves `evalPlaneZeroSet h`, matching `edgeB_crossingInput_unsheared`.

### 7.1 The R-2 lemma (polynomial-indexed form, recommended)

State the original family by its defining polynomials, so the LHS is in the same
`Γ₀.image evalPlaneZeroSet` shape as the target leaf. Let `origPolys : Finset PlanePoly` be the
chosen defining polynomials of the original curves (`Γ = origPolys.image evalPlaneZeroSet`), and
`allFactors : Finset PlanePoly` the deduplicated irreducible factors.

```lean
/-- **R-2 — incidence translation.** The incidence count of the original curve family is
bounded by the incidence count of the deduplicated irreducible-component family plus a
degree-only additive correction `d·(d+1)^5` per original curve. -/
lemma incidence_translation
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (origPolys : Finset PlanePoly)
    (hne     : ∀ f ∈ origPolys, f ≠ 0)
    (hdeg    : ∀ f ∈ origPolys, f.totalDegree ≤ d)
    (allFactors : Finset PlanePoly)
    (hAF_irr : ∀ C ∈ allFactors, Irreducible C)
    (hAF_pos : ∀ C ∈ allFactors, 1 ≤ C.totalDegree)
    (hAF_deg : ∀ C ∈ allFactors, C.totalDegree ≤ d)
    -- allFactors contains every normalized irreducible factor of every f ∈ origPolys:
    (hAF_cov : ∀ f ∈ origPolys, ∀ C ∈ UniqueFactorizationMonoid.normalizedFactors f,
                 C ∈ allFactors)
    -- original-family 2-DOF curve–curve clause (the ONLY 2-DOF hypothesis R-2 uses):
    (hcc : ∀ f₁ ∈ origPolys, ∀ f₂ ∈ origPolys,
             evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ →
             (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard ≤ (M : ℕ∞)) :
    PachSharir.incidenceCount P (origPolys.image evalPlaneZeroSet)
      ≤ PachSharir.incidenceCount P (allFactors.image evalPlaneZeroSet)
        + d * (d + 1) ^ 5 * origPolys.card := by
  sorry
```

Notes on the statement:
- The `hcc` hypothesis is phrased on **distinct zero sets** (`evalPlaneZeroSet f₁ ≠
  evalPlaneZeroSet f₂`), which is what the original-family 2-DOF supplies after collapsing
  `origPolys` to distinct curves. (If two `f`'s define the same curve they are the same element of
  `origPolys.image evalPlaneZeroSet` and contribute once.) `Set.Infinite.encard_eq` then makes the
  unique-ownership argument fire.
- `+ d*(d+1)^5 * origPolys.card` is `K(d)·|Γ|` with `K(d) = d·(d+1)^5`. Note
  `origPolys.card ≥ |origPolys.image evalPlaneZeroSet| = |Γ|`, so this is `≥ K(d)·|Γ|`; the
  inequality is therefore safe whether `|Γ|` or `|origPolys|` is used on the RHS. For the cleanest
  downstream use, `origPolys.card` can be replaced by `(origPolys.image evalPlaneZeroSet).card` at
  the cost of a `Finset.card_image_le` step.

### 7.2 Proof skeleton (step-by-step, leaves named)

1. **Reduce both sides to sums** via `incidenceCount_eq_sum` (`EdgeBE1.lean:416`). LHS becomes
   `∑_{S ∈ origPolys.image evalPlaneZeroSet} |P.filter (· ∈ S)|`; RHS-main becomes
   `∑_{T ∈ allFactors.image evalPlaneZeroSet} |P.filter (· ∈ T)|`. **[PROVEN, landed]**

2. **Set up the injection on incidence pairs.** Work with the `Finset`
   `LHSpairs := (P ×ˢ (origPolys.image evalPlaneZeroSet)).filter (·.1 ∈ ·.2)` (this is exactly the
   `card` defining `incidenceCount`, `Theorem23.lean:38`). For each such pair `(p, S)`, choose a
   defining `f` with `evalPlaneZeroSet f = S` and `f ∈ origPolys` (classical `choose` over the
   `Finset.mem_image` witness). **[PROVEN, classical choice; LOW]**

3. **Component selection.** From `p ∈ S = evalPlaneZeroSet f` and `hAF_cov`, obtain `C ∈
   allFactors` with `p ∈ evalPlaneZeroSet C`, via `zeroSet_subset_normalizedFactor_union`
   (`AlgebraicPrelim.lean:1487`) transported to `ℝ × ℝ` (the `evalPlane`-product = product-of-evals
   fact, `map_prod`/`map_mul`). **[PROVEN, landed + routine transport]**

4. **Branch + canonical choice (§3.3).** Decide `(evalPlaneZeroSet C).Infinite` for the chosen
   `C`. Use `Set.Infinite` decidability classically. On the infinite branch, pick the canonical
   `S' ∈ 𝒵` with `p ∈ S'`, `S'` infinite, `S' ⊆ S` (resolution (2), §3.3; `Finset` choice). Target
   `Sum.inl (p, S')`. On the finite branch, target `Sum.inr (S, p)`. **[PROVEN, choice
   bookkeeping; LOW-MED]**

5. **Infinite-branch injectivity (Proposition 2/3).** Given two pairs with equal `inl (p, S')`:
   first coordinates agree; for the curves, use that `S' ⊆ S₁` and `S' ⊆ S₂` with `S'` infinite
   forces `S₁ = S₂` (distinct ⟹ `S₁ ∩ S₂ ⊇ S'` infinite ⟹ `encard = ⊤` by
   `Set.Infinite.encard_eq`, contradicting `hcc`). Hence the original pairs agree.
   **[PROVEN modulo §2; the crux; MED]**

6. **Disjointness + finite-branch injectivity.** `inl`/`inr` disjoint by `Sum` tag; `inr (S, p)`
   records `S` and `p`, injective by construction. Conclude `Φ` injective:
   `Function.Injective Φ` ⟹ `LHSpairs.card ≤ (target).card` via `Finset.card_le_card_of_injOn`.
   **[PROVEN; LOW]**

7. **Bound the target card.**
   `(target).card = |inl image| + |inr image|`.
   - `|inl image| ≤ incidenceCount P (allFactors.image evalPlaneZeroSet)`: the `inl` targets are
     deduped incidence pairs `(p, S')`, `S' ∈ 𝒵`, `p ∈ S'`; they form a subset of all such pairs,
     whose count is `incidenceCount P 𝒵`. `Finset.card_le_card` on the subset. **[PROVEN; LOW]**
   - `|inr image| = ∑_{S ∈ Γ} |{p : (S,p) tagged}| ≤ K(d) · |Γ|` by Proposition 4. **[PROVEN
     modulo §6; MED]**

8. **Per-curve finite bound (Proposition 4 / §4).** For each original curve, the special points
   lie in `⋃_{C finite factor} evalPlaneZeroSet C`; each finite factor's locus has `ncard ≤
   (d+1)^5` via `chartEquiv_image_finite_iff` (`ChartBridge.lean:120`) +
   `finite_zeroSet_subset_singularities` (`Bezout.lean:738`) +
   `finite_singularities_of_irreducible_bound` (`Bezout.lean:1085`) (precondition `pderiv i C ≠ 0`
   from `exists_pderiv_ne_zero_of_one_le_totalDegree`, §6) +
   `Set.ncard_le_ncard` + `Set.ncard_image_of_injective`. The factor count is `≤ d`
   (`card_normalizedFactors_le_totalDegree`, `AlgebraicPrelim.lean:1456`). `biUnion` bound:
   `Set.ncard_biUnion_le` / `Finset.card_biUnion_le`. **[PROVEN modulo §6; MED]**

9. **Assemble** the inequalities from 1, 6, 7, 8 by `le_trans` / `add_le_add`. **[PROVEN; LOW]**

### 7.3 Glue to the final corollary (NOT part of R-2; listed for completeness)

```
FLAG FOR IMPLEMENTER: build-allFactors + hAF_cov     [glue; LOW-MED]
  allFactors := (origPolys.biUnion (fun f => (normalizedFactors f).toFinset)).
  hAF_irr/_pos/_deg from normalized_factor_irreducible / _totalDegree_pos / _degree_le
    (AlgebraicPrelim.lean:1394/1401/1479) with hdeg.  hAF_cov is membership in the biUnion.

FLAG FOR IMPLEMENTER: |allFactors| ≤ d · |origPolys|   [glue; for the assembly, NOT R-2; LOW]
  allFactors.card ≤ ∑_{f} card (normalizedFactors f).toFinset ≤ ∑_{f} d = d·|origPolys|,
  via Finset.card_biUnion_le and card_normalizedFactors_le_totalDegree.

FLAG FOR IMPLEMENTER: chartEquiv-transport of Theorem23 hypotheses to ℝ×ℝ   [glue; LOW-MED]
  IsPlaneAlgebraicCurveOfDegreeLE (Point2) ⟹ evalPlaneZeroSet form (ℝ×ℝ), and the 2-DOF
  cc clause on Point2 ⟹ the hcc above, via chartEquiv_image_planeCurveZeroSet
  (ChartBridge.lean:97) and image-commutes-with-∩.

FLAG FOR IMPLEMENTER: final apply of edgeB_crossingInput_unsheared    [glue; LOW]
  Feed allFactors as Γ₀ with hAF_irr/_deg/_pos and the deduped-family 2-DOF (cc:
  planeCurveZeroSet_inter_encard_le, EdgeBDedup.lean:83 transported; pp: the M·d cover,
  hinj-discharge doc R-3).  Combine with R-2 (incidence_translation) by le_trans and absorb
  |allFactors| ≤ d·|origPolys| into incidenceBoundTerm.
```

## 8. Empirical verification of the counting skeleton (scope explicit)

To stress the combinatorial core independent of the real-AG content, I ran a finite abstract
model: components carry abstract point-membership and an infinite/finite flag; original curves are
unions of components; `incidenceCount` is counted as pairs `(p, S)` over distinct set-images on
both sides; special points are points on a curve lying on no infinite component of a representative.

- **Naive form (no 2-DOF hypothesis): FALSE.** With `rhs = incidenceCount P 𝒵 + (max per-curve
  special count)·|Γ|`, a counterexample appears at 3 components / 4 points / 3 curves: two distinct
  original zero sets share an infinite locus (a curve `⊋ S` and a curve `= S`), overcounting the
  LHS. EMPIRICALLY VERIFIED (single explicit witness; `/tmp/inj_check.py`).
- **Corrected form (unique ownership of infinite loci enforced): HOLDS.** With the §2 hypothesis
  enforced (each infinite-locus value contained in `≤ 1` distinct original zero set) and
  `rhs = incidenceCount P 𝒵 + ∑_{S ∈ Γ} special(S)`, the inequality `LHS ≤ rhs` held across
  **145,703** finite worlds (scope: ≤6 points, ≤6 components, ≤5 curves; deterministic seed).
  EMPIRICALLY VERIFIED (`/tmp/inj_check4.py`). This is a finite-range check; it does **not** promote
  the result to PROVEN — the PROVEN status comes from §2–§4. It confirms (i) the hypothesis of §2 is
  the right one, and (ii) the `∑ special(S) ≤ K·|Γ|` step is the correct accounting.
- **Finite-branch non-injectivity witness.** The explicit `(x²+y²)·A`, `(x²+y²)·B` configuration
  confirms distinct curves share a finite locus while unique-ownership of infinite loci holds, so
  the finite branch genuinely cannot be folded into the injection (`/tmp/inj_check5.py`).
  EMPIRICALLY VERIFIED.

These are scratch checks on throwaway inputs; the mathematical content is §2–§4. No scratch result
is treated as a proof.

## 9. What uses finiteness / structural assumptions (stated explicitly)

- **Finiteness of `P`, `origPolys`, `allFactors`** — throughout; `𝒵` is a finite image, the
  injection is between finite sets, `incidenceCount` is a `Finset.card`.
- **`ℝ[x,y]` is a UFD** — for `normalizedFactors`, factor count, factor irreducibility (mathlib).
- **`ℝ` is a field of characteristic 0** — for §6 (positive degree ⟹ nonzero partial). The field
  hypothesis is used; the **characteristic-0** hypothesis is used **only** in §6.
- **`chartEquiv` is a homeomorphism (bijection + continuity)** — for transporting finiteness and
  `ncard` between `Point2` (Bézout's carrier) and `ℝ × ℝ` (the target carrier) in §4.
- **2-DOF curve–curve clause on the ORIGINAL family** — used **only** in §2 (unique ownership),
  and there only via `Set.Infinite.encard_eq` + `(M : ℕ∞) < ⊤`. The point–point clause of the
  original 2-DOF is **not** used by R-2 (it feeds the *deduped* family's `pp` clause, R-3, in the
  assembly). The **deduped** family's 2-DOF is not used by R-2 at all.
- **NOT used by R-2**: real Nullstellensatz, real radical, polynomial-level zero-set injectivity
  (`edgeB-zeroset-injectivity-real`), decidability of real set equality (classical only),
  `|𝒵| ≤ d·|Γ|` (that is assembly-only, §5(d)).

## 10. What next (ranked)

1. **§6 `exists_pderiv_ne_zero_of_one_le_totalDegree` (NEEDS-MATHLIB-DERIVATION, the single new
   leaf).** The only mathlib-side derivation R-2 needs beyond landed material. Char-0 fact, short
   Lean lemma via `MvPolynomial.totalDegree_eq_zero_iff_eq_C` (`Degrees.lean:590`) +
   `pderiv_monomial_single` (`PDeriv.lean:107`) + `CharZero`. **Do this first** — every other R-2
   step is landed or routine, and §4 cannot close without it. If it proves awkward, fall back to
   assembly option (ii) (§6 alternative): run R-2 post-shear and read `pderiv 1 ≠ 0` off the
   `EdgeBCurve` field — but that couples R-2 to the shear and is less clean.

2. **§3.4 infinite-branch injectivity (the crux; MED).** Proposition 2 + the recovery of the owning
   curve from the infinite deduped set. The trap is recovering the *factor* instead of the *curve*
   — recover only the curve (use `S ⊆ γᵢ`, not `S = Z(C)` for a specific `C`), which is what keeps
   `edgeB-zeroset-injectivity-real` out. Landed: `Set.Infinite.encard_eq`, the `hcc` clause.

3. **§4 / §8 per-curve finite bound assembly (MED).** Compose the landed leaves
   (`finite_singularities_of_irreducible_bound`, `finite_zeroSet_subset_singularities`,
   `card_normalizedFactors_le_totalDegree`, `chartEquiv` transport) into `≤ d·(d+1)^5` per curve.
   Friction: the `biUnion` ncard bound and the `chartEquiv` finiteness/ncard transport.

4. **§3.1–§3.3, §7.2 steps 2–7 (injection plumbing; LOW-MED).** Classical sections, the `Sum`-type
   target, `Finset.card_le_card_of_injOn`. Math is routine; the bookkeeping is the cost.

5. **Assembly glue (§7.3; LOW-MED), not part of R-2.** Build `allFactors`, the `|allFactors| ≤
   d·|origPolys|` bound, the `chartEquiv` transport of the `Theorem23` hypotheses, and the final
   `edgeB_crossingInput_unsheared` application.

**Single hardest sub-brick:** §6 (`exists_pderiv_ne_zero_of_one_le_totalDegree`). It is the only
genuinely *new* obligation (everything else is landed leaves or injection bookkeeping), it is the
gate on the finite-locus bound, and it is constructible from char-0 mathlib — **not**
`edgeB-zeroset-injectivity-real`, which remains avoided.
