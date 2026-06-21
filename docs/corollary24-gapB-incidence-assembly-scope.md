# Gap B — §3 incidence-assembly scope (consumer side of `Corollary24Statement`)

## 0. What was investigated

The single `sorry` at
`lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/Bridge.lean:50`:

```lean
theorem positiveAuxiliaryIncidenceCardBound_of_corollary24
    (_h : PachSharir.Corollary24Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  sorry
```

This document decomposes that obligation ("Gap B") into named sub-lemmas, classifies each, and
identifies the genuine obstruction(s) versus the mechanical wiring. Scope is strictly the
**consumer** of `Corollary24Statement` (Bridge.lean and what feeds it). The separate workstream
that **proves** `Corollary24Statement` (Edge A = Theorem 2.3 ⇐ Szemerédi–Trotter; Edge B =
algebraic-curve decomposition; docs `corollary24-E1E2-assembly-design.md`,
`corollary24-edge-feasibility.md`) is out of scope and not analyzed here.

Everything labeled "exists in repo" cites `file:line` I read. Items labeled VERIFIED were read
from source; items labeled INFER are deductions about what the `sorry` must contain, drawn from
the paper text and the existing Lean surface.

The paper is `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex` (arXiv 2015-10-31);
section/line citations below refer to that file. The relevant region is §3 (`\section{Proof of
Theorem 1.1 and 1.2}`, tex line 464) and §4 (`\section{Proof of Lemma 3.2}`, tex line 834).

---

## 1. The two endpoints, verbatim

### 1.1 Hypothesis: `PachSharir.Corollary24Statement`
VERIFIED — `PachDeZeeuw/PachSharir/Theorem23.lean:93-99`:

```lean
def Corollary24Statement : Prop :=
  ∀ D e d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin D)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin D)))),
      (∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ
```

with (Theorem23.lean:38-66):

```lean
noncomputable def incidenceCount {α} (P : Finset α) (Γ : Finset (Set α)) : ℕ :=
  ((P ×ˢ Γ).filter (fun pγ => pγ.1 ∈ pγ.2)).card

def TwoDegreesOfFreedom {α} (P : Finset α) (Γ : Finset (Set α)) (M : ℕ) : Prop :=
  (∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → (γ₁ ∩ γ₂).encard ≤ (M : ℕ∞)) ∧
  (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
      (Γ.filter (fun γ => p₁ ∈ γ ∧ p₂ ∈ γ)).card ≤ M)

noncomputable def incidenceBoundTerm {α} (P : Finset α) (Γ : Finset (Set α)) : ℝ :=
  max (max ((P.card : ℝ) ^ ((2:ℝ)/3) * (Γ.card : ℝ) ^ ((2:ℝ)/3)) (P.card : ℝ)) (Γ.card : ℝ)

def IsAlgebraicCurveDefinedBy (D e d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin D))) : Prop :=
  ∃ fs : Fin e → MvPolynomial (Fin D) ℝ, (∀ i, (fs i).totalDegree ≤ d) ∧
    γ = {x | ∀ i, MvPolynomial.eval (fun k => x k) (fs i) = 0}
```

Two structural facts about this hypothesis (VERIFIED from the definitions):

- `Γ` is a `Finset (Set α)` — a finite set **of point-sets**. Distinct index pairs whose curves
  coincide as point sets collapse to one element of `Γ`. The paper instead keeps `|Γ| = m²`
  by "considering them as different curves" even when they coincide (tex 537-538). This is a real
  representational mismatch, addressed in §3.4 below.
- `M` is bound by the outer `∀ D e d M`, i.e. the constant `C` may depend on `M`. So instantiating
  `M = 16 d⁴` is legitimate: `C` is allowed to grow with it.

### 1.2 Conclusion: `PositiveAuxiliaryIncidenceCardBoundStatement`
VERIFIED — `PachDeZeeuw/IncidenceBound.lean:97-103`:

```lean
def PositiveAuxiliaryIncidenceCardBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
      0 < X.P₁.card * X.P₂.card →
        (auxIncidences X).card ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4
```

with the relevant pieces (VERIFIED, `AuxiliaryCurves.lean` / `Basic.lean`):

- `auxIncidences X : Finset (Point4 × (X.P₁ × X.P₁))` (`AuxiliaryCurves.lean:114-120`) — the set of
  `(z, (i,j))` with `z ∈ auxPointSet X` and `z ∈ auxCurve X i j`. The index runs over **all** of
  `X.P₁ × X.P₁` (no `Γ₀` removed). So `(auxIncidences X).card` is the full `|I(P, Γ)|` in paper
  notation, including the exceptional curves.
- `auxPointSet X = (X.P₂.product X.P₂).image auxPointOfPair` (`AuxiliaryCurves.lean:96-98`), the set
  `P` of paper tex 525-526, encoded into `Point4`.
- `auxCurve X i j` (`AuxiliaryCurves.lean:106-111`):

```lean
{z : Point4 |
   MvPolynomial.eval (fun k => auxFirstPair z k) (curveWitnessPoly₂ X) = 0 ∧
   MvPolynomial.eval (fun k => auxSecondPair z k) (curveWitnessPoly₂ X) = 0 ∧
   dist (i : Point2) (auxFirstPair z) ^ 2 = dist (j : Point2) (auxSecondPair z) ^ 2}
```

This is `C_ij` of tex eq (3.1)/`eq:defcij` (tex 516-521), but written with the **projection maps**
`auxFirstPair`/`auxSecondPair : Point4 → Point2` and a `dist²` term — **not** yet in the
`IsAlgebraicCurveDefinedBy 4 e d` polynomial normal form the corollary demands. Closing that gap is
sub-lemma GB-2 below.

`PreparedBipartiteInput d` (`Basic.lean:213-223`) carries `C₁,C₂ : Set Point2`, finite `P₁,P₂` on
them, irreducibility `hC₁,hC₂ : IsIrreducibleCurve d Cᵢ`, `notExceptional`, and the full
`Assumption31Data` bundle (`Basic.lean:148-173`) corresponding to the paper's Assumption 3.1 parts
1–6 (tex 492-505). VERIFIED: every normalization the paper invokes is present as a field.

### 1.3 What already connects them
VERIFIED — the downstream side is fully wired and `sorry`-free **below** the card bound:

- `bipartiteDistinctDistances_of_positiveCardBound` (`IncidenceBound.lean:173-177`) routes
  `PositiveAuxiliaryIncidenceCardBoundStatement` → Theorem 1.2 statement, through
  `positiveAuxiliaryIncidenceDecomposition_of_cardBound` (IncidenceBound.lean:109) →
  `auxiliaryIncidenceUpperBound_of_decomposition` (IncidenceBound.lean:139) →
  `bipartiteDistinctDistances` (`Theorem12.lean:54`).
- `irreducibleCurve_distinctDistances` (`Theorem11.lean:107`) routes Theorem 1.2 → Theorem 1.1.
- `auxIncidenceBridge` (`AuxiliaryCurves.lean:164`, PROVEN, `sorry`-free) gives the **lower**-bound
  direction `(equalDistanceQuadruples X).card ≤ (auxIncidences X).card`, i.e. it certifies that
  every equal-distance quadruple is an incidence (paper tex 778-780). This is the Elekes side and is
  already done. **Gap B is the opposite, upper-bound direction** and does not reuse this lemma.

So Bridge.lean's `sorry` is the **only** thing between an unconditional `Corollary24Statement` and an
unconditional Theorem 1.1 (`IncidenceAssembly/Bridge.lean:64-69` confirms `irreducibleCurve_
distinctDistances_of_corollary24` consumes exactly this `sorry` and nothing else).

---

## 2. Direct answers to the four questions

### Q1 — Does `Corollary24Statement`'s hypothesis shape fit the D=4 / C_ij / 2-DOF instantiation?

**Partly, and only after real work; not by a flat instantiation.** Three sub-points:

(a) **Curve normal form: YES in principle, but not as currently written.** `auxCurve` is cut out by
exactly `e = 3` equations (two `f₂∘projection` equations + one distance equation), matching
`IsAlgebraicCurveDefinedBy 4 3 d'` once each equation is exhibited as an `MvPolynomial (Fin 4) ℝ` of
bounded total degree. INFER: the natural degree bound is `d' = max d 2` (the two `f₂` pull-backs
have total degree ≤ d; the distance polynomial `(x−aᵢ)²+(y−bᵢ)²−(x'−aⱼ)²−(y'−bⱼ)²` has total degree
exactly 2). **So the corollary must be instantiated at `D = 4`, `e = 3`, `d := max d 2`, not `d := d`.**
The Bridge docstring's "`D = 4`" is right; it omits that `d` is bumped to `max d 2` and `e = 3`. This
is real and is sub-lemma GB-2.

(b) **The curve–curve half of `TwoDegreesOfFreedom`: the value `M = 16 d⁴` is correct but does NOT
hold for the whole family.** The paper is explicit (tex 539-543, 626): "We would like `P` and `Γ`
to form a system with two degrees of freedom, but this is false if some pairs of curves have a common
component." The flat reading in the Bridge docstring ("establish the two-degrees-of-freedom system
with multiplicity `M = 16 d⁴`, apply the corollary") **does not match the paper.** The 2-DOF property
is established only on the pieces of a partition (Lemma 3.4 / `lem:partition`, tex 632-687), and the
corollary is applied once per piece `(P_α, Γ_β)`. This is the core of the obstruction (GB-1).

(c) **The point–point half of `TwoDegreesOfFreedom`** ("any two points lie on ≤ M curves") is the
field `(Γ.filter (fun γ => p₁∈γ ∧ p₂∈γ)).card ≤ M`. The paper obtains it by the **dual**
construction `C̃_st` with roles of `C₁`,`C₂` swapped (tex 657-686) and a second graph-colouring on
`P`. So the point–point bound is **not** symmetric bookkeeping; it requires re-running the entire
Lemma-3.2/3.3/3.4 apparatus on the transposed family. INFER.

Conclusion for Q1: the hypotheses are **satisfiable**, but only after (i) a polynomial-presentation
lemma (GB-2), and (ii) the full partition apparatus (GB-1), and (iii) its dual (GB-1′). The corollary
cannot be applied to `(P, Γ)` directly.

### Q2 — Content of the "real max{·} → internal ℕ-cube" conversion: mechanical or hidden inequality?

**Mechanical, given a real bound of the paper's `max{·}` shape.** Two layers:

- **ℝ → ℕ cast + monotonicity.** `incidenceCount` is `ℕ` cast to `ℝ`; `auxIncidences.card` is `ℕ`.
  The corollary delivers `(I : ℝ) ≤ C · max{(mn)^{2/3} k^{2/3}, mn, k}` where `k = |Γ_β|`, `mn =
  |P_α|`. Pulling back to ℕ via `Nat.cast_le`, `Nat.le_floor`, etc., and cubing both sides
  (`Nat.pow_le_pow_left`) is standard `Nat.cast`/monotonicity bookkeeping. MATHLIB-mechanical.

- **Collapsing the `max` and the partition sum into `C' · (mn)^4`.** The shape fact needed is

  > under `m ≤ 2n`, `n ≤ 2m`, `m,n ≥ 1`: `max{(mn)^4, m^6, n^6} ≤ 4 (mn)^4`,

  which follows from `m^6 ≤ 4(mn)^4 ⇔ m² ≤ 4n^4` and `m² ≤ 4n² ≤ 4n^4` (since `n ≥ 1`), symmetrically
  for `n^6`. **EMPIRICALLY VERIFIED** for all `1 ≤ m,n < 80` (scratch run, `/tmp/gapb_arith.py`,
  0 counterexamples); the per-term argument above is a complete PROVEN derivation — the scratch run
  only rules out a typo. The partition contributes a **bounded number of terms** (`L² ≤ 5d⁴`, tex
  776), and the minor pieces `|I(P,Γ₀)|, |I(P₀,Γ)| ≤ 8d²mn` (Lemma 3.6, tex 706) are also `≤ const ·
  mn ≤ const · (mn)^4`. Summing a `d`-bounded number of `max{·}` terms and absorbing into one
  `(mn)^4` is `omega`/`nlinarith`-level once the per-piece real bounds are in hand.

So Q2 hides **no** real inequality beyond the elementary comparability fact above. The substance is
entirely upstream (producing the per-piece real bound), which is GB-1, not the conversion.

Caveat (INFER): this is only mechanical **after** the partition sum exists. The Bridge docstring
frames the conversion as the hard residue; that framing is inverted — the conversion is the easy
residue.

### Q3 — Single hardest sub-lemma

Yes. **Obstruction GB-1 — the partition into two-degrees-of-freedom pieces (paper Lemmas 3.2–3.4).**

GB-1 is hardest because the corollary is **not applicable to the whole family** (Q1b), and making it
applicable requires the paper's deepest content, none of which exists in the repo:

- **Lemma 3.2 / `lem:infinite`** (tex 551-555, proof deferred to all of §4, tex 834-1290 — roughly
  450 tex lines, four further lemmas `lem:samedist`, `lem:diffdist`, `lem:conic`, `lem:line` at tex
  864 / 932 / 1000 / 1095): there is a `Γ₀ ⊆ Γ`, `|Γ₀| ≤ 4dm`, such that no three curves in `Γ∖Γ₀`
  share infinite intersection. The proof uses curve symmetries, a bound on the number of
  translation/rotation symmetries of `C₂` (using Assumption 3.1 parts 4,5,6), and a case split on
  `deg C₂` (≥3 / conic / line). This is genuine algebraic geometry over ℂ.
- **Lemma 3.3 / `lem:intersect`** (tex 571-623): three claims — `C_ij` has complex dimension one;
  finite `|C_ij ∩ C_kl| ≤ 16 d⁴`; each `C_ij ∈ Γ∖Γ₀` has infinite intersection with ≤ `2d²` others.
  The `16 d⁴` claim is a **Milnor–Thom** application (four degree-≤d equations in ℝ⁴ ⇒ ≤ `(2d)^4`
  components ⇒ ≤ `16d⁴` points when finite). The other two claims use **complex** dimension theory
  and irreducible-component counting (Harris, Exercises 11.6, 5.9), which is the part that does *not*
  reduce to the existing real-`Bezout.lean`.
- **Lemma 3.4 / `lem:partition`** (tex 632-687): a graph-colouring argument — `G` on `Γ∖Γ₀` with edges
  = infinite intersection has max degree `≤ 2d² = L−1`, hence is `L`-colourable, giving the partition
  `Γ₁,…,Γ_L`; dually for `P` via `C̃_st`. This is the only **combinatorial** piece (greedy
  colouring of a bounded-degree graph); it is tractable in Lean *given* Lemmas 3.2–3.3 as inputs.

The hardness is concentrated in Lemma 3.2 (§4) and the complex-dimension claims of Lemma 3.3. These
rest on tools that the **pinned mathlib lacks** (semialgebraic geometry / complex variety dimension /
component counting); the repo already axiomatizes the closest available substitute, the Milnor–Thom
bound, as a statement-level `Prop` (`MilnorThom.MilnorThom22FiniteStatement`,
`MilnorThom.lean:67-71`, accepted as a named input per the file's Tier-B note, MilnorThom.lean:30-34).

Subordinate obstruction: **GB-1′ — the dual point–point partition.** Same machinery transposed
(`C̃_st`, graph `H` on `P∖P₀`). Not independently hard, but it doubles the surface and is a separate
formalization because `C̃_st` is a *different* curve family (built from `f₁`, `S₂`-indexed), so the
Lemma-3.2/3.3 inputs must be re-instantiated, not reused verbatim.

### Q4 — Ranked "what to attempt first"

Ordered so each item's dependencies precede it. "ROUTINE-WIRING" = mechanical given its deps;
"NEEDS-CONSTRUCTION" = a real but bounded mathematical construction; "MATHLIB-ABSENT" = needs a tool
not in the pinned mathlib (must be axiomatized as a named input or proved from scratch in a separate
workstream).

1. **GB-2 — `auxCurve` as `IsAlgebraicCurveDefinedBy 4 3 (max d 2)`** (NEEDS-CONSTRUCTION, no
   external deps). Build the three `MvPolynomial (Fin 4) ℝ` (two `f₂`-pullbacks along the coordinate
   projections `Fin 4 ⊇ {0,1}` and `{2,3}`, one explicit degree-2 distance polynomial), prove each
   `totalDegree ≤ max d 2`, and prove the set equality `auxCurve X i j = {z | ∀ i, eval … = 0}`. This
   is self-contained `MvPolynomial` plumbing (rename/embed variables; the repo already does the
   `curveWitnessPoly₂` extraction at `AuxiliaryCurves.lean:27-36`). Independent of GB-1, so it can go
   first and de-risks the interface. **Deps: none.** Largest mechanical risk: matching mathlib's
   `MvPolynomial.totalDegree` of a renamed/composed polynomial — spec this carefully (see FLAG below).

2. **GB-3 — `incidenceCount`/`Γ`-as-`Finset (Set Point4)` reconciliation** (NEEDS-CONSTRUCTION, small).
   Decide how the index-keyed `auxIncidences` (over `X.P₁ × X.P₁`) maps to the corollary's
   set-keyed `incidenceCount P Γ` (over `Finset (Set Point4)`). Because distinct `(i,j)` can give the
   same point set, the honest move (INFER) is: do **not** push the count through `incidenceCount`
   directly; instead apply the corollary per partition-piece to the *image* `Finset (Set Point4)` and
   carry a multiplicity/injectivity bound from index-pairs to sets, OR sum index-keyed incidences and
   bound them by set-keyed incidences times the max fibre size. This is the representational mismatch
   from §1.1; it is bounded but must be gotten exactly right. **Deps: GB-2** (need the curves as sets
   in the corollary's vocabulary first).

3. **GB-1c — graph-colouring partition (Lemma 3.4)** (NEEDS-CONSTRUCTION; combinatorial). Greedy
   `L`-colouring of a graph of max degree `≤ L−1` on `Γ∖Γ₀`, and the dual on `P∖P₀`. Mathlib has
   `SimpleGraph` chromatic-number / greedy-colouring infrastructure; this is the most "ordinary Lean"
   of the GB-1 pieces. **Deps: GB-1a, GB-1b (their *statements* suffice to state the edge relation;
   their *proofs* are needed for soundness).** Can be drafted against the statements of GB-1a/1b
   before those are proven.

4. **GB-1a — `16 d⁴` finite-intersection bound (Lemma 3.3, middle claim)** (MATHLIB-ABSENT at the
   Milnor–Thom step; otherwise NEEDS-CONSTRUCTION). Instantiate `MilnorThom22FiniteStatement` at
   `D = 4, d := max d 2` on the four-equation intersection `C_ij ∩ C_kl`, then convert `(2·max d 2)^4`
   to a `16 d⁴`-style bound. **Deps: GB-2** (the four equations as bounded-degree polynomials), plus
   the **named input** `MilnorThom22FiniteStatement`. If that input is accepted (per MilnorThom.lean's
   Tier-B note), GB-1a is mechanical; otherwise it is its own MATHLIB-ABSENT project.

5. **GB-1b — `≤ 2d²` infinite-intersection-degree bound + Lemma 3.2 (`Γ₀`, `|Γ₀| ≤ 4dm`)**
   (MATHLIB-ABSENT). The complex-dimension / shared-component counting (Lemma 3.3 first & last claims)
   and the whole of §4. This is the deepest sub-lemma and the bottleneck of GB-1. It needs complex
   variety dimension theory and bounded symmetry counts not present in the pinned mathlib. **Must be
   scoped as a named-input axiom or a separate workstream** mirroring how MilnorThom is handled.
   **Deps: GB-2** for the curve presentation; otherwise upstream of everything else in GB-1.

6. **GB-1′ — dual point–point partition** (mirrors GB-1a/1b/1c for `C̃_st`). **Deps: GB-1 analogues
   re-instantiated for `f₁`.**

7. **GB-4 — minor-incidence bounds (Lemma 3.6)** (NEEDS-CONSTRUCTION; uses real Bézout). `|I(P,Γ₀)|,
   |I(P₀,Γ)| ≤ 8 d² m n` via "≤ 2d circle intersections" (tex 706-717). The repo's
   `Bezout.lean:1315 bezout : BezoutFiniteIntersectionStatement` (PROVEN, constant `(d₁+d₂+1)^8`,
   not the sharp `2d`) can supply a *finite* bound but **not** the sharp `2d` constant — so GB-4 as
   stated needs either the sharp circle-intersection count (degree-2 sphere ∩ degree-d curve ≤ 2d) or
   a constant-relaxed restatement of the minor bound. INFER: the repo target only needs *some*
   `const(d)·mn`, so the crude Bézout constant is likely sufficient after re-checking the final
   arithmetic. **Deps: GB-2; optionally the existing `bezout`.**

8. **GB-5 — real `max{·}` → ℕ-cube conversion + partition sum** (ROUTINE-WIRING). The Q2 bookkeeping:
   per-piece corollary outputs + minor bounds, summed over `≤ 5d⁴` pieces, collapsed via
   `max{(mn)^4,m^6,n^6} ≤ 4(mn)^4` into `(auxIncidences X).card³ ≤ C·(mn)^4`. **Deps: GB-1, GB-1′,
   GB-3, GB-4 (all per-piece real bounds in hand).** This is the *last* step, not the hard one.

---

## 3. Classification table

| Sub-lemma | Paper ref | What it asserts | Class | Exists in repo? |
|---|---|---|---|---|
| GB-2 curve presentation | tex 514-523 (`eq:defcij`) | `auxCurve X i j ∈ IsAlgebraicCurveDefinedBy 4 3 (max d 2)` | NEEDS-CONSTRUCTION | No — `auxCurve` uses projections+`dist²`, not `MvPolynomial (Fin 4)` (`AuxiliaryCurves.lean:106-111`) |
| GB-3 `incidenceCount` reconciliation | tex 525-538 | index-keyed `auxIncidences` ↔ set-keyed `incidenceCount P Γ` | NEEDS-CONSTRUCTION | No — `Γ : Finset (Set α)` collapses coincident curves (`Theorem23.lean:38-48` vs index keys `AuxiliaryCurves.lean:114-120`) |
| GB-1a `16 d⁴` bound | Lemma 3.3 (tex 573-607) | finite `|C_ij∩C_kl| ≤ 16 d⁴` via Milnor–Thom in ℝ⁴ | MATHLIB-ABSENT (at MT step) | Statement-level input only: `MilnorThom22FiniteStatement` (`MilnorThom.lean:67-71`); not applied to `auxCurve` anywhere |
| GB-1b complex-dim + `Γ₀` | Lemma 3.2 (tex 551-555, §4) + Lemma 3.3 claims 1,3 | `dim_ℂ C_ij = 1`; `Γ₀`, `|Γ₀|≤4dm`; ≤ `2d²` infinite-intersection neighbours | MATHLIB-ABSENT | No. `Bezout.lean`/`ComponentSplit.lean` are real-plane only; `ComponentSplit` itself carries `sorry`s (`ComponentSplit.lean:33,35,37`) |
| GB-1c partition / colouring | Lemma 3.4 (tex 632-687) | `L`-colour `Γ∖Γ₀` (max degree `L−1`), dual on `P∖P₀` | NEEDS-CONSTRUCTION | No |
| GB-1′ dual partition | tex 657-686 | same as GB-1a/1b/1c for `C̃_st` | MATHLIB-ABSENT + NEEDS-CONSTRUCTION | No |
| GB-4 minor incidences | Lemma 3.6 (tex 704-720) | `|I(P,Γ₀)|, |I(P₀,Γ)| ≤ 8 d² m n` | NEEDS-CONSTRUCTION | Crude Bézout exists (`Bezout.lean:1315`, const `(d₁+d₂+1)^8`, not sharp `2d`) |
| GB-5 max→ℕ-cube + sum | tex 768-783 | collapse per-piece real bounds to `card³ ≤ C·(mn)^4` | ROUTINE-WIRING | No (this is the Bridge `sorry`'s final step) |

Note on "PROVEN" column: the only PROVEN items relevant here are the already-discharged downstream
wiring (§1.3) and `auxIncidenceBridge` (the lower-bound direction). None of GB-1…GB-5 is proven.

---

## 4. Structural assumptions made explicit

- **Finiteness of the target curve.** The paper assumes throughout that `C₁,C₂` are *infinite* (tex
  468), handling finite curves trivially by Milnor–Thom. The Lean `PreparedBipartiteInput` does **not**
  carry an infiniteness field; INFER the assembly must either add it or discharge the finite case
  separately. This is a (small) scope item not currently visible in the endpoints.
- **Finiteness of `C_ij ∩ C_kl`.** The `16 d⁴` bound (GB-1a) is conditional on the intersection being
  *finite* (`MilnorThom22FiniteStatement` has a `.Finite` hypothesis, `MilnorThom.lean:70`). The whole
  point of the partition (GB-1c) is to put curves with *infinite* intersection into different colour
  classes so that within a class all pairwise intersections are finite. So GB-1a and GB-1c are
  coupled: GB-1a's hypothesis is *supplied* by GB-1b's "no infinite intersection within a class."
- **`Assumption31Data` is genuinely used, not decorative.** Lemma 3.3's dimension-one claim uses
  Assumption 3.1.3 (tex 593-594); Lemma 3.2/§4 uses 3.1.4–3.1.6 (tex 858-862). The repo carries all
  six as fields (`Basic.lean:148-173`) and `assumption31Data_of_not_controlledDegenerate`
  (`Basic.lean:180`) discharges them vacuously when the curve is neither a line nor a circle — which
  is exactly the Theorem 1.1 situation (`Theorem11.lean:127-142` builds `X` this way). VERIFIED. So in
  the Theorem-1.1 reduction the Assumption-3.1 *conditional* clauses are vacuous; the substantive
  content of GB-1b is the non-line/non-circle symmetry-count and component-count argument, which is
  *not* vacuous.
- **The corollary's `C` may depend on `D,e,d,M`.** Required for `M = 16d⁴` and `d := max d 2` (the
  constant grows with `d`); this is allowed by the `∃ C` placement (Theorem23.lean:94). VERIFIED.

---

## 5. Where the Bridge docstring overstates simplicity

VERIFIED mismatch between `Bridge.lean:22-29` and the paper:

- Docstring: "establish the two-degrees-of-freedom system with multiplicity `M = 16 d⁴`, apply the
  corollary." Paper: the 2-DOF system does **not** exist on `(P, Γ)` (tex 539-543, 626); it exists
  only on partition pieces, requiring Lemmas 3.2–3.4 and their duals. The phrase "the … system"
  (singular) hides the partition.
- Docstring frames "convert the real `max{·}` bound into the internal cubed-integer statement" as the
  notable residue. Per Q2, that conversion is the *mechanical* tail (GB-5). The mass is GB-1/GB-1′,
  which the docstring compresses to one clause.

This is a documentation-accuracy observation, not a soundness defect: the `sorry` is honestly a
`sorry`, and the conditional theorem above it (`irreducibleCurve_distinctDistances_of_corollary24`,
Bridge.lean:64) correctly inherits it.

---

## 6. What next (ranked)

1. **GB-2** (curve presentation) and **GB-4** (minor incidences) first — both NEEDS-CONSTRUCTION with
   no MATHLIB-ABSENT dependency, both de-risk the interface, both independently checkable. GB-2 is the
   precondition for *every* later piece.
2. **GB-1c** (colouring) — draftable against the *statements* of GB-1a/1b; the only purely
   combinatorial piece; uses mathlib `SimpleGraph` colouring.
3. **GB-5** (the conversion) — can be written against *assumed* per-piece real bounds, validating the
   arithmetic end-to-end before the hard pieces land.
4. **GB-1a** — mechanical *iff* `MilnorThom22FiniteStatement` is accepted as a named input; otherwise
   promote to its own workstream.
5. **GB-1b** (the bottleneck) and **GB-1′** — scope as named-input axioms / separate workstream,
   mirroring the MilnorThom treatment. These are MATHLIB-ABSENT (complex variety dimension, bounded
   symmetry counts, shared-component counting) and are where the genuine obstruction lives.

The single hardest sub-lemma is **GB-1b** (Lemma 3.2 / §4 plus the complex-dimension claims of Lemma
3.3); the partition apparatus **GB-1** as a whole is the genuine obstruction. Everything else
(GB-2, GB-3, GB-4, GB-1c, GB-5) is mechanical or a bounded construction once GB-1's outputs exist.

---

## FLAG FOR IMPLEMENTER

- **GB-2 polynomial spec.** Compute, in `MvPolynomial (Fin 4) ℝ`:
  - `f₂⁽¹⁾ := rename (embed {0,1} ↪ Fin 4) (curveWitnessPoly₂ X)` so that
    `eval z f₂⁽¹⁾ = eval (auxFirstPair z) (curveWitnessPoly₂ X)`; symmetrically `f₂⁽²⁾` via `{2,3}`.
  - `g := (X 0 − a_i)² + (X 1 − b_i)² − (X 2 − a_j)² − (X 3 − b_j)²` with `(a_i,b_i)=(i:Point2) 0,1`,
    `(a_j,b_j)=(j:Point2) 0,1`.
  - Expected: `f₂⁽ᵏ⁾.totalDegree ≤ (curveWitnessPoly₂ X).totalDegree ≤ d`; `g.totalDegree = 2`
    (assuming `g ≠ 0`, which holds when the two centres differ — supplied by Assumption 3.1.2
    disjointness in the `i ≠ j` use, vacuous degenerate case otherwise). Verify the set equality
    `auxCurve X i j = {z | eval z f₂⁽¹⁾ = 0 ∧ eval z f₂⁽²⁾ = 0 ∧ eval z g = 0}` then repackage as
    `IsAlgebraicCurveDefinedBy 4 3 (max d 2)`. Verify the `rename` step's `totalDegree` behaviour
    against mathlib (`MvPolynomial.totalDegree_rename_le` or equivalent) — this is the one place the
    "mechanical" label could fail on a missing lemma.
- **GB-5 arithmetic.** The shape inequality `max{(mn)^4, m^6, n^6} ≤ 4·(mn)^4` under `m ≤ 2n, n ≤ 2m,
  m,n ≥ 1` was EMPIRICALLY VERIFIED over `1 ≤ m,n < 80` (scratch `/tmp/gapb_arith.py`, 0
  counterexamples) and has a complete elementary proof (`m^6 ≤ 4(mn)^4 ⇔ m² ≤ 4n^4`, and `m² ≤ 4n² ≤
  4n^4`). Implement as `nlinarith`/`omega` lemmas; no solver search needed. Final constant `C` in the
  conclusion is `≈ 4·B_d³` with `B_d = 6 d⁴ A_d` (paper tex 776) — recompute once the per-piece `A_d`
  constant from the corollary is fixed; do not hard-code the paper's `B_d` without re-deriving from
  the actual Lean constant returned by `Corollary24Statement`.
- **GB-1b / GB-1′ named-input decision.** These require complex variety dimension theory and bounded
  symmetry counts absent from the pinned mathlib (`MvPolynomial`/real-`Bezout` only). Recommend the
  orchestrator decide whether to axiomatize them as named `Prop` inputs (as `MilnorThom22*Statement`
  already is, `MilnorThom.lean:30-34,55-71`) or open a dedicated workstream. This decision gates the
  whole of Gap B and is not a wiring choice.
