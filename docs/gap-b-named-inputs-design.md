# Gap B — the minimal, faithful, TRUE named `Prop` input surface to axiomatize

## 0. What was investigated

The single `sorry` on the erdos-98 spine, `Bridge.lean:69`:

```lean
theorem positiveAuxiliaryIncidenceCardBound_of_theorem23
    (_h : PachSharir.Theorem23Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement := sorry
```

Task: produce the **minimal set of named `Prop` inputs** (in `MilnorThom.lean`
house style — `def … : Prop`, threaded as hypotheses) such that the rest of the
§3 assembly is provable from {those inputs} ∪ {`Theorem23Statement`,
`MilnorThom22FiniteStatement`, in-repo lemmas}, with each named input being a
faithful and TRUE transcription of a published Pach–de Zeeuw lemma absent from
pinned mathlib v4.30.

This document supersedes the *decomposition* docs (`gap-b-assembly-skeleton.md`,
`corollary24-gapB-incidence-assembly-scope.md`) on the question of **what to
axiomatize**. Those docs enumerated nodes; this one fixes the axiom boundary and
the exact `Prop` signatures, and adjudicates the one place where the naive
transcription is FALSE-or-open (GB-PROJ-curve).

Everything labelled VERIFIED was read from the cited `file:line` this session.
Claims are tagged PROVEN / CONJECTURED / HEURISTIC / EMPIRICALLY VERIFIED per the
project rigor standard.

### 0.1 The headline finding (read this first)

The `_of_theorem23` re-target consumes the **planar** bound
`Theorem23Statement` (`D=2`). The auxiliary curves `auxCurve X i j ⊆ ℝ⁴`
(`AuxiliaryCurves.lean:106`) live in `ℝ⁴`. **The paper never projects to ℝ²** — it
applies Corollary 2.4 *in ℝ⁴ directly* (Lemma 3.5 / `lem:mainincidences`, tex 694:
"Applying Corollary \ref{cor:incidences} now gives an incidence bound", with
`cor:incidences` being the `ℝ^D` Corollary 2.4). The projection ℝ⁴→ℝ² is an
artifact introduced *solely* by re-targeting from `Corollary24Statement` to
`Theorem23Statement`.

That projection step (the GB-PROJ-curve node) is the binding design decision, and
it is **not** cleanly axiomatizable as a single recognizable published lemma:

1. It needs the image `π '' (auxCurve X i j)` to be *exactly* the real zero set
   of a **nonzero** plane polynomial of degree bounded by a function of `d`
   (`IsPlaneAlgebraicCurveOfDegreeLE` demands set-equality `γ = {f=0}`, `f ≠ 0`).
   The faithful version of this is **two** mathlib-absent ingredients —
   strengthened-A1 (a rank-2, secant-cone-avoiding generic projection) and
   A2_canonical (the canonical eliminant with a uniform degree bound) — neither of
   which is a single named Pach–de Zeeuw lemma. They are the *internal machinery*
   of the proof of Corollary 2.4, adjudicated PROVEN-mathematically but
   mathlib-absent in `docs/corollary24-A4a-adjudication.md` §6.
2. It is gated on `auxCurve` having **complex dimension one**, which is itself a
   mathlib-absent fact (paper Lemma 3.3 first claim, complex variety dimension
   theory).
3. In the degenerate branch (`auxCurve` finite/empty) the only available degree
   bound for the defining polynomial is `2k` where `k` is the image point count
   (EMPIRICALLY VERIFIED below), which is **not** bounded by a function of `d`
   alone — so even the "easy" case does not give a clean `someDegree d` bound.

**Recommendation (ranked in §7):** axiomatize at the **ℝ⁴ published-lemma
boundary**, not the ℝ²-projection boundary. Two named inputs suffice for the whole
partition + incidence-application core, each a faithful transcription of a single
Pach–de Zeeuw lemma:

- **GB-IN-1** = Lemma 3.4 (`lem:partition`) **at the ℝ⁴ level**: the 2-DOF
  partition of `(auxPointSet, auxCurve-family)` exists, with the dual already
  folded in (the paper's Lemma 3.4 proves both halves in one lemma).
- **GB-IN-2** = the ℝ⁴ incidence bound for the `auxCurve` family (Lemma 3.5
  content = Corollary 2.4 *specialized to the auxCurve family*), keyed on the
  index pairs, so that no projection and no `IsPlaneAlgebraicCurveOfDegreeLE`
  obligation is incurred.

Under this boundary `Theorem23Statement` is **not** the consumer of Gap B —
GB-IN-2 is. That is a problem for the current spine, which routes through
`theorem23_of_crossingLemma`. §6 gives the honest reconciliation: either (Option
A) keep `_of_theorem23` and pay the full GB-PROJ-curve price as a **third** named
input GB-IN-3 (the generic-projection-to-plane-curve fact, stated faithfully with
its complex-dim-1 hypothesis), or (Option B) re-target the *bridge* back to a
narrow ℝ⁴ corollary input and drop the planar detour. Both are stated; the
trade-off is made explicit. The minimal *number* of mathlib-absent axioms is the
same either way (the projection does not remove an axiom — it adds one), so the
decision is about faithfulness and provability, not axiom count.

---

## 1. Definitions and notation (self-contained)

All from source, VERIFIED:

- `Point2 := EuclideanSpace ℝ (Fin 2)`, `Point4 := EuclideanSpace ℝ (Fin 4)`
  (`Basic.lean:25`, `CurveInterface`).
- `X : PreparedBipartiteInput d` (`Basic.lean:213`): fields `C₁ C₂ : Set Point2`,
  `P₁ P₂ : Finset Point2`, `hC₁ hC₂ : IsIrreducibleCurve d Cᵢ`, `hP₁ hP₂`
  (point sets on curves), `notExceptional`, `assumption31 : Assumption31Data …`.
- `auxCurve X i j : Set Point4` (`AuxiliaryCurves.lean:106`), `i j : X.P₁`: the
  set of `z` with `f₂(auxFirstPair z)=0 ∧ f₂(auxSecondPair z)=0 ∧
  dist(i, auxFirstPair z)² = dist(j, auxSecondPair z)²`, where `f₂ =
  curveWitnessPoly₂ X` and `auxFirstPair/auxSecondPair : Point4 → Point2` are the
  two coordinate projections (`AuxiliaryCurves.lean:75,80`).
- `auxPointSet X : Finset Point4 = (X.P₂.product X.P₂).image auxPointOfPair`
  (`AuxiliaryCurves.lean:96`); `auxPointOfPair` injective
  (`AuxiliaryCurves.lean:62`).
- `auxIncidences X : Finset (Point4 × (X.P₁ × X.P₁))` (`AuxiliaryCurves.lean:114`):
  pairs `(z,(i,j))` with `z ∈ auxPointSet X ∧ z ∈ auxCurve X i j`. Index runs over
  **all** of `X.P₁ × X.P₁`.
- `PachSharir.incidenceCount P Γ`, `TwoDegreesOfFreedom P Γ M`,
  `incidenceBoundTerm P Γ`, `IsPlaneAlgebraicCurveOfDegreeLE d γ`,
  `IsAlgebraicCurveDefinedBy D e d γ`, `Theorem23Statement`, `Corollary24Statement`
  (`Theorem23.lean:38–99`).
- `MilnorThom.MilnorThom22FiniteStatement` (`MilnorThom.lean:67`),
  `MilnorThom.realZeroSet` (`MilnorThom.lean:44`).
- `PositiveAuxiliaryIncidenceCardBoundStatement` (`IncidenceBound.lean:97`): the
  conclusion — `∀ d, ∃ C>0, ∀ X, (compatibility) → (auxIncidences X).card³ ≤
  C·(|P₁|·|P₂|)⁴`.

In-repo PROVEN (do **not** axiomatize):
`GapBSupport.incidence_pigeonhole` (`GapBSupport.lean:137`),
`auxIncidences_card_le_product` (`IncidenceBound.lean:36`),
`exists_rank2_projection_injOn` (`GenericProjection.lean:210`),
`bezout` (`Bezout.lean:1315`),
the downstream wiring `bipartiteDistinctDistances_of_positiveCardBound`
(`IncidenceBound.lean:173`), `auxIncidenceBridge` (`AuxiliaryCurves.lean:164`),
mathlib `SimpleGraph.Colorable`.

`theorem23_of_crossingLemma : CrossingLemmaMultigraphStatement →
Theorem23Statement` is PROVEN sorry-free (`EdgeBCorollaryLift.lean:951`); the
spine routes crossing-lemma → `Theorem23Statement`. **`Corollary24Statement` is
no longer consumed anywhere on the spine** (VERIFIED: `grep` finds it only in
docstrings, `Bridge.lean:40` and `EdgeBE1.lean:56`).

---

## 2. The faithful named inputs

### 2.1 GB-IN-1 — the 2-DOF partition (paper Lemma 3.4 / `lem:partition`, tex 632–687)

This is the deepest published lemma and the one that *must* be axiomatized: its
proof rests on Lemma 3.2 (`lem:infinite`, deferred to all of §4, tex 834+) and
the complex-dimension claims of Lemma 3.3 (`lem:intersect`, tex 571–623), all
requiring complex variety dimension theory + bounded symmetry/component counts
absent from pinned mathlib.

**Granularity decision (task Q on Lemma 3.2/3.3 vs 3.4).** Axiomatize at the
**Lemma 3.4 level** (the partition exists), *not* the finer Lemma 3.2 + 3.3 level.
Rationale:

- Lemma 3.4 is the single statement that delivers exactly the object the
  incidence application needs: a finite colouring of the index set into classes,
  each forming a 2-DOF(M=16d⁴) system, plus the small exceptional sets
  `Γ₀, P₀`. The colouring → 2-DOF step *inside* Lemma 3.4 (greedy colouring of a
  max-degree-≤2d² graph) is the only part that is mathlib-present
  (`SimpleGraph.Colorable`), but it is **not separable** from the inputs: to run
  the greedy colouring you need Lemma 3.3's "≤ 2d² infinite-intersection
  neighbours" bound, which is itself mathlib-absent. So splitting at 3.2+3.3 buys
  you a provable colouring step bolted onto **two** mathlib-absent inputs (the
  `Γ₀` existence and the degree bound) instead of **one** (the partition). It
  *increases* the axiom surface and fragments a single published lemma into a
  named input that is no longer a recognizable Pach–de Zeeuw lemma. Reject.
- The "each `auxCurve` has complex dimension one" fact (Lemma 3.3 claim 1) is
  **internal** to the proof of Lemma 3.4 in the paper and need **not** appear as a
  hypothesis to GB-IN-1: the partition conclusion does not mention dimension.
  Keeping it internal is faithful (the published Lemma 3.4 statement carries no
  dimension hypothesis) and minimizes the surface. So the answer to the task's
  sub-question is: **dimension-one is internal to the input, not a hypothesis.**

The faithful `Prop`, in `MilnorThom.lean` house style. It quantifies the
multiplicity at the paper's `M = 16d⁴` and the colour count at `L = 2d²+1`, and
carries the exceptional-set cardinality bounds `|Γ₀| ≤ 4dm`, `|P₀| ≤ 4dn`
verbatim. Both halves of Lemma 3.4 (the `Γ`-partition via graph `G` on the
`auxCurve` family, and the dual `P`-partition via the transposed `C̃` family,
graph `H`) are folded into one statement, exactly as the paper's single Lemma 3.4
does:

```lean
/--
**Lemma 3.4 (Pach–de Zeeuw, `lem:partition`).**

For a prepared bipartite input, the index square `X.P₁ × X.P₁` (the curve family,
`|Γ| = m²` with coincident curves kept distinct by index) admits a finite
colouring `cΓ : (X.P₁ × X.P₁) → Fin (2*d^2+1+1)` and the point square
`X.P₂ × X.P₂` (encoded into `auxPointSet`) a finite colouring
`cP : (X.P₂ × X.P₂) → Fin (2*d^2+1+1)`, together with exceptional index sets
`Γ₀ ⊆ X.P₁ × X.P₁`, `P₀ ⊆ X.P₂ × X.P₂`, such that:

* `Γ₀.card ≤ 4 * d * X.P₁.card`  and  `P₀.card ≤ 4 * d * X.P₂.card`  (tex 638);
* colour `0` is exactly the exceptional class on each side;
* for every non-exceptional colour pair `(β, α)` with `β ≠ 0`, `α ≠ 0`, the
  point set `Pα := auxPointSet` restricted to `cP = α` and the curve family
  `Γβ := auxCurve` restricted to `cΓ = β` form a two-degrees-of-freedom system
  with multiplicity `M = 16 * d^4`, in the sense of `PachSharir`'s ambient-ℝ⁴
  intersection clause and point–point clause.

This is the partition that makes the incidence bound applicable; it is the deepest
content of §3–§4 (complex dimension one of `C_ij`, the `Γ₀` of Lemma 3.2, the
≤ 2d² infinite-intersection degree bound of Lemma 3.3, and the greedy colouring),
absent from pinned Mathlib and threaded as a named input under the project's
Tier-B program (mirroring `MilnorThom22FiniteStatement`).
-/
def Lemma34PartitionStatement : Prop :=
  ∀ d : ℕ, ∀ X : PachDeZeeuw.PreparedBipartiteInput d,
    ∃ (Γ₀ : Finset (X.P₁ × X.P₁)) (P₀ : Finset (X.P₂ × X.P₂))
      (cΓ : (X.P₁ × X.P₁) → Fin (2 * d ^ 2 + 2))
      (cP : (X.P₂ × X.P₂) → Fin (2 * d ^ 2 + 2)),
      Γ₀.card ≤ 4 * d * X.P₁.card ∧
      P₀.card ≤ 4 * d * X.P₂.card ∧
      (∀ ij, ij ∈ Γ₀ ↔ cΓ ij = 0) ∧
      (∀ st, st ∈ P₀ ↔ cP st = 0) ∧
      (∀ (β α : Fin (2 * d ^ 2 + 2)), β ≠ 0 → α ≠ 0 →
        -- curve–curve clause (ambient ℝ⁴): two distinct same-class curves meet
        -- in ≤ 16 d⁴ points
        (∀ ij kl : X.P₁ × X.P₁, cΓ ij = β → cΓ kl = β →
            PachDeZeeuw.auxCurve X ij.1 ij.2 ≠ PachDeZeeuw.auxCurve X kl.1 kl.2 →
            (PachDeZeeuw.auxCurve X ij.1 ij.2 ∩
              PachDeZeeuw.auxCurve X kl.1 kl.2).encard ≤ (16 * d ^ 4 : ℕ∞)) ∧
        -- point–point clause: two distinct same-class points lie on ≤ 16 d⁴
        -- curves of the WHOLE family
        (∀ st uv : X.P₂ × X.P₂, cP st = α → cP uv = α →
            auxPointOfPair' X st ≠ auxPointOfPair' X uv →
            (Finset.univ.filter (fun ij : X.P₁ × X.P₁ =>
                auxPointOfPair' X st ∈ PachDeZeeuw.auxCurve X ij.1 ij.2 ∧
                auxPointOfPair' X uv ∈ PachDeZeeuw.auxCurve X ij.1 ij.2)).card
              ≤ 16 * d ^ 4))
```

where `auxPointOfPair' X st := auxPointOfPair ((st.1 : Point2 from X.P₂),
(st.2 : Point2))` is the obvious encoding of a `P₂×P₂` index pair into `Point4`
(it factors through the existing private `auxPointOfPair`; the named input would
either be stated with an exposed wrapper or directly over `auxPointSet`
membership — a presentation choice, see FLAG). The two `card ≤ 16 d⁴` clauses are
**exactly** the `M = 16d⁴` of Lemma 3.4 in the two roles of `TwoDegreesOfFreedom`.

**Faithfulness argument.** The paper's Lemma 3.4 asserts precisely: partitions of
`P` into `P₀…P_L` and `Γ` into `Γ₀…Γ_L` with `|Γ₀| ≤ 4dm`, `|P₀| ≤ 4dn`, and for
all `1 ≤ α,β ≤ L` the pair `(P_α, Γ_β)` is a 2-DOF system with `M = 16d⁴`. The
`Prop` above encodes the partitions as colourings `cΓ, cP` with `Fin (2d²+2)`
labels (`L = 2d²+1` non-exceptional classes + class `0` for the exceptional set,
matching `L+1` parts `P₀,…,P_L`), the cardinality bounds verbatim, and the 2-DOF
property as the two `≤ 16d⁴` clauses — the ambient-ℝ⁴ curve–curve clause and the
point–point clause that `PachSharir.TwoDegreesOfFreedom` is defined by
(`Theorem23.lean:45`). **No strengthening:** the conclusion is exactly the
paper's; the curve–curve clause is stated for the *ambient* ℝ⁴ intersection
(matching both the paper and `TwoDegreesOfFreedom`'s `(γ₁∩γ₂).encard`), and the
point–point clause counts curves of the whole index family (matching the paper's
"at most 16d⁴ curves from Γ passing through any two points", tex 685).

**TRUTH argument.** This is the published Lemma 3.4, correctly transcribed. Its
proof in the paper (tex 632–687) is:
(i) take `Γ₀` from Lemma 3.2 (`|Γ₀| ≤ 4dm`, no three remaining curves share
infinite intersection);
(ii) build graph `G` on `Γ\Γ₀` with edges = infinite intersection; by Lemma 3.3
its max degree is ≤ 2d², so `χ(G) ≤ L = 2d²+1`, giving the colour classes; same-
class curves have finite intersection, hence ≤ 16d⁴ points by Lemma 3.3 (the
Milnor–Thom bound);
(iii) dually for `P` via the transposed family `C̃_st`.
Every step is a published, proven step of Pach–de Zeeuw. The only reason it is an
**axiom** rather than a Lean theorem is the mathlib-absence of complex variety
dimension theory (Lemma 3.3 claim 1, "`dim_ℂ C_ij = 1`"), the bounded symmetry
counts of §4 (Lemma 3.2), and the irreducible-component count (Lemma 3.3 claim 3).
*Status of the transcription: PROVEN-faithful, TRUE (it is the published lemma).*

**Caveat I will not paper over (HEURISTIC → must be checked at implementation).**
The cleanest faithful statement keeps the point–point clause counting over the
*whole* family `Finset.univ : X.P₁ × X.P₁` (as the paper's "≤ 16d⁴ curves from Γ"
does). But `TwoDegreesOfFreedom Pα Γβ M` (the object GB-APPLY feeds to
`Theorem23Statement`) needs the point–point clause **restricted to the curve
class `Γβ`**, i.e. `(Γβ.filter …).card ≤ M`. Restricting the count to a subfamily
only *decreases* it, so "≤ M over the whole family" ⇒ "≤ M over `Γβ`" — the
implication is monotone and PROVEN-trivial. Therefore the whole-family form above
is **at least as strong** as what GB-APPLY needs, and the derivation goes through.
(Stating it over `Γβ` directly would be equally faithful and slightly weaker; the
whole-family form is preferred because it is the paper's literal wording and is
the form Lemma 3.6 also consumes.)

### 2.2 GB-IN-2 — the ℝ⁴ incidence bound for the auxCurve family (Lemma 3.5 content)

The published Lemma 3.5 (`lem:mainincidences`, tex 694) is: for each class pair
`(α,β)`, `|I(P_α, Γ_β)| ≤ A_d · max{m^{4/3}n^{4/3}, m², n²}`. The paper obtains it
by **applying Corollary 2.4 in ℝ⁴** to `(P_α, Γ_β)` (the `C_ij` are real algebraic
curves in ℝ⁴ defined by `e=3` polynomials of degree ≤ d, with the 2-DOF property
from Lemma 3.4). There are two honest ways to name this:

**(2.2a) The narrow form — incidence bound for the auxCurve family, index-keyed.**
This avoids `incidenceCount`'s `Finset (Set _)` collapse entirely by counting over
index pairs, and avoids `IsPlaneAlgebraicCurveOfDegreeLE` by staying in ℝ⁴:

```lean
/--
**Lemma 3.5 (Pach–de Zeeuw, `lem:mainincidences`), specialized to the auxiliary
family.**

For each subfamily `S ⊆ X.P₁ × X.P₁` and point subset `T ⊆ auxPointSet X` that
form a two-degrees-of-freedom system with multiplicity `M` in ℝ⁴ (ambient
intersection clause + point–point clause), the number of index-keyed incidences
between `T` and the curves indexed by `S` obeys the Pach–Sharir bound. The curves
`auxCurve X i j` are real algebraic curves in ℝ⁴ defined by `e = 3` polynomials of
degree ≤ d (their complex dimension is one), so Corollary 2.4 applies; this is the
content of Lemma 3.5, threaded as a named input (the generic-projection /
elimination machinery of Corollary 2.4's proof is absent from pinned Mathlib).
-/
def Lemma35AuxIncidenceStatement : Prop :=
  ∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (X : PachDeZeeuw.PreparedBipartiteInput d)
      (T : Finset Point4) (S : Finset (X.P₁ × X.P₁)),
      (T : Set Point4) ⊆ ↑(PachDeZeeuw.auxPointSet X) →
      -- 2-DOF(M) in ℝ⁴ on (T, S):
      (∀ ij ∈ S, ∀ kl ∈ S,
          PachDeZeeuw.auxCurve X ij.1 ij.2 ≠ PachDeZeeuw.auxCurve X kl.1 kl.2 →
          (PachDeZeeuw.auxCurve X ij.1 ij.2 ∩
            PachDeZeeuw.auxCurve X kl.1 kl.2).encard ≤ (M : ℕ∞)) →
      (∀ z₁ ∈ T, ∀ z₂ ∈ T, z₁ ≠ z₂ →
          (S.filter (fun ij => z₁ ∈ PachDeZeeuw.auxCurve X ij.1 ij.2 ∧
                                z₂ ∈ PachDeZeeuw.auxCurve X ij.1 ij.2)).card ≤ M) →
        ((T.product S).filter
            (fun zij => zij.1 ∈ PachDeZeeuw.auxCurve X zij.2.1 zij.2.2)).card
          ≤ C * max (max ((T.card : ℝ) ^ ((2:ℝ)/3) * (S.card : ℝ) ^ ((2:ℝ)/3))
                      (T.card : ℝ)) (S.card : ℝ)
```

**Faithfulness.** This is Corollary 2.4 (the `max{·}` Pach–Sharir bound,
`incidenceBoundTerm` shape, constant depending only on `(d,M)`) *instantiated at
the specific curve family* `auxCurve` and the specific point set `auxPointSet`,
keyed on indices to keep `|Γ| = m²` (the paper's "consider them as different
curves", tex 537). The hypotheses are exactly the two clauses of
`TwoDegreesOfFreedom` written for the index-keyed family in ℝ⁴; the conclusion is
exactly `incidenceCount`-shaped (the filtered-product card) bounded by
`C·incidenceBoundTerm`. **No strengthening:** the bound, the exponents, and the
constant-dependence (`C` after `(d,M)`, before everything else) match the
published corollary verbatim.

**TRUTH.** This is the genuine published content. The `auxCurve` are complex-dim-1
real algebraic curves in ℝ⁴ defined by 3 bounded-degree polynomials (the two
`f₂`-pullbacks + the degree-2 distance equation), exactly the hypothesis class of
Corollary 2.4. Corollary 2.4 is a theorem (Pach–de Zeeuw §2, via Theorem 2.3 +
generic projection of a 1-dim complex curve to a plane curve). It is an **axiom**
here only because (i) the generic-projection-to-plane-curve + elimination-degree
machinery is mathlib-absent (`docs/corollary24-A4a-adjudication.md` §6.1–6.2), and
(ii) the literal general `Corollary24Statement` is *open* for the dim-≥2 class
(`docs/corollary24-literal-statement-truth.md`) — but **this named input is NOT
the general corollary**. By restricting to the `auxCurve` family it ranges only
over genuinely complex-dim-1 curves, so it sidesteps the W1 dim-≥2 open case
entirely. *Status: PROVEN-faithful, TRUE (published Cor 2.4 on its genuine
hypothesis class).*

**Non-circularity (task constraint).** GB-IN-2 is independent of
`Theorem23Statement` and the crossing lemma: the crossing lemma proves the
*planar* Pach–Sharir bound (`Theorem23Statement`, `D=2`); GB-IN-2 is a ℝ⁴
statement about polynomially-defined curves and is not derivable from the planar
bound without exactly the projection machinery that is mathlib-absent. So GB-IN-2
does **not** transitively re-assume Theorem23 or the crossing lemma. It is a
genuinely new published-geometry input, on a par with `MilnorThom22FiniteStatement`.
PROVEN (reading of the dependency graph).

**(2.2b) Why not state Lemma 3.5 via `Theorem23Statement` + projection?** Because
that *is* GB-PROJ-curve (§3), which is not a clean single axiom. GB-IN-2 (2.2a)
axiomatizes the **conclusion** of Lemma 3.5 directly, which is faithful to the
paper and needs no projection. The cost: GB-IN-2 makes the consumer of Gap B be
GB-IN-2, not `Theorem23Statement` — see §6.

### 2.3 GB-IN-3 (CONDITIONAL — only if Option A in §6 is chosen) — generic projection of a complex-dim-1 ℝ⁴ curve to a bounded-degree plane curve

If the orchestrator insists on keeping the bridge as `_of_theorem23` and routing
the incidence application through the *planar* `Theorem23Statement` (rather than
GB-IN-2), then the projection ℝ⁴→ℝ² must be discharged, and the **only** faithful
way to state it as a named input is the published "generic projection of a
complex-dim-1 curve is a plane curve" fact, **carrying its complex-dim-1
hypothesis explicitly**:

```lean
/--
**Generic projection to a plane curve (Pach–de Zeeuw §2, proof of Corollary 2.4).**

A real algebraic curve `γ ⊆ ℝ^D` of **complex dimension one**, defined by `e`
polynomials of degree ≤ d, has a generic rank-2 linear projection `π : ℝ^D → ℝ²`
whose set-image is the real zero set of a nonzero plane polynomial of total degree
bounded by `B D e d`, with `π` simultaneously injective on a prescribed finite
point set and incidence-preserving on it (a point of `P` lies on the image plane
curve iff it lay on `γ`). This bundles strengthened-A1 (rank-2 secant-cone-avoiding
projection) and A2_canonical (canonical eliminant + uniform degree bound) of
`docs/corollary24-A4a-adjudication.md` §6; both are absent from pinned Mathlib.

The complex-dimension-one hypothesis `hdim` is LOAD-BEARING and NOT derivable from
`IsAlgebraicCurveDefinedBy` (Witness W1, paraboloid). It must be supplied
externally (for `auxCurve`, by Lemma 3.3 claim 1, itself axiomatized inside
GB-IN-1 or as a separate dimension input).
-/
def GenericPlaneProjectionStatement : Prop :=
  ∀ (D e d : ℕ), ∃ B : ℕ,
    ∀ (γ : Set (EuclideanSpace ℝ (Fin D)))
      (P : Finset (EuclideanSpace ℝ (Fin D))),
      PachSharir.IsAlgebraicCurveDefinedBy D e d γ →
      ComplexDimensionOne γ →                                   -- the ADDED hypothesis (mathlib-absent predicate)
      ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
        Function.Surjective π ∧
        Set.InjOn π ↑P ∧
        PachSharir.IsPlaneAlgebraicCurveOfDegreeLE B ((π : _ → _) '' γ) ∧
        (∀ p ∈ P, (π p ∈ ((π : _ → _) '' γ) ↔ p ∈ γ))           -- incidence preservation (INCID)
```

**Faithfulness / truth.** Each conjunct is PROVEN-mathematically in
`docs/corollary24-A4a-adjudication.md` (rank-2: §6.1 cond.1; InjOn: §6.1 cond.2 /
in-repo `exists_rank2_projection_injOn`; plane-curve-of-bounded-degree:
§5.1 + §6.2; INCID: Theorem 4 / Proposition 3) **for genuinely complex-dim-1
curves**. The `ComplexDimensionOne` hypothesis is exactly the W1 fix and is
mandatory — without it the statement is **FALSE** (paraboloid W1:
`IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` is unsatisfiable, the image is
Zariski-dense in ℝ², no nonzero `f` vanishes on it; PROVEN in
`corollary24-literal-statement-truth.md` §5.1). *Status: PROVEN-faithful **only
with** `hdim`; TRUE (the published Cor-2.4 projection machinery on its genuine
hypothesis class).*

**This is the node the task flagged.** Three honest defects of the naive
transcription, and how GB-IN-3 handles each:

1. **Set-image vs Zariski closure.** Naive "`π '' γ` = real zero set of nonzero
   `f`" is generally FALSE: real projection images need not be Zariski-closed
   (isolated real points of the eliminant not in the image, unreached real
   branches, closure limit points — `corollary24-A4a-adjudication.md` §2). The
   *faithful* fix is **not** to weaken to containment-plus-correction; it is to use
   the INCID equivalence and have the named input assert that the canonical
   eliminant's real zero set agrees with the image **on the prescribed `P`** (the
   last conjunct), which is what the incidence application actually consumes.
   `IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` then holds because the canonical
   eliminant of a complex-dim-1 curve is a genuine nonzero plane polynomial whose
   real zero set *equals* `cl_Zar(π '' γ)` — and the conjunct `IsPlane…(π '' γ)`
   asserts the image *itself* is that zero set, which is **TRUE only when the image
   is already Zariski-closed**. For curves where the image is not Zariski-closed,
   `IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` as written is **FALSE**.
   **Therefore the conjunct must be stated on the closure, not the set-image**:
   replace `IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` with
   `∃ f ≠ 0, totalDegree f ≤ B ∧ {y | eval y f = 0} = cl_Zar(π '' γ)` and feed
   `cl_Zar(π '' γ)` (not `π '' γ`) to `Theorem23Statement` as the curve, with the
   incidence read-back handled by the INCID conjunct. This is a real correction:
   **the naive `IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` is not faithfully
   true**, and GB-IN-3 above is *itself* slightly wrong as first written — the
   honest version uses the closure. (FLAGGED; see §3.2.)

2. **Degree bound in the degenerate branch.** When `auxCurve` is finite/empty,
   `π '' γ` is a finite set of `k` points. EMPIRICALLY VERIFIED (`/tmp/finite_zeroset.py`,
   exact over ℚ): a finite set of `k` points in ℝ² is the exact real zero set of a
   nonzero polynomial of total degree `2k` (product of squared-distances). But `2k`
   is **not** bounded by `B D e d`: `k` can be as large as `|auxPointSet| = n²`.
   So a *uniform* degree bound `B D e d` over the finite branch is **FALSE** as a
   bound on the minimal-degree defining polynomial of the image-as-a-finite-set.
   The paper sidesteps this because in ℝ⁴ Corollary 2.4 handles finite curves
   directly (Milnor–Thom), without projecting. So GB-IN-3's `B D e d` bound is
   honest **only in the genuinely-1-dimensional branch**; the finite branch needs
   separate treatment (it contributes to `Γ₀`/minor incidences and is bounded by
   GB-MINOR, not by the plane-curve route). FLAGGED.

3. **`ComplexDimensionOne` is mathlib-absent and circular-risk.** The predicate
   `ComplexDimensionOne` does not exist in pinned mathlib; supplying it for
   `auxCurve` is Lemma 3.3 claim 1, which is *already inside GB-IN-1's truth
   justification*. If GB-IN-3 is used **and** GB-IN-1 is used, the dimension fact
   is needed in both places; either expose it as a fourth named input
   `AuxCurveComplexDimOneStatement` (cleaner) or have GB-IN-1 also *output* a
   dimension witness (couples the two). No circularity against the spine (it does
   not re-assume Theorem23), but a redundancy to manage. FLAGGED.

**Net verdict on GB-IN-3 / GB-PROJ-curve.** It **cannot** be stated faithfully and
truly as a *clean single* named input of the naive form
`IsPlaneAlgebraicCurveOfDegreeLE (someDegree d) (π '' auxCurve X i j)`. The honest
faithful statement (a) bundles two distinct published-machinery pieces
(strengthened-A1 + A2_canonical), (b) must use `cl_Zar(π '' γ)` not the set-image,
(c) carries a mandatory mathlib-absent `ComplexDimensionOne` hypothesis, and (d)
holds the degree bound only on the 1-dimensional branch. This is the **honest
alternative** the task asked for, and it is why §7 recommends GB-IN-2 (the ℝ⁴
incidence bound) over the projection route: GB-IN-2 axiomatizes the *conclusion*
Lemma 3.5 needs without incurring (a)–(d) at all.

### 2.4 GB-IN-4 (the minor-incidence input — Lemma 3.6, OPTIONAL given in-repo Bézout)

Lemma 3.6 (`lem:minorincidences`, tex 704): `|I(P,Γ₀)|, |I(P₀,Γ)| ≤ 8d²mn`. The
paper proves it from Theorem 2.1 (real Bézout, sharp `2d`: a circle meets `C₂` in
≤ 2d points unless `C₂` is that circle, excluded by Assumption 3.1.3). The repo
has `bezout` (`Bezout.lean:1315`) with the **crude** constant `(d₁+d₂+1)^8`, not
the sharp `2d`. The target conclusion `PositiveAuxiliaryIncidenceCardBound` only
needs *some* `const(d)·mn` minor bound (the cube and the partition-sum absorb any
polynomial-in-d constant), so the crude `bezout` plausibly suffices — but it
requires a `NoCommonCurveComponent` hypothesis (`Bezout.lean`, VERIFIED via the
A4a doc §1), which for the circle-meets-`C₂` instance is Assumption 3.1.3.

**Recommendation:** do **not** axiomatize Lemma 3.6 as a named input *yet*.
Attempt GB-MINOR (§4) from in-repo `bezout` + Assumption31. If the
`NoCommonCurveComponent` discharge for "circle ∩ C₂ is finite" turns out to need
the sharp `2d` count (which `bezout` does not give) or a mathlib-absent fact, then
add the minimal named input

```lean
def Lemma36MinorIncidenceStatement : Prop :=
  ∀ d : ℕ, ∃ K : ℕ, 0 < K ∧
    ∀ (X : PachDeZeeuw.PreparedBipartiteInput d)
      (Γ₀ : Finset (X.P₁ × X.P₁)),
      Γ₀.card ≤ 4 * d * X.P₁.card →
        ((auxIncidences X).filter (fun t => t.2 ∈ Γ₀)).card
          ≤ K * X.P₁.card * X.P₂.card ^ 2
```

(and its dual), faithful to Lemma 3.6 with a relaxed constant `K` in place of the
sharp `8d²`. CONJECTURED that in-repo `bezout` discharges this without the named
input; the discharge is GB-MINOR's open question (§4). I do not assert GB-IN-4 is
*needed* — it is the fallback if GB-MINOR cannot be proven from `bezout`.

---

## 3. The GB-PROJ-curve adjudication (task's flagged node, consolidated)

Restating the verdict cleanly, since it is the crux.

**Question.** Is "image `π '' (auxCurve X i j)` under a generic ℝ⁴→ℝ² projection
is *exactly* the real zero set of a nonzero bounded-degree plane polynomial"
statable as a faithful+true named input?

**Answer: NO, not in the naive set-equality form.** Three independent reasons,
each PROVEN:

1. **Set-image is not Zariski-closed** (PROVEN, `corollary24-A4a-adjudication.md`
   §2, with exact-symbolic corroboration §3.3). `IsPlaneAlgebraicCurveOfDegreeLE B
   (π '' γ)` demands `π '' γ = {f=0}`. For a 1-dim complex curve whose image has
   isolated real eliminant-points / unreached real branches / closure limit points,
   `π '' γ ⊊ {f=0}` for the canonical `f`, and **no** nonzero `f` has `{f=0}`
   equal to the (non-closed) set-image. So the naive conjunct is FALSE on those
   curves. The faithful repair uses `cl_Zar(π '' γ)` and an INCID conjunct
   (GB-IN-3, §2.3) — that is not the naive statement.

2. **Degree bound fails on the finite branch** (EMPIRICALLY VERIFIED, exact:
   `/tmp/finite_zeroset.py` — a `k`-point set needs degree `2k`; `k` up to `n²`).
   No `someDegree d` exists. The honest fix routes finite `auxCurve` through
   minor-incidences (GB-MINOR), not the plane-curve predicate.

3. **`ComplexDimensionOne` is a mandatory, mathlib-absent hypothesis** (PROVEN
   W1, `corollary24-literal-statement-truth.md` §5.1): without it the image can be
   Zariski-dense (dim-2), and `f ≠ 0` is unsatisfiable. `IsAlgebraicCurveDefinedBy
   4 3 d` does **not** imply it.

**Does the downstream incidence bound still go through if weakened to
containment + finite correction?** Partially, and only via the INCID route, not a
naive correction. The honest statement is: feed `cl_Zar(π '' γ)` (a genuine plane
curve, `f ≠ 0`, degree ≤ B) to `Theorem23Statement`, and use INCID
(`π p ∈ cl_Zar(π '' γ) ↔ p ∈ γ` for `p ∈ P`) to read the plane incidence count
back to the ℝ⁴ index-keyed count with the same `|P|`. This is PROVEN-mathematically
(`corollary24-A4a-adjudication.md` Prop 5 + A3 read-back, the latter
CONJECTURED-as-routine there, "exact Finset de-duplication not written out"). So
the bound goes through, but the named input that makes it go through is GB-IN-3
(the bundled projection fact), and the read-back (A3) is an additional un-written
bookkeeping obligation. **The projection route therefore costs one named input
(GB-IN-3) PLUS an unproven-here read-back lemma, versus GB-IN-2's single named
input and no projection.** Hence §7's ranking.

### 3.2 Correction to my own GB-IN-3 draft

As flagged in §2.3 defect 1, the conjunct
`IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)` in the GB-IN-3 `def` is **not
faithfully true** — the image need not be its own Zariski closure. The corrected
conjunct is

```lean
        (∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ B ∧
            {y : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => y i) f = 0}
              = closure_Zariski ((π : _ → _) '' γ)) ∧
```

with `closure_Zariski` the real Zariski closure (mathlib-absent as a ready
operator at this generality — another reason GB-IN-3 is the costly route). The
incidence application then uses this `f`'s zero set as the plane curve and the
INCID conjunct for read-back. I record this so no implementer ships the naive
(false) version.

---

## 4. Dependency check — is each "provable" node derivable from {GB-IN-1, GB-IN-2}
∪ {Theorem23Statement?, MilnorThom22FiniteStatement, in-repo}?

I check the **GB-IN-2 boundary** (the recommended one; §6 Option B). Under this
boundary the incidence application is GB-IN-2 itself, so several former nodes
collapse.

| Node | Was | Under GB-IN-2 boundary | Derivable? |
|---|---|---|---|
| GB-PRES (ℝ⁴ poly presentation) | needed for Milnor–Thom + Cor 2.4 | needed only to *justify* GB-IN-2's truth, not to *use* it (GB-IN-2 is stated over `auxCurve` directly) | **Not needed on the proof path.** GB-IN-2 abstracts over the presentation. PROVEN-unnecessary. |
| GB-PART-a (`16d⁴` finite-inter) | Milnor–Thom application | **internal to GB-IN-1** (it is the 2-DOF curve–curve clause) | Folded into GB-IN-1. Not a separate obligation. |
| GB-PART-b (dim + `Γ₀`) | bottleneck | **internal to GB-IN-1** | Folded in. |
| GB-PART-c (colouring) | greedy `SimpleGraph` | **internal to GB-IN-1** | Folded in (the colouring is part of what GB-IN-1 asserts exists). |
| GB-PART′ (dual) | doubles surface | **internal to GB-IN-1** (the `cP`/`P₀` half) | Folded in. |
| GB-PROJ-curve | load-bearing | **eliminated** (GB-IN-2 is ℝ⁴, no projection) | Not on path. |
| GB-PROJ-pt | rank-2 π | **eliminated** | Not on path. |
| GB-RECON (index→set) | bounded fibre | **eliminated** (GB-IN-2 is index-keyed; conclusion is the filtered-product card = `auxIncidences`-on-`S` directly) | Not on path. |
| GB-APPLY | apply Cor 2.4 per piece | **= apply GB-IN-2 per piece** | Derivable: instantiate GB-IN-2 at `(T,S) = (auxPointSet|cP=α, indices|cΓ=β)`, hypotheses supplied by GB-IN-1. PROVEN-derivable (sketch §5). |
| GB-MINOR | Lemma 3.6 | from in-repo `bezout` + Assumption31, OR GB-IN-4 | **CONJECTURED-derivable** from `bezout`; fallback GB-IN-4 (§2.4). Open. |
| GB-CONV (max→ℕ-cube + sum) | last step | sum GB-APPLY over `≤ (2d²+1)²` classes + GB-MINOR, cube, cast | **PROVEN-derivable** (sketch §5); shape lemma EMPIRICALLY VERIFIED + elementary proof, prior doc §FLAG. |
| asymmetric regime | — | `GapBSupport.incidence_pigeonhole` (in-repo PROVEN) | Already done. |

So under the GB-IN-2 boundary, the **only** mathlib-absent axioms are GB-IN-1 and
GB-IN-2; everything else is either folded into them, eliminated, or provable from
in-repo lemmas — with the **single** residual open obligation being GB-MINOR's
discharge from `bezout` (fallback: GB-IN-4). This is the minimal surface.

### 4.1 What about the GB-IN-3 (projection) boundary (Option A)?

Then GB-PROJ-curve = GB-IN-3, GB-RECON and GB-APPLY come back (now applying the
*planar* `Theorem23Statement` to image curves), and GB-PART-a returns as a
separate Milnor–Thom application **unless** GB-IN-1 already carries the `16d⁴`
clause (it does, §2.1). The axiom set is {GB-IN-1, GB-IN-3, + the A3 read-back
lemma (unproven here) + `ComplexDimensionOne` input}. This is **strictly more**
mathlib-absent surface than {GB-IN-1, GB-IN-2}. PROVEN by the count: Option A has
GB-IN-1 + GB-IN-3 + dim-input (3 axioms) + an unproven read-back; Option B has
GB-IN-1 + GB-IN-2 (2 axioms) + a possible GB-IN-4. Option B is minimal.

---

## 5. Provability sketches for the derivable nodes (no "should be provable" without this)

### 5.1 GB-APPLY (PROVEN-derivable from GB-IN-1 + GB-IN-2)

Goal: per non-exceptional class pair `(β,α)`, bound the index-keyed incidences of
class-`α` points with class-`β` curves.

1. From GB-IN-1 at `(d,X)`: get `Γ₀,P₀,cΓ,cP` and, for `(β,α)` with `β,α ≠ 0`, the
   two 2-DOF clauses at `M = 16d⁴`.
2. Set `S := Finset.univ.filter (cΓ · = β)`, `T := auxPointSet`-elements whose
   `cP`-colour is `α` (a `Finset Point4 ⊆ auxPointSet X`).
3. GB-IN-1's curve–curve clause gives exactly GB-IN-2's first hypothesis on
   `(T,S)`; the point–point clause (whole-family form) restricted to `S` (monotone,
   §2.1 caveat) gives GB-IN-2's second hypothesis.
4. Apply GB-IN-2 at `(d, 16d⁴)`: obtain `((T.product S).filter …).card ≤ C ·
   max{…}`. The filtered-product card is precisely the restriction of
   `auxIncidences X` to `(T,S)`.

Every step is instantiation + the monotone restriction. **PROVEN-derivable.**

### 5.2 GB-CONV (PROVEN-derivable)

1. `auxIncidences X` decomposes (as a `Finset`) over the colour classes: the
   index second-coordinate `(i,j)` has a `cΓ`-colour, the point first-coordinate
   has a `cP`-colour. Partition `auxIncidences X` into:
   (a) incidences with `cΓ = 0` (curve-exceptional, ⊆ `I(P,Γ₀)`) — bounded by
   GB-MINOR;
   (b) incidences with `cP = 0` (point-exceptional, ⊆ `I(P₀,Γ)`) — bounded by
   GB-MINOR dual;
   (c) the `(β,α)` non-exceptional cells — each bounded by GB-APPLY.
   This is a finite `Finset.biUnion`/filter decomposition; the count is ≤ the sum.
2. Sum over `≤ (2d²+1)²` cells (a `d`-bounded number) of the GB-APPLY bound +
   2 minor bounds. Cast ℝ→ℕ (the cell counts are ℕ; the `max{·}` bound is the only
   ℝ object — bound `auxIncidences`-on-cell ≤ `⌊C·max⌋ + 1` etc., or carry ℝ to
   the end). Cube. Collapse via the shape inequality
   `max{(mn)^4, m^6, n^6} ≤ 4(mn)^4` under `m ≤ 2n, n ≤ 2m, m,n ≥ 1`
   (EMPIRICALLY VERIFIED `1 ≤ m,n < 80`, prior doc §FLAG; elementary proof:
   `m^6 ≤ 4(mn)^4 ⇔ m² ≤ 4n^4`, and `m² ≤ 4n² ≤ 4n^4`).
3. The asymmetric regime (a class with `|Γβ| ≥ |Pα|²`) is handled by
   `GapBSupport.incidence_pigeonhole` (in-repo PROVEN), which dominates the `max`
   by `|Γβ|` and gives `I ≤ M|Pα|² + |Γβ| ≤ (M+1)|Γβ|`, absorbed into `C(mn)^4`.

The arithmetic is `Nat.cast`/`nlinarith`/`omega`-level once the per-cell bounds
are in hand. **PROVEN-derivable** (modulo GB-MINOR). The final constant `C` is
`≈ 4·B_d³` with `B_d` polynomial in `d` (recompute from the actual GB-IN-2
constant; do not hard-code the paper's `B_d`). FLAGGED.

### 5.3 GB-MINOR (CONJECTURED-derivable; the one residual open node)

Goal: `((auxIncidences X).filter (·.2 ∈ Γ₀)).card ≤ const(d)·m·n²` (and dual).

Paper argument (tex 706): each `C_ij ∈ Γ₀` has ≤ `2dn` incidences with `P`,
because for each of the `n` choices of `q_s ∈ S₂`, the matching `q_t` lies on
`C₂ ∩ (circle around p_j of radius d(p_i,q_s))`, ≤ 2d points by real Bézout
(Theorem 2.1), unless `C₂` is that circle (excluded by Assumption 3.1.3). Then
`|I(P,Γ₀)| ≤ 2dn · 4dm = 8d²mn`.

To derive in Lean from in-repo `bezout` (`Bezout.lean:1315`, constant
`(d₁+d₂+1)^8`, with a `NoCommonCurveComponent` hypothesis):

- For fixed `(i,j,s)`, `{q_t ∈ S₂ : (q_s,q_t) ∈ C_ij}` ⊆ `C₂ ∩ sphere(p_j, r)`
  with `r = d(p_i,q_s)`. Both are bounded-degree curves (`C₂` degree ≤ d, sphere
  degree 2). `bezout` gives finiteness + `≤ (d+2+1)^8` **provided**
  `NoCommonCurveComponent C₂ (sphere p_j r)`. The sphere and the irreducible `C₂`
  share a component only if `C₂` *is* that sphere (irreducibility), excluded by
  Assumption 3.1.3 (circle-center-not-in-point-set ⇒ `C₂` not concentric witness)
  — this discharge is the open step.
- Summing: `|I(P,Γ₀)| ≤ |Γ₀| · n · (d+3)^8 ≤ 4dm · n · (d+3)^8 = const(d)·mn`.

**Status: CONJECTURED-derivable.** The crude `(d+3)^8` is fine (cube/sum absorb
it). The genuine gap is the `NoCommonCurveComponent` discharge for "irreducible
`C₂` ≠ a specific sphere": it needs (sphere is irreducible *or* `C₂`-irreducible-
of-degree-d cannot equal a degree-2 sphere unless d=2 and they coincide) + the
Assumption-3.1.3 exclusion. This is plausibly in-repo-provable from
`IsIrreducibleCurve` + Assumption31, but I have **not** verified the exact mathlib
lemmas exist. If it stalls, GB-IN-4 (§2.4) is the minimal fallback. FLAGGED — this
is the one place "provable" is CONJECTURED, not PROVEN.

---

## 6. The bridge-consumer problem (Theorem23Statement vs GB-IN-2)

**The tension.** The current spine is
`crossing-lemma → Theorem23Statement → (Bridge) → PositiveAuxIncidenceCardBound`.
Under the recommended GB-IN-2 boundary, the consumer of Gap B is **GB-IN-2**, not
`Theorem23Statement`. So `positiveAuxiliaryIncidenceCardBound_of_theorem23`'s
hypothesis `_h : Theorem23Statement` is **not the right hypothesis** — it would be
`_h : Lemma35AuxIncidenceStatement` (GB-IN-2). Two honest options:

**Option B (recommended).** Re-target the bridge to consume GB-IN-2 + GB-IN-1:

```lean
theorem positiveAuxiliaryIncidenceCardBound_of_namedInputs
    (hPart : MilnorThom.Lemma34PartitionStatement)
    (hInc  : MilnorThom.Lemma35AuxIncidenceStatement) :
    PositiveAuxiliaryIncidenceCardBoundStatement := …
```

Then a *separate* lemma derives `Lemma35AuxIncidenceStatement` from
`Theorem23Statement` **if and only if** the projection machinery (GB-IN-3 + read-
back) is supplied — which is exactly the optional Option-A surface. The spine no
longer claims `Theorem23Statement` alone closes Gap B; it claims {GB-IN-1, GB-IN-2}
do, and `theorem23_of_crossingLemma` becomes relevant only to the *optional*
GB-IN-2-from-Theorem23 derivation. **This is the faithful state:** the paper's §3
uses Corollary 2.4 (≈ GB-IN-2), not Theorem 2.3, so the named input that closes §3
is the ℝ⁴ corollary content, and the planar `Theorem23Statement` is upstream of
*that* (via the crossing lemma) only under the projection route.

Cost of Option B: the crossing-lemma → spine connection weakens. Currently
`positiveAuxiliaryIncidenceCardBound_of_crossingLemma` (`Bridge.lean:81`) composes
`theorem23_of_crossingLemma` into Gap B. Under Option B that composition only works
if GB-IN-2 is derived from `Theorem23Statement` (needing GB-IN-3 + read-back).
So Option B makes the *honest* dependency visible: **the spine needs GB-IN-1 +
GB-IN-2 as named inputs, and GB-IN-2 is not free from the crossing lemma** — the
crossing lemma gives the *planar* bound, and lifting it to the ℝ⁴ auxCurve
incidence count is the (mathlib-absent) projection step. The current `_of_theorem23`
signature **understates** this: it suggests `Theorem23Statement` suffices, when in
truth the ℝ⁴ content (GB-IN-2) or the projection machinery (GB-IN-3) is also
required. This is a faithfulness defect in the *current* `Bridge.lean` framing, not
just a wiring choice.

**Option A.** Keep `_of_theorem23`, supply GB-IN-1 + GB-IN-3 (+ dim input + read-
back), project each class's curves to the plane, apply `Theorem23Statement` to the
images. Faithful to "use the planar bound", but pays the full GB-PROJ-curve price
(§2.3, §3): GB-IN-3 is a bundled, closure-corrected, dim-hypothesised axiom, and
the A3 read-back is an extra unproven lemma. Strictly larger surface (§4.1).

**Recommendation: Option B.** It axiomatizes the *least* mathlib-absent surface
(GB-IN-1 + GB-IN-2, two recognizable published lemmas), eliminates the projection
node entirely, and exposes the honest dependency (the ℝ⁴ corollary content is a
genuine named input, not a free consequence of the planar crossing-lemma route).
If the orchestrator's strategy-of-record *requires* the consumer to be
`Theorem23Statement` (planar) for crossing-lemma-attribution reasons, Option A is
available but is the costlier, less faithful route, and its GB-IN-3 must use the
closure-corrected form of §3.2 — never the naive set-image form.

---

## 7. What to land first (ranked) + summary table

**Ranked directions:**

1. **Adjudicate Option A vs Option B with the orchestrator (strategic, gates
   everything).** This is the binding decision: does Gap B's consumer stay
   `Theorem23Statement` (Option A, projection route, costlier) or become the ℝ⁴
   named inputs (Option B, minimal, faithful to the paper's actual Corollary-2.4
   usage)? My recommendation is Option B. Do not write any GB node before this is
   settled — Option A and B have different consumer signatures.

2. **Land GB-IN-1 (`Lemma34PartitionStatement`) as a named `Prop` in
   `MilnorThom.lean`-style** (its own file, e.g. `Lemma34Partition.lean`). This is
   the deepest published lemma, needed under *both* options, faithful and true as
   transcribed (§2.1). Settle the `auxPointOfPair'` exposure (FLAG) — either expose
   the wrapper or state the point–point clause via `auxPointSet` membership.

3. **Land GB-IN-2 (`Lemma35AuxIncidenceStatement`)** (Option B) — the ℝ⁴ incidence
   bound, faithful (§2.2a), true (Cor 2.4 on its genuine hypothesis class), non-
   circular. With GB-IN-1 + GB-IN-2 in place, GB-APPLY and GB-CONV are
   PROVEN-derivable (§5.1–5.2).

4. **GB-CONV + the shape lemma `max_pow_le`** — writable now against the stated
   GB-IN-1/GB-IN-2, validates the arithmetic end-to-end. `incidence_pigeonhole`
   already supplies the asymmetric branch.

5. **GB-MINOR from in-repo `bezout`** — the one residual open derivation (§5.3,
   CONJECTURED-derivable). If the `NoCommonCurveComponent` discharge stalls, add
   GB-IN-4 (`Lemma36MinorIncidenceStatement`, §2.4) as the minimal fallback named
   input.

6. **(Option A only) GB-IN-3 + A3 read-back** — only if Option A is chosen. Use the
   closure-corrected form (§3.2), the mandatory `ComplexDimensionOne` hypothesis,
   and accept the extra unproven read-back lemma. Not recommended.

**Summary table** (recommended Option-B surface in bold; GB-IN-3/4 conditional):

| input name | paper lemma (tex) | faithful? | true? | mathlib-absent justification |
|---|---|---|---|---|
| **GB-IN-1 `Lemma34PartitionStatement`** | Lemma 3.4 `lem:partition` (632–687), resting on Lemma 3.2 (834+) + Lemma 3.3 (571–623) | yes — partitions + `|Γ₀|≤4dm`, `|P₀|≤4dn` + 2-DOF(16d⁴) verbatim, both halves; dim-1 internal | yes — published lemma, transcribed | complex variety dimension (dim_ℂ C_ij=1), bounded symmetry counts (§4), irreducible-component count — all absent from pinned mathlib |
| **GB-IN-2 `Lemma35AuxIncidenceStatement`** | Lemma 3.5 `lem:mainincidences` (694) = Cor 2.4 on the auxCurve family | yes — `max{·}` Pach–Sharir, index-keyed, ℝ⁴, constant dep. (d,M) | yes — Cor 2.4 on genuine complex-dim-1 curves (sidesteps W1) | generic-projection-to-plane-curve + elimination-degree machinery (A4a §6.1–6.2) absent; **NOT** the open general `Corollary24Statement` |
| GB-IN-3 `GenericPlaneProjectionStatement` (Option A only) | proof of Cor 2.4 (§2, projection) | **only** with `ComplexDimensionOne` hyp + closure-corrected conjunct (§3.2); naive set-image form is FALSE | yes with those fixes; FALSE without `hdim` (W1) | strengthened-A1 (rank-2 secant-cone-avoiding π) + A2_canonical (eliminant + degree bound) + Zariski-closure operator, all mathlib-absent |
| GB-IN-4 `Lemma36MinorIncidenceStatement` (fallback) | Lemma 3.6 `lem:minorincidences` (704) | yes — relaxed constant K for 8d² | yes — published lemma | only if in-repo `bezout` cannot discharge the `NoCommonCurveComponent` for circle∩C₂; otherwise unneeded |

**Structural assumptions made explicit:**

- **Finiteness is load-bearing** in two places: GB-IN-1's curve–curve `16d⁴` clause
  is the *finite-intersection* bound (the partition is what *supplies* finiteness
  within a class); and GB-MINOR's `bezout` needs `(C₂ ∩ sphere).Finite`. Both are
  faithful to the paper (Milnor–Thom is conditional on finiteness, tex 600).
- **Complex dimension one** of `auxCurve` is used: it is **internal** to GB-IN-1's
  truth (Lemma 3.3 claim 1) and, under Option A only, an **explicit hypothesis** of
  GB-IN-3. Under Option B it never appears as a Lean hypothesis (it lives inside the
  axiom's justification), which is the cleaner state.
- **The 2-DOF curve–curve clause is FALSE on the full family** (tex 626) — it holds
  only per partition class. This is why GB-IN-1 cannot be skipped under either
  option; it is dimension-independent.
- **`C`/constants may depend on `(d,M)`** (`Theorem23Statement`/`Corollary24Statement`
  quantifier order, `Theorem23.lean:77,94`), legitimizing `M = 16d⁴` and a
  polynomial-in-d incidence constant.
- **No circularity against the spine:** neither GB-IN-1 nor GB-IN-2 re-assumes
  `Theorem23Statement` or `CrossingLemmaMultigraphStatement` (PROVEN, §2.2 / §1 —
  GB-IN-2 is a ℝ⁴ statement not derivable from the planar bound without the absent
  projection machinery). GB-IN-1 is purely combinatorial-geometric (partition
  existence) and references neither.

## FLAG FOR IMPLEMENTER

- **GB-IN-1 point-encoding.** Decide the presentation of the point–point clause:
  either expose a public `auxPointOfPair` wrapper (`AuxiliaryCurves.lean:39` is
  `private`) so `auxPointOfPair' X st` typechecks, or state the clause over
  `z₁ z₂ ∈ auxPointSet X` membership (no `P₂×P₂` index needed) and colour the
  *points* of `auxPointSet` directly via `cP : Point4 → Fin (2d²+2)` restricted to
  `auxPointSet`. The latter avoids touching `private`; preferred. Verify the
  colouring-of-a-Finset vs colouring-of-the-index-type choice against how GB-APPLY
  consumes it (§5.1 wants `T : Finset Point4 ⊆ auxPointSet`).
- **GB-IN-2 constant recompute.** The final `C` in `PositiveAuxIncidenceCardBound`
  is `≈ 4·B_d³` where `B_d` is built from GB-IN-2's `C(d, 16d⁴)` — do **not**
  hard-code the paper's `B_d = 6d⁴A_d`; re-derive from the actual Lean constant
  GB-IN-2 returns (`Classical.choose`), per `corollary24-gapB-incidence-assembly-
  scope.md` §FLAG.
- **GB-IN-3 (Option A only) must use the closure-corrected conjunct** of §3.2
  (`{f=0} = cl_Zar(π '' γ)`), never `IsPlaneAlgebraicCurveOfDegreeLE B (π '' γ)`
  (FALSE on non-Zariski-closed images), and must carry `ComplexDimensionOne` (FALSE
  without it, W1). It also needs a Zariski-closure operator (mathlib-absent at this
  generality) and an A3 read-back lemma (unproven here, CONJECTURED-routine in
  `corollary24-A4a-adjudication.md` §6 FLAG 3).
- **GB-MINOR discharge.** The `NoCommonCurveComponent (C₂) (sphere p_j r)` step
  (§5.3) needs: irreducible degree-d `C₂` ≠ a degree-2 sphere (from
  `IsIrreducibleCurve` + degree, or Assumption 3.1.3). Confirm the mathlib lemmas
  for "irreducible curve shares a component with another curve iff equal" exist at
  the in-repo `PlaneCurve` generality before committing to the `bezout`-only route;
  else fall back to GB-IN-4.
- **Scratch artifact** `/tmp/finite_zeroset.py` (EMPIRICALLY VERIFIED, exact over
  ℚ): a `k`-point set in ℝ² is the exact zero set of a nonzero degree-`2k`
  polynomial; degree grows with `k` (up to `n²`), so no `someDegree d` bound exists
  on the finite branch — the basis for §2.3 defect 2 and §3 reason 2.
