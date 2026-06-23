/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.AuxiliaryCurves
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23

/-!
# §3 named literature inputs — the faithful Pach–de Zeeuw lemmas the assembly rests on

This file freezes the **statement surface** of the three §3 lemmas of Pach–de
Zeeuw, "Distinct distances on algebraic curves in the plane," that the incidence
assembly (`IncidenceAssembly/SectionThreeAssembly.lean`) consumes. Each is a
`def … : Prop` in the house style of `MilnorThom.MilnorThom22FiniteStatement`: a
faithful, TRUE transcription of a published lemma that is absent from the pinned
Mathlib, threaded downstream as a hypothesis (never an `axiom`).

The boundary is the **ℝ⁴ published-lemma boundary** (`docs/gap-b-named-inputs-design.md`,
Option B): no projection ℝ⁴→ℝ², no `IsPlaneAlgebraicCurveOfDegreeLE` obligation,
no over-broad `Corollary24Statement` (open for complex dimension ≥ 2). The named
inputs range only over the genuinely complex-dimension-one `auxCurve` family, so
they are the published lemmas on their genuine hypothesis class.

* `Lemma34PartitionStatement` — **Lemma 3.4** (`lem:partition`, tex 632–687): the
  two-degrees-of-freedom partition of the auxiliary family.
* `Lemma35AuxIncidenceStatement` — **Lemma 3.5** (`lem:mainincidences`, tex 694) =
  **Corollary 2.4** specialized to the `auxCurve` family, index-keyed in ℝ⁴.
* `Lemma36MinorIncidenceStatement` — **Lemma 3.6** (`lem:minorincidences`, tex 704):
  the minor (exceptional-set) incidence bound.

All three are PROVEN-faithful and TRUE (the faithfulness/truth arguments are in
`docs/gap-b-named-inputs-design.md` §2.1, §2.2, §2.4 and the paper's §3 proofs).
They are accepted as named inputs only because complex variety dimension theory
(Lemma 3.3 claim 1), the bounded symmetry/component counts of §4 (Lemma 3.2), and
the generic-projection / elimination-degree machinery of Corollary 2.4's proof are
absent from pinned Mathlib — exactly as `MilnorThom22FiniteStatement` is accepted
because the semialgebraic Morse-theory route to Theorem 2.2 is absent.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw

open scoped Classical

/--
**Lemma 3.4 (Pach–de Zeeuw, `lem:partition`, tex 632–687).**

*Let `L = 2d² + 1`. There are partitions of `P` into `P₀,…,P_L` and `Γ` into
`Γ₀,…,Γ_L` such that `|Γ₀| ≤ 4dm` and `|P₀| ≤ 4dn`, and such that for all
`1 ≤ α, β ≤ L`, the pair `(P_α, Γ_β)` forms a system with two degrees of freedom,
with multiplicity `M = 16d⁴`.*

Here the curve family `Γ = {C_ij}` is indexed by `X.P₁ × X.P₁` (so `m = |P₁|`,
`|Γ| = m²`, coincident curves kept distinct by index — the paper's "consider them
as different curves", tex 537), and the point set `P = {(q_s, q_t)}` is encoded in
`auxPointSet X` (`n = |P₂|`). The partition is presented as two finite colourings
`cΓ : (X.P₁ × X.P₁) → Fin (2d²+2)` and `cP : Point4 → Fin (2d²+2)` (label `0` is the
exceptional class, labels `1,…,L` the `L` non-exceptional classes) together with
the exceptional finite sets `Γ₀ ⊆ X.P₁ × X.P₁` and `P₀ ⊆ Point4`.

The two-degrees-of-freedom property of `(P_α, Γ_β)` is recorded as the two clauses
of `PachSharir.TwoDegreesOfFreedom` in ℝ⁴:

* **curve–curve clause**: two distinct same-class curves meet in at most `16d⁴`
  points of the ambient ℝ⁴ (`(γ₁ ∩ γ₂).encard ≤ 16d⁴`);
* **point–point clause**: two distinct same-class points lie on at most `16d⁴`
  curves of the *whole* family `Γ` (the paper's literal "at most `16d⁴` curves from
  `Γ` passing through any two points", tex 682–683). Counting over the whole family
  is the paper's wording and is *at least as strong* as the per-class count the
  incidence application needs (restriction to a subfamily only decreases the count).

**Faithfulness.** The conclusion is exactly the paper's Lemma 3.4: the partitions,
the cardinality bounds `|Γ₀| ≤ 4dm`, `|P₀| ≤ 4dn` verbatim, and the 2-DOF(16d⁴)
property in its two roles. No strengthening — the curve–curve clause uses the
ambient ℝ⁴ intersection (matching the paper and `TwoDegreesOfFreedom`), and the
point–point clause counts the whole index family.

**Truth.** This is the published Lemma 3.4, transcribed. Its proof (tex 632–687)
takes `Γ₀` from Lemma 3.2 (`|Γ₀| ≤ 4dm`), colours the infinite-intersection graph
`G` on `Γ \ Γ₀` (max degree `≤ 2d²` by Lemma 3.3, so `χ ≤ L`), giving same-class
curves finite intersection hence `≤ 16d⁴` points by the Milnor–Thom bound (Theorem
2.2 with `D = 4`); the dual construction on the transposed family `C̃_st` gives the
point side. It is a named input here only because complex variety dimension theory
(`dim_ℂ C_ij = 1`, Lemma 3.3 claim 1 — internal to this lemma, not a hypothesis),
the bounded symmetry counts of §4 (Lemma 3.2), and the irreducible-component count
(Lemma 3.3 claim 3) are absent from pinned Mathlib.
-/
def Lemma34PartitionStatement : Prop :=
  ∀ (d : ℕ) (X : PreparedBipartiteInput d),
    ∃ (Γ₀ : Finset (X.P₁ × X.P₁)) (P₀ : Finset Point4)
      (cΓ : (X.P₁ × X.P₁) → Fin (2 * d ^ 2 + 2))
      (cP : Point4 → Fin (2 * d ^ 2 + 2)),
      Γ₀.card ≤ 4 * d * X.P₁.card ∧
      P₀.card ≤ 4 * d * X.P₂.card ∧
      (∀ ij, ij ∈ Γ₀ ↔ cΓ ij = 0) ∧
      (∀ z ∈ auxPointSet X, z ∈ P₀ ↔ cP z = 0) ∧
      (∀ β α : Fin (2 * d ^ 2 + 2), β ≠ 0 → α ≠ 0 →
        -- curve–curve clause (ambient ℝ⁴): two distinct same-class curves meet in
        -- ≤ 16 d⁴ points
        (∀ ij kl : X.P₁ × X.P₁, cΓ ij = β → cΓ kl = β →
            auxCurve X ij.1 ij.2 ≠ auxCurve X kl.1 kl.2 →
            (auxCurve X ij.1 ij.2 ∩ auxCurve X kl.1 kl.2).encard ≤ (16 * d ^ 4 : ℕ)) ∧
        -- point–point clause: two distinct same-class points lie on ≤ 16 d⁴ curves
        -- of the WHOLE family
        (∀ z₁ ∈ auxPointSet X, ∀ z₂ ∈ auxPointSet X, cP z₁ = α → cP z₂ = α → z₁ ≠ z₂ →
            ((Finset.univ : Finset (X.P₁ × X.P₁)).filter (fun ij =>
                z₁ ∈ auxCurve X ij.1 ij.2 ∧ z₂ ∈ auxCurve X ij.1 ij.2)).card
              ≤ 16 * d ^ 4))

/--
**Lemma 3.5 (Pach–de Zeeuw, `lem:mainincidences`, tex 694), specialized to the
auxiliary family** = **Corollary 2.4** applied to `(P_α, Γ_β)` in ℝ⁴.

*For all `1 ≤ α, β ≤ L`, `|I(P_α, Γ_β)| ≤ A_d · max{m^{4/3}n^{4/3}, m², n²}`.* The
paper obtains it by applying Corollary 2.4 in ℝ⁴ (tex 691): the `C_ij` are real
algebraic curves in ℝ⁴ defined by `e = 3` polynomials of degree `≤ d` (the two
`f₂`-pullbacks plus the degree-2 distance equation), of complex dimension one, with
the 2-DOF property supplied by Lemma 3.4.

This input states the **conclusion** of Corollary 2.4 directly, *index-keyed* over
the `auxCurve` family and *staying in ℝ⁴* — so it incurs neither the `incidenceCount`
`Finset (Set _)` collapse nor any `IsPlaneAlgebraicCurveOfDegreeLE` (projection)
obligation. For each point subset `T ⊆ auxPointSet X` and index subset
`S ⊆ X.P₁ × X.P₁` forming a 2-DOF(M) system in ℝ⁴ (the two hypotheses below — the
ambient-intersection clause and the point–point clause of
`PachSharir.TwoDegreesOfFreedom`, written for the index-keyed family), the number of
index-keyed incidences obeys the Pach–Sharir bound, with the constant `C` depending
only on `(d, M)`.

**Faithfulness.** The `max{·}` shape, the `2/3` exponents, and the constant-
dependence `C = C(d, M)` (before `T, S`) match the published corollary verbatim
(`PachSharir.incidenceBoundTerm`, `PachSharir.Corollary24Statement`'s quantifier
order). The hypotheses are exactly the two clauses of `TwoDegreesOfFreedom` for the
index-keyed ℝ⁴ family; the conclusion is exactly the filtered-product incidence
count (which is `auxIncidences X` restricted to `(T, S)`).

**Truth.** Corollary 2.4 is a theorem of Pach–de Zeeuw §2 (Theorem 2.3 + generic
projection of a complex-dimension-one curve to a plane curve). The `auxCurve` are
genuinely complex-dimension-one real algebraic curves in ℝ⁴ defined by 3 bounded-
degree polynomials — exactly the hypothesis class of Corollary 2.4 — so this input
ranges only over that class and **sidesteps the open complex-dimension-≥2 case** of
the literal `Corollary24Statement` (`docs/corollary24-literal-statement-truth.md`).
It is a named input only because the generic-projection-to-plane-curve and
elimination-degree machinery of Corollary 2.4's proof is absent from pinned Mathlib.

**Non-circularity.** This is a ℝ⁴ statement about polynomially-defined curves; it is
not derivable from the *planar* Pach–Sharir bound (`Theorem23Statement`, `D = 2`)
without exactly the projection machinery that is mathlib-absent. So it does **not**
transitively re-assume `Theorem23Statement` or the crossing lemma — it is a genuinely
new published-geometry input, on a par with `MilnorThom22FiniteStatement`.

Note: the `D = 4`, `e = 3`, `degree ≤ d` characterization of the auxiliary curves is
a **prose truth-justification** here, not a Lean-checked hypothesis — this `Prop`
ranges directly over `auxCurve X` (whose definition `AuxiliaryCurves.auxCurve` *is*
the common zero set of three bounded-degree polynomials: two `curveWitnessPoly₂`
pullbacks of degree ≤ d and the degree-2 distance equation), so no
`IsAlgebraicCurveDefinedBy 4 3 d` obligation is incurred (the Option-B boundary
axiomatizes the *conclusion* of Corollary 2.4, not its hypotheses).
-/
def Lemma35AuxIncidenceStatement : Prop :=
  ∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (X : PreparedBipartiteInput d)
      (T : Finset Point4) (S : Finset (X.P₁ × X.P₁)),
      (T : Set Point4) ⊆ ↑(auxPointSet X) →
      -- 2-DOF(M) in ℝ⁴ on (T, S), curve–curve clause:
      (∀ ij ∈ S, ∀ kl ∈ S,
          auxCurve X ij.1 ij.2 ≠ auxCurve X kl.1 kl.2 →
          (auxCurve X ij.1 ij.2 ∩ auxCurve X kl.1 kl.2).encard ≤ (M : ℕ)) →
      -- 2-DOF(M) in ℝ⁴ on (T, S), point–point clause:
      (∀ z₁ ∈ T, ∀ z₂ ∈ T, z₁ ≠ z₂ →
          (S.filter (fun ij => z₁ ∈ auxCurve X ij.1 ij.2 ∧
                                z₂ ∈ auxCurve X ij.1 ij.2)).card ≤ M) →
        ((T.product S).filter
            (fun zij => zij.1 ∈ auxCurve X zij.2.1 zij.2.2)).card
          ≤ C * max (max ((T.card : ℝ) ^ ((2:ℝ)/3) * (S.card : ℝ) ^ ((2:ℝ)/3))
                      (T.card : ℝ)) (S.card : ℝ)

/--
**Lemma 3.6 (Pach–de Zeeuw, `lem:minorincidences`, tex 704).**

*`|I(P, Γ₀)| ≤ 8d²mn` and `|I(P₀, Γ)| ≤ 8d²mn`.*

The paper proves it from Theorem 2.1 (real Bézout, sharp count `2d`): each curve
`C_ij ∈ Γ₀` has at most `2dn` incidences with `P`, because for each of the `n`
choices of `q_s ∈ S₂` the matching `q_t` lies on `C₂ ∩ (circle around p_j of radius
d(p_i, q_s))`, at most `2d` points unless `C₂` is that circle (excluded by
Assumption 3.1.3); hence `|I(P, Γ₀)| ≤ 2dn · 4dm = 8d²mn`, and dually for `P₀`.

This input is stated with a **relaxed constant `K`** in place of the sharp `8d²`
(the downstream cube and partition-sum absorb any constant depending only on `d`),
keyed directly on the `auxIncidences X` count so the assembly consumes it without an
ℝ⁴→ℝ² read-back. Both incidence bounds are *linear* in `m·n` (= `|P₁|·|P₂|`),
exactly as the paper's `8d²mn`. The curve-exceptional bound is taken over any
`Γ₀ : Finset (X.P₁ × X.P₁)` with `|Γ₀| ≤ 4dm`, and the point-exceptional bound over
any `P₀ : Finset Point4 ⊆ auxPointSet X` with `|P₀| ≤ 4dn` — the exact objects
Lemma 3.4 produces.

**Faithfulness.** The bound shape `K · m · n` matches the paper's `8d²mn` with `K`
relaxed from `8d²` (relaxing a constant that depends only on `d` is faithful, not
strengthening). The two clauses are the paper's two inequalities of Lemma 3.6.

**Truth.** This is the published Lemma 3.6 (relaxed constant). It is a named input
because the discharge of "irreducible `C₂` shares no infinite component with the
distance circle (so their intersection is finite of bounded size)" via the sharp
real-Bézout `2d` count and Assumption 3.1.3, together with the ℝ⁴→ℝ² incidence
read-back, is not available from pinned Mathlib in-repo (`docs/gap-b-named-inputs-design.md`
§5.3 rates the in-repo `bezout` discharge CONJECTURED-derivable with an unverified
`NoCommonCurveComponent` step). It is purely a real-algebraic finiteness/counting
fact and does not re-assume `Theorem23Statement` or the crossing lemma.
-/
def Lemma36MinorIncidenceStatement : Prop :=
  ∀ d : ℕ, ∃ K : ℕ, 0 < K ∧
    ∀ (X : PreparedBipartiteInput d),
      (∀ Γ₀ : Finset (X.P₁ × X.P₁), Γ₀.card ≤ 4 * d * X.P₁.card →
          ((auxIncidences X).filter (fun t => t.2 ∈ Γ₀)).card
            ≤ K * X.P₁.card * X.P₂.card) ∧
      (∀ P₀ : Finset Point4, (P₀ : Set Point4) ⊆ ↑(auxPointSet X) →
          P₀.card ≤ 4 * d * X.P₂.card →
          ((auxIncidences X).filter (fun t => t.1 ∈ P₀)).card
            ≤ K * X.P₁.card * X.P₂.card)

end PachDeZeeuw
