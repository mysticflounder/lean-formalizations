/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CurveInterface

/-!
# Pach--de Zeeuw low-level interface

This file starts the no-external-dependency Pach–de Zeeuw development. The first
goal is the finite counting core used by the Elekes lower bound; the curve
predicates and normalized input wrappers live alongside it so the later PDZ
files can build on a stable namespace.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry

/-- The ambient 4-vector space for auxiliary-curve geometry. -/
abbrev Point4 := EuclideanSpace ℝ (Fin 4)

/-- Bipartite distances between two finite point sets in the plane. -/
noncomputable def bipartiteDistances (P Q : Finset Point2) : Finset ℝ :=
  (P.product Q).image (fun pq ↦ dist pq.1 pq.2)

private def lineSet (a b c : ℝ) : Set Point2 :=
  {p : Point2 | a * p 0 + b * p 1 = c}

/-- Parallel-line exceptional pair. -/
def ParallelLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a b c₁ c₂ : ℝ, (a, b) ≠ (0, 0) ∧
    C₁ = lineSet a b c₁ ∧ C₂ = lineSet a b c₂

/-- Orthogonal-line exceptional pair. -/
def OrthogonalLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ, (a₁, b₁) ≠ (0, 0) ∧ (a₂, b₂) ≠ (0, 0) ∧
    a₁ * a₂ + b₁ * b₂ = 0 ∧
    C₁ = lineSet a₁ b₁ c₁ ∧ C₂ = lineSet a₂ b₂ c₂

/-- Concentric-circle exceptional pair. -/
def ConcentricCirclePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ center : Point2, ∃ r₁ r₂ : ℝ,
    C₁ = Metric.sphere center r₁ ∧ C₂ = Metric.sphere center r₂

/--
Pach--de Zeeuw exceptional curve-pair alternatives for Theorem 1.2:
parallel lines, orthogonal lines, or concentric circles.
-/
def ExceptionalCurvePair (C₁ C₂ : Set Point2) : Prop :=
  ParallelLinePair C₁ C₂ ∨ OrthogonalLinePair C₁ C₂ ∨ ConcentricCirclePair C₁ C₂

lemma exceptionalCurvePair_of_parallelLines {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inl h

lemma exceptionalCurvePair_of_orthogonalLines {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inr (Or.inl h)

lemma exceptionalCurvePair_of_concentricCircles {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inr (Or.inr h)

lemma ParallelLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₁, hab, rfl⟩

lemma ParallelLinePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₂ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₂, hab, rfl⟩

lemma OrthogonalLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₁, b₁, c₁, hab₁, rfl⟩

lemma OrthogonalLinePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₂ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₂, b₂, c₂, hab₂, rfl⟩

lemma ConcentricCirclePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₁, rfl⟩

lemma ConcentricCirclePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₂ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₂, rfl⟩

lemma ExceptionalCurvePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with h | h | h
  · exact ParallelLinePair.left_controlledDegenerate h
  · exact OrthogonalLinePair.left_controlledDegenerate h
  · exact ConcentricCirclePair.left_controlledDegenerate h

lemma ExceptionalCurvePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₂ := by
  rcases h with h | h | h
  · exact ParallelLinePair.right_controlledDegenerate h
  · exact OrthogonalLinePair.right_controlledDegenerate h
  · exact ConcentricCirclePair.right_controlledDegenerate h

/-- A vertical line `{p | p₀ = c}` (Pach--de Zeeuw, Assumption 3.1.1). -/
def IsVerticalLine (C : Set Point2) : Prop :=
  ∃ c : ℝ, C = {p : Point2 | p 0 = c}

/-- Assumption 3.1.3 for one curve: if `C` is a circle, its center is not a
point of `P` — the *other* curve's point set (`S₂` for `C₁`, `S₁` for `C₂`). -/
def CircleCenterNotIn (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ (center : Point2) (r : ℝ), C = Metric.sphere center r → center ∉ (P : Set Point2)

/-- Assumption 3.1.4 for one curve: if `C` is a circle with center `o`, then
every concentric circle `sphere o ρ` meets `P` in at most one point. -/
def ConcentricFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ (center : Point2) (r : ℝ), C = Metric.sphere center r →
    ∀ ρ : ℝ, ((P : Set Point2) ∩ Metric.sphere center ρ).Subsingleton

/-- Assumption 3.1.5 for one curve: if `C` is the line `a x + b y = c`, then the
union of any parallel line `a x + b y = c'` with its reflection in `C`
(the line `a x + b y = 2c - c'`) meets `P` in at most one point. -/
def ParallelReflectionFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ a b c : ℝ, (a, b) ≠ (0, 0) → C = lineSet a b c →
    ∀ c' : ℝ,
      ((P : Set Point2) ∩ (lineSet a b c' ∪ lineSet a b (2 * c - c'))).Subsingleton

/-- Assumption 3.1.6 for one curve: if `C` is a line, then every orthogonal line
meets `P` in at most one point. Orthogonality `a a' + b b' = 0` is the same
relation used by `OrthogonalLinePair`. -/
def OrthogonalFibersSparse (C : Set Point2) (P : Finset Point2) : Prop :=
  ∀ a b c : ℝ, (a, b) ≠ (0, 0) → C = lineSet a b c →
    ∀ a' b' c' : ℝ, a * a' + b * b' = 0 →
      ((P : Set Point2) ∩ lineSet a' b' c').Subsingleton

/-- Assumption 3.1 normalization data from Pach--de Zeeuw. Each field is one of
the six numbered conditions; the conditions that single out one curve (resp. the
other) are recorded per curve, with the constrained point set being the *other*
curve's set (`S₂` for `C₁`, `S₁` for `C₂`), exactly as in the paper. -/
structure Assumption31Data
    (C₁ C₂ : Set Point2) (P₁ P₂ : Finset Point2) where
  /-- (3.1.1) `C₁` is not a vertical line. -/
  noVerticalComponent₁ : ¬ IsVerticalLine C₁
  /-- (3.1.1) `C₂` is not a vertical line. -/
  noVerticalComponent₂ : ¬ IsVerticalLine C₂
  /-- (3.1.2) The point sets are disjoint. -/
  pointSetsDisjoint : Disjoint (P₁ : Set Point2) (P₂ : Set Point2)
  /-- (3.1.3) If `C₁` (resp. `C₂`) is a circle, its center is not in the other
  curve's point set. -/
  circleCenterNotInPointSet :
    CircleCenterNotIn C₁ P₂ ∧ CircleCenterNotIn C₂ P₁
  /-- (3.1.4) If `C₁` (resp. `C₂`) is a circle, concentric circles are sparse in
  the other curve's point set. -/
  sparseConcentricFibers :
    ConcentricFibersSparse C₁ P₂ ∧ ConcentricFibersSparse C₂ P₁
  /-- (3.1.5) If `C₁` (resp. `C₂`) is a line, parallel-line/reflection unions are
  sparse in the other curve's point set. -/
  sparseParallelFibers :
    ParallelReflectionFibersSparse C₁ P₂ ∧ ParallelReflectionFibersSparse C₂ P₁
  /-- (3.1.6) If `C₁` (resp. `C₂`) is a line, orthogonal lines are sparse in the
  other curve's point set. -/
  sparseOrthogonalFibers :
    OrthogonalFibersSparse C₁ P₂ ∧ OrthogonalFibersSparse C₂ P₁
  /-- The pair is not parallel lines, orthogonal lines, or concentric circles. -/
  noExceptionalPair : ¬ ExceptionalCurvePair C₁ C₂

/-- When neither curve is a line or a circle, every conditional clause of
Assumption 3.1 (parts 1, 3–6) is vacuously true, so the data is determined by
disjointness of the point sets and the curves not forming an exceptional pair.
This is the situation in the proof of Theorem 1.1, where the curve is excluded
from being a line or circle. -/
lemma assumption31Data_of_not_controlledDegenerate {C₁ C₂ : Set Point2}
    {P₁ P₂ : Finset Point2}
    (h₁ : ¬ PlaneCurve.IsLineOrCircle C₁)
    (h₂ : ¬ PlaneCurve.IsLineOrCircle C₂)
    (hdisj : Disjoint (P₁ : Set Point2) (P₂ : Set Point2))
    (hexc : ¬ ExceptionalCurvePair C₁ C₂) :
    Assumption31Data C₁ C₂ P₁ P₂ where
  noVerticalComponent₁ := by
    rintro ⟨c, hc⟩
    exact h₁ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  noVerticalComponent₂ := by
    rintro ⟨c, hc⟩
    exact h₂ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  pointSetsDisjoint := hdisj
  circleCenterNotInPointSet :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseConcentricFibers :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseParallelFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  sparseOrthogonalFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  noExceptionalPair := hexc

/--
Prepared bipartite input satisfying the normalizations of Assumption 3.1:
irreducible curves, finite point sets on the curves, and no exceptional
parallel/orthogonal/concentric configuration.
-/
structure PreparedBipartiteInput (d : ℕ) where
  C₁ : Set Point2
  C₂ : Set Point2
  P₁ : Finset Point2
  P₂ : Finset Point2
  hC₁ : PlaneCurve.IsIrreducibleCurve d C₁
  hC₂ : PlaneCurve.IsIrreducibleCurve d C₂
  hP₁ : (P₁ : Set Point2) ⊆ C₁
  hP₂ : (P₂ : Set Point2) ⊆ C₂
  notExceptional : ¬ ExceptionalCurvePair C₁ C₂
  assumption31 : Assumption31Data C₁ C₂ P₁ P₂

private noncomputable def distanceFiber (P Q : Finset Point2) (r : ℝ) :
    Finset (Point2 × Point2) :=
  (P.product Q).filter (fun pq ↦ dist pq.1 pq.2 = r)

private noncomputable def equalDistanceQuadruplePairs {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  ((X.P₁.product X.P₂).product (X.P₁.product X.P₂)).filter
    (fun pp ↦ dist pp.1.1 pp.1.2 = dist pp.2.1 pp.2.2)

private def quadrupleOfPairs :
    (Point2 × Point2) × (Point2 × Point2) → Point2 × Point2 × Point2 × Point2
| ⟨⟨a, b⟩, ⟨c, d⟩⟩ => (a, b, c, d)

private lemma quadrupleOfPairs_injective :
    Function.Injective quadrupleOfPairs := by
  intro x y h
  cases x
  cases y
  simp [quadrupleOfPairs] at h
  aesop

/-- Equal-distance quadruples used by the Elekes lower-bound step. -/
noncomputable def equalDistanceQuadruples {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  equalDistanceQuadruplePairs X

/-- The finite Cauchy-style lower bound behind the equal-distance quadruple count. -/
lemma lemma37_equalDistanceQuadruple_lower {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card *
        (equalDistanceQuadruples X).card := by
  classical
  let S : Finset (Point2 × Point2) := X.P₁.product X.P₂
  let f : Point2 × Point2 → ℝ := fun pq ↦ dist pq.1 pq.2
  let fibers : ℝ → Finset (Point2 × Point2) := fun r ↦ distanceFiber X.P₁ X.P₂ r
  let qfibers : ℝ → Finset ((Point2 × Point2) × (Point2 × Point2)) := fun r ↦
    fibers r ×ˢ fibers r
  have hS : S.card = X.P₁.card * X.P₂.card := by
    simpa [S] using (Finset.card_product X.P₁ X.P₂)
  have hsum : ∑ r ∈ S.image f, (fibers r).card = S.card := by
    have hsum0 :
        ∑ r ∈ S.image f, (fibers r).card =
          {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i}.card := by
      simpa [S, f, fibers, distanceFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter S (S.image f) f)
    have hfilter :
        {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i} = S := by
      apply Finset.filter_true_of_mem
      intro i hi
      rcases Finset.mem_product.mp hi with ⟨hiA, hiB⟩
      exact ⟨i.1, i.2, ⟨⟨hiA, hiB⟩, rfl⟩⟩
    simpa [hfilter] using hsum0
  have hbiUnion :
      ((S.image f).biUnion qfibers).card =
        ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro r hr
      simpa [qfibers, pow_two, Finset.card_product]
    · intro r₁ _hr₁ r₂ _hr₂ hne
      change Disjoint (qfibers r₁) (qfibers r₂)
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      rw [Finset.mem_product] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁₁, hq₁₂⟩
      rcases hq₂ with ⟨hq₂₁, hq₂₂⟩
      simp [fibers, distanceFiber] at hq₁₁ hq₂₁
      rcases hq₁₁ with ⟨_, hdist₁⟩
      rcases hq₂₁ with ⟨_, hdist₂⟩
      exact hne (hdist₁.symm.trans hdist₂)
  have hquad_ge :
      ∑ r ∈ S.image f, (fibers r).card ^ 2 ≤ (equalDistanceQuadruples X).card := by
    have hsub : (S.image f).biUnion qfibers ⊆ equalDistanceQuadruples X := by
      intro q hq
      rw [Finset.mem_biUnion] at hq
      rcases hq with ⟨r, hr, hq⟩
      rw [Finset.mem_image] at hr
      rcases hr with ⟨pq, hpq, rfl⟩
      rw [Finset.mem_product] at hq
      rcases hq with ⟨hq₁, hq₂⟩
      simp [fibers, distanceFiber] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁S, hq₁dist⟩
      rcases hq₂ with ⟨hq₂S, hq₂dist⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr hq₁S, Finset.mem_product.mpr hq₂S⟩, ?_⟩
      simpa [S, f] using hq₁dist.trans hq₂dist.symm
    calc
      ∑ r ∈ S.image f, (fibers r).card ^ 2 = ((S.image f).biUnion qfibers).card := by
        simpa [qfibers] using hbiUnion.symm
      _ ≤ (equalDistanceQuadruples X).card := Finset.card_le_card hsub
  have hcs :
      S.card ^ 2 ≤ (S.image f).card * ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    simpa [hsum] using
      (sq_sum_le_card_mul_sum_sq (s := S.image f) (f := fun r ↦ (fibers r).card))
  have hmain : S.card ^ 2 ≤ (S.image f).card * (equalDistanceQuadruples X).card := by
    exact hcs.trans (Nat.mul_le_mul_left _ hquad_ge)
  have hmain' : (X.P₁.card * X.P₂.card) ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card * (equalDistanceQuadruples X).card := by
    rw [hS] at hmain
    simpa [S, f, bipartiteDistances, equalDistanceQuadruples] using hmain
  simpa [Nat.mul_pow] using hmain'

end PachDeZeeuw
