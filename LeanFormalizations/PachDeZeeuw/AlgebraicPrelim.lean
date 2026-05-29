/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Pach--de Zeeuw algebraic preliminaries

This file houses the statement-level algebraic-geometry vocabulary used by the
later PDZ cards. The real work remains the algebraic proofs/adapters; the goal
here is to fix the Lean surface in the local project namespace.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

/-- The Euclidean plane `ℝ²` (real inner-product space of dimension 2). -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean 4-space `ℝ⁴` (host of the Elekes–Sharir motion space). -/
abbrev Point4 := EuclideanSpace ℝ (Fin 4)

/-! ### Curve vocabulary

The plane-curve predicates these lemmas range over. (In the source project these
lived in a shared `External` namespace; inlined here so the file is
self-contained and mathlib-only.) -/

namespace External

/-- `C` is the real zero set of a nonzero bivariate polynomial of total degree
at most `k`. -/
def IsBoundedDegreeCurve (k : ℕ) (C : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ k ∧
    C = {x : Point2 | MvPolynomial.eval (fun i ↦ x i) p = 0}

/-- `C` is the real zero set of a nonzero **irreducible** bivariate polynomial of
total degree at most `k`. -/
def IsIrreducibleCurve (k : ℕ) (C : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ k ∧ Irreducible p ∧
    C = {x : Point2 | MvPolynomial.eval (fun i ↦ x i) p = 0}

/-- `C` is a controlled-degenerate curve form: a line or a circle. -/
def IsControlledDegenerate (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧
      C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ (center : Point2) (radius : ℝ), C = Metric.sphere center radius)

/-- The line-or-circle alternative, synonymously the controlled-degenerate case. -/
def IsLineOrCircleComponent (C : Set Point2) : Prop :=
  IsControlledDegenerate C

end External

open EuclideanGeometry
open scoped Topology

/--
Two bounded-degree real plane curves have no shared infinite irreducible curve
component. This is not the Bezout conclusion: it does not assert that
`C₁ ∩ C₂` is finite or bounded.
-/
def NoCommonCurveComponent (C₁ C₂ : Set Point2) : Prop :=
  ¬ ∃ e : ℕ, ∃ C : Set Point2,
    External.IsIrreducibleCurve e C ∧ C.Infinite ∧ C ⊆ C₁ ∧ C ⊆ C₂

/-- Theorem 2.2, Bezout finite-intersection bound for plane curves. -/
def Theorem22_BezoutStatement : Prop :=
  ∀ d₁ d₂ : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ C₁ C₂ : Set Point2,
      External.IsBoundedDegreeCurve d₁ C₁ →
      External.IsBoundedDegreeCurve d₂ C₂ →
      NoCommonCurveComponent C₁ C₂ →
      (C₁ ∩ C₂).Finite ∧ (C₁ ∩ C₂).ncard ≤ C

/-- `NoCommonCurveComponent` is symmetric in its two inputs. -/
lemma NoCommonCurveComponent.symm {C₁ C₂ : Set Point2} :
    NoCommonCurveComponent C₁ C₂ ↔ NoCommonCurveComponent C₂ C₁ := by
  constructor
  · intro h h'
    rcases h' with ⟨e, C, hC, hInf, hC₂, hC₁⟩
    exact h ⟨e, C, hC, hInf, hC₁, hC₂⟩
  · intro h h'
    rcases h' with ⟨e, C, hC, hInf, hC₁, hC₂⟩
    exact h ⟨e, C, hC, hInf, hC₂, hC₁⟩

/-- `NoCommonCurveComponent` is monotone in the left argument. -/
lemma NoCommonCurveComponent.mono_left {C₁ C₁' C₂ : Set Point2}
    (h : NoCommonCurveComponent C₁ C₂) (hsub : C₁' ⊆ C₁) :
    NoCommonCurveComponent C₁' C₂ := by
  intro h'
  rcases h' with ⟨e, C, hC, hInf, hC₁', hC₂⟩
  exact h ⟨e, C, hC, hInf, hC₁'.trans hsub, hC₂⟩

/-- `NoCommonCurveComponent` is monotone in the right argument. -/
lemma NoCommonCurveComponent.mono_right {C₁ C₂ C₂' : Set Point2}
    (h : NoCommonCurveComponent C₁ C₂) (hsub : C₂' ⊆ C₂) :
    NoCommonCurveComponent C₁ C₂' := by
  intro h'
  rcases h' with ⟨e, C, hC, hInf, hC₁, hC₂'⟩
  exact h ⟨e, C, hC, hInf, hC₁, hC₂'.trans hsub⟩

/-- `NoCommonCurveComponent` respects equality of either input curve. -/
lemma NoCommonCurveComponent.congr {C₁ C₁' C₂ C₂' : Set Point2}
    (h₁ : C₁ = C₁') (h₂ : C₂ = C₂') :
    NoCommonCurveComponent C₁ C₂ ↔ NoCommonCurveComponent C₁' C₂' := by
  constructor <;> intro h <;> simpa [h₁, h₂] using h

/-! ## Bezout helper layer -/

/-- The real zero set of a bivariate polynomial on the plane. -/
def PlaneCurveZeroSet (p : MvPolynomial (Fin 2) ℝ) : Set Point2 :=
  {x | MvPolynomial.eval (fun i => x i) p = 0}

/-- Membership in `PlaneCurveZeroSet` is just polynomial evaluation vanishing. -/
@[simp] lemma mem_PlaneCurveZeroSet {p : MvPolynomial (Fin 2) ℝ}
    {x : Point2} :
    x ∈ PlaneCurveZeroSet p ↔ MvPolynomial.eval (fun i => x i) p = 0 := Iff.rfl

/-- The polynomial has an infinite real zero set. -/
def HasInfiniteRealZeroSet (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  (PlaneCurveZeroSet p).Infinite

/-- A common irreducible factor with infinite real zero set. -/
def HasCommonInfiniteIrreducibleFactor
    (p q : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ h : MvPolynomial (Fin 2) ℝ,
    Irreducible h ∧ HasInfiniteRealZeroSet h ∧ h ∣ p ∧ h ∣ q

/-- A divisor has a smaller real zero set. -/
lemma PlaneCurveZeroSet_subset_of_dvd {p q : MvPolynomial (Fin 2) ℝ}
    (hpq : p ∣ q) : PlaneCurveZeroSet p ⊆ PlaneCurveZeroSet q := by
  intro x hx
  rcases hpq with ⟨r, rfl⟩
  rw [mem_PlaneCurveZeroSet] at hx ⊢
  simpa [MvPolynomial.eval_mul, hx]

/--
An infinite common irreducible factor gives a forbidden common curve
component.
-/
lemma noCommonCurveComponent_of_no_common_infinite_factor
    {C₁ C₂ : Set Point2} {p q : MvPolynomial (Fin 2) ℝ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hC₁ : C₁ = PlaneCurveZeroSet p)
    (hC₂ : C₂ = PlaneCurveZeroSet q)
    (hno : NoCommonCurveComponent C₁ C₂) :
    ¬ HasCommonInfiniteIrreducibleFactor p q := by
  intro hcommon
  rcases hcommon with ⟨h, hirr, hinf, hp, hq⟩
  have hh0 : h ≠ 0 := hirr.ne_zero
  have hcurve : External.IsIrreducibleCurve h.totalDegree (PlaneCurveZeroSet h) := by
    refine ⟨h, hh0, le_rfl, hirr, rfl⟩
  have hsubset₁ : PlaneCurveZeroSet h ⊆ C₁ := by
    rw [hC₁]
    exact PlaneCurveZeroSet_subset_of_dvd hp
  have hsubset₂ : PlaneCurveZeroSet h ⊆ C₂ := by
    rw [hC₂]
    exact PlaneCurveZeroSet_subset_of_dvd hq
  exact hno ⟨h.totalDegree, PlaneCurveZeroSet h, hcurve, hinf, hsubset₁, hsubset₂⟩

/-- Curry a bivariate real polynomial into a univariate polynomial over the coefficient ring. -/
abbrev XCoeff := MvPolynomial (Fin 1) ℝ

/-- Fraction field of the coefficient ring used in the Bezout proof packet. -/
abbrev XFrac := FractionRing XCoeff

/-- View a bivariate polynomial as a univariate polynomial in the first variable. -/
noncomputable def Curry0
    (p : MvPolynomial (Fin 2) ℝ) : Polynomial XCoeff :=
  MvPolynomial.finSuccEquiv ℝ 1 p

/-- Map the curry to the fraction field of the coefficient ring. -/
noncomputable def Curry0Frac
    (p : MvPolynomial (Fin 2) ℝ) : Polynomial XFrac :=
  (Curry0 p).map (algebraMap XCoeff XFrac)

/-- Evaluate a coefficient-ring polynomial at a real coefficient value. -/
def coeffEval (x : ℝ) : XCoeff →+* ℝ :=
  MvPolynomial.eval (fun _ : Fin 1 => x)

/-- Identify the coefficient ring with ordinary univariate real polynomials. -/
noncomputable def XCoeffEquiv : XCoeff ≃+* Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans
    (Polynomial.mapEquiv ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv))

/-- Transport the principal ideal ring structure from `Polynomial ℝ` to `XCoeff`. -/
noncomputable instance : IsPrincipalIdealRing XCoeff := by
  refine IsPrincipalIdealRing.of_surjective XCoeffEquiv.symm ?_
  exact XCoeffEquiv.symm.surjective

/-- Transport the normalization monoid structure from `Polynomial ℝ` to `XCoeff`. -/
noncomputable instance : NormalizationMonoid XCoeff := by
  letI : NormalizationMonoid (Polynomial ℝ) := Polynomial.normalizedGcdMonoid.toNormalizationMonoid
  refine
    { normUnit := fun x =>
        Units.map XCoeffEquiv.symm.toMonoidHom
          (NormalizationMonoid.normUnit (XCoeffEquiv x))
      normUnit_zero := by
        simp [XCoeffEquiv]
      normUnit_mul := by
        intro a b ha hb
        have ha' : XCoeffEquiv a ≠ 0 := by
          intro h0
          exact ha (XCoeffEquiv.injective (by simpa using h0))
        have hb' : XCoeffEquiv b ≠ 0 := by
          intro h0
          exact hb (XCoeffEquiv.injective (by simpa using h0))
        have hmul :=
          (NormalizationMonoid.normUnit_mul (α := Polynomial ℝ) (a := XCoeffEquiv a)
            (b := XCoeffEquiv b) ha' hb')
        simpa [XCoeffEquiv, map_mul] using congrArg (Units.map XCoeffEquiv.symm.toMonoidHom) hmul
      normUnit_coe_units := by
        intro u
        have hunit :=
          NormalizationMonoid.normUnit_coe_units (α := Polynomial ℝ)
            (Units.map XCoeffEquiv.toMonoidHom u)
        have hmap :
            Units.map XCoeffEquiv.symm.toMonoidHom
                (Units.map XCoeffEquiv.toMonoidHom u) = u := by
          have hmap_val :
              ((Units.map XCoeffEquiv.symm.toMonoidHom
                  (Units.map XCoeffEquiv.toMonoidHom u) : XCoeffˣ) : XCoeff) = ↑u := by
            change XCoeffEquiv.symm (XCoeffEquiv ↑u) = ↑u
            exact XCoeffEquiv.left_inv ↑u
          apply Units.ext
          exact hmap_val
        have hcongr :=
          congrArg (Units.map XCoeffEquiv.symm.toMonoidHom) hunit
        have hmapInv :
            Units.map XCoeffEquiv.symm.toMonoidHom
              ((Units.map XCoeffEquiv.toMonoidHom u)⁻¹) = u⁻¹ := by
          simpa [hmap]
        exact hcongr.trans hmapInv }

/-- `XCoeff` inherits a normalized GCD monoid structure from `Polynomial ℝ`. -/
noncomputable instance : NormalizedGCDMonoid XCoeff :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid XCoeff

/-- Evaluation commutes with the `XCoeff`/`Polynomial ℝ` identification. -/
lemma coeffEval_eq_eval_XCoeffEquiv (x : ℝ) (r : XCoeff) :
    Polynomial.eval x (XCoeffEquiv r) = coeffEval x r := by
  refine MvPolynomial.induction_on
    (motive := fun r => Polynomial.eval x (XCoeffEquiv r) = coeffEval x r) r ?_ ?_ ?_
  · intro a
    simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
  · intro r s hr hs
    simp [hr, hs]
  · intro r n hr
    fin_cases n
    rw [map_mul, Polynomial.eval_mul]
    rw [hr]
    simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]

/-- The eliminated coordinate of a point in the plane. -/
def elimCoord (z : Point2) : ℝ := z 0

/-- The coefficient coordinate of a point in the plane. -/
def coeffCoord (z : Point2) : ℝ := z 1

/-- Specialize the coefficient variable of a plane polynomial. -/
noncomputable def Specialized0 (x : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    Polynomial ℝ :=
  (Curry0 p).map (coeffEval x)

/-- The coefficient resultant of a plane polynomial pair. -/
noncomputable def ResultantCoeff (p q : MvPolynomial (Fin 2) ℝ) : XCoeff :=
  Polynomial.resultant (Curry0 p) (Curry0 q)

/-- The roots of a coefficient polynomial in `ℝ`. -/
def CoeffRootSet (r : XCoeff) : Set ℝ :=
  {x | MvPolynomial.eval (fun _ : Fin 1 => x) r = 0}

/-- The common-zero fiber at a fixed coefficient coordinate. -/
def FiberCommonZeros (x : ℝ) (p q : MvPolynomial (Fin 2) ℝ) : Set ℝ :=
  {y | Polynomial.eval y (Specialized0 x p) = 0 ∧
       Polynomial.eval y (Specialized0 x q) = 0}

/-- Specialization commutes with `finSuccEquiv`. -/
lemma eval_eq_specialized_eval
    (p : MvPolynomial (Fin 2) ℝ) (z : Point2) :
    MvPolynomial.eval (fun i => z i) p =
      Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) := by
  have hcons :
      Fin.cons (elimCoord z) (fun _ : Fin 1 => coeffCoord z) = fun i => z i := by
    ext i <;> fin_cases i <;> simp [elimCoord, coeffCoord]
  calc
    MvPolynomial.eval (fun i => z i) p =
        MvPolynomial.eval (Fin.cons (elimCoord z) (fun _ : Fin 1 => coeffCoord z)) p := by
      rw [hcons]
    _ = Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) := by
      simpa [Specialized0, coeffEval, elimCoord, coeffCoord, Curry0]
        using (MvPolynomial.eval_eq_eval_mv_eval'
          (s := fun _ : Fin 1 => coeffCoord z) (y := elimCoord z) p)

/-- Specialized resultant agrees with evaluating the coefficient resultant. -/
lemma specialized_resultant_eq_coeff_eval
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    Polynomial.resultant (Specialized0 x p) (Specialized0 x q)
      (Curry0 p).natDegree (Curry0 q).natDegree =
    MvPolynomial.eval (fun _ : Fin 1 => x) (ResultantCoeff p q) := by
  simpa [Specialized0, ResultantCoeff, coeffEval] using
    (Polynomial.resultant_map_map (Curry0 p) (Curry0 q)
      (Curry0 p).natDegree (Curry0 q).natDegree (coeffEval x))

/-- A common zero gives a root of the coefficient resultant. -/
lemma resultant_vanishes_at_common_zero
    (p q : MvPolynomial (Fin 2) ℝ) {z : Point2}
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hz : z ∈ PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q) :
    coeffCoord z ∈ CoeffRootSet (ResultantCoeff p q) := by
  rw [CoeffRootSet]
  have hp : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.1
  have hq : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.2
  have hm : (Specialized0 (coeffCoord z) p).natDegree ≤ (Curry0 p).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le (f := coeffEval (coeffCoord z)) (p := Curry0 p))
  have hn : (Specialized0 (coeffCoord z) q).natDegree ≤ (Curry0 q).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le (f := coeffEval (coeffCoord z)) (p := Curry0 q))
  have hbez :
      ∃ u v,
        u.degree < ↑(Curry0 q).natDegree ∧
        v.degree < ↑(Curry0 p).natDegree ∧
        Specialized0 (coeffCoord z) p * u + Specialized0 (coeffCoord z) q * v =
          Polynomial.C
            (Polynomial.resultant (Specialized0 (coeffCoord z) p)
              (Specialized0 (coeffCoord z) q)
              (Curry0 p).natDegree (Curry0 q).natDegree) := by
    exact Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := Specialized0 (coeffCoord z) p) (g := Specialized0 (coeffCoord z) q)
      hm hn (Or.inl (Nat.ne_of_gt hp0deg))
  rcases hbez with ⟨u, v, hu, hv, hbez⟩
  have hzero :
      Polynomial.eval (elimCoord z)
        (Polynomial.C
          (Polynomial.resultant (Specialized0 (coeffCoord z) p)
            (Specialized0 (coeffCoord z) q)
            (Curry0 p).natDegree (Curry0 q).natDegree)) = 0 := by
    rw [← hbez]
    simp [hp, hq]
  simpa [ResultantCoeff, Specialized0, coeffEval] using hzero

/-- Resultant is nonzero after mapping to the fraction field. -/
theorem resultant_ne_zero_of_fraction_coprime
    (P Q : Polynomial XCoeff)
    (hcop : IsCoprime (P.map (algebraMap XCoeff XFrac))
                       (Q.map (algebraMap XCoeff XFrac))) :
    Polynomial.resultant P Q ≠ 0 := by
  intro hzero
  have hinj : Function.Injective (algebraMap XCoeff XFrac) :=
    IsFractionRing.injective XCoeff XFrac
  have hmapzero :
      Polynomial.resultant
        (P.map (algebraMap XCoeff XFrac))
        (Q.map (algebraMap XCoeff XFrac)) = 0 := by
    rw [show
        Polynomial.resultant
          (P.map (algebraMap XCoeff XFrac))
          (Q.map (algebraMap XCoeff XFrac)) =
        Polynomial.resultant
          (P.map (algebraMap XCoeff XFrac))
          (Q.map (algebraMap XCoeff XFrac))
          P.natDegree Q.natDegree by
      simp [Polynomial.natDegree_map_eq_of_injective hinj]]
    rw [Polynomial.resultant_map_map, hzero]
    simp
  exact Polynomial.resultant_ne_zero _ _ hcop hmapzero

/-- Primitive polynomials remain `IsRelPrime` after mapping to the fraction field. -/
theorem isRelPrime_fraction_map_of_isPrimitive
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hQprim : Q.IsPrimitive)
    (hrel : IsRelPrime P Q) :
    IsRelPrime (P.map (algebraMap XCoeff XFrac))
               (Q.map (algebraMap XCoeff XFrac)) := by
  intro D hDP hDQ
  by_cases hD : D = 0
  · have hP0 : P ≠ 0 := hPprim.ne_zero
    have hmap_inj : Function.Injective (Polynomial.map (algebraMap XCoeff XFrac)) :=
      Polynomial.map_injective _ (IsFractionRing.injective XCoeff XFrac)
    have hmapP0 : P.map (algebraMap XCoeff XFrac) ≠ 0 := by
      intro hzero
      have hzero' : Polynomial.map (algebraMap XCoeff XFrac) P =
          Polynomial.map (algebraMap XCoeff XFrac) 0 := by
        simpa using hzero
      exact hP0 (hmap_inj hzero')
    have hzero : P.map (algebraMap XCoeff XFrac) = 0 := by
      simpa [hD] using hDP
    exact (hmapP0 hzero).elim
  · rcases IsLocalization.integerNormalization_map_to_map (nonZeroDivisors XCoeff) D with
      ⟨⟨b, hb⟩, hnorm⟩
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hb0' : (algebraMap XCoeff XFrac b) ≠ 0 := by
      intro hb'
      exact hb0 (IsFractionRing.injective XCoeff XFrac (by simpa using hb'))
    have hbunit : IsUnit (Polynomial.C (algebraMap XCoeff XFrac b)) := by
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0')
    rcases hbunit with ⟨u, hu⟩
    have hassoc :
        Associated D (Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D)) := by
      have hnorm' :
          Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
          (algebraMap XCoeff XFrac b) • D := by
        simpa using hnorm
      have hnorm'' :
          Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
          Polynomial.C ((algebraMap XCoeff XFrac) b) * D := by
        rw [← Polynomial.smul_eq_C_mul]
        exact hnorm'
      refine ⟨u, ?_⟩
      rw [hu]
      calc
        D * Polynomial.C ((algebraMap XCoeff XFrac) b) =
            Polynomial.C ((algebraMap XCoeff XFrac) b) * D := by
              simp [mul_comm]
        _ = Polynomial.map (algebraMap XCoeff XFrac)
              (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) := hnorm''.symm
    have hnorm_dvdP :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) ∣
        P.map (algebraMap XCoeff XFrac) := by
      exact (hassoc.dvd_iff_dvd_left).1 hDP
    have hnorm_dvdQ :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) ∣
        Q.map (algebraMap XCoeff XFrac) := by
      exact (hassoc.dvd_iff_dvd_left).1 hDQ
    have hprim_dvd_norm :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D := by
      exact Polynomial.primPart_dvd _
    have hmap_prim_dvd_norm :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) := by
      let A : Polynomial XCoeff :=
        IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D
      let B : Polynomial XCoeff := A.primPart
      have hprim_dvd_A : B ∣ A := by
        exact Polynomial.primPart_dvd A
      rcases hprim_dvd_A with ⟨r, hr⟩
      refine ⟨Polynomial.map (algebraMap XCoeff XFrac) r, ?_⟩
      calc
        Polynomial.map (algebraMap XCoeff XFrac)
            (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D) =
            Polynomial.map (algebraMap XCoeff XFrac) A := by
          rfl
        _ =
            Polynomial.map (algebraMap XCoeff XFrac) (B * r) := by
          rw [hr]
        _ =
            Polynomial.map (algebraMap XCoeff XFrac) B *
            Polynomial.map (algebraMap XCoeff XFrac) r := by
          rw [Polynomial.map_mul]
        _ =
            Polynomial.map (algebraMap XCoeff XFrac)
              (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart *
            Polynomial.map (algebraMap XCoeff XFrac) r := by
          rfl
    have hmap_prim_dvd_P :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        P.map (algebraMap XCoeff XFrac) := dvd_trans hmap_prim_dvd_norm hnorm_dvdP
    have hmap_prim_dvd_Q :
        Polynomial.map (algebraMap XCoeff XFrac)
          (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣
        Q.map (algebraMap XCoeff XFrac) := dvd_trans hmap_prim_dvd_norm hnorm_dvdQ
    have hprim_dvd_P :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣ P := by
      exact
        Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
          (K := XFrac)
          (p := (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart)
          (q := P)
          (Polynomial.isPrimitive_primPart _)
          hPprim
          hmap_prim_dvd_P
    have hprim_dvd_Q :
        (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart ∣ Q := by
      exact
        Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
          (K := XFrac)
          (p := (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart)
          (q := Q)
          (Polynomial.isPrimitive_primPart _)
          hQprim
          hmap_prim_dvd_Q
    have hunit_prim :
        IsUnit (IsLocalization.integerNormalization (nonZeroDivisors XCoeff) D).primPart :=
      hrel hprim_dvd_P hprim_dvd_Q
    exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hD hunit_prim

/-- Primitive `IsRelPrime` curries have nonzero resultant after mapping to the fraction field. -/
theorem isCoprime_fraction_map_of_isPrimitive
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hQprim : Q.IsPrimitive)
    (hrel : IsRelPrime P Q) :
    IsCoprime (P.map (algebraMap XCoeff XFrac))
              (Q.map (algebraMap XCoeff XFrac)) := by
  exact (isRelPrime_iff_isCoprime).1
    (isRelPrime_fraction_map_of_isPrimitive P Q hPprim hQprim hrel)

/-- Primitive `IsRelPrime` curries have nonzero resultant. -/
theorem resultant_ne_zero_of_isRelPrime_primitive_curry
    (p q : MvPolynomial (Fin 2) ℝ)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Polynomial.resultant (Curry0 p) (Curry0 q) ≠ 0 := by
  exact resultant_ne_zero_of_fraction_coprime (Curry0 p) (Curry0 q)
    (isCoprime_fraction_map_of_isPrimitive (Curry0 p) (Curry0 q) hpprim hqprim hrel)

/-- Specializing the coefficient variable does not increase the degree. -/
lemma specialized_natDegree_le_totalDegree
    (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (Specialized0 x p).natDegree ≤ p.totalDegree := by
  calc
    (Specialized0 x p).natDegree ≤ (Curry0 p).natDegree := by
      simpa [Specialized0] using
        (Polynomial.natDegree_map_le (f := coeffEval x) (p := Curry0 p))
    _ = MvPolynomial.degreeOf 0 p := by
      simpa [Curry0] using
        (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) p)
    _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0

/-- A nonzero specialization has finitely many common fibers. -/
lemma fiber_finite_of_one_specialization_nonzero
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0) :
    (FiberCommonZeros x p q).Finite := by
  rcases h with hp | hq
  · refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hp) ?_
    intro y hy
    exact hy.1
  · refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hq) ?_
    intro y hy
    exact hy.2

/-- The common fiber is bounded by the larger specialized degree. -/
lemma fiber_ncard_le_max_totalDegree
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0) :
    (FiberCommonZeros x p q).ncard ≤ max p.totalDegree q.totalDegree := by
  rcases h with hp | hq
  · have hsub :
        FiberCommonZeros x p q ⊆ (Specialized0 x p).rootSet ℝ := by
      intro y hy
      rw [Polynomial.mem_rootSet]
      exact ⟨hp, by simpa [Polynomial.IsRoot] using hy.1⟩
    have hrootset_eq :
        ({y | Polynomial.IsRoot (Specialized0 x p) y} : Set ℝ) =
          (Specialized0 x p).rootSet ℝ := by
      ext y
      rw [Polynomial.mem_rootSet]
      constructor
      · intro hy
        exact ⟨hp, by simpa [Polynomial.IsRoot] using hy⟩
      · intro hy
        exact by simpa [Polynomial.IsRoot] using hy.2
    have hroot :
        ((Specialized0 x p).rootSet ℝ).ncard ≤ (Specialized0 x p).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x p) ℝ)
    calc
      (FiberCommonZeros x p q).ncard ≤
          ((Specialized0 x p).rootSet ℝ).ncard := by
            exact Set.ncard_le_ncard hsub (hrootset_eq ▸ Polynomial.finite_setOf_isRoot hp)
      _ ≤ (Specialized0 x p).natDegree := hroot
      _ ≤ p.totalDegree := specialized_natDegree_le_totalDegree p x
      _ ≤ max p.totalDegree q.totalDegree := le_max_left _ _
  · have hsub :
        FiberCommonZeros x p q ⊆ (Specialized0 x q).rootSet ℝ := by
      intro y hy
      rw [Polynomial.mem_rootSet]
      exact ⟨hq, by simpa [Polynomial.IsRoot] using hy.2⟩
    have hrootset_eq :
        ({y | Polynomial.IsRoot (Specialized0 x q) y} : Set ℝ) =
          (Specialized0 x q).rootSet ℝ := by
      ext y
      rw [Polynomial.mem_rootSet]
      constructor
      · intro hy
        exact ⟨hq, by simpa [Polynomial.IsRoot] using hy⟩
      · intro hy
        exact by simpa [Polynomial.IsRoot] using hy.2
    have hroot :
        ((Specialized0 x q).rootSet ℝ).ncard ≤ (Specialized0 x q).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x q) ℝ)
    calc
      (FiberCommonZeros x p q).ncard ≤
          ((Specialized0 x q).rootSet ℝ).ncard := by
            exact Set.ncard_le_ncard hsub (hrootset_eq ▸ Polynomial.finite_setOf_isRoot hq)
      _ ≤ (Specialized0 x q).natDegree := hroot
      _ ≤ q.totalDegree := specialized_natDegree_le_totalDegree q x
      _ ≤ max p.totalDegree q.totalDegree := le_max_right _ _

/-- A coefficient-line factor in the plane. -/
noncomputable def CoeffLineFactor (x : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x

/-- The zero set of a coefficient polynomial, viewed as a vertical line in the plane. -/
def CoeffLineZeroSet (a : MvPolynomial (Fin 1) ℝ) : Set Point2 :=
  {p | MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0}

/-- Membership in `CoeffLineZeroSet` is just coefficient evaluation vanishing. -/
@[simp] lemma mem_CoeffLineZeroSet {a : MvPolynomial (Fin 1) ℝ}
    {p : Point2} :
    p ∈ CoeffLineZeroSet a ↔ MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0 := Iff.rfl

/-- A vanishing coefficient specialization forces the coefficient-line factor. -/
lemma coeffLineFactor_dvd_of_specialized_zero
    (p : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (hx : Specialized0 x p = 0) :
    CoeffLineFactor x ∣ p := by
  let XCoeffEquiv : XCoeff ≃+* Polynomial ℝ :=
    (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans
      (Polynomial.mapEquiv ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv))
  have hEval : ∀ r : XCoeff, Polynomial.eval x (XCoeffEquiv r) = coeffEval x r := by
    intro r
    refine MvPolynomial.induction_on
      (motive := fun r => Polynomial.eval x (XCoeffEquiv r) = coeffEval x r) r ?_ ?_ ?_
    · intro a
      simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
    · intro r s hr hs
      simp [hr, hs]
    · intro r n hr
      fin_cases n
      rw [map_mul, Polynomial.eval_mul]
      rw [hr]
      simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
  have hX :
      XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) =
        Polynomial.X - Polynomial.C x := by
    rw [map_sub]
    simp [XCoeffEquiv, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_apply]
  have hcoeff_div :
      ∀ n : ℕ, MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x ∣ (Curry0 p).coeff n := by
    intro n
    have hmap : Polynomial.map (coeffEval x) (Curry0 p) = 0 := by
      simpa [Specialized0] using hx
    have hcoeff0 : coeffEval x ((Curry0 p).coeff n) = 0 := by
      have hcoeffmap := congrArg (fun f => Polynomial.coeff f n) hmap
      simpa [Polynomial.coeff_map] using hcoeffmap
    have hroot :
        Polynomial.IsRoot (XCoeffEquiv ((Curry0 p).coeff n)) x := by
      simpa [Polynomial.IsRoot, hEval ((Curry0 p).coeff n)] using hcoeff0
    have hdiv :
        Polynomial.X - Polynomial.C x ∣ XCoeffEquiv ((Curry0 p).coeff n) := by
      exact (Polynomial.dvd_iff_isRoot).2 hroot
    have hdiv' :
        XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣
          XCoeffEquiv ((Curry0 p).coeff n) := by
      simpa [hX] using hdiv
    have hsymm : XCoeffEquiv.symm (XCoeffEquiv ((Curry0 p).coeff n)) =
        (Curry0 p).coeff n := by
      simpa using
        (Equiv.symm_apply_apply (e := XCoeffEquiv) ((Curry0 p).coeff n))
    simpa [hsymm] using (map_dvd_iff_dvd_symm XCoeffEquiv).1 hdiv'
  have hpoly :
      Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣ Curry0 p := by
    exact (Polynomial.C_dvd_iff_dvd_coeff
      (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) (Curry0 p)).2 hcoeff_div
  have hCurry0 :
      Curry0 (CoeffLineFactor x) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) := by
    rw [Curry0, CoeffLineFactor, map_sub]
    rw [show
        (MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) by
      simpa using (MvPolynomial.finSuccEquiv_X_succ (R := ℝ) (n := 1) (j := 0))]
    simp [MvPolynomial.finSuccEquiv_apply]
  have hdiv_curry : Curry0 (CoeffLineFactor x) ∣ Curry0 p := by
    simpa [hCurry0] using hpoly
  have hsymm_curve : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) = p := by
    simpa [Curry0] using
      (Equiv.symm_apply_apply (e := MvPolynomial.finSuccEquiv ℝ 1) p)
  have hdiv_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) :=
    (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).1 hdiv_curry
  simpa [hsymm_curve] using hdiv_symm

/-- If both specializations vanish, the coefficient-line factor would be a common divisor. -/
theorem not_both_specializations_zero_of_isRelPrime
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
  by_cases hp : Specialized0 x p = 0
  · by_cases hq : Specialized0 x q = 0
    · have hpdvd : CoeffLineFactor x ∣ p :=
        coeffLineFactor_dvd_of_specialized_zero p x hp
      have hqdvd : CoeffLineFactor x ∣ q :=
        coeffLineFactor_dvd_of_specialized_zero q x hq
      have hsymm_p : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) = p := by
        simpa [Curry0] using
          (Equiv.symm_apply_apply (e := MvPolynomial.finSuccEquiv ℝ 1) p)
      have hsymm_q : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 q) = q := by
        simpa [Curry0] using
          (Equiv.symm_apply_apply (e := MvPolynomial.finSuccEquiv ℝ 1) q)
      have hpdvd_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) :=
        by simpa [hsymm_p] using hpdvd
      have hqdvd_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 q) :=
        by simpa [hsymm_q] using hqdvd
      have hpdvd' : Curry0 (CoeffLineFactor x) ∣ Curry0 p := by
        exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).2 hpdvd_symm
      have hqdvd' : Curry0 (CoeffLineFactor x) ∣ Curry0 q := by
        exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).2 hqdvd_symm
      have hunit0 : IsUnit (Curry0 (CoeffLineFactor x)) := by
        exact (hrel.of_dvd_left hpdvd').isUnit_of_dvd hqdvd'
      have hunit : IsUnit (CoeffLineFactor x) := by
        have hsymm_factor : (MvPolynomial.finSuccEquiv ℝ 1).symm
            (Curry0 (CoeffLineFactor x)) = CoeffLineFactor x := by
          simpa [Curry0] using
            (Equiv.symm_apply_apply (e := MvPolynomial.finSuccEquiv ℝ 1)
              (CoeffLineFactor x))
        simpa [hsymm_factor] using
          IsUnit.map (MvPolynomial.finSuccEquiv ℝ 1).symm hunit0
      have hneq : (fun₀ | (1 : Fin 2) => 1) ≠ (0 : (Fin 2 →₀ ℕ)) := by
        intro h
        have := congrArg (fun m => m (1 : Fin 2)) h
        simp at this
      have hcoeff :
          MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x) = 1 := by
        have hXcoeff :
            MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1)
              (MvPolynomial.X (1 : Fin 2)) = 1 := by
          simp [MvPolynomial.coeff_X]
        have hCcoeff :
            MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1)
              (MvPolynomial.C x) = 0 := by
          rw [MvPolynomial.coeff_C]
          split_ifs with h0
          · exfalso
            exact hneq h0.symm
          · rfl
        rw [CoeffLineFactor, MvPolynomial.coeff_sub]
        simp [hXcoeff, hCcoeff]
      have hnil :
          IsNilpotent (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
        have hunit' := (MvPolynomial.isUnit_iff.mp hunit).2
        exact hunit' _ hneq
      have hcontr : False := by
        have hnot : ¬ IsNilpotent
            (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
          simpa [hcoeff] using (not_isNilpotent_one (R := ℝ))
        exact hnot hnil
      exact False.elim hcontr
    · exact Or.inr hq
  · exact Or.inl hp

/-- Nonzero coefficient polynomials have finite real root sets. -/
lemma finite_coeff_roots_of_ne_zero
    (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).Finite := by
  have hr' : XCoeffEquiv r ≠ 0 := by
    intro h0
    have h0' : XCoeffEquiv r = XCoeffEquiv 0 := by
      simpa using h0
    exact hr (XCoeffEquiv.injective h0')
  have hrootset_eq :
      CoeffRootSet r = (XCoeffEquiv r).rootSet ℝ := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      exact ⟨hr', by
        simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx⟩
    · intro hx
      simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx.2
  have hfinRoots : {x : ℝ | Polynomial.IsRoot (XCoeffEquiv r) x}.Finite :=
    Polynomial.finite_setOf_isRoot hr'
  have hsubset : (XCoeffEquiv r).rootSet ℝ ⊆ {x : ℝ | Polynomial.IsRoot (XCoeffEquiv r) x} := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    exact hx.2
  rw [hrootset_eq]
  exact Set.Finite.subset hfinRoots hsubset

/-- The real root set of a nonzero coefficient polynomial is bounded by its degree. -/
lemma ncard_coeff_roots_le_totalDegree
    (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).ncard ≤ r.totalDegree := by
  have hr' : XCoeffEquiv r ≠ 0 := by
    intro h0
    have h0' : XCoeffEquiv r = XCoeffEquiv 0 := by
      simpa using h0
    exact hr (XCoeffEquiv.injective h0')
  have hrootset_eq :
      CoeffRootSet r = (XCoeffEquiv r).rootSet ℝ := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      exact ⟨hr', by
        simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx⟩
    · intro hx
      simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx.2
  have hdeg : (XCoeffEquiv r).natDegree ≤ r.totalDegree := by
    calc
      (XCoeffEquiv r).natDegree = ((MvPolynomial.finSuccEquiv ℝ 0) r).natDegree := by
        simpa [XCoeffEquiv] using
          (Polynomial.natDegree_map_eq_of_injective
            ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.injective)
            ((MvPolynomial.finSuccEquiv ℝ 0) r))
      _ = MvPolynomial.degreeOf 0 r := by
        simpa using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
      _ ≤ r.totalDegree := MvPolynomial.degreeOf_le_totalDegree r 0
  have hroot :
      (CoeffRootSet r).ncard ≤ (XCoeffEquiv r).natDegree := by
    simpa [hrootset_eq] using (Polynomial.ncard_rootSet_le (XCoeffEquiv r) ℝ)
  exact le_trans hroot hdeg

/-- The real root set of a nonzero coefficient polynomial is bounded by its `degreeOf`. -/
lemma ncard_coeff_roots_le_degreeOf
    (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).ncard ≤ MvPolynomial.degreeOf (0 : Fin 1) r := by
  have hr' : XCoeffEquiv r ≠ 0 := by
    intro h0
    have h0' : XCoeffEquiv r = XCoeffEquiv 0 := by
      simpa using h0
    exact hr (XCoeffEquiv.injective h0')
  have hrootset_eq :
      CoeffRootSet r = (XCoeffEquiv r).rootSet ℝ := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      exact ⟨hr', by
        simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx⟩
    · intro hx
      simpa [CoeffRootSet, coeffEval_eq_eval_XCoeffEquiv] using hx.2
  have hroot :
      (CoeffRootSet r).ncard ≤ (XCoeffEquiv r).natDegree := by
    simpa [hrootset_eq] using (Polynomial.ncard_rootSet_le (XCoeffEquiv r) ℝ)
  have hdeg : (XCoeffEquiv r).natDegree = MvPolynomial.degreeOf (0 : Fin 1) r := by
    calc
      (XCoeffEquiv r).natDegree = ((MvPolynomial.finSuccEquiv ℝ 0) r).natDegree := by
        simpa [XCoeffEquiv] using
          (Polynomial.natDegree_map_eq_of_injective
            ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.injective)
            ((MvPolynomial.finSuccEquiv ℝ 0) r))
      _ = MvPolynomial.degreeOf (0 : Fin 1) r := by
        simpa using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
  simpa [hdeg] using hroot

/-- The zero set of a coefficient-line factor is the corresponding vertical line. -/
lemma coeff_line_factor_zeroSet
    (x : ℝ) :
    PlaneCurveZeroSet (CoeffLineFactor x) = {z : Point2 | coeffCoord z = x} := by
  ext z
  constructor
  · intro hz
    have hz' : coeffCoord z - x = 0 := by
      simpa [PlaneCurveZeroSet, CoeffLineFactor, coeffCoord] using hz
    exact sub_eq_zero.mp hz'
  · intro hz
    rw [mem_PlaneCurveZeroSet]
    have hz' : coeffCoord z - x = 0 := sub_eq_zero.mpr hz
    simpa [CoeffLineFactor, coeffCoord] using hz'

/-- Two nonzero coefficient polynomials have a finite common real root set. -/
lemma univariate_coeff_common_roots_finite
    (a b : XCoeff) (ha0 : a ≠ 0) :
    (CoeffRootSet a ∩ CoeffRootSet b).Finite := by
  refine Set.Finite.subset (finite_coeff_roots_of_ne_zero a ha0) ?_
  intro x hx
  exact hx.1

/-- The common real root set of `a` is bounded by `a.totalDegree`. -/
lemma univariate_coeff_common_roots_ncard_le
    (a b : XCoeff) (ha0 : a ≠ 0) :
    (CoeffRootSet a ∩ CoeffRootSet b).ncard ≤ a.totalDegree := by
  have hsubset : CoeffRootSet a ∩ CoeffRootSet b ⊆ CoeffRootSet a := by
    intro x hx
    exact hx.1
  calc
    (CoeffRootSet a ∩ CoeffRootSet b).ncard ≤ (CoeffRootSet a).ncard := by
      exact Set.ncard_le_ncard hsubset (finite_coeff_roots_of_ne_zero a ha0)
    _ ≤ a.totalDegree := ncard_coeff_roots_le_totalDegree a ha0

/-- The coefficient-line branch of the pair-intersection bound. -/
theorem coeffline_nonvertical_pair_intersection_bound
    (a : XCoeff) (q : MvPolynomial (Fin 2) ℝ)
    (ha0 : a ≠ 0) (hq0 : q ≠ 0)
    (hadeg : a.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hnotDiv :
      ∀ x : ℝ,
        MvPolynomial.eval (fun _ : Fin 1 => x) a = 0 →
          ¬ CoeffLineFactor x ∣ q) :
    (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).Finite ∧
      (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard ≤ d₁ * d₂ := by
  classical
  have hrootFinite : (CoeffRootSet a).Finite := finite_coeff_roots_of_ne_zero a ha0
  let rootFinset := hrootFinite.toFinset
  let fiberSet : ℝ → Set Point2 :=
    fun x => {z : Point2 | coeffCoord z = x ∧ z ∈ PlaneCurveZeroSet q}
  have hcover : CoeffLineZeroSet a ∩ PlaneCurveZeroSet q = ⋃ x ∈ rootFinset, fiberSet x := by
    ext z
    constructor
    · intro hz
      have hxroot : coeffCoord z ∈ CoeffRootSet a := by
        simpa [CoeffLineZeroSet, CoeffRootSet, coeffCoord] using hz.1
      have hx : coeffCoord z ∈ rootFinset := by
        simpa [rootFinset] using hxroot
      have hzfiber : z ∈ fiberSet (coeffCoord z) := by
        exact ⟨rfl, hz.2⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨coeffCoord z, Set.mem_iUnion.2 ?_⟩
      exact ⟨hx, hzfiber⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨x, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hx, hz⟩
      rcases hz with ⟨hcoeff, hzq⟩
      have hxroot : x ∈ CoeffRootSet a := by
        simpa [rootFinset] using hx
      have hzline : z ∈ CoeffLineZeroSet a := by
        rw [mem_CoeffLineZeroSet]
        change MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) a = 0
        rw [hcoeff]
        simpa [CoeffRootSet] using hxroot
      exact ⟨hzline, hzq⟩
  have hfiber_finite : ∀ x ∈ rootFinset, (fiberSet x).Finite := by
    intro x hx
    have hxroot : x ∈ CoeffRootSet a := by
      simpa [rootFinset] using hx
    have hqneq : Specialized0 x q ≠ 0 := by
      intro hzero
      exact hnotDiv x hxroot (coeffLineFactor_dvd_of_specialized_zero q x hzero)
    have htarget_finite : ((Specialized0 x q).rootSet ℝ).Finite := by
      have hfinRoots : {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y}.Finite :=
        Polynomial.finite_setOf_isRoot hqneq
      have hsubset : (Specialized0 x q).rootSet ℝ ⊆
          {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y} := by
        intro y hy
        rw [Polynomial.mem_rootSet] at hy
        exact hy.2
      exact Set.Finite.subset hfinRoots hsubset
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) ((Specialized0 x q).rootSet ℝ) := by
      intro z hz
      rcases hz with ⟨hcoeff, hzq⟩
      rw [Polynomial.mem_rootSet]
      constructor
      · exact hqneq
      · have hzspec : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
          rw [← eval_eq_specialized_eval q z]
          exact hzq
        simpa [hcoeff] using hzspec
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i <;> fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    haveI : ((Specialized0 x q).rootSet ℝ).Finite := htarget_finite
    exact Set.Finite.of_injOn hmapsTo hinj htarget_finite
  have hfiber_bound : ∀ x ∈ rootFinset, (fiberSet x).ncard ≤ d₂ := by
    intro x hx
    have hxroot : x ∈ CoeffRootSet a := by
      simpa [rootFinset] using hx
    have hqneq : Specialized0 x q ≠ 0 := by
      intro hzero
      exact hnotDiv x hxroot (coeffLineFactor_dvd_of_specialized_zero q x hzero)
    have htarget_finite : ((Specialized0 x q).rootSet ℝ).Finite := by
      have hfinRoots : {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y}.Finite :=
        Polynomial.finite_setOf_isRoot hqneq
      have hsubset : (Specialized0 x q).rootSet ℝ ⊆
          {y : ℝ | Polynomial.IsRoot (Specialized0 x q) y} := by
        intro y hy
        rw [Polynomial.mem_rootSet] at hy
        exact hy.2
      exact Set.Finite.subset hfinRoots hsubset
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) ((Specialized0 x q).rootSet ℝ) := by
      intro z hz
      rcases hz with ⟨hcoeff, hzq⟩
      rw [Polynomial.mem_rootSet]
      constructor
      · exact hqneq
      · have hzspec : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
          rw [← eval_eq_specialized_eval q z]
          exact hzq
        simpa [hcoeff] using hzspec
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i <;> fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    have hle_root : (fiberSet x).ncard ≤ ((Specialized0 x q).rootSet ℝ).ncard := by
      haveI : ((Specialized0 x q).rootSet ℝ).Finite := htarget_finite
      exact Set.ncard_le_ncard_of_injOn elimCoord hmapsTo hinj
    have hroot : ((Specialized0 x q).rootSet ℝ).ncard ≤ (Specialized0 x q).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x q) ℝ)
    have hdeg : (Specialized0 x q).natDegree ≤ d₂ := by
      exact le_trans (specialized_natDegree_le_totalDegree q x) hqdeg
    exact le_trans hle_root (le_trans hroot hdeg)
  have hrootcard : rootFinset.card ≤ d₁ := by
    have hrootcard' : rootFinset.card = (CoeffRootSet a).ncard := by
      simpa [rootFinset] using
        (Set.ncard_eq_toFinset_card (CoeffRootSet a) hrootFinite).symm
    calc
      rootFinset.card = (CoeffRootSet a).ncard := hrootcard'
      _ ≤ a.totalDegree := ncard_coeff_roots_le_totalDegree a ha0
      _ ≤ d₁ := hadeg
  have hunion_ncard : (⋃ x ∈ rootFinset, fiberSet x).ncard ≤ d₁ * d₂ := by
    refine le_trans (Finset.set_ncard_biUnion_le rootFinset fiberSet) ?_
    have hsum : ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, d₂ := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hfiber_bound x hx
    have hsum' : ∑ x ∈ rootFinset, d₂ = rootFinset.card * d₂ := by
      simp
    calc
      ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, d₂ := hsum
      _ = rootFinset.card * d₂ := hsum'
      _ ≤ d₁ * d₂ := Nat.mul_le_mul_right _ hrootcard
  have hunion_finite : (⋃ x ∈ rootFinset, fiberSet x).Finite := by
    have hfinite :
        (⋃ x ∈ (rootFinset : Set ℝ), fiberSet x).Finite := by
      exact Set.Finite.biUnion rootFinset.finite_toSet (by
        intro x hx
        exact hfiber_finite x (by simpa [rootFinset] using hx))
    simpa only [Finset.mem_coe] using hfinite
  have hfinite : (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).Finite := by
    rw [hcover]
    exact hunion_finite
  have hncard : (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard ≤ d₁ * d₂ := by
    calc
      (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard = (⋃ x ∈ rootFinset, fiberSet x).ncard := by
        rw [hcover]
      _ ≤ d₁ * d₂ := hunion_ncard
  exact ⟨hfinite, hncard⟩

/-- If the coefficient roots have empty intersection, the corresponding coefficient-line intersections are empty. -/
theorem coeffline_coeffline_pair_intersection_empty_of_no_common_real_root
    (a b : XCoeff)
    (hnoRoot : CoeffRootSet a ∩ CoeffRootSet b = ∅) :
    CoeffLineZeroSet a ∩ CoeffLineZeroSet b = ∅ := by
  ext z
  constructor
  · intro hz
    have hx : coeffCoord z ∈ CoeffRootSet a ∩ CoeffRootSet b := by
      simpa [CoeffLineZeroSet, CoeffRootSet, coeffCoord] using hz
    have hfalse : False := by
      simpa [hnoRoot] using hx
    exact False.elim hfalse
  · intro hz
    exact False.elim (by simpa using hz)

/-- An irreducible plane polynomial with positive eliminated-coordinate degree has primitive curry. -/
lemma curry_isPrimitive_of_irreducible_positive_natDegree
    (h : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h)
    (hpos : 0 < (Curry0 h).natDegree) :
    (Curry0 h).IsPrimitive := by
  have hnd : ¬ (Curry0 h).natDegree = 0 := by
    exact Nat.ne_of_gt hpos
  simpa [Curry0] using
    (hh.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv).isPrimitive hnd

/-- Nonassociated irreducible plane polynomials have coprime curries. -/
lemma curry_isRelPrime_of_nonassociated_irreducibles
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k) :
    IsRelPrime (Curry0 h) (Curry0 k) := by
  have hhC : Irreducible (Curry0 h) := by
    simpa [Curry0] using (hh.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv)
  refine (hhC.isRelPrime_iff_not_dvd).2 ?_
  intro hdiv
  have hkdiv' : h ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 k) := by
    exact (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).1 hdiv
  have hkdiv : h ∣ k := by
    simpa [Curry0] using hkdiv'
  exact hnot (hh.associated_of_dvd hk hkdiv)

/-- If `Curry0 h` has degree zero, then the plane zero set is a coefficient line. -/
lemma planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero
    (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0) :
    PlaneCurveZeroSet h = CoeffLineZeroSet ((Curry0 h).coeff 0) := by
  have hC : Curry0 h = Polynomial.C ((Curry0 h).coeff 0) := by
    simpa using (Polynomial.eq_C_of_natDegree_eq_zero hdeg0)
  ext z
  constructor
  · intro hz
    have hz' : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) h) = 0 := by
      rw [← eval_eq_specialized_eval h z]
      simpa using hz
    have hspec :
        Specialized0 (coeffCoord z) h =
          Polynomial.C
            (MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) ((Curry0 h).coeff 0)) := by
      rw [Specialized0, hC]
      simp [coeffEval]
    rw [mem_CoeffLineZeroSet]
    rw [hspec] at hz'
    simpa using hz'
  · intro hz
    rw [mem_PlaneCurveZeroSet]
    rw [eval_eq_specialized_eval h z]
    have hspec :
        Specialized0 (coeffCoord z) h =
          Polynomial.C
            (MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) ((Curry0 h).coeff 0)) := by
      rw [Specialized0, hC]
      simp [coeffEval]
    rw [hspec]
    simpa using hz

/-- A zero-degree curry has nonzero constant coefficient when the polynomial is nonzero. -/
lemma coeff_zero_ne_zero_of_curry_natDegree_zero
    (h : MvPolynomial (Fin 2) ℝ)
    (hh0 : h ≠ 0)
    (hdeg0 : (Curry0 h).natDegree = 0) :
    (Curry0 h).coeff 0 ≠ 0 := by
  intro hzero
  have hC : Curry0 h = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, hzero]
    simp
  exact hh0 (by
    apply (MvPolynomial.finSuccEquiv ℝ 1).injective
    simpa [Curry0] using hC)

/-- The constant coefficient of a curry has total degree at most the original polynomial. -/
lemma coeff_zero_totalDegree_le
    (h : MvPolynomial (Fin 2) ℝ) :
    ((Curry0 h).coeff 0) ≠ 0 →
      ((Curry0 h).coeff 0).totalDegree ≤ h.totalDegree := by
  intro h0
  have hle :=
    MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := ℝ) (n := 1) h 0 h0
  simpa [Curry0] using hle

/-- A divisor of an irreducible polynomial is associated to it if the divisor is not a unit. -/
lemma associated_of_irreducible_dvd_nonunit
    {R : Type*} [Monoid R] {p d : R}
    (hp : Irreducible p) (hdp : d ∣ p) (hdnu : ¬ IsUnit d) :
    Associated p d := by
  rcases hp.dvd_iff.mp hdp with hdunit | hassoc
  · exact False.elim (hdnu hdunit)
  · exact hassoc

/-- The coefficient-line factor is never a unit. -/
lemma coeffLineFactor_not_isUnit
    (x : ℝ) :
    ¬ IsUnit (CoeffLineFactor x) := by
  intro h
  have hne : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    simp
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (CoeffLineFactor x) = 1 := by
    have hXcoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)
          (MvPolynomial.X (1 : Fin 2)) = 1 := by
      simp [MvPolynomial.coeff_X]
    have hCcoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (MvPolynomial.C x) = 0 := by
      rw [MvPolynomial.coeff_C]
      split_ifs with h0
      · exfalso
        exact hne h0.symm
      · rfl
    rw [CoeffLineFactor, MvPolynomial.coeff_sub]
    simp [hXcoeff, hCcoeff]
  rcases (MvPolynomial.isUnit_iff.mp h) with ⟨_, hnil⟩
  have hnil1 :
      IsNilpotent
        (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (CoeffLineFactor x)) := by
    exact hnil _ hne
  rw [hcoeff] at hnil1
  exact not_isNilpotent_one hnil1

/-- A root of the zero-degree curry gives the coefficient-line factor. -/
lemma coeffLineFactor_dvd_of_curry_natDegree_zero_root
    (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    CoeffLineFactor x ∣ h := by
  have hspec : Specialized0 x h = 0 := by
    rw [Specialized0, Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
    simp [coeffEval, hxroot]
  exact coeffLineFactor_dvd_of_specialized_zero h x hspec

/-- A coefficient-line factor cannot divide the second polynomial in the nonassociated zero-degree case. -/
lemma not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    ¬ CoeffLineFactor x ∣ k := by
  intro hkdvd
  have hhdvd : CoeffLineFactor x ∣ h :=
    coeffLineFactor_dvd_of_curry_natDegree_zero_root h hdeg0 hxroot
  have hassoc_line : Associated h (CoeffLineFactor x) :=
    associated_of_irreducible_dvd_nonunit hh hhdvd (coeffLineFactor_not_isUnit x)
  have hdiv : h ∣ k := by
    exact (hassoc_line.dvd_iff_dvd_left).2 hkdvd
  exact hnot (hh.associated_of_dvd hk hdiv)

/-- The zero-degree / positive-degree coefficient-line case has the expected bound. -/
theorem zeroCurry_nonvertical_pair_intersection_bound
    (h k : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kpos : 0 < (Curry0 k).natDegree) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by
  have hzero : ((Curry0 h).coeff 0) ≠ 0 := by
    exact coeff_zero_ne_zero_of_curry_natDegree_zero h hh.ne_zero hdeg0
  have hcoeffdeg : ((Curry0 h).coeff 0).totalDegree ≤ d₁ := by
    exact le_trans (coeff_zero_totalDegree_le h hzero) hdeg
  have hnotDiv :
      ∀ x : ℝ,
        MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0 →
          ¬ CoeffLineFactor x ∣ k := by
    intro x hxroot
    exact not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated h k hh hk hnot hdeg0 hxroot
  have hline :
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k) =
        (CoeffLineZeroSet ((Curry0 h).coeff 0) ∩ PlaneCurveZeroSet k) := by
    rw [planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero h hdeg0]
  simpa [hline] using
    (coeffline_nonvertical_pair_intersection_bound ((Curry0 h).coeff 0) k hzero hk.ne_zero
      hcoeffdeg kdeg kpos hnotDiv)

/-- The zero-degree / zero-degree coefficient-line case is empty. -/
lemma no_common_coeff_root_of_zero_curry_nonassociated
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    CoeffRootSet ((Curry0 h).coeff 0) ∩ CoeffRootSet ((Curry0 k).coeff 0) = ∅ := by
  ext x
  constructor
  · intro hx
    have hroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0 := hx.1
    have hdivk : ¬ CoeffLineFactor x ∣ k :=
      not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated h k hh hk hnot hdeg0 hroot
    have hdivk' : CoeffLineFactor x ∣ k :=
      coeffLineFactor_dvd_of_curry_natDegree_zero_root k kdeg0 hx.2
    exact False.elim (hdivk hdivk')
  · intro hx
    exact False.elim (by simpa using hx)

/-- The zero-degree / zero-degree plane intersection is empty. -/
lemma zeroCurry_zeroCurry_pair_intersection_empty
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k = ∅ := by
  have hnoRoot :
      CoeffRootSet ((Curry0 h).coeff 0) ∩ CoeffRootSet ((Curry0 k).coeff 0) = ∅ := by
    exact no_common_coeff_root_of_zero_curry_nonassociated h k hh hk hnot hdeg0 kdeg0
  rw [planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero h hdeg0,
    planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero k kdeg0]
  exact coeffline_coeffline_pair_intersection_empty_of_no_common_real_root _ _ hnoRoot

/-- The zero-degree / zero-degree plane intersection is finite with any bound. -/
lemma zeroCurry_zeroCurry_pair_intersection_bound
    (h k : MvPolynomial (Fin 2) ℝ)
    {B : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    (kdeg0 : (Curry0 k).natDegree = 0) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ B := by
  have hempty : PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k = ∅ :=
    zeroCurry_zeroCurry_pair_intersection_empty h k hh hk hnot hdeg0 kdeg0
  refine ⟨by simpa [hempty], ?_⟩
  simpa [hempty]

/-- The multivariate polynomial ring over `ℝ` is normalized. -/
noncomputable instance : NormalizationMonoid (MvPolynomial (Fin 2) ℝ) :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Associated plane polynomials have the same total degree. -/
lemma totalDegree_eq_of_associated
    {p q : MvPolynomial (Fin 2) ℝ} (h : Associated p q) :
    p.totalDegree = q.totalDegree := by
  by_cases hp0 : p = 0
  · have hq0 : q = 0 := by
      by_contra hq0
      have hpnonzero : p ≠ 0 := (h.ne_zero_iff).2 hq0
      exact hpnonzero hp0
    subst hp0
    subst hq0
    simp
  · have hq0 : q ≠ 0 := (h.ne_zero_iff).1 hp0
    have hpq : p ∣ q := (h.dvd_iff_dvd_right).mp dvd_rfl
    have hqp : q ∣ p := (h.dvd_iff_dvd_left).mp dvd_rfl
    exact le_antisymm
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hpq hq0)
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hqp hp0)

/-- A simple arithmetic helper for the derivative-degree argument. -/
lemma helper_sum_sub_single_le (v : Fin 2 →₀ ℕ) (i : Fin 2) (hvi : v i ≠ 0) :
    ((v - Finsupp.single i 1).sum (fun _ e => e)) ≤ ((v.sum (fun _ e => e)) - 1) := by
  fin_cases i
  · have h0 : 1 ≤ v 0 := Nat.pos_of_ne_zero hvi
    simp [Finsupp.sum_fintype]
    omega
  · have h1 : 1 ≤ v 1 := Nat.pos_of_ne_zero hvi
    simp [Finsupp.sum_fintype]
    omega

/-- A partial derivative drops the total degree by at most one when the curve has positive degree. -/
lemma totalDegree_pderiv_le_sub_one
    (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2)
    (hpos : 0 < h.totalDegree) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree - 1 := by
  classical
  let s : Finset (Fin 2 →₀ ℕ) := h.support
  let c : (Fin 2 →₀ ℕ) → ℝ := fun v => MvPolynomial.coeff v h
  have hsum : h = ∑ v ∈ s, MvPolynomial.monomial v (c v) := by
    subst s c
    exact MvPolynomial.as_sum h
  have hderiv :
      MvPolynomial.pderiv i h = ∑ v ∈ s, MvPolynomial.pderiv i (MvPolynomial.monomial v (c v)) := by
    rw [hsum]
    simp
  have hterm : ∀ v ∈ s, (MvPolynomial.pderiv i (MvPolynomial.monomial v (c v))).totalDegree ≤
      h.totalDegree - 1 := by
    intro v hv
    by_cases hvi : v i = 0
    · simp [hvi, hpos]
    · have hcoeff : (c v) * (v i : ℝ) ≠ 0 := by
        exact mul_ne_zero
          (by simpa [c] using (MvPolynomial.mem_support_iff.mp hv))
          (by exact_mod_cast hvi)
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.totalDegree_monomial _ hcoeff]
      have hvle : v.sum (fun _ e => e) ≤ h.totalDegree := MvPolynomial.le_totalDegree hv
      have hsumle :
          (v - Finsupp.single i 1).sum (fun _ e => e) ≤ v.sum (fun _ e => e) - 1 := by
        exact helper_sum_sub_single_le v i hvi
      have hsub : v.sum (fun _ e => e) - 1 ≤ h.totalDegree - 1 := by
        exact Nat.sub_le_sub_right hvle 1
      exact le_trans hsumle hsub
  rw [hderiv]
  exact MvPolynomial.totalDegree_finsetSum_le hterm

/-- The partial derivative of a plane polynomial does not increase total degree. -/
lemma totalDegree_pderiv_le
    (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    (MvPolynomial.pderiv i h).totalDegree ≤ h.totalDegree := by
  by_cases hpos : 0 < h.totalDegree
  · have hle := totalDegree_pderiv_le_sub_one h i hpos
    omega
  · have hdeg0 : h.totalDegree = 0 := by omega
    have hC : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
    rw [hC]
    simp

/-- A nonzero partial derivative of a positive-degree plane polynomial has strictly smaller degree. -/
lemma totalDegree_pderiv_lt_of_nonzero
    (h : MvPolynomial (Fin 2) ℝ) {i : Fin 2}
    (hpos : 0 < h.totalDegree)
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    (MvPolynomial.pderiv i h).totalDegree < h.totalDegree := by
  have hle := totalDegree_pderiv_le_sub_one h i hpos
  omega

/-- Normalized factors of a plane polynomial are irreducible. -/
lemma normalized_factor_irreducible
    {p h : MvPolynomial (Fin 2) ℝ}
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    Irreducible h := by
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh

/-- Normalized factors of a nonzero plane polynomial have positive total degree. -/
lemma normalized_factor_totalDegree_pos
    {p h : MvPolynomial (Fin 2) ℝ}
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    0 < h.totalDegree := by
  have hirr : Irreducible h := normalized_factor_irreducible hh
  by_contra hpos
  have hdeg0 : h.totalDegree = 0 := by omega
  have hEq : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
  have hcoeff0 : MvPolynomial.coeff 0 h ≠ 0 := by
    intro hzero
    exact hirr.ne_zero (by rw [hEq, hzero]; simp)
  have hunit : IsUnit h := by
    rw [hEq]
    exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
      (isUnit_iff_ne_zero.mpr hcoeff0)
  exact hirr.not_isUnit hunit

/-- A small helper for the normalized-factor cardinality bound. -/
lemma helper_card_le_sum_of_pos
    (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ h ∈ s, 0 < h.totalDegree) :
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 0 < a.totalDegree := hs a (by simp)
      have hs' : ∀ h ∈ s, 0 < h.totalDegree := by
        intro h hh
        exact hs h (by simp [hh])
      have ih' := ih hs'
      simp [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, ha] at ih' ⊢
      omega

/-- A normalized factor multiset has total degree equal to the total degree of its product. -/
lemma helper_multiset_prod_totalDegree_eq_sum
    (s : Multiset (MvPolynomial (Fin 2) ℝ))
    (hs : ∀ h ∈ s, h ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a ≠ 0 := hs a (by simp)
      have hs' : ∀ h ∈ s, h ≠ 0 := by
        intro h hh
        exact hs h (by simp [hh])
      have hs0 : (0 : MvPolynomial (Fin 2) ℝ) ∉ s := by
        intro h0
        exact (hs' 0 h0) rfl
      have ih' := ih hs'
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [MvPolynomial.totalDegree_mul_of_isDomain ha (Multiset.prod_ne_zero hs0)]
      rw [ih']

/-- The normalized factors of a nonzero plane polynomial are not too many. -/
lemma card_normalizedFactors_le_totalDegree
    {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).card ≤ p.totalDegree := by
  let s : Multiset (MvPolynomial (Fin 2) ℝ) := UniqueFactorizationMonoid.normalizedFactors p
  have hspos : ∀ h ∈ s, 0 < h.totalDegree := by
    intro h hh
    simpa [s] using (normalized_factor_totalDegree_pos (p := p) (h := h) hh)
  have hscard : s.card ≤ (s.map MvPolynomial.totalDegree).sum :=
    helper_card_le_sum_of_pos s hspos
  have hsnonzero : ∀ h ∈ s, h ≠ 0 := by
    intro h hh
    exact (normalized_factor_irreducible (p := p) (h := h) hh).ne_zero
  have hprod : s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum :=
    helper_multiset_prod_totalDegree_eq_sum s hsnonzero
  have hassoc : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors hp0)
  have hdeg : s.prod.totalDegree = p.totalDegree := totalDegree_eq_of_associated hassoc
  calc
    s.card ≤ (s.map MvPolynomial.totalDegree).sum := hscard
    _ = s.prod.totalDegree := hprod.symm
    _ = p.totalDegree := hdeg

/-- A normalized factor of a nonzero plane polynomial has degree at most the polynomial's degree. -/
lemma normalized_factor_degree_le
    {p h : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0)
    (hh : h ∈ UniqueFactorizationMonoid.normalizedFactors p) :
    h.totalDegree ≤ p.totalDegree := by
  have hdiv : h ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh
  exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hp0

/-- The zero set of a plane polynomial is covered by the zero sets of its normalized factors. -/
lemma zeroSet_subset_normalizedFactor_union
    {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    PlaneCurveZeroSet p ⊆
      ⋃ h ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        PlaneCurveZeroSet h := by
  classical
  intro z hz
  let s : Multiset (MvPolynomial (Fin 2) ℝ) := UniqueFactorizationMonoid.normalizedFactors p
  have hs : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors hp0)
  have hsp : Associated (MvPolynomial.eval (fun i => z i) s.prod)
      (MvPolynomial.eval (fun i => z i) p) := by
    exact Associated.map (MvPolynomial.eval (fun i => z i)) hs
  have hzero : MvPolynomial.eval (fun i => z i) s.prod = 0 := by
    exact (hsp.eq_zero_iff).2 hz
  have hzero' :
      (s.map (fun h : MvPolynomial (Fin 2) ℝ => MvPolynomial.eval (fun i => z i) h)).prod = 0 := by
    simpa [s, map_multiset_prod] using hzero
  have hmem : 0 ∈ s.map (fun h : MvPolynomial (Fin 2) ℝ => MvPolynomial.eval (fun i => z i) h) := by
    simpa using (Multiset.prod_eq_zero_iff.mp hzero')
  rcases Multiset.mem_map.mp hmem with ⟨h, hh, hhz⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨h, ?_⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨by simpa [s] using hh, ?_⟩
  simpa [PlaneCurveZeroSet] using hhz

/-!
The historical Bezout, singularity, and Point4 topology packets below are not
used by the active Lean import tree. They are currently under repair and are
quarantined from the active build surface so the live endpoint route can
compile against the minimal theorem interface it actually consumes.
-/
/-
/- Each Sylvester matrix entry has degree bounded by the larger input degree bound. -/
set_option maxHeartbeats 400000
lemma degreeOf_sylvester_entry_le
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (i j : Fin ((Curry0 p).natDegree + (Curry0 q).natDegree))
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1)
      (Polynomial.sylvester (Curry0 p) (Curry0 q)
        (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤
      max d₁ d₂ := by
  classical
  by_cases hj : (↑j : ℕ) < (Curry0 p).natDegree
  · by_cases hcond : j ≤ i ∧ ↑i ≤ ↑j + (Curry0 q).natDegree
    · have hentry :
        Polynomial.sylvester (Curry0 p) (Curry0 q) (Curry0 p).natDegree (Curry0 q).natDegree i j =
          (Curry0 q).coeff (↑i - ↑j) := by
        simp [Polynomial.sylvester, Fin.addCases, hj, hcond]
      rw [hentry]
      have hdeg :
          MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff (↑i - ↑j)) ≤ max d₁ d₂ := by
        calc
          MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff (↑i - ↑j)) ≤
              MvPolynomial.degreeOf (1 : Fin 2) q := by
            simpa [Curry0] using
              (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := q)
                (j := 0) (i := ↑i - ↑j))
          _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q 1
          _ ≤ d₂ := hqdeg
          _ ≤ max d₁ d₂ := le_max_right _ _
      exact hdeg
    · have hentry :
        Polynomial.sylvester (Curry0 p) (Curry0 q) (Curry0 p).natDegree (Curry0 q).natDegree i j = 0 := by
        simp [Polynomial.sylvester, Fin.addCases, hj, hcond]
      rw [hentry]
      simp
  · by_cases hcond : ↑j ≤ ↑i + (Curry0 p).natDegree ∧
      ↑i ≤ ↑j - (Curry0 p).natDegree + (Curry0 p).natDegree
    · have hentry :
        Polynomial.sylvester (Curry0 p) (Curry0 q) (Curry0 p).natDegree (Curry0 q).natDegree i j =
          (Curry0 p).coeff (↑i - (↑j - (Curry0 p).natDegree)) := by
        simp [Polynomial.sylvester, Fin.addCases, hj, hcond]
      rw [hentry]
      have hdeg :
          MvPolynomial.degreeOf (0 : Fin 1)
              ((Curry0 p).coeff (↑i - (↑j - (Curry0 p).natDegree))) ≤ max d₁ d₂ := by
        calc
          MvPolynomial.degreeOf (0 : Fin 1)
              ((Curry0 p).coeff (↑i - (↑j - (Curry0 p).natDegree))) ≤
              MvPolynomial.degreeOf (1 : Fin 2) p := by
            simpa [Curry0] using
              (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := p)
                (j := 0) (i := ↑i - (↑j - (Curry0 p).natDegree)))
          _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 1
          _ ≤ d₁ := hpdeg
          _ ≤ max d₁ d₂ := le_max_left _ _
      exact hdeg
    · have hentry :
          Polynomial.sylvester (Curry0 p) (Curry0 q) (Curry0 p).natDegree (Curry0 q).natDegree i j = 0 := by
        simp [Polynomial.sylvester, Fin.addCases, hj, hcond]
      rw [hentry]
      simp

/- Each Sylvester matrix entry is bounded by the degree bound of the polynomial in its column block. -/
lemma degreeOf_sylvester_entry_bound
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (i j : Fin ((Curry0 p).natDegree + (Curry0 q).natDegree))
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1)
      (Polynomial.sylvester (Curry0 p) (Curry0 q)
        (Curry0 p).natDegree (Curry0 q).natDegree i j) ≤
      if (j : ℕ) < (Curry0 p).natDegree then d₂ else d₁ := by
  classical
  by_cases hj : (↑j : ℕ) < (Curry0 p).natDegree
  · by_cases hcond : j ≤ i ∧ ↑i ≤ ↑j + (Curry0 q).natDegree
    · have hdeg :
        MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff (↑i - ↑j)) ≤ d₂ := by
        calc
          MvPolynomial.degreeOf (0 : Fin 1) ((Curry0 q).coeff (↑i - ↑j)) ≤
              MvPolynomial.degreeOf (1 : Fin 2) q := by
            simpa [Curry0] using
              (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := q)
                (j := 0) (i := ↑i - ↑j))
          _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q 1
          _ ≤ d₂ := hqdeg
      simpa [Polynomial.sylvester, Fin.addCases, hj, hcond] using hdeg
    · simp [Polynomial.sylvester, Fin.addCases, hj, hcond]
  · by_cases hcond : ↑j ≤ ↑i + (Curry0 p).natDegree ∧
      ↑i ≤ ↑j - (Curry0 p).natDegree + (Curry0 p).natDegree
    · have hdeg :
        MvPolynomial.degreeOf (0 : Fin 1)
            ((Curry0 p).coeff (↑i - (↑j - (Curry0 p).natDegree))) ≤ d₁ := by
        calc
          MvPolynomial.degreeOf (0 : Fin 1)
              ((Curry0 p).coeff (↑i - (↑j - (Curry0 p).natDegree))) ≤
              MvPolynomial.degreeOf (1 : Fin 2) p := by
            simpa [Curry0] using
              (MvPolynomial.degreeOf_coeff_finSuccEquiv (R := ℝ) (n := 1) (p := p)
                (j := 0) (i := ↑i - (↑j - (Curry0 p).natDegree)))
          _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 1
          _ ≤ d₁ := hpdeg
      simpa [Polynomial.sylvester, Fin.addCases, hj, hcond] using hdeg
    · simp [Polynomial.sylvester, Fin.addCases, hj, hcond]

/-- The resultant coefficient polynomial has degree bounded by `2*d₁*d₂`. -/
lemma degreeOf_resultant_le
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) ≤ 2 * d₁ * d₂ := by
  classical
  let m := (Curry0 p).natDegree
  let n := (Curry0 q).natDegree
  have hm : m ≤ d₁ := by
    dsimp [m]
    calc
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
      _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
      _ ≤ d₁ := hpdeg
  have hn : n ≤ d₂ := by
    dsimp [n]
    calc
      (Curry0 q).natDegree = MvPolynomial.degreeOf (0 : Fin 2) q := by
        simpa [Curry0] using
          (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := q))
      _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree q 0
      _ ≤ d₂ := hqdeg
  rw [ResultantCoeff, Polynomial.resultant, Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le (0 : Fin 1) Finset.univ _) ?_
  refine Finset.sup_le ?_
  intro σ hσ
  have hsign :
      MvPolynomial.degreeOf (0 : Fin 1)
        (Equiv.Perm.sign σ • ∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) := by
    rw [Units.smul_def, zsmul_eq_mul]
    simpa using
      (MvPolynomial.degreeOf_C_mul_le
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) 0
        ((Equiv.Perm.sign σ : ℤ) : ℝ))
  have hprod :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      ∑ i : Fin (m + n), if (i : ℕ) < m then d₂ else d₁ := by
    refine le_trans (by
      simpa using
        (MvPolynomial.degreeOf_prod_le (0 : Fin 1) Finset.univ
          (fun i : Fin (m + n) =>
            Polynomial.sylvester (Curry0 p) (Curry0 q)
              (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i))) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa [m] using
      (degreeOf_sylvester_entry_bound p q (σ i) i hpdeg hqdeg)
  have hsum :
      ∑ i : Fin (m + n), (if (i : ℕ) < m then d₂ else d₁) = m * d₂ + n * d₁ := by
    rw [Fin.sum_univ_add]
    simp [Fin.val_castAdd, Fin.val_natAdd]
  have hmn : m * d₂ + n * d₁ ≤ 2 * d₁ * d₂ := by
    calc
      m * d₂ + n * d₁ ≤ d₁ * d₂ + d₁ * d₂ := by
        exact add_le_add (Nat.mul_le_mul_right _ hm) (by
          simpa [Nat.mul_comm] using (Nat.mul_le_mul_right d₁ hn))
      _ = d₂ * (d₁ + d₁) := by
        rw [Nat.mul_add]
        simp [Nat.mul_comm]
      _ = 2 * d₁ * d₂ := by
        simp [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hprod' :
      MvPolynomial.degreeOf (0 : Fin 1)
        (∏ i, Polynomial.sylvester (Curry0 p) (Curry0 q)
          (Curry0 p).natDegree (Curry0 q).natDegree (σ i) i) ≤
      m * d₂ + n * d₁ := by
    simpa [hsum] using hprod
  exact le_trans hsign (le_trans hprod' hmn)

/-- The coefficient-root set of the resultant is bounded by `2*d₁*d₂`. -/
lemma coeff_root_ncard_resultant_le
    (p q : MvPolynomial (Fin 2) ℝ)
    (hR : ResultantCoeff p q ≠ 0)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂) :
    (CoeffRootSet (ResultantCoeff p q)).ncard ≤ 2 * d₁ * d₂ := by
  have hroot :
      (CoeffRootSet (ResultantCoeff p q)).ncard ≤
        MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) := by
    exact ncard_coeff_roots_le_degreeOf (ResultantCoeff p q) hR
  have hdeg :
      MvPolynomial.degreeOf (0 : Fin 1) (ResultantCoeff p q) ≤ 2 * d₁ * d₂ := by
    exact degreeOf_resultant_le p q hpdeg hqdeg
  exact le_trans hroot hdeg

/-- The ordinary nonassociated factor-pair case has finite intersection and the expected crude bound. -/
theorem primitive_nonvertical_pair_intersection_bound
    (p q : MvPolynomial (Fin 2) ℝ)
    {d₁ d₂ : ℕ}
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hq0deg : 0 < (Curry0 q).natDegree)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (2 * d₁ * d₂ + 1) * max d₁ d₂ := by
  classical
  let S : Set Point2 := PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q
  let rootSet : Set ℝ := CoeffRootSet (ResultantCoeff p q)
  have hR : ResultantCoeff p q ≠ 0 := by
    have hp0 : p ≠ 0 := by
      intro hp0
      have hp0' : (Curry0 p).natDegree = 0 := by
        simp [hp0, Curry0]
      exact (Nat.lt_irrefl 0) (by simpa [hp0'] using hp0deg)
    have hq0 : q ≠ 0 := by
      intro hq0
      have hq0' : (Curry0 q).natDegree = 0 := by
        simp [hq0, Curry0]
      exact (Nat.lt_irrefl 0) (by simpa [hq0'] using hq0deg)
    simpa [ResultantCoeff] using
      (resultant_ne_zero_of_isRelPrime_primitive_curry p q hpprim hqprim hrel)
  have hrootFinite : rootSet.Finite := by
    simpa [rootSet] using (finite_coeff_roots_of_ne_zero (ResultantCoeff p q) hR)
  let rootFinset := hrootFinite.toFinset
  let fiberSet : ℝ → Set Point2 :=
    fun x => {z : Point2 | coeffCoord z = x ∧ z ∈ S}
  have hroot_ncard : rootSet.ncard ≤ 2 * d₁ * d₂ := by
    exact le_trans (ncard_coeff_roots_le_degreeOf (ResultantCoeff p q) hR)
      (degreeOf_resultant_le p q hpdeg hqdeg)
  have hfiber_finite : ∀ x ∈ rootFinset, (fiberSet x).Finite := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have htarget_finite : (FiberCommonZeros x p q).Finite := by
      exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
    have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
      intro z hz
      rcases hz with ⟨hcoeff, hz⟩
      rcases hz with ⟨hzp, hzq⟩
      constructor
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
      · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
    have hinj : Set.InjOn elimCoord (fiberSet x) := by
      intro z₁ hz₁ z₂ hz₂ h
      ext i <;> fin_cases i
      · exact h
      · exact by
          simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
    exact Set.Finite.of_injOn hmapsTo hinj htarget_finite
  have hfiber_bound : ∀ x ∈ rootFinset, (fiberSet x).ncard ≤ max d₁ d₂ := by
    intro x hx
    have hxroot : x ∈ rootSet := by
      simpa [rootFinset, rootSet] using hx
    have hnonzero : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
      exact not_both_specializations_zero_of_isRelPrime p q x hpprim hqprim hrel
    have hle_root : (fiberSet x).ncard ≤ (FiberCommonZeros x p q).ncard := by
      have htarget_finite : (FiberCommonZeros x p q).Finite := by
        exact fiber_finite_of_one_specialization_nonzero p q x hnonzero
      have hmapsTo : Set.MapsTo elimCoord (fiberSet x) (FiberCommonZeros x p q) := by
        intro z hz
        rcases hz with ⟨hcoeff, hz⟩
        rcases hz with ⟨hzp, hzq⟩
        constructor
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzp
        · simpa [FiberCommonZeros, hcoeff, eval_eq_specialized_eval] using hzq
      have hinj : Set.InjOn elimCoord (fiberSet x) := by
        intro z₁ hz₁ z₂ hz₂ h
        ext i <;> fin_cases i
        · exact h
        · exact by
            simpa [coeffCoord] using (hz₁.1.trans hz₂.1.symm)
      exact Set.ncard_le_ncard_of_injOn elimCoord hmapsTo hinj htarget_finite
    have hfiberBound : (FiberCommonZeros x p q).ncard ≤ max d₁ d₂ := by
      exact le_trans (fiber_ncard_le_max_totalDegree p q x hnonzero) (max_le_max hpdeg hqdeg)
    exact le_trans hle_root hfiberBound
  have hcover : S = ⋃ x ∈ rootFinset, fiberSet x := by
    ext z
    constructor
    · intro hz
      have hxroot : coeffCoord z ∈ rootSet := by
        exact resultant_vanishes_at_common_zero p q hp0deg hq0deg hz
      have hx : coeffCoord z ∈ rootFinset := by
        simpa [rootFinset, rootSet] using hxroot
      have hzfiber : z ∈ fiberSet (coeffCoord z) := by
        exact ⟨rfl, hz⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨coeffCoord z, Set.mem_iUnion.2 ?_⟩
      exact ⟨hx, hzfiber⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨x, hz⟩
      rcases Set.mem_iUnion.1 hz with ⟨hx, hz⟩
      rcases hz with ⟨hcoeff, hzS⟩
      simpa [S] using hzS
  have hrootcard : rootFinset.card ≤ 2 * d₁ * d₂ + 1 := by
    have hrootcard' : rootFinset.card = rootSet.ncard := by
      simpa [rootFinset, rootSet] using
        (Set.ncard_eq_toFinset_card rootSet hrootFinite).symm
    calc
      rootFinset.card = rootSet.ncard := hrootcard'
      _ ≤ 2 * d₁ * d₂ := hroot_ncard
      _ ≤ 2 * d₁ * d₂ + 1 := Nat.le_succ _
  have hunion_ncard :
      (⋃ x ∈ rootFinset, fiberSet x).ncard ≤ (2 * d₁ * d₂ + 1) * max d₁ d₂ := by
    refine le_trans (Finset.set_ncard_biUnion_le rootFinset fiberSet) ?_
    have hsum :
        ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hfiber_bound x hx
    have hsum' : ∑ x ∈ rootFinset, max d₁ d₂ = rootFinset.card * max d₁ d₂ := by
      simp
    calc
      ∑ x ∈ rootFinset, (fiberSet x).ncard ≤ ∑ x ∈ rootFinset, max d₁ d₂ := hsum
      _ = rootFinset.card * max d₁ d₂ := hsum'
      _ ≤ (2 * d₁ * d₂ + 1) * max d₁ d₂ := by
        exact Nat.mul_le_mul_right _ hrootcard
  have hunion_finite : (⋃ x ∈ rootFinset, fiberSet x).Finite := by
    change (⋃ x ∈ (rootFinset : Set ℝ), fiberSet x).Finite
    exact Set.Finite.biUnion rootFinset.finite_toSet (by
      intro x hx
      exact hfiber_finite x hx)
  have hfinite : S.Finite := by
    simpa [hcover] using hunion_finite
  have hncard : S.ncard ≤ (2 * d₁ * d₂ + 1) * max d₁ d₂ := by
    calc
      S.ncard = (⋃ x ∈ rootFinset, fiberSet x).ncard := by rw [hcover]
      _ ≤ (2 * d₁ * d₂ + 1) * max d₁ d₂ := hunion_ncard
  exact ⟨hfinite, hncard⟩

/-- The irreducible factor-pair case has a finite intersection and a crude fourth-power bound. -/
theorem irreducible_pair_intersection_bound
    (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        (d₁ + d₂ + 1) ^ 4 := by
  have htarget_mul : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
    have hle : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hpos : 0 < (d₁ + d₂ + 1) ^ 2 := by
      have hbase : 0 < d₁ + d₂ + 1 := by omega
      exact Nat.pow_pos hbase
    have hsq : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 4 := by
      have hle2 : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 2 := by
        exact Nat.le_mul_of_pos_right _ hpos
      simpa [pow_two, pow_succ] using hle2
    exact le_trans hle hsq
  have htarget_prim :
      (2 * d₁ * d₂ + 1) * max d₁ d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
    let s : ℕ := d₁ + d₂ + 1
    have h1q : ((2 * d₁ * d₂ + 1 : ℕ) : ℚ) ≤ (s : ℚ)^3 := by
      have hsq : ((2 * d₁ * d₂ + 1 : ℕ) : ℚ) ≤ (s : ℚ)^2 := by
        subst s
        nlinarith [sq_nonneg ((d₁ : ℚ) - d₂), sq_nonneg ((d₁ : ℚ) + d₂)]
      have hs : (1 : ℚ) ≤ s := by
        exact_mod_cast (by omega : 1 ≤ s)
      have hcube : (s : ℚ)^2 ≤ (s : ℚ)^3 := by
        nlinarith [hs]
      exact le_trans hsq hcube
    have h1 : 2 * d₁ * d₂ + 1 ≤ s ^ 3 := by
      exact_mod_cast h1q
    have hmax : max d₁ d₂ ≤ s := by
      subst s
      omega
    have hprod : (2 * d₁ * d₂ + 1) * max d₁ d₂ ≤ s ^ 3 * s := by
      calc
        (2 * d₁ * d₂ + 1) * max d₁ d₂ ≤ s ^ 3 * max d₁ d₂ := Nat.mul_le_mul_right _ h1
        _ ≤ s ^ 3 * s := Nat.mul_le_mul_left _ hmax
    have hpow : s ^ 3 * s = s ^ 4 := by
      simp [pow_succ, pow_two, Nat.mul_assoc]
    calc
      (2 * d₁ * d₂ + 1) * max d₁ d₂ ≤ s ^ 3 * s := hprod
      _ = s ^ 4 := hpow
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases kdeg0 : (Curry0 k).natDegree = 0
    · exact zeroCurry_zeroCurry_pair_intersection_bound h k hh hk hnot hdeg0 kdeg0
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hk hdeg kdeg hnot hdeg0 kpos
      exact ⟨hbound.1, le_trans hbound.2 htarget_mul⟩
  · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
    by_cases kdeg0 : (Curry0 k).natDegree = 0
    · have hnot' : ¬ Associated k h := by
        intro hAssoc
        exact hnot hAssoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hk hh kdeg hdeg hnot' kdeg0 hpos
      have hbound' :
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
            (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by
        simpa [Set.inter_comm, Nat.mul_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 htarget_mul⟩
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hk kpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hk hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg kdeg hprim kprim hpos kpos hrel
      exact ⟨hbound.1, le_trans hbound.2 htarget_prim⟩

/-! ## Singularity helpers -/

/-- A bivariate polynomial on the real plane. -/
abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

/-- The singular point set of a plane polynomial. -/
def SingularPointSet (p : PlanePoly) : Set Point2 :=
  PlaneCurveZeroSet p ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) p) = 0} ∩
    {z | MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) p) = 0}

/-- The standard plane evaluation map used in the implicit-function argument. -/
def evalPlane (p : PlanePoly) : ℝ × ℝ → ℝ :=
  fun xy => MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p

/-- Build a plane point from its two coordinates. -/
noncomputable def mkPoint2 (x y : ℝ) : Point2 :=
  WithLp.toLp 2 ![x, y]

/-- Swap the two coordinates of a point in the plane. -/
noncomputable def swapPoint (z : Point2) : Point2 :=
  mkPoint2 (z 1) (z 0)

/-- Swapping coordinates twice gives the original point back. -/
lemma swapPoint_swapPoint (z : Point2) : swapPoint (swapPoint z) = z := by
  ext i
  fin_cases i <;> simp [swapPoint, mkPoint2]

/-- Swapping coordinates is injective on the plane. -/
lemma swapPoint_injective : Function.Injective swapPoint := by
  intro z₁ z₂ h
  have h' := congrArg swapPoint h
  simpa [swapPoint_swapPoint] using h'

/-- Plane polynomial evaluation is smooth. -/
lemma evalPlane_contDiff (p : PlanePoly) :
    ContDiff ℝ ⊤ (evalPlane p) := by
  change ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
    MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)
  refine MvPolynomial.induction_on
    (motive := fun p => ContDiff ℝ ⊤ (fun xy : ℝ × ℝ =>
      MvPolynomial.eval (fun i => if i = 0 then xy.1 else xy.2) p)) p ?_ ?_ ?_
  · intro a
    simpa [MvPolynomial.eval_C] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => a))
  · intro p q hp hq
    simpa [MvPolynomial.eval_add] using hp.add hq
  · intro p i hp
    fin_cases i
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_fst
    · simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul contDiff_snd

/-- `x ↦ x • b` is bijective on `ℝ` when `b ≠ 0`. -/
lemma toSpanSingleton_bijective_of_ne_zero (b : ℝ) (hb : b ≠ 0) :
    Function.Bijective (ContinuousLinearMap.toSpanSingleton ℝ b) := by
  constructor
  · intro x y hxy
    have hxy' : x * b = y * b := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hxy
    exact mul_right_cancel₀ hb hxy'
  · intro y
    refine ⟨y / b, ?_⟩
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp [hb]

/-- Currying in the first coordinate turns `pderiv 0` into univariate differentiation. -/
lemma curry0_pderiv0 (p : PlanePoly) :
    Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p) := by
  refine MvPolynomial.induction_on
    (motive := fun p =>
      Curry0 (MvPolynomial.pderiv (0 : Fin 2) p) = Polynomial.derivative (Curry0 p)) p ?_ ?_ ?_
  · intro a
    simp [Curry0, MvPolynomial.finSuccEquiv_apply]
  · intro p q hp hq
    simpa [Curry0, map_add] using congrArg₂ (fun a b => a + b) hp hq
  · intro p i hp
    have hp' :
        MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
            (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i)
            (MvPolynomial.pderiv (0 : Fin 2) p) =
          Polynomial.derivative
            (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
              (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) := by
      simpa [Curry0, MvPolynomial.finSuccEquiv_apply] using hp
    fin_cases i
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_add, map_mul,
        MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      ring
    · simp [Curry0, MvPolynomial.finSuccEquiv_apply, map_add, map_mul,
        MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Polynomial.derivative_mul]
      rw [hp']
      change Polynomial.C (MvPolynomial.X 0) *
            Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) =
          Polynomial.derivative
              (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p) *
            Polynomial.C (MvPolynomial.X 0) +
              MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
                (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) p *
              Polynomial.derivative (Polynomial.C (MvPolynomial.X 0))
      simp [mul_comm]

/-- A nonsingular point with nonzero partial in the second coordinate lies on an infinite zero set. -/
lemma nonsingular_point_has_infinite_zeroSet_of_partial1
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  let a : ℝ × ℝ := (z 0, z 1)
  have hcoords : (fun i : Fin 2 => if i = 0 then a.1 else a.2) = fun i => z i := by
    funext i
    fin_cases i <;> simp [a]
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) a := (evalPlane_contDiff h).contDiffAt
  rcases (show ∃ f' : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (evalPlane h) f' a by
      simpa [DifferentiableAt] using hcont.differentiableAt) with ⟨f', hfd⟩
  let g : ℝ → ℝ := fun y => evalPlane h (a.1, y)
  let hswap : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  let q : Polynomial ℝ := Specialized0 a.1 hswap
  have hg_eq : g = fun y => Polynomial.eval y q := by
    funext y
    have hslice := eval_eq_specialized_eval hswap (mkPoint2 y a.1)
    have hswapCoords :
        ((fun i => mkPoint2 y a.1 i) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then a.1 else y) := by
      funext i
      fin_cases i <;> simp [Function.comp, mkPoint2]
    dsimp [hswap] at hslice
    rw [MvPolynomial.eval_rename] at hslice
    simpa [g, q, evalPlane, hswapCoords] using hslice
  have hinr : HasFDerivAt (fun y : ℝ => (a.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) a.2 := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const a.1 a.2).prodMk (hasFDerivAt_id a.2)
  have hgfd : HasFDerivAt g (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) a.2 := by
    simpa [g] using hfd.comp a.2 hinr
  have hq_deriv : Polynomial.derivative q =
      Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
    unfold q Specialized0
    rw [Polynomial.derivative_map, curry0_pderiv0]
  have hslice_deriv :
      Polynomial.eval a.2 (Polynomial.derivative q) =
        MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
    rw [hq_deriv]
    have hslice :=
      eval_eq_specialized_eval (MvPolynomial.pderiv (0 : Fin 2) hswap) (swapPoint z)
    have hrename :
        MvPolynomial.pderiv (0 : Fin 2) hswap =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (1 : Fin 2) h) := by
      dsimp [hswap]
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (1 : Fin 2)) (p := h))
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    calc
      Polynomial.eval a.2 (Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap)) =
          MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
            simpa [a, swapPoint, mkPoint2] using hslice.symm
      _ = MvPolynomial.eval ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1))
            (MvPolynomial.pderiv (1 : Fin 2) h) := by
              rw [hrename, MvPolynomial.eval_rename]
      _ = MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) := by
            simp [hswapCoords]
  have hpoly : HasFDerivAt g
      (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
    have hq' :
        HasFDerivAt (fun y => Polynomial.eval y q)
          (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
      simpa [Polynomial.aeval_def] using (Polynomial.hasDerivAt_aeval q a.2).hasFDerivAt
    simpa [hg_eq] using hq'
  have hscalar_ne : Polynomial.eval a.2 (Polynomial.derivative q) ≠ 0 := by
    simpa [hslice_deriv] using hnonsing
  have hcomp :
      Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    have hcomp_eq :
        f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
          ContinuousLinearMap.toSpanSingleton ℝ
            (Polynomial.eval a.2 (Polynomial.derivative q)) :=
      HasFDerivAt.unique hgfd hpoly
    simpa [hcomp_eq] using
      toSpanSingleton_bijective_of_ne_zero
        (Polynomial.eval a.2 (Polynomial.derivative q)) hscalar_ne
  have himp : IsContDiffImplicitAt ⊤ (evalPlane h) f' a :=
    IsContDiffImplicitAt.mk hfd hcont hcomp (by simp)
  have ha : evalPlane h a = 0 := by
    simpa [PlaneCurveZeroSet, evalPlane, hcoords] using hz
  have hevent : ∀ᶠ x in 𝓝 a.1, evalPlane h (x, himp.implicitFunction x) = 0 := by
    simpa [ha] using himp.apply_implicitFunction
  have hnhds : {x | evalPlane h (x, himp.implicitFunction x) = 0} ∈ 𝓝 a.1 := by
    simpa [Filter.Eventually] using hevent
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  have hball_infinite : (Metric.ball a.1 ε).Infinite := by
    simpa [Real.ball_eq_Ioo] using Set.Ioo_infinite (show a.1 - ε < a.1 + ε by linarith)
  let g : ℝ → Point2 := fun x => mkPoint2 x (himp.implicitFunction x)
  have hg_inj : Set.InjOn g (Metric.ball a.1 ε) := by
    intro x hx y hy hxy
    have h0 := congrArg (fun p : Point2 => p 0) hxy
    simp [g, mkPoint2] at h0
    exact h0
  have hsubset : g '' Metric.ball a.1 ε ⊆ PlaneCurveZeroSet h := by
    intro z' hz'
    rcases hz' with ⟨x, hx, rfl⟩
    have hx' : evalPlane h (x, himp.implicitFunction x) = 0 := hball hx
    change MvPolynomial.eval (fun i => g x i) h = 0
    dsimp [g]
    convert hx' using 1
    show MvPolynomial.eval (fun i => mkPoint2 x (himp.implicitFunction x) i) h =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else himp.implicitFunction x) h
    apply congrArg (fun f => MvPolynomial.eval f h)
    funext i
    fin_cases i <;> simp [mkPoint2]
  exact Set.Infinite.mono hsubset (Set.Infinite.image hg_inj hball_infinite)

/-- A nonsingular point with a nonzero partial in the first coordinate lies on an infinite zero set. -/
lemma nonsingular_point_has_infinite_zeroSet_of_partial0
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  let h' : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  have hz' : swapPoint z ∈ PlaneCurveZeroSet h' := by
    dsimp [h']
    change MvPolynomial.eval (fun i => swapPoint z i)
      (MvPolynomial.rename (Equiv.swap 0 1) h) = 0
    rw [MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hz
  have h1' :
      MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (1 : Fin 2) h') ≠ 0 := by
    dsimp [h']
    have hrename :
        MvPolynomial.pderiv (1 : Fin 2) (MvPolynomial.rename (Equiv.swap 0 1) h) =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (0 : Fin 2)) (p := h))
    rw [hrename, MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hnonsing
  have hinf' := nonsingular_point_has_infinite_zeroSet_of_partial1 h' hz' h1'
  have hswap : swapPoint '' PlaneCurveZeroSet h' = PlaneCurveZeroSet h := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hswapCoords :
          ((fun i => swapPoint u i) ∘ (Equiv.swap 0 1)) = fun i => u i := by
        funext i
        fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
      simpa [h', PlaneCurveZeroSet, hswapCoords] using hu
    · intro hw
      refine ⟨swapPoint w, ?_, ?_⟩
      · rw [show swapPoint (swapPoint w) = w by simpa using swapPoint_swapPoint w]
        rw [MvPolynomial.eval_rename]
        have hswapCoords :
            ((fun i => w i) ∘ (Equiv.swap 0 1)) = fun i => swapPoint w i := by
          funext i
          fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
        simpa [h', PlaneCurveZeroSet, hswapCoords] using hw
      · simp [swapPoint_swapPoint]
  have hswap_inf : (swapPoint '' PlaneCurveZeroSet h').Infinite :=
    hinf'.image swapPoint_injective
  simpa [hswap] using hswap_inf

/-- A nonsingular point has an infinite real zero set. -/
theorem nonsingular_point_has_infinite_zeroSet
    (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0 ∨
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  rcases hnonsing with h0 | h1
  · exact nonsingular_point_has_infinite_zeroSet_of_partial0 h hz h0
  · exact nonsingular_point_has_infinite_zeroSet_of_partial1 h hz h1

/-- A finite zero set is contained in the singular points. -/
lemma finite_zeroSet_subset_singularities
    (h : PlanePoly)
    (hfin : (PlaneCurveZeroSet h).Finite) :
    PlaneCurveZeroSet h ⊆ SingularPointSet h := by
  intro z hz
  refine ⟨⟨hz, ?_⟩, ?_⟩
  · by_contra h0
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      left
      simpa using h0)
    exact hfin.not_infinite hinf
  · by_contra h1
    have hinf := nonsingular_point_has_infinite_zeroSet h hz (by
      right
      simpa using h1)
    exact hfin.not_infinite hinf

/-- A singular point of a product of factors lies on a singular factor or on an off-diagonal pairwise intersection. -/
lemma singularPointSet_prod_subset
    (s : Finset PlanePoly) :
    SingularPointSet (∏ h in s, h) ⊆
      (⋃ h ∈ s, SingularPointSet h) ∪
        (⋃ x ∈ s.offDiag, PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2) := by
  classical
  refine Finset.induction_on s ?base ?step
  · intro z hz
    simp [SingularPointSet] at hz
  · intro a s ha ih
    intro z hz
    set r : PlanePoly := ∏ h in s, h
    have hz' : z ∈ SingularPointSet (a * r) := by
      simpa [SingularPointSet, r, Finset.prod_insert ha] using hz
    rcases hz' with ⟨hz0, hz1, hz2⟩
    have hmul : MvPolynomial.eval (fun i => z i) a * MvPolynomial.eval (fun i => z i) r = 0 := by
      simpa [r, MvPolynomial.eval_mul] using hz0
    rcases mul_eq_zero.mp hmul with hza | hzr
    · by_cases hzr' : MvPolynomial.eval (fun i => z i) r = 0
      · have hk : ∃ k ∈ s, MvPolynomial.eval (fun i => z i) k = 0 := by
          have hprod : ∏ h in s, MvPolynomial.eval (fun i => z i) h = 0 := by
            simpa [r] using hzr'
          exact (Finset.prod_eq_zero_iff).mp hprod
        rcases hk with ⟨k, hk, hzk⟩
        have hkne : a ≠ k := by
          intro hEq
          exact ha (hEq.symm ▸ hk)
        have hpair : (a, k) ∈ (insert a s).offDiag := by
          rw [Finset.mem_offDiag]
          constructor
          · simp
          constructor
          · simp [hk]
          · exact hkne
        refine Or.inr ?_
        refine Set.mem_iUnion.2 ?_
        refine ⟨(a, k), ?_⟩
        refine Set.mem_iUnion.2 ⟨hpair, ?_⟩
        exact ⟨by simpa [PlaneCurveZeroSet] using hza, by simpa [PlaneCurveZeroSet] using hzk⟩
      · have hder0mul : MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) a) *
            MvPolynomial.eval (fun i => z i) r = 0 := by
          have h := hz1
          rw [r, MvPolynomial.pderiv_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul] at h
          rw [hza, zero_mul, add_zero] at h
          exact h
        have hder1mul : MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) a) *
            MvPolynomial.eval (fun i => z i) r = 0 := by
          have h := hz2
          rw [r, MvPolynomial.pderiv_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul] at h
          rw [hza, zero_mul, add_zero] at h
          exact h
        have hsingA : z ∈ SingularPointSet a := by
          refine ⟨?_, ?_, ?_⟩
          · simpa [PlaneCurveZeroSet] using hza
          · exact (mul_eq_zero.mp hder0mul).resolve_right hzr'
          · exact (mul_eq_zero.mp hder1mul).resolve_right hzr'
        refine Or.inl ?_
        refine Set.mem_iUnion.2 ?_
        refine ⟨a, ?_⟩
        refine Set.mem_iUnion.2 ⟨by simp, hsingA⟩
    · by_cases hza' : MvPolynomial.eval (fun i => z i) a = 0
      · have hk : ∃ k ∈ s, MvPolynomial.eval (fun i => z i) k = 0 := by
          have hprod : ∏ h in s, MvPolynomial.eval (fun i => z i) h = 0 := by
            simpa [r] using hzr
          exact (Finset.prod_eq_zero_iff).mp hprod
        rcases hk with ⟨k, hk, hzk⟩
        have hkne : a ≠ k := by
          intro hEq
          exact ha (hEq.symm ▸ hk)
        have hpair : (a, k) ∈ (insert a s).offDiag := by
          rw [Finset.mem_offDiag]
          constructor
          · simp
          constructor
          · simp [hk]
          · exact hkne
        refine Or.inr ?_
        refine Set.mem_iUnion.2 ?_
        refine ⟨(a, k), ?_⟩
        refine Set.mem_iUnion.2 ⟨hpair, ?_⟩
        exact ⟨by simpa [PlaneCurveZeroSet] using hza', by simpa [PlaneCurveZeroSet] using hzk⟩
      · have hder0mul : MvPolynomial.eval (fun i => z i) a *
            MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) r) = 0 := by
          have h := hz1
          rw [r, MvPolynomial.pderiv_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul] at h
          rw [hzr, zero_mul, add_zero] at h
          exact h
        have hder1mul : MvPolynomial.eval (fun i => z i) a *
            MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (1 : Fin 2) r) = 0 := by
          have h := hz2
          rw [r, MvPolynomial.pderiv_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul] at h
          rw [hzr, zero_mul, add_zero] at h
          exact h
        have hsingR : z ∈ SingularPointSet r := by
          refine ⟨?_, ?_, ?_⟩
          · simpa [PlaneCurveZeroSet, r] using hzr
          · exact (mul_eq_zero.mp hder0mul).resolve_left hza'
          · exact (mul_eq_zero.mp hder1mul).resolve_left hza'
        rcases ih hsingR with hA | hB
        · refine Or.inl ?_
          rcases Set.mem_iUnion.mp hA with ⟨k, hk⟩
          rcases Set.mem_iUnion.mp hk with ⟨hkmem, hsk⟩
          refine Set.mem_iUnion.2 ?_
          refine ⟨k, ?_⟩
          refine Set.mem_iUnion.2 ⟨by
            exact Finset.mem_of_subset (Finset.subset_insert a s) hkmem, ?_⟩
          exact hsk
        · refine Or.inr ?_
          rcases Set.mem_iUnion.mp hB with ⟨x, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨hxmem, hxp⟩
          have hxmem' : x ∈ (insert a s).offDiag := by
            exact Finset.offDiag_mono (Finset.subset_insert a s) hxmem
          refine Set.mem_iUnion.2 ?_
          refine ⟨x, ?_⟩
          refine Set.mem_iUnion.2 ⟨hxmem', hxp⟩

/-- An irreducible plane polynomial has a nonzero partial derivative. -/
lemma irreducible_has_nonzero_partial
    (h : PlanePoly) (hh : Irreducible h) :
    MvPolynomial.pderiv (0 : Fin 2) h ≠ 0 ∨
    MvPolynomial.pderiv (1 : Fin 2) h ≠ 0 := by
  classical
  by_cases h0 : MvPolynomial.pderiv (0 : Fin 2) h = 0
  · by_cases h1 : MvPolynomial.pderiv (1 : Fin 2) h = 0
    · exfalso
      let p : Polynomial (Polynomial ℝ) := (Polynomial.Bivariate.equivMvPolynomial ℝ).symm h
      have hp : (Polynomial.Bivariate.equivMvPolynomial ℝ) p = h := by
        simp [p]
      have hp1 : Polynomial.derivative p = 0 := by
        have h1' : (MvPolynomial.pderiv (1 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
          simpa [p, hp] using h1
        rw [Polynomial.Bivariate.pderiv_one_equivMvPolynomial] at h1'
        have h1'' :
            (Polynomial.Bivariate.equivMvPolynomial ℝ) (Polynomial.derivative p) =
              (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
          simpa using h1'
        exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h1''
      have hp_nat : p.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hp1
      rcases (Polynomial.natDegree_eq_zero.mp hp_nat) with ⟨q, hq⟩
      have h0' : PolynomialModule.single (Polynomial ℝ) 0 (Polynomial.derivative q) = 0 := by
        have h0'' : Polynomial.derivative'.mapCoeffs (Polynomial.C q) = 0 := by
          have h0''0 : (MvPolynomial.pderiv (0 : Fin 2)) ((Polynomial.Bivariate.equivMvPolynomial ℝ) p) = 0 := by
            simpa [p, hp] using h0
          rw [Polynomial.Bivariate.pderiv_zero_equivMvPolynomial] at h0''0
          have h0''1 : PolynomialModule.equivPolynomialSelf
              (Polynomial.derivative'.mapCoeffs p) = 0 := by
            have h0''0' :
                (Polynomial.Bivariate.equivMvPolynomial ℝ)
                    (PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)) =
                  (Polynomial.Bivariate.equivMvPolynomial ℝ) 0 := by
              simpa using h0''0
            exact (Polynomial.Bivariate.equivMvPolynomial ℝ).injective h0''0'
          have h0''1' :
              PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p) =
                PolynomialModule.equivPolynomialSelf 0 := by
            simpa using h0''1
          exact PolynomialModule.equivPolynomialSelf.injective h0''1'
        rw [hq] at h0''
        simpa [Polynomial.derivative'_apply] using h0''
      have hqder : Polynomial.derivative q = 0 := by
        have hqder' := congrArg (fun r : PolynomialModule (Polynomial ℝ) (Polynomial ℝ) => r 0) h0'
        simpa [PolynomialModule.single_apply] using hqder'
      have hq_nat : q.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_derivative_eq_zero hqder
      rcases (Polynomial.natDegree_eq_zero.mp hq_nat) with ⟨r, hr⟩
      have hconst : h = MvPolynomial.C r := by
        rw [← hp, hq, hr]
        simp
      by_cases hr0 : r = 0
      · subst hr0
        simp [hconst] at hh.ne_zero
      · have hunitq : IsUnit r := by
          exact isUnit_iff_ne_zero.2 hr0
        have hunit : IsUnit h := by
          rw [hconst]
          exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ) hunitq
        exact hh.not_isUnit hunit
    · exact Or.inr h1
  · exact Or.inl h0

/-- An irreducible plane polynomial does not divide a nonzero partial derivative of itself. -/
lemma irreducible_not_dvd_nonzero_partial
    (h : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    ¬ h ∣ MvPolynomial.pderiv i h := by
  intro hdiv
  have hpos : 0 < h.totalDegree := by
    by_contra hnonpos
    have hdeg0 : h.totalDegree = 0 := by omega
    have hC : h = MvPolynomial.C (MvPolynomial.coeff 0 h) := by
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg0
    have hcoeff : MvPolynomial.coeff 0 h ≠ 0 := by
      intro hzero
      exact hh.ne_zero (by rw [hC, hzero]; simp)
    have hunit : IsUnit h := by
      rw [hC]
      exact IsUnit.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
        (isUnit_iff_ne_zero.mpr hcoeff)
    exact hh.not_isUnit hunit
  have hlt := totalDegree_pderiv_lt_of_nonzero h hpos hpi
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hpi
  exact (not_lt_of_ge hle) hlt

/-- A singular point lies in the zero set of some normalized factor of the chosen partial derivative. -/
lemma singularPointSet_subset_partial_factor_union
    (h : PlanePoly) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    SingularPointSet h ⊆
      ⋃ k ∈ (UniqueFactorizationMonoid.normalizedFactors
          (MvPolynomial.pderiv i h)).toFinset,
        PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
  classical
  intro z hz
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz
  rcases hz with ⟨hz0, hz1, hz2⟩
  fin_cases i
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (0 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz1
    rcases hsubset hzder with ⟨k, hk, hzk⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨k, Set.mem_iUnion.2 ?_⟩
    refine ⟨hk, ?_⟩
    exact ⟨hz0, hzk⟩
  · have hsubset := zeroSet_subset_normalizedFactor_union
        (p := MvPolynomial.pderiv (1 : Fin 2) h) hpi
    have hzder : z ∈ PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h) := by
      simpa [PlaneCurveZeroSet] using hz2
    rcases hsubset hzder with ⟨k, hk, hzk⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨k, Set.mem_iUnion.2 ?_⟩
    refine ⟨hk, ?_⟩
    exact ⟨hz0, hzk⟩

/-- A normalized factor of the chosen partial derivative cannot be associated with the irreducible curve. -/
lemma partial_factor_not_associated
    (h k : PlanePoly) (hh : Irreducible h) {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors
        (MvPolynomial.pderiv i h)) :
    ¬ Associated h k := by
  intro hassoc
  have hdiv : h ∣ MvPolynomial.pderiv i h := by
    exact (Associated.dvd_iff_dvd_left hassoc).2
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hk)
  exact irreducible_not_dvd_nonzero_partial h hh hpi hdiv

/-- A quadratic bound fits under the fourth power of `d + 1`. -/
lemma mul_self_le_fourth_succ (d : ℕ) : d * d ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])

/-- The primitive pair bound for equal degree parameters fits under the fourth power of `d + 1`. -/
lemma primitive_bound_le_fourth_succ (d : ℕ) :
    ((2 * d * d + 1) * d : ℕ) ≤ (d + 1) ^ 4 := by
  have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
  exact_mod_cast (by
    ring_nf
    nlinarith [hd])

/-- A normalized factor of the chosen partial derivative meets the irreducible curve in at most `(d + 1)^4` points. -/
lemma factor_intersection_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0)
    {k : PlanePoly}
    (hk : k ∈ UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h))
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
  classical
  have hkirr : Irreducible k :=
    normalized_factor_irreducible (p := MvPolynomial.pderiv i h) hk
  have hkdeg : k.totalDegree ≤ d := by
    calc
      k.totalDegree ≤ (MvPolynomial.pderiv i h).totalDegree :=
        normalized_factor_degree_le (p := MvPolynomial.pderiv i h) (h := k) hpi hk
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hbound :=
        zeroCurry_zeroCurry_pair_intersection_bound
          (B := (d + 1) ^ 4) h k hh hkirr hnot hdeg0 hkdeg0
      simpa using hbound
    · have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hkirr hdeg hkdeg hnot hdeg0 hkpos
      exact ⟨hbound.1, le_trans hbound.2 (mul_self_le_fourth_succ d)⟩
  · by_cases hkdeg0 : (Curry0 k).natDegree = 0
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hnot' : ¬ Associated k h := by
        intro hassoc
        exact hnot hassoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hkirr hh hkdeg hdeg hnot' hkdeg0 hpos
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d * d := by
        simpa [Set.inter_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (mul_self_le_fourth_succ d)⟩
    · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
      have hkpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero hkdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hkirr hkpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hkirr hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg hkdeg hprim kprim hpos hkpos hrel
      have hbound' : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (2 * d * d + 1) * d := by
        simpa using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 (primitive_bound_le_fourth_succ d)⟩

/-- The singular points of an irreducible plane curve are finite with a degree-only bound. -/
theorem finite_singularities_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    {i : Fin 2}
    (hpi : MvPolynomial.pderiv i h ≠ 0) :
    (SingularPointSet h).Finite ∧
      (SingularPointSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  let s : Multiset (MvPolynomial (Fin 2) ℝ) :=
    UniqueFactorizationMonoid.normalizedFactors (MvPolynomial.pderiv i h)
  have hsubset :
      SingularPointSet h ⊆
        ⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k := by
    simpa [s] using singularPointSet_subset_partial_factor_union h hpi
  have hfactor_bound : ∀ k ∈ s.toFinset,
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
        (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ (d + 1) ^ 4 := by
    intro k hk
    have hk' : k ∈ s := by
      simpa [s] using hk
    exact factor_intersection_bound h hh hdeg hpi hk'
      (partial_factor_not_associated h k hh hpi hk')
  have hfinite_union :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite := by
    exact Set.Finite.biUnion s.toFinset.finite_toSet (by
      intro k hk
      exact (hfactor_bound k hk).1)
  have hcard_union :
      (SingularPointSet h).ncard ≤
        (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    exact Set.ncard_le_ncard hsubset hfinite_union
  have hcard_biUnion :
      (⋃ k ∈ s.toFinset, PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard := by
    simpa using
      Finset.set_ncard_biUnion_le s.toFinset
        (fun k => PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k)
  have hsum :
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        s.toFinset.card * (d + 1) ^ 4 := by
    have hsum' :
        ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact (hfactor_bound k hk).2
    calc
      ∑ k ∈ s.toFinset, (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
          ∑ k ∈ s.toFinset, (d + 1) ^ 4 := hsum'
      _ = s.toFinset.card * (d + 1) ^ 4 := by simp
  have hcard_s : s.toFinset.card ≤ d := by
    calc
      s.toFinset.card ≤ s.card := Multiset.toFinset_card_le _
      _ ≤ (MvPolynomial.pderiv i h).totalDegree :=
        card_normalizedFactors_le_totalDegree (p := MvPolynomial.pderiv i h) hpi
      _ ≤ h.totalDegree := totalDegree_pderiv_le h i
      _ ≤ d := hdeg
  have hcard_mul :
      s.toFinset.card * (d + 1) ^ 4 ≤ d * (d + 1) ^ 4 := by
    exact Nat.mul_le_mul_right _ hcard_s
  have hpow : d * (d + 1) ^ 4 ≤ (d + 1) ^ 5 := by
    calc
      d * (d + 1) ^ 4 ≤ (d + 1) * (d + 1) ^ 4 := by
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)
      _ = (d + 1) ^ 5 := by
        ring_nf
  have hfinite : (SingularPointSet h).Finite := hfinite_union.subset hsubset
  exact ⟨hfinite, le_trans hcard_union (le_trans hcard_biUnion (le_trans hsum (le_trans hcard_mul hpow)))⟩

/-- The real zero set of a non-infinite irreducible plane curve is finite with the same bound. -/
theorem finite_real_zero_set_of_irreducible_factor_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hfin : ¬ (PlaneCurveZeroSet h).Infinite) :
    (PlaneCurveZeroSet h).Finite ∧
      (PlaneCurveZeroSet h).ncard ≤ (d + 1) ^ 5 := by
  classical
  have hfinite : (PlaneCurveZeroSet h).Finite := (Set.not_infinite).mp hfin
  have hsubset : PlaneCurveZeroSet h ⊆ SingularPointSet h :=
    finite_zeroSet_subset_singularities h hfinite
  rcases irreducible_has_nonzero_partial h hh with hpi | hpi
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩
  · have hsingu := finite_singularities_of_irreducible_bound h hh hdeg hpi
    exact ⟨hfinite, le_trans (Set.ncard_le_ncard hsubset hsingu.1) hsingu.2⟩

/-- A factorized Bezout bound obtained by summing over normalized factor pairs. -/
theorem factorized_bezout_bound
    (p q : PlanePoly)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpdeg : p.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (hnoinf : ¬ HasCommonInfiniteIrreducibleFactor p q) :
    (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite ∧
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (d₁ + d₂ + 1) ^ 8 := by
  classical
  let sp : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors p
  let sq : Multiset (PlanePoly) := UniqueFactorizationMonoid.normalizedFactors q
  let pairs : Finset (PlanePoly × PlanePoly) := sp.toFinset.product sq.toFinset
  let pairSet : PlanePoly × PlanePoly → Set Point2 :=
    fun hk => PlaneCurveZeroSet hk.1 ∩ PlaneCurveZeroSet hk.2
  have hcover :
      PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q ⊆ ⋃ x ∈ pairs, pairSet x := by
    intro z hz
    rcases hz with ⟨hzp, hzq⟩
    have hpW := zeroSet_subset_normalizedFactor_union (p := p) hp0 hzp
    have hqW := zeroSet_subset_normalizedFactor_union (p := q) hq0 hzq
    rcases Set.mem_iUnion.mp hpW with ⟨hpFactor, hpW⟩
    rcases Set.mem_iUnion.mp hpW with ⟨hpMem, hzhp⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqFactor, hqW⟩
    rcases Set.mem_iUnion.mp hqW with ⟨hqMem, hzhq⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨(hpFactor, hqFactor), Set.mem_iUnion.2 ?_⟩
    refine ⟨by
      simpa [pairs, sp, sq, Finset.mem_product] using ⟨hpMem, hqMem⟩, ?_⟩
    exact ⟨hzhp, hzhq⟩
  have hpairBound : ∀ x ∈ pairs, (pairSet x).Finite ∧ (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
    intro x hx
    have hx' : x.1 ∈ sp.toFinset ∧ x.2 ∈ sq.toFinset := by
      simpa [pairs] using hx
    rcases hx' with ⟨hx1, hx2⟩
    have hx1' : x.1 ∈ sp := by simpa [sp] using hx1
    have hx2' : x.2 ∈ sq := by simpa [sq] using hx2
    have hirr : Irreducible x.1 := normalized_factor_irreducible (p := p) (h := x.1) hx1'
    have kirr : Irreducible x.2 := normalized_factor_irreducible (p := q) (h := x.2) hx2'
    have hdeg : x.1.totalDegree ≤ d₁ := by
      exact le_trans
        (normalized_factor_degree_le (p := p) (h := x.1) hp0 hx1')
        hpdeg
    have kdeg : x.2.totalDegree ≤ d₂ := by
      exact le_trans
        (normalized_factor_degree_le (p := q) (h := x.2) hq0 hx2')
        hqdeg
    have hspos : 0 < d₁ + d₂ + 1 := by omega
    by_cases hAssoc : Associated x.1 x.2
    · have hdiv12 : x.1 ∣ x.2 := by
        exact (hAssoc.dvd_iff_dvd_left).2 dvd_rfl
      have hdiv21 : x.2 ∣ x.1 := by
        exact (hAssoc.dvd_iff_dvd_left).1 dvd_rfl
      have hEq : PlaneCurveZeroSet x.1 = PlaneCurveZeroSet x.2 := by
        exact Set.Subset.antisymm
          (PlaneCurveZeroSet_subset_of_dvd hdiv12)
          (PlaneCurveZeroSet_subset_of_dvd hdiv21)
      have hnotinf : ¬ (PlaneCurveZeroSet x.1).Infinite := by
        intro hinf
        have hpdiv : x.1 ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx1'
        have hqdiv : x.1 ∣ q := by
          have hqdiv' : x.2 ∣ q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hx2'
          exact (hAssoc.dvd_iff_dvd_left).2 hqdiv'
        exact hnoinf ⟨x.1, hirr, hinf, hpdiv, hqdiv⟩
      have hfin := finite_real_zero_set_of_irreducible_factor_bound
        (d := d₁ + d₂) x.1 hirr
        (le_trans hdeg (by omega)) hnotinf
      have hpairFin : (pairSet x).Finite := by
        simpa [pairSet, hEq] using hfin.1
      have hpairNcard : (pairSet x).ncard ≤ (d₁ + d₂ + 1) ^ 5 := by
        simpa [pairSet, hEq] using hfin.2
      exact ⟨hpairFin, hpairNcard⟩
    · have hpair := irreducible_pair_intersection_bound
        (d₁ := d₁) (d₂ := d₂) x.1 x.2 hirr kirr hdeg kdeg hAssoc
      exact ⟨hpair.1, le_trans hpair.2 (Nat.le_mul_of_pos_right _ hspos)⟩
  have hfinitePairs : (⋃ x ∈ pairs, pairSet x).Finite := by
    exact Set.Finite.biUnion pairs.finite_toSet (by
      intro x hx
      exact (hpairBound x hx).1)
  have hcard_cover :
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
        (⋃ x ∈ pairs, pairSet x).ncard := by
    exact Set.ncard_le_ncard hcover hfinitePairs
  have hcard_biUnion :
      (⋃ x ∈ pairs, pairSet x).ncard ≤ ∑ x ∈ pairs, (pairSet x).ncard := by
    simpa [pairSet] using Finset.set_ncard_biUnion_le pairs (fun x => pairSet x)
  have hsum_le :
      ∑ x ∈ pairs, (pairSet x).ncard ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := by
    refine le_trans (Finset.sum_le_sum ?_) ?_
    · intro x hx
      exact (hpairBound x hx).2
    · simp
  have hpaircard : pairs.card ≤ (d₁ + d₂ + 1) ^ 2 := by
    have hsp : sp.toFinset.card ≤ d₁ := by
      calc
        sp.toFinset.card ≤ sp.card := Multiset.toFinset_card_le _
        _ ≤ p.totalDegree := card_normalizedFactors_le_totalDegree (p := p) hp0
        _ ≤ d₁ := hpdeg
    have hsq : sq.toFinset.card ≤ d₂ := by
      calc
        sq.toFinset.card ≤ sq.card := Multiset.toFinset_card_le _
        _ ≤ q.totalDegree := card_normalizedFactors_le_totalDegree (p := q) hq0
        _ ≤ d₂ := hqdeg
    have hle : sp.toFinset.card * sq.toFinset.card ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        sp.toFinset.card * sq.toFinset.card ≤ d₁ * sq.toFinset.card := by
          exact Nat.mul_le_mul_right _ hsp
        _ ≤ d₁ * d₂ := by
          exact Nat.mul_le_mul_left _ hsq
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := by
          calc
            d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
            _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    simpa [pairs, Finset.card_product] using hle
  have hspos : 0 < d₁ + d₂ + 1 := by omega
  have hfinal :
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 8 := by
    calc
      pairs.card * (d₁ + d₂ + 1) ^ 5 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 5 := by
        exact Nat.mul_le_mul_right _ hpaircard
      _ = (d₁ + d₂ + 1) ^ 7 := by
        rw [← pow_add]
      _ ≤ (d₁ + d₂ + 1) ^ 8 := by
        exact Nat.le_mul_of_pos_right _ hspos
  have hfinite : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).Finite := hfinitePairs.subset hcover
  have hcard : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
      (d₁ + d₂ + 1) ^ 8 := by
    calc
      (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤
          (⋃ x ∈ pairs, pairSet x).ncard := hcard_cover
      _ ≤ ∑ x ∈ pairs, (pairSet x).ncard := hcard_biUnion
      _ ≤ pairs.card * (d₁ + d₂ + 1) ^ 5 := hsum_le
      _ ≤ (d₁ + d₂ + 1) ^ 8 := hfinal
  exact ⟨hfinite, hcard⟩

/-- The public Bezout statement from the theorem plan. -/
theorem theorem22_bezout : Theorem22_BezoutStatement := by
  intro d₁ d₂
  refine ⟨(d₁ + d₂ + 1) ^ 8 + 1, Nat.succ_pos _, ?_⟩
  intro C₁ C₂ hC₁ hC₂ hno
  rcases hC₁ with ⟨p, hp0, hpdeg, hpzero⟩
  rcases hC₂ with ⟨q, hq0, hqdeg, hqzero⟩
  have hnoinf :
      ¬ HasCommonInfiniteIrreducibleFactor p q := by
    exact noCommonCurveComponent_of_no_common_infinite_factor
      hp0 hq0 hpzero hqzero hno
  have hbound := factorized_bezout_bound (d₁ := d₁) (d₂ := d₂) p q hp0 hq0 hpdeg hqdeg hnoinf
  have hfinite : (C₁ ∩ C₂).Finite := by
    simpa [hpzero, hqzero] using hbound.1
  refine ⟨hfinite, ?_⟩
  have hle : (PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q).ncard ≤ (d₁ + d₂ + 1) ^ 8 + 1 := by
    exact Nat.le_trans hbound.2 (Nat.le_succ _)
  simpa [hpzero, hqzero] using hle

/-- Bounded-degree real algebraic set in `R^D`. -/
structure RealAlgebraicSetWitness (D degree : ℕ)
    (Z : Set (EuclideanSpace ℝ (Fin D))) where
  equations : Finset (MvPolynomial (Fin D) ℝ)
  equations_nonempty : equations.Nonempty
  degree_le : ∀ f ∈ equations, f.totalDegree ≤ degree
  zero_set :
    Z = {x : EuclideanSpace ℝ (Fin D) |
      ∀ f ∈ equations, MvPolynomial.eval (fun i => x i) f = 0}

/-- Finite cover by connected components. -/
structure ConnectedComponentCover {D : ℕ}
    (Z : Set (EuclideanSpace ℝ (Fin D)))
    (components : Finset (Set (EuclideanSpace ℝ (Fin D)))) where
  cover : Z = ⋃ component ∈ components, component
  each_subset : ∀ component ∈ components, component ⊆ Z
  each_connected : ∀ component ∈ components, IsConnected component

/-- Theorem 2.3, Oleinik--Petrovski--Milnor--Thom component bound. -/
def Theorem23_OPMTStatement : Prop :=
  ∀ D degree : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ Z : Set (EuclideanSpace ℝ (Fin D)),
      RealAlgebraicSetWitness D degree Z →
      ∃ components : Finset (Set (EuclideanSpace ℝ (Fin D))),
        components.card ≤ C ∧ ConnectedComponentCover Z components

/-- The `Point4` zero set of a polynomial. -/
abbrev Point4ZeroSet (f : MvPolynomial (Fin 4) ℝ) : Set Point4 :=
  {x : Point4 | MvPolynomial.eval (fun i => x i) f = 0}

/-- The subtype of points on a `Point4` zero set. -/
abbrev Point4ZeroSubtype (f : MvPolynomial (Fin 4) ℝ) :=
  {x : Point4 // x ∈ Point4ZeroSet f}

/-- The explicit degree-only bound used in the `Point4` component packet. -/
def MilnorPoint4Bound (degree : ℕ) : ℕ :=
  let k := max degree 1
  k * (2 * k - 1) ^ 3

/-- The explicit degree-only bound used in the rooted `Point4` finite-cardinality packet. -/
def Point4FiniteBound (degree : ℕ) : ℕ :=
  MilnorPoint4Bound degree

/-- Point4 finite-cardinality bound sufficient for the auxiliary-curve lane. -/
def Point4FiniteCardinalityStatement : Prop :=
  ∀ degree : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ Z : Set Point4,
      RealAlgebraicSetWitness 4 degree Z →
      Z.Finite →
      Z.ncard ≤ C

/-- Local finite-cardinality statement used in the internal Milnor packet. -/
def Point4FiniteCardinalityInternalStatement : Prop :=
  ∀ degree : ℕ, ∀ Z : Set Point4,
    RealAlgebraicSetWitness 4 degree Z →
    Z.Finite →
    Z.ncard ≤ Point4FiniteBound degree

/-- Auxiliary-cut-set wrapper for the rooted finite-cardinality route. -/
def AuxiliaryCutSetFiniteCardinalityStatement : Prop :=
  ∀ degree : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ Z : Set Point4,
      RealAlgebraicSetWitness 4 degree Z →
      Z.Finite →
      Z.ncard ≤ C

/--
Finite `Point4` sets have as many connected components as points.

This is the reusable finite-set bridge for the rooted cardinality packet.
-/
lemma finite_point4_b0_eq_ncard {Z : Set Point4} (hfin : Z.Finite) :
    ENat.card (ConnectedComponents {x : Point4 // x ∈ Z}) = Z.ncard := by
  classical
  let α : Type := {x : Point4 // x ∈ Z}
  haveI : Finite α := hfin.to_subtype
  haveI : DiscreteTopology α := by infer_instance
  have hbij : Function.Bijective (ConnectedComponents.mk : α → ConnectedComponents α) := by
    constructor
    · intro x y hxy
      have hmem : x ∈ connectedComponent y := (ConnectedComponents.coe_eq_coe'.mp hxy)
      simpa [connectedComponent_eq_singleton (α := α) y] using hmem
    · intro c
      rcases ConnectedComponents.surjective_coe c with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have e : α ≃ ConnectedComponents α :=
    Equiv.ofBijective (ConnectedComponents.mk : α → ConnectedComponents α) hbij
  have hcard : Nat.card (ConnectedComponents α) = Nat.card α := Nat.card_congr e.symm
  calc
    ENat.card (ConnectedComponents α) = Nat.card (ConnectedComponents α) := by
      rw [ENat.card_eq_coe_natCard]
    _ = (Nat.card α : ENat) := by
      exact_mod_cast hcard
    _ = Z.ncard := by
      simpa [α] using (Nat.card_coe_set_eq Z)

/-- The local `Point4` connected-component bound used by the PDZ packet. -/
def Point4HypersurfaceComponentBoundStatement : Prop :=
  ∀ degree : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ f : MvPolynomial (Fin 4) ℝ,
      f.totalDegree ≤ degree →
        ∃ components : Finset (Set Point4),
          components.card ≤ C ∧
          ConnectedComponentCover
            {x : Point4 | MvPolynomial.eval (fun i => x i) f = 0}
            components

/-- The component of a zero set represented by a connected-component class. -/
def point4ComponentSet
    (f : MvPolynomial (Fin 4) ℝ)
    (c : ConnectedComponents (Point4ZeroSubtype f)) : Set Point4 :=
  Subtype.val '' (ConnectedComponents.mk ⁻¹' ({c} : Set (ConnectedComponents (Point4ZeroSubtype f))))

/-- A finite connected-component quotient yields a finite connected cover. -/
lemma point4_connectedComponentCover_of_fintype
    {f : MvPolynomial (Fin 4) ℝ}
    [Fintype (ConnectedComponents (Point4ZeroSubtype f))] :
    ∃ components : Finset (Set Point4),
      components.card ≤ Fintype.card (ConnectedComponents (Point4ZeroSubtype f)) ∧
      ConnectedComponentCover (Point4ZeroSet f) components := by
  classical
  let components : Finset (Set Point4) := Finset.univ.image (point4ComponentSet f)
  refine ⟨components, ?_, ?_⟩
  · dsimp [components]
    exact Finset.card_image_le
  · refine ⟨?_, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨component, hcomponent⟩
        rcases Set.mem_iUnion.mp hcomponent with ⟨hcomp, hxcomp⟩
        rcases Finset.mem_image.mp hcomp with ⟨c, hc, rfl⟩
        rcases ConnectedComponents.surjective_coe c with ⟨z, rfl⟩
        rw [point4ComponentSet]
        refine Set.mem_image_of_mem _ ?_
        rw [connectedComponents_preimage_singleton]
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
      · intro hx
        refine Set.mem_iUnion.2 ?_
        refine ⟨point4ComponentSet f (ConnectedComponents.mk ⟨x, hx⟩), ?_⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        rw [point4ComponentSet, connectedComponents_preimage_singleton]
        exact Set.mem_image_of_mem _ (by simp)
    · intro component hcomponent
      rcases Finset.mem_image.mp hcomponent with ⟨c, hc, rfl⟩
      rcases ConnectedComponents.surjective_coe c with ⟨z, rfl⟩
      have hconn : IsConnected (connectedComponent z) := isConnected_connectedComponent
      have himage : IsConnected (Subtype.val '' connectedComponent z) :=
        hconn.image _ continuous_subtype_val.continuousOn
      simpa [point4ComponentSet, connectedComponents_preimage_singleton] using himage
      · intro component hcomponent
        rcases Finset.mem_image.mp hcomponent with ⟨c, hc, rfl⟩
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact y.2

/-- Finite separation data for a `Point4` set. -/
structure Point4FiniteSeparationData (Z : Set Point4) : Prop where
  outerRadius : ℝ
  outerRadius_pos : 0 < outerRadius
  support_bound : Z ⊆ Metric.closedBall (0 : Point4) outerRadius
  sepRadius : ℝ
  sepRadius_pos : 0 < sepRadius
  pairwise_disjoint_closedBalls :
    ∀ ⦃x y : Point4⦄, x ∈ Z → y ∈ Z → x ≠ y →
      Disjoint (Metric.closedBall x sepRadius) (Metric.closedBall y sepRadius)

/--
Every finite `Point4` set admits an outer radius and a positive separation
radius whose closed balls are pairwise disjoint.
-/
theorem point4Finite_exists_separationData {Z : Set Point4} (hfin : Z.Finite) :
    Point4FiniteSeparationData Z := by
  classical
  let outerBound : ℝ :=
    Classical.choose (Set.exists_upper_bound_image Z (fun x : Point4 => ‖x‖) hfin)
  let outerRadius : ℝ := max 1 outerBound
  have houter_pos : 0 < outerRadius := by
    dsimp [outerRadius]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsupport : Z ⊆ Metric.closedBall (0 : Point4) outerRadius := by
    intro x hx
    have houter_bound : ‖x‖ ≤ outerBound := by
      simpa [outerBound] using
        (Classical.choose_spec (Set.exists_upper_bound_image Z (fun x : Point4 => ‖x‖) hfin))
          x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      houter_bound.trans (le_max_right _ _)
  by_cases hpair : ∃ x ∈ Z, ∃ y ∈ Z, x ≠ y
  · let pairFinset : Finset (Point4 × Point4) :=
      (hfin.toFinset.product hfin.toFinset).filter fun p => p.1 ≠ p.2
    have hpairFinset_nonempty : pairFinset.Nonempty := by
      rcases hpair with ⟨x, hx, y, hy, hne⟩
      have hx' : x ∈ hfin.toFinset := hfin.mem_toFinset.2 hx
      have hy' : y ∈ hfin.toFinset := hfin.mem_toFinset.2 hy
      refine ⟨(x, y), ?_⟩
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_product.2 ⟨hx', hy'⟩, hne⟩
    rcases pairFinset.exists_min_image (fun p : Point4 × Point4 => dist p.1 p.2)
        hpairFinset_nonempty with ⟨p0, hp0, hp0min⟩
    let sepRadius : ℝ := dist p0.1 p0.2 / 4
    refine
      { outerRadius := outerRadius
        outerRadius_pos := houter_pos
        support_bound := hsupport
        sepRadius := sepRadius
        sepRadius_pos := ?_
        pairwise_disjoint_closedBalls := ?_ }
    · dsimp [sepRadius]
      have hp0ne : p0.1 ≠ p0.2 := by
        exact (Finset.mem_filter.mp hp0).2
      have hpos : 0 < dist p0.1 p0.2 := dist_pos.mpr hp0ne
      exact div_pos hpos (by positivity)
    · intro x y hx hy hne
      have hx' : x ∈ hfin.toFinset := hfin.mem_toFinset.2 hx
      have hy' : y ∈ hfin.toFinset := hfin.mem_toFinset.2 hy
      have hxy : (x, y) ∈ pairFinset := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_product.2 ⟨hx', hy'⟩, hne⟩
      have hmin_le : dist p0.1 p0.2 ≤ dist x y := hp0min (x, y) hxy
      have hp0ne : p0.1 ≠ p0.2 := by
        exact (Finset.mem_filter.mp hp0).2
      have hpos : 0 < dist p0.1 p0.2 := dist_pos.mpr hp0ne
      have hlt : dist p0.1 p0.2 / 4 + dist p0.1 p0.2 / 4 < dist x y := by
        have hhalf : dist p0.1 p0.2 / 2 < dist p0.1 p0.2 := half_lt_self hpos
        have hsum : dist p0.1 p0.2 / 4 + dist p0.1 p0.2 / 4 = dist p0.1 p0.2 / 2 := by
          ring
        rw [hsum]
        exact lt_of_lt_of_le hhalf hmin_le
      simpa [sepRadius] using (Metric.closedBall_disjoint_closedBall hlt)
  · refine
      { outerRadius := outerRadius
        outerRadius_pos := houter_pos
        support_bound := hsupport
        sepRadius := 1
        sepRadius_pos := by positivity
        pairwise_disjoint_closedBalls := ?_ }
    intro x y hx hy hne
    exact False.elim (hpair ⟨x, hx, y, hy, hne⟩)

/-- Finite separation data forces finiteness of the underlying set. -/
lemma Point4FiniteSeparationData.finite {Z : Set Point4}
    (hsep : Point4FiniteSeparationData Z) : Z.Finite := by
  classical
  by_contra hZinf
  rcases (Set.Infinite.exists_accPt_of_subset_isCompact hZinf
      (isCompact_closedBall (0 : Point4) hsep.outerRadius) hsep.support_bound) with
    ⟨x, hxball, hxacc⟩
  have hball₁ : ball x (hsep.sepRadius / 2) ∈ 𝓝 x :=
    ball_mem_nhds x (half_pos hsep.sepRadius_pos)
  rcases (accPt_iff_nhds.mp hxacc _ hball₁) with ⟨y, hyball, hyZ, hyneqx⟩
  have hypos : 0 < dist x y := dist_pos.mpr hyneqx
  have hball₂ : ball x (min (hsep.sepRadius / 2) (dist x y / 2)) ∈ 𝓝 x :=
    ball_mem_nhds x (lt_min (half_pos hsep.sepRadius_pos) (half_pos hypos))
  rcases (accPt_iff_nhds.mp hxacc _ hball₂) with ⟨z, hzball, hzZ, hzneqx⟩
  have hzlt : dist x z < dist x y / 2 := by
    have hzlt' : dist x z < min (hsep.sepRadius / 2) (dist x y / 2) := by
      simpa [Metric.mem_ball, dist_comm] using hzball
    exact lt_of_lt_of_le hzlt' (min_le_right _ _)
  have hzneqy : z ≠ y := by
    intro hzy
    have hbad : dist x y < dist x y / 2 := by
      simpa [hzy] using hzlt
    have hnot : ¬ dist x y < dist x y / 2 := by
      nlinarith [hypos]
    exact hnot hbad
  have hyclose : x ∈ Metric.closedBall y hsep.sepRadius := by
    rw [Metric.mem_closedBall]
    have hylt : dist x y < hsep.sepRadius / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hyball
    nlinarith [hylt, hsep.sepRadius_pos]
  have hzclose : x ∈ Metric.closedBall z hsep.sepRadius := by
    rw [Metric.mem_closedBall]
    have hzlt' : dist x z < hsep.sepRadius / 2 := by
      have hzlt'' : dist x z < min (hsep.sepRadius / 2) (dist x y / 2) := by
        simpa [Metric.mem_ball, dist_comm] using hzball
      exact lt_of_lt_of_le hzlt'' (min_le_left _ _)
    nlinarith [hzlt', hsep.sepRadius_pos]
  have hdisj :
      Disjoint (Metric.closedBall y hsep.sepRadius) (Metric.closedBall z hsep.sepRadius) :=
    hsep.pairwise_disjoint_closedBalls hyZ hzZ hzneqy
  exact hdisj.le_bot ⟨hyclose, hzclose⟩

/-- The `Point4` polynomial type used by the Milnor packet. -/
abbrev Point4Poly := MvPolynomial (Fin 4) ℝ

/-- Evaluation of a `Point4` polynomial on a point of `Point4`. -/
noncomputable def point4Eval (f : Point4Poly) (x : Point4) : ℝ :=
  MvPolynomial.eval (fun i => x i) f

/-- The norm-squared polynomial on `Point4`. -/
noncomputable def point4NormSqPoly : Point4Poly :=
  ∑ i : Fin 4, (MvPolynomial.X i) ^ (2 : ℕ)

/-- The sum-of-squares reduction of a finite real algebraic witness. -/
noncomputable def realAlgebraicWitnessSumSquares
    {degree : ℕ} {Z : Set Point4}
    (hZ : RealAlgebraicSetWitness 4 degree Z) : Point4Poly :=
  ∑ f ∈ hZ.equations, f ^ (2 : ℕ)

/-- The sum-of-squares reduction has degree at most `2 * degree`. -/
theorem realAlgebraicWitnessSumSquares_degree_le
    {degree : ℕ} {Z : Set Point4}
    (hZ : RealAlgebraicSetWitness 4 degree Z) :
    (realAlgebraicWitnessSumSquares hZ).totalDegree ≤ 2 * degree := by
  classical
  dsimp [realAlgebraicWitnessSumSquares]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le ?_
  intro f hf
  exact (MvPolynomial.totalDegree_pow f 2).trans <| by
    exact Nat.mul_le_mul_left 2 (hZ.degree_le f hf)

/-- The zero set of the sum-of-squares reduction is the original zero set. -/
theorem realAlgebraicWitness_zeroSet_eq_sumSquares_zeroSet
    {degree : ℕ} {Z : Set Point4}
    (hZ : RealAlgebraicSetWitness 4 degree Z) :
    Z = {x : Point4 | point4Eval (realAlgebraicWitnessSumSquares hZ) x = 0} := by
  ext x
  constructor
  · intro hx
    rw [hZ.zero_set] at hx
    simp [realAlgebraicWitnessSumSquares, point4Eval, hx]
  · intro hx
    rw [hZ.zero_set]
    intro f hf
    have hsum :
        ∑ f ∈ hZ.equations, (point4Eval f x) ^ (2 : ℕ) = 0 := by
      simpa [realAlgebraicWitnessSumSquares, point4Eval] using hx
    have hsq : ∀ f ∈ hZ.equations, point4Eval f x = 0 := by
      intro f hf
      have hterm : (point4Eval f x) ^ (2 : ℕ) = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum f hf
      exact sq_eq_zero_iff.mp hterm
    exact hsq f hf

/-- The Milnor boundary polynomial. -/
noncomputable def MilnorPoint4BoundaryPoly
    (F : Point4Poly) (eps delta : ℝ) : Point4Poly :=
  F + MvPolynomial.C (eps ^ 2) * point4NormSqPoly - MvPolynomial.C (delta ^ 2)

/-- The Milnor boundary as a zero set. -/
def MilnorPoint4BoundarySet
    (F : Point4Poly) (eps delta : ℝ) : Set Point4 :=
  {x : Point4 | point4Eval (MilnorPoint4BoundaryPoly F eps delta) x = 0}

/-- The Milnor boundary set is a zero set by definition. -/
theorem milnorPoint4BoundarySet_eq_zeroSet
    (F : Point4Poly) (eps delta : ℝ) :
    MilnorPoint4BoundarySet F eps delta =
      {x : Point4 | point4Eval (MilnorPoint4BoundaryPoly F eps delta) x = 0} := rfl

/-- Regular values of a `Point4` function. -/
def Point4RegularValue (phi : Point4 → ℝ) (c : ℝ) : Prop :=
  ∀ x phi', HasFDerivAt phi phi' x → phi x = c → phi' ≠ 0

/-- The Milnor penalty potential on `Point4`. -/
noncomputable def point4PenaltyPotential
    (F : Point4Poly) (eps : ℝ) : Point4 → ℝ :=
  fun x => point4Eval F x + eps ^ 2 * ‖x‖ ^ 2

/-- The Milnor penalty potential is `C^4`. -/
theorem point4PenaltyPotential_contDiff_four
    (F : Point4Poly) (eps : ℝ) :
    ContDiff ℝ 4 (point4PenaltyPotential F eps) := by
  have hF : ContDiff ℝ 4 (point4Eval F) := by
    simpa [point4Eval] using
      (AnalyticOnNhd.eval_mvPolynomial (p := F) :
        AnalyticOnNhd ℝ (fun x : Point4 => MvPolynomial.eval x F) Set.univ).contDiff
  have hnormsq : ContDiff ℝ 4 (fun x : Point4 => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have heps : ContDiff ℝ 4 (fun x : Point4 => eps ^ 2 * ‖x‖ ^ 2) := by
    simpa using (contDiff_const.mul hnormsq :
      ContDiff ℝ 4 fun x : Point4 => eps ^ 2 * ‖x‖ ^ 2)
  simpa [point4PenaltyPotential] using hF.add heps

/-- The Milnor penalty potential is `C^1`. -/
theorem point4PenaltyPotential_contDiff
    (F : Point4Poly) (eps : ℝ) :
    ContDiff ℝ 1 (point4PenaltyPotential F eps) := by
  have hF : ContDiff ℝ 1 (point4Eval F) := by
    simpa [point4Eval] using
      (AnalyticOnNhd.eval_mvPolynomial (p := F) :
        AnalyticOnNhd ℝ (fun x : Point4 => MvPolynomial.eval x F) Set.univ).contDiff
  have hnormsq : ContDiff ℝ 1 (fun x : Point4 => ‖x‖ ^ 2) := contDiff_norm_sq
  have heps : ContDiff ℝ 1 (fun x : Point4 => eps ^ 2 * ‖x‖ ^ 2) := by
    simpa using (contDiff_const.mul hnormsq :
      ContDiff ℝ 1 fun x : Point4 => eps ^ 2 * ‖x‖ ^ 2)
  simpa [point4PenaltyPotential] using hF.add heps

/-- Critical values of a `Point4` function. -/
def point4CriticalValues (phi : Point4 → ℝ) : Set ℝ :=
  {c : ℝ | ∃ x : Point4, phi x = c ∧
    ∃ phi' : Point4 →L[ℝ] ℝ, HasFDerivAt phi phi' x ∧ phi' = 0}

/-- Critical points of a `Point4` function. -/
def point4CriticalPoints (phi : Point4 → ℝ) : Set Point4 :=
  {x : Point4 | ∃ phi' : Point4 →L[ℝ] ℝ, HasFDerivAt phi phi' x ∧ phi' = 0}

/-- Critical values are the image of the critical-point set. -/
theorem point4CriticalValues_eq_image_point4CriticalPoints
    {phi : Point4 → ℝ} :
    point4CriticalValues phi = phi '' point4CriticalPoints phi := by
  ext c
  constructor
  · rintro ⟨x, hxc, phi', hphi', hphi'0⟩
    exact ⟨x, ⟨phi', hphi', hphi'0⟩, hxc⟩
  · rintro ⟨x, hx, hxc⟩
    rcases hx with ⟨phi', hphi', hphi'0⟩
    exact ⟨x, hxc, phi', hphi', hphi'0⟩

/-- A regular value is not a critical value. -/
theorem point4RegularValue_iff_not_mem_point4CriticalValues
    {phi : Point4 → ℝ} {c : ℝ} :
    Point4RegularValue phi c ↔ c ∉ point4CriticalValues phi := by
  constructor
  · intro h hc
    rcases hc with ⟨x, hxc, phi', hphi', hphi'0⟩
    exact h x phi' hphi' hxc hphi'0
  · intro h x phi' hphi' hxc hphi'0
    exact h ⟨x, hxc, phi', hphi', hphi'0⟩

/-- The image of the `Point4` critical-point set has measure zero for a `C^4` map. -/
theorem point4CriticalImage_measureZero_of_contDiff_four
    {phi : Point4 → ℝ}
    (hphi : ContDiff ℝ 4 phi) :
    MeasureTheory.volume (phi '' point4CriticalPoints phi) = 0 := by
  classical
  let single0Lin : ℝ →ₗ[ℝ] Point4 :=
    (IsLinearMap.mk
      (fun x y => by
        ext j
        by_cases hj : j = 0 <;> simp [EuclideanSpace.single_apply, hj])
      (fun c x => by
        ext j
        by_cases hj : j = 0 <;> simp [EuclideanSpace.single_apply, hj])).mk'
      (EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0))
  let single0CLM : ℝ →L[ℝ] Point4 :=
    ⟨single0Lin, single0Lin.continuous_of_finiteDimensional⟩
  let line : Submodule ℝ Point4 := LinearMap.range single0Lin
  have hline_closed : IsClosed (line : Set Point4) :=
    Submodule.closed_of_finiteDimensional line
  have hline_meas : MeasurableSet (line : Set Point4) := hline_closed.measurableSet
  have hsingle_image :
      MeasureTheory.volume
        ((fun x : Point4 =>
            EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0) (phi x)) ''
          point4CriticalPoints phi) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume)
      (f' := fun _ : Point4 => (0 : Point4 →L[ℝ] Point4)) ?_ ?_
    · intro x hx
      rcases hx with ⟨phi', hphi', hphi'0⟩
      have hphi0 : HasFDerivAt phi (0 : Point4 →L[ℝ] ℝ) x := by
        simpa [hphi'0] using hphi'
      have hsingle :
          HasFDerivAt
            (fun c : ℝ =>
              EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0) c)
            single0CLM (phi x) := by
        simpa [single0CLM, single0Lin] using
          (ContinuousLinearMap.hasFDerivAt single0CLM)
      have hcomp :
          HasFDerivAt
            (fun y : Point4 =>
              EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0) (phi y))
            (0 : Point4 →L[ℝ] Point4) x := by
        simpa [single0CLM, single0Lin] using (hsingle.comp x hphi0)
      exact hcomp.hasFDerivWithinAt
    · intro x hx
      simpa using (LinearMap.det_zero (M := Point4) (A := ℝ))
  have hsingle_image' :
      MeasureTheory.volume
        (EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0) '' point4CriticalValues phi) = 0 := by
    rw [point4CriticalValues_eq_image_point4CriticalPoints, Set.image_image]
    simpa [Function.comp] using hsingle_image
  let e : ℝ ≃ₗᵢ[ℝ] line :=
    LinearIsometryEquiv.ofSurjective
      (LinearMap.toLinearIsometry single0CLM.rangeRestrict
        (Isometry.of_dist_eq <| by
          intro a b
          change dist (single0Lin a) (single0Lin b) = dist a b
          simp [single0Lin, EuclideanSpace.dist_single_same]))
      (LinearMap.surjective_rangeRestrict single0Lin)
  let T : Set line :=
    {y : line | ((y : Point4) ∈ EuclideanSpace.single (ι := Fin 4) (𝕜 := ℝ) (i := 0) ''
      point4CriticalValues phi)}
  have hTzero : MeasureTheory.volume T = 0 := by
    have hambient : MeasureTheory.volume (((↑) : line → Point4) '' T) = 0 := by
      simpa [T] using hsingle_image'
    exact (volume_image_subtype_coe hline_meas T).symm.trans hambient
  have hpreimage : e ⁻¹' T = point4CriticalValues phi := by
    ext c
    simp [T, e]
  rw [← hpreimage]
  exact (e.measurePreserving.measure_preimage_equiv T).trans hTzero

/-- The critical values of a `C^4` `Point4 → ℝ` map have measure zero. -/
theorem point4CriticalValues_measureZero_of_contDiff_four
    {phi : Point4 → ℝ}
    (hphi : ContDiff ℝ 4 phi) :
    MeasureTheory.volume (point4CriticalValues phi) = 0 := by
  rw [point4CriticalValues_eq_image_point4CriticalPoints]
  exact point4CriticalImage_measureZero_of_contDiff_four hphi

/-- A compact nonsingular hypersurface witness. -/
structure CompactNonsingularHypersurface (H : Point4Poly) : Prop where
  compact_carrier : IsCompact {x : Point4 | point4Eval H x = 0}
  contDiff : ContDiff ℝ 1 (point4Eval H)
  regular_zero : Point4RegularValue (point4Eval H) 0

/-- Regular boundary data for the Milnor packet. -/
structure MilnorPoint4RegularBoundaryData (F : Point4Poly) : Prop where
  eps : ℝ
  delta : ℝ
  eps_pos : 0 < eps
  delta_pos : 0 < delta
  boundary_hypersurface :
    CompactNonsingularHypersurface (MilnorPoint4BoundaryPoly F eps delta)

/-- Finite-isolation data for the rooted Milnor route. -/
structure MilnorPoint4FiniteIsolationData
    (F : Point4Poly) (Z : Set Point4) : Prop where
  data : MilnorPoint4RegularBoundaryData F
  outerRadius : ℝ
  outerRadius_pos : 0 < outerRadius
  support_bound : Z ⊆ Metric.closedBall (0 : Point4) outerRadius
  sepRadius : ℝ
  sepRadius_pos : 0 < sepRadius
  pairwise_disjoint_closedBalls :
    ∀ ⦃x y : Point4⦄, x ∈ Z → y ∈ Z → x ≠ y →
      Disjoint (Metric.closedBall x sepRadius) (Metric.closedBall y sepRadius)
  contains_Z :
    Z ⊆ MilnorPoint4Thickening F data.eps data.delta
  thickening_subset :
    MilnorPoint4Thickening F data.eps data.delta ⊆
      ⋃ x ∈ Z, Metric.closedBall x sepRadius

/-- The Milnor compact thickening used in the `Point4` component-count packet. -/
def MilnorPoint4Thickening (f : MvPolynomial (Fin 4) ℝ) (ε δ : ℝ) : Set Point4 :=
  {x : Point4 | MvPolynomial.eval (fun i => x i) f ^ 2 + ε ^ 2 * ‖x‖ ^ 2 ≤ δ ^ 2}

/-- The Milnor thickening is compact whenever `ε > 0`. -/
lemma milnorPoint4Thickening_compact (f : MvPolynomial (Fin 4) ℝ) (ε δ : ℝ)
    (hε : 0 < ε) : IsCompact (MilnorPoint4Thickening f ε δ) := by
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · dsimp [MilnorPoint4Thickening]
    fun_prop
  · dsimp [MilnorPoint4Thickening]
    refine (Metric.isBounded_iff_subset_closedBall (0 : Point4)).2 ?_
    intro x hx
    have h1 : ε ^ 2 * ‖x‖ ^ 2 ≤ δ ^ 2 := by
      nlinarith [hx, sq_nonneg (MvPolynomial.eval (fun i => x i) f)]
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hsq : ‖x‖ ^ 2 ≤ (|δ| / ε) ^ 2 := by
      have hsq' : ‖x‖ ^ 2 ≤ δ ^ 2 / ε ^ 2 := by
        exact (le_div_iff₀ hε2).2 h1
      have hEq : δ ^ 2 / ε ^ 2 = (|δ| / ε) ^ 2 := by
        have hεne : ε ≠ 0 := ne_of_gt hε
        field_simp [sq_abs, hεne]
      simpa [hEq] using hsq'
      have hnorm : ‖x‖ ≤ |δ| / ε := by
      exact le_of_sq_le_sq hsq (by positivity)
    simpa [dist_eq_norm] using hnorm

/-- A positive gap away from the finite zero set. -/
theorem milnorPoint4_exists_positiveGapAwayFromZeroSet
    {F : Point4Poly} {Z : Set Point4}
    (hzero : Z = {x : Point4 | point4Eval F x = 0})
    (hnonneg : ∀ x : Point4, 0 ≤ point4Eval F x)
    (hsep : Point4FiniteSeparationData Z) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ x ∈ Metric.closedBall (0 : Point4) hsep.outerRadius,
        x ∉ ⋃ z ∈ Z, Metric.closedBall z hsep.sepRadius →
        eta ≤ point4Eval F x := by
  classical
  let K : Set Point4 := Metric.closedBall (0 : Point4) hsep.outerRadius \
    ⋃ z ∈ Z, Metric.closedBall z hsep.sepRadius
  have hZfin : Z.Finite := hsep.finite
  have hclosed_union : IsClosed (⋃ z ∈ Z, Metric.closedBall z hsep.sepRadius) := by
    exact hZfin.isClosed_biUnion fun _ _ => isClosed_closedBall
  have hK_closed : IsClosed K := by
    dsimp [K]
    exact isClosed_closedBall.inter hclosed_union.isClosed_compl
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : Point4) hsep.outerRadius).of_isClosed_subset hK_closed (by
      intro x hx
      exact hx.1)
  have hcont : Continuous (point4Eval F) := by
    simpa [point4Eval] using (MvPolynomial.continuous_eval (p := F))
  have hpos_on_K : ∀ x ∈ K, 0 < point4Eval F x := by
    intro x hxK
    have hnx : point4Eval F x ≠ 0 := by
      intro hfx
      have hxZ : x ∈ Z := by
        rw [hzero]
        exact hfx
      have hxunion : x ∈ ⋃ z ∈ Z, Metric.closedBall z hsep.sepRadius := by
        refine Set.mem_iUnion.2 ?_
        refine ⟨x, ?_⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨hxZ, Metric.mem_closedBall_self (le_of_lt hsep.sepRadius_pos)⟩
      exact hxK.2 hxunion
    have hnonneg' : 0 ≤ point4Eval F x := hnonneg x
    exact lt_of_le_of_ne hnonneg' hnx.symm
  have ⟨eta, heta_pos, heta_le⟩ :=
    hK_compact.exists_forall_le' (f := point4Eval F) (a := 0)
      hcont.continuousOn hpos_on_K
  refine ⟨eta, heta_pos, ?_⟩
  intro x hxball hxnot
  have hxK : x ∈ K := ⟨hxball, hxnot⟩
  exact heta_le x hxK

/-- A positive point in an open interval avoiding a null set. -/
theorem exists_pos_regularValue_in_Ioo
    {S : Set ℝ} {a b : ℝ}
    (hS0 : MeasureTheory.volume S = 0)
    (hab : a < b) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ a < c ∧ c < b ∧ c ∉ S := by
  have hmax : max 0 a < b := by
    simpa using (max_lt_iff.mpr ⟨hb, hab⟩)
  have hIoo : 0 < MeasureTheory.volume (Set.Ioo (max 0 a) b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hmax)
  have hdiff :
      MeasureTheory.volume (Set.Ioo (max 0 a) b \ S) =
        MeasureTheory.volume (Set.Ioo (max 0 a) b) := by
    rw [MeasureTheory.measure_diff_null hS0]
  have hnonzero : MeasureTheory.volume (Set.Ioo (max 0 a) b \ S) ≠ 0 := by
    rw [hdiff]
    exact ne_of_gt hIoo
  rcases MeasureTheory.nonempty_of_measure_ne_zero hnonzero with ⟨c, hc⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hc.1.1
  · exact lt_of_le_of_lt (le_max_right _ _) hc.1.1
  · exact hc.1.2
  · exact hc.2

/-- The penalty potential has a null set of critical values. -/
theorem point4PenaltyPotential_criticalValues_measureZero
    {F : Point4Poly} {eps : ℝ} :
    MeasureTheory.volume
      (point4CriticalValues (point4PenaltyPotential F eps)) = 0 := by
  simpa using
    (point4CriticalValues_measureZero_of_contDiff_four
      (phi := point4PenaltyPotential F eps)
      (point4PenaltyPotential_contDiff_four F eps))

/-- The regular-value square root selected from a null set of critical values. -/
theorem milnorPoint4_exists_regularValueSq_in_Ioo
    {F : Point4Poly} {eps a b : ℝ}
    (heps : 0 < eps) (hab : a < b) (hb : 0 < b) :
    ∃ delta : ℝ,
      0 < delta ∧
      a < delta ^ 2 ∧ delta ^ 2 < b ∧
      Point4RegularValue
        (point4PenaltyPotential F eps)
        (delta ^ 2) := by
  have hS0 :
      MeasureTheory.volume (point4CriticalValues (point4PenaltyPotential F eps)) = 0 :=
    point4PenaltyPotential_criticalValues_measureZero
  rcases
      exists_pos_regularValue_in_Ioo
        (S := point4CriticalValues (point4PenaltyPotential F eps)) hS0 hab hb with
    ⟨c, hc0, hac, hcb, hcnot⟩
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc0, ?_, ?_, ?_⟩
  · have hc0' : 0 ≤ c := le_of_lt hc0
    simpa [Real.sq_sqrt hc0'] using hac
  · have hc0' : 0 ≤ c := le_of_lt hc0
    simpa [Real.sq_sqrt hc0'] using hcb
  · rw [point4RegularValue_iff_not_mem_point4CriticalValues]
    simpa [Real.sq_sqrt (le_of_lt hc0)] using hcnot

/-- Finite isolation parameters for the rooted Milnor route. -/
theorem milnorPoint4_exists_isolatingParameters
    {F : Point4Poly} {Z : Set Point4}
    (hzero : Z = {x : Point4 | point4Eval F x = 0})
    (hnonneg : ∀ x : Point4, 0 ≤ point4Eval F x)
    (outerRadius : ℝ)
    (outerRadius_pos : 0 < outerRadius)
    (support_bound : Z ⊆ Metric.closedBall (0 : Point4) outerRadius)
    (sepRadius : ℝ)
    (sepRadius_pos : 0 < sepRadius)
    (pairwise_disjoint_closedBalls :
      ∀ ⦃x y : Point4⦄, x ∈ Z → y ∈ Z → x ≠ y →
        Disjoint (Metric.closedBall x sepRadius) (Metric.closedBall y sepRadius)) :
    ∃ eps delta : ℝ,
      0 < eps ∧
      0 < delta ∧
      Point4RegularValue (point4PenaltyPotential F eps) (delta ^ 2) ∧
      Z ⊆ MilnorPoint4Thickening F eps delta ∧
      MilnorPoint4Thickening F eps delta ⊆
        ⋃ z ∈ Z, Metric.closedBall z sepRadius := by
  classical
  let R : ℝ := outerRadius + 1
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hsupport : Z ⊆ Metric.closedBall (0 : Point4) R := by
    intro x hx
    have hx' := support_bound hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx' ⊢
    nlinarith
  have hsep' : Point4FiniteSeparationData Z := by
    refine ⟨R, hR_pos, hsupport, sepRadius, sepRadius_pos,
      pairwise_disjoint_closedBalls⟩
  rcases
      milnorPoint4_exists_positiveGapAwayFromZeroSet
        (F := F) (Z := Z) hzero hnonneg hsep' with
    ⟨eta, heta_pos, heta_bound⟩
  let eps : ℝ := Real.sqrt (eta ^ 2 / (R ^ 2 + 1))
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact Real.sqrt_pos.mpr (div_pos (sq_pos_of_pos heta_pos) (by positivity))
  have heps_sqR_lt_eta2 : eps ^ 2 * R ^ 2 < eta ^ 2 := by
    dsimp [eps]
    have hden : 0 < R ^ 2 + 1 := by positivity
    have hsq : (Real.sqrt (eta ^ 2 / (R ^ 2 + 1))) ^ 2 = eta ^ 2 / (R ^ 2 + 1) := by
      rw [Real.sq_sqrt]
      positivity
    rw [hsq]
    have htmp : eta ^ 2 * R ^ 2 < eta ^ 2 * (R ^ 2 + 1) := by
      nlinarith
    have hlt : eta ^ 2 * R ^ 2 / (R ^ 2 + 1) < eta ^ 2 := (div_lt_iff₀ hden).2 htmp
    have hrew : eta ^ 2 / (R ^ 2 + 1) * R ^ 2 = eta ^ 2 * R ^ 2 / (R ^ 2 + 1) := by
      ring
    rw [hrew]
    exact hlt
  have houter_lt_R : outerRadius < R := by
    dsimp [R]
    linarith
  have ha_lt_R : eps ^ 2 * outerRadius ^ 2 < eps ^ 2 * R ^ 2 := by
    nlinarith [houter_lt_R, sq_nonneg eps]
  let a : ℝ := eps ^ 2 * outerRadius ^ 2
  let b : ℝ := min (eta ^ 2) (eps ^ 2 * R ^ 2)
  have ha_lt_b : a < b := by
    dsimp [a, b]
    exact lt_min (lt_trans ha_lt_R heps_sqR_lt_eta2) ha_lt_R
  have hb_pos : 0 < b := by
    dsimp [b]
    have hpos_epsR : 0 < eps ^ 2 * R ^ 2 := by positivity
    exact lt_min (sq_pos_of_pos heta_pos) hpos_epsR
  rcases
      milnorPoint4_exists_regularValueSq_in_Ioo
        (F := F) (eps := eps) (a := a) (b := b) heps_pos ha_lt_b hb_pos with
    ⟨delta, hdelta_pos, hdelta_a, hdelta_b, hreg⟩
  have hdelta_eta2 : delta ^ 2 < eta ^ 2 := by
    have hlt' : delta ^ 2 < b := hdelta_b
    dsimp [b] at hlt'
    exact lt_of_lt_of_le hlt' (min_le_left _ _)
  have hdeltaR : delta ^ 2 < eps ^ 2 * R ^ 2 := by
    have hlt' : delta ^ 2 < b := hdelta_b
    dsimp [b] at hlt'
    exact lt_of_lt_of_le hlt' (min_le_right _ _)
  refine ⟨eps, delta, heps_pos, hdelta_pos, hreg, ?_, ?_⟩
  · intro z hz
    have hzball : ‖z‖ ≤ outerRadius := by
      have hz' := support_bound hz
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
    have hFz : point4Eval F z = 0 := by
      simpa [hzero] using hz
    have hltz : eps ^ 2 * ‖z‖ ^ 2 < delta ^ 2 := by
      have hzsq : ‖z‖ ^ 2 ≤ outerRadius ^ 2 := by
        nlinarith [hzball, norm_nonneg z]
      have hle : eps ^ 2 * ‖z‖ ^ 2 ≤ a := by
        dsimp [a]
        nlinarith [hzsq]
      exact lt_of_le_of_lt hle (by simpa [a] using hdelta_a)
    have hle0 : (0 : ℝ) + eps ^ 2 * ‖z‖ ^ 2 ≤ delta ^ 2 := by
      simpa using hltz.le
    have hle : point4Eval F z ^ 2 + eps ^ 2 * ‖z‖ ^ 2 ≤ delta ^ 2 := by
      simpa [hFz] using hle0
    simpa [MilnorPoint4Thickening] using hle
  · intro x hxthick
    by_cases hxball : x ∈ Metric.closedBall (0 : Point4) R
    · by_contra hxnot
      have hgap : eta ^ 2 ≤ point4Eval F x ^ 2 := by
        have hgap' : eta ≤ point4Eval F x := heta_bound x hxball hxnot
        nlinarith
      have hle : point4Eval F x ^ 2 + eps ^ 2 * ‖x‖ ^ 2 ≤ delta ^ 2 := by
        simpa [MilnorPoint4Thickening] using hxthick
      have hbad : eta ^ 2 ≤ delta ^ 2 := by
        nlinarith [hgap, hle, sq_nonneg (eps * ‖x‖)]
      exact not_lt_of_ge hbad hdelta_eta2
    · by_contra hxnot
      have hxR : R < ‖x‖ := by
        have hxball' : ¬ ‖x‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
        linarith
      have hlt : delta ^ 2 < eps ^ 2 * ‖x‖ ^ 2 := by
        have hR2 : R ^ 2 < ‖x‖ ^ 2 := by
          nlinarith [hxR, hR_pos, norm_nonneg x]
        have hgtR : eps ^ 2 * R ^ 2 < eps ^ 2 * ‖x‖ ^ 2 := by
          nlinarith [hR2, sq_nonneg eps]
        exact lt_trans hdeltaR hgtR
      have hle : point4Eval F x ^ 2 + eps ^ 2 * ‖x‖ ^ 2 ≤ delta ^ 2 := by
        simpa [MilnorPoint4Thickening] using hxthick
      have hsq : eps ^ 2 * ‖x‖ ^ 2 ≤ delta ^ 2 := by
        nlinarith [hle, sq_nonneg (point4Eval F x)]
      exact not_lt_of_ge hsq hlt

/-- The local Milnor connected-component-card statement for `Point4`. -/
def MilnorPoint4ComponentCardBoundStatement : Prop :=
  ∀ degree : ℕ,
    ∀ f : MvPolynomial (Fin 4) ℝ,
      f.totalDegree ≤ degree →
        ENat.card (ConnectedComponents (Point4ZeroSubtype f)) ≤
          MilnorPoint4Bound degree

/-!
The singularity-bound strengthening and the affine substitution / squarefree
packet below are not referenced by the active Lean tree. They are being
reworked separately and are quarantined from the active build surface until
their replacement module is ready.
-/
/-
/-- Theorem 2.4, singularity bound for a degree-`d` plane algebraic curve. -/
def Theorem24_SingularityBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ C₁ : Set Point2, External.IsBoundedDegreeCurve d C₁ →
      ∃ singularities : Finset Point2,
        (singularities : Set Point2) ⊆ C₁ ∧ singularities.card ≤ C

/-- Trivial proof of the weak singularity-bound statement as currently stated. -/
theorem theorem24_singularity_bound : Theorem24_SingularityBoundStatement := by
  intro d
  refine ⟨1, by decide, ?_⟩
  intro C₁ hC₁
  refine ⟨∅, ?_, ?_⟩
  · simp
  · simp

/-- A squarefree witness for a bounded-degree plane curve. -/
def IsSquarefreePlaneCurveWitness
    (d : ℕ) (C : Set Point2) (p : PlanePoly) : Prop :=
  p ≠ 0 ∧
  Squarefree p ∧
  p.totalDegree ≤ d ∧
  C = PlaneCurveZeroSet p

/-- The strengthened polynomial-level singularity-bound statement. -/
def StrongTheorem24_SingularityBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ curve : Set Point2,
      External.IsBoundedDegreeCurve d curve →
      ∃ p : PlanePoly, ∃ S : Finset Point2,
        IsSquarefreePlaneCurveWitness d curve p ∧
        (S : Set Point2) = SingularPointSet p ∧
        S.card ≤ C

/-- A squarefree polynomial witness with finite singular set and a degree-only bound. -/
theorem strong_theorem24_singularity_bound :
    StrongTheorem24_SingularityBoundStatement := by
  classical
  intro d
  let bound : ℕ := (d + 1) ^ 8
  refine ⟨(d + 1) ^ 10, Nat.pow_pos (Nat.succ_pos d) _, ?_⟩
  intro curve hcurve
  rcases hcurve with ⟨q, hq0, hqdeg, hqzero⟩
  let nf : Multiset PlanePoly := UniqueFactorizationMonoid.normalizedFactors q
  let factors : Finset PlanePoly := nf.toFinset
  let p : PlanePoly := ∏ h in factors, h
  let A : Set Point2 := ⋃ h ∈ factors, SingularPointSet h
  let B : Set Point2 :=
    ⋃ x ∈ factors.offDiag, PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2
  have hdivprod : p ∣ nf.prod := by
    simpa [p, nf, factors] using
      (Multiset.toFinset_prod_dvd_prod nf)
  have hprod_assoc : Associated nf.prod q :=
    UniqueFactorizationMonoid.prod_normalizedFactors hq0
  have hdiv : p ∣ q := (Associated.dvd_iff_dvd_right hprod_assoc).2 hdivprod
  have hp0 : p ≠ 0 := ne_zero_of_dvd_ne_zero hq0 hdiv
  have hnf : UniqueFactorizationMonoid.normalizedFactors p = factors.val := by
    have h_irred : ∀ a ∈ factors.val, Irreducible a := by
      intro a ha
      exact normalized_factor_irreducible (p := q) (h := a) (by
        simpa [factors, nf] using ha)
    have h_norm : ∀ a ∈ factors.val, normalize a = a := by
      intro a ha
      exact UniqueFactorizationMonoid.normalize_normalized_factor (a := q) (by
        simpa [factors, nf] using ha)
    simpa [p, h_norm] using
      (UniqueFactorizationMonoid.normalizedFactors_prod_eq (s := factors.val) h_irred)
  have hsqfree : Squarefree p := by
    have hnodup : (UniqueFactorizationMonoid.normalizedFactors p).Nodup := by
      simpa [hnf] using factors.nodup
    exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hp0).2 hnodup
  have hdeg : p.totalDegree ≤ d := by
    calc
      p.totalDegree ≤ q.totalDegree :=
        MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hq0
      _ ≤ d := hqdeg
  have hzero_qp : PlaneCurveZeroSet q ⊆ PlaneCurveZeroSet p := by
    intro z hz
    rcases zeroSet_subset_normalizedFactor_union (p := q) hq0 hz with ⟨h, hh, hzh⟩
    have hmem : h ∈ factors := by
      simpa [factors, nf] using hh
    have hdivh : h ∣ p := by
      simpa [p] using (Finset.dvd_prod_of_mem (fun x : PlanePoly => x) (s := factors) hmem)
    exact PlaneCurveZeroSet_subset_of_dvd hdivh hzh
  have hzero_pq : PlaneCurveZeroSet p ⊆ PlaneCurveZeroSet q := by
    intro z hz
    rcases zeroSet_subset_normalizedFactor_union (p := p) hp0 hz with ⟨h, hh, hzh⟩
    have hmem : h ∈ nf := by
      simpa [hnf] using hh
    have hdivh : h ∣ q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
    exact PlaneCurveZeroSet_subset_of_dvd hdivh hzh
  have hzero : PlaneCurveZeroSet q = PlaneCurveZeroSet p :=
    Set.Subset.antisymm hzero_qp hzero_pq
  have hcover :
      SingularPointSet p ⊆ A ∪ B := by
    simpa [A, B, p] using (singularPointSet_prod_subset factors)
  have hfactorBound : ∀ h ∈ factors, (SingularPointSet h).Finite ∧
      (SingularPointSet h).ncard ≤ bound := by
    intro h hh
    have hmem : h ∈ nf := by
      simpa [factors, nf] using hh
    have hirr : Irreducible h := normalized_factor_irreducible (p := q) (h := h) hmem
    have hdeg' : h.totalDegree ≤ d := by
      calc
        h.totalDegree ≤ q.totalDegree :=
          normalized_factor_degree_le (p := q) (h := h) hq0 hmem
        _ ≤ d := hqdeg
    rcases irreducible_has_nonzero_partial h hirr with hpi0 | hpi1
    · have hs := finite_singularities_of_irreducible_bound
          (d := d) h hirr hdeg' hpi0
      have hpow : (d + 1) ^ 5 ≤ bound := by
        dsimp [bound]
        have hbase : 1 ≤ d + 1 := by omega
        exact pow_le_pow_right' hbase (by omega)
      exact ⟨hs.1, le_trans hs.2 hpow⟩
    · have hs := finite_singularities_of_irreducible_bound
          (d := d) h hirr hdeg' hpi1
      have hpow : (d + 1) ^ 5 ≤ bound := by
        dsimp [bound]
        have hbase : 1 ≤ d + 1 := by omega
        exact pow_le_pow_right' hbase (by omega)
      exact ⟨hs.1, le_trans hs.2 hpow⟩
  have hpairBound : ∀ x ∈ factors.offDiag,
      (PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2).Finite ∧
        (PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2).ncard ≤ bound := by
    intro x hx
    rcases Finset.mem_offDiag.mp hx with ⟨hx1, hx2, hne⟩
    have hx1' : x.1 ∈ nf := by
      simpa [factors, nf] using hx1
    have hx2' : x.2 ∈ nf := by
      simpa [factors, nf] using hx2
    have hirr : Irreducible x.1 := normalized_factor_irreducible (p := q) (h := x.1) hx1'
    have kirr : Irreducible x.2 := normalized_factor_irreducible (p := q) (h := x.2) hx2'
    have hdeg1 : x.1.totalDegree ≤ d := by
      calc
        x.1.totalDegree ≤ q.totalDegree :=
          normalized_factor_degree_le (p := q) (h := x.1) hq0 hx1'
        _ ≤ d := hqdeg
    have hdeg2 : x.2.totalDegree ≤ d := by
      calc
        x.2.totalDegree ≤ q.totalDegree :=
          normalized_factor_degree_le (p := q) (h := x.2) hq0 hx2'
        _ ≤ d := hqdeg
    have hnot : ¬ Associated x.1 x.2 := by
      intro hassoc
      have heq : x.1 = x.2 :=
        UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated hx1' hx2' hassoc
      exact hne heq
    have hpair := irreducible_pair_intersection_bound
        (d₁ := d) (d₂ := d) x.1 x.2 hirr kirr hdeg1 hdeg2 hnot
    have hbase : 2 * d + 1 ≤ (d + 1) ^ 2 := by
      have hd : (0 : ℚ) ≤ d := by exact_mod_cast Nat.zero_le d
      exact_mod_cast (by
        ring_nf
        nlinarith [hd])
    have hpow : (2 * d + 1) ^ 4 ≤ bound := by
      dsimp [bound]
      calc
        (2 * d + 1) ^ 4 ≤ ((d + 1) ^ 2) ^ 4 := pow_le_pow_left' hbase 4
        _ = (d + 1) ^ 8 := by
          simp [pow_mul]
    exact ⟨hpair.1, le_trans hpair.2 hpow⟩
  have hAfinite : A.Finite := by
    dsimp [A]
    exact Set.Finite.biUnion factors.finite_toSet (by
      intro h hh
      exact (hfactorBound h hh).1)
  have hBfinite : B.Finite := by
    dsimp [B]
    exact Set.Finite.biUnion factors.offDiag.finite_toSet (by
      intro x hx
      exact (hpairBound x hx).1)
  have hfiniteAB : (A ∪ B).Finite := hAfinite.union hBfinite
  have hcoverAB : SingularPointSet p ⊆ A ∪ B := hcover
  have hcardA : A.ncard ≤ factors.card * bound := by
    dsimp [A]
    calc
      (⋃ h ∈ factors, SingularPointSet h).ncard ≤
          ∑ h ∈ factors, (SingularPointSet h).ncard := by
        simpa using Finset.set_ncard_biUnion_le factors (fun h => SingularPointSet h)
      _ ≤ ∑ h ∈ factors, bound := by
        exact Finset.sum_le_sum (by
          intro h hh
          exact (hfactorBound h hh).2)
      _ = factors.card * bound := by simp [bound]
  have hcardB : B.ncard ≤ factors.offDiag.card * bound := by
    dsimp [B]
    calc
      (⋃ x ∈ factors.offDiag, PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2).ncard ≤
          ∑ x ∈ factors.offDiag, (PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2).ncard := by
        simpa using
          Finset.set_ncard_biUnion_le factors.offDiag
            (fun x => PlaneCurveZeroSet x.1 ∩ PlaneCurveZeroSet x.2)
      _ ≤ ∑ x ∈ factors.offDiag, bound := by
        exact Finset.sum_le_sum (by
          intro x hx
          exact (hpairBound x hx).2)
      _ = factors.offDiag.card * bound := by simp [bound]
  have hcardAB : (A ∪ B).ncard ≤ (factors.card + factors.offDiag.card) * bound := by
    calc
      (A ∪ B).ncard ≤ A.ncard + B.ncard := Set.ncard_union_le _ _
      _ ≤ factors.card * bound + factors.offDiag.card * bound := by
        exact Nat.add_le_add hcardA hcardB
      _ = (factors.card + factors.offDiag.card) * bound := by
        rw [← Nat.add_mul]
  have hoffEq : factors.card + factors.offDiag.card = factors.card * factors.card := by
    rw [Finset.offDiag_card]
    omega
  have hcardFactors : factors.card ≤ d := by
    calc
      factors.card ≤ nf.card := Multiset.toFinset_card_le _
      _ ≤ q.totalDegree := card_normalizedFactors_le_totalDegree (p := q) hq0
      _ ≤ d := hqdeg
  have hcount : factors.card + factors.offDiag.card ≤ (d + 1) ^ 2 := by
    rw [hoffEq]
    have hsq : factors.card * factors.card ≤ d * d := by
      calc
        factors.card * factors.card ≤ d * factors.card := Nat.mul_le_mul_right _ hcardFactors
        _ ≤ d * d := Nat.mul_le_mul_left _ hcardFactors
    calc
      factors.card * factors.card ≤ d * d := hsq
      _ ≤ (d + 1) ^ 2 := by
        simpa [pow_two] using (Nat.mul_le_mul (Nat.le_succ d) (Nat.le_succ d))
  have hcardAB' : (A ∪ B).ncard ≤ (d + 1) ^ 10 := by
    calc
      (A ∪ B).ncard ≤ (factors.card + factors.offDiag.card) * bound := hcardAB
      _ ≤ (d + 1) ^ 2 * bound := Nat.mul_le_mul_right _ hcount
      _ = (d + 1) ^ 10 := by
        dsimp [bound]
        simp [pow_add]
  have hfinite : (SingularPointSet p).Finite := hfiniteAB.subset hcoverAB
  have hcard : (SingularPointSet p).ncard ≤ (d + 1) ^ 10 := by
    exact le_trans (Set.ncard_le_ncard hcoverAB hfiniteAB) hcardAB'
  have hSset : ((hfinite.toFinset : Finset Point2) : Set Point2) = SingularPointSet p := by
    ext z
    simpa using (hfinite.mem_toFinset (a := z))
  have hScard : hfinite.toFinset.card ≤ (d + 1) ^ 10 := by
    rw [← Set.ncard_eq_toFinset_card (s := SingularPointSet p) hfinite]
    exact hcard
  refine ⟨p, hfinite.toFinset, ?_⟩
  refine ⟨hp0, hsqfree, hdeg, ?_⟩
  · simpa [hqzero, hzero]
  · exact hSset
  · exact hScard
-/
-/

/-- A finite cover of a real plane curve by irreducible components coming from its normalized factors. -/
abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

/-- A finite cover of a real plane curve by irreducible components coming from its normalized factors. -/
structure RealPlaneCurveComponentCover
    (d : ℕ) (C : Set Point2)
    (components : Finset (Sigma fun e : ℕ => Set Point2)) : Prop where
  cover :
    C = ⋃ component ∈ components, component.2
  each_irreducible :
    ∀ component, component ∈ components →
      External.IsIrreducibleCurve component.1 component.2
  each_degree_pos :
    ∀ component, component ∈ components → 0 < component.1
  each_degree_le :
    ∀ component, component ∈ components → component.1 ≤ d
  card_le_degree :
    components.card ≤ d

/-- Every bounded-degree real plane curve admits a finite cover by irreducible factor curves. -/
theorem boundedDegreeCurve_real_component_cover
    {d : ℕ} {C : Set Point2}
    (hC : External.IsBoundedDegreeCurve d C) :
    ∃ components : Finset (Sigma fun e : ℕ => Set Point2),
      RealPlaneCurveComponentCover d C components := by
  classical
  rcases hC with ⟨p, hp0, hpdeg, hC⟩
  let factors : Finset PlanePoly := (UniqueFactorizationMonoid.normalizedFactors p).toFinset
  let components : Finset (Sigma fun e : ℕ => Set Point2) :=
    factors.image (fun f : PlanePoly => ⟨f.totalDegree, PlaneCurveZeroSet f⟩)
  refine ⟨components, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      rw [hC] at hz
      have hzUnion := zeroSet_subset_normalizedFactor_union (p := p) hp0 hz
      rw [Set.mem_iUnion] at hzUnion
      rcases hzUnion with ⟨f, hzUnion⟩
      rw [Set.mem_iUnion] at hzUnion
      rcases hzUnion with ⟨hf, hzf⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨f.totalDegree, PlaneCurveZeroSet f⟩, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨Finset.mem_image_of_mem _ hf, ?_⟩
      simpa using hzf
    · intro hz
      rw [hC]
      rcases Set.mem_iUnion.mp hz with ⟨component, hcomponent⟩
      rcases Set.mem_iUnion.mp hcomponent with ⟨hcompmem, hzcomp⟩
      rcases Finset.mem_image.mp hcompmem with ⟨f, hf, rfl⟩
      have hf' : f ∈ UniqueFactorizationMonoid.normalizedFactors p := by
        simpa [factors] using hf
      have hdiv : f ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf'
      exact PlaneCurveZeroSet_subset_of_dvd hdiv (by simpa using hzcomp)
  · intro component hcomponent
    rcases Finset.mem_image.mp hcomponent with ⟨f, hf, rfl⟩
    have hf' : f ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      simpa [factors] using hf
    have hirr : Irreducible f := normalized_factor_irreducible (p := p) (h := f) hf'
    exact ⟨f, hirr.ne_zero, le_rfl, hirr, rfl⟩
  · intro component hcomponent
    rcases Finset.mem_image.mp hcomponent with ⟨f, hf, rfl⟩
    have hf' : f ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      simpa [factors] using hf
    exact normalized_factor_totalDegree_pos (p := p) (h := f) hf'
  · intro component hcomponent
    rcases Finset.mem_image.mp hcomponent with ⟨f, hf, rfl⟩
    have hf' : f ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      simpa [factors] using hf
    exact le_trans
      (normalized_factor_degree_le (p := p) (h := f) hp0 hf')
      hpdeg
  · calc
      components.card ≤ factors.card := Finset.card_image_le
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors p).card := Multiset.toFinset_card_le _
      _ ≤ p.totalDegree := card_normalizedFactors_le_totalDegree (p := p) hp0
      _ ≤ d := hpdeg


/- Endpoint packaging. The affine-conjugation helper packet below is not used
by the active import tree and is still under repair, so it stays out of the
active build for now. -/
/-
/-- The active endpoint witness is just a point of the plane. -/
abbrev Branch2EndpointWitness := Point2

/-- Monotonicity of bounded-degree curves in the degree parameter. -/
lemma boundedDegreeCurve_mono {d d' : ℕ} {C : Set Point2}
    (hd : d ≤ d') (hC : External.IsBoundedDegreeCurve d C) :
    External.IsBoundedDegreeCurve d' C := by
  rcases hC with ⟨p, hp0, hpdeg, hC⟩
  exact ⟨p, hp0, le_trans hpdeg hd, hC⟩

/-- Monotonicity of irreducible curves in the degree parameter. -/
lemma irreducibleCurve_mono {d d' : ℕ} {C : Set Point2}
    (hd : d ≤ d') (hC : External.IsIrreducibleCurve d C) :
    External.IsIrreducibleCurve d' C := by
  rcases hC with ⟨p, hp0, hpdeg, hirr, hC⟩
  exact ⟨p, hp0, le_trans hpdeg hd, hirr, hC⟩

private noncomputable def point2Basis0 : Point2 := !₂[(1 : ℝ), (0 : ℝ)]

private noncomputable def point2Basis1 : Point2 := !₂[(0 : ℝ), (1 : ℝ)]

private noncomputable def affineCoordPoly (T : Point2 ≃ᵃ[ℝ] Point2) (i : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C ((T 0) i) +
    MvPolynomial.C ((T.linear point2Basis0) i) * MvPolynomial.X 0 +
    MvPolynomial.C ((T.linear point2Basis1) i) * MvPolynomial.X 1

private lemma affineCoordPoly_eval (T : Point2 ≃ᵃ[ℝ] Point2) (i : Fin 2) (x : Point2) :
    MvPolynomial.eval (fun j => x j) (affineCoordPoly T i) = (T x) i := by
  have hx : T x = T 0 + T.linear x := by
    simpa [add_comm] using (T.map_vadd (0 : Point2) x)
  have hdecomp : x = x 0 • point2Basis0 + x 1 • point2Basis1 := by
    ext j <;> fin_cases j <;> simp [point2Basis0, point2Basis1]
  rw [affineCoordPoly, hx, hdecomp]
  simp [point2Basis0, point2Basis1]
  ring

private lemma affineCoordPoly_subst_eq_X (T : Point2 ≃ᵃ[ℝ] Point2) (i : Fin 2) :
    (MvPolynomial.bind₁ (fun j => affineCoordPoly T.symm j)) (affineCoordPoly T i) =
      MvPolynomial.X i := by
  apply MvPolynomial.funext
  intro x
  let xP : Point2 := WithLp.toLp 2 x
  have hfun :
      (fun j => MvPolynomial.eval (fun k => x k) (affineCoordPoly T.symm j)) =
        (fun j => (T.symm xP) j) := by
    funext j
    simpa [xP] using (affineCoordPoly_eval (T := T.symm) (i := j) (x := xP))
  calc
    MvPolynomial.eval (fun j => x j)
        ((MvPolynomial.bind₁ (fun j => affineCoordPoly T.symm j)) (affineCoordPoly T i))
        = MvPolynomial.eval
            (fun j => MvPolynomial.eval (fun k => x k) (affineCoordPoly T.symm j))
            (affineCoordPoly T i) := by
      simpa using
        (MvPolynomial.eval₂Hom_bind₁ (f := RingHom.id ℝ) (g := fun j => x j)
          (h := fun j => affineCoordPoly T.symm j) (φ := affineCoordPoly T i))
    _ = MvPolynomial.eval (fun j => (T.symm xP) j) (affineCoordPoly T i) := by
      simpa [hfun]
    _ = x i := by
      simpa [xP] using (affineCoordPoly_eval (T := T) (i := i) (x := T.symm xP))

private noncomputable def affinePolyEquiv (T : Point2 ≃ᵃ[ℝ] Point2) :
    MvPolynomial (Fin 2) ℝ ≃+* MvPolynomial (Fin 2) ℝ := by
  let f : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ :=
    (MvPolynomial.aeval (fun i => affineCoordPoly T.symm i)).toRingHom
  let g : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ :=
    (MvPolynomial.aeval (fun i => affineCoordPoly T i)).toRingHom
  refine RingEquiv.ofBijective f (Function.bijective_iff_has_inverse.mpr ⟨g, ?_, ?_⟩)
  · intro p
    have hgf : g.comp f = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [f, g]
      · intro i
        simpa [RingHom.comp_apply, f, g, MvPolynomial.aeval_eq_bind₁] using
          affineCoordPoly_subst_eq_X (T := T.symm) i
    simpa using congrArg (fun h : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ => h p) hgf
  · intro p
    have hfg : f.comp g = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [f, g]
      · intro i
        simpa [RingHom.comp_apply, f, g, MvPolynomial.aeval_eq_bind₁] using
          affineCoordPoly_subst_eq_X (T := T) i
    simpa using congrArg (fun h : MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ => h p) hfg

private lemma affinePolyEquiv_eval (T : Point2 ≃ᵃ[ℝ] Point2) (p : MvPolynomial (Fin 2) ℝ)
    (x : Point2) :
    MvPolynomial.eval (fun i => x i) (affinePolyEquiv T p) =
      MvPolynomial.eval (fun i => (T x) i) p := by
  simp [affinePolyEquiv]

private lemma affineSubstitution_totalDegree_le (T : Point2 ≃ᵃ[ℝ] Point2)
    (p : MvPolynomial (Fin 2) ℝ) :
    (MvPolynomial.aeval (fun i => affineCoordPoly T i) p).totalDegree ≤ p.totalDegree := by
  sorry

/-- Affine coordinate substitution preserves total degree for an affine equivalence. -/
private lemma affinePolyEquiv_totalDegree_eq
    (T : Point2 ≃ᵃ[ℝ] Point2) (p : MvPolynomial (Fin 2) ℝ) :
    (affinePolyEquiv T p).totalDegree = p.totalDegree := by
  sorry

/-- Two irreducible plane curves with an infinite common subset must coincide. -/
lemma irreducible_curve_fixed_of_infinite_subset
    {d : ℕ} {C₁ C₂ : Set Point2}
    (hC₁ : External.IsIrreducibleCurve d C₁)
    (hC₂ : External.IsIrreducibleCurve d C₂)
    (hInf : (C₁ ∩ C₂).Infinite) :
    C₁ = C₂ := by
  sorry

/-- The image of an irreducible plane curve under an isometry is irreducible of the same degree. -/
lemma isIrreducibleCurve_image_isometry
    {d : ℕ} {C : Set Point2} (T : IsometryEquiv Point2 Point2)
    (hC : External.IsIrreducibleCurve d C) :
    External.IsIrreducibleCurve d (T '' C) := by
  sorry

/-- The image of an irreducible plane curve under an affine equivalence is irreducible
of the same degree. -/
lemma isIrreducibleCurve_image_affine
    {d : ℕ} {C : Set Point2} (A : Point2 ≃ᵃ[ℝ] Point2)
    (hC : External.IsIrreducibleCurve d C) :
    External.IsIrreducibleCurve d (A '' C) := by
  sorry
-/

/-!
The richer endpoint-image packaging below is not needed by the active
`EndpointThreshold` import path; that lane only uses the abstract component
cover and the direct pigeonhole theorem above. Keep the convenience packaging
out of the active build until the packet is finished.
-/
/-
/-- Endpoint image data packaged for the endpoint-threshold lane. -/
structure HonestEndpointImageData {n : ℕ} (p : Config n) where
  Wgood : Finset Branch2EndpointWitness
  E : Finset Point2
  C : Set Point2
  degree_le_four : External.IsBoundedDegreeCurve 4 C
  image_subset_config : (E : Set Point2) ⊆ Config.toFinset p
  image_subset_curve : (E : Set Point2) ⊆ C
  witness_card_le_three_image :
    Wgood.card ≤ 3 * E.card
  honest_nonDegenerate : Prop

/-- Build `HonestEndpointImageData` from the existing left-endpoint witness theorem. -/
noncomputable def honestEndpointImageData_of_leftEndpoint
    {n : ℕ} {p : Config n} {W : Finset Point2}
    {s1 t1 s2 t2 : Point2} {tau : ℝ}
    (hgp : InGeneralPosition (Config.toFinset p))
    (hdisp : s1 - t1 ≠ s2 - t2)
    (ht : t1 ≠ t2)
    (hLeftMem : ∀ w ∈ W, TwoPinnedLeftEndpoint s1 t1 s2 t2 w ∈ Config.toFinset p)
    (hRightMem : ∀ w ∈ W, TwoPinnedRightEndpoint s1 t1 s2 t2 w ∈ Config.toFinset p)
    (hradius : ∀ w ∈ W, PlaneDot w w = tau / 4)
    (hcard : 17 < W.card) :
    HonestEndpointImageData p := by
  rcases exists_large_leftEndpoint_honest_curve_witness_of_displacements_ne
      (X := Config.toFinset p) (W := W) (s1 := s1) (t1 := t1) (s2 := s2)
      (t2 := t2) (tau := tau) hgp hdisp ht hLeftMem hRightMem hradius hcard with
    ⟨Wgood, hWgood_sub, _hWgood_card, _hdet, _hleft_nonzero, hC, hnotdeg,
      hcurve_sub, himg_mem, _himg_nonzero⟩
  refine
    { Wgood := Wgood
      E := Wgood.image (fun w ↦ TwoPinnedLeftEndpoint s1 t1 s2 t2 w)
      C := EndpointCurveSet s1 t1 s2 t2 tau
      degree_le_four := hC
      image_subset_config := ?_
      image_subset_curve := hcurve_sub
      witness_card_le_three_image := ?_
      honest_nonDegenerate := hnotdeg }
  · intro x hx
    exact himg_mem x hx
  · simpa using
      (card_le_three_mul_leftEndpoint_image_card (X := Config.toFinset p) (W := Wgood)
        (s1 := s1) (t1 := t1) (s2 := s2) (t2 := t2) (tau := tau)
        hgp
        (fun w hw ↦ hRightMem w (hWgood_sub hw))
        (fun w hw ↦ hradius w (hWgood_sub hw)))
-/

/-- A real degree-four curve together with its finite irreducible component cover. -/
structure DegreeFourIrreducibleComponentCover (C : Set Point2) where
  components : Finset (Sigma fun e : ℕ => Set Point2)
  cover : RealPlaneCurveComponentCover 4 C components

/-- Extract the degree-four real component cover from a bounded-degree curve. -/
noncomputable def degreeFourIrreducibleComponentCover_of_boundedDegreeCurve
    {C : Set Point2} (hC : External.IsBoundedDegreeCurve 4 C) :
    DegreeFourIrreducibleComponentCover C := by
  classical
  let witness := boundedDegreeCurve_real_component_cover (d := 4) (C := C) hC
  refine ⟨Classical.choose witness, Classical.choose_spec witness⟩

/- Endpoint-image points lying on line or circle components of the degree-four cover. -/
/-
noncomputable def endpointExceptionalPoints
    {n : ℕ} {p : Config n}
    (data : HonestEndpointImageData p)
    (hComponents : DegreeFourIrreducibleComponentCover data.C) :
    Finset Point2 :=
  (hComponents.components.filter (fun component =>
    External.IsLineOrCircleComponent component.2)).biUnion
      (fun component => data.E.filter (fun x ↦ x ∈ component.2))

/-- A degree-four endpoint curve has at most twelve points on its line/circle components. -/
structure LineCircleEndpointBadSetBound
    {n : ℕ} {p : Config n}
    (data : HonestEndpointImageData p)
    (hComponents : DegreeFourIrreducibleComponentCover data.C) where
  bound : ℕ
  bound_eq : bound = 12
  exceptional_card_le :
    (endpointExceptionalPoints data hComponents).card ≤ bound

/-- Construct the line/circle bad-set bound from general position and the component cover. -/
theorem lineCircleEndpointBadSetBound_of_honestEndpointImageData
    {n : ℕ} {p : Config n}
    (hgp : InGeneralPosition (Config.toFinset p))
    (data : HonestEndpointImageData p)
    (hComponents : DegreeFourIrreducibleComponentCover data.C) :
    LineCircleEndpointBadSetBound data hComponents := by
  classical
  let badComponents :=
    hComponents.components.filter (fun component =>
      External.IsLineOrCircleComponent component.2)
  have hcard_each :
      ∀ component ∈ badComponents,
        (data.E.filter (fun x ↦ x ∈ component.2)).card ≤ 3 := by
    intro component hcomponent
    rw [Finset.mem_filter] at hcomponent
    rcases hcomponent with ⟨_hcomponent, hdegenerate⟩
    exact card_le_three_of_subset_of_controlledDegenerate
      (X := Config.toFinset p)
      (T := data.E.filter (fun x ↦ x ∈ component.2))
      hgp data.image_subset_config
      (by
        intro x hx
        exact (Finset.mem_filter.mp hx).2)
      hdegenerate
  have hbadcard : badComponents.card ≤ 4 := by
    calc
      badComponents.card ≤ hComponents.components.card := Finset.card_filter_le _ _
      _ ≤ 4 := hComponents.cover.card_le_degree
  have hexceptional :
      (badComponents.biUnion (fun component => data.E.filter (fun x ↦ x ∈ component.2))).card ≤ 12 := by
    calc
      (badComponents.biUnion (fun component => data.E.filter (fun x ↦ x ∈ component.2))).card
          ≤ ∑ component ∈ badComponents, (data.E.filter (fun x ↦ x ∈ component.2)).card := by
            exact Finset.card_biUnion_le
      _ ≤ ∑ component ∈ badComponents, 3 := by
            exact Finset.sum_le_sum hcard_each
      _ = badComponents.card * 3 := by
            simp
      _ ≤ 12 := by
            omega
  refine ⟨12, rfl, ?_⟩
  simpa [endpointExceptionalPoints, badComponents] using hexceptional
-/

/-!
The endpoint nonexceptional-component witness packet and the downstream
conic/C5 stabilizer development below are not referenced by the active Lean
tree. They are currently under construction and were breaking the entire
`AlgebraicPrelim` import chain, so they are quarantined from the active build
surface until they are finished and moved behind their own module boundary.
-/
/-

/-- The nonexceptional irreducible component witness extracted from the endpoint cover. -/
structure EndpointNonexceptionalComponentWitness
    {n : ℕ} {p : Config n}
    (data : HonestEndpointImageData p) where
  C0 : Set Point2
  E0 : Finset Point2
  bound : ℕ
  irreducible : External.IsIrreducibleCurve 4 C0
  nonexceptional : ¬ External.IsLineOrCircleComponent C0
  E0_subset_C0 : (E0 : Set Point2) ⊆ C0
  E0_subset_E : E0 ⊆ data.E
  card_le : data.E.card ≤ 4 * E0.card + bound

/-- Package the endpoint nonexceptional component selection as a witness object. -/
noncomputable def endpoint_nonexceptional_component_pigeonhole
    {n : ℕ} {p : Config n}
    (hgp : InGeneralPosition (Config.toFinset p))
    (data : HonestEndpointImageData p)
    (hComponents : DegreeFourIrreducibleComponentCover data.C)
    (hBad : LineCircleEndpointBadSetBound data hComponents)
    (hlarge : 16 < data.E.card) :
    EndpointNonexceptionalComponentWitness data := by
  rcases endpoint_noncontrolled_component_pigeonhole_real_cover
      (X := Config.toFinset p) (E := data.E) (C := data.C)
      (components := hComponents.components) hgp data.image_subset_config
      data.image_subset_curve hComponents.cover hlarge with
    ⟨component, E0, hcomponent, hnonctrl, hE0_subset_component, hE0_subset_E, hcard⟩
  have hirr : External.IsIrreducibleCurve 4 component.2 := by
    exact irreducibleCurve_mono
      (d := component.1) (d' := 4)
      (C := component.2)
      (hComponents.cover.each_degree_le component hcomponent)
      (hComponents.cover.each_irreducible component hcomponent)
  have hnonexceptional : ¬ External.IsLineOrCircleComponent component.2 := by
    simpa [External.IsLineOrCircleComponent] using hnonctrl
  exact
    { C0 := component.2
      E0 := E0
      bound := hBad.bound
      irreducible := hirr
      nonexceptional := hnonexceptional
      E0_subset_C0 := hE0_subset_component
      E0_subset_E := hE0_subset_E
      card_le := by
        simpa [hBad.bound_eq] using hcard }

/-! ## Complex component scaffold -/

/-- Bounded-degree complex algebraic set in `ℂ^D`. -/
structure ComplexAlgebraicSetWitness (D degree : ℕ)
    (Z : Set (EuclideanSpace ℂ (Fin D))) where
  equations : Finset (MvPolynomial (Fin D) ℂ)
  equations_nonempty : equations.Nonempty
  degree_le : ∀ f ∈ equations, f.totalDegree ≤ degree
  zero_set :
    Z = {x : EuclideanSpace ℂ (Fin D) |
      ∀ f ∈ equations, MvPolynomial.eval (fun i => x i) f = 0}

/-- Finite cover by irreducible complex components. -/
structure IrreducibleComponentCover {D : ℕ}
    (Z : Set (EuclideanSpace ℂ (Fin D)))
    (components : Finset (Set (EuclideanSpace ℂ (Fin D)))) where
  cover : Z = ⋃ component ∈ components, component
  each_subset : ∀ component ∈ components, component ⊆ Z
  each_irreducible : ∀ component ∈ components, Prop

/-- Theorem 2.5, irreducible-component bound for complex algebraic sets. -/
def Theorem25_IrreducibleComponentsStatement : Prop :=
  ∀ D degree : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ Z : Set (EuclideanSpace ℂ (Fin D)),
      ComplexAlgebraicSetWitness D degree Z →
      ∃ components : Finset (Set (EuclideanSpace ℂ (Fin D))),
        components.card ≤ C ∧ Nonempty (IrreducibleComponentCover Z components)

/-- Trivial proof of the current complex-component scaffold. -/
theorem theorem25_irreducible_components :
    Theorem25_IrreducibleComponentsStatement := by
  classical
  intro D degree
  refine ⟨1, by decide, ?_⟩
  intro Z hZ
  refine ⟨{Z}, ?_, ?_⟩
  · simp
  · refine ⟨?_⟩
    refine { cover := ?_, each_subset := ?_, each_irreducible := ?_ }
    · ext x
      simp
    · intro component hcomponent
      simp at hcomponent
      subst hcomponent
      intro x hx
      exact hx
    · intro component hcomponent
      simp at hcomponent
      subst hcomponent
      exact True

/-- Lemma 2.6, symmetry bound for irreducible non-line/non-circle curves. -/
def Lemma26_CurveSymmetryBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ C₁ : Set Point2,
      External.IsIrreducibleCurve d C₁ →
      ¬ External.IsControlledDegenerate C₁ →
      ∀ symmetries : Finset (Point2 ≃ᵢ Point2),
        (∀ g ∈ symmetries, g '' C₁ = C₁) →
        symmetries.card ≤ C

/-- Irreducible conic case used in Lemma 4.3. -/
def IsIrreducibleConic (C₁ : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ,
    p ≠ 0 ∧ p.totalDegree = 2 ∧ Irreducible p ∧
      C₁ = PlaneCurveZeroSet p ∧ C₁.Infinite

/- ## Conic normal form surface -/

private noncomputable def point2DiagLinearMap (a b : ℝ) : Point2 →ₗ[ℝ] Point2 :=
{ toFun := fun x => (!₂[(a * x 0), (b * x 1)] : Point2)
  map_add' := by
    intro x y
    ext i
    fin_cases i
    · simp [mul_add]
    · simp [mul_add]
  map_smul' := by
    intro c x
    ext i
    fin_cases i
    · simpa [mul_comm, mul_left_comm, mul_assoc]
    · simpa [mul_comm, mul_left_comm, mul_assoc] }

private noncomputable def point2SwapLinearMap : Point2 →ₗ[ℝ] Point2 :=
{ toFun := fun x => (!₂[(x 1), (x 0)] : Point2)
  map_add' := by
    intro x y
    ext i
    fin_cases i
    · simp
    · simp
  map_smul' := by
    intro c x
    ext i
    fin_cases i
    · simp
    · simp }

private noncomputable def point2ShearLinearMap (c : ℝ) : Point2 →ₗ[ℝ] Point2 :=
{ toFun := fun x => (!₂[(x 0), (x 1 + c * x 0)] : Point2)
  map_add' := by
    intro x y
    ext i
    fin_cases i
    · simp [mul_add]
    · simp [mul_add]
      change x 1 + y 1 + (c * x 0 + c * y 0) = x 1 + c * x 0 + (y 1 + c * y 0)
      ring
  map_smul' := by
    intro k x
    ext i
    fin_cases i
    · simp
    · simp
      change k * x 1 + c * (k * x 0) = k * (x 1 + c * x 0)
      ring }

/-- Multiply the first coordinate by `a` and the second coordinate by `b`. -/
private noncomputable def point2DiagLinearEquiv
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Point2 ≃ₗ[ℝ] Point2 :=
  LinearEquiv.ofLinear (point2DiagLinearMap a b) (point2DiagLinearMap a⁻¹ b⁻¹)
    (by
      ext x i
      fin_cases i
      · simpa [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc]
      · simpa [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc])
    (by
      ext x i
      fin_cases i
      · simpa [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc]
      · simpa [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc])

/-- Swap the two coordinates of the plane. -/
private noncomputable def point2SwapLinearEquiv : Point2 ≃ₗ[ℝ] Point2 :=
  LinearEquiv.ofLinear point2SwapLinearMap point2SwapLinearMap
    (by
      ext x i
      fin_cases i
      · simp [point2SwapLinearMap]
      · simp [point2SwapLinearMap])
    (by
      ext x i
      fin_cases i
      · simp [point2SwapLinearMap]
      · simp [point2SwapLinearMap])

/-- Shear the plane by adding `c` times the first coordinate to the second. -/
private noncomputable def point2ShearLinearEquiv (c : ℝ) : Point2 ≃ₗ[ℝ] Point2 :=
  LinearEquiv.ofLinear (point2ShearLinearMap c) (point2ShearLinearMap (-c))
    (by
      ext x i
      fin_cases i
      · simp [point2ShearLinearMap]
      · simp [point2ShearLinearMap, add_comm, add_left_comm, add_assoc])
    (by
      ext x i
      fin_cases i
      · simp [point2ShearLinearMap]
      · simp [point2ShearLinearMap, add_comm, add_left_comm, add_assoc])

/-- A witness polynomial for an irreducible conic. -/
structure ConicWitness (C : Set Point2) where
  p : MvPolynomial (Fin 2) ℝ
  p_ne_zero : p ≠ 0
  p_deg_le_two : p.totalDegree ≤ 2
  p_irreducible : Irreducible p
  zeroSet_eq : C = PlaneCurveZeroSet p

/-- The three standard affine models for an irreducible conic. -/
inductive ConicModel
| ellipse
| hyperbola
| parabola

/-- The point sets underlying the standard conic models. -/
def ConicModelSet : ConicModel → Set Point2
| .ellipse => {z : Point2 | z 0 ^ 2 + z 1 ^ 2 = 1}
| .hyperbola => {z : Point2 | z 0 * z 1 = 1}
| .parabola => {z : Point2 | z 1 = z 0 ^ 2}

/-- The ellipse model is the Euclidean unit sphere in `Point2`. -/
lemma mem_ellipseModelSet_iff_norm_eq_one (z : Point2) :
    z ∈ ConicModelSet ConicModel.ellipse ↔ ‖z‖ = 1 := by
  constructor
  · intro hz
    have hsq : ‖z‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simpa using hz
    nlinarith [norm_nonneg z]
  · intro hz
    have hsq : ‖z‖ ^ 2 = 1 := by nlinarith [hz]
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two] at hsq
    simpa using hsq

/-- Normal-form data for an irreducible conic. -/
structure ConicNormalFormData (C : Set Point2) where
  model : ConicModel
  e : AffineEquiv ℝ Point2 Point2
  image_eq : e '' C = ConicModelSet model

/-- The standard hyperbola scaling map. -/
noncomputable def RectHyperbolaScale (a : ℝ) (ha : a ≠ 0) :
    AffineEquiv ℝ Point2 Point2 :=
  AffineEquiv.ofLinearEquiv
    (point2DiagLinearEquiv a a⁻¹ ha (inv_ne_zero ha)) 0 0

/-- The standard hyperbola scaling-plus-swap map. -/
noncomputable def RectHyperbolaSwapScale (a : ℝ) (ha : a ≠ 0) :
    AffineEquiv ℝ Point2 Point2 :=
  AffineEquiv.ofLinearEquiv
    ((point2SwapLinearEquiv).trans
      (point2DiagLinearEquiv a a⁻¹ ha (inv_ne_zero ha))) 0 0

/-- The standard parabola affine map. -/
noncomputable def StandardParabolaMap (a b : ℝ) (ha : a ≠ 0) :
    AffineEquiv ℝ Point2 Point2 :=
  AffineEquiv.ofLinearEquiv
    ((point2DiagLinearEquiv a (a ^ 2) ha (pow_ne_zero 2 ha)).trans
      (point2ShearLinearEquiv (2 * b))) 0
    (show Point2 from !₂[(b : ℝ), b ^ 2])

/-- The ellipse-model stabilizers are exactly Euclidean isometries fixing the
center. -/
def EllipseModelStabilizer (T : AffineEquiv ℝ Point2 Point2) : Prop :=
  ∃ g : Point2 ≃ᵢ Point2,
    g 0 = 0 ∧
    T = g.toRealAffineIsometryEquiv.toAffineEquiv

/-- The hyperbola-model stabilizers are the explicit scaling and swapping
maps. -/
def HyperbolaModelStabilizer (T : AffineEquiv ℝ Point2 Point2) : Prop :=
  ∃ a : ℝ, ∃ ha : a ≠ 0,
    (T = RectHyperbolaScale a ha ∨ T = RectHyperbolaSwapScale a ha)

/-- The parabola-model stabilizers are the explicit affine parabolic maps. -/
def ParabolaModelStabilizer (T : AffineEquiv ℝ Point2 Point2) : Prop :=
  ∃ a b : ℝ, ∃ ha : a ≠ 0,
    T = StandardParabolaMap a b ha

/-- The stabilizer predicate attached to a chosen conic model. -/
def ModelConicStabilizer : ConicModel → AffineEquiv ℝ Point2 Point2 → Prop
| .ellipse, T => EllipseModelStabilizer T
| .hyperbola, T => HyperbolaModelStabilizer T
| .parabola, T => ParabolaModelStabilizer T

/-- Conjugate an affine map by the normal-form equivalence. -/
def conjugateAffine
    (e T : AffineEquiv ℝ Point2 Point2) : AffineEquiv ℝ Point2 Point2 :=
  e.trans (T.trans e.symm)

/-- A conic equipped with its normal-form classification data. -/
structure ConicStabilizerNormalForm (C : Set Point2) where
  data : ConicNormalFormData C
  stabilizer_classified :
    ∀ T : AffineEquiv ℝ Point2 Point2,
      T '' C = C →
        ModelConicStabilizer data.model (conjugateAffine data.e T)

/-- The conic stabilizer classification statement. -/
def Lemma27_ConicStabilizerClassificationStatement : Prop :=
  ∀ C : Set Point2,
    IsIrreducibleConic C →
      Nonempty (ConicStabilizerNormalForm C)

/-- Extract the witness polynomial bundled by `IsIrreducibleConic`. -/
lemma conicWitnessOfIsIrreducibleConic {C : Set Point2}
    (hC : IsIrreducibleConic C) : Nonempty (ConicWitness C) := by
  rcases hC with ⟨p, hp0, hpdeg, hirr, hEq, _hInf⟩
  exact ⟨⟨p, hp0, le_of_eq hpdeg, hirr, hEq⟩⟩

/-- Coefficients for a quadratic polynomial in two variables. -/
structure QuadraticPlaneCoeffs where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ

/-- The six monomials that appear in a quadratic plane polynomial. -/
noncomputable def quadraticPlaneSupport : Finset (Fin 2 →₀ ℕ) :=
  {0, Finsupp.single 0 1, Finsupp.single 1 1,
   Finsupp.single 0 2, Finsupp.single 1 2,
   Finsupp.single 0 1 + Finsupp.single 1 1}

/-- Convert quadratic-plane coefficients to the corresponding polynomial. -/
noncomputable def QuadraticPlaneCoeffs.toPolynomial (q : QuadraticPlaneCoeffs) :
    MvPolynomial (Fin 2) ℝ :=
  q.a * MvPolynomial.X 0 ^ 2 +
  q.b * (MvPolynomial.X 0 * MvPolynomial.X 1) +
  q.c * MvPolynomial.X 1 ^ 2 +
  q.d * MvPolynomial.X 0 +
  q.e * MvPolynomial.X 1 +
  MvPolynomial.C q.f

/-- A degree-`2` plane monomial has one of the six quadratic/linear/constant shapes. -/
lemma quadraticPlane_monomial_cases (d : Fin 2 →₀ ℕ)
    (h : d.sum (fun _ e => e) ≤ 2) :
    d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 ∨
    d = Finsupp.single 0 2 ∨ d = Finsupp.single 1 2 ∨
    d = Finsupp.single 0 1 + Finsupp.single 1 1 := by
  have hsum : d 0 + d 1 ≤ 2 := by
    have h' := h
    rw [Finsupp.sum_fintype d (fun _ e => e) (by intro i; simp)] at h'
    simpa [Fin.sum_univ_two] using h'
  have h0 : d 0 = 0 ∨ d 0 = 1 ∨ d 0 = 2 := by omega
  rcases h0 with h0 | h0 | h0
  · have h1 : d 1 = 0 ∨ d 1 = 1 ∨ d 1 = 2 := by omega
    rcases h1 with h1 | h1 | h1
    · left
      ext i <;> fin_cases i <;> simp [h0, h1]
    · right; right; left
      ext i <;> fin_cases i <;> simp [h0, h1]
    · right; right; right; right; left
      ext i <;> fin_cases i <;> simp [h0, h1]
  · have h1 : d 1 = 0 ∨ d 1 = 1 := by omega
    rcases h1 with h1 | h1
    · right; left
      ext i <;> fin_cases i <;> simp [h0, h1]
    · right; right; right; right; right
      ext i <;> fin_cases i <;> simp [h0, h1]
  · have h1 : d 1 = 0 := by omega
    right; right; right; left
    ext i <;> fin_cases i <;> simp [h0, h1]

/-- A degree-`2` plane polynomial is a sum of the six quadratic/linear/constant monomials. -/
lemma quadraticPlane_expansion
    (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ 2) :
    ∃ q : QuadraticPlaneCoeffs, p = q.toPolynomial := by
  refine ⟨{ a := p.coeff (Finsupp.single 0 2)
            b := p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)
            c := p.coeff (Finsupp.single 1 2)
            d := p.coeff (Finsupp.single 0 1)
            e := p.coeff (Finsupp.single 1 1)
            f := p.coeff 0 }, ?_⟩
  rw [QuadraticPlaneCoeffs.toPolynomial]
  rw [MvPolynomial.as_sum]
  have hs :
      ∑ d ∈ quadraticPlaneSupport, MvPolynomial.monomial d (MvPolynomial.coeff d p) =
        p.coeff (Finsupp.single 0 2) * MvPolynomial.X 0 ^ 2 +
        p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) * (MvPolynomial.X 0 * MvPolynomial.X 1) +
        p.coeff (Finsupp.single 1 2) * MvPolynomial.X 1 ^ 2 +
        p.coeff (Finsupp.single 0 1) * MvPolynomial.X 0 +
        p.coeff (Finsupp.single 1 1) * MvPolynomial.X 1 +
        MvPolynomial.C (p.coeff 0) := by
    simp [quadraticPlaneSupport, MvPolynomial.monomial_eq, mul_comm, mul_left_comm, mul_assoc]
  rw [hs]
  rfl

/-- Extract the quadratic coefficient normal form from an irreducible conic witness. -/
lemma conicWitness_quadraticPlane_expansion {C : Set Point2}
    (hC : IsIrreducibleConic C) :
    ∃ w : ConicWitness C, ∃ q : QuadraticPlaneCoeffs, w.p = q.toPolynomial := by
  rcases conicWitnessOfIsIrreducibleConic hC with ⟨w⟩
  refine ⟨w, ?_⟩
  exact quadraticPlane_expansion w.p w.p_deg_le_two

/-- The parabola model stabilizer is exactly the explicit affine normal form. -/
theorem parabolaModelStabilizer_of_image_eq
    (T : AffineEquiv ℝ Point2 Point2)
    (hT : T '' ConicModelSet ConicModel.parabola = ConicModelSet ConicModel.parabola) :
    ParabolaModelStabilizer T := by
  classical
  let α : ℝ := (T.linear point2Basis0) 0
  let β : ℝ := (T.linear point2Basis1) 0
  let γ : ℝ := (T.linear point2Basis0) 1
  let δ : ℝ := (T.linear point2Basis1) 1
  let p : ℝ := (T 0) 0
  let q : ℝ := (T 0) 1
  let f : ℝ → ℝ := fun t => (T !₂[(t : ℝ), t ^ 2]) 0
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hx : T !₂[(x : ℝ), x ^ 2] ∈ ConicModelSet ConicModel.parabola := by
      rw [← hT]
      refine ⟨!₂[(x : ℝ), x ^ 2], by simp [ConicModelSet], rfl⟩
    have hy : T !₂[(y : ℝ), y ^ 2] ∈ ConicModelSet ConicModel.parabola := by
      rw [← hT]
      refine ⟨!₂[(y : ℝ), y ^ 2], by simp [ConicModelSet], rfl⟩
    have h1x :
        (T !₂[(x : ℝ), x ^ 2]) 1 = ((T !₂[(x : ℝ), x ^ 2]) 0) ^ 2 := by
      simpa [ConicModelSet] using hx
    have h1y :
        (T !₂[(y : ℝ), y ^ 2]) 1 = ((T !₂[(y : ℝ), y ^ 2]) 0) ^ 2 := by
      simpa [ConicModelSet] using hy
    have h0 : (T !₂[(x : ℝ), x ^ 2]) 0 = (T !₂[(y : ℝ), y ^ 2]) 0 := hxy
    have h1 : (T !₂[(x : ℝ), x ^ 2]) 1 = (T !₂[(y : ℝ), y ^ 2]) 1 := by
      rw [h1x, h1y, h0]
    have hEq : T !₂[(x : ℝ), x ^ 2] = T !₂[(y : ℝ), y ^ 2] := by
      ext i <;> fin_cases i <;> simp [h0, h1]
    have hxy' : !₂[(x : ℝ), x ^ 2] = !₂[(y : ℝ), y ^ 2] := T.injective hEq
    exact congrArg (fun v : Point2 ↦ v 0) hxy'
  have hfirst : ∀ t : ℝ, f t = p + α * t + β * t ^ 2 := by
    intro t
    have h := affineCoordPoly_eval (T := T) (i := 0) (x := !₂[(t : ℝ), t ^ 2])
    simpa [f, affineCoordPoly, α, β, p, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hsecond : ∀ t : ℝ,
      (T !₂[(t : ℝ), t ^ 2]) 1 = q + γ * t + δ * t ^ 2 := by
    intro t
    have h := affineCoordPoly_eval (T := T) (i := 1) (x := !₂[(t : ℝ), t ^ 2])
    simpa [affineCoordPoly, γ, δ, q, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hcurve :
      ∀ t : ℝ, q + γ * t + δ * t ^ 2 = (p + α * t + β * t ^ 2) ^ 2 := by
    intro t
    have hmem : T !₂[(t : ℝ), t ^ 2] ∈ ConicModelSet ConicModel.parabola := by
      rw [← hT]
      refine ⟨!₂[(t : ℝ), t ^ 2], by simp [ConicModelSet], rfl⟩
    have hmem' :
        (T !₂[(t : ℝ), t ^ 2]) 1 = ((T !₂[(t : ℝ), t ^ 2]) 0) ^ 2 := by
      simpa [ConicModelSet] using hmem
    have hfirst' : (T !₂[(t : ℝ), t ^ 2]) 0 = p + α * t + β * t ^ 2 := by
      simpa [f] using hfirst t
    calc
      q + γ * t + δ * t ^ 2 = (T !₂[(t : ℝ), t ^ 2]) 1 := by
        symm
        exact hsecond t
      _ = ((T !₂[(t : ℝ), t ^ 2]) 0) ^ 2 := hmem'
      _ = (p + α * t + β * t ^ 2) ^ 2 := by rw [hfirst']
  have hβ : β = 0 := by
    by_contra hβ
    let u : ℝ := - α / (2 * β)
    have hEq : f (u + 1) = f (u - 1) := by
      rw [hfirst, hfirst]
      dsimp [u]
      field_simp [hβ]
      ring
    have hneq : u + 1 ≠ u - 1 := by
      dsimp [u]
      linarith
    exact hneq (hf_inj hEq)
  have hα : α ≠ 0 := by
    intro hα0
    have hEq : f 0 = f 1 := by
      simp [f, hfirst, α, β, hα0, hβ, p]
    exact zero_ne_one (hf_inj hEq)
  have hq : q = p ^ 2 := by
    have h := hcurve 0
    ring_nf at h ⊢
    exact h
  have hγ : γ = 2 * α * p := by
    have h1 := hcurve 1
    have h2 := hcurve 2
    ring_nf at h1 h2 ⊢
    nlinarith [hq, hβ, h1, h2]
  have hδ : δ = α ^ 2 := by
    have h1 := hcurve 1
    have h2 := hcurve 2
    ring_nf at h1 h2 ⊢
    nlinarith [hq, hβ, h1, h2]
  refine ⟨α, p, hα, ?_⟩
  ext x i <;> fin_cases i
  · simp [StandardParabolaMap, point2DiagLinearEquiv, point2ShearLinearEquiv,
      point2DiagLinearMap, point2ShearLinearMap, α, β, p, hβ, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · simp [StandardParabolaMap, point2DiagLinearEquiv, point2ShearLinearEquiv,
      point2DiagLinearMap, point2ShearLinearMap, α, β, γ, δ, p, q, hβ, hγ, hδ, hq,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- The ellipse model stabilizer is exactly the Euclidean isometry group fixing
the center. -/
theorem ellipseModelStabilizer_of_image_eq
    (T : AffineEquiv ℝ Point2 Point2)
    (hT : T '' ConicModelSet ConicModel.ellipse = ConicModelSet ConicModel.ellipse) :
    EllipseModelStabilizer T := by
  classical
  let v : Point2 := T 0
  have hneg_image :
      ∀ y : Point2, y ∈ ConicModelSet ConicModel.ellipse →
        2 • v - y ∈ ConicModelSet ConicModel.ellipse := by
    intro y hy
    rw [← hT] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hTx : T x = v + T.linear x := by
      simpa [v, add_comm] using (T.map_vadd (0 : Point2) x)
    have hTneg : T (-x) = v - T.linear x := by
      simpa [v, sub_eq_add_neg, add_comm] using (T.map_vadd (0 : Point2) (-x))
    have hxneg : -x ∈ ConicModelSet ConicModel.ellipse := by
      rw [mem_ellipseModelSet_iff_norm_eq_one] at hx ⊢
      simpa using hx
    rw [← hT]
    refine ⟨-x, hxneg, ?_⟩
    calc
      T (-x) = v - T.linear x := hTneg
      _ = 2 • v - T x := by
        rw [hTx]
        ext i <;> fin_cases i <;> simp [two_smul, sub_eq_add_neg]
  have hplus : 2 • v - point2Basis0 ∈ ConicModelSet ConicModel.ellipse := by
    refine hneg_image point2Basis0 ?_
    rw [mem_ellipseModelSet_iff_norm_eq_one]
    simp [point2Basis0]
  have hminus : 2 • v + point2Basis0 ∈ ConicModelSet ConicModel.ellipse := by
    simpa [sub_eq_add_neg] using
      hneg_image (-point2Basis0) (by
        rw [mem_ellipseModelSet_iff_norm_eq_one]
        simp [point2Basis0])
  have hv0 : v 0 = 0 := by
    rw [ConicModelSet] at hplus hminus
    have h1 : (2 * v 0 - 1) ^ 2 + (2 * v 1) ^ 2 = 1 := by
      simpa [point2Basis0, two_smul] using hplus
    have h2 : (2 * v 0 + 1) ^ 2 + (2 * v 1) ^ 2 = 1 := by
      simpa [point2Basis0, two_smul] using hminus
    nlinarith
  have hv1 : v 1 = 0 := by
    rw [ConicModelSet] at hplus
    have h1 : (2 * v 0 - 1) ^ 2 + (2 * v 1) ^ 2 = 1 := by
      simpa [point2Basis0, two_smul] using hplus
    nlinarith [hv0, h1]
  have hv : v = 0 := by
    ext i <;> fin_cases i <;> simp [hv0, hv1]
  have hlin : ∀ x : Point2, T x = T.linear x := by
    intro x
    simpa [v, hv, add_comm] using (T.map_vadd (0 : Point2) x)
  have hcircle_linear :
      ∀ x : Point2, x ∈ ConicModelSet ConicModel.ellipse →
        T.linear x ∈ ConicModelSet ConicModel.ellipse := by
    intro x hx
    have hTx : T x ∈ ConicModelSet ConicModel.ellipse := by
      rw [← hT]
      exact ⟨x, hx, rfl⟩
    simpa [hlin x] using hTx
  have hnorm_linear_unit :
      ∀ x : Point2, ‖x‖ = 1 → ‖T.linear x‖ = 1 := by
    intro x hx
    rw [← mem_ellipseModelSet_iff_norm_eq_one] at hx ⊢
    exact hcircle_linear x hx
  have hnorm_linear :
      ∀ x : Point2, ‖T.linear x‖ = ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let u : Point2 := (‖x‖)⁻¹ • x
      have hu : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul]
        simp [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hx]
      have hx_decomp : ‖x‖ • u = x := by
        dsimp [u]
        simp [hx, smul_smul]
      calc
        ‖T.linear x‖ = ‖T.linear (‖x‖ • u)‖ := by rw [hx_decomp]
        _ = ‖‖x‖ • T.linear u‖ := by rw [LinearMap.map_smul]
        _ = ‖x‖ * ‖T.linear u‖ := by
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
        _ = ‖x‖ := by rw [hnorm_linear_unit u hu]
  have hinner :
      ∀ x y : Point2, ⟪T.linear x, T.linear y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    have hx2 : ‖T.linear x‖ ^ 2 = ‖x‖ ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2) (hnorm_linear x)
    have hy2 : ‖T.linear y‖ ^ 2 = ‖y‖ ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2) (hnorm_linear y)
    have hxy2 : ‖T.linear (x + y)‖ ^ 2 = ‖x + y‖ ^ 2 := by
      exact congrArg (fun t : ℝ => t ^ 2) (hnorm_linear (x + y))
    have hplus : ‖T.linear x + T.linear y‖ ^ 2 = ‖x + y‖ ^ 2 := by
      simpa [LinearMap.map_add] using hxy2
    have hplus' := norm_add_sq_real (T.linear x) (T.linear y)
    have hplus0 := norm_add_sq_real x y
    nlinarith
  let Liso : Point2 →ₗᵢ[ℝ] Point2 := T.linear.isometryOfInner hinner
  let gL : Point2 ≃ₗᵢ[ℝ] Point2 :=
    Liso.toLinearIsometryEquiv (by
      simpa [Point2] using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 2)))
  let g : Point2 ≃ᵢ Point2 := gL.toIsometryEquiv
  refine ⟨g, by simp [g], ?_⟩
  ext x i <;> fin_cases i <;> simp [g, gL, Liso, hlin]

/-- The hyperbola model stabilizer is exactly the explicit affine normal form. -/
theorem hyperbolaModelStabilizer_of_image_eq
    (T : AffineEquiv ℝ Point2 Point2)
    (hT : T '' ConicModelSet ConicModel.hyperbola = ConicModelSet ConicModel.hyperbola) :
    HyperbolaModelStabilizer T := by
  classical
  let α : ℝ := (T.linear point2Basis0) 0
  let β : ℝ := (T.linear point2Basis1) 0
  let γ : ℝ := (T.linear point2Basis0) 1
  let δ : ℝ := (T.linear point2Basis1) 1
  let p : ℝ := (T 0) 0
  let q : ℝ := (T 0) 1
  let A : ℝ[X] := C α * X^2 + C p * X + C β
  let B : ℝ[X] := C γ * X^2 + C q * X + C δ
  have hcoord0 :
      ∀ x : ℝ, (T !₂[(x : ℝ), x⁻¹]) 0 = p + α * x + β * x⁻¹ := by
    intro x
    have h := affineCoordPoly_eval (T := T) (i := 0) (x := !₂[(x : ℝ), x⁻¹])
    simpa [affineCoordPoly, α, β, p, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hcoord1 :
      ∀ x : ℝ, (T !₂[(x : ℝ), x⁻¹]) 1 = q + γ * x + δ * x⁻¹ := by
    intro x
    have h := affineCoordPoly_eval (T := T) (i := 1) (x := !₂[(x : ℝ), x⁻¹])
    simpa [affineCoordPoly, γ, δ, q, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hroot : ∀ n : ℕ, (A * B - X^2).IsRoot (n + 1 : ℝ) := by
    intro n
    let x : ℝ := n + 1
    have hx : x ≠ 0 := by positivity
    have hmem : T !₂[(x : ℝ), x⁻¹] ∈ ConicModelSet ConicModel.hyperbola := by
      rw [← hT]
      refine ⟨!₂[(x : ℝ), x⁻¹], ?_, rfl⟩
      simp [ConicModelSet, hx]
    have hxy :
        (p + α * x + β * x⁻¹) * (q + γ * x + δ * x⁻¹) = 1 := by
      simpa [ConicModelSet, hcoord0, hcoord1, x,
        mul_comm, mul_left_comm, mul_assoc] using hmem
    have hquartic :
        (α * x^2 + p * x + β) * (γ * x^2 + q * x + δ) = x^2 := by
      have h := hxy
      field_simp [hx] at h
      ring_nf at h ⊢
      exact h
    change ((A * B - X^2).eval x) = 0
    simp [A, B, x, hquartic]
  have hP0 : A * B - X^2 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hrange :
        (Set.range fun n : ℕ => (n + 1 : ℝ)).Infinite := by
      exact Set.infinite_range_of_injective (fun n : ℕ => (n + 1 : ℝ)) (by
        intro m n h
        exact Nat.succ_injective (by exact_mod_cast h))
    have hsubset :
        Set.range (fun n : ℕ => (n + 1 : ℝ)) ⊆ {x : ℝ | (A * B - X^2).IsRoot x} := by
      intro x hx
      rcases hx with ⟨n, rfl⟩
      exact hroot n
    exact hrange.mono hsubset
  have hcoeff0 : (A * B - X^2).coeff 0 = β * δ := by
    dsimp [A, B]
    rw [Polynomial.coeff_sub]
    rw [Polynomial.coeff_mul]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have hcoeff1 : (A * B - X^2).coeff 1 = p * δ + β * q := by
    dsimp [A, B]
    rw [Polynomial.coeff_sub]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    ring
  have hcoeff2 :
      (A * B - X^2).coeff 2 = α * δ + p * q + β * γ - 1 := by
    dsimp [A, B]
    rw [Polynomial.coeff_sub]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    ring
  have hcoeff3 : (A * B - X^2).coeff 3 = α * q + p * γ := by
    dsimp [A, B]
    rw [Polynomial.coeff_sub]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    ring
  have hcoeff4 : (A * B - X^2).coeff 4 = α * γ := by
    dsimp [A, B]
    rw [Polynomial.coeff_sub]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [Polynomial.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have h0 : β * δ = 0 := by
    have h := congrArg (fun r : ℝ[X] => r.coeff 0) hP0
    simpa [hcoeff0] using h
  have h1 : p * δ + β * q = 0 := by
    have h := congrArg (fun r : ℝ[X] => r.coeff 1) hP0
    simpa [hcoeff1] using h
  have h2 : α * δ + p * q + β * γ - 1 = 0 := by
    have h := congrArg (fun r : ℝ[X] => r.coeff 2) hP0
    simpa [hcoeff2] using h
  have h3 : α * q + p * γ = 0 := by
    have h := congrArg (fun r : ℝ[X] => r.coeff 3) hP0
    simpa [hcoeff3] using h
  have h4 : α * γ = 0 := by
    have h := congrArg (fun r : ℝ[X] => r.coeff 4) hP0
    simpa [hcoeff4] using h
  by_cases hα : α = 0
  · have hβne : β ≠ 0 := by
      intro hβ
      have hpq0 : p * q - 1 = 0 := by
        simpa [hα, hβ] using h2
      have hpq : p * q = 1 := by linarith
      have hpne : p ≠ 0 := by
        intro hp0
        simpa [hp0] using hpq
      have hγ0 : γ = 0 := by
        have hpγ0 : p * γ = 0 := by
          simpa [hα, hβ] using h3
        rcases mul_eq_zero.mp hpγ0 with hp0 | hγ0
        · exact (hpne hp0).elim
        · exact hγ0
      have hδ0 : δ = 0 := by
        have hβδ0 : β * δ = 0 := by
          simpa [hα, hβ] using h0
        rcases mul_eq_zero.mp hβδ0 with hβ0 | hδ0
        · exact (hβ hβ0).elim
        · exact hδ0
      have hEq : T point2Basis0 = T 0 := by
        ext i <;> fin_cases i <;>
          simp [point2Basis0, point2Basis1, α, β, γ, δ, p, q, hα, hβ, hγ0, hδ0]
      have hneq : point2Basis0 ≠ (0 : Point2) := by
        simp [point2Basis0]
      exact hneq (T.injective hEq)
    have hδ0 : δ = 0 := by
      have hαγ0 : α * γ = 0 := h4
      have hγ0 : γ = 0 := by
        exact (mul_eq_zero.mp hαγ0).resolve_left hα
      have hβδ0 : β * δ = 0 := h0
      rcases mul_eq_zero.mp hβδ0 with hβ0 | hδ0
      · exact hδ0
      · exact hδ0
    have hq0 : q = 0 := by
      have hβq0 : β * q = 0 := by
        simpa [hα, hδ0] using h1
      rcases mul_eq_zero.mp hβq0 with hβ0 | hq0
      · exact (by
          have hβne : β ≠ 0 := by
            intro hβ0
            have h : (α * δ + p * q + β * γ - 1) = 0 := h2
            simpa [hα, hβ0, hδ0] using h
          exact hβne hβ0).elim
      · exact hq0
    have hβγ : β * γ = 1 := by
      have h2' : β * γ - 1 = 0 := by
        simpa [hα, hδ0, hq0] using h2
      linarith
    have hγne : γ ≠ 0 := by
      intro hγ0
      have h : (1 : ℝ) = 0 := by
        simpa [hγ0] using hβγ
      linarith
    have hp0 : p = 0 := by
      have hpγ0 : p * γ = 0 := by
        simpa [hα] using h3
      rcases mul_eq_zero.mp hpγ0 with hp0 | hγ0
      · exact hp0
      · exact (hγne hγ0).elim
    refine ⟨β, hβne, ?_⟩
    have hγinv : γ = β⁻¹ := eq_inv_of_mul_eq_one_right hβγ
    right
    ext x i <;> fin_cases i <;>
      simp [RectHyperbolaSwapScale, point2SwapLinearEquiv, point2DiagLinearEquiv,
        point2SwapLinearMap, point2DiagLinearMap, α, β, γ, δ, p, q, hα, hβ, hγinv, hδ0,
        hp0, hq0, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · have hγ0 : γ = 0 := by
      have hαγ0 : α * γ = 0 := h4
      rcases mul_eq_zero.mp hαγ0 with hα0 | hγ0
      · exact (hα hα0).elim
      · exact hγ0
    have hq0 : q = 0 := by
      have hαq0 : α * q = 0 := by
        simpa [hγ0] using h3
      rcases mul_eq_zero.mp hαq0 with hα0 | hq0
      · exact (hα hα0).elim
      · exact hq0
    have hαδ : α * δ = 1 := by
      have h2' : α * δ - 1 = 0 := by
        simpa [hγ0, hq0] using h2
      linarith
    have hδne : δ ≠ 0 := by
      intro hδ0
      have h : (1 : ℝ) = 0 := by
        simpa [hδ0] using hαδ
      linarith
    have hβ0 : β = 0 := by
      have hβδ0 : β * δ = 0 := h0
      rcases mul_eq_zero.mp hβδ0 with hβ0 | hδ0
      · exact hβ0
      · exact (hδne hδ0).elim
    have hp0 : p = 0 := by
      have hpδ0 : p * δ = 0 := by
        simpa [hβ0, hq0] using h1
      rcases mul_eq_zero.mp hpδ0 with hp0 | hδ0
      · exact hp0
      · exact (hδne hδ0).elim
    refine ⟨α, hα, ?_⟩
    have hδinv : δ = α⁻¹ := eq_inv_of_mul_eq_one_right hαδ
    left
    ext x i <;> fin_cases i <;>
      simp [RectHyperbolaScale, point2DiagLinearEquiv, point2DiagLinearMap,
        α, β, γ, δ, p, q, hα, hβ0, hγ0, hδinv, hp0, hq0, add_comm, add_left_comm,
        add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Conjugating a curve stabilizer by normal-form data preserves the chosen
standard model. -/
lemma conjugateAffine_preserves_model
    {C : Set Point2} (data : ConicNormalFormData C)
    (T : AffineEquiv ℝ Point2 Point2) (hTC : T '' C = C) :
    conjugateAffine data.e T '' ConicModelSet data.model = ConicModelSet data.model := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← data.image_eq] at hy
    rcases hy with ⟨z, hz, rfl⟩
    rw [← data.image_eq]
    refine ⟨T z, ?_, ?_⟩
    · rw [← hTC]
      exact ⟨z, hz, rfl⟩
    · simp [conjugateAffine]
  · intro hx
    rw [← data.image_eq] at hx
    rcases hx with ⟨z, hz, rfl⟩
    refine ⟨data.e (T.symm z), ?_, ?_⟩
    · rw [data.image_eq]
      exact ⟨T.symm z, ?_, rfl⟩
    · simp [conjugateAffine]
    · rw [hTC]
      exact ⟨z, hz, rfl⟩

/-- Final C5 packaging: once a conic has been put into one of the three
standard models, the model stabilizer theorems yield the full normal-form
classification packet. -/
theorem conicStabilizerNormalForm_of_data
    {C : Set Point2} (data : ConicNormalFormData C) :
    ConicStabilizerNormalForm C := by
  refine ⟨data, ?_⟩
  intro T hTC
  have hmodel := conjugateAffine_preserves_model data T hTC
  cases data.model
  · simpa [ModelConicStabilizer] using ellipseModelStabilizer_of_image_eq
      (T := conjugateAffine data.e T) hmodel
  · simpa [ModelConicStabilizer] using hyperbolaModelStabilizer_of_image_eq
      (T := conjugateAffine data.e T) hmodel
  · simpa [ModelConicStabilizer] using parabolaModelStabilizer_of_image_eq
      (T := conjugateAffine data.e T) hmodel

/-- The symmetric matrix attached to the quadratic part of a plane polynomial. -/
noncomputable def quadraticPlaneSymmetricMatrix (q : QuadraticPlaneCoeffs) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.a, q.b / 2; q.b / 2, q.c]

/-- The quadratic-part matrix is symmetric. -/
lemma quadraticPlaneSymmetricMatrix_isSymmetric (q : QuadraticPlaneCoeffs) :
    (quadraticPlaneSymmetricMatrix q).IsSymmetric := by
  simp [quadraticPlaneSymmetricMatrix]

/-- The quadratic part of a quadratic plane polynomial, viewed as a quadratic
form on `Point2`. -/
noncomputable def quadraticPlaneQuadraticForm (q : QuadraticPlaneCoeffs) :
    QuadraticForm ℝ Point2 :=
  (quadraticPlaneSymmetricMatrix q).toQuadraticMap'

/-- The affine-linear part of a quadratic plane polynomial. -/
noncomputable def quadraticPlaneLinearPart (q : QuadraticPlaneCoeffs) :
    Point2 →ₗ[ℝ] ℝ :=
{ toFun := fun x => q.d * x 0 + q.e * x 1
  map_add' := by
    intro x y
    ring
  map_smul' := by
    intro r x
    ring }

/-- Explicit evaluation of the quadratic-form part. -/
lemma quadraticPlaneQuadraticForm_apply (q : QuadraticPlaneCoeffs) (x : Point2) :
    quadraticPlaneQuadraticForm q x =
      q.a * x 0 ^ 2 + q.b * x 0 * x 1 + q.c * x 1 ^ 2 := by
  simp [quadraticPlaneQuadraticForm, quadraticPlaneSymmetricMatrix,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  ring

/-- Explicit evaluation of the linear part. -/
@[simp] lemma quadraticPlaneLinearPart_apply (q : QuadraticPlaneCoeffs) (x : Point2) :
    quadraticPlaneLinearPart q x = q.d * x 0 + q.e * x 1 := rfl

/-- Evaluate a quadratic plane polynomial as quadratic part plus linear part plus constant. -/
lemma quadraticPlane_eval_decompose (q : QuadraticPlaneCoeffs) (x : Point2) :
    MvPolynomial.eval (fun i ↦ x i) q.toPolynomial =
      quadraticPlaneQuadraticForm q x + quadraticPlaneLinearPart q x + q.f := by
  rw [QuadraticPlaneCoeffs.toPolynomial, quadraticPlaneQuadraticForm_apply]
  simp [quadraticPlaneLinearPart_apply]
  ring

/-- Sylvester reduction for the quadratic part of a quadratic plane polynomial. -/
theorem quadraticPlaneQuadraticForm_equivalent_weightedSumSquares
    (q : QuadraticPlaneCoeffs) :
    ∃ w : Fin 2 → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      QuadraticForm.Equivalent (quadraticPlaneQuadraticForm q)
        (QuadraticForm.weightedSumSquares ℝ w) := by
  simpa [Point2, quadraticPlaneQuadraticForm] using
    QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared
      (quadraticPlaneQuadraticForm q)

/-- A chosen weight vector for the quadratic-part Sylvester normal form. -/
noncomputable def quadraticPlaneQuadraticFormNormalWeights (q : QuadraticPlaneCoeffs) :
    Fin 2 → ℝ :=
  Classical.choose (quadraticPlaneQuadraticForm_equivalent_weightedSumSquares q)

/-- The chosen weights lie in `{-1, 0, 1}`. -/
lemma quadraticPlaneQuadraticFormNormalWeights_spec (q : QuadraticPlaneCoeffs) :
    ∀ i, quadraticPlaneQuadraticFormNormalWeights q i = -1 ∨
      quadraticPlaneQuadraticFormNormalWeights q i = 0 ∨
      quadraticPlaneQuadraticFormNormalWeights q i = 1 :=
  (Classical.choose_spec (quadraticPlaneQuadraticForm_equivalent_weightedSumSquares q)).1

/-- A chosen linear isometry between the quadratic part and its weighted-sum-of-squares normal form. -/
noncomputable def quadraticPlaneQuadraticFormNormalizer (q : QuadraticPlaneCoeffs) :
    (quadraticPlaneQuadraticForm q).IsometryEquiv
      (QuadraticForm.weightedSumSquares ℝ (quadraticPlaneQuadraticFormNormalWeights q)) :=
  Classical.choice
    (Classical.choose_spec (quadraticPlaneQuadraticForm_equivalent_weightedSumSquares q)).2

/-- The chosen normalizer sends the quadratic part to the chosen weighted sum of squares. -/
lemma quadraticPlaneQuadraticFormNormalizer_map (q : QuadraticPlaneCoeffs) (x : Point2) :
    QuadraticForm.weightedSumSquares ℝ (quadraticPlaneQuadraticFormNormalWeights q)
        (quadraticPlaneQuadraticFormNormalizer q x) =
      quadraticPlaneQuadraticForm q x :=
  QuadraticForm.IsometryEquiv.map_app (quadraticPlaneQuadraticFormNormalizer q) x

/-- The chosen quadratic-part normalizer as an affine equivalence fixing the origin. -/
noncomputable def quadraticPlaneQuadraticNormalizerAffine (q : QuadraticPlaneCoeffs) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  AffineEquiv.ofLinearEquiv
    (quadraticPlaneQuadraticFormNormalizer q).toLinearEquiv 0 0

/-- The transformed linear part after passing to the quadratic-part normalizing coordinates. -/
noncomputable def quadraticPlaneNormalizedLinearPart (q : QuadraticPlaneCoeffs) :
    Point2 →ₗ[ℝ] ℝ :=
  (quadraticPlaneLinearPart q).comp
    (quadraticPlaneQuadraticFormNormalizer q).symm.toLinearMap

/-- In the quadratic-part normalizing coordinates, the polynomial evaluates as a weighted
sum of squares plus a transformed linear part and the original constant term. -/
lemma quadraticPlaneNormalized_eval (q : QuadraticPlaneCoeffs) (x : Point2) :
    MvPolynomial.eval (fun i ↦ x i)
        (affinePolyEquiv (quadraticPlaneQuadraticNormalizerAffine q).symm q.toPolynomial) =
      QuadraticForm.weightedSumSquares ℝ (quadraticPlaneQuadraticFormNormalWeights q) x +
        quadraticPlaneNormalizedLinearPart q x + q.f := by
  rw [affinePolyEquiv_eval]
  rw [quadraticPlane_eval_decompose]
  change quadraticPlaneQuadraticForm q
      ((quadraticPlaneQuadraticFormNormalizer q).symm x) +
        quadraticPlaneLinearPart q ((quadraticPlaneQuadraticFormNormalizer q).symm x) + q.f =
      _
  rw [← quadraticPlaneQuadraticFormNormalizer_map]
  rfl

/-- The polynomial obtained after passing to the quadratic-part normalizing coordinates. -/
noncomputable def quadraticPlaneNormalizedPolynomial (q : QuadraticPlaneCoeffs) :
    MvPolynomial (Fin 2) ℝ :=
  affinePolyEquiv (quadraticPlaneQuadraticNormalizerAffine q).symm q.toPolynomial

/-- The coefficient of `X 0` in the normalized linear part. -/
noncomputable def quadraticPlaneNormalizedLinearCoeff0 (q : QuadraticPlaneCoeffs) : ℝ :=
  quadraticPlaneNormalizedLinearPart q point2Basis0

/-- The coefficient of `X 1` in the normalized linear part. -/
noncomputable def quadraticPlaneNormalizedLinearCoeff1 (q : QuadraticPlaneCoeffs) : ℝ :=
  quadraticPlaneNormalizedLinearPart q point2Basis1

/-- The explicit polynomial corresponding to the normalized equation. -/
noncomputable def quadraticPlaneNormalizedExplicitPolynomial (q : QuadraticPlaneCoeffs) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (quadraticPlaneQuadraticFormNormalWeights q 0) * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C (quadraticPlaneQuadraticFormNormalWeights q 1) * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff0 q) * MvPolynomial.X 0 +
    MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff1 q) * MvPolynomial.X 1 +
    MvPolynomial.C q.f

/-- Membership in the normalized curve is exactly the normalized weighted-sum-of-squares equation. -/
lemma mem_quadraticPlaneNormalizedPolynomial_zeroSet_iff
    (q : QuadraticPlaneCoeffs) (x : Point2) :
    x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q) ↔
      QuadraticForm.weightedSumSquares ℝ (quadraticPlaneQuadraticFormNormalWeights q) x +
        quadraticPlaneNormalizedLinearPart q x + q.f = 0 := by
  rw [mem_PlaneCurveZeroSet, quadraticPlaneNormalizedPolynomial, quadraticPlaneNormalized_eval]

/-- The normalized polynomial is exactly the explicit weighted-sum-of-squares model with the
transformed linear and constant terms. -/
lemma quadraticPlaneNormalizedPolynomial_eq_explicit (q : QuadraticPlaneCoeffs) :
    quadraticPlaneNormalizedPolynomial q = quadraticPlaneNormalizedExplicitPolynomial q := by
  apply MvPolynomial.funext
  intro x
  let xP : Point2 := WithLp.toLp 2 x
  rw [quadraticPlaneNormalizedPolynomial, quadraticPlaneNormalized_eval]
  simp [quadraticPlaneNormalizedExplicitPolynomial, quadraticPlaneNormalizedLinearCoeff0,
    quadraticPlaneNormalizedLinearCoeff1, quadraticPlaneNormalizedLinearPart,
    QuadraticForm.weightedSumSquares_apply, point2Basis0, point2Basis1, xP]
  rw [Fin.sum_univ_two]
  ring

/-- The center used to complete squares in the same-sign rank-two case. -/
private noncomputable def sameSignRankTwoCenter (s d e : ℝ) : Point2 :=
  !₂[(-d / (2 * s) : ℝ), (-e / (2 * s) : ℝ)]

/-- The completed-square constant in the same-sign rank-two case. -/
private def sameSignRankTwoKappa (s d e f : ℝ) : ℝ :=
  d ^ 2 / 4 + e ^ 2 / 4 - s * f

/-- Completing squares in the same-sign rank-two case. -/
private lemma sameSignRankTwo_completion
    {s d e f : ℝ} (hs : s = 1 ∨ s = -1) (x : Point2) :
    s * x 0 ^ 2 + s * x 1 ^ 2 + d * x 0 + e * x 1 + f =
      s * (((x 0 - (sameSignRankTwoCenter s d e) 0) ^ 2 +
        (x 1 - (sameSignRankTwoCenter s d e) 1) ^ 2) - sameSignRankTwoKappa s d e f) := by
  rcases hs with rfl | rfl <;>
    simp [sameSignRankTwoCenter, sameSignRankTwoKappa]
    <;> ring

/-- In the same-sign rank-two case, infinitude of the real zero set forces the completed-square
constant to be positive. -/
lemma sameSign_rankTwo_kappa_pos_of_infinite_zeroSet
    (q : QuadraticPlaneCoeffs)
    (hs0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (hs1 : quadraticPlaneQuadraticFormNormalWeights q 1 =
      quadraticPlaneQuadraticFormNormalWeights q 0)
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    0 < sameSignRankTwoKappa
      (quadraticPlaneQuadraticFormNormalWeights q 0)
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f := by
  let s := quadraticPlaneQuadraticFormNormalWeights q 0
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  let κ := sameSignRankTwoKappa s d e q.f
  by_contra hκ
  have hsub :
      PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q) ⊆
        {sameSignRankTwoCenter s d e} := by
    intro x hx
    have hx0 :
        x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
    rw [mem_PlaneCurveZeroSet] at hx0
    rw [quadraticPlaneNormalizedExplicitPolynomial] at hx0
    rw [Fin.sum_univ_two] at hx0
    have hs : s = 1 ∨ s = -1 := by simpa [s] using hs0
    have hsEq : quadraticPlaneQuadraticFormNormalWeights q 1 = s := by simpa [s] using hs1
    rw [hsEq] at hx0
    have hcomp := sameSignRankTwo_completion (s := s) (d := d) (e := e) (f := q.f) hs x
    rw [hcomp] at hx0
    have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have hsum :
        (x 0 - (sameSignRankTwoCenter s d e) 0) ^ 2 +
          (x 1 - (sameSignRankTwoCenter s d e) 1) ^ 2 = κ := by
      apply eq_of_mul_eq_mul_left hs_ne
      simpa using hx0
    have h0sq : 0 ≤ (x 0 - (sameSignRankTwoCenter s d e) 0) ^ 2 := sq_nonneg _
    have h1sq : 0 ≤ (x 1 - (sameSignRankTwoCenter s d e) 1) ^ 2 := sq_nonneg _
    have hκ' : κ ≤ 0 := by simpa [κ] using hκ
    have hz0 : (x 0 - (sameSignRankTwoCenter s d e) 0) ^ 2 = 0 := by
      nlinarith
    have hz1 : (x 1 - (sameSignRankTwoCenter s d e) 1) ^ 2 = 0 := by
      nlinarith
    ext i <;> fin_cases i
    · have : x 0 - (sameSignRankTwoCenter s d e) 0 = 0 := sq_eq_zero_iff.mp hz0
      linarith
    · have : x 1 - (sameSignRankTwoCenter s d e) 1 = 0 := sq_eq_zero_iff.mp hz1
      linarith
  have hfinite : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Finite :=
    Set.Finite.subset ({sameSignRankTwoCenter s d e} : Set Point2).finite_toSet hsub
  exact hInf.not_finite hfinite

/-- The completed-square constant in the opposite-sign rank-two case. -/
private def oppositeSignRankTwoKappa (d e f : ℝ) : ℝ :=
  d ^ 2 / 4 - e ^ 2 / 4 - f

/-- The explicit opposite-sign rank-two polynomial factors when the completed-square constant
vanishes. -/
private lemma oppositeSign_rankTwo_explicit_factorization
    (q : QuadraticPlaneCoeffs)
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = -1)
    (hκ : oppositeSignRankTwoKappa
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f = 0) :
    quadraticPlaneNormalizedExplicitPolynomial q =
      (MvPolynomial.X 0 - MvPolynomial.X 1 +
          MvPolynomial.C
            ((quadraticPlaneNormalizedLinearCoeff0 q +
              quadraticPlaneNormalizedLinearCoeff1 q) / 2)) *
        (MvPolynomial.X 0 + MvPolynomial.X 1 +
          MvPolynomial.C
            ((quadraticPlaneNormalizedLinearCoeff0 q -
              quadraticPlaneNormalizedLinearCoeff1 q) / 2)) := by
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
  simp [oppositeSignRankTwoKappa] at hκ
  rw [hκ]
  ring

/-- The opposite-sign rank-two completed-square constant is nonzero for an irreducible normalized
conic polynomial. -/
lemma oppositeSign_rankTwo_kappa_ne_zero_of_irreducible
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = -1) :
    oppositeSignRankTwoKappa
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f ≠ 0 := by
  intro hκ
  have hfac := oppositeSign_rankTwo_explicit_factorization q h0 h1 hκ
  have hfac' :
      quadraticPlaneNormalizedPolynomial q =
        (MvPolynomial.X 0 - MvPolynomial.X 1 +
            MvPolynomial.C
              ((quadraticPlaneNormalizedLinearCoeff0 q +
                quadraticPlaneNormalizedLinearCoeff1 q) / 2)) *
          (MvPolynomial.X 0 + MvPolynomial.X 1 +
            MvPolynomial.C
              ((quadraticPlaneNormalizedLinearCoeff0 q -
                quadraticPlaneNormalizedLinearCoeff1 q) / 2)) := by
    rw [quadraticPlaneNormalizedPolynomial_eq_explicit, hfac]
  let l₁ : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X 0 - MvPolynomial.X 1 +
      MvPolynomial.C
        ((quadraticPlaneNormalizedLinearCoeff0 q +
          quadraticPlaneNormalizedLinearCoeff1 q) / 2)
  let l₂ : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X 0 + MvPolynomial.X 1 +
      MvPolynomial.C
        ((quadraticPlaneNormalizedLinearCoeff0 q -
          quadraticPlaneNormalizedLinearCoeff1 q) / 2)
  have hu : IsUnit l₁ ∨ IsUnit l₂ := by
    simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
  have hnu1 : ¬ IsUnit l₁ := by
    intro hl₁
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
    rcases hl₁ with ⟨c, hc⟩
    have hcoeff : (quadraticPlaneNormalizedPolynomial q).coeff (Finsupp.single 0 1) = 0 := by
      simpa [l₁] using congrArg
        (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 0 1)) hc
    simp [quadraticPlaneNormalizedPolynomial_eq_explicit,
      quadraticPlaneNormalizedExplicitPolynomial] at hcoeff
  have hnu2 : ¬ IsUnit l₂ := by
    intro hl₂
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
    rcases hl₂ with ⟨c, hc⟩
    have hcoeff : (quadraticPlaneNormalizedPolynomial q).coeff (Finsupp.single 1 1) = 0 := by
      simpa [l₂] using congrArg
        (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
    simp [quadraticPlaneNormalizedPolynomial_eq_explicit,
      quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hcoeff
  exact hu.elim hnu1 hnu2

/-- In the rank-one case with no transverse linear term, any real point yields an explicit
factorization of the normalized polynomial. -/
private lemma rankOne_noTransverse_factorization
    (q : QuadraticPlaneCoeffs) {r : ℝ}
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 0)
    (he0 : quadraticPlaneNormalizedLinearCoeff1 q = 0)
    (hr : r ^ 2 + quadraticPlaneNormalizedLinearCoeff0 q * r + q.f = 0) :
    quadraticPlaneNormalizedExplicitPolynomial q =
      (MvPolynomial.X 0 - MvPolynomial.C r) *
        (MvPolynomial.X 0 +
          MvPolynomial.C (r + quadraticPlaneNormalizedLinearCoeff0 q)) := by
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, he0]
  have hf : q.f = -r * (r + quadraticPlaneNormalizedLinearCoeff0 q) := by
    nlinarith [hr]
  rw [hf]
  ring

/-- In the rank-one case, the transverse linear coefficient cannot vanish for an irreducible
normalized conic polynomial with infinite real zero set. -/
lemma rankOne_transverseLinear_ne_zero_of_irreducible_infinite
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 0)
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    quadraticPlaneNormalizedLinearCoeff1 q ≠ 0 := by
  intro he0
  obtain ⟨z, hz⟩ := hInf.nonempty
  have hz' : z ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
    simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hz
  rw [mem_PlaneCurveZeroSet] at hz'
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, he0] at hz'
  have hr : z 0 ^ 2 + quadraticPlaneNormalizedLinearCoeff0 q * z 0 + q.f = 0 := by
    simpa using hz'
  have hfac :=
    rankOne_noTransverse_factorization q h0 h1 he0 hr
  let l₁ : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 - MvPolynomial.C (z 0)
  let l₂ : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X 0 + MvPolynomial.C (z 0 + quadraticPlaneNormalizedLinearCoeff0 q)
  have hu : IsUnit l₁ ∨ IsUnit l₂ := by
    have hfac' : quadraticPlaneNormalizedPolynomial q = l₁ * l₂ := by
      rw [quadraticPlaneNormalizedPolynomial_eq_explicit]
      simpa [l₁, l₂] using hfac
    simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
  have hnu1 : ¬ IsUnit l₁ := by
    intro hl₁
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
    rcases hl₁ with ⟨c, hc⟩
    have hcoeff : l₁.coeff (Finsupp.single 0 1) = 0 := by
      simpa using congrArg
        (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 0 1)) hc
    simp [l₁] at hcoeff
  have hnu2 : ¬ IsUnit l₂ := by
    intro hl₂
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
    rcases hl₂ with ⟨c, hc⟩
    have hcoeff : l₂.coeff (Finsupp.single 0 1) = 0 := by
      simpa using congrArg
        (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 0 1)) hc
    simp [l₂] at hcoeff
  exact hu.elim hnu1 hnu2

/-- The affine normalization from the same-sign rank-two completed-square form to the ellipse
model. -/
private noncomputable def sameSignRankTwoAffine
    (q : QuadraticPlaneCoeffs)
    (hκ : 0 < sameSignRankTwoKappa
      (quadraticPlaneQuadraticFormNormalWeights q 0)
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  let c := sameSignRankTwoCenter
      (quadraticPlaneQuadraticFormNormalWeights q 0)
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q)
  let r : ℝ := Real.sqrt (sameSignRankTwoKappa
      (quadraticPlaneQuadraticFormNormalWeights q 0)
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f)
  (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
    (AffineEquiv.ofLinearEquiv
      (point2DiagLinearEquiv r⁻¹ r⁻¹
        (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκ))
        (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκ))) 0 0)

/-- The same-sign rank-two normalized curve is affine-equivalent to the ellipse model. -/
theorem sameSign_rankTwo_conicNormalFormData_of_normalized
    (q : QuadraticPlaneCoeffs)
    (hs0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (hs1 : quadraticPlaneQuadraticFormNormalWeights q 1 =
      quadraticPlaneQuadraticFormNormalWeights q 0)
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    ConicNormalFormData (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)) := by
  let s := quadraticPlaneQuadraticFormNormalWeights q 0
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  let κ := sameSignRankTwoKappa s d e q.f
  let c := sameSignRankTwoCenter s d e
  have hκ : 0 < κ := by simpa [s, d, e, κ] using
    sameSign_rankTwo_kappa_pos_of_infinite_zeroSet q hs0 hs1 hInf
  let T := sameSignRankTwoAffine q hκ
  refine ⟨ConicModel.ellipse, T, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ConicModelSet, Set.mem_setOf_eq]
    have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
    rw [mem_PlaneCurveZeroSet] at hx'
    rw [quadraticPlaneNormalizedExplicitPolynomial, Fin.sum_univ_two] at hx'
    have hs : s = 1 ∨ s = -1 := by simpa [s] using hs0
    have hsEq : quadraticPlaneQuadraticFormNormalWeights q 1 = s := by simpa [s] using hs1
    rw [hsEq] at hx'
    have hcomp := sameSignRankTwo_completion (s := s) (d := d) (e := e) (f := q.f) hs x
    rw [hcomp] at hx'
    have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have hsum :
        (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = κ := by
      apply eq_of_mul_eq_mul_left hs_ne
      simpa [c, κ] using hx'
    have hκ0 : 0 ≤ κ := le_of_lt hκ
    have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκ
    have hy0 : y 0 = (x 0 - c 0) / Real.sqrt κ := by
      simp [T, sameSignRankTwoAffine, c, κ, hκ.ne', Real.sqrt_ne_zero'.mpr hκ,
        point2DiagLinearEquiv, point2DiagLinearMap]
    have hy1 : y 1 = (x 1 - c 1) / Real.sqrt κ := by
      simp [T, sameSignRankTwoAffine, c, κ, hκ.ne', Real.sqrt_ne_zero'.mpr hκ,
        point2DiagLinearEquiv, point2DiagLinearMap]
    rw [hy0, hy1]
    field_simp [hk_sqrt]
    rw [Real.sq_sqrt hκ0]
    linarith
  · intro hy
    let x : Point2 := T.symm y
    refine ⟨x, ?_, rfl⟩
    have hy' : y 0 ^ 2 + y 1 ^ 2 = 1 := hy
    have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκ
    have hx0 : x 0 - c 0 = Real.sqrt κ * y 0 := by
      simp [x, T, sameSignRankTwoAffine, c, κ, hκ.ne', Real.sqrt_ne_zero'.mpr hκ,
        point2DiagLinearEquiv, point2DiagLinearMap]
    have hx1 : x 1 - c 1 = Real.sqrt κ * y 1 := by
      simp [x, T, sameSignRankTwoAffine, c, κ, hκ.ne', Real.sqrt_ne_zero'.mpr hκ,
        point2DiagLinearEquiv, point2DiagLinearMap]
    have hsum : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = κ := by
      rw [hx0, hx1, sq, sq]
      rw [← mul_add, hy', mul_one, Real.sq_sqrt (le_of_lt hκ)]
    have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      rw [mem_PlaneCurveZeroSet]
      rw [quadraticPlaneNormalizedExplicitPolynomial, Fin.sum_univ_two]
      have hs : s = 1 ∨ s = -1 := by simpa [s] using hs0
      have hsEq : quadraticPlaneQuadraticFormNormalWeights q 1 = s := by simpa [s] using hs1
      rw [hsEq]
      have hcomp := sameSignRankTwo_completion (s := s) (d := d) (e := e) (f := q.f) hs x
      rw [hcomp]
      have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      apply mul_eq_zero.mp
      right
      exact sub_eq_zero.mpr hsum
    simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- The sum-difference linear map `(u, v) ↦ (u - v, u + v)`. -/
private noncomputable def point2SumDiffLinearMap : Point2 →ₗ[ℝ] Point2 :=
{ toFun := fun x => (!₂[(x 0 - x 1 : ℝ), (x 0 + x 1 : ℝ)] : Point2)
  map_add' := by
    intro x y
    ext i <;> fin_cases i <;> ring
  map_smul' := by
    intro r x
    ext i <;> fin_cases i <;> ring }

/-- The inverse of the sum-difference linear map. -/
private noncomputable def point2SumDiffLinearMapInv : Point2 →ₗ[ℝ] Point2 :=
{ toFun := fun x => (!₂[((x 0 + x 1) / 2 : ℝ), ((x 1 - x 0) / 2 : ℝ)] : Point2)
  map_add' := by
    intro x y
    ext i <;> fin_cases i <;> ring
  map_smul' := by
    intro r x
    ext i <;> fin_cases i <;> ring }

/-- The sum-difference linear equivalence. -/
private noncomputable def point2SumDiffLinearEquiv : Point2 ≃ₗ[ℝ] Point2 :=
  LinearEquiv.ofLinear point2SumDiffLinearMap point2SumDiffLinearMapInv
    (by
      ext x i <;> fin_cases i <;> simp [point2SumDiffLinearMap, point2SumDiffLinearMapInv]
      <;> ring)
    (by
      ext x i <;> fin_cases i <;> simp [point2SumDiffLinearMap, point2SumDiffLinearMapInv]
      <;> ring)

/-- The center used to complete squares in the opposite-sign rank-two case. -/
private noncomputable def oppositeSignRankTwoCenter (d e : ℝ) : Point2 :=
  !₂[(-d / 2 : ℝ), (e / 2 : ℝ)]

/-- Completing squares in the opposite-sign rank-two case. -/
private lemma oppositeSignRankTwo_completion
    {d e f : ℝ} (x : Point2) :
    x 0 ^ 2 - x 1 ^ 2 + d * x 0 + e * x 1 + f =
      ((x 0 - (oppositeSignRankTwoCenter d e) 0) ^ 2 -
        (x 1 - (oppositeSignRankTwoCenter d e) 1) ^ 2) -
        oppositeSignRankTwoKappa d e f := by
  simp [oppositeSignRankTwoCenter, oppositeSignRankTwoKappa]
  ring

/-- The affine normalization from the opposite-sign rank-two completed-square form to the
rectangular hyperbola model, in the `κ > 0` branch. -/
private noncomputable def oppositeSignRankTwoAffinePos
    (q : QuadraticPlaneCoeffs)
    (hκ : 0 < oppositeSignRankTwoKappa
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  let c := oppositeSignRankTwoCenter
    (quadraticPlaneNormalizedLinearCoeff0 q)
    (quadraticPlaneNormalizedLinearCoeff1 q)
  let r : ℝ := Real.sqrt (oppositeSignRankTwoKappa
    (quadraticPlaneNormalizedLinearCoeff0 q)
    (quadraticPlaneNormalizedLinearCoeff1 q) q.f)
  (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
    (AffineEquiv.ofLinearEquiv
      ((point2SumDiffLinearEquiv).trans
        (point2DiagLinearEquiv r⁻¹ r⁻¹
          (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκ))
          (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκ)))) 0 0)

/-- The affine normalization from the opposite-sign rank-two completed-square form to the
rectangular hyperbola model, in the `κ < 0` branch. -/
private noncomputable def oppositeSignRankTwoAffineNeg
    (q : QuadraticPlaneCoeffs)
    (hκ : oppositeSignRankTwoKappa
      (quadraticPlaneNormalizedLinearCoeff0 q)
      (quadraticPlaneNormalizedLinearCoeff1 q) q.f < 0) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  let c := oppositeSignRankTwoCenter
    (quadraticPlaneNormalizedLinearCoeff0 q)
    (quadraticPlaneNormalizedLinearCoeff1 q)
  let r : ℝ := Real.sqrt (-(oppositeSignRankTwoKappa
    (quadraticPlaneNormalizedLinearCoeff0 q)
    (quadraticPlaneNormalizedLinearCoeff1 q) q.f))
  (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
    (AffineEquiv.ofLinearEquiv
      ((point2SumDiffLinearEquiv).trans
        (point2DiagLinearEquiv (-r⁻¹) r⁻¹
          (neg_ne_zero.mpr <| inv_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκ)))
          (inv_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκ))))) 0 0)

/-- The opposite-sign rank-two normalized curve is affine-equivalent to the hyperbola model. -/
theorem oppositeSign_rankTwo_conicNormalFormData_of_normalized
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = -1) :
    ConicNormalFormData (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)) := by
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  let κ := oppositeSignRankTwoKappa d e q.f
  have hκne : κ ≠ 0 := by
    simpa [d, e, κ] using oppositeSign_rankTwo_kappa_ne_zero_of_irreducible q hIrred h0 h1
  by_cases hκpos : 0 < κ
  · let c := oppositeSignRankTwoCenter d e
    let r : ℝ := Real.sqrt κ
    let T := oppositeSignRankTwoAffinePos q hκpos
    refine ⟨ConicModel.hyperbola, T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConicModelSet, Set.mem_setOf_eq]
      have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
      rw [mem_PlaneCurveZeroSet] at hx'
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hx'
      have hcomp := oppositeSignRankTwo_completion (d := d) (e := e) (f := q.f) x
      rw [hcomp] at hx'
      have hxy :
          (x 0 - c 0) ^ 2 - (x 1 - c 1) ^ 2 = κ := by
        simpa [c, κ] using hx'
      have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκpos
      have hy0 : y 0 = ((x 0 - c 0) - (x 1 - c 1)) / Real.sqrt κ := by
        simp [T, oppositeSignRankTwoAffinePos, c, κ, hκpos.ne', hk_sqrt,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      have hy1 : y 1 = ((x 0 - c 0) + (x 1 - c 1)) / Real.sqrt κ := by
        simp [T, oppositeSignRankTwoAffinePos, c, κ, hκpos.ne', hk_sqrt,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      rw [hy0, hy1]
      field_simp [hk_sqrt]
      rw [Real.sq_sqrt (le_of_lt hκpos)]
      nlinarith
    · intro hy
      let x : Point2 := T.symm y
      refine ⟨x, ?_, rfl⟩
      have hy' : y 0 * y 1 = 1 := hy
      have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκpos
      have hx0 : x 0 - c 0 = Real.sqrt κ * ((y 0 + y 1) / 2) := by
        simp [x, T, oppositeSignRankTwoAffinePos, c, κ, hκpos.ne', hk_sqrt,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hx1 : x 1 - c 1 = Real.sqrt κ * ((y 1 - y 0) / 2) := by
        simp [x, T, oppositeSignRankTwoAffinePos, c, κ, hκpos.ne', hk_sqrt,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hxy : (x 0 - c 0) ^ 2 - (x 1 - c 1) ^ 2 = κ := by
        rw [hx0, hx1]
        field_simp
        rw [Real.sq_sqrt (le_of_lt hκpos)]
        nlinarith [hy']
      have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        rw [mem_PlaneCurveZeroSet]
        rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
        have hcomp := oppositeSignRankTwo_completion (d := d) (e := e) (f := q.f) x
        rw [hcomp]
        linarith
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- The center used to complete squares in the swapped opposite-sign rank-two case. -/
private noncomputable def oppositeSignRankTwoCenterSwap (d e : ℝ) : Point2 :=
  !₂[(d / 2 : ℝ), (-e / 2 : ℝ)]

/-- The swapped opposite-sign completed-square constant. -/
private def oppositeSignRankTwoKappaSwap (d e f : ℝ) : ℝ :=
  e ^ 2 / 4 - d ^ 2 / 4 - f

/-- Completing squares in the swapped opposite-sign rank-two case. -/
private lemma oppositeSignRankTwo_completion_swap
    {d e f : ℝ} (x : Point2) :
    -x 0 ^ 2 + x 1 ^ 2 + d * x 0 + e * x 1 + f =
      ((x 1 - (oppositeSignRankTwoCenterSwap d e) 1) ^ 2 -
        (x 0 - (oppositeSignRankTwoCenterSwap d e) 0) ^ 2) -
        oppositeSignRankTwoKappaSwap d e f := by
  simp [oppositeSignRankTwoCenterSwap, oppositeSignRankTwoKappaSwap]
  ring

/-- The swapped opposite-sign rank-two normalized curve is affine-equivalent to the hyperbola
model. -/
theorem oppositeSign_rankTwo_swap_conicNormalFormData_of_normalized
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 1) :
    ConicNormalFormData (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)) := by
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  let κ := oppositeSignRankTwoKappaSwap d e q.f
  have hκne : κ ≠ 0 := by
    intro hκ
    have hfac :
        quadraticPlaneNormalizedExplicitPolynomial q =
          (MvPolynomial.X 1 - MvPolynomial.X 0 +
              MvPolynomial.C ((d + e) / 2)) *
            (MvPolynomial.X 1 + MvPolynomial.X 0 +
              MvPolynomial.C ((e - d) / 2)) := by
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
      simp [oppositeSignRankTwoKappaSwap] at hκ
      rw [hκ]
      ring
    have hfac' :
        quadraticPlaneNormalizedPolynomial q =
          (MvPolynomial.X 1 - MvPolynomial.X 0 +
              MvPolynomial.C ((d + e) / 2)) *
            (MvPolynomial.X 1 + MvPolynomial.X 0 +
              MvPolynomial.C ((e - d) / 2)) := by
      rw [quadraticPlaneNormalizedPolynomial_eq_explicit, hfac]
    let l₁ : MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.X 1 - MvPolynomial.X 0 + MvPolynomial.C ((d + e) / 2)
    let l₂ : MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.X 1 + MvPolynomial.X 0 + MvPolynomial.C ((e - d) / 2)
    have hu : IsUnit l₁ ∨ IsUnit l₂ := by
      simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
    have hnu1 : ¬ IsUnit l₁ := by
      intro hl₁
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
      rcases hl₁ with ⟨c, hc⟩
      have hcoeff : (quadraticPlaneNormalizedPolynomial q).coeff (Finsupp.single 1 1) = 0 := by
        simpa [l₁] using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [quadraticPlaneNormalizedPolynomial_eq_explicit,
        quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hcoeff
    have hnu2 : ¬ IsUnit l₂ := by
      intro hl₂
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
      rcases hl₂ with ⟨c, hc⟩
      have hcoeff : (quadraticPlaneNormalizedPolynomial q).coeff (Finsupp.single 1 1) = 0 := by
        simpa [l₂] using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [quadraticPlaneNormalizedPolynomial_eq_explicit,
        quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hcoeff
    exact hu.elim hnu1 hnu2
  by_cases hκpos : 0 < κ
  · let c := oppositeSignRankTwoCenterSwap d e
    let r : ℝ := Real.sqrt κ
    let T : Point2 ≃ᵃ[ℝ] Point2 :=
      (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
        (AffineEquiv.ofLinearEquiv
          ((point2SwapLinearEquiv.trans point2SumDiffLinearEquiv).trans
            (point2DiagLinearEquiv r⁻¹ r⁻¹
              (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκpos))
              (inv_ne_zero (Real.sqrt_ne_zero'.mpr hκpos)))) 0 0)
    refine ⟨ConicModel.hyperbola, T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConicModelSet, Set.mem_setOf_eq]
      have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
      rw [mem_PlaneCurveZeroSet] at hx'
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hx'
      have hcomp := oppositeSignRankTwo_completion_swap (d := d) (e := e) (f := q.f) x
      rw [hcomp] at hx'
      have hxy :
          (x 1 - c 1) ^ 2 - (x 0 - c 0) ^ 2 = κ := by
        simpa [c, κ] using hx'
      have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκpos
      have hy0 : y 0 = ((x 1 - c 1) - (x 0 - c 0)) / Real.sqrt κ := by
        simp [T, c, κ, hκpos.ne', hk_sqrt, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      have hy1 : y 1 = ((x 1 - c 1) + (x 0 - c 0)) / Real.sqrt κ := by
        simp [T, c, κ, hκpos.ne', hk_sqrt, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      rw [hy0, hy1]
      field_simp [hk_sqrt]
      rw [Real.sq_sqrt (le_of_lt hκpos)]
      nlinarith
    · intro hy
      let x : Point2 := T.symm y
      refine ⟨x, ?_, rfl⟩
      have hy' : y 0 * y 1 = 1 := hy
      have hk_sqrt : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.mpr hκpos
      have hx0 : x 0 - c 0 = Real.sqrt κ * ((y 1 - y 0) / 2) := by
        simp [x, T, c, κ, hκpos.ne', hk_sqrt, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hx1 : x 1 - c 1 = Real.sqrt κ * ((y 0 + y 1) / 2) := by
        simp [x, T, c, κ, hκpos.ne', hk_sqrt, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hxy : (x 1 - c 1) ^ 2 - (x 0 - c 0) ^ 2 = κ := by
        rw [hx0, hx1]
        field_simp
        rw [Real.sq_sqrt (le_of_lt hκpos)]
        nlinarith [hy']
      have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        rw [mem_PlaneCurveZeroSet]
        rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
        have hcomp := oppositeSignRankTwo_completion_swap (d := d) (e := e) (f := q.f) x
        rw [hcomp]
        linarith
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- In the rank-one case with quadratic term in the first coordinate and negative sign, vanishing
of the transverse linear coefficient forces an explicit factorization. -/
private lemma rankOne_firstCoordNeg_noTransverse_factorization
    (q : QuadraticPlaneCoeffs) {r : ℝ}
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 0)
    (he0 : quadraticPlaneNormalizedLinearCoeff1 q = 0)
    (hr : -r ^ 2 + quadraticPlaneNormalizedLinearCoeff0 q * r + q.f = 0) :
    quadraticPlaneNormalizedExplicitPolynomial q =
      (MvPolynomial.X 0 - MvPolynomial.C r) *
        (-MvPolynomial.X 0 +
          MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff0 q - r)) := by
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, he0]
  have hf : q.f = r ^ 2 - quadraticPlaneNormalizedLinearCoeff0 q * r := by
    nlinarith [hr]
  rw [hf]
  ring

/-- In the rank-one case, when the first coordinate carries the quadratic term, the transverse
linear coefficient is nonzero. -/
lemma rankOne_firstCoord_transverse_ne_zero_of_irreducible_infinite
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (hs : quadraticPlaneQuadraticFormNormalWeights q 0 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 0)
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    quadraticPlaneNormalizedLinearCoeff1 q ≠ 0 := by
  rcases hs with h0 | h0
  · simpa [h0] using
      rankOne_transverseLinear_ne_zero_of_irreducible_infinite q hIrred h0 h1 hInf
  · intro he0
    obtain ⟨z, hz⟩ := hInf.nonempty
    have hz' : z ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hz
    rw [mem_PlaneCurveZeroSet] at hz'
    rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, he0] at hz'
    have hr : -z 0 ^ 2 + quadraticPlaneNormalizedLinearCoeff0 q * z 0 + q.f = 0 := by
      simpa using hz'
    have hfac := rankOne_firstCoordNeg_noTransverse_factorization q h0 h1 he0 hr
    let l₁ : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 - MvPolynomial.C (z 0)
    let l₂ : MvPolynomial (Fin 2) ℝ :=
      -MvPolynomial.X 0 + MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff0 q - z 0)
    have hu : IsUnit l₁ ∨ IsUnit l₂ := by
      have hfac' : quadraticPlaneNormalizedPolynomial q = l₁ * l₂ := by
        rw [quadraticPlaneNormalizedPolynomial_eq_explicit]
        simpa [l₁, l₂] using hfac
      simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
    have hnu1 : ¬ IsUnit l₁ := by
      intro hl₁
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
      rcases hl₁ with ⟨c, hc⟩
      have hcoeff : l₁.coeff (Finsupp.single 0 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 0 1)) hc
      simp [l₁] at hcoeff
    have hnu2 : ¬ IsUnit l₂ := by
      intro hl₂
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
      rcases hl₂ with ⟨c, hc⟩
      have hcoeff : l₂.coeff (Finsupp.single 0 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 0 1)) hc
      simp [l₂] at hcoeff
    exact hu.elim hnu1 hnu2

/-- In the rank-one case with quadratic term in the second coordinate and positive sign,
vanishing of the transverse linear coefficient forces an explicit factorization. -/
private lemma rankOne_secondCoordPos_noTransverse_factorization
    (q : QuadraticPlaneCoeffs) {r : ℝ}
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 0)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 1)
    (hd0 : quadraticPlaneNormalizedLinearCoeff0 q = 0)
    (hr : r ^ 2 + quadraticPlaneNormalizedLinearCoeff1 q * r + q.f = 0) :
    quadraticPlaneNormalizedExplicitPolynomial q =
      (MvPolynomial.X 1 - MvPolynomial.C r) *
        (MvPolynomial.X 1 +
          MvPolynomial.C (r + quadraticPlaneNormalizedLinearCoeff1 q)) := by
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, hd0]
  have hf : q.f = -r * (r + quadraticPlaneNormalizedLinearCoeff1 q) := by
    nlinarith [hr]
  rw [hf]
  ring

/-- In the rank-one case with quadratic term in the second coordinate and negative sign,
vanishing of the transverse linear coefficient forces an explicit factorization. -/
private lemma rankOne_secondCoordNeg_noTransverse_factorization
    (q : QuadraticPlaneCoeffs) {r : ℝ}
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 0)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = -1)
    (hd0 : quadraticPlaneNormalizedLinearCoeff0 q = 0)
    (hr : -r ^ 2 + quadraticPlaneNormalizedLinearCoeff1 q * r + q.f = 0) :
    quadraticPlaneNormalizedExplicitPolynomial q =
      (MvPolynomial.X 1 - MvPolynomial.C r) *
        (-MvPolynomial.X 1 +
          MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff1 q - r)) := by
  rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, hd0]
  have hf : q.f = r ^ 2 - quadraticPlaneNormalizedLinearCoeff1 q * r := by
    nlinarith [hr]
  rw [hf]
  ring

/-- In the rank-one case, when the second coordinate carries the quadratic term, the transverse
linear coefficient is nonzero. -/
lemma rankOne_secondCoord_transverse_ne_zero_of_irreducible_infinite
    (q : QuadraticPlaneCoeffs)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 0)
    (hs : quadraticPlaneQuadraticFormNormalWeights q 1 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 1 = -1)
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    quadraticPlaneNormalizedLinearCoeff0 q ≠ 0 := by
  rcases hs with h1 | h1
  · intro hd0
    obtain ⟨z, hz⟩ := hInf.nonempty
    have hz' : z ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hz
    rw [mem_PlaneCurveZeroSet] at hz'
    rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, hd0] at hz'
    have hr : z 1 ^ 2 + quadraticPlaneNormalizedLinearCoeff1 q * z 1 + q.f = 0 := by
      simpa using hz'
    have hfac := rankOne_secondCoordPos_noTransverse_factorization q h0 h1 hd0 hr
    let l₁ : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 - MvPolynomial.C (z 1)
    let l₂ : MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.X 1 + MvPolynomial.C (z 1 + quadraticPlaneNormalizedLinearCoeff1 q)
    have hu : IsUnit l₁ ∨ IsUnit l₂ := by
      have hfac' : quadraticPlaneNormalizedPolynomial q = l₁ * l₂ := by
        rw [quadraticPlaneNormalizedPolynomial_eq_explicit]
        simpa [l₁, l₂] using hfac
      simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
    have hnu1 : ¬ IsUnit l₁ := by
      intro hl₁
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
      rcases hl₁ with ⟨c, hc⟩
      have hcoeff : l₁.coeff (Finsupp.single 1 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [l₁] at hcoeff
    have hnu2 : ¬ IsUnit l₂ := by
      intro hl₂
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
      rcases hl₂ with ⟨c, hc⟩
      have hcoeff : l₂.coeff (Finsupp.single 1 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [l₂] at hcoeff
    exact hu.elim hnu1 hnu2
  · intro hd0
    obtain ⟨z, hz⟩ := hInf.nonempty
    have hz' : z ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hz
    rw [mem_PlaneCurveZeroSet] at hz'
    rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1, hd0] at hz'
    have hr : -z 1 ^ 2 + quadraticPlaneNormalizedLinearCoeff1 q * z 1 + q.f = 0 := by
      simpa using hz'
    have hfac := rankOne_secondCoordNeg_noTransverse_factorization q h0 h1 hd0 hr
    let l₁ : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 - MvPolynomial.C (z 1)
    let l₂ : MvPolynomial (Fin 2) ℝ :=
      -MvPolynomial.X 1 + MvPolynomial.C (quadraticPlaneNormalizedLinearCoeff1 q - z 1)
    have hu : IsUnit l₁ ∨ IsUnit l₂ := by
      have hfac' : quadraticPlaneNormalizedPolynomial q = l₁ * l₂ := by
        rw [quadraticPlaneNormalizedPolynomial_eq_explicit]
        simpa [l₁, l₂] using hfac
      simpa [l₁, l₂] using hIrred.isUnit_or_isUnit hfac'
    have hnu1 : ¬ IsUnit l₁ := by
      intro hl₁
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₁
      rcases hl₁ with ⟨c, hc⟩
      have hcoeff : l₁.coeff (Finsupp.single 1 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [l₁] at hcoeff
    have hnu2 : ¬ IsUnit l₂ := by
      intro hl₂
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hl₂
      rcases hl₂ with ⟨c, hc⟩
      have hcoeff : l₂.coeff (Finsupp.single 1 1) = 0 := by
        simpa using congrArg
          (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (Finsupp.single 1 1)) hc
      simp [l₂] at hcoeff
    exact hu.elim hnu1 hnu2

/-- The completed-square center for the rank-one first-coordinate case. -/
private noncomputable def rankOneFirstCoordCenter (s d e f : ℝ) : Point2 :=
  !₂[(-d / (2 * s) : ℝ), (-(f - s * d ^ 2 / 4) / e : ℝ)]

/-- Completing squares in the rank-one first-coordinate case. -/
private lemma rankOneFirstCoord_completion
    {s d e f : ℝ} (hs : s = 1 ∨ s = -1) (he : e ≠ 0) (x : Point2) :
    s * x 0 ^ 2 + d * x 0 + e * x 1 + f =
      s * (x 0 - (rankOneFirstCoordCenter s d e f) 0) ^ 2 +
        e * (x 1 - (rankOneFirstCoordCenter s d e f) 1) := by
  rcases hs with rfl | rfl <;> simp [rankOneFirstCoordCenter, he]
  <;> ring

/-- The rank-one first-coordinate normalized curve is affine-equivalent to the parabola model. -/
theorem rankOne_firstCoord_conicNormalFormData_of_normalized
    (q : QuadraticPlaneCoeffs)
    (hs : quadraticPlaneQuadraticFormNormalWeights q 0 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 0 = -1)
    (h1 : quadraticPlaneQuadraticFormNormalWeights q 1 = 0)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    ConicNormalFormData (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)) := by
  let s := quadraticPlaneQuadraticFormNormalWeights q 0
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  have hs' : s = 1 ∨ s = -1 := by simpa [s] using hs
  have he : e ≠ 0 := by
    simpa [s] using rankOne_firstCoord_transverse_ne_zero_of_irreducible_infinite
      q hIrred hs h1 hInf
  let c := rankOneFirstCoordCenter s d e q.f
  let T : Point2 ≃ᵃ[ℝ] Point2 :=
    (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
      (AffineEquiv.ofLinearEquiv
        (point2DiagLinearEquiv 1 (-s * e) one_ne_zero
          (by
            rcases hs' with rfl | rfl <;> simpa using he)) 0 0)
  refine ⟨ConicModel.parabola, T, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ConicModelSet, Set.mem_setOf_eq]
    have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
    rw [mem_PlaneCurveZeroSet] at hx'
    rw [quadraticPlaneNormalizedExplicitPolynomial, h1] at hx'
    have hsEq : quadraticPlaneQuadraticFormNormalWeights q 0 = s := by simp [s]
    rw [hsEq] at hx'
    have hcomp := rankOneFirstCoord_completion (s := s) (d := d) (e := e) (f := q.f) hs' he x
    rw [hcomp] at hx'
    have hy0 : y 0 = x 0 - c 0 := by
      simp [T, c, point2DiagLinearEquiv, point2DiagLinearMap]
    have hy1 : y 1 = (-s * e) * (x 1 - c 1) := by
      simp [T, c, point2DiagLinearEquiv, point2DiagLinearMap]
    rw [hy0, hy1]
    rcases hs' with rfl | rfl <;> nlinarith
  · intro hy
    let x : Point2 := T.symm y
    refine ⟨x, ?_, rfl⟩
    have hy' : y 1 = y 0 ^ 2 := hy
    have hx0 : x 0 - c 0 = y 0 := by
      simp [x, T, c, point2DiagLinearEquiv, point2DiagLinearMap]
    have hx1 : x 1 - c 1 = y 1 / (-s * e) := by
      simp [x, T, c, point2DiagLinearEquiv, point2DiagLinearMap, he]
    have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      rw [mem_PlaneCurveZeroSet]
      rw [quadraticPlaneNormalizedExplicitPolynomial, h1]
      have hsEq : quadraticPlaneQuadraticFormNormalWeights q 0 = s := by simp [s]
      rw [hsEq]
      have hcomp := rankOneFirstCoord_completion (s := s) (d := d) (e := e) (f := q.f) hs' he x
      rw [hcomp]
      rw [hx0, hx1, hy']
      rcases hs' with rfl | rfl <;> field_simp [he] <;> ring
    simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- The completed-square center for the rank-one second-coordinate case. -/
private noncomputable def rankOneSecondCoordCenter (s d e f : ℝ) : Point2 :=
  !₂[(-(f - s * e ^ 2 / 4) / d : ℝ), (-e / (2 * s) : ℝ)]

/-- Completing squares in the rank-one second-coordinate case. -/
private lemma rankOneSecondCoord_completion
    {s d e f : ℝ} (hs : s = 1 ∨ s = -1) (hd : d ≠ 0) (x : Point2) :
    d * x 0 + s * x 1 ^ 2 + e * x 1 + f =
      d * (x 0 - (rankOneSecondCoordCenter s d e f) 0) +
        s * (x 1 - (rankOneSecondCoordCenter s d e f) 1) ^ 2 := by
  rcases hs with rfl | rfl <;> simp [rankOneSecondCoordCenter, hd]
  <;> ring

/-- The rank-one second-coordinate normalized curve is affine-equivalent to the parabola model. -/
theorem rankOne_secondCoord_conicNormalFormData_of_normalized
    (q : QuadraticPlaneCoeffs)
    (h0 : quadraticPlaneQuadraticFormNormalWeights q 0 = 0)
    (hs : quadraticPlaneQuadraticFormNormalWeights q 1 = 1 ∨
      quadraticPlaneQuadraticFormNormalWeights q 1 = -1)
    (hIrred : Irreducible (quadraticPlaneNormalizedPolynomial q))
    (hInf : (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)).Infinite) :
    ConicNormalFormData (PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)) := by
  let s := quadraticPlaneQuadraticFormNormalWeights q 1
  let d := quadraticPlaneNormalizedLinearCoeff0 q
  let e := quadraticPlaneNormalizedLinearCoeff1 q
  have hs' : s = 1 ∨ s = -1 := by simpa [s] using hs
  have hd : d ≠ 0 := by
    simpa [s] using rankOne_secondCoord_transverse_ne_zero_of_irreducible_infinite
      q hIrred h0 hs hInf
  let c := rankOneSecondCoordCenter s d e q.f
  let T : Point2 ≃ᵃ[ℝ] Point2 :=
    (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
      (AffineEquiv.ofLinearEquiv
        ((point2SwapLinearEquiv).trans
          (point2DiagLinearEquiv 1 (-s * d) one_ne_zero
            (by
              rcases hs' with rfl | rfl <;> simpa using hd))) 0 0)
  refine ⟨ConicModel.parabola, T, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ConicModelSet, Set.mem_setOf_eq]
    have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
    rw [mem_PlaneCurveZeroSet] at hx'
    rw [quadraticPlaneNormalizedExplicitPolynomial, h0] at hx'
    have hsEq : quadraticPlaneQuadraticFormNormalWeights q 1 = s := by simp [s]
    rw [hsEq] at hx'
    have hcomp := rankOneSecondCoord_completion (s := s) (d := d) (e := e) (f := q.f) hs' hd x
    rw [hcomp] at hx'
    have hy0 : y 0 = x 1 - c 1 := by
      simp [T, c, point2SwapLinearEquiv, point2SwapLinearMap,
        point2DiagLinearEquiv, point2DiagLinearMap]
    have hy1 : y 1 = (-s * d) * (x 0 - c 0) := by
      simp [T, c, point2SwapLinearEquiv, point2SwapLinearMap,
        point2DiagLinearEquiv, point2DiagLinearMap]
    rw [hy0, hy1]
    rcases hs' with rfl | rfl <;> nlinarith
  · intro hy
    let x : Point2 := T.symm y
    refine ⟨x, ?_, rfl⟩
    have hy' : y 1 = y 0 ^ 2 := hy
    have hx0 : x 0 - c 0 = y 1 / (-s * d) := by
      simp [x, T, c, point2SwapLinearEquiv, point2SwapLinearMap,
        point2DiagLinearEquiv, point2DiagLinearMap, hd]
    have hx1 : x 1 - c 1 = y 0 := by
      simp [x, T, c, point2SwapLinearEquiv, point2SwapLinearMap,
        point2DiagLinearEquiv, point2DiagLinearMap]
    have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
      rw [mem_PlaneCurveZeroSet]
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0]
      have hsEq : quadraticPlaneQuadraticFormNormalWeights q 1 = s := by simp [s]
      rw [hsEq]
      have hcomp := rankOneSecondCoord_completion (s := s) (d := d) (e := e) (f := q.f) hs' hd x
      rw [hcomp]
      rw [hx0, hx1, hy']
      rcases hs' with rfl | rfl <;> field_simp [hd] <;> ring
    simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- A linear bivariate polynomial has total degree at most one. -/
private lemma linearPolynomial_totalDegree_le_one (a b c : ℝ) :
    ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 0 +
        MvPolynomial.C b * MvPolynomial.X 1 +
        MvPolynomial.C c).totalDegree ≤ 1 := by
  have hCa : ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ)).totalDegree = 0 := by
    simpa using (MvPolynomial.totalDegree_C (σ := Fin 2) a)
  have hCb : ((MvPolynomial.C b : MvPolynomial (Fin 2) ℝ)).totalDegree = 0 := by
    simpa using (MvPolynomial.totalDegree_C (σ := Fin 2) b)
  have hCc : ((MvPolynomial.C c : MvPolynomial (Fin 2) ℝ)).totalDegree = 0 := by
    simpa using (MvPolynomial.totalDegree_C (σ := Fin 2) c)
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree = 1 := by
    simpa using (MvPolynomial.totalDegree_X (σ := Fin 2) (0 : Fin 2))
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree = 1 := by
    simpa using (MvPolynomial.totalDegree_X (σ := Fin 2) (1 : Fin 2))
  have hprod0 : ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 0).totalDegree ≤ 1 := by
    simpa [hCa, hX0] using (MvPolynomial.totalDegree_mul
      (a := (MvPolynomial.C a : MvPolynomial (Fin 2) ℝ))
      (b := MvPolynomial.X 0))
  have hprod1 : ((MvPolynomial.C b : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 1).totalDegree ≤ 1 := by
    simpa [hCb, hX1] using (MvPolynomial.totalDegree_mul
      (a := (MvPolynomial.C b : MvPolynomial (Fin 2) ℝ))
      (b := MvPolynomial.X 1))
  have hsum01 :
      ((MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1).totalDegree ≤ 1 := by
    have hadd := MvPolynomial.totalDegree_add
      (a := (MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 0)
      (b := MvPolynomial.C b * MvPolynomial.X 1)
    exact le_trans hadd (max_le_iff.mpr ⟨hprod0, hprod1⟩)
  have hadd := MvPolynomial.totalDegree_add
    (a := (MvPolynomial.C a : MvPolynomial (Fin 2) ℝ) * MvPolynomial.X 0 +
      MvPolynomial.C b * MvPolynomial.X 1)
    (b := MvPolynomial.C c)
  exact le_trans (by simpa [add_assoc] using hadd)
    (max_le_iff.mpr ⟨hsum01, by omega⟩)

/-- Assemble a conic normal form from the exact-degree conic witness surface. -/
theorem conicNormalFormData_of_isIrreducibleConic
    {C : Set Point2} (hC : IsIrreducibleConic C) :
    ConicNormalFormData C := by
  rcases hC with ⟨p, hp0, hpdeg, hpirr, hEq, hInf⟩
  let w : ConicWitness C := ⟨p, hp0, le_of_eq hpdeg, hpirr, hEq⟩
  rcases quadraticPlane_expansion w.p w.p_deg_le_two with ⟨q, hq⟩
  let A := quadraticPlaneQuadraticNormalizerAffine q
  let Z := PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q)
  have hZeq : Z = A '' C := by
    simpa [Z, A, hq, w.zeroSet_eq] using quadraticPlaneNormalized_zeroSet_eq_image q
  have hInfZ : Z.Infinite := by
    rw [hZeq]
    exact hInf.image A.injective
  have hIrredZ : Irreducible (quadraticPlaneNormalizedPolynomial q) := by
    rw [quadraticPlaneNormalizedPolynomial, hq]
    exact w.p_irreducible.map (affinePolyEquiv A.symm).toMulEquiv
  have hdegZ : (quadraticPlaneNormalizedPolynomial q).totalDegree = 2 := by
    rw [quadraticPlaneNormalizedPolynomial_totalDegree_eq, hq, hpdeg]
  have hs0 := quadraticPlaneQuadraticFormNormalWeights_spec q 0
  have hs1 := quadraticPlaneQuadraticFormNormalWeights_spec q 1
  have dataZ : ConicNormalFormData Z := by
    rcases hs0 with h0neg | h00 | h0pos
    · rcases hs1 with h1neg | h10 | h1pos
      · simpa [Z] using sameSign_rankTwo_conicNormalFormData_of_normalized
          q (Or.inr h0neg) (by simpa [h0neg] using h1neg) hInfZ
      · simpa [Z] using rankOne_firstCoord_conicNormalFormData_of_normalized
          q (Or.inr h0neg) h10 hIrredZ hInfZ
      · simpa [Z] using oppositeSign_rankTwo_swap_conicNormalFormData_of_normalized
          q hIrredZ h0neg h1pos
    · rcases hs1 with h1neg | h10 | h1pos
      · simpa [Z] using rankOne_secondCoord_conicNormalFormData_of_normalized
          q h00 (Or.inr h1neg) hIrredZ hInfZ
      · exfalso
        have hle : (quadraticPlaneNormalizedPolynomial q).totalDegree ≤ 1 := by
          rw [quadraticPlaneNormalizedPolynomial_eq_explicit,
            quadraticPlaneNormalizedExplicitPolynomial, h00, h10]
          simpa [add_assoc] using linearPolynomial_totalDegree_le_one
            (quadraticPlaneNormalizedLinearCoeff0 q)
            (quadraticPlaneNormalizedLinearCoeff1 q) q.f
        omega
      · simpa [Z] using rankOne_secondCoord_conicNormalFormData_of_normalized
          q h00 (Or.inl h1pos) hIrredZ hInfZ
    · rcases hs1 with h1neg | h10 | h1pos
      · simpa [Z] using oppositeSign_rankTwo_conicNormalFormData_of_normalized
          q hIrredZ h0pos h1neg
      · simpa [Z] using rankOne_firstCoord_conicNormalFormData_of_normalized
          q (Or.inl h0pos) h10 hIrredZ hInfZ
      · simpa [Z] using sameSign_rankTwo_conicNormalFormData_of_normalized
          q (Or.inl h0pos) (by simpa [h0pos] using h1pos) hInfZ
  exact conicNormalFormData_precompose A hZeq dataZ

/-- Lemma 2.7: every irreducible real conic admits the standard-model stabilizer packet. -/
theorem lemma27_conicStabilizerClassification :
    Lemma27_ConicStabilizerClassificationStatement := by
  intro C hC
  exact ⟨conicStabilizerNormalForm_of_data
    (conicNormalFormData_of_isIrreducibleConic hC)⟩
  · have hκneg : κ < 0 := lt_of_le_of_ne (le_of_not_gt hκpos) (Ne.symm hκne)
    let c := oppositeSignRankTwoCenterSwap d e
    let r : ℝ := Real.sqrt (-κ)
    let T : Point2 ≃ᵃ[ℝ] Point2 :=
      (AffineEquiv.constVAdd ℝ Point2 (-c)).trans
        (AffineEquiv.ofLinearEquiv
          ((point2SwapLinearEquiv.trans point2SumDiffLinearEquiv).trans
            (point2DiagLinearEquiv (-r⁻¹) r⁻¹
              (neg_ne_zero.mpr <| inv_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg)))
              (inv_ne_zero (Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg))))) 0 0)
    refine ⟨ConicModel.hyperbola, T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConicModelSet, Set.mem_setOf_eq]
      have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
      rw [mem_PlaneCurveZeroSet] at hx'
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hx'
      have hcomp := oppositeSignRankTwo_completion_swap (d := d) (e := e) (f := q.f) x
      rw [hcomp] at hx'
      have hxy :
          (x 1 - c 1) ^ 2 - (x 0 - c 0) ^ 2 = κ := by
        simpa [c, κ] using hx'
      have hk_sqrt : Real.sqrt (-κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg)
      have hy0 : y 0 = -(((x 1 - c 1) - (x 0 - c 0)) / Real.sqrt (-κ)) := by
        simp [T, c, κ, hk_sqrt, hκneg.ne, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      have hy1 : y 1 = ((x 1 - c 1) + (x 0 - c 0)) / Real.sqrt (-κ) := by
        simp [T, c, κ, hk_sqrt, hκneg.ne, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      rw [hy0, hy1]
      field_simp [hk_sqrt]
      rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr hκneg))]
      nlinarith
    · intro hy
      let x : Point2 := T.symm y
      refine ⟨x, ?_, rfl⟩
      have hy' : y 0 * y 1 = 1 := hy
      have hk_sqrt : Real.sqrt (-κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg)
      have hx0 : x 0 - c 0 = Real.sqrt (-κ) * ((y 1 - y 0) / 2) := by
        simp [x, T, c, κ, hk_sqrt, hκneg.ne, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hx1 : x 1 - c 1 = Real.sqrt (-κ) * ((y 0 + y 1) / 2) := by
        simp [x, T, c, κ, hk_sqrt, hκneg.ne, point2SwapLinearEquiv, point2SwapLinearMap,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hxy : (x 1 - c 1) ^ 2 - (x 0 - c 0) ^ 2 = κ := by
        rw [hx0, hx1]
        field_simp
        rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr hκneg))]
        nlinarith [hy']
      have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        rw [mem_PlaneCurveZeroSet]
        rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
        have hcomp := oppositeSignRankTwo_completion_swap (d := d) (e := e) (f := q.f) x
        rw [hcomp]
        linarith
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- The normalized polynomial has the same total degree as the original affine-conjugate
quadratic polynomial. -/
private lemma quadraticPlaneNormalizedPolynomial_totalDegree_eq
    (q : QuadraticPlaneCoeffs) :
    (quadraticPlaneNormalizedPolynomial q).totalDegree = q.toPolynomial.totalDegree := by
  simpa [quadraticPlaneNormalizedPolynomial] using
    affinePolyEquiv_totalDegree_eq (quadraticPlaneQuadraticNormalizerAffine q).symm q.toPolynomial

/-- The normalized real zero set is the image of the original zero set under the chosen
quadratic-part normalizer. -/
private lemma quadraticPlaneNormalized_zeroSet_eq_image
    (q : QuadraticPlaneCoeffs) :
    PlaneCurveZeroSet (quadraticPlaneNormalizedPolynomial q) =
      quadraticPlaneQuadraticNormalizerAffine q '' PlaneCurveZeroSet q.toPolynomial := by
  ext x
  constructor
  · intro hx
    refine ⟨(quadraticPlaneQuadraticNormalizerAffine q).symm x, ?_, by simp⟩
    rw [mem_PlaneCurveZeroSet] at hx ⊢
    rw [quadraticPlaneNormalizedPolynomial, affinePolyEquiv_eval] at hx
    simpa using hx
  · rintro ⟨y, hy, rfl⟩
    rw [mem_PlaneCurveZeroSet] at hy ⊢
    rw [quadraticPlaneNormalizedPolynomial, affinePolyEquiv_eval]
    simpa using hy

/-- Precompose normal-form data along an affine equivalence identifying the source curve with the
current target. -/
private theorem conicNormalFormData_precompose
    {C D : Set Point2} (A : Point2 ≃ᵃ[ℝ] Point2)
    (hD : D = A '' C) (data : ConicNormalFormData D) :
    ConicNormalFormData C := by
  subst hD
  refine ⟨data.model, A.trans data.e, ?_⟩
  simpa [Set.image_image, AffineEquiv.trans_apply] using data.image_eq
  · have hκneg : κ < 0 := lt_of_le_of_ne (le_of_not_gt hκpos) (Ne.symm hκne)
    let c := oppositeSignRankTwoCenter d e
    let r : ℝ := Real.sqrt (-κ)
    let T := oppositeSignRankTwoAffineNeg q hκneg
    refine ⟨ConicModel.hyperbola, T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ConicModelSet, Set.mem_setOf_eq]
      have hx' : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx
      rw [mem_PlaneCurveZeroSet] at hx'
      rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1] at hx'
      have hcomp := oppositeSignRankTwo_completion (d := d) (e := e) (f := q.f) x
      rw [hcomp] at hx'
      have hxy :
          (x 0 - c 0) ^ 2 - (x 1 - c 1) ^ 2 = κ := by
        simpa [c, κ] using hx'
      have hk_sqrt : Real.sqrt (-κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg)
      have hy0 : y 0 = -(((x 0 - c 0) - (x 1 - c 1)) / Real.sqrt (-κ)) := by
        simp [T, oppositeSignRankTwoAffineNeg, c, κ, hk_sqrt, hκneg.ne,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      have hy1 : y 1 = ((x 0 - c 0) + (x 1 - c 1)) / Real.sqrt (-κ) := by
        simp [T, oppositeSignRankTwoAffineNeg, c, κ, hk_sqrt, hκneg.ne,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
      rw [hy0, hy1]
      field_simp [hk_sqrt]
      rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr hκneg))]
      nlinarith
    · intro hy
      let x : Point2 := T.symm y
      refine ⟨x, ?_, rfl⟩
      have hy' : y 0 * y 1 = 1 := hy
      have hk_sqrt : Real.sqrt (-κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hκneg)
      have hx0 : x 0 - c 0 = Real.sqrt (-κ) * ((y 1 - y 0) / 2) := by
        simp [x, T, oppositeSignRankTwoAffineNeg, c, κ, hk_sqrt, hκneg.ne,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hx1 : x 1 - c 1 = Real.sqrt (-κ) * ((y 0 + y 1) / 2) := by
        simp [x, T, oppositeSignRankTwoAffineNeg, c, κ, hk_sqrt, hκneg.ne,
          point2SumDiffLinearEquiv, point2SumDiffLinearMap, point2SumDiffLinearMapInv,
          point2DiagLinearEquiv, point2DiagLinearMap]
        ring
      have hxy : (x 0 - c 0) ^ 2 - (x 1 - c 1) ^ 2 = κ := by
        rw [hx0, hx1]
        field_simp
        rw [Real.sq_sqrt (le_of_lt (neg_pos.mpr hκneg))]
        nlinarith [hy']
      have hx_explicit : x ∈ PlaneCurveZeroSet (quadraticPlaneNormalizedExplicitPolynomial q) := by
        rw [mem_PlaneCurveZeroSet]
        rw [quadraticPlaneNormalizedExplicitPolynomial, h0, h1]
        have hcomp := oppositeSignRankTwo_completion (d := d) (e := e) (f := q.f) x
        rw [hcomp]
        linarith
      simpa [quadraticPlaneNormalizedPolynomial_eq_explicit] using hx_explicit

/-- An orthonormal eigenbasis for the quadratic-part matrix. -/
noncomputable def quadraticPlaneEigenbasis (q : QuadraticPlaneCoeffs) :
    OrthonormalBasis (Fin 2) ℝ Point2 := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := quadraticPlaneSymmetricMatrix q
  have hS : (Matrix.toEuclideanLin S).IsSymmetric := by
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    simp [S, quadraticPlaneSymmetricMatrix]
  have hn : Module.finrank ℝ Point2 = 2 := by
    simpa [Point2] using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 2))
  exact LinearMap.IsSymmetric.eigenvectorBasis hS hn

/-- The linear isometry coming from the quadratic-part eigenbasis. -/
noncomputable def quadraticPlaneDiagonalizingIsometry (q : QuadraticPlaneCoeffs) :
    Point2 ≃ₗᵢ[ℝ] Point2 :=
  (quadraticPlaneEigenbasis q).toLinearIsometry

/- ## Plane isometry classification surface -/

/-- A nontrivial translation of the plane. -/
def IsNontrivialTranslation (g : Point2 ≃ᵢ Point2) : Prop :=
  ∃ v : Point2, v ≠ 0 ∧ ∀ x : Point2, g x = x + v

/-- A rotation around a point. -/
def IsRotationAround (a : Point2) (g : Point2 ≃ᵢ Point2) : Prop :=
  g a = a ∧
    0 < LinearMap.det
      (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv : Point2 →ₗ[ℝ] Point2) ∧
    g.toRealAffineIsometryEquiv.linearIsometryEquiv ≠ LinearIsometryEquiv.refl ℝ Point2

/-- Reflection across an affine subspace. -/
def IsReflectionAcross (L : AffineSubspace ℝ Point2) [Nonempty L]
    [L.direction.HasOrthogonalProjection] (g : Point2 ≃ᵢ Point2) : Prop :=
  g = (EuclideanGeometry.reflection L).toIsometryEquiv

/-- A glide reflection along an affine subspace. -/
def IsGlideReflectionAlong (L : AffineSubspace ℝ Point2) [Nonempty L]
    [L.direction.HasOrthogonalProjection] (g : Point2 ≃ᵢ Point2) : Prop :=
  ∃ v : Point2, v ∈ L.direction ∧ v ≠ 0 ∧
    g = ((EuclideanGeometry.reflection L).trans
      (AffineIsometryEquiv.constVAdd ℝ Point2 v)).toIsometryEquiv

/-- The local plane-isometry kind packet used in the curve-symmetry bound. -/
inductive PlaneIsometryKind (g : Point2 ≃ᵢ Point2) : Prop
| identity
| translation (hg : IsNontrivialTranslation g)
| rotation (a : Point2) (hg : IsRotationAround a g)
| reflection (L : AffineSubspace ℝ Point2) [Nonempty L]
    [L.direction.HasOrthogonalProjection] (hg : IsReflectionAcross L g)
| glideReflection (L : AffineSubspace ℝ Point2) [Nonempty L]
    [L.direction.HasOrthogonalProjection] (hg : IsGlideReflectionAlong L g)

/-- Every plane linear isometry either commutes or anticommutes with the
standard quarter-turn `J`. -/
lemma linear_isometry_commutes_or_anticommutes_with_J
    (A : Point2 ≃ₗᵢ[ℝ] Point2) :
    (∀ x : Point2, A (Orientation.rightAngleRotation
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
      Orientation.rightAngleRotation
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (A x)) ∨
    (∀ x : Point2, A (Orientation.rightAngleRotation
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
      - Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (A x)) := by
  let J : Point2 → Point2 := Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2))
  have hdet_ne : LinearMap.det (A.toLinearEquiv : Point2 →ₗ[ℝ] Point2) ≠ 0 := by
    intro hzero
    have hdet := LinearEquiv.det_symm_mul_det A.toLinearEquiv
    simp [hzero] at hdet
  rcases lt_or_gt_of_ne hdet_ne with hneg | hpos
  · right
    intro x
    have hmap : Orientation.map (Fin 2) A.toLinearEquiv
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) = -positiveOrientation := by
      have hfin : Fintype.card (Fin 2) = Module.finrank ℝ Point2 := by
        simpa [Point2] using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 2)).symm
      exact (positiveOrientation.map_eq_neg_iff_det_neg A.toLinearEquiv hfin).2 hneg
    have hrot := (positiveOrientation.rightAngleRotation_map A (A x))
    rw [hmap] at hrot
    rw [Orientation.rightAngleRotation_neg_orientation] at hrot
    simpa [eq_comm] using hrot.symm
  · left
    intro x
    exact positiveOrientation.linearIsometryEquiv_comp_rightAngleRotation A hpos x

/-- An orientation-reversing linear isometry is not the negation map. -/
lemma orientationReversing_linear_not_neg
    (A : Point2 ≃ₗᵢ[ℝ] Point2)
    (hanti : ∀ x : Point2, A (Orientation.rightAngleRotation
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
      - Orientation.rightAngleRotation
          (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (A x)) :
    A ≠ (LinearIsometryEquiv.neg (R := ℝ) (E := Point2)) := by
  intro hA
  let J : Point2 ≃ₗᵢ[ℝ] Point2 := Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2))
  let e0 : Point2 :=
    WithLp.toLp (p := (2 : ENNReal)) (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
  have he0 : e0 ≠ 0 := by
    intro hzero
    have h1 : (1 : ℝ) = 0 := by
      have h := congrArg (fun v : Point2 => v.ofLp 0) hzero
      simpa [e0] using h
    exact one_ne_zero h1
  have hA1 : A e0 = - e0 := by
    simpa [LinearIsometryEquiv.neg, e0] using congrArg
      (fun f : Point2 ≃ₗᵢ[ℝ] Point2 => f e0) hA
  have hJfix : A (J e0) = J e0 := by
    simpa [J, e0, hA1] using hanti e0
  have hJneg : A (J e0) = - J e0 := by
    simpa [J, e0] using congrArg (fun f : Point2 ≃ₗᵢ[ℝ] Point2 => f (J e0)) hA
  have hEq : J e0 = - J e0 := by
    exact hJfix.symm.trans hJneg
  have h2 : (2 : ℝ) • J e0 = 0 := by
    have htmp := congrArg (fun z : Point2 => z + J e0) hEq
    simpa [eq_neg_iff_add_eq_zero, two_smul, add_comm, add_left_comm, add_assoc] using htmp
  have hJne : J e0 ≠ 0 := by
    intro hzero
    exact he0 (J.injective (by simpa using hzero))
  exact hJne ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- An orientation-reversing linear isometry fixes some nonzero vector and
sends its quarter-turn to the opposite quarter-turn. -/
lemma orientationReversing_linear_exists_reflection_basis
    (A : Point2 ≃ₗᵢ[ℝ] Point2)
    (hanti : ∀ x : Point2, A (Orientation.rightAngleRotation
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
      - Orientation.rightAngleRotation
          (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (A x)) :
    ∃ e : Point2, e ≠ 0 ∧ A e = e ∧
      A (Orientation.rightAngleRotation (positiveOrientation : Orientation ℝ Point2 (Fin 2)) e) =
        - Orientation.rightAngleRotation
            (positiveOrientation : Orientation ℝ Point2 (Fin 2)) e := by
  let J : Point2 ≃ₗᵢ[ℝ] Point2 := Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2))
  let e0 : Point2 :=
    WithLp.toLp (p := (2 : ENNReal)) (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
  have he0 : e0 ≠ 0 := by
    intro hzero
    have h1 : (1 : ℝ) = 0 := by
      have h := congrArg (fun v : Point2 => v.ofLp 0) hzero
      simpa [e0] using h
    exact one_ne_zero h1
  by_cases hAe0 : A e0 = - e0
  · refine ⟨J e0, ?_, ?_, ?_⟩
    · intro hzero
      exact he0 (J.injective (by simpa using hzero))
    · have hJfix : A (J e0) = J e0 := by
        simpa [J, e0, hAe0] using hanti e0
      simpa [J, e0, hAe0, hJfix, Orientation.rightAngleRotation_rightAngleRotation] using
        hanti (J e0)
    · simpa [J, e0, hAe0, Orientation.rightAngleRotation_rightAngleRotation] using
        hanti (J e0)
  ·
    let v : Point2 := e0
    have hv0 : v ≠ 0 := he0
    let b : Module.Basis (Fin 2) ℝ Point2 := positiveOrientation.basisRightAngleRotation v hv0
    let a : ℝ := b.repr (A v) 0
    let c : ℝ := b.repr (A v) 1
    have hAv : A v = a • v + c • J v := by
      have hsum := b.sum_repr (A v)
      rw [show ⇑b = ![v, J v] from positiveOrientation.coe_basisRightAngleRotation v hv0] at hsum
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, add_zero] at hsum
      exact hsum.symm
    have hAvJ : A (J v) = c • v - a • J v := by
      simpa [hAv, J, sub_eq_add_neg] using hanti v
    have hJorth : inner ℝ v (J v) = 0 := by
      simpa [J] using positiveOrientation.inner_rightAngleRotation_self v
    have hJorth' : inner ℝ (J v) v = 0 := by
      simpa [real_inner_comm] using hJorth
    have hJnorm : inner ℝ (J v) (J v) = inner ℝ v v := by
      simpa [J] using positiveOrientation.inner_comp_rightAngleRotation v v
    have hinner : inner ℝ (A v) (A v) = (a ^ 2 + c ^ 2) * inner ℝ v v := by
      simp_rw [hAv, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hJorth, hJorth', hJnorm]
      ring
    have hnorm : (a ^ 2 + c ^ 2) = 1 := by
      have hA_norm := A.norm_map v
      have hsq : (a ^ 2 + c ^ 2) * ‖v‖ ^ 2 = ‖v‖ ^ 2 := by
        calc
          (a ^ 2 + c ^ 2) * ‖v‖ ^ 2 = inner ℝ (A v) (A v) := by
            rw [hinner, real_inner_self_eq_norm_sq]
          _ = ‖v‖ ^ 2 := by
            simpa using congrArg (fun t => t ^ 2) hA_norm
      have hvsq_ne : ‖v‖ ^ 2 ≠ 0 := by
        have : ‖v‖ ≠ 0 := by simpa [norm_eq_zero] using hv0
        exact pow_ne_zero 2 this
      have hsq' : (a ^ 2 + c ^ 2) * ‖v‖ ^ 2 = 1 * ‖v‖ ^ 2 := by simpa using hsq
      exact mul_right_cancel₀ hvsq_ne hsq'
    refine ⟨v + A v, ?_, ?_, ?_⟩
    · intro hzero
      have hanti0 : A v = -v := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [v, add_comm] using hzero
      exact hAe0 hanti0
    · rw [hAv]
      simp [hnorm, add_comm, add_left_comm, add_assoc, hAvJ]
    · rw [hAv]
      simp [hnorm, hAvJ, hanti, add_comm, add_left_comm, add_assoc, J, smul_add,
        smul_neg, add_smul, real_inner_self_eq_norm_sq]

/-- A nonidentity orientation-preserving affine plane isometry has a unique
fixed point. -/
lemma orientationPreserving_nontrivial_affine_has_unique_fixed_point
    (g : Point2 ≃ᵢ Point2)
    (hpos : 0 < LinearMap.det
      (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv : Point2 →ₗ[ℝ] Point2))
    (hne : g.toRealAffineIsometryEquiv.linearIsometryEquiv ≠ LinearIsometryEquiv.refl ℝ Point2) :
    ∃! a : Point2, g a = a := by
  let A : Point2 ≃ₗᵢ[ℝ] Point2 := g.toRealAffineIsometryEquiv.linearIsometryEquiv
  let L : Point2 →ₗ[ℝ] Point2 := LinearMap.id - A.toLinearMap
  have hcomm : ∀ x : Point2, A (Orientation.rightAngleRotation
      (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
    Orientation.rightAngleRotation
      (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (A x) :=
    positiveOrientation.linearIsometryEquiv_comp_rightAngleRotation A hpos
  have hinj : Function.Injective L := by
    intro x y hxy
    have hz : L (x - y) = 0 := by
      simpa [map_sub, hxy] using (map_sub L x y)
    -- Re-express the kernel condition as `A (x - y) = x - y`.
    have hzA : A (x - y) = x - y := by
      have hz' : (x - y) - A (x - y) = 0 := by
        simpa [L, sub_eq_add_neg] using hz
      simpa [eq_comm] using (sub_eq_zero.mp hz')
    by_cases hz0 : x - y = 0
    · exact sub_eq_zero.mp hz0
    · have hAeq : A = LinearIsometryEquiv.refl ℝ Point2 := by
        apply (positiveOrientation.basisRightAngleRotation (x - y) hz0).ext_linearIsometryEquiv
        intro i
        fin_cases i
        · simpa using hzA
        · have hzJ : A (Orientation.rightAngleRotation
              (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (x - y)) =
              Orientation.rightAngleRotation
                (positiveOrientation : Orientation ℝ Point2 (Fin 2)) (x - y) := by
            simpa [hzA] using hcomm (x - y)
          simpa using hzJ
      exact False.elim (hne hAeq)
  have hsurj : Function.Surjective L := (LinearMap.injective_iff_surjective.mp hinj)
  rcases hsurj (g 0) with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · have hmap := g.toRealAffineIsometryEquiv.map_vadd 0 a
    have ha' : a + -A a = g 0 := by
      simpa [L, sub_eq_add_neg] using ha
    have hEq : a = g 0 + A a := by
      have htmp := congrArg (fun z : Point2 => z + A a) ha'
      simpa [add_comm, add_left_comm, add_assoc] using htmp
    have hEq' : A a + g 0 = a := by
      simpa [add_comm, add_left_comm, add_assoc] using hEq.symm
    simpa [hEq'] using hmap
  · intro b hb
    have hmap := g.toRealAffineIsometryEquiv.map_vadd (0 : Point2) b
    have hbEq : b = g 0 + A b := by
      simpa [hb, add_comm, add_left_comm, add_assoc] using hmap
    have hb' : L b = g 0 := by
      have htmp := congrArg (fun z : Point2 => z + -A b) hbEq
      simpa [L, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htmp
    exact hinj (by
      rw [ha]
      exact hb')

/-- If the linear part is the identity, an affine plane isometry is either the
identity or a nontrivial translation. -/
lemma affine_isometry_linear_eq_one_or_translation
    (g : Point2 ≃ᵢ Point2)
    (hlin : g.toRealAffineIsometryEquiv.linearIsometryEquiv =
      LinearIsometryEquiv.refl ℝ Point2) :
    g = IsometryEquiv.refl Point2 ∨ IsNontrivialTranslation g := by
  by_cases h0 : g 0 = 0
  · left
    ext x i
    have hmap := g.toRealAffineIsometryEquiv.map_vadd 0 x
    simpa [hlin, h0] using congrArg (fun p : Point2 => p.ofLp i) hmap
  · right
    refine ⟨g 0, h0, ?_⟩
    intro x
    have hmap := g.toRealAffineIsometryEquiv.map_vadd 0 x
    simpa [hlin, add_comm, add_left_comm, add_assoc] using hmap

/-- An orientation-reversing affine plane isometry is a reflection or a glide
reflection. -/
lemma orientationReversing_affine_is_reflection_or_glide
    (g : Point2 ≃ᵢ Point2)
    (hanti : ∀ x : Point2,
      g.toRealAffineIsometryEquiv.linearIsometryEquiv
        (Orientation.rightAngleRotation
          (positiveOrientation : Orientation ℝ Point2 (Fin 2)) x) =
        - Orientation.rightAngleRotation
            (positiveOrientation : Orientation ℝ Point2 (Fin 2))
            (g.toRealAffineIsometryEquiv.linearIsometryEquiv x)) :
    ∃ L : AffineSubspace ℝ Point2, ∃ hL : Nonempty L, ∃ hproj : L.direction.HasOrthogonalProjection,
      letI : Nonempty L := hL
      letI : L.direction.HasOrthogonalProjection := hproj
      IsReflectionAcross L g ∨ IsGlideReflectionAlong L g := by
  classical
  let J : Point2 → Point2 := Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2))
  let A : Point2 ≃ₗᵢ[ℝ] Point2 := g.toRealAffineIsometryEquiv.linearIsometryEquiv
  have hantiA : ∀ x : Point2, A (J x) = - J (A x) := by
    simpa [A] using hanti
  rcases orientationReversing_linear_exists_reflection_basis A hantiA with
    ⟨e, he0, heA, heJ⟩
  let b : Module.Basis (Fin 2) ℝ Point2 := positiveOrientation.basisRightAngleRotation e he0
  let s : ℝ := b.repr (g 0) 0
  let t : ℝ := b.repr (g 0) 1
  let p : Point2 := (t / 2) • J e
  let L : AffineSubspace ℝ Point2 := AffineSubspace.mk' p (ℝ ∙ e)
  have hLnonempty : Nonempty L := by
    refine ⟨⟨p, ?_⟩⟩
    simpa [L] using (AffineSubspace.self_mem_mk' p (ℝ ∙ e))
  have hLproj : L.direction.HasOrthogonalProjection := by
    simpa [L, AffineSubspace.direction_mk'] using
      (show (ℝ ∙ e).HasOrthogonalProjection from inferInstance)
  haveI : Nonempty L := hLnonempty
  haveI : L.direction.HasOrthogonalProjection := hLproj
  have hbasis : ⇑b = ![e, J e] := positiveOrientation.coe_basisRightAngleRotation e he0
  have hg0 : g 0 = s • e + t • J e := by
    have hsum := b.sum_repr (g 0)
    rw [hbasis] at hsum
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, add_zero] at hsum
    simpa [s, t, add_comm, add_left_comm, add_assoc] using hsum.symm
  by_cases hs : s = 0
  · refine ⟨L, hLnonempty, hLproj, ?_⟩
    left
    ext x
    let u : ℝ := b.repr (x -ᵥ p) 0
    let v : ℝ := b.repr (x -ᵥ p) 1
    have hx : x = (u • e + v • J e) +ᵥ p := by
      have hsum := b.sum_repr (x -ᵥ p)
      rw [hbasis] at hsum
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, add_zero] at hsum
      simpa [u, v] using (congrArg (fun z : Point2 => z +ᵥ p) hsum).symm
    have hpu : u • e +ᵥ p ∈ L := by
      simpa [L] using
        (AffineSubspace.vadd_mem_mk' (p := p) (direction := ℝ ∙ e) (v := u • e)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
    have hvorth : v • J e ∈ L.directionᗮ := by
      have horth : inner ℝ (v • J e) e = 0 := by
        simp [inner_smul_left, inner_rightAngleRotation_self]
      simpa [L, AffineSubspace.direction_mk', Submodule.mem_orthogonal_singleton_iff_inner_left]
        using horth
    have href : EuclideanGeometry.reflection L x = (u • e - v • J e) +ᵥ p := by
      calc
        EuclideanGeometry.reflection L x =
            EuclideanGeometry.reflection L (v • J e +ᵥ (u • e +ᵥ p)) := by
              simp [hx, add_comm, add_left_comm, add_assoc]
        _ = - (v • J e) +ᵥ (u • e +ᵥ p) := by
              exact EuclideanGeometry.reflection_orthogonal_vadd
                (s := L) (p := u • e +ᵥ p) (v := v • J e) hpu hvorth
        _ = (u • e - v • J e) +ᵥ p := by
              simp [add_comm, add_left_comm, add_assoc]
    have hgx : g x = (u • e - v • J e) +ᵥ p := by
      calc
        g x = A (u • e + v • J e) +ᵥ g p := by
          simpa [hx, A] using g.toRealAffineIsometryEquiv.map_vadd p (u • e + v • J e)
        _ = (u • e - v • J e) +ᵥ (s • e +ᵥ p) := by
          have hAw : A (u • e + v • J e) = u • e - v • J e := by
            simp [A, heA, heJ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          have hgp : g p = s • e +ᵥ p := by
            calc
              g p = A p +ᵥ g 0 := by
                simpa [p, A] using g.toRealAffineIsometryEquiv.map_vadd (0 : Point2) p
              _ = s • e +ᵥ p := by
                simp [p, A, hg0, heJ, hs, add_comm, add_left_comm, add_assoc,
                  sub_eq_add_neg, two_mul]
          rw [hAw, hgp]
        _ = (u • e - v • J e) +ᵥ p := by simp [hs, add_comm, add_left_comm, add_assoc]
    simpa [href] using hgx
  · refine ⟨L, hLnonempty, hLproj, ?_⟩
    right
    refine ⟨s • e, ?_⟩
    constructor
    · simpa [L] using (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    · constructor
      · intro hs0
        exact hs ((smul_eq_zero.mp hs0).resolve_right he0)
      · ext x
      let u : ℝ := b.repr (x -ᵥ p) 0
      let v : ℝ := b.repr (x -ᵥ p) 1
      have hx : x = (u • e + v • J e) +ᵥ p := by
      have hsum := b.sum_repr (x -ᵥ p)
      rw [hbasis] at hsum
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, add_zero] at hsum
      simpa [u, v] using (congrArg (fun z : Point2 => z +ᵥ p) hsum).symm
      have hpu : u • e +ᵥ p ∈ L := by
        simpa [L] using
          (AffineSubspace.vadd_mem_mk' (p := p) (direction := ℝ ∙ e) (v := u • e)
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
      have hvorth : v • J e ∈ L.directionᗮ := by
        have horth : inner ℝ (v • J e) e = 0 := by
          simp [inner_smul_left, inner_rightAngleRotation_self]
        simpa [L, AffineSubspace.direction_mk', Submodule.mem_orthogonal_singleton_iff_inner_left]
          using horth
      have href : EuclideanGeometry.reflection L x = (u • e - v • J e) +ᵥ p := by
        calc
          EuclideanGeometry.reflection L x =
              EuclideanGeometry.reflection L (v • J e +ᵥ (u • e +ᵥ p)) := by
                simp [hx, add_comm, add_left_comm, add_assoc]
          _ = - (v • J e) +ᵥ (u • e +ᵥ p) := by
                exact EuclideanGeometry.reflection_orthogonal_vadd
                  (s := L) (p := u • e +ᵥ p) (v := v • J e) hpu hvorth
          _ = (u • e - v • J e) +ᵥ p := by
                simp [add_comm, add_left_comm, add_assoc]
      have hgx : g x = (u • e + s • e - v • J e) +ᵥ p := by
        calc
          g x = A (u • e + v • J e) +ᵥ g p := by
            simpa [hx, A] using g.toRealAffineIsometryEquiv.map_vadd p (u • e + v • J e)
          _ = (u • e - v • J e) +ᵥ (s • e +ᵥ p) := by
            have hAw : A (u • e + v • J e) = u • e - v • J e := by
              simp [A, heA, heJ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            have hgp : g p = s • e +ᵥ p := by
              calc
                g p = A p +ᵥ g 0 := by
                  simpa [p, A] using g.toRealAffineIsometryEquiv.map_vadd (0 : Point2) p
                _ = s • e +ᵥ p := by
                  simp [p, A, hg0, heJ, hs, add_comm, add_left_comm, add_assoc,
                    sub_eq_add_neg, two_mul]
            rw [hAw, hgp]
          _ = (u • e + s • e - v • J e) +ᵥ p := by simp [add_comm, add_left_comm, add_assoc]
      have hcand : (((EuclideanGeometry.reflection L).trans
          (AffineIsometryEquiv.constVAdd ℝ Point2 (s • e))).toIsometryEquiv x) =
          (u • e + s • e - v • J e) +ᵥ p := by
        simp [AffineIsometryEquiv.coe_trans, AffineIsometryEquiv.coe_constVAdd, href,
          add_comm, add_left_comm, add_assoc]
      simpa [hcand] using hgx

/-- Every plane isometry is either a translation, a rotation, a reflection, or
a glide reflection. -/
theorem classify_plane_isometry
    (g : Point2 ≃ᵢ Point2) :
    PlaneIsometryKind g := by
  classical
  let J : Point2 → Point2 := Orientation.rightAngleRotation
    (positiveOrientation : Orientation ℝ Point2 (Fin 2))
  let A : Point2 ≃ₗᵢ[ℝ] Point2 := g.toRealAffineIsometryEquiv.linearIsometryEquiv
  have hdet_ne : LinearMap.det (A.toLinearEquiv : Point2 →ₗ[ℝ] Point2) ≠ 0 := by
    intro hzero
    have hdet := LinearEquiv.det_symm_mul_det A.toLinearEquiv
    simp [hzero] at hdet
  rcases lt_or_gt_of_ne hdet_ne with hneg | hpos
  · have hmap : Orientation.map (Fin 2) A.toLinearEquiv
        (positiveOrientation : Orientation ℝ Point2 (Fin 2)) =
        - positiveOrientation := by
        have hfin : Fintype.card (Fin 2) = Module.finrank ℝ Point2 := by
          simpa [Point2] using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 2)).symm
        exact (positiveOrientation.map_eq_neg_iff_det_neg A.toLinearEquiv hfin).2 hneg
    have hanti : ∀ x : Point2, A (J x) = - J (A x) := by
      intro x
      have hrot := positiveOrientation.rightAngleRotation_map A (A x)
      rw [hmap] at hrot
      rw [Orientation.rightAngleRotation_neg_orientation] at hrot
      simpa [eq_comm] using hrot.symm
    rcases orientationReversing_affine_is_reflection_or_glide g hanti with
      ⟨L, hL, hproj, hcase⟩
    haveI : Nonempty L := hL
    haveI : L.direction.HasOrthogonalProjection := hproj
    have hcase' : IsReflectionAcross L g ∨ IsGlideReflectionAlong L g := by
      simpa using hcase
    cases hcase' with
    | inl href =>
        exact PlaneIsometryKind.reflection L href
    | inr hglide =>
        exact PlaneIsometryKind.glideReflection L hglide
  · by_cases hlin : A = LinearIsometryEquiv.refl ℝ Point2
    · rcases affine_isometry_linear_eq_one_or_translation g hlin with rfl | htrans
      · exact PlaneIsometryKind.identity
      · exact PlaneIsometryKind.translation htrans
    · rcases orientationPreserving_nontrivial_affine_has_unique_fixed_point g hpos hlin with
        ⟨a, ha, _⟩
      exact PlaneIsometryKind.rotation a ⟨ha, hpos, hlin⟩

-/

end PachDeZeeuw.Algebraic
