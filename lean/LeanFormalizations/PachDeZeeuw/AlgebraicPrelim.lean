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

The plane-curve predicates these lemmas range over. (Inlined here in the
`PlaneCurve` namespace so the file is self-contained and mathlib-only.) -/

namespace PlaneCurve

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
def IsLineOrCircle (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧
      C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ (center : Point2) (radius : ℝ), C = Metric.sphere center radius)

/-- The line-or-circle alternative, synonymously the controlled-degenerate case. -/
def IsLineOrCircleComponent (C : Set Point2) : Prop :=
  IsLineOrCircle C

end PlaneCurve

open EuclideanGeometry
open scoped Topology

/--
Two bounded-degree real plane curves have no shared infinite irreducible curve
component. This is not the Bezout conclusion: it does not assert that
`C₁ ∩ C₂` is finite or bounded.
-/
def NoCommonCurveComponent (C₁ C₂ : Set Point2) : Prop :=
  ¬ ∃ e : ℕ, ∃ C : Set Point2,
    PlaneCurve.IsIrreducibleCurve e C ∧ C.Infinite ∧ C ⊆ C₁ ∧ C ⊆ C₂

/-- Theorem 2.1, Bezout finite-intersection bound for plane curves. This is the
existential / finite-intersection consequence of Bézout's inequality (Theorem 2.1):
it asserts only that some degree-dependent bound `C` exists, a weaker statement than
the sharp `≤ d₁·d₂` count that is Theorem 2.1's full form. -/
def BezoutFiniteIntersectionStatement : Prop :=
  ∀ d₁ d₂ : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ C₁ C₂ : Set Point2,
      PlaneCurve.IsBoundedDegreeCurve d₁ C₁ →
      PlaneCurve.IsBoundedDegreeCurve d₂ C₂ →
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
  simp [MvPolynomial.eval_mul, hx]

/--
An infinite common irreducible factor gives a forbidden common curve
component.
-/
lemma noCommonCurveComponent_of_no_common_infinite_factor
    {C₁ C₂ : Set Point2} {p q : MvPolynomial (Fin 2) ℝ}
    (_hp0 : p ≠ 0) (_hq0 : q ≠ 0)
    (hC₁ : C₁ = PlaneCurveZeroSet p)
    (hC₂ : C₂ = PlaneCurveZeroSet q)
    (hno : NoCommonCurveComponent C₁ C₂) :
    ¬ HasCommonInfiniteIrreducibleFactor p q := by
  intro hcommon
  rcases hcommon with ⟨h, hirr, hinf, hp, hq⟩
  have hh0 : h ≠ 0 := hirr.ne_zero
  have hcurve : PlaneCurve.IsIrreducibleCurve h.totalDegree (PlaneCurveZeroSet h) := by
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

/-- Fraction field of the coefficient ring used in the Bézout proof. -/
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
    ext i
    fin_cases i
    · simp [elimCoord, coeffCoord]
    · simp [elimCoord, coeffCoord]
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
  rw [Specialized0, ResultantCoeff, coeffEval]
  exact Polynomial.resultant_map_map (Curry0 p) (Curry0 q)
    (Curry0 p).natDegree (Curry0 q).natDegree (MvPolynomial.eval fun _ => x)

/-- A common zero gives a root of the coefficient resultant. -/
lemma resultant_vanishes_at_common_zero
    (p q : MvPolynomial (Fin 2) ℝ) {z : Point2}
    (hp0deg : 0 < (Curry0 p).natDegree)
    (_hq0deg : 0 < (Curry0 q).natDegree)
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
  · rcases IsLocalization.integerNormalization_spec (nonZeroDivisors XCoeff) D with
      ⟨b, hb, hnorm⟩
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
    simp [XCoeffEquiv, MvPolynomial.finSuccEquiv_apply]
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
      exact XCoeffEquiv.symm_apply_apply ((Curry0 p).coeff n)
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
    rw [Curry0]
    exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply p
  have hdiv_symm : CoeffLineFactor x ∣ (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) :=
    (map_dvd_iff_dvd_symm (MvPolynomial.finSuccEquiv ℝ 1)).1 hdiv_curry
  simpa [hsymm_curve] using hdiv_symm

/-- If both specializations vanish, the coefficient-line factor would be a common divisor. -/
theorem not_both_specializations_zero_of_isRelPrime
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (_hpprim : (Curry0 p).IsPrimitive)
    (_hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by
  by_cases hp : Specialized0 x p = 0
  · by_cases hq : Specialized0 x q = 0
    · have hpdvd : CoeffLineFactor x ∣ p :=
        coeffLineFactor_dvd_of_specialized_zero p x hp
      have hqdvd : CoeffLineFactor x ∣ q :=
        coeffLineFactor_dvd_of_specialized_zero q x hq
      have hsymm_p : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 p) = p := by
        rw [Curry0]
        exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply p
      have hsymm_q : (MvPolynomial.finSuccEquiv ℝ 1).symm (Curry0 q) = q := by
        rw [Curry0]
        exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply q
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
          rw [Curry0]
          exact (MvPolynomial.finSuccEquiv ℝ 1).symm_apply_apply (CoeffLineFactor x)
        simpa [hsymm_factor] using
          IsUnit.map (MvPolynomial.finSuccEquiv ℝ 1).symm hunit0
      have hneq : (fun₀ | (1 : Fin 2) => 1) ≠ (0 : (Fin 2 →₀ ℕ)) := by
        intro h
        have := congrArg (fun m => m (1 : Fin 2)) h
        simp at this
      have hcoeff :
          MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x) = 1 := by
        have hCcoeff :
            MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1)
              (MvPolynomial.C x) = 0 := by
          rw [MvPolynomial.coeff_C]
          split_ifs with h0
          · exfalso
            exact hneq h0.symm
          · rfl
        rw [CoeffLineFactor, MvPolynomial.coeff_sub]
        simp [hCcoeff]
      have hnil :
          IsNilpotent (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
        have hunit' := (MvPolynomial.isUnit_iff.mp hunit).2
        exact hunit' _ hneq
      have hcontr : False := by
        have hnot : ¬ IsNilpotent
            (MvPolynomial.coeff (fun₀ | (1 : Fin 2) => 1) (CoeffLineFactor x)) := by
          simp [hcoeff]
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
    (ha0 : a ≠ 0) (_hq0 : q ≠ 0)
    (hadeg : a.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (_hq0deg : 0 < (Curry0 q).natDegree)
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
      ext i
      fin_cases i
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
      ext i
      fin_cases i
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

/-- If the coefficient roots have empty intersection, the corresponding coefficient-line
intersections are empty. -/
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
      simp [hnoRoot] at hx
    exact False.elim hfalse
  · intro hz
    cases hz

/-- An irreducible plane polynomial with positive eliminated-coordinate degree has primitive
curry. -/
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
    have hCcoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1) (MvPolynomial.C x) = 0 := by
      rw [MvPolynomial.coeff_C]
      split_ifs with h0
      · exfalso
        exact hne h0.symm
      · rfl
    rw [CoeffLineFactor, MvPolynomial.coeff_sub]
    simp [hCcoeff]
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

/-- A coefficient-line factor cannot divide the second polynomial in the nonassociated
zero-degree case. -/
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
    cases hx

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
  refine ⟨by simp [hempty], ?_⟩
  simp [hempty]

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

/-- A partial derivative drops the total degree by at most one when the curve has positive
degree. -/
lemma totalDegree_pderiv_le_sub_one
    (h : MvPolynomial (Fin 2) ℝ) (i : Fin 2)
    (_hpos : 0 < h.totalDegree) :
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
    · simp [hvi]
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

/-- A nonzero partial derivative of a positive-degree plane polynomial has strictly smaller
degree. -/
lemma totalDegree_pderiv_lt_of_nonzero
    (h : MvPolynomial (Fin 2) ℝ) {i : Fin 2}
    (hpos : 0 < h.totalDegree)
    (_hpi : MvPolynomial.pderiv i h ≠ 0) :
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
      simp [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons] at ih' ⊢
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


/-- Bivariate real polynomials — the ambient ring for plane curves. -/
abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

/-- A finite cover of a real plane curve by irreducible components coming from its normalized
factors. -/
structure RealPlaneCurveComponentCover
    (d : ℕ) (C : Set Point2)
    (components : Finset (Sigma fun _e : ℕ => Set Point2)) : Prop where
  cover :
    C = ⋃ component ∈ components, component.2
  each_irreducible :
    ∀ component, component ∈ components →
      PlaneCurve.IsIrreducibleCurve component.1 component.2
  each_degree_pos :
    ∀ component, component ∈ components → 0 < component.1
  each_degree_le :
    ∀ component, component ∈ components → component.1 ≤ d
  card_le_degree :
    components.card ≤ d

/-- Every bounded-degree real plane curve admits a finite cover by irreducible factor curves. -/
theorem boundedDegreeCurve_real_component_cover
    {d : ℕ} {C : Set Point2}
    (hC : PlaneCurve.IsBoundedDegreeCurve d C) :
    ∃ components : Finset (Sigma fun _e : ℕ => Set Point2),
      RealPlaneCurveComponentCover d C components := by
  classical
  rcases hC with ⟨p, hp0, hpdeg, hC⟩
  let factors : Finset PlanePoly := (UniqueFactorizationMonoid.normalizedFactors p).toFinset
  let components : Finset (Sigma fun _e : ℕ => Set Point2) :=
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




/-- A real degree-four curve together with its finite irreducible component cover. -/
structure DegreeFourIrreducibleComponentCover (C : Set Point2) where
  components : Finset (Sigma fun _e : ℕ => Set Point2)
  cover : RealPlaneCurveComponentCover 4 C components

/-- Extract the degree-four real component cover from a bounded-degree curve. -/
noncomputable def degreeFourIrreducibleComponentCover_of_boundedDegreeCurve
    {C : Set Point2} (hC : PlaneCurve.IsBoundedDegreeCurve 4 C) :
    DegreeFourIrreducibleComponentCover C := by
  classical
  let witness := boundedDegreeCurve_real_component_cover (d := 4) (C := C) hC
  refine ⟨Classical.choose witness, Classical.choose_spec witness⟩



end PachDeZeeuw.Algebraic
