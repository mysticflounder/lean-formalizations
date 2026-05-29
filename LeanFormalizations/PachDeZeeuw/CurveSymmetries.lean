/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Symmetries of plane algebraic curves

Formalization of **§2.3 ("Symmetries of curves")** of Pach–de Zeeuw, "Distinct
distances on algebraic curves in the plane":

* **Lemma 2.5.** An irreducible plane algebraic curve of degree `d` has at most
  `4d` symmetries (isometries of `ℝ²` that fix it), unless it is a line or a
  circle.
* **Lemma 2.6.** The affine transformations that fix a conic, classified up to a
  rotation or translation (the hyperbola / ellipse / parabola normal forms).

These feed §4: Lemma 2.5 gives `|Γ₀| ≤ 4dm` in the symmetry branch of Lemma 3.2,
and Lemma 2.6 drives the conic case of Lemma 4.3. Lemma 2.5's proof invokes
Bézout's inequality (Theorem 2.1, from the sibling `bezout` module): a symmetry
fixing infinitely many points of an irreducible curve must fix the curve.

This file fixes the **statement surface** of §2.3: the isometry/affine and conic
vocabulary, `Lemma25Statement` (≤ `4d` symmetries) and `Lemma26Statement` (the
conic-stabilizer normal-form classification), defined locally (Mathlib-only; the
`bezout` dependency is for the eventual *proofs*, which invoke Theorem 2.1). The
discharging terms are deferred — these `Prop`s are the named interfaces §4
threads through.
-/

set_option linter.style.longLine false

namespace CurveSymmetries

open scoped Classical

/-- The Euclidean plane. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- The real zero set `Z_ℝ(p)` of `p ∈ ℝ[x, y]` in the plane (Pach–de Zeeuw,
§2.1). -/
def PlaneCurveZeroSet (p : MvPolynomial (Fin 2) ℝ) : Set Point2 :=
  {x | MvPolynomial.eval (fun i => x i) p = 0}

/-- An irreducible plane algebraic curve of degree `≤ d`: `Z_ℝ(f)` for an
irreducible nonzero `f` of total degree `≤ d` (Pach–de Zeeuw, §2.1). -/
def IsIrreducibleCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧ Irreducible f ∧
    C = PlaneCurveZeroSet f

/-- `C` is a line or a circle — the configuration Lemma 2.5 excludes. -/
def IsLineOrCircle (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧ C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ center : Point2, ∃ r : ℝ, C = Metric.sphere center r)

/--
**Lemma 2.5.**

An irreducible plane algebraic curve of degree `d` has at most `4d` symmetries
(isometries `g` of `ℝ²` with `g(C) = C`), unless it is a line or a circle
(Pach–de Zeeuw, Lemma 2.5).

Encoded so no finiteness precondition is needed: *every* finite set of symmetries
has at most `4d` elements, which says the symmetry group has order `≤ 4d`. -/
def Lemma25Statement : Prop :=
  ∀ (d : ℕ) (C : Set Point2),
    IsIrreducibleCurve d C →
    ¬ IsLineOrCircle C →
    ∀ symmetries : Finset (Point2 ≃ᵢ Point2),
      (∀ g ∈ symmetries, g '' C = C) →
        symmetries.card ≤ 4 * d

/- ## Conic normal-form surface (Lemma 2.6) -/

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
    · simp [mul_comm, mul_left_comm, mul_assoc]
    · simp [mul_comm, mul_left_comm, mul_assoc] }

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
      · simp [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc]
      · simp [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc])
    (by
      ext x i
      fin_cases i
      · simp [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc]
      · simp [point2DiagLinearMap, ha, hb, mul_comm, mul_left_comm, mul_assoc])

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
      · simp [point2ShearLinearMap, add_comm])
    (by
      ext x i
      fin_cases i
      · simp [point2ShearLinearMap]
      · simp [point2ShearLinearMap, add_comm])

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

/-- Normal-form data for an irreducible conic: an affine equivalence carrying `C`
to one of the three standard model sets. -/
structure ConicNormalFormData (C : Set Point2) where
  model : ConicModel
  e : Point2 ≃ᵃ[ℝ] Point2
  image_eq : e '' C = ConicModelSet model

/-- The standard hyperbola scaling map. -/
noncomputable def RectHyperbolaScale (a : ℝ) (ha : a ≠ 0) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  AffineEquiv.ofLinearEquiv
    (point2DiagLinearEquiv a a⁻¹ ha (inv_ne_zero ha)) 0 0

/-- The standard hyperbola scaling-plus-swap map. -/
noncomputable def RectHyperbolaSwapScale (a : ℝ) (ha : a ≠ 0) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  AffineEquiv.ofLinearEquiv
    ((point2SwapLinearEquiv).trans
      (point2DiagLinearEquiv a a⁻¹ ha (inv_ne_zero ha))) 0 0

/-- The standard parabola affine map. -/
noncomputable def StandardParabolaMap (a b : ℝ) (ha : a ≠ 0) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  AffineEquiv.ofLinearEquiv
    ((point2DiagLinearEquiv a (a ^ 2) ha (pow_ne_zero 2 ha)).trans
      (point2ShearLinearEquiv (2 * b))) 0
    (show Point2 from !₂[(b : ℝ), b ^ 2])

/-- The ellipse-model stabilizers are exactly the Euclidean isometries fixing the
center. -/
def EllipseModelStabilizer (T : Point2 ≃ᵃ[ℝ] Point2) : Prop :=
  ∃ g : Point2 ≃ᵢ Point2,
    g 0 = 0 ∧
    T = g.toRealAffineIsometryEquiv.toAffineEquiv

/-- The hyperbola-model stabilizers are the explicit scaling and swapping maps. -/
def HyperbolaModelStabilizer (T : Point2 ≃ᵃ[ℝ] Point2) : Prop :=
  ∃ a : ℝ, ∃ ha : a ≠ 0,
    (T = RectHyperbolaScale a ha ∨ T = RectHyperbolaSwapScale a ha)

/-- The parabola-model stabilizers are the explicit affine parabolic maps. -/
def ParabolaModelStabilizer (T : Point2 ≃ᵃ[ℝ] Point2) : Prop :=
  ∃ a b : ℝ, ∃ ha : a ≠ 0,
    T = StandardParabolaMap a b ha

/-- The stabilizer predicate attached to a chosen conic model. -/
def ModelConicStabilizer : ConicModel → (Point2 ≃ᵃ[ℝ] Point2) → Prop
  | .ellipse, T => EllipseModelStabilizer T
  | .hyperbola, T => HyperbolaModelStabilizer T
  | .parabola, T => ParabolaModelStabilizer T

/-- Conjugate an affine map by the normal-form equivalence. -/
noncomputable def conjugateAffine
    (e T : Point2 ≃ᵃ[ℝ] Point2) : Point2 ≃ᵃ[ℝ] Point2 :=
  e.trans (T.trans e.symm)

/-- A conic equipped with its normal-form classification data: an affine
equivalence `e` to a standard model, such that every affine map fixing `C`
becomes, after conjugation by `e`, one of the explicit model stabilizers. -/
structure ConicStabilizerNormalForm (C : Set Point2) where
  data : ConicNormalFormData C
  stabilizer_classified :
    ∀ T : Point2 ≃ᵃ[ℝ] Point2,
      T '' C = C →
        ModelConicStabilizer data.model (conjugateAffine data.e T)

/-- An irreducible conic: the (infinite) zero set of an irreducible degree-`2`
polynomial (Pach–de Zeeuw, used in Lemma 4.3). -/
def IsIrreducibleConic (C : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ,
    p ≠ 0 ∧ p.totalDegree = 2 ∧ Irreducible p ∧
      C = PlaneCurveZeroSet p ∧ C.Infinite

/--
**Lemma 2.6.**

The affine transformations that fix an irreducible conic `C`, classified up to a
rotation or translation: there is a normal-form equivalence to one of the
ellipse / hyperbola / parabola models under which every conic-fixing affine map
is one of the explicit model stabilizers (Pach–de Zeeuw, Lemma 2.6). -/
def Lemma26Statement : Prop :=
  ∀ C : Set Point2,
    IsIrreducibleConic C →
      Nonempty (ConicStabilizerNormalForm C)

end CurveSymmetries
