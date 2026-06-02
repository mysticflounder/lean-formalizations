/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Theorem 2.3 / Corollary 2.4 — the Pach–Sharir incidence bound

The Pach–Sharir incidence bound, stated **exactly as in the paper** (Pach–de
Zeeuw, "Distinct distances on algebraic curves in the plane," Theorem 2.3 and its
`ℝ^D` variant Corollary 2.4).

These are verbatim paper statements: real-valued bound with the `2/3` exponents,
the constant `C_{d,M}` (resp. `C_{D,e,d,M}`) depending only on the stated
parameters, algebraic curves of the degrees the paper specifies, and the paper's
own definition of a *system with two degrees of freedom and multiplicity `M`*
(two curves meet in at most `M` points of the ambient space; any two points lie
on at most `M` curves). No reformulation is folded in here — the cubed-integer
restatement, the `D = 4` instantiation, and the reduction to the `pdz`-internal
incidence-card statement are project wiring that lives in the `pdz` adapter, not
in this paper-faithful module.

Both statements are currently supplied with a `sorry` (**Gap A**): the
crossing-lemma → Szemerédi–Trotter → Pach–Sharir chain is not yet formalized. The
holes are isolated to `theorem23` and `corollary24`.
-/

set_option linter.style.longLine false

namespace PachSharir

open scoped Classical

/-- `|I(P, Γ)|`: the number of incidences, i.e. pairs `(p, γ) ∈ P × Γ` with
`p ∈ γ`. A curve is its set of points; incidence is membership. -/
noncomputable def incidenceCount {α : Type*} (P : Finset α) (Γ : Finset (Set α)) : ℕ :=
  ((P ×ˢ Γ).filter (fun pγ => pγ.1 ∈ pγ.2)).card

/-- `P` and `Γ` form a *system with two degrees of freedom and multiplicity `M`*
(Pach–de Zeeuw, definition preceding Theorem 2.3, with `k = 2`): any two distinct
curves intersect in at most `M` points of the ambient space, and any two distinct
points of `P` lie on at most `M` curves of `Γ`. -/
def TwoDegreesOfFreedom {α : Type*} (P : Finset α) (Γ : Finset (Set α)) (M : ℕ) : Prop :=
  (∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → (γ₁ ∩ γ₂).encard ≤ (M : ℕ∞)) ∧
  (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
      (Γ.filter (fun γ => p₁ ∈ γ ∧ p₂ ∈ γ)).card ≤ M)

/-- The paper's right-hand side `max{|P|^{2/3} |Γ|^{2/3}, |P|, |Γ|}`. -/
noncomputable def incidenceBoundTerm {α : Type*} (P : Finset α) (Γ : Finset (Set α)) : ℝ :=
  max (max ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3))
        (P.card : ℝ)) (Γ.card : ℝ)

/-- A plane algebraic curve of degree at most `d`: the real zero set of a nonzero
`f ∈ ℝ[x, y]` of total degree `≤ d` (Pach–de Zeeuw, §2.1). -/
def IsPlaneAlgebraicCurveOfDegreeLE (d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧
    γ = {x | MvPolynomial.eval (fun i => x i) f = 0}

/-- A real algebraic curve in `ℝ^D` defined by `e` polynomials of degree at most
`d` (Pach–de Zeeuw, Corollary 2.4): the common real zero set of `e` polynomials
in `D` variables, each of total degree `≤ d`. -/
def IsAlgebraicCurveDefinedBy (D e d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin D))) : Prop :=
  ∃ fs : Fin e → MvPolynomial (Fin D) ℝ, (∀ i, (fs i).totalDegree ≤ d) ∧
    γ = {x | ∀ i, MvPolynomial.eval (fun k => x k) (fs i) = 0}

/--
**Theorem 2.3 (Pach–Sharir).**

If a set `P` of points in `ℝ²` and a set `Γ` of algebraic curves in `ℝ²` of degree
at most `d` form a system with two degrees of freedom and multiplicity `M`, then
`|I(P, Γ)| ≤ C_{d,M} · max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}`, where `C_{d,M}` depends
only on `d` and `M`.
-/
def Theorem23Statement : Prop :=
  ∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ γ ∈ Γ, IsPlaneAlgebraicCurveOfDegreeLE d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ

/--
**Corollary 2.4.**

If a set `P` of points in `ℝ^D` and a set `Γ` of real algebraic curves in `ℝ^D`,
each defined by `e` polynomials of degree at most `d`, form a system with two
degrees of freedom and multiplicity `M`, then
`|I(P, Γ)| ≤ C_{D,e,d,M} · max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}`, where `C_{D,e,d,M}`
depends only on `D`, `e`, `d`, and `M`.
-/
def Corollary24Statement : Prop :=
  ∀ D e d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin D)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin D)))),
      (∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ

/-- **Theorem 2.3.** Gap A — supplied by `sorry` pending the crossing-lemma →
Szemerédi–Trotter → Pach–Sharir formalization. -/
theorem theorem23 : Theorem23Statement :=
  sorry

/-- **Corollary 2.4.** Gap A — the `ℝ^D` generic-projection consequence of
`theorem23`, also pending formalization. -/
theorem corollary24 : Corollary24Statement :=
  sorry

end PachSharir
