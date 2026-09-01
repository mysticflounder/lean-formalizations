/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Elekes-Sharir distinct-distances program -- comparator solution module

This file discharges every `sorry` stub in this directory's `Challenge.lean` by
importing the full project (`import LeanFormalizations`) and inhabiting each
headline statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` -- same `Headline.` name, identical statement -- and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and re-checks
it under both the `nanoda` kernel and the Lean default kernel.

## Contents

The Elekes-Sharir distinct-distances program, in the three layers the project
formalizes. They are gated as one entry because they are one argument: the
linear-algebra core is machinery for the geometric core, which in turn feeds the
Elekes-Sharir-Guth-Katz base layer.

* Generic linear-algebra core: rank-nullity for a functional, the two-dimensional
  kernel consequence, pullback non-degeneracy, and the orthogonal-matrix
  quadratic-form identities.
* Geometric core: `dist2`, `J`, `esLine`, `Intersect`, `Parallel`,
  `IsDist2Preserving` and `PairwiseSkewRuling` inlined to their mathlib bodies --
  the two-pinned determinant, the squared-distance intersection criterion, and
  the isometry-graph exclusions.
* Elekes-Sharir-Guth-Katz base layer: `Config`, `OrderedMultiplicity`,
  `DistanceEnergy`, `Richness`, `IsDirect`, `InGeneralPosition` and `hIndexed`
  inlined, ending in the rich-isometry-family decomposition.

## Scope

See `config.json` in this directory for the `theorem_names` list and the permitted
axiom set, and `comparator/README.md` for the audit boundary across all nine
per-formalization configurations.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── Elekes–Sharir generic linear-algebra core (ElekesSharir) ───────────────

theorem finrank_ker_functional_ge {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K) :
    Module.finrank K W - 1 ≤ Module.finrank K (LinearMap.ker ω) :=
  ElekesSharir.finrank_ker_functional_ge ω

theorem finrank_ker_ge_two_of_finrank_eq_three {K : Type*} {W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K)
    (h : Module.finrank K W = 3) :
    2 ≤ Module.finrank K (LinearMap.ker ω) :=
  ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three ω h

theorem pullback_nondegenerate {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {A : Type*} [AddCommGroup A] [Module K A] (pull : W →ₗ[K] A)
    (hpull : Function.Injective pull) {ℓ : W} (hℓ : ℓ ≠ 0) :
    pull ℓ ≠ 0 :=
  ElekesSharir.pullback_nondegenerate pull hpull hℓ

theorem quadraticPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) :
    A.mulVec p ⬝ᵥ A.mulVec p - p ⬝ᵥ p = p ⬝ᵥ (A.transpose * A - 1).mulVec p :=
  ElekesSharir.quadraticPart_eq A p

theorem dotProduct_mulVec_self_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.transpose = M) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ M.mulVec p = 0) ↔ M = 0 :=
  ElekesSharir.dotProduct_mulVec_self_eq_zero_iff hM

theorem quadraticPart_vanishes_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ (A.transpose * A - 1).mulVec p = 0) ↔ A.transpose * A = 1 :=
  ElekesSharir.quadraticPart_vanishes_iff A

-- ── Elekes–Sharir geometric core ────────────────────────────────────────────

theorem twoPinnedDet_affine (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        - 2 * (a₁.1 * w.2 - a₁.2 * w.1)
        - 2 * (w.1 * a₂.2 - w.2 * a₂.1) :=
  ElekesSharir.twoPinnedDet_affine a₁ a₂ w

theorem twoPinnedDet_eq_const_add_linear (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        + (- 2 * (a₁.1 - a₂.1) * w.2 + 2 * (a₁.2 - a₂.2) * w.1) :=
  ElekesSharir.twoPinnedDet_eq_const_add_linear a₁ a₂ w

theorem intersect_or_parallel_of_dist2_eq {p q p' q' : ℝ × ℝ}
    (h : (p.1 - p'.1) ^ 2 + (p.2 - p'.2) ^ 2 = (q.1 - q'.1) ^ 2 + (q.2 - q'.2) ^ 2) :
    (∃ t s : ℝ,
      (((p.1 + q.1) / 2 + (t / 2) * (-(q - p).2, (q - p).1).1,
        (p.2 + q.2) / 2 + (t / 2) * (-(q - p).2, (q - p).1).2), t)
        = (((p'.1 + q'.1) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).1,
            (p'.2 + q'.2) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).2), s))
    ∨ (-(q - p).2, (q - p).1) = (-(q' - p').2, (q' - p').1) :=
  ElekesSharir.intersect_or_parallel_of_dist2_eq (p := p) (q := q) (p' := p') (q' := q') h

theorem intersect_or_parallel_of_isometryGraph {g : ℝ × ℝ → ℝ × ℝ}
    (hg : ∀ x y : ℝ × ℝ,
        ((g x).1 - (g y).1) ^ 2 + ((g x).2 - (g y).2) ^ 2
          = (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
    (p p' : ℝ × ℝ) :
    (∃ t s : ℝ,
      (((p.1 + (g p).1) / 2 + (t / 2) * (-((g p) - p).2, ((g p) - p).1).1,
        (p.2 + (g p).2) / 2 + (t / 2) * (-((g p) - p).2, ((g p) - p).1).2), t)
        = (((p'.1 + (g p').1) / 2 + (s / 2) * (-((g p') - p').2, ((g p') - p').1).1,
            (p'.2 + (g p').2) / 2 + (s / 2) * (-((g p') - p').2, ((g p') - p').1).2), s))
    ∨ (-((g p) - p).2, ((g p) - p).1) = (-((g p') - p').2, ((g p') - p').1) :=
  ElekesSharir.intersect_or_parallel_of_isometryGraph hg p p'

theorem atMostOneLine_of_skewRuling_isometryGraph {g : ℝ × ℝ → ℝ × ℝ}
    (hg : ∀ x y : ℝ × ℝ,
        ((g x).1 - (g y).1) ^ 2 + ((g x).2 - (g y).2) ^ 2
          = (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
    {S : Set ((ℝ × ℝ) × (ℝ × ℝ))}
    (hskew : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (¬ ∃ t s : ℝ,
        (((x.1.1 + x.2.1) / 2 + (t / 2) * (-(x.2 - x.1).2, (x.2 - x.1).1).1,
          (x.1.2 + x.2.2) / 2 + (t / 2) * (-(x.2 - x.1).2, (x.2 - x.1).1).2), t)
          = (((y.1.1 + y.2.1) / 2 + (s / 2) * (-(y.2 - y.1).2, (y.2 - y.1).1).1,
              (y.1.2 + y.2.2) / 2 + (s / 2) * (-(y.2 - y.1).2, (y.2 - y.1).1).2), s))
      ∧ ¬ ((-(x.2 - x.1).2, (x.2 - x.1).1) = (-(y.2 - y.1).2, (y.2 - y.1).1)))
    (hgraph : ∀ x ∈ S, x.2 = g x.1) :
    S.Subsingleton :=
  ElekesSharir.atMostOneLine_of_skewRuling_isometryGraph hg hskew hgraph

-- ── Elekes–Sharir–Guth–Katz base layer ──────────────────────────────────────

theorem energy_lower_bound_of_few_distances {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ (Fin 2)) :
    (n * (n - 1)) ^ 2 ≤
      (Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2))).card
        * (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
              ((Finset.univ.product Finset.univ).filter
                (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
            ((Finset.univ.product Finset.univ).filter
                (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2) :=
  Esgk.energy_lower_bound_of_few_distances p

theorem gp_config_nonempty :
    ∀ n : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :=
  Esgk.gp_config_nonempty

theorem orderedMultiplicity_le_three_mul {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T))
    (r : ℝ) :
    ((Finset.univ.product Finset.univ).filter
        (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ≤ 3 * n :=
  Esgk.orderedMultiplicity_le_three_mul hp hgp r

theorem distanceEnergy_le_three_mul_cube {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :
    (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
        ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2)
      ≤ 3 * n ^ 3 :=
  Esgk.distanceEnergy_le_three_mul_cube hp hgp

theorem numDistances_ge_of_ceiling {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :
    (n * (n - 1)) ^ 2 ≤ 3 * n ^ 3 *
      ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card :=
  Esgk.numDistances_ge_of_ceiling hp hgp

theorem all_configs_lower_bound_to_hIndexed_lower_bound {n : ℕ} {B : ℕ}
    (hB : ∀ p : Fin n → EuclideanSpace ℝ (Fin 2), Function.Injective p →
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) →
      B ≤ ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card) :
    B ≤ sInf {k : ℕ | ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) ∧
      k = ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card} :=
  Esgk.all_configs_lower_bound_to_hIndexed_lower_bound hB

theorem distanceEnergy_eq_sum_energyAtLevel {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    (isoms : Finset (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)))
    (hisoms :
      (∀ g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
          0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
              EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
          2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card →
          g ∈ isoms) ∧
        (∀ g ∈ isoms,
          0 < (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) ∧
        (∀ g ∈ isoms,
          0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
              EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
          2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card)) :
    (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
        ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2)
      = ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          ∑ g ∈ isoms.filter (fun g =>
              0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                  EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∧
              2 ^ k ≤ (Finset.univ.filter fun i : Fin n =>
                  g (p i) ∈ Finset.image p Finset.univ).card ∧
              (Finset.univ.filter fun i : Fin n =>
                  g (p i) ∈ Finset.image p Finset.univ).card < 2 ^ (k + 1)),
            (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card *
              ((Finset.univ.filter fun i : Fin n =>
                g (p i) ∈ Finset.image p Finset.univ).card - 1) :=
  Esgk.distanceEnergy_eq_sum_energyAtLevel p hp isoms hisoms

theorem elekes_sharir_guth_katz_decomposition :
    ∀ n : ℕ, ∀ p : Fin n → EuclideanSpace ℝ (Fin 2), Function.Injective p →
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) →
      ∃ isoms : Finset (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)),
        (∀ g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
            0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
            2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card →
            g ∈ isoms) ∧
          (∀ g ∈ isoms,
            0 < (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) ∧
          (∀ g ∈ isoms,
            0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
            2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) :=
  Esgk.elekes_sharir_guth_katz_decomposition

end Headline
