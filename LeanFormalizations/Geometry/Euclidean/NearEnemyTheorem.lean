/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Near Enemy Theorem for Bisector Energy

The **Near Enemy Theorem for Bisector Energy** is the official project name for
the bisector-energy theorem about the Erdos-Furedi-Pach-Ruzsa lattice
sphere-slice construction under a generic planar projection.

In prose, the near enemy is the finite set

`G' = {x in [-h, h]^d cap Z^d : |x|^2 = R}`

after applying a projection `T : R^d -> R^2` chosen generically enough to avoid
accidental finite coincidences. The sphere slice gives the upstairs line
rigidity: a line meets the sphere in at most two points. The generic planar
projection realizes the construction in the plane while preserving the finite
coincidence pattern relevant to the theorem.

The theorem is specifically about the **bisector-energy channel**, not the full
distinct-distances problem. Its conclusion is that generic planar projections
of the near enemy attain the absolute minimum possible bisector energy: every
unordered point-pair has a distinct perpendicular bisector.

The public theorem name is:

`Near Enemy Theorem for Bisector Energy`

The intended Lean theorem name is:

`nearEnemy_genericProjection_bisectorEnergy_minimal`

Intended supporting names:

* `nearEnemySphereSlice`
* `nearEnemyProjectionGeneric`
* `nearEnemy_sharedBisector_forces_samePair`
* `nearEnemy_bisectors_injective_on_unorderedPairs`
* `nearEnemy_genericProjection_bisectorEnergy_eq_pairCount`

Mathematical content currently in this module, in proof-pipeline order:

1. **Generic-projection algebra** (the identical-vanishing characterizations
   that the genericity wrapper consumes, in `∀`-instantiation form):
   * `eq_zero_of_forall_inner_mul_inner_eq_zero` — the coefficient lemma: if
     `⟪r, m⟫ * ⟪r, v⟫ = 0` for every row vector `r` and `v ≠ 0`, then `m = 0`.
     Downstairs this is the midpoint step: a shared bisector forces, for every
     admissible projection row, the orthogonality polynomial to vanish, and
     identical vanishing forces equal midpoints upstairs.
   * `exists_smul_eq_of_forall_inner_det_eq_zero` — the parallelism step: if
     the projected `2×2` determinant `⟪p, v⟫⟪q, w⟫ - ⟪p, w⟫⟪q, v⟫` vanishes
     for all row vectors `p, q`, the difference vectors are dependent
     upstairs (Cauchy–Binet in instantiation form, no Cauchy–Schwarz
     equality case needed).
   * `eq_or_eq_neg_of_forall_inner_sub_mul_inner_add` — distance-class
     separation: `‖Tv‖² - ‖Tw‖² = Σ_k ⟪T_k, v-w⟫⟪T_k, v+w⟫`, so identical
     vanishing forces `w = ±v`; distinct `±`-difference classes stay
     separated under generic projection. (This is also the algebraic core of
     the companion zero-rotation-energy statement for the same family: with
     all `±`-classes separated, every congruent quadruple downstairs is a
     translation or half-turn.)
2. **Upstairs sphere rigidity**:
   * `sphereSlice_chordLength_sq_eq_of_same_midpoint` — chords of one sphere
     with a common midpoint have equal length (parallelogram law).
   * `nearEnemy_sphereSlice_parallel_midpoint_eq_samePair` — two chords of
     one sphere with the same midpoint and parallel differences are the same
     unordered pair: the upstairs geometric core of the theorem.

The genericity wrapper itself (a polynomial in the projection entries that is
not identically zero vanishes only on finitely many proper hypersurfaces,
which a generic integer matrix avoids) remains pen-and-paper; the lemmas above
are exactly the identical-vanishing characterizations it consumes. The
remaining stages are the generic-projection shared-bisector criterion and the
bisector-injectivity / energy-minimality statements.
-/

open scoped RealInnerProductSpace

namespace NearEnemy

/-! ## Generic-projection algebra -/

section GenericProjectionAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Coefficient lemma**, instantiation form: if `⟪r, m⟫ * ⟪r, v⟫ = 0` for
every `r`, and `v ≠ 0`, then `m = 0`.  The two instantiations `r := v` and
`r := m + v` replace the polynomial coefficient extraction of the prose
proof. -/
theorem eq_zero_of_forall_inner_mul_inner_eq_zero {m v : V} (hv : v ≠ 0)
    (h : ∀ r : V, ⟪r, m⟫ * ⟪r, v⟫ = 0) : m = 0 := by
  have hvv : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.mpr hv
  have hvm : ⟪v, m⟫ = 0 := by
    rcases mul_eq_zero.mp (h v) with h' | h'
    · exact h'
    · exact absurd h' hvv
  have hmv : ⟪m, v⟫ = 0 := by rw [real_inner_comm]; exact hvm
  have hmm : ⟪m, m⟫ = 0 := by
    have hmv' := h (m + v)
    rw [inner_add_left, inner_add_left, hvm, hmv, add_zero, zero_add] at hmv'
    rcases mul_eq_zero.mp hmv' with h' | h'
    · exact h'
    · exact absurd h' hvv
  exact inner_self_eq_zero.mp hmm

/-- **Distance-class separation**: if `⟪r, v - w⟫ * ⟪r, v + w⟫ = 0` for every
`r`, then `w = v` or `w = -v`.  Downstairs,
`‖Tv‖² - ‖Tw‖² = Σ_k ⟪T_k, v-w⟫⟪T_k, v+w⟫`; identical vanishing of each
summand is what a projection equating two distance classes would force, so
distinct `±`-classes stay separated generically. -/
theorem eq_or_eq_neg_of_forall_inner_sub_mul_inner_add {v w : V}
    (h : ∀ r : V, ⟪r, v - w⟫ * ⟪r, v + w⟫ = 0) : w = v ∨ w = -v := by
  by_cases hvw : v + w = 0
  · exact Or.inr (eq_neg_of_add_eq_zero_left (by rwa [add_comm] at hvw))
  · left
    have := eq_zero_of_forall_inner_mul_inner_eq_zero hvw h
    rw [sub_eq_zero] at this
    exact this.symm

/-- **Parallelism lemma** (Cauchy–Binet step in instantiation form): if the
`2×2` "projected determinant" `⟪p, v⟫⟪q, w⟫ - ⟪p, w⟫⟪q, v⟫` vanishes for ALL
row vectors `p, q`, then `v` and `w` are linearly dependent.  Proved without
the Cauchy–Schwarz equality case, via the Gram–Schmidt vector
`u := ⟪v,v⟫ • w - ⟪v,w⟫ • v`. -/
theorem exists_smul_eq_of_forall_inner_det_eq_zero {v w : V}
    (h : ∀ p q : V, ⟪p, v⟫ * ⟪q, w⟫ - ⟪p, w⟫ * ⟪q, v⟫ = 0) :
    (∃ t : ℝ, w = t • v) ∨ (∃ t : ℝ, v = t • w) := by
  by_cases hv : v = 0
  · exact Or.inr ⟨0, by simp [hv]⟩
  · left
    have hvv : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.mpr hv
    set u : V := ⟪v, v⟫ • w - ⟪v, w⟫ • v with hu
    have expand : ∀ x : V, ⟪x, u⟫ = ⟪v, v⟫ * ⟪x, w⟫ - ⟪v, w⟫ * ⟪x, v⟫ := by
      intro x
      rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    have huv : ⟪u, v⟫ = 0 := by
      rw [real_inner_comm, expand v]
      ring
    have huw : ⟪u, w⟫ = 0 := by
      have hpq := h v u
      rw [huv, mul_zero, sub_zero] at hpq
      rcases mul_eq_zero.mp hpq with h' | h'
      · exact absurd h' hvv
      · exact h'
    have huu : ⟪u, u⟫ = 0 := by
      rw [expand u, huv, huw, mul_zero, mul_zero, sub_zero]
    have hu0 : u = 0 := inner_self_eq_zero.mp huu
    rw [hu, sub_eq_zero] at hu0
    refine ⟨⟪v, v⟫⁻¹ * ⟪v, w⟫, ?_⟩
    rw [mul_smul, ← hu0, inv_smul_smul₀ hvv]

end GenericProjectionAlgebra

/-! ## Bisector vocabulary -/

/-- Set of points equidistant from `p` and `q`. This local definition keeps the
Near Enemy module self-contained. -/
def perpBisector (p q : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | dist x p = dist x q}

/-- Perpendicular bisectors are symmetric in their two endpoints. -/
@[simp] theorem perpBisector_comm (p q : EuclideanSpace ℝ (Fin 2)) :
    perpBisector p q = perpBisector q p := by
  ext x
  constructor <;> intro h <;> exact h.symm

open scoped Classical in
/-- Bisector energy of a finite planar point set: the number of ordered
quadruples of nondegenerate ordered pairs whose perpendicular bisectors
agree. -/
noncomputable def bisectorEnergy (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2).card

/-! ## Upstairs sphere rigidity -/

/-- Two chords of the same Euclidean sphere with the same midpoint have equal
chord length. This is the metric part of the sphere-slice rigidity argument. -/
theorem sphereSlice_chordLength_sq_eq_of_same_midpoint
    {ι : Type*} [Fintype ι]
    {a b c e center : EuclideanSpace ℝ ι} {R : ℝ}
    (ha : a ∈ Metric.sphere center R)
    (hb : b ∈ Metric.sphere center R)
    (hc : c ∈ Metric.sphere center R)
    (he : e ∈ Metric.sphere center R)
    (hmid : a + b = c + e) :
    ‖a - b‖ ^ 2 = ‖c - e‖ ^ 2 := by
  have haR : ‖a - center‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm, norm_sub_rev] using ha
  have hbR : ‖b - center‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm, norm_sub_rev] using hb
  have hcR : ‖c - center‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm, norm_sub_rev] using hc
  have heR : ‖e - center‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm, norm_sub_rev] using he
  have hsum : (a - center) + (b - center) = (c - center) + (e - center) := by
    calc
      (a - center) + (b - center) = a + b - (2 : ℝ) • center := by module
      _ = c + e - (2 : ℝ) • center := by rw [hmid]
      _ = (c - center) + (e - center) := by module
  have hdiff_ab : (a - center) - (b - center) = a - b := by module
  have hdiff_ce : (c - center) - (e - center) = c - e := by module
  have hpab := parallelogram_law_with_norm ℝ (a - center) (b - center)
  have hpce := parallelogram_law_with_norm ℝ (c - center) (e - center)
  rw [haR, hbR, hdiff_ab] at hpab
  rw [hcR, heR, hdiff_ce] at hpce
  rw [hsum] at hpab
  nlinarith

/-- Sphere-slice line rigidity for the Near Enemy Theorem for Bisector Energy.

If two chords of one Euclidean sphere have the same midpoint and parallel
difference vectors, then they are the same unordered pair. This is the upstairs
geometric core of the theorem: after the generic-projection algebra has forced
parallel differences and equal midpoints upstairs, the sphere permits no
distinct second chord on that line.
-/
theorem nearEnemy_sphereSlice_parallel_midpoint_eq_samePair
    {ι : Type*} [Fintype ι]
    {a b c e center : EuclideanSpace ℝ ι} {R : ℝ}
    (ha : a ∈ Metric.sphere center R)
    (hb : b ∈ Metric.sphere center R)
    (hc : c ∈ Metric.sphere center R)
    (he : e ∈ Metric.sphere center R)
    (hmid : a + b = c + e)
    (hpar : ∃ t : ℝ, c - e = t • (a - b)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) =
      ({c, e} : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨t, ht⟩ := hpar
  have htwo : (2 : ℝ) ≠ 0 := two_ne_zero
  by_cases hab : a = b
  · -- Degenerate chord: the parallel hypothesis collapses `c = e`, and the
    -- shared midpoint then collapses everything to one point.
    subst hab
    have hce : c = e := by simpa [sub_eq_zero] using ht
    subst hce
    have hca : c = a := by
      refine smul_right_injective (EuclideanSpace ℝ ι) htwo ?_
      calc (2 : ℝ) • c = c + c := two_smul ℝ c
        _ = a + a := hmid.symm
        _ = (2 : ℝ) • a := (two_smul ℝ a).symm
    rw [hca]
  · -- Nondegenerate chord: equal midpoints force equal chord lengths, so the
    -- parallelism scalar satisfies `t ^ 2 = 1`, i.e. `t = 1` or `t = -1`.
    have hlen := sphereSlice_chordLength_sq_eq_of_same_midpoint ha hb hc he hmid
    have habn : ‖a - b‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab))
    have ht2 : t ^ 2 = 1 := by
      have hce2 : ‖c - e‖ ^ 2 = t ^ 2 * ‖a - b‖ ^ 2 := by
        rw [ht, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hmul : t ^ 2 * ‖a - b‖ ^ 2 = 1 * ‖a - b‖ ^ 2 := by
        rw [one_mul, ← hce2, ← hlen]
      exact mul_right_cancel₀ habn hmul
    have hcases : t = 1 ∨ t = -1 := by
      have h0 : (t - 1) * (t + 1) = 0 := by linear_combination ht2
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcases with h1 | h1
    · -- `t = 1`: same difference and same sum give `(c, e) = (a, b)`.
      subst h1
      rw [one_smul] at ht
      have hca : c = a := by
        refine smul_right_injective (EuclideanSpace ℝ ι) htwo ?_
        calc (2 : ℝ) • c = (c - e) + (c + e) := by module
          _ = (a - b) + (a + b) := by rw [ht, ← hmid]
          _ = (2 : ℝ) • a := by module
      have heb : e = b := by
        have h := hmid
        rw [hca] at h
        exact (add_left_cancel h).symm
      rw [hca, heb]
    · -- `t = -1`: opposite difference and same sum give `(c, e) = (b, a)`.
      subst h1
      have hcb : c = b := by
        refine smul_right_injective (EuclideanSpace ℝ ι) htwo ?_
        calc (2 : ℝ) • c = (c - e) + (c + e) := by module
          _ = (-1 : ℝ) • (a - b) + (a + b) := by rw [ht, ← hmid]
          _ = (2 : ℝ) • b := by module
      have hea : e = a := by
        have h : b + a = b + e := by rw [add_comm b a, hmid, hcb]
        exact (add_left_cancel h).symm
      rw [hcb, hea]
      exact Set.pair_comm a b

end NearEnemy
