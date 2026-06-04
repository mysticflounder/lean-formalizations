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

The headline Lean theorems (unconditional, complete) are:

* `nearEnemy_exists_bisectorEnergy_minimal_image_generalPosition` — **the
  strongest form**: every finite set with no three collinear points and
  every four points affinely independent admits an injective planar
  projection realizing both the exact count `2n(n−1)` and absolute
  minimality among planar sets of the same size, whose image is in full
  planar general position: no three collinear AND no four concyclic.
* `nearEnemy_exists_bisectorEnergy_minimal_image_noThreeCollinear` — under
  no-three-collinear alone: floor + minimality + image again has no three
  collinear points.
* `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal` — the same
  without the image-general-position clause.
* `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal` — the sphere-slice
  form, a corollary: a line meets a sphere in at most two points
  (`not_collinear_of_mem_sphere`), so sphere subsets have no three
  collinear points.
* `nearEnemy_exists_projection_image_rotationEnergy_zero` — the
  rotation-channel companion, with NO hypothesis at all: every finite set in
  any Euclidean space admits an injective planar projection whose image has
  zero rotational energy (`rotationEnergy`, the proper-rotation channel of
  the congruent-quadruple count) — every congruent quadruple of the image is
  translation or half-turn related.

Conditional forms (on the `ProjectionGeneric` interface):

* `nearEnemy_genericProjection_bisectorEnergy_eq_pairCount` — exact count
* `nearEnemy_genericProjection_bisectorEnergy_minimal` — absolute minimality

Supporting chain (all complete):

* `ProjectionGeneric` — the coincidence-avoidance interface
* `nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair` — upstairs
  general-position line rigidity (equal sums + parallel differences put all
  four points on one line)
* `not_collinear_of_mem_sphere` — sphere ⟹ no-three-collinear bridge
* `nearEnemy_offPair_not_both_vanish_of_rigid` — per-quadruple certificate,
  rigidity-parameterized core (sphere and general-position instantiations:
  `nearEnemy_offPair_not_both_vanish`,
  `nearEnemy_noThreeCollinear_offPair_not_both_vanish`)
* `sharedBisector_parallel_and_sum_orth` — downstairs translation
* `nearEnemy_sharedBisector_forces_samePair` — shared-bisector criterion
* `nearEnemy_bisectors_injective_on_unorderedPairs` — bisector injectivity
* `two_mul_pairCount_le_bisectorEnergy` — universal floor
* `bisectorEnergy_eq_of_bisectorInjective` — floor counting
* `exists_projectionGeneric_of_forall_offPair_witness` — existence of a
  generic projection, witness-parameterized core (`MvPolynomial`
  nonvanishing; `MvPolynomial.funext` used exactly once); instantiations
  `nearEnemy_noThreeCollinear_exists_projectionGeneric` and
  `nearEnemy_exists_projectionGeneric`
* `collinear_of_detPoly_eq_zero` — per-triple witness: an identically
  vanishing triple-determinant polynomial forces upstairs collinearity
* `nearEnemy_exists_projectionGeneric_preserving_noThreeCollinear` —
  existence with one more master-product factor family (a collinearity
  constraint polynomial per distinct triple): the generic projection also
  keeps every distinct triple non-collinear downstairs
* `circPoly` / `circPoly_ne_zero_of_affineIndependent` /
  `eval_circPoly_eq_zero_of_dist_eq` — the concyclicity constraint
  polynomial (`4×4` circle determinant in explicit cofactor form), its
  per-quadruple nonvanishing for affinely independent quadruples (via the
  parabola-determinant extraction along row scalings and a Vandermonde
  weight vector), and the downstairs circle bridge
* `nearEnemy_exists_projectionGeneric_image_generalPosition` — existence
  with both extra factor families: the image is in full planar general
  position (no three collinear, no four concyclic)
* `distClassPoly` / `distClassPoly_ne_zero` /
  `eval_distClassPoly_eq_zero_of_dist_eq` /
  `rotationEnergy_image_eq_zero` — the distance-class constraint polynomial
  `‖Tv‖² - ‖Tw‖²`, its unconditional per-pair nonvanishing for `w ≠ ±v`
  (via `eq_or_eq_neg_of_forall_inner_sub_mul_inner_add`), the downstairs
  distance bridge, and the rotation-channel vanishing of the image under
  full distance-class separation

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
     separated under generic projection. (This is the algebraic core of the
     zero-rotation-energy companion, now formalized: with all `±`-classes
     separated, every congruent quadruple downstairs is a translation or
     half-turn — `nearEnemy_exists_projection_image_rotationEnergy_zero`.)
2. **Upstairs line rigidity** (the geometric core, two forms):
   * `nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair` — two pairs
     with the same midpoint and parallel differences lie on one line, so a
     no-three-collinear hypothesis forces them to be the same unordered
     pair.  This is the form the headline consumes.
   * `sphereSlice_chordLength_sq_eq_of_same_midpoint` — chords of one sphere
     with a common midpoint have equal length (parallelogram law).
   * `nearEnemy_sphereSlice_parallel_midpoint_eq_samePair` — two chords of
     one sphere with the same midpoint and parallel differences are the same
     unordered pair: the original sphere-specific rigidity, kept as
     standalone content; the headline now reaches the sphere through
     `not_collinear_of_mem_sphere` instead.

The chain is complete: no stage remains, no `sorry` anywhere, and every
theorem depends only on the standard axioms
`[propext, Classical.choice, Quot.sound]`.
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

/-! ## Rotation vocabulary -/

open scoped Classical in
/-- Rotational energy (proper-rotation channel) of a finite planar point set:
the number of ordered congruent quadruples of nondegenerate ordered pairs
whose difference vectors are neither equal nor opposite.  A congruent
quadruple `(a, b, c, e)` (`a ≠ b`, `c ≠ e`, `dist a b = dist c e`) is
realized by a unique orientation-preserving isometry taking `(a, b)` to
`(c, e)`; that isometry is a translation iff `a - b = c - e`, a half-turn iff
`a - b = -(c - e)`, and a proper rotation (angle `∉ {0, π}`) otherwise — so
the channel split is decided by difference vectors alone, and this counts
the proper-rotation channel. -/
noncomputable def rotationEnergy (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
      q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
      q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)).card

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

/-! ## Upstairs general-position rigidity -/

/-- General-position line rigidity for the Near Enemy Theorem for Bisector
Energy: if no three of the points are collinear, two pairs with the same
midpoint and parallel difference vectors are the same unordered pair.

Equal sums and parallel differences place all four points on one line
through the common midpoint, so a no-three-collinear hypothesis on the
triple `{a, b, c}` is all the rigidity the argument needs.  This strictly
generalizes the sphere-slice rigidity: a line meets a sphere in at most two
points (`not_collinear_of_mem_sphere`). -/
theorem nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair
    {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hgp : a ≠ b → c ≠ a → c ≠ b →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hmid : a + b = c + e)
    (hpar : ∃ t : ℝ, c - e = t • (a - b)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) =
      ({c, e} : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨t, ht⟩ := hpar
  by_cases hab : a = b
  · -- Degenerate chord: the parallel hypothesis collapses `c = e`, and the
    -- shared midpoint then collapses everything to one point.
    subst hab
    have hce : c = e := by simpa [sub_eq_zero] using ht
    subst hce
    have hca : c = a := by
      refine smul_right_injective (EuclideanSpace ℝ ι) (two_ne_zero (α := ℝ)) ?_
      calc (2 : ℝ) • c = c + c := two_smul ℝ c
        _ = a + a := hmid.symm
        _ = (2 : ℝ) • a := (two_smul ℝ a).symm
    rw [hca]
  · by_cases hca : c = a
    · -- `c = a`: equal sums force `e = b`.
      have hbe : b = e := by
        have h := hmid
        rw [hca] at h
        exact add_left_cancel h
      rw [hca, ← hbe]
    · by_cases hcb : c = b
      · -- `c = b`: equal sums force `e = a`.
        have hae : a = e := by
          have h := hmid
          rw [hcb, add_comm a b] at h
          exact add_left_cancel h
        rw [hcb, ← hae, Set.pair_comm a b]
      · -- `a`, `b`, `c` pairwise distinct: equal sums and parallel
        -- differences put `c` on the line through `a` and `b`, contradicting
        -- the no-three-collinear hypothesis.
        exfalso
        apply hgp hab hca hcb
        rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
        refine ⟨a - b, fun p hp => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨-1, by rw [vadd_eq_add]; module⟩
        · refine ⟨(t - 1) / 2, ?_⟩
          refine smul_right_injective (EuclideanSpace ℝ ι) (two_ne_zero (α := ℝ)) ?_
          rw [vadd_eq_add]
          linear_combination (norm := module) -hmid + ht

/-- Three distinct points of one Euclidean sphere are never collinear: a
line meets a sphere in at most two points.  This is the bridge showing the
general-position form of the theorem subsumes the sphere-slice form. -/
theorem not_collinear_of_mem_sphere
    {ι : Type*} [Fintype ι]
    {center p₁ p₂ p₃ : EuclideanSpace ℝ ι} {R : ℝ}
    (h₁ : p₁ ∈ Metric.sphere center R)
    (h₂ : p₂ ∈ Metric.sphere center R)
    (h₃ : p₃ ∈ Metric.sphere center R)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)) := by
  have hcos : EuclideanGeometry.Cospherical
      ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)) := by
    refine ⟨center, R, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simpa using h₁
    · simpa using h₂
    · simpa using h₃
  exact affineIndependent_iff_not_collinear_set.mp
    (hcos.affineIndependent_of_ne h₁₂ h₁₃ h₂₃)

/-! ## Per-quadruple genericity certificate -/

/-- **Per-quadruple certificate, rigidity-parameterized core**: for two
distinct pairs (the first nondegenerate) subject to a line-rigidity
hypothesis, the two identical-vanishing conditions that a
bisector-coincidence under projection would force cannot BOTH hold: the
projected-determinant form (parallelism) and the orthogonality form
(midpoint relation) are not simultaneously identically zero over all row
vectors.

This is the input the existence-of-a-generic-projection argument consumes:
for each off-pair quadruple, at least one of the two constraint polynomials
in the projection entries is not identically zero, so a generic projection
avoids the coincidence.  Contrapositive assembly of the coefficient lemma,
the parallelism lemma, and the supplied line rigidity. -/
theorem nearEnemy_offPair_not_both_vanish_of_rigid
    {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hrigid : a + b = c + e → (∃ t : ℝ, c - e = t • (a - b)) →
      ({a, b} : Set (EuclideanSpace ℝ ι)) = {c, e})
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0)) := by
  rintro ⟨hdet, hinn⟩
  have habv : a - b ≠ 0 := sub_ne_zero.mpr hab
  -- Coefficient lemma: identical vanishing of the orthogonality form forces
  -- equal midpoints upstairs.
  have hmid : a + b = c + e :=
    sub_eq_zero.mp (eq_zero_of_forall_inner_mul_inner_eq_zero habv hinn)
  -- Parallelism lemma: identical vanishing of the determinant form forces
  -- parallel difference vectors upstairs (the swap branch has a nonzero
  -- scalar, so it inverts).
  have hpar : ∃ t : ℝ, c - e = t • (a - b) := by
    rcases exists_smul_eq_of_forall_inner_det_eq_zero hdet with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, ht⟩
    · have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact habv ht
      exact ⟨t⁻¹, by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩
  -- Line rigidity closes the contradiction.
  exact hne (hrigid hmid hpar)

/-- **Per-quadruple certificate, sphere form**: the rigidity-parameterized
core instantiated with sphere-slice rigidity. -/
theorem nearEnemy_offPair_not_both_vanish
    {ι : Type*} [Fintype ι]
    {a b c e center : EuclideanSpace ℝ ι} {R : ℝ}
    (ha : a ∈ Metric.sphere center R)
    (hb : b ∈ Metric.sphere center R)
    (hc : c ∈ Metric.sphere center R)
    (he : e ∈ Metric.sphere center R)
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0)) :=
  nearEnemy_offPair_not_both_vanish_of_rigid
    (nearEnemy_sphereSlice_parallel_midpoint_eq_samePair ha hb hc he) hab hne

/-- **Per-quadruple certificate, general-position form**: the
rigidity-parameterized core instantiated with no-three-collinear
rigidity. -/
theorem nearEnemy_noThreeCollinear_offPair_not_both_vanish
    {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hgp : a ≠ b → c ≠ a → c ≠ b →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0)) :=
  nearEnemy_offPair_not_both_vanish_of_rigid
    (nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair hgp) hab hne

/-! ## Generic projections -/

/-- A linear projection to the plane is **generic** for a finite set `G` when
it sends distinct points of `G` to distinct points (with nondegenerate
difference vectors) and avoids, for every off-pair quadruple of `G`, the
coincidence "projected differences parallel AND projected midpoint-difference
orthogonal to the projected direction" — exactly the conjunction a shared
perpendicular bisector downstairs would force.

All polynomial content of the construction is isolated in the existence
statement for such a `T`; the main theorem is conditional on this
interface. -/
def ProjectionGeneric {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (G : Finset (EuclideanSpace ℝ ι)) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, a ≠ b → T (a - b) ≠ 0) ∧
  (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G, a ≠ b → c ≠ e →
    ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e} →
    ¬ ((∃ t : ℝ, T (c - e) = t • T (a - b)) ∧
        ⟪T (a + b - (c + e)), T (a - b)⟫ = 0))

/-! ## Downstairs: a shared bisector forces the coincidence conditions -/

/-- The module-local `perpBisector` is the coercion of mathlib's
affine-subspace perpendicular bisector. -/
theorem perpBisector_eq_coe (p q : EuclideanSpace ℝ (Fin 2)) :
    perpBisector p q = ↑(AffineSubspace.perpBisector p q) := by
  ext x
  simp [perpBisector, AffineSubspace.mem_perpBisector_iff_dist_eq]

/-- **Downstairs shared-bisector conditions**: if two point pairs in the plane
have equal perpendicular bisectors, then (1) their difference vectors are
parallel and (2) the difference of their pair-sums is orthogonal to the
direction.

Note carefully what is NOT concluded: the two midpoints need not be equal —
both lie on the common bisector line and may differ along it.  (2) is only
the component of the midpoint difference along the normal.  Equal midpoints
materialize upstairs, out of identical vanishing over all projections, via
the coefficient lemma. -/
theorem sharedBisector_parallel_and_sum_orth
    {p q p' q' : EuclideanSpace ℝ (Fin 2)}
    (h : perpBisector p q = perpBisector p' q') :
    (∃ t : ℝ, q' - p' = t • (q - p)) ∧ ⟪p + q - (p' + q'), q - p⟫ = 0 := by
  -- Promote the set equality to mathlib's affine-subspace bisector.
  have hS : AffineSubspace.perpBisector p q =
      AffineSubspace.perpBisector p' q' :=
    AffineSubspace.coe_injective
      (by rw [← perpBisector_eq_coe, ← perpBisector_eq_coe, h])
  constructor
  · -- (1) Equal affine subspaces have equal directions; the directions are
    -- the orthogonal complements of the difference-vector spans, and the
    -- double orthogonal complement recovers the spans.
    have hdir := congrArg AffineSubspace.direction hS
    rw [AffineSubspace.direction_perpBisector,
      AffineSubspace.direction_perpBisector] at hdir
    have hspan : (ℝ ∙ (q -ᵥ p)) = (ℝ ∙ (q' -ᵥ p')) := by
      have horth := congrArg Submodule.orthogonal hdir
      rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal]
        at horth
    have hmem : q' - p' ∈ (ℝ ∙ (q - p)) := by
      have hself : q' -ᵥ p' ∈ (ℝ ∙ (q' -ᵥ p')) :=
        Submodule.mem_span_singleton_self _
      rw [← hspan] at hself
      simpa [vsub_eq_sub] using hself
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨t, ht.symm⟩
  · -- (2) Both midpoints lie on the common bisector, so their difference is
    -- in its direction, i.e. orthogonal to the normal `q - p`.
    have hm : midpoint ℝ p q ∈ AffineSubspace.perpBisector p q :=
      AffineSubspace.midpoint_mem_perpBisector p q
    have hm' : midpoint ℝ p' q' ∈ AffineSubspace.perpBisector p q := by
      rw [hS]
      exact AffineSubspace.midpoint_mem_perpBisector p' q'
    have hd := AffineSubspace.vsub_mem_direction hm hm'
    rw [AffineSubspace.direction_perpBisector] at hd
    have hinner : ⟪q - p, midpoint ℝ p q - midpoint ℝ p' q'⟫ = 0 := by
      have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hd
      simpa [vsub_eq_sub] using this
    have h2m : (2 : ℝ) • (midpoint ℝ p q - midpoint ℝ p' q') =
        p + q - (p' + q') := by
      rw [smul_sub, two_smul, two_smul, midpoint_add_self, midpoint_add_self]
    calc ⟪p + q - (p' + q'), q - p⟫
        = ⟪(2 : ℝ) • (midpoint ℝ p q - midpoint ℝ p' q'), q - p⟫ := by
          rw [h2m]
      _ = 2 * ⟪midpoint ℝ p q - midpoint ℝ p' q', q - p⟫ :=
          real_inner_smul_left _ _ _
      _ = 2 * ⟪q - p, midpoint ℝ p q - midpoint ℝ p' q'⟫ := by
          rw [real_inner_comm]
      _ = 0 := by rw [hinner, mul_zero]

/-! ## Generic projections give bisector injectivity on unordered pairs -/

/-- **Shared-bisector criterion under a generic projection**: if a projection
is generic for `G` and two nondegenerate pairs from `G` acquire the same
perpendicular bisector downstairs, they were the same unordered pair
upstairs.  Sphere-free: coincidence-avoidance forbids every off-pair
quadruple directly; the sphere enters only the existence statement for a
generic `T`. -/
theorem nearEnemy_sharedBisector_forces_samePair
    {ι : Type*} [Fintype ι]
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    {G : Finset (EuclideanSpace ℝ ι)}
    (hT : ProjectionGeneric T G)
    {a b c e : EuclideanSpace ℝ ι}
    (ha : a ∈ G) (hb : b ∈ G) (hc : c ∈ G) (he : e ∈ G)
    (hab : a ≠ b) (hce : c ≠ e)
    (hbis : perpBisector (T a) (T b) = perpBisector (T c) (T e)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) = {c, e} := by
  by_contra hne
  obtain ⟨-, havoid⟩ := hT
  apply havoid a ha b hb c hc e he hab hce hne
  obtain ⟨⟨t, ht⟩, horth⟩ := sharedBisector_parallel_and_sum_orth hbis
  constructor
  · -- (1) downstairs parallelism transfers through linearity with the same
    -- scalar: `T e - T c = t • (T b - T a)` rewrites to
    -- `T (c - e) = t • T (a - b)`.
    refine ⟨t, ?_⟩
    rw [map_sub, map_sub]
    linear_combination (norm := module) -ht
  · -- (2) downstairs orthogonality transfers through linearity up to sign.
    have e1 : T (a + b - (c + e)) = T a + T b - (T c + T e) := by
      rw [map_sub, map_add, map_add]
    have e2 : T (a - b) = -(T b - T a) := by
      rw [map_sub]
      module
    rw [e1, e2, inner_neg_right, horth, neg_zero]

/-! ## Floor counting -/

/-- The bisector map of a planar point set is injective on unordered
nondegenerate pairs. -/
def BisectorInjectiveOnPairs (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ p' ∈ P, ∀ q' ∈ P, p ≠ q → p' ≠ q' →
    perpBisector p q = perpBisector p' q' →
    ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) = {p', q'}

section FloorCounting

open scoped Classical

/-- The trivial quadruples on an ordered nondegenerate pair: the pair repeated,
either in the same order or swapped. -/
def trivialQuad :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) × Bool →
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  fun rb => (rb.1, if rb.2 then rb.1 else (rb.1.2, rb.1.1))

private theorem trivialQuad_injOn (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set.InjOn trivialQuad ↑(P.offDiag ×ˢ (Finset.univ : Finset Bool)) := by
  rintro ⟨⟨x, y⟩, b⟩ h1 ⟨⟨x', y'⟩, b'⟩ h2 heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
    Finset.mem_offDiag] at h1 h2
  obtain ⟨⟨-, -, hxy⟩, -⟩ := h1
  have hfst : (x, y) = (x', y') := congrArg Prod.fst heq
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfst
  have hsnd : (if b then (x, y) else (y, x)) =
      (if b' then (x, y) else (y, x)) := congrArg Prod.snd heq
  cases b <;> cases b'
  · rfl
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true] at hsnd
    exact hxy (Prod.ext_iff.mp hsnd).2
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true] at hsnd
    exact hxy (Prod.ext_iff.mp hsnd).1
  · rfl

private theorem trivialQuad_mem_and_cond (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hq : q ∈ (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad) :
    q ∈ (P ×ˢ P) ×ˢ (P ×ˢ P) ∧ q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2 := by
  rw [Finset.mem_image] at hq
  obtain ⟨⟨⟨x, y⟩, b⟩, hmem, rfl⟩ := hq
  rw [Finset.mem_product, Finset.mem_offDiag] at hmem
  obtain ⟨⟨hx, hy, hxy⟩, -⟩ := hmem
  cases b <;>
    simp only [trivialQuad, ite_true, ite_false, Bool.false_eq_true,
      Finset.mem_product] <;>
    exact ⟨⟨⟨hx, hy⟩, by aesop⟩, hxy, by aesop, by simp [perpBisector_comm]⟩

private theorem mem_image_trivialQuad_of_injective
    {P : Finset (EuclideanSpace ℝ (Fin 2))} (hP : BisectorInjectiveOnPairs P)
    (q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hmem : q ∈ (P ×ˢ P) ×ˢ (P ×ˢ P)) (hne1 : q.1.1 ≠ q.1.2)
    (hne2 : q.2.1 ≠ q.2.2)
    (hbis : perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2) :
    q ∈ (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad := by
  obtain ⟨⟨x, y⟩, z, w⟩ := q
  rw [Finset.mem_product] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [Finset.mem_product] at h1 h2
  have hpair := hP x h1.1 y h1.2 z h2.1 w h2.2 hne1 hne2 hbis
  rw [Finset.mem_image]
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact ⟨((x, y), true), by
      rw [Finset.mem_product, Finset.mem_offDiag]
      exact ⟨⟨h1.1, h1.2, hne1⟩, Finset.mem_univ _⟩,
      by simp [trivialQuad, hz, hw]⟩
  · exact ⟨((x, y), false), by
      rw [Finset.mem_product, Finset.mem_offDiag]
      exact ⟨⟨h1.1, h1.2, hne1⟩, Finset.mem_univ _⟩,
      by simp [trivialQuad, ← hz, ← hw]⟩

private theorem card_arith (n : ℕ) : n * n - n = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ m => rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

/-- **Universal bisector-energy floor**: every finite planar point set has
bisector energy at least `2n(n−1)`, contributed by the trivial quadruples
alone.  This is what makes "minimal" in the headline theorem a theorem rather
than a count. -/
theorem two_mul_pairCount_le_bisectorEnergy
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * P.card * (P.card - 1) ≤ bisectorEnergy P := by
  have hsub : (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad ⊆
      ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2 := by
    intro q hq
    rw [Finset.mem_filter]
    obtain ⟨hmem, hcond⟩ := trivialQuad_mem_and_cond P q hq
    exact ⟨hmem, hcond⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (trivialQuad_injOn P), Finset.card_product,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_bool] at hle
  calc 2 * P.card * (P.card - 1)
      = (P.card * P.card - P.card) * 2 := by rw [card_arith]; ring
    _ ≤ _ := hle

/-- **Floor counting**: if the bisector map is injective on unordered pairs,
the bisector energy is exactly `2n(n−1)` — only the trivial quadruples
survive. -/
theorem bisectorEnergy_eq_of_bisectorInjective
    {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : BisectorInjectiveOnPairs P) :
    bisectorEnergy P = 2 * P.card * (P.card - 1) := by
  have heq : (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
      q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
        perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2) =
      (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad := by
    apply Finset.Subset.antisymm
    · intro q hq
      rw [Finset.mem_filter] at hq
      exact mem_image_trivialQuad_of_injective hP q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · intro q hq
      rw [Finset.mem_filter]
      obtain ⟨hmem, hcond⟩ := trivialQuad_mem_and_cond P q hq
      exact ⟨hmem, hcond⟩
  have hcard : bisectorEnergy P =
      ((P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad).card :=
    congrArg Finset.card heq
  rw [hcard, Finset.card_image_of_injOn (trivialQuad_injOn P),
    Finset.card_product, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_bool, card_arith]
  ring

end FloorCounting

/-! ## The Near Enemy Theorem for Bisector Energy (conditional form) -/

section MainTheorem

open scoped Classical

variable {ι : Type*} [Fintype ι]
  {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
  {G : Finset (EuclideanSpace ℝ ι)}

/-- A generic projection is injective on `G`. -/
theorem injOn_of_projectionGeneric (hT : ProjectionGeneric T G) :
    Set.InjOn (fun x ↦ T x) ↑G := by
  intro a ha b hb hTab
  by_contra hab
  exact hT.1 a ha b hb hab (by rw [map_sub, sub_eq_zero]; exact hTab)

/-- **Bisector injectivity downstairs**: under a generic projection, the
bisector map is injective on unordered pairs of the projected set. -/
theorem nearEnemy_bisectors_injective_on_unorderedPairs
    (hT : ProjectionGeneric T G) :
    BisectorInjectiveOnPairs (G.image fun x ↦ T x) := by
  intro p hp q hq p' hp' q' hq' hpq hpq' hbis
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq'
  have hab : a ≠ b := fun h ↦ hpq (by rw [h])
  have hce : c ≠ e := fun h ↦ hpq' (by rw [h])
  have hpair := nearEnemy_sharedBisector_forces_samePair hT ha hb hc he hab hce hbis
  calc ({T a, T b} : Set (EuclideanSpace ℝ (Fin 2)))
      = (fun x ↦ T x) '' {a, b} := (Set.image_pair _ _ _).symm
    _ = (fun x ↦ T x) '' {c, e} := by rw [hpair]
    _ = {T c, T e} := Set.image_pair _ _ _

/-- **Near Enemy Theorem for Bisector Energy, exact count (conditional
form)**: the image of a finite set under a generic projection has bisector
energy exactly `2n(n−1)`.  Sphere-free; the sphere enters only the existence
statement for a generic projection. -/
theorem nearEnemy_genericProjection_bisectorEnergy_eq_pairCount
    (hT : ProjectionGeneric T G) :
    bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) := by
  rw [bisectorEnergy_eq_of_bisectorInjective
    (nearEnemy_bisectors_injective_on_unorderedPairs hT),
    Finset.card_image_of_injOn (injOn_of_projectionGeneric hT)]

/-- **Near Enemy Theorem for Bisector Energy, minimality (conditional
form)**: the image of a finite set under a generic projection attains the
absolute minimum bisector energy among all planar point sets of the same
size. -/
theorem nearEnemy_genericProjection_bisectorEnergy_minimal
    (hT : ProjectionGeneric T G)
    (P' : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : P'.card = G.card) :
    bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P' := by
  rw [nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT, ← hcard]
  exact two_mul_pairCount_le_bisectorEnergy P'

end MainTheorem

/-! ## Existence of a generic projection

All polynomial content of the construction lives here.  Projections are
parameterized by their `2 × d` entry assignments `f : Fin 2 × ι → ℝ`; each
forbidden coincidence contributes a witness polynomial that is not
identically zero (by the per-quadruple certificate), the product over the
finitely many constraints is a nonzero polynomial over an infinite integral
domain, and any point where the product does not vanish yields a generic
projection.  `MvPolynomial.funext` is used exactly once, to produce that
point. -/

section Existence

open MvPolynomial
open scoped Classical

variable {ι : Type*} [Fintype ι]

/-- The linear form `Σ_i v_i · X_(k,i)` in the projection entries: the
polynomial whose value at an entry assignment is `⟪row k, v⟫`. -/
noncomputable def innerPoly (k : Fin 2) (v : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  ∑ i, C (v i) * X (k, i)

/-- Row extraction from an entry assignment. -/
def rowOf (f : Fin 2 × ι → ℝ) (k : Fin 2) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ f (k, i)

/-- The projection with prescribed rows: `(rowMap r x) k = ⟪r k, x⟫`. -/
noncomputable def rowMap (r : Fin 2 → EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun k ↦ innerₗ (EuclideanSpace ℝ ι) (r k))

@[simp] theorem rowMap_apply (r : Fin 2 → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (k : Fin 2) :
    rowMap r x k = ⟪r k, x⟫ := rfl

/-- Evaluation of the linear form recovers the row inner product. -/
theorem eval_innerPoly (f : Fin 2 × ι → ℝ) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval f (innerPoly k v) = ⟪rowOf f k, v⟫ := by
  simp [innerPoly, rowOf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Evaluation at the assignment built from two explicit rows. -/
theorem eval_innerPoly_rows (p q : EuclideanSpace ℝ ι) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval (fun ki ↦ ![p, q] ki.1 ki.2) (innerPoly k v) = ⟪![p, q] k, v⟫ :=
  eval_innerPoly _ k v

/-- Parallelism constraint polynomial of an off-pair quadruple: the projected
`2×2` determinant of the difference vectors. -/
noncomputable def detPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 (a - b) * innerPoly 1 (c - e) -
    innerPoly 0 (c - e) * innerPoly 1 (a - b)

/-- Orthogonality constraint polynomial of an off-pair quadruple: the inner
product of the projected pair-sum difference with the projected direction. -/
noncomputable def orthPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 (a + b - (c + e)) * innerPoly 0 (a - b) +
    innerPoly 1 (a + b - (c + e)) * innerPoly 1 (a - b)

/-- Constraint witness polynomial of a quadruple: the determinant polynomial
when it is nonzero as a polynomial, the orthogonality polynomial otherwise. -/
noncomputable def quadWitness
    (pq : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  if detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0 then
    detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2
  else orthPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2

/-- A nondegenerate difference vector has a nonzero linear form. -/
theorem innerPoly_ne_zero {a b : EuclideanSpace ℝ ι} (hab : a ≠ b) :
    innerPoly (ι := ι) 0 (a - b) ≠ 0 := by
  intro h0
  have heval := congrArg (eval fun ki ↦ ![a - b, 0] ki.1 ki.2) h0
  rw [eval_innerPoly_rows, map_zero, Matrix.cons_val_zero] at heval
  exact sub_ne_zero.mpr hab (inner_self_eq_zero.mp heval)

/-- **Per-quadruple witness, certificate-parameterized core**: if the two
identical-vanishing conditions cannot both hold for a quadruple, at least
one of the two constraint polynomials is nonzero as a polynomial.  This is
the polynomial-side form of the per-quadruple certificate. -/
theorem detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
    {a b c e : EuclideanSpace ℝ ι}
    (hnb : ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0))) :
    detPoly a b c e ≠ 0 ∨ orthPoly a b c e ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hd, ho⟩ := h
  refine hnb ⟨?_, ?_⟩
  · intro p q
    have h0 := congrArg (eval fun ki ↦ ![p, q] ki.1 ki.2) hd
    rw [map_zero] at h0
    simpa [detPoly, eval_innerPoly_rows] using h0
  · intro r
    have h0 := congrArg (eval fun ki ↦ ![r, 0] ki.1 ki.2) ho
    rw [map_zero] at h0
    simpa [orthPoly, eval_innerPoly_rows] using h0

/-- **Per-quadruple witness, sphere form**: for an off-pair quadruple on a
sphere, at least one of the two constraint polynomials is nonzero as a
polynomial. -/
theorem detPoly_ne_zero_or_orthPoly_ne_zero
    {a b c e center : EuclideanSpace ℝ ι} {R : ℝ}
    (ha : a ∈ Metric.sphere center R)
    (hb : b ∈ Metric.sphere center R)
    (hc : c ∈ Metric.sphere center R)
    (he : e ∈ Metric.sphere center R)
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    detPoly a b c e ≠ 0 ∨ orthPoly a b c e ≠ 0 :=
  detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
    (nearEnemy_offPair_not_both_vanish ha hb hc he hab hne)

/-- **Per-triple witness**: if the collinearity constraint polynomial of a
triple — the determinant polynomial of the difference vectors `b - a` and
`c - a` — vanishes as a polynomial, the triple is collinear upstairs.
Polynomial-side form of the parallelism lemma for triples; contrapositively,
a non-collinear triple has a nonzero constraint polynomial. -/
theorem collinear_of_detPoly_eq_zero
    {a b c : EuclideanSpace ℝ ι}
    (hd : detPoly b a c a = 0) :
    Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)) := by
  have hvan : ∀ p q : EuclideanSpace ℝ ι,
      ⟪p, b - a⟫ * ⟪q, c - a⟫ - ⟪p, c - a⟫ * ⟪q, b - a⟫ = 0 := by
    intro p q
    have h0 := congrArg (eval fun ki ↦ ![p, q] ki.1 ki.2) hd
    rw [map_zero] at h0
    simpa [detPoly, eval_innerPoly_rows] using h0
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  rcases exists_smul_eq_of_forall_inner_det_eq_zero hvan with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- `c - a = t • (b - a)`: the line through `a` with direction `b - a`.
    refine ⟨b - a, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [vadd_eq_add]; module⟩
    · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩
  · -- `b - a = t • (c - a)`: the line through `a` with direction `c - a`.
    refine ⟨c - a, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩
    · exact ⟨1, by rw [vadd_eq_add]; module⟩

omit [Fintype ι] in
/-- A row-pair assignment extracts to the given rows. -/
theorem rowOf_pair (p q : EuclideanSpace ℝ ι) (k : Fin 2) :
    rowOf (fun ki ↦ ![p, q] ki.1 ki.2) k = ![p, q] k := rfl

/-- Concyclicity constraint polynomial of a quadruple: the `4×4`
circle determinant `det (‖uᵢ‖², uᵢ₀, uᵢ₁, 1)` of the projected points,
written via explicit first-column cofactor expansion.  It vanishes at an
entry assignment exactly when the four projected points are concyclic or
collinear. -/
noncomputable def circPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  (innerPoly 0 a ^ 2 + innerPoly 1 a ^ 2) *
      (innerPoly 0 b * (innerPoly 1 c - innerPoly 1 e) -
        innerPoly 1 b * (innerPoly 0 c - innerPoly 0 e) +
        (innerPoly 0 c * innerPoly 1 e - innerPoly 0 e * innerPoly 1 c)) -
    (innerPoly 0 b ^ 2 + innerPoly 1 b ^ 2) *
      (innerPoly 0 a * (innerPoly 1 c - innerPoly 1 e) -
        innerPoly 1 a * (innerPoly 0 c - innerPoly 0 e) +
        (innerPoly 0 c * innerPoly 1 e - innerPoly 0 e * innerPoly 1 c)) +
    (innerPoly 0 c ^ 2 + innerPoly 1 c ^ 2) *
      (innerPoly 0 a * (innerPoly 1 b - innerPoly 1 e) -
        innerPoly 1 a * (innerPoly 0 b - innerPoly 0 e) +
        (innerPoly 0 b * innerPoly 1 e - innerPoly 0 e * innerPoly 1 b)) -
    (innerPoly 0 e ^ 2 + innerPoly 1 e ^ 2) *
      (innerPoly 0 a * (innerPoly 1 b - innerPoly 1 c) -
        innerPoly 1 a * (innerPoly 0 b - innerPoly 0 c) +
        (innerPoly 0 b * innerPoly 1 c - innerPoly 0 c * innerPoly 1 b))

/-- **Separating row**: four pairwise distinct points admit a row vector
whose inner products with them are pairwise distinct.  Polynomial
nonvanishing over the six difference forms. -/
theorem exists_row_pairwise_ne {a b c e : EuclideanSpace ℝ ι}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∃ v : EuclideanSpace ℝ ι,
      ⟪v, a⟫ ≠ ⟪v, b⟫ ∧ ⟪v, a⟫ ≠ ⟪v, c⟫ ∧ ⟪v, a⟫ ≠ ⟪v, e⟫ ∧
      ⟪v, b⟫ ≠ ⟪v, c⟫ ∧ ⟪v, b⟫ ≠ ⟪v, e⟫ ∧ ⟪v, c⟫ ≠ ⟪v, e⟫ := by
  set P : MvPolynomial (Fin 2 × ι) ℝ :=
    innerPoly 0 (a - b) * innerPoly 0 (a - c) * innerPoly 0 (a - e) *
      innerPoly 0 (b - c) * innerPoly 0 (b - e) * innerPoly 0 (c - e) with hP
  have hPne : P ≠ 0 := by
    rw [hP]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (innerPoly_ne_zero hab) (innerPoly_ne_zero hac)) (innerPoly_ne_zero hae))
      (innerPoly_ne_zero hbc)) (innerPoly_ne_zero hbe)) (innerPoly_ne_zero hce)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f P ≠ 0 := by
    by_contra h
    push Not at h
    exact hPne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  rw [hP] at hf
  simp only [map_mul] at hf
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have h3 := right_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf)))
  have h4 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have h5 := right_ne_zero_of_mul (left_ne_zero_of_mul hf)
  have h6 := right_ne_zero_of_mul hf
  exact ⟨rowOf f 0,
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h1),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h2),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h3),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h4),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h5),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h6)⟩

/-- **Per-quadruple concyclicity witness**: the concyclicity constraint
polynomial of an affinely independent quadruple is nonzero as a polynomial.

Proof design: along the curve of row pairs `(v, s • w)` the evaluation is
`s·P + s³·Q`, where `P` is the parabola determinant `det (xᵢ², xᵢ, yᵢ, 1)`
with `xᵢ` the `v`-coordinates and `yᵢ` the `w`-coordinates.  `P` is linear
in the `yᵢ` with Vandermonde-cofactor coefficients `wᵢ` (nonzero once `v`
separates the four points), so choosing `w := Σ wᵢ • pᵢ` makes
`P = ⟪w, w⟫`.  Identical vanishing then forces `w = 0`, an affine
dependence with nonzero weights — impossible for an affinely independent
quadruple. -/
theorem circPoly_ne_zero_of_affineIndependent
    {a b c e : EuclideanSpace ℝ ι}
    (hind : AffineIndependent ℝ ![a, b, c, e]) :
    circPoly a b c e ≠ 0 := by
  intro hcirc
  have hinj := hind.injective
  have hab : a ≠ b := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 1 from h)) (by decide)
  have hac : a ≠ c := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 2 from h)) (by decide)
  have hae : a ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 3 from h)) (by decide)
  have hbc : b ≠ c := fun h =>
    absurd (hinj (show ![a, b, c, e] 1 = ![a, b, c, e] 2 from h)) (by decide)
  have hbe : b ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 1 = ![a, b, c, e] 3 from h)) (by decide)
  have hce : c ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 2 = ![a, b, c, e] 3 from h)) (by decide)
  obtain ⟨v, hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄⟩ :=
    exists_row_pairwise_ne hab hac hae hbc hbe hce
  set m : EuclideanSpace ℝ ι :=
    ((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)) • a +
      (-((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫))) • b +
      ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)) • c +
      (-((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))) • e
    with hmdef
  have hE1 := congrArg (eval fun ki ↦ ![v, m] ki.1 ki.2) hcirc
  have hE2 := congrArg (eval fun ki ↦ ![v, (2 : ℝ) • m] ki.1 ki.2) hcirc
  rw [map_zero] at hE1 hE2
  simp only [circPoly, map_add, map_sub, map_mul, map_pow, eval_innerPoly,
    rowOf_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    real_inner_smul_left] at hE1 hE2
  -- The parabola determinant, extracted from two scalings of the second row.
  have hP : ((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)) * ⟪m, a⟫
      + (-((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫))) * ⟪m, b⟫
      + ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)) * ⟪m, c⟫
      + (-((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))) * ⟪m, e⟫
      = 0 := by
    linear_combination (4 / 3 : ℝ) * hE1 - (1 / 6 : ℝ) * hE2
  have hmm : ⟪m, m⟫ = (0 : ℝ) := by
    nth_rewrite 2 [hmdef]
    rw [inner_add_right, inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right]
    linear_combination hP
  have hm0 : m = 0 := inner_self_eq_zero.mp hmm
  rw [hmdef] at hm0
  -- Affine independence kills the Vandermonde weights, but the first one is
  -- a product of nonzero differences.
  have hw := affineIndependent_iff.mp hind Finset.univ
    ![((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)),
      -((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫)),
      ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)),
      -((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))]
    (by simp [Fin.sum_univ_four]; ring)
    (by simpa [Fin.sum_univ_four] using hm0)
    0 (Finset.mem_univ _)
  simp only [Matrix.cons_val_zero] at hw
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd₃₄)
    (sub_ne_zero.mpr hd₂₃)) (sub_ne_zero.mpr hd₂₄) hw

/-- **Downstairs concyclicity bridge**: if the four projected points lie on
one circle, the concyclicity constraint polynomial evaluates to zero at the
entry assignment.  The circle equation makes the first determinant column an
affine combination of the other three. -/
theorem eval_circPoly_eq_zero_of_dist_eq
    {f : Fin 2 × ι → ℝ} {a b c e : EuclideanSpace ℝ ι}
    {z : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    (ha : dist (rowMap (rowOf f) a) z = ρ)
    (hb : dist (rowMap (rowOf f) b) z = ρ)
    (hc : dist (rowMap (rowOf f) c) z = ρ)
    (he : dist (rowMap (rowOf f) e) z = ρ) :
    eval f (circPoly a b c e) = 0 := by
  have key : ∀ p : EuclideanSpace ℝ ι, dist (rowMap (rowOf f) p) z = ρ →
      ⟪rowOf f 0, p⟫ ^ 2 + ⟪rowOf f 1, p⟫ ^ 2 =
        2 * z 0 * ⟪rowOf f 0, p⟫ + 2 * z 1 * ⟪rowOf f 1, p⟫ +
          (ρ ^ 2 - z 0 ^ 2 - z 1 ^ 2) := by
    intro p hp
    have h2 : dist (rowMap (rowOf f) p) z ^ 2 = ρ ^ 2 := by rw [hp]
    rw [EuclideanSpace.dist_sq_eq] at h2
    simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, rowMap_apply] at h2
    linear_combination h2
  have h₁ := key a ha
  have h₂ := key b hb
  have h₃ := key c hc
  have h₄ := key e he
  simp only [circPoly, map_add, map_sub, map_mul, map_pow, eval_innerPoly]
  linear_combination
    (⟪rowOf f 0, b⟫ * (⟪rowOf f 1, c⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, b⟫ * (⟪rowOf f 0, c⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, c⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, c⟫)) * h₁
    - (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, c⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, c⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, c⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, c⟫)) * h₂
    + (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, b⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, b⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, b⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, b⟫)) * h₃
    - (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, b⟫ - ⟪rowOf f 1, c⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, b⟫ - ⟪rowOf f 0, c⟫) +
      (⟪rowOf f 0, b⟫ * ⟪rowOf f 1, c⟫ - ⟪rowOf f 0, c⟫ * ⟪rowOf f 1, b⟫)) * h₄

/-- Distance-class constraint polynomial of a pair of difference vectors:
the difference `‖Tv‖² - ‖Tw‖²` of the squared norms of the projected
vectors, as a polynomial in the projection entries. -/
noncomputable def distClassPoly (v w : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 v ^ 2 + innerPoly 1 v ^ 2 -
    (innerPoly 0 w ^ 2 + innerPoly 1 w ^ 2)

/-- **Per-pair distance-class witness**: for difference vectors that are
neither equal nor opposite, the distance-class constraint polynomial is
nonzero as a polynomial.  No nondegeneracy or general-position hypothesis is
needed: identical vanishing forces `w = ±v` by the distance-class separation
lemma. -/
theorem distClassPoly_ne_zero {v w : EuclideanSpace ℝ ι}
    (h1 : w ≠ v) (h2 : w ≠ -v) : distClassPoly v w ≠ 0 := by
  intro h0
  have key : ∀ r : EuclideanSpace ℝ ι, ⟪r, v - w⟫ * ⟪r, v + w⟫ = 0 := by
    intro r
    have heval := congrArg (eval fun ki ↦ ![r, 0] ki.1 ki.2) h0
    rw [map_zero] at heval
    simp only [distClassPoly, map_add, map_sub, map_pow, eval_innerPoly_rows,
      Matrix.cons_val_zero, Matrix.cons_val_one, inner_zero_left] at heval
    rw [inner_sub_right, inner_add_right]
    linear_combination heval
  rcases eq_or_eq_neg_of_forall_inner_sub_mul_inner_add key with h | h
  · exact h1 h
  · exact h2 h

/-- **Downstairs distance bridge**: if two projected pairs have equal planar
distance, the distance-class constraint polynomial of their difference
vectors evaluates to zero at the entry assignment. -/
theorem eval_distClassPoly_eq_zero_of_dist_eq
    {f : Fin 2 × ι → ℝ} {a b c e : EuclideanSpace ℝ ι}
    (h : dist (rowMap (rowOf f) a) (rowMap (rowOf f) b) =
      dist (rowMap (rowOf f) c) (rowMap (rowOf f) e)) :
    eval f (distClassPoly (a - b) (c - e)) = 0 := by
  have h2 : dist (rowMap (rowOf f) a) (rowMap (rowOf f) b) ^ 2 =
      dist (rowMap (rowOf f) c) (rowMap (rowOf f) e) ^ 2 := by rw [h]
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at h2
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, rowMap_apply] at h2
  simp only [distClassPoly, map_add, map_sub, map_pow, eval_innerPoly,
    inner_sub_right]
  linear_combination h2

/-- **Downstairs rotation-channel vanishing**: a projection that separates
the planar distances of all difference-distinct (non-translation,
non-half-turn) pairs of pairs of `G` has an image with zero rotational
energy — every congruent quadruple of the image is translation or half-turn
related. -/
theorem rotationEnergy_image_eq_zero
    {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e)) :
    rotationEnergy (G.image fun x ↦ T x) = 0 := by
  rw [rotationEnergy, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨q₁, q₂⟩, q₃, q₄⟩ hq
  simp only [Finset.mem_product] at hq
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h2
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h3
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h4
  rintro ⟨-, -, hdist, hne1, hne2⟩
  by_cases hvw : a - b = c - e
  · refine hne1 ?_
    show T a - T b = T c - T e
    rw [← map_sub, ← map_sub, hvw]
  by_cases hvw' : a - b = -(c - e)
  · refine hne2 ?_
    show T a - T b = -(T c - T e)
    rw [← map_sub, ← map_sub, ← map_neg, hvw']
  exact hsep a ha b hb c hc e he hvw hvw' hdist

/-- **Existence of a generic projection, witness-parameterized core**: for
any finite set whose off-pair quadruples each carry a nonzero constraint
polynomial, a generic projection exists.  The master polynomial multiplies a
witness polynomial per constraint; it is nonzero over the infinite integral
domain `ℝ[X]`, so it has a nonvanishing point, and the rows read off that
point give a generic projection. -/
theorem exists_projectionGeneric_of_forall_offPair_witness
    {G : Finset (EuclideanSpace ℝ ι)}
    (hW : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G, a ≠ b → c ≠ e →
      ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e} →
      detPoly a b c e ≠ 0 ∨ orthPoly a b c e ≠ 0) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G := by
  -- Constraint index set for the quadruple constraints.
  set Quads : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    (G.offDiag ×ˢ G.offDiag).filter
      (fun pq ↦ ({pq.1.1, pq.1.2} : Set (EuclideanSpace ℝ ι)) ≠
        {pq.2.1, pq.2.2}) with hQuads
  -- Each quadruple witness is nonzero as a polynomial.
  have hwq_ne : ∀ pq ∈ Quads, quadWitness pq ≠ 0 := by
    intro pq hpq
    rw [hQuads, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne⟩ := hpq
    rw [Finset.mem_offDiag] at h1 h2
    rw [quadWitness]
    by_cases hdet : detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0
    · rwa [if_pos hdet]
    · rw [if_neg hdet]
      push Not at hdet
      rcases hW _ h1.1 _ h1.2.1 _ h2.1 _ h2.2.1 h1.2.2 h2.2.2 hne with h | h
      · exact absurd hdet h
      · exact h
  -- The master polynomial and its nonvanishing point.
  set master : MvPolynomial (Fin 2 × ι) ℝ :=
    (∏ ab ∈ G.offDiag, innerPoly 0 (ab.1 - ab.2)) * ∏ pq ∈ Quads, quadWitness pq
      with hmaster
  have hmaster_ne : master ≠ 0 := by
    rw [hmaster]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun ab hab ↦
        innerPoly_ne_zero (Finset.mem_offDiag.mp hab).2.2)
      (Finset.prod_ne_zero_iff.mpr hwq_ne)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f master ≠ 0 := by
    by_contra h
    push Not at h
    exact hmaster_ne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  -- All factor evaluations are nonzero at `f`.
  rw [hmaster, map_mul, map_prod, map_prod] at hf
  have hpairs_eval : ∀ ab ∈ G.offDiag, eval f (innerPoly 0 (ab.1 - ab.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf)
  have hquads_eval : ∀ pq ∈ Quads, eval f (quadWitness pq) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf)
  -- The projection with rows read off `f` is generic.
  refine ⟨rowMap (rowOf f), ?_, ?_⟩
  · -- Injectivity / nondegeneracy.
    intro a ha b hb hab hT0
    have hmem : (a, b) ∈ G.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
    apply hpairs_eval (a, b) hmem
    rw [eval_innerPoly]
    have h0 : rowMap (rowOf f) (a - b) 0 = 0 := by rw [hT0]; rfl
    rwa [rowMap_apply] at h0
  · -- Coincidence-avoidance.
    intro a ha b hb c hc e he hab hce hne hbad
    obtain ⟨⟨t, hpar⟩, horth⟩ := hbad
    have hmem : ((a, b), (c, e)) ∈ Quads := by
      rw [hQuads, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩,
        Finset.mem_offDiag.mpr ⟨hc, he, hce⟩⟩, hne⟩
    apply hquads_eval _ hmem
    rw [quadWitness]
    -- Components of the projected vectors.
    have hcomp : ∀ k : Fin 2, ⟪rowOf f k, c - e⟫ = t * ⟪rowOf f k, a - b⟫ := by
      intro k
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v k) hpar
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul, inner_sub_right]
        using h
    by_cases hdet : detPoly a b c e ≠ 0
    · rw [if_pos hdet]
      simp only [detPoly, map_sub, map_mul, eval_innerPoly]
      rw [hcomp 0, hcomp 1]
      ring
    · rw [if_neg hdet]
      simp only [orthPoly, map_add, map_mul, eval_innerPoly]
      have hexp : ⟪rowMap (rowOf f) (a + b - (c + e)),
          rowMap (rowOf f) (a - b)⟫ =
          ⟪rowOf f 0, a + b - (c + e)⟫ * ⟪rowOf f 0, a - b⟫ +
            ⟪rowOf f 1, a + b - (c + e)⟫ * ⟪rowOf f 1, a - b⟫ := by
        rw [PiLp.inner_apply]
        simp only [Fin.sum_univ_two, RCLike.inner_apply, rowMap_apply,
          starRingEnd_apply, star_trivial, inner_add_right, inner_sub_right]
        ring
      rw [← hexp, horth]

/-- **Existence of a generic projection** for any finite set with no three
collinear points. -/
theorem nearEnemy_noThreeCollinear_exists_projectionGeneric
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G :=
  exists_projectionGeneric_of_forall_offPair_witness
    fun a ha b hb c hc _e _he hab _hce hne =>
      detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
        (nearEnemy_noThreeCollinear_offPair_not_both_vanish
          (fun hab' hca hcb => hG a ha b hb c hc hab' hca.symm hcb.symm)
          hab hne)

/-- **Existence of a generic projection preserving general position**: for a
finite set with no three collinear points, there is a generic projection
whose images of distinct triples are again non-collinear — the planar image
is itself in general position.  Same master-product argument with one more
factor family: a collinearity constraint polynomial per distinct triple,
nonzero by the per-triple witness. -/
theorem nearEnemy_exists_projectionGeneric_preserving_noThreeCollinear
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G ∧
      ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
        ¬ Collinear ℝ ({T p₁, T p₂, T p₃} : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Constraint index sets for the quadruple and triple constraints.
  set Quads : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    (G.offDiag ×ˢ G.offDiag).filter
      (fun pq ↦ ({pq.1.1, pq.1.2} : Set (EuclideanSpace ℝ ι)) ≠
        {pq.2.1, pq.2.2}) with hQuads
  set Triples : Finset (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    (G ×ˢ G ×ˢ G).filter
      (fun p ↦ p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) with hTriples
  -- Each quadruple witness is nonzero as a polynomial.
  have hwq_ne : ∀ pq ∈ Quads, quadWitness pq ≠ 0 := by
    intro pq hpq
    rw [hQuads, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne⟩ := hpq
    rw [Finset.mem_offDiag] at h1 h2
    rw [quadWitness]
    by_cases hdet : detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0
    · rwa [if_pos hdet]
    · rw [if_neg hdet]
      push Not at hdet
      rcases detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
        (nearEnemy_noThreeCollinear_offPair_not_both_vanish
          (fun hab' hca hcb =>
            hG _ h1.1 _ h1.2.1 _ h2.1 hab' hca.symm hcb.symm)
          h1.2.2 hne) with h | h
      · exact absurd hdet h
      · exact h
  -- Each triple constraint polynomial is nonzero as a polynomial.
  have htr_ne : ∀ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1 ≠ 0 := by
    intro tr htr hd
    rw [hTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at htr
    obtain ⟨⟨h1, h2, h3⟩, h12, h13, h23⟩ := htr
    exact hG _ h1 _ h2 _ h3 h12 h13 h23 (collinear_of_detPoly_eq_zero hd)
  -- The master polynomial and its nonvanishing point.
  set master : MvPolynomial (Fin 2 × ι) ℝ :=
    ((∏ ab ∈ G.offDiag, innerPoly 0 (ab.1 - ab.2)) *
        ∏ pq ∈ Quads, quadWitness pq) *
      ∏ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1 with hmaster
  have hmaster_ne : master ≠ 0 := by
    rw [hmaster]
    exact mul_ne_zero
      (mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun ab hab ↦
          innerPoly_ne_zero (Finset.mem_offDiag.mp hab).2.2)
        (Finset.prod_ne_zero_iff.mpr hwq_ne))
      (Finset.prod_ne_zero_iff.mpr htr_ne)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f master ≠ 0 := by
    by_contra h
    push Not at h
    exact hmaster_ne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  -- All factor evaluations are nonzero at `f`.
  rw [hmaster, map_mul, map_mul, map_prod, map_prod, map_prod] at hf
  have hpairs_eval : ∀ ab ∈ G.offDiag, eval f (innerPoly 0 (ab.1 - ab.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have hquads_eval : ∀ pq ∈ Quads, eval f (quadWitness pq) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have htriples_eval : ∀ tr ∈ Triples,
      eval f (detPoly tr.2.1 tr.1 tr.2.2 tr.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf)
  -- The projection with rows read off `f` is generic and preserves
  -- non-collinearity of triples.
  refine ⟨rowMap (rowOf f), ⟨?_, ?_⟩, ?_⟩
  · -- Injectivity / nondegeneracy.
    intro a ha b hb hab hT0
    have hmem : (a, b) ∈ G.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
    apply hpairs_eval (a, b) hmem
    rw [eval_innerPoly]
    have h0 : rowMap (rowOf f) (a - b) 0 = 0 := by rw [hT0]; rfl
    rwa [rowMap_apply] at h0
  · -- Coincidence-avoidance.
    intro a ha b hb c hc e he hab hce hne hbad
    obtain ⟨⟨t, hpar⟩, horth⟩ := hbad
    have hmem : ((a, b), (c, e)) ∈ Quads := by
      rw [hQuads, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩,
        Finset.mem_offDiag.mpr ⟨hc, he, hce⟩⟩, hne⟩
    apply hquads_eval _ hmem
    rw [quadWitness]
    -- Components of the projected vectors.
    have hcomp : ∀ k : Fin 2, ⟪rowOf f k, c - e⟫ = t * ⟪rowOf f k, a - b⟫ := by
      intro k
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v k) hpar
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul, inner_sub_right]
        using h
    by_cases hdet : detPoly a b c e ≠ 0
    · rw [if_pos hdet]
      simp only [detPoly, map_sub, map_mul, eval_innerPoly]
      rw [hcomp 0, hcomp 1]
      ring
    · rw [if_neg hdet]
      simp only [orthPoly, map_add, map_mul, eval_innerPoly]
      have hexp : ⟪rowMap (rowOf f) (a + b - (c + e)),
          rowMap (rowOf f) (a - b)⟫ =
          ⟪rowOf f 0, a + b - (c + e)⟫ * ⟪rowOf f 0, a - b⟫ +
            ⟪rowOf f 1, a + b - (c + e)⟫ * ⟪rowOf f 1, a - b⟫ := by
        rw [PiLp.inner_apply]
        simp only [Fin.sum_univ_two, RCLike.inner_apply, rowMap_apply,
          starRingEnd_apply, star_trivial, inner_add_right, inner_sub_right]
        ring
      rw [← hexp, horth]
  · -- Triple non-collinearity downstairs.
    intro p₁ h₁ p₂ h₂ p₃ h₃ h₁₂ h₁₃ h₂₃ hcol
    have hmem : (p₁, p₂, p₃) ∈ Triples := by
      rw [hTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨h₁, h₂, h₃⟩, h₁₂, h₁₃, h₂₃⟩
    apply htriples_eval _ hmem
    -- Collinear images give a common direction; both projected difference
    -- vectors are multiples of it, so the projected determinant vanishes.
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₂, hr₂⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨r₃, hr₃⟩ := hv _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hcomp₂ : ∀ k : Fin 2,
        ⟪rowOf f k, p₂⟫ - ⟪rowOf f k, p₁⟫ = r₂ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₂ - p₁) = r₂ • v := by
        rw [map_sub, hr₂, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    have hcomp₃ : ∀ k : Fin 2,
        ⟪rowOf f k, p₃⟫ - ⟪rowOf f k, p₁⟫ = r₃ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₃ - p₁) = r₃ • v := by
        rw [map_sub, hr₃, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    simp only [detPoly, map_sub, map_mul, eval_innerPoly, inner_sub_right]
    rw [hcomp₂ 0, hcomp₂ 1, hcomp₃ 0, hcomp₃ 1]
    ring

/-- **Existence of a generic projection landing in full general position**:
for a finite set with no three collinear points and every four points
affinely independent, there is a generic projection whose image has no
three collinear points AND no four concyclic points.  Same master-product
argument with two extra factor families: a collinearity constraint
polynomial per distinct triple and a concyclicity constraint polynomial per
distinct quadruple. -/
theorem nearEnemy_exists_projectionGeneric_image_generalPosition
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)))
    (hG4 : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, ∀ p₄ ∈ G,
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
      AffineIndependent ℝ ![p₁, p₂, p₃, p₄]) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G ∧
      (∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
        ¬ Collinear ℝ ({T p₁, T p₂, T p₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, ∀ p₄ ∈ G,
        p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
        ¬ EuclideanGeometry.Cospherical
          ({T p₁, T p₂, T p₃, T p₄} : Set (EuclideanSpace ℝ (Fin 2))) := by
  -- Constraint index sets.
  set Quads : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    (G.offDiag ×ˢ G.offDiag).filter
      (fun pq ↦ ({pq.1.1, pq.1.2} : Set (EuclideanSpace ℝ ι)) ≠
        {pq.2.1, pq.2.2}) with hQuads
  set Triples : Finset (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    (G ×ˢ G ×ˢ G).filter
      (fun p ↦ p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) with hTriples
  set Quads4 : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
      (fun q ↦ q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧
        q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2) with hQuads4
  -- Per-constraint nonzero witnesses.
  have hwq_ne : ∀ pq ∈ Quads, quadWitness pq ≠ 0 := by
    intro pq hpq
    rw [hQuads, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne⟩ := hpq
    rw [Finset.mem_offDiag] at h1 h2
    rw [quadWitness]
    by_cases hdet : detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0
    · rwa [if_pos hdet]
    · rw [if_neg hdet]
      push Not at hdet
      rcases detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
        (nearEnemy_noThreeCollinear_offPair_not_both_vanish
          (fun hab' hca hcb =>
            hG _ h1.1 _ h1.2.1 _ h2.1 hab' hca.symm hcb.symm)
          h1.2.2 hne) with h | h
      · exact absurd hdet h
      · exact h
  have htr_ne : ∀ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1 ≠ 0 := by
    intro tr htr hd
    rw [hTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at htr
    obtain ⟨⟨h1, h2, h3⟩, h12, h13, h23⟩ := htr
    exact hG _ h1 _ h2 _ h3 h12 h13 h23 (collinear_of_detPoly_eq_zero hd)
  have hq4_ne : ∀ q ∈ Quads4, circPoly q.1.1 q.1.2 q.2.1 q.2.2 ≠ 0 := by
    intro q hq
    rw [hQuads4, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_product] at hq
    obtain ⟨⟨⟨ha, hb⟩, hc, he⟩, h12, h13, h14, h23, h24, h34⟩ := hq
    exact circPoly_ne_zero_of_affineIndependent
      (hG4 _ ha _ hb _ hc _ he h12 h13 h14 h23 h24 h34)
  -- The master polynomial and its nonvanishing point.
  set master : MvPolynomial (Fin 2 × ι) ℝ :=
    (((∏ ab ∈ G.offDiag, innerPoly 0 (ab.1 - ab.2)) *
        ∏ pq ∈ Quads, quadWitness pq) *
      ∏ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1) *
      ∏ q ∈ Quads4, circPoly q.1.1 q.1.2 q.2.1 q.2.2 with hmaster
  have hmaster_ne : master ≠ 0 := by
    rw [hmaster]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun ab hab ↦
        innerPoly_ne_zero (Finset.mem_offDiag.mp hab).2.2)
      (Finset.prod_ne_zero_iff.mpr hwq_ne))
      (Finset.prod_ne_zero_iff.mpr htr_ne))
      (Finset.prod_ne_zero_iff.mpr hq4_ne)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f master ≠ 0 := by
    by_contra h
    push Not at h
    exact hmaster_ne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  -- All factor evaluations are nonzero at `f`.
  rw [hmaster, map_mul, map_mul, map_mul, map_prod, map_prod, map_prod,
    map_prod] at hf
  have hpairs_eval : ∀ ab ∈ G.offDiag, eval f (innerPoly 0 (ab.1 - ab.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul hf)))
  have hquads_eval : ∀ pq ∈ Quads, eval f (quadWitness pq) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul hf)))
  have htriples_eval : ∀ tr ∈ Triples,
      eval f (detPoly tr.2.1 tr.1 tr.2.2 tr.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have hquads4_eval : ∀ q ∈ Quads4,
      eval f (circPoly q.1.1 q.1.2 q.2.1 q.2.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf)
  -- The projection with rows read off `f`.
  refine ⟨rowMap (rowOf f), ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Injectivity / nondegeneracy.
    intro a ha b hb hab hT0
    have hmem : (a, b) ∈ G.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
    apply hpairs_eval (a, b) hmem
    rw [eval_innerPoly]
    have h0 : rowMap (rowOf f) (a - b) 0 = 0 := by rw [hT0]; rfl
    rwa [rowMap_apply] at h0
  · -- Coincidence-avoidance.
    intro a ha b hb c hc e he hab hce hne hbad
    obtain ⟨⟨t, hpar⟩, horth⟩ := hbad
    have hmem : ((a, b), (c, e)) ∈ Quads := by
      rw [hQuads, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩,
        Finset.mem_offDiag.mpr ⟨hc, he, hce⟩⟩, hne⟩
    apply hquads_eval _ hmem
    rw [quadWitness]
    have hcomp : ∀ k : Fin 2, ⟪rowOf f k, c - e⟫ = t * ⟪rowOf f k, a - b⟫ := by
      intro k
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v k) hpar
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul, inner_sub_right]
        using h
    by_cases hdet : detPoly a b c e ≠ 0
    · rw [if_pos hdet]
      simp only [detPoly, map_sub, map_mul, eval_innerPoly]
      rw [hcomp 0, hcomp 1]
      ring
    · rw [if_neg hdet]
      simp only [orthPoly, map_add, map_mul, eval_innerPoly]
      have hexp : ⟪rowMap (rowOf f) (a + b - (c + e)),
          rowMap (rowOf f) (a - b)⟫ =
          ⟪rowOf f 0, a + b - (c + e)⟫ * ⟪rowOf f 0, a - b⟫ +
            ⟪rowOf f 1, a + b - (c + e)⟫ * ⟪rowOf f 1, a - b⟫ := by
        rw [PiLp.inner_apply]
        simp only [Fin.sum_univ_two, RCLike.inner_apply, rowMap_apply,
          starRingEnd_apply, star_trivial, inner_add_right, inner_sub_right]
        ring
      rw [← hexp, horth]
  · -- Triple non-collinearity downstairs.
    intro p₁ h₁ p₂ h₂ p₃ h₃ h₁₂ h₁₃ h₂₃ hcol
    have hmem : (p₁, p₂, p₃) ∈ Triples := by
      rw [hTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨h₁, h₂, h₃⟩, h₁₂, h₁₃, h₂₃⟩
    apply htriples_eval _ hmem
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₂, hr₂⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨r₃, hr₃⟩ := hv _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hcomp₂ : ∀ k : Fin 2,
        ⟪rowOf f k, p₂⟫ - ⟪rowOf f k, p₁⟫ = r₂ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₂ - p₁) = r₂ • v := by
        rw [map_sub, hr₂, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    have hcomp₃ : ∀ k : Fin 2,
        ⟪rowOf f k, p₃⟫ - ⟪rowOf f k, p₁⟫ = r₃ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₃ - p₁) = r₃ • v := by
        rw [map_sub, hr₃, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    simp only [detPoly, map_sub, map_mul, eval_innerPoly, inner_sub_right]
    rw [hcomp₂ 0, hcomp₂ 1, hcomp₃ 0, hcomp₃ 1]
    ring
  · -- Quadruple non-concyclicity downstairs.
    intro p₁ h₁ p₂ h₂ p₃ h₃ p₄ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hcos
    obtain ⟨z, ρ, hz⟩ := hcos
    have hmem : ((p₁, p₂), (p₃, p₄)) ∈ Quads4 := by
      rw [hQuads4, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
    exact hquads4_eval _ hmem (eval_circPoly_eq_zero_of_dist_eq
      (hz _ (Set.mem_insert _ _))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _))))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))))

/-- **Existence of a generic projection** for any finite sphere subset.
Derived from the general-position form: a line meets a sphere in at most
two points, so sphere subsets have no three collinear points. -/
theorem nearEnemy_exists_projectionGeneric
    {center : EuclideanSpace ℝ ι} {R : ℝ} {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ x ∈ G, x ∈ Metric.sphere center R) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G :=
  nearEnemy_noThreeCollinear_exists_projectionGeneric
    fun _p₁ h₁ _p₂ h₂ _p₃ h₃ h₁₂ h₁₃ h₂₃ =>
      not_collinear_of_mem_sphere (hG _ h₁) (hG _ h₂) (hG _ h₃) h₁₂ h₁₃ h₂₃

/-- **Universal rotation-killing projection**: every finite set in any
Euclidean space admits an injective planar projection whose image has zero
rotational energy — every congruent quadruple of the image is translation or
half-turn related.  No hypothesis on `G` at all: the per-pair distance-class
witnesses are unconditionally nonzero, so the master-product argument
applies to every finite set. -/
theorem nearEnemy_exists_projection_image_rotationEnergy_zero
    (G : Finset (EuclideanSpace ℝ ι)) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      rotationEnergy (G.image fun x ↦ T x) = 0 := by
  -- Constraint index set: pairs of pairs with difference-distinct vectors.
  set DPairs : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
      (fun q ↦ q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
        q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)) with hDPairs
  have hdp_ne : ∀ q ∈ DPairs,
      distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2) ≠ 0 := by
    intro q hq
    rw [hDPairs, Finset.mem_filter] at hq
    exact distClassPoly_ne_zero (fun h ↦ hq.2.1 h.symm)
      (fun h ↦ hq.2.2 (by rw [h, neg_neg]))
  -- The master polynomial and its nonvanishing point.
  set master : MvPolynomial (Fin 2 × ι) ℝ :=
    (∏ ab ∈ G.offDiag, innerPoly 0 (ab.1 - ab.2)) *
      ∏ q ∈ DPairs, distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2) with hmaster
  have hmaster_ne : master ≠ 0 := by
    rw [hmaster]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun ab hab ↦
        innerPoly_ne_zero (Finset.mem_offDiag.mp hab).2.2)
      (Finset.prod_ne_zero_iff.mpr hdp_ne)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f master ≠ 0 := by
    by_contra h
    push Not at h
    exact hmaster_ne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  -- All factor evaluations are nonzero at `f`.
  rw [hmaster, map_mul, map_prod, map_prod] at hf
  have hpairs_eval : ∀ ab ∈ G.offDiag, eval f (innerPoly 0 (ab.1 - ab.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf)
  have hdpairs_eval : ∀ q ∈ DPairs,
      eval f (distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf)
  refine ⟨rowMap (rowOf f), ?_, ?_⟩
  · -- Injectivity on `G`.
    intro a ha b hb hTab
    by_contra hab
    have hmem : (a, b) ∈ G.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
    apply hpairs_eval (a, b) hmem
    rw [eval_innerPoly]
    have hT0 : rowMap (rowOf f) (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hTab
    have h0 : rowMap (rowOf f) (a - b) 0 = 0 := by rw [hT0]; rfl
    rwa [rowMap_apply] at h0
  · -- Zero rotational energy downstairs.
    apply rotationEnergy_image_eq_zero
    intro a ha b hb c hc e he hvw hvw' hdist
    have hmem : ((a, b), (c, e)) ∈ DPairs := by
      rw [hDPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨⟨ha, hb⟩, hc, he⟩, hvw, hvw'⟩
    exact hdpairs_eval _ hmem (eval_distClassPoly_eq_zero_of_dist_eq hdist)

end Existence

/-! ## The Near Enemy Theorem for Bisector Energy (unconditional form) -/

section Unconditional

open scoped Classical

variable {ι : Type*} [Fintype ι]

/-- **Near Enemy Theorem for Bisector Energy, general-position form**: every
finite set with no three collinear points in any Euclidean space admits a
planar projection that is injective on it and realizes the absolute minimum
bisector energy `2n(n−1)` — every unordered point-pair has a distinct
perpendicular bisector.  This is the strongest form proved here; the
sphere-slice form is the corollary below. -/
theorem nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      ∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P' := by
  obtain ⟨T, hT⟩ := nearEnemy_noThreeCollinear_exists_projectionGeneric hG
  exact ⟨T, injOn_of_projectionGeneric hT,
    nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT,
    nearEnemy_genericProjection_bisectorEnergy_minimal hT⟩

/-- **Near Enemy Theorem for Bisector Energy, sphere-slice form**: every
finite subset of a sphere in any Euclidean space admits a planar projection
that is injective on it and realizes the absolute minimum bisector energy
`2n(n−1)`.  Corollary of the general-position form: a line meets a sphere
in at most two points. -/
theorem nearEnemy_sphereSlice_exists_bisectorEnergy_minimal
    {center : EuclideanSpace ℝ ι} {R : ℝ} {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ x ∈ G, x ∈ Metric.sphere center R) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      ∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P' :=
  nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal
    fun _p₁ h₁ _p₂ h₂ _p₃ h₃ h₁₂ h₁₃ h₂₃ =>
      not_collinear_of_mem_sphere (hG _ h₁) (hG _ h₂) (hG _ h₃) h₁₂ h₁₃ h₂₃

/-- **Near Enemy Theorem for Bisector Energy, general-position-preserving
form**: every finite set with no three collinear points admits an injective
planar projection that realizes the absolute minimum bisector energy
`2n(n−1)` AND whose image again has no three collinear points.  The floor
witness is itself a general-position planar set: bisector-floor attainment
is compatible with general position at every cardinality. -/
theorem nearEnemy_exists_bisectorEnergy_minimal_image_noThreeCollinear
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P') ∧
      ∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨T, hT, htriple⟩ :=
    nearEnemy_exists_projectionGeneric_preserving_noThreeCollinear hG
  refine ⟨T, injOn_of_projectionGeneric hT,
    nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT,
    nearEnemy_genericProjection_bisectorEnergy_minimal hT, ?_⟩
  intro q₁ hq₁ q₂ hq₂ q₃ hq₃ h₁₂ h₁₃ h₂₃
  obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
  obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
  obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp hq₃
  exact htriple p₁ hp₁ p₂ hp₂ p₃ hp₃
    (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
    (fun h => h₂₃ (congrArg _ h))

/-- **Near Enemy Theorem for Bisector Energy, full-general-position form**:
every finite set with no three collinear points and every four points
affinely independent admits an injective planar projection that realizes
the absolute minimum bisector energy `2n(n−1)` AND whose image is in full
planar general position — no three collinear points and no four concyclic
points.  This is the complete general-position profile of the projected
near enemy in one statement.

The affine-independence hypothesis on quadruples is what the per-quadruple
concyclicity witness consumes; whether coplanar (but non-collinear)
quadruples also admit the witness is open here. -/
theorem nearEnemy_exists_bisectorEnergy_minimal_image_generalPosition
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)))
    (hG4 : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, ∀ p₄ ∈ G,
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
      AffineIndependent ℝ ![p₁, p₂, p₃, p₄]) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P') ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), ∀ q₄ ∈ G.image (fun x ↦ T x),
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₁ ≠ q₄ → q₂ ≠ q₃ → q₂ ≠ q₄ → q₃ ≠ q₄ →
          ¬ EuclideanGeometry.Cospherical
            ({q₁, q₂, q₃, q₄} : Set (EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨T, hT, htriple, hquad⟩ :=
    nearEnemy_exists_projectionGeneric_image_generalPosition hG hG4
  refine ⟨T, injOn_of_projectionGeneric hT,
    nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT,
    nearEnemy_genericProjection_bisectorEnergy_minimal hT, ?_, ?_⟩
  · intro q₁ hq₁ q₂ hq₂ q₃ hq₃ h₁₂ h₁₃ h₂₃
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
    obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp hq₃
    exact htriple p₁ hp₁ p₂ hp₂ p₃ hp₃
      (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
      (fun h => h₂₃ (congrArg _ h))
  · intro q₁ hq₁ q₂ hq₂ q₃ hq₃ q₄ hq₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
    obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp hq₃
    obtain ⟨p₄, hp₄, rfl⟩ := Finset.mem_image.mp hq₄
    exact hquad p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
      (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
      (fun h => h₁₄ (congrArg _ h)) (fun h => h₂₃ (congrArg _ h))
      (fun h => h₂₄ (congrArg _ h)) (fun h => h₃₄ (congrArg _ h))

end Unconditional

end NearEnemy
