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

/-! ## Per-quadruple genericity certificate -/

/-- **Per-quadruple certificate**: for two distinct chords of one sphere (the
first nondegenerate), the two identical-vanishing conditions that a
bisector-coincidence under projection would force cannot BOTH hold: the
projected-determinant form (parallelism) and the orthogonality form
(midpoint relation) are not simultaneously identically zero over all row
vectors.

This is the input the existence-of-a-generic-projection argument consumes:
for each off-pair quadruple, at least one of the two constraint polynomials
in the projection entries is not identically zero, so a generic projection
avoids the coincidence.  Contrapositive assembly of the coefficient lemma,
the parallelism lemma, and sphere rigidity. -/
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
  -- Sphere rigidity closes the contradiction.
  exact hne (nearEnemy_sphereSlice_parallel_midpoint_eq_samePair ha hb hc he hmid hpar)

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

end NearEnemy
