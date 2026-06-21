/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Generic linear projection injective on a finite point set (node A1)

Node A1 of the Corollary 2.4 top-down route
(`docs/corollary24-edge-feasibility.md`); Pach–de Zeeuw §2.4 generic-projection
step.

For a finite set `P` of points in `EuclideanSpace ℝ (Fin D)` there is a linear
map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)` injective on
`P`. The construction is the elementary moment-curve / Vandermonde route: a
single separating linear functional
`λ_s(x) = ∑_{j < D} x_j · s^j` is injective on `P` for all but finitely many
scalars `s`, because for each nonzero difference `d = p − q` the map
`s ↦ ∑_j d_j s^j` is a nonzero polynomial of degree `< D` with finitely many
roots, and `ℝ` is infinite. The projection is then `π x = ![λ x, 0]`, whose
first coordinate already separates points.
-/

namespace PachSharir

open scoped BigOperators

variable {D : ℕ}

/-- The separating linear functional parameterized by a scalar `s`:
`λ_s(x) = ∑_{j < D} s^j · x_j`. -/
noncomputable def momentFunctional (D : ℕ) (s : ℝ) :
    EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ :=
  ∑ j : Fin D, (s ^ (j : ℕ)) • (EuclideanSpace.projₗ j : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ)

@[simp]
theorem momentFunctional_apply (s : ℝ) (x : EuclideanSpace ℝ (Fin D)) :
    momentFunctional D s x = ∑ j : Fin D, (s ^ (j : ℕ)) * x j := by
  unfold momentFunctional
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rfl

/-- The moment polynomial attached to a vector `v`: `∑_{j < D} v_j · X^j`. Its
value at `s` is `λ_s(v)`, and its `k`-th coefficient is `v_k`, so it is nonzero
whenever `v` is. -/
noncomputable def momentPoly (D : ℕ) (v : EuclideanSpace ℝ (Fin D)) : Polynomial ℝ :=
  ∑ j : Fin D, Polynomial.monomial (j : ℕ) (v j)

/-- The `k`-th coefficient of `momentPoly D v` (for `k : Fin D`) is `v k`. -/
theorem momentPoly_coeff (v : EuclideanSpace ℝ (Fin D)) (k : Fin D) :
    (momentPoly D v).coeff (k : ℕ) = v k := by
  unfold momentPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro j _ hjk
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => hjk (Fin.ext h)
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Evaluating `momentPoly D v` at `s` recovers the separating functional. -/
theorem momentPoly_eval (v : EuclideanSpace ℝ (Fin D)) (s : ℝ) :
    (momentPoly D v).eval s = momentFunctional D s v := by
  unfold momentPoly
  rw [Polynomial.eval_finsetSum]
  rw [momentFunctional_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.eval_monomial]
  ring

/-- A nonzero vector gives a nonzero moment polynomial. -/
theorem momentPoly_ne_zero {v : EuclideanSpace ℝ (Fin D)} (hv : v ≠ 0) :
    momentPoly D v ≠ 0 := by
  -- some coordinate of `v` is nonzero
  have : ∃ k : Fin D, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by ext k; simpa using h k)
  obtain ⟨k, hk⟩ := this
  intro hzero
  apply hk
  rw [← momentPoly_coeff v k, hzero, Polynomial.coeff_zero]

/-- **Engine (node A1).** A single separating linear functional injective on a
finite point set: there is `λ : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ` with
`Set.InjOn λ P`. -/
theorem exists_linearFunctional_injOn (D : ℕ) (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ lam : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ, Set.InjOn lam ↑P := by
  -- The bad scalars: roots of any difference polynomial over the off-diagonal.
  set bad : Set ℝ :=
    ⋃ pq ∈ P.offDiag, {s : ℝ | (momentPoly D (pq.1 - pq.2)).IsRoot s} with hbad
  have hbad_fin : bad.Finite := by
    rw [hbad]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 - pq.2 ≠ 0 := by
      rw [sub_ne_zero]
      exact (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOf_isRoot (momentPoly_ne_zero hne)
  obtain ⟨s₀, hs₀⟩ := hbad_fin.exists_notMem
  refine ⟨momentFunctional D s₀, ?_⟩
  intro p hp q hq hpq
  by_contra hne
  -- `p ≠ q` but `λ p = λ q`, so `p − q` is nonzero and `s₀` is a root.
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr (fun h => hne (by rw [h]))
  apply hs₀
  rw [hbad]
  rw [Set.mem_iUnion₂]
  refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq,
    sub_ne_zero.mp hdiff⟩, ?_⟩
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
  rw [momentPoly_eval, map_sub, hpq, sub_self]

/-- **Headline (node A1).** A generic linear projection is injective on a finite
point set: there is a linear map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ]
EuclideanSpace ℝ (Fin 2)` with `Set.InjOn π P`. -/
theorem exists_linearProjection_injOn (D : ℕ) (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2), Set.InjOn π ↑P := by
  obtain ⟨lam, hlam⟩ := exists_linearFunctional_injOn D P
  -- `π x = ![λ x, 0]`, whose first coordinate already separates points.
  refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
    (LinearMap.pi ![lam, 0]), ?_⟩
  intro p hp q hq hpqeq
  refine hlam hp hq ?_
  -- read off the first coordinate of the image equality
  have h0 : (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.pi ![lam, 0])) p) 0 =
      (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.pi ![lam, 0])) q) 0 := by rw [hpqeq]
  simpa using h0

/-! ### Rank-2 strengthening (conditions (1)∧(2) of strengthened-A1)

The headline above produces a `π` with image in a single line, so it is *not*
surjective. The strengthened-A1 node of the Corollary 2.4 route
(`docs/corollary24-A4a-adjudication.md` §6.1) needs `π` to additionally have rank
2 (be surjective onto `ℝ²`). The construction pairs the separating functional `λ`
with a second functional `μ` chosen linearly independent from it (possible since
`D ≥ 2` makes the dual space at least `2`-dimensional): `InjOn` is inherited from
the `λ`-coordinate, and surjectivity follows from independence of the pair. Only
conditions (1) (surjective) and (2) (`InjOn`) are established here; condition (3)
of §6.1 (secant-cone / BAD-avoidance, which is entangled with the canonical
eliminant `F_γ`) is a separate node and is *not* addressed by this theorem. -/

/-- An independent pair of linear functionals `f, g : ℝ^D → ℝ` assembles, via
`LinearMap.pi`, to a linear map `ℝ^D → (Fin 2 → ℝ)` that is surjective. The
argument is the transpose criterion `LinearMap.dualMap_injective_iff`: the dual
map sends a covector `φ` to the combination `∑ i, φ(eᵢ) • ![f, g] i`, which
vanishes only when both coefficients do, by independence of `![f, g]`. -/
theorem surjective_pi_of_linearIndependent
    (f g : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) (hfg : LinearIndependent ℝ ![f, g]) :
    Function.Surjective
      (LinearMap.pi ![f, g] : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] (Fin 2 → ℝ)) := by
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro φ hφ
  simp only [LinearMap.mem_ker] at hφ
  set c : Fin 2 → ℝ := fun i => φ (Pi.single i 1) with hc
  have hcomb : (LinearMap.pi ![f, g]).dualMap φ = ∑ i, c i • ![f, g] i := by
    ext v
    rw [LinearMap.dualMap_apply]
    have harg : (LinearMap.pi ![f, g]) v = ∑ i, ((![f, g] i) v) • Pi.single i (1 : ℝ) := by
      funext j
      simp [LinearMap.pi_apply, Pi.single_apply, Finset.sum_apply]
    rw [harg, map_sum]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]
    simp only [hc, smul_eq_mul]
    ring
  rw [hcomb] at hφ
  have hci : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hfg c hφ
  ext x
  simpa [hc] using hci x

/-- For `D ≥ 2`, any nonzero linear functional `f : ℝ^D → ℝ` extends to a pair
`![g, f]` that is linearly independent in the dual space. The new functional `g`
is the first entry and the given `f` the second. Uses
`exists_linearIndependent_cons_of_lt_rank` together with `dim (dual) = D > 1`. -/
theorem exists_linearIndependent_pair_of_ne_zero (hD : 2 ≤ D)
    (f : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ g : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ, LinearIndependent ℝ ![g, f] := by
  have h1 : LinearIndependent ℝ ![f] := linearIndependent_unique_iff.mpr hf
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) = D := by
      rw [Module.finrank_linearMap]
      simp [finrank_euclideanSpace]
    rw [← Module.finrank_eq_rank]
    have hD' : (1 : ℕ) < D := by omega
    exact_mod_cast hfr ▸ hD'
  obtain ⟨g, hg⟩ := exists_linearIndependent_cons_of_lt_rank h1 (by exact_mod_cast hrank)
  refine ⟨g, ?_⟩
  have hcons : Fin.cons g ![f] = ![g, f] := by funext i; fin_cases i <;> rfl
  rwa [hcons] at hg

/-- **Strengthened-A1, conditions (1)∧(2).** For `D ≥ 2` and a finite point set
`P` there is a linear map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ
(Fin 2)` that is **surjective** (rank 2) **and** injective on `P`. This is the
rank-2 strengthening of `exists_linearProjection_injOn`: the separating functional
`λ` of `exists_linearFunctional_injOn` is completed to an independent pair, which
makes the assembled map surjective while `λ`'s coordinate still separates `P`.

Condition (3) of `docs/corollary24-A4a-adjudication.md` §6.1 (secant-cone
avoidance, entangled with the canonical eliminant) is **not** established here. -/
theorem exists_rank2_projection_injOn (hD : 2 ≤ D)
    (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Function.Surjective π ∧ Set.InjOn π ↑P := by
  obtain ⟨lam, hlam⟩ := exists_linearFunctional_injOn D P
  by_cases hlam0 : lam = 0
  · -- `λ = 0`: then `InjOn λ P` forces `P` to be a subsingleton, so any rank-2
    -- `π` is injective on `P`. Seed surjectivity with the (nonzero) functional
    -- `proj 0`, completed to an independent pair.
    have hproj0 : (EuclideanSpace.projₗ (⟨0, by omega⟩ : Fin D) :
        EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h
      have hev := congrArg
        (fun L => L (EuclideanSpace.single (⟨0, by omega⟩ : Fin D) (1 : ℝ))) h
      simp only [LinearMap.zero_apply] at hev
      rw [show (EuclideanSpace.projₗ (⟨0, by omega⟩ : Fin D)
            (EuclideanSpace.single (⟨0, by omega⟩ : Fin D) (1 : ℝ)))
          = EuclideanSpace.single (⟨0, by omega⟩ : Fin D) (1 : ℝ) (⟨0, by omega⟩ : Fin D)
            from rfl] at hev
      rw [PiLp.single_apply] at hev
      simp at hev
    obtain ⟨g, hg⟩ := exists_linearIndependent_pair_of_ne_zero hD _ hproj0
    refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
      (LinearMap.pi ![g, (EuclideanSpace.projₗ (⟨0, by omega⟩ : Fin D))]), ?_, ?_⟩
    · rw [LinearMap.coe_comp]
      exact (LinearEquiv.surjective _).comp (surjective_pi_of_linearIndependent _ _ hg)
    · intro p hp q hq _
      exact hlam hp hq (by rw [hlam0]; rfl)
  · -- `λ ≠ 0`: complete `λ` to an independent pair `![g, λ]`. The assembled map
    -- is surjective, and its second coordinate is `λ`, which separates `P`.
    obtain ⟨g, hg⟩ := exists_linearIndependent_pair_of_ne_zero hD lam hlam0
    refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
      (LinearMap.pi ![g, lam]), ?_, ?_⟩
    · rw [LinearMap.coe_comp]
      exact (LinearEquiv.surjective _).comp (surjective_pi_of_linearIndependent _ _ hg)
    · intro p hp q hq hpqeq
      refine hlam hp hq ?_
      -- read off the second coordinate of the image equality
      have h1 : (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
            (LinearMap.pi ![g, lam])) p) 1 =
          (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
            (LinearMap.pi ![g, lam])) q) 1 := by rw [hpqeq]
      simpa using h1

end PachSharir
