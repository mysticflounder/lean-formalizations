/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear

/-!
# Finiteness of the bad-shear set for a single curve (`generic-rotation` step 2)

The per-curve "bad scalar set is finite" brick of Edge B's generic-direction WLOG
(`docs/corollary24-generic-rotation-scope.md` §3.2). The downstream `exists_good_shear`
will `Set.Finite.biUnion` this over a finite curve family and pick a scalar in the
complement (`Set.Finite.exists_notMem`), so the finite-set shape proved here is exactly
what is consumed.

## The deliverable

> `partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :`
> `    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite`

`shearPoly s h = aeval (x ↦ x + s·y, y ↦ y) h` is the scope-doc shear (`Shear.lean`).
For a scalar `s` the curve `{shearPoly s h = 0}` genuinely involves `y`
(`pderiv (1 : Fin 2) (shearPoly s h) ≠ 0`) for all but finitely many `s`.

## The route (scope §3.2, EMPIRICALLY VERIFIED in `/tmp/shear_fix.py`)

Let `D := h.totalDegree ≥ 1` (so `h ≠ 0`). Substituting `x ↦ x + s·y`, `y ↦ y`, the
coefficient of the pure `y^D` monomial `Finsupp.single (1 : Fin 2) D` in `shearPoly s h`,
as a function of `s`, is the univariate real polynomial

> `P(s) = ∑_{a+b=D} (coeff of x^a y^b in h) · s^a = H(s, 1)`,

where `H` is the top homogeneous part of `h`. Only the top-degree monomials `x^a y^b`
(`a + b = D`) contribute a pure `y^D` term; each contributes `coeff · s^a · y^D`. Distinct
top monomials have distinct `a` (since `b = D − a`), so `P` is the zero polynomial iff
`H = 0`; since `D = totalDegree h` and `h ≠ 0`, `P ≠ 0`.

`P` (here `shearTopPoly h`) is a nonzero real univariate polynomial, hence has finitely
many roots (`Polynomial.finite_setOf_isRoot`). For `s` not a root of `P`, the `y^D`
coefficient of `shearPoly s h` is `P(s) ≠ 0`; since `D ≥ 1`, this forces
`pderiv (1 : Fin 2) (shearPoly s h) ≠ 0` (the chain
`pderiv 1 g = 0 ⟹ (D : ℝ) · coeff (single 1 D) g = 0 ⟹ coeff (single 1 D) g = 0`, via
`X 1 * pderiv 1 g`). Therefore the bad set is contained in the finite root set of `P`.

All names live in `PachDeZeeuw.Algebraic`; `PlanePoly`, `shearPoly` resolve unqualified
(matching `Shear.lean`).
-/

namespace PachDeZeeuw.Algebraic

open MvPolynomial

/-! ### Bridge facts on `Fin 2` finsupp degrees -/

/-- For `m : Fin 2 →₀ ℕ`, the monomial degree `∑ᵢ mᵢ` is `m 0 + m 1`. -/
private theorem msum_eq (m : Fin 2 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum, ← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- `∑ i ∈ (single 1 D).support, (single 1 D) i = D`. -/
private theorem sum_support_single (D : ℕ) :
    ∑ i ∈ (Finsupp.single (1 : Fin 2) D).support, (Finsupp.single (1 : Fin 2) D) i = D := by
  rw [← Finsupp.degree_apply, Finsupp.degree_single]

/-! ### The pure-`y^D` coefficient of a sheared monomial -/

/-- The pure-`y^a` coefficient of `(X₀ + s·X₁)^a` is `s^a`. By induction on `a`: the
top `y`-power of `(X₀ + s·X₁)^(n+1) = (X₀ + s·X₁)^n · (X₀ + s·X₁)` comes only from the
`s·X₁` factor (the `· X₀` term has `X₀`-degree `≥ 1`, so its `single 1 (n+1)` coefficient
vanishes), shifting the inductive `s^n` to `s^(n+1)`. -/
private theorem coeff_single_one_pow (s : ℝ) (a : ℕ) :
    coeff (Finsupp.single (1 : Fin 2) a) ((X 0 + C s * X 1) ^ a) = s ^ a := by
  classical
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, coeff_add]
    have hX0 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * X 0) = 0 := by
      rw [coeff_mul_X', if_neg]; simp [Finsupp.mem_support_iff]
    have hX1 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * (C s * X 1))
        = s ^ (n + 1) := by
      rw [show (X 0 + C s * X 1 : PlanePoly) ^ n * (C s * X 1)
            = C s * ((X 0 + C s * X 1) ^ n * X 1) by ring, coeff_C_mul,
          show (Finsupp.single (1 : Fin 2) (n + 1))
            = (Finsupp.single (1 : Fin 2) n) + (Finsupp.single (1 : Fin 2) 1) by
              rw [← Finsupp.single_add], coeff_mul_X, ih]
      ring
    rw [hX0, hX1, zero_add]

/-- The shear applied to a single monomial: `aeval (x ↦ x + s·y, y ↦ y) (monomial m c)`
expands to `C c · (X₀ + s·X₁)^(m 0) · X₁^(m 1)`. -/
private theorem shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    shearPoly s (monomial m c) = C c * (X 0 + C s * X 1) ^ (m 0) * (X 1) ^ (m 1) := by
  unfold shearPoly shearVars
  rw [aeval_monomial, MvPolynomial.algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [Fin.prod_univ_two, Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  ring

/-- The pure-`y^(a+b)` coefficient of the sheared monomial `shearPoly s (monomial m c)`
(with `a = m 0`, `b = m 1`) is `c · s^a`. The `X₁^b` factor shifts `single 1 (a+b)` down
to `single 1 a`, then `coeff_single_one_pow` evaluates the binomial top coefficient. -/
private theorem coeff_yD_shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) (m 0 + m 1)) (shearPoly s (monomial m c))
      = c * s ^ (m 0) := by
  classical
  rw [shear_monomial, X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    show (Finsupp.single (1 : Fin 2) (m 0 + m 1))
        = (Finsupp.single (1 : Fin 2) (m 0)) + (Finsupp.single (1 : Fin 2) (m 1)) by
        rw [← Finsupp.single_add],
    coeff_mul_monomial, coeff_single_one_pow, mul_one]

/-- If a monomial `m` has degree `m 0 + m 1 < D` then the pure-`y^D` coefficient of
`shearPoly s (monomial m c)` is `0`: the shear does not raise total degree
(`shearPoly_totalDegree_le`), so the image has total degree `≤ m 0 + m 1 < D`, below the
degree `D` of `single 1 D`. -/
private theorem coeff_yD_shear_monomial_lt (s : ℝ) (D : ℕ) (m : Fin 2 →₀ ℕ) (c : ℝ)
    (hlt : m 0 + m 1 < D) :
    coeff (Finsupp.single (1 : Fin 2) D) (shearPoly s (monomial m c)) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [sum_support_single]
  refine lt_of_le_of_lt (shearPoly_totalDegree_le s (monomial m c)) ?_
  refine lt_of_le_of_lt (totalDegree_monomial_le m c) ?_
  rw [Function.id_def, msum_eq]
  exact hlt

/-! ### The `s`-polynomial `P` whose roots bound the bad set -/

/-- `shearTopPoly h` is the univariate real polynomial `P(s) = H(s, 1)` — the pure-`y^D`
coefficient of `shearPoly s h` read as a polynomial in `s`. It is the sum, over the
degree-`D` support monomials `x^a y^b` (`a + b = D = totalDegree h`), of
`(coeff of x^a y^b) · X^a`. -/
noncomputable def shearTopPoly (h : PlanePoly) : Polynomial ℝ :=
  ∑ m ∈ h.support, (if m 0 + m 1 = h.totalDegree then
    Polynomial.C (coeff m h) * Polynomial.X ^ (m 0) else 0)

/-- **The coefficient identity.** The pure-`y^D` coefficient of `shearPoly s h`
(`D = totalDegree h`), as a function of `s`, is `(shearTopPoly h).eval s`. Expand
`shearPoly s h` over `h.support` by linearity; each support monomial contributes
`coeff m h · s^(m 0)` when its degree is `D` (`coeff_yD_shear_monomial`) and `0` when its
degree is `< D` (`coeff_yD_shear_monomial_lt`); this matches `shearTopPoly h` evaluated. -/
theorem coeff_yD_shear_eq_eval (h : PlanePoly) (s : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) h.totalDegree) (shearPoly s h)
      = (shearTopPoly h).eval s := by
  classical
  set D := h.totalDegree with hD
  have hexp : shearPoly s h
      = ∑ m ∈ h.support, shearPoly s (monomial m (coeff m h)) := by
    conv_lhs => rw [h.as_sum]
    rw [shearPoly, map_sum]
    rfl
  rw [hexp, coeff_sum, shearTopPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hle : m 0 + m 1 ≤ D := by
    rw [hD, ← msum_eq m]; exact le_totalDegree hm
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [if_pos (heq.trans hD)]
    have hidx : (Finsupp.single (1 : Fin 2) D) = Finsupp.single (1 : Fin 2) (m 0 + m 1) := by
      rw [heq]
    rw [hidx, coeff_yD_shear_monomial]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  · rw [if_neg (by omega), coeff_yD_shear_monomial_lt s D m (coeff m h) hlt]
    simp

/-- **`P ≠ 0`.** A nonzero `h` has a support monomial `m₀` of degree `D = totalDegree h`
with `coeff m₀ h ≠ 0`. Among degree-`D` monomials, `m₀ 0` determines the monomial (its
`y`-exponent is `D − m₀ 0`), so the `X^(m₀ 0)` coefficient of `shearTopPoly h` is exactly
`coeff m₀ h ≠ 0`; hence `shearTopPoly h ≠ 0`. -/
theorem shearTopPoly_ne_zero (h : PlanePoly) (hh : h ≠ 0) : shearTopPoly h ≠ 0 := by
  classical
  set D := h.totalDegree with hD
  have hne : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m0, hm0, hsup⟩ :=
    Finset.exists_mem_eq_sup h.support hne (fun s => s.sum fun _ e => e)
  have hm0deg : m0 0 + m0 1 = D := by rw [← msum_eq m0, ← hsup]; rfl
  have hcoeff0 : coeff m0 h ≠ 0 := MvPolynomial.mem_support_iff.mp hm0
  intro hzero
  apply hcoeff0
  have hkey : (shearTopPoly h).coeff (m0 0) = coeff m0 h := by
    rw [shearTopPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single m0]
    · rw [if_pos hm0deg, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro m _ hmm0
      by_cases hmd : m 0 + m 1 = D
      · rw [if_pos hmd, Polynomial.coeff_C_mul_X_pow, if_neg]
        intro hm00
        apply hmm0
        have hm00' : m 0 = m0 0 := hm00.symm
        have hm1 : m 1 = m0 1 := by omega
        apply Finsupp.ext
        intro i
        match i with
        | 0 => exact hm00'
        | 1 => exact hm1
      · rw [if_neg hmd, Polynomial.coeff_zero]
    · intro hm
      exact absurd hm0 (by rw [MvPolynomial.notMem_support_iff] at hm ⊢; exact hm)
  rw [hzero, Polynomial.coeff_zero] at hkey
  exact hkey.symm

/-! ### From a nonzero `y^D` coefficient to `pderiv 1 ≠ 0` -/

/-- `coeff m (X i · ∂ᵢ g) = (m i) • coeff m g`. Expand `g` over its support; on each
monomial `X i · ∂ᵢ (monomial v c) = (v i) • monomial v c` (`X_mul_pderiv_monomial`), and
extracting `coeff m` keeps only the `v = m` term. -/
private theorem coeff_X_mul_pderiv (i : Fin 2) (g : PlanePoly) (m : Fin 2 →₀ ℕ) :
    coeff m (X i * pderiv i g) = (m i) • coeff m g := by
  classical
  have hexp : X i * pderiv i g
      = ∑ v ∈ g.support, (v i) • monomial v (coeff v g) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [X_mul_pderiv_monomial]
  rw [hexp, coeff_sum]
  simp only [coeff_smul, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro v _ hvm
    rw [if_neg (fun h => hvm h), smul_zero]
  · intro hm
    rw [notMem_support_iff] at hm
    rw [if_pos rfl, hm, smul_zero]

/-- If `pderiv (1 : Fin 2) g = 0` and `D ≥ 1` then the pure-`y^D` coefficient of `g`
vanishes. From `coeff_X_mul_pderiv`, `pderiv 1 g = 0` gives
`(single 1 D) 1 • coeff (single 1 D) g = D • coeff (single 1 D) g = 0`; with `D ≥ 1` the
real coefficient is forced to `0`. -/
private theorem coeff_yD_eq_zero_of_pderiv_eq_zero (g : PlanePoly) (D : ℕ) (hD : 1 ≤ D)
    (h0 : pderiv (1 : Fin 2) g = 0) :
    coeff (Finsupp.single (1 : Fin 2) D) g = 0 := by
  have hco := coeff_X_mul_pderiv (1 : Fin 2) g (Finsupp.single (1 : Fin 2) D)
  rw [h0, mul_zero, coeff_zero] at hco
  rw [Finsupp.single_eq_same, nsmul_eq_mul] at hco
  have hDpos : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hco.symm).resolve_left hDpos

/-! ### The deliverable -/

/-- **`partialY_shearPoly_finite_bad` (generic-rotation step 2).** The set of real scalars
`s` for which the sheared curve `shearPoly s h` fails to involve `y`
(`pderiv (1 : Fin 2) (shearPoly s h) = 0`) is finite, for any curve `h` with
`1 ≤ totalDegree h`.

The bad set is contained in the real-root set of `shearTopPoly h`: for a bad `s`,
`coeff_yD_eq_zero_of_pderiv_eq_zero` makes the pure-`y^D` coefficient of `shearPoly s h`
vanish, which by the identity `coeff_yD_shear_eq_eval` is exactly `(shearTopPoly h).eval s`,
so `s` is a root. `shearTopPoly h ≠ 0` (`shearTopPoly_ne_zero`, using `h ≠ 0` from
`1 ≤ totalDegree h`), so its root set is finite (`Polynomial.finite_setOf_isRoot`); the bad
set, a subset, is finite (`Set.Finite.subset`). -/
theorem partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :
    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite := by
  have hh : h ≠ 0 := by
    intro h0
    rw [h0, totalDegree_zero] at hpos
    exact absurd hpos (by norm_num)
  have hPne : shearTopPoly h ≠ 0 := shearTopPoly_ne_zero h hh
  apply Set.Finite.subset (Polynomial.finite_setOf_isRoot hPne)
  intro s hs
  simp only [Set.mem_setOf_eq] at hs ⊢
  -- s is a root of shearTopPoly h.
  rw [Polynomial.IsRoot.def, ← coeff_yD_shear_eq_eval]
  exact coeff_yD_eq_zero_of_pderiv_eq_zero (shearPoly s h) h.totalDegree hpos hs

end PachDeZeeuw.Algebraic
