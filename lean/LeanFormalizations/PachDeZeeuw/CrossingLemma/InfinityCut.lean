/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.StripCompact

/-!
# The infinity-cut set `Inf_x(h)` and its containment in `{lc_y(h) = 0}` (`uinf-containment`)

The `U_∞` term of Edge B's generic monotone graph decomposition
(`docs/corollary24-decomposition-spec.md`, §2.3, FLAG `uinf-containment`).

A plane curve `γ = {evalPlane h = 0}` can break into separate x-monotone sheets at an
x-value `c` not because of any affine critical point but because a branch escapes to
`y = ±∞` as `x → c` (the `xy = 1` hyperbola at `x = 0`, spec §2.2). This file pins the
precise set of such x-values and bounds it.

## The definition

`Inf_x(h)` is the set of `c ∈ ℝ` at which the curve has a **vertical asymptote**:

> `c ∈ Inf_x(h)` iff for every `δ > 0` and every `M`, there is a curve point `(x, y)`
> with `|x − c| < δ` and `|y| > M`.

That is: every neighborhood `(c − δ, c + δ)` of `c` has curve points of arbitrarily
large `|y|`; the strip over each neighborhood of `c` is unbounded in `y`. This is exactly
"a branch escapes to `y = ±∞` as `x → c`": for any target height `M` and any closeness
`δ`, there is a curve point that close in `x` and that high in `|y|`. (The doc's §2.3
phrasing "for every `R > 0` and every `δ > 0` there is `(x,y) ∈ γ` with `|x − c| < δ` and
`|y| > R`" is this verbatim, with `R = M`.)

## The containment (`uinf-containment`)

> `Inf_x(h) ⊆ { c | lc_y(h)(c) = 0 }`,

where `lc_y(h) = yLeadCoeff h ∈ MvPolynomial (Fin 1) ℝ` is the leading coefficient of `h`
as a polynomial in `y` (`StripCompact.lean`). Proof by contrapositive on the foundational
strip-compactness lemma: if `lc_y(h)(c) ≠ 0`, then by continuity of
`x ↦ lc_y(h)(x)` (`continuous_evalCoeff`) it is nonzero on a whole closed interval
`[c − ε, c + ε]`; `isCompact_strip` then makes the strip over that interval bounded in
`y` (`exists_uniform_y_bound`), giving a finite height bound `B`; so no branch over a
`< ε` neighborhood of `c` can exceed `M := B`, i.e. `c ∉ Inf_x(h)`.

## Finiteness and the degree bound

When `lc_y(h) ≠ 0` (i.e. `h` genuinely involves `y`), the bounding set
`{ c | lc_y(h)(c) = 0 }` is the real-root set of the **nonzero** univariate polynomial
`XCoeffEquiv (lc_y(h)) ∈ ℝ[X]` (the `AlgebraicPrelim.XCoeffEquiv` bridge
`MvPolynomial (Fin 1) ℝ ≃+* ℝ[X]`, already used in `StripCompact.lean`). Hence it is
finite of cardinality `≤ (XCoeffEquiv (lc_y h)).natDegree`, and therefore so is
`Inf_x(h)`.

The hypothesis `yLeadCoeff h ≠ 0` is essential and kept honest: if `h ∈ ℝ[x]` carries no
`y` then `lc_y(h) = 0`, the containment target is **all** of `ℝ`, and there is no degree
bound — the generic-rotation step (spec §1.4) is what excludes that case upstream.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### The infinity-cut set -/

/-- **The infinity-cut set.** `c ∈ InfX h` iff the curve `{evalPlane h = 0}` has a
vertical asymptote at `x = c`: for every closeness `δ > 0` and every height `M`, there is
a curve point `(x, y)` with `|x − c| < δ` and `|y| > M`. Equivalently, the strip over
every neighborhood of `c` is unbounded in `y`. -/
def InfX (h : PlanePoly) : Set ℝ :=
  {c : ℝ | ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
      ∃ x y : ℝ, |x - c| < δ ∧ M < |y| ∧ evalPlane h (x, y) = 0}

theorem mem_InfX {h : PlanePoly} {c : ℝ} :
    c ∈ InfX h ↔
      ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
        ∃ x y : ℝ, |x - c| < δ ∧ M < |y| ∧ evalPlane h (x, y) = 0 :=
  Iff.rfl

/-! ### Containment in the zero set of `lc_y(h)` -/

/-- The leading-coefficient-in-`y` function `x ↦ lc_y(h)(x)`, nonzero at `c`, is nonzero
on a whole **closed** interval `[c − ε, c + ε]` for some `ε > 0`. (Continuity of the
real univariate polynomial `XCoeffEquiv (lc_y h)`, via `continuous_evalCoeff`.) -/
theorem exists_closedInterval_yLeadCoeff_ne_zero (h : PlanePoly) {c : ℝ}
    (hc : MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Set.Icc (c - ε) (c + ε),
        MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := by
  -- The nonvanishing locus of the continuous function `g x = lc_y(h)(x)` is open and
  -- contains `c`, so it contains a metric ball; halve its radius to land inside a closed
  -- interval.
  set g : ℝ → ℝ := fun x => MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) with hg
  have hgc : Continuous g := continuous_evalCoeff (yLeadCoeff h)
  have hopen : IsOpen {x : ℝ | g x ≠ 0} := isOpen_ne.preimage hgc
  have hmem : {x : ℝ | g x ≠ 0} ∈ 𝓝 c := hopen.mem_nhds hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r / 2, by positivity, fun x hx => ?_⟩
  -- `x ∈ [c − r/2, c + r/2] ⊆ ball c r`, so `g x ≠ 0`.
  have hxball : x ∈ Metric.ball c r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    obtain ⟨hxl, hxu⟩ := Set.mem_Icc.mp hx
    constructor <;> linarith
  exact hball hxball

/-- **`uinf-containment` (main).** Every vertical-asymptote x-value of the curve is a root
of the leading coefficient of `h` in `y`:
`Inf_x(h) ⊆ { c | lc_y(h)(c) = 0 }`.

Proof by contrapositive on `isCompact_strip`/`exists_uniform_y_bound`: if `lc_y(h)(c) ≠ 0`
then `lc_y(h)` is nonzero on a closed interval `[c − ε, c + ε]`
(`exists_closedInterval_yLeadCoeff_ne_zero`), so the strip over it is bounded in `y` by
some `B` (`exists_uniform_y_bound`); the asymptote condition at `δ = ε`, `M = B` would
then produce a curve point with `|x − c| < ε` (hence `x ∈ [c − ε, c + ε]`) and `|y| > B ≥
|y|`, a contradiction. -/
theorem InfX_subset_yLeadCoeff_zeroSet (h : PlanePoly) :
    InfX h ⊆ {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0} := by
  intro c hc
  by_contra hne
  rw [Set.mem_setOf_eq] at hne
  -- `lc_y(h)` is nonzero throughout a closed interval `[c − ε, c + ε]`.
  obtain ⟨ε, hεpos, hεne⟩ := exists_closedInterval_yLeadCoeff_ne_zero h hne
  -- Hence the strip over `[c − ε, c + ε]` is uniformly `y`-bounded by some `B`.
  obtain ⟨B, hB⟩ := exists_uniform_y_bound h (xP := c - ε) (xQ := c + ε) hεne
  -- The asymptote condition at `δ = ε`, `M = B` yields a curve point exceeding `B`.
  obtain ⟨x, y, hxδ, hyM, hzero⟩ := (mem_InfX.mp hc) ε hεpos B
  -- `|x − c| < ε` puts `x` in the closed interval `[c − ε, c + ε]`.
  have hxIcc : x ∈ Set.Icc (c - ε) (c + ε) := by
    rw [Set.mem_Icc]
    rw [abs_sub_lt_iff] at hxδ
    constructor <;> linarith [hxδ.1, hxδ.2]
  -- But then `|y| ≤ B`, contradicting `B < |y|`.
  have hyle : |y| ≤ B := hB x hxIcc y hzero
  linarith

/-! ### Finiteness and the degree bound -/

/-- Bridge: the zero set of `lc_y(h)` (as a real-coefficient evaluation) is the **root
set** of the univariate polynomial `XCoeffEquiv (lc_y h) ∈ ℝ[X]`. -/
theorem yLeadCoeff_zeroSet_eq_isRoot (h : PlanePoly) :
    {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}
      = {c : ℝ | (XCoeffEquiv (yLeadCoeff h)).IsRoot c} := by
  ext c
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
  rw [coeffEval_eq_eval_XCoeffEquiv c (yLeadCoeff h)]
  rfl

/-- When `lc_y(h) ≠ 0`, its zero set is **finite** (the real roots of the nonzero
univariate polynomial `XCoeffEquiv (lc_y h)`). -/
theorem finite_yLeadCoeff_zeroSet (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}.Finite := by
  rw [yLeadCoeff_zeroSet_eq_isRoot h]
  have hpne : XCoeffEquiv (yLeadCoeff h) ≠ 0 :=
    fun h0 => hlc (XCoeffEquiv.map_eq_zero_iff.mp h0)
  exact Polynomial.finite_setOf_isRoot hpne

/-- The zero set of `lc_y(h)` has at most `(XCoeffEquiv (lc_y h)).natDegree` points
(roots of a nonzero univariate polynomial). -/
theorem ncard_yLeadCoeff_zeroSet_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}.ncard
      ≤ (XCoeffEquiv (yLeadCoeff h)).natDegree := by
  classical
  have hpne : XCoeffEquiv (yLeadCoeff h) ≠ 0 :=
    fun h0 => hlc (XCoeffEquiv.map_eq_zero_iff.mp h0)
  set p : Polynomial ℝ := XCoeffEquiv (yLeadCoeff h) with hp
  -- Rewrite the zero set as the root set, then as the coercion of `p.roots.toFinset`.
  have hset : {c : ℝ | MvPolynomial.eval (fun _ : Fin 1 => c) (yLeadCoeff h) = 0}
      = (↑p.roots.toFinset : Set ℝ) := by
    rw [yLeadCoeff_zeroSet_eq_isRoot h, ← hp]
    ext c
    simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, Finset.mem_coe,
      Polynomial.mem_roots hpne]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le p.roots).trans (p.card_roots')

/-- **`U_∞` finiteness + bound.** If `h` genuinely involves `y` (`yLeadCoeff h ≠ 0`), the
infinity-cut set `Inf_x(h)` is finite with `ncard ≤ (XCoeffEquiv (lc_y h)).natDegree`. -/
theorem finite_InfX (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) : (InfX h).Finite :=
  (finite_yLeadCoeff_zeroSet h hlc).subset (InfX_subset_yLeadCoeff_zeroSet h)

theorem ncard_InfX_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfX h).ncard ≤ (XCoeffEquiv (yLeadCoeff h)).natDegree :=
  le_trans
    (Set.ncard_le_ncard (InfX_subset_yLeadCoeff_zeroSet h) (finite_yLeadCoeff_zeroSet h hlc))
    (ncard_yLeadCoeff_zeroSet_le h hlc)

/-! ### The coarse degree bound `≤ totalDegree h` -/

/-- The univariate `x`-degree of `lc_y(h)` is at most the total degree of `h` in `y`.
(`MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le` on the `y`-leading coefficient, with
`rename`-invariance of total degree.) Needs `yLeadCoeff h ≠ 0`. -/
theorem totalDegree_yLeadCoeff_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (yLeadCoeff h).totalDegree ≤ h.totalDegree := by
  -- `yLeadCoeff h` is the `natDegree`-th coefficient of `finSuccEquiv (rename swap2 h)`.
  have hcoeff : yLeadCoeff h
      = (MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.rename swap2 h)).coeff (Curry1 h).natDegree := by
    rw [yLeadCoeff, Polynomial.leadingCoeff, Curry1]
  have hne : (MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.rename swap2 h)).coeff
      (Curry1 h).natDegree ≠ 0 := by rw [← hcoeff]; exact hlc
  have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
    (MvPolynomial.rename swap2 h) (Curry1 h).natDegree hne
  -- `rename` by the (involutive) coordinate swap preserves total degree.
  have hren : (MvPolynomial.rename swap2 h).totalDegree = h.totalDegree := by
    apply le_antisymm
    · exact MvPolynomial.totalDegree_rename_le swap2 h
    · have hback : MvPolynomial.rename swap2 (MvPolynomial.rename swap2 h) = h := by
        rw [MvPolynomial.rename_rename]
        have hid : (swap2 ∘ swap2) = (id : Fin 2 → Fin 2) := by
          funext i; fin_cases i <;> simp [swap2]
        rw [hid, MvPolynomial.rename_id, AlgHom.id_apply]
      calc h.totalDegree
          = (MvPolynomial.rename swap2 (MvPolynomial.rename swap2 h)).totalDegree := by rw [hback]
        _ ≤ (MvPolynomial.rename swap2 h).totalDegree :=
            MvPolynomial.totalDegree_rename_le swap2 _
  rw [hren] at hle
  rw [hcoeff]
  exact le_trans (Nat.le_add_right _ _) hle

/-- The univariate polynomial `XCoeffEquiv (lc_y h)` has degree at most `totalDegree h`.
(`(XCoeffEquiv r).natDegree = degreeOf 0 r ≤ totalDegree r`, then
`totalDegree_yLeadCoeff_le`.) Needs `yLeadCoeff h ≠ 0`. -/
theorem natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (XCoeffEquiv (yLeadCoeff h)).natDegree ≤ h.totalDegree := by
  have hstep : (XCoeffEquiv (yLeadCoeff h)).natDegree ≤ (yLeadCoeff h).totalDegree := by
    calc
      (XCoeffEquiv (yLeadCoeff h)).natDegree
          = ((MvPolynomial.finSuccEquiv ℝ 0) (yLeadCoeff h)).natDegree := by
        simpa [XCoeffEquiv] using
          (Polynomial.natDegree_map_eq_of_injective
            ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.injective)
            ((MvPolynomial.finSuccEquiv ℝ 0) (yLeadCoeff h)))
      _ = MvPolynomial.degreeOf 0 (yLeadCoeff h) := by
        simpa using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) (yLeadCoeff h))
      _ ≤ (yLeadCoeff h).totalDegree := MvPolynomial.degreeOf_le_totalDegree (yLeadCoeff h) 0
  exact le_trans hstep (totalDegree_yLeadCoeff_le h hlc)

/-- **`U_∞(d) ≤ d` (the spec's headline bound).** If `h` genuinely involves `y`, the
infinity-cut set is finite with `ncard ≤ totalDegree h`. -/
theorem ncard_InfX_le_totalDegree (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfX h).ncard ≤ h.totalDegree :=
  le_trans (ncard_InfX_le h hlc) (natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree h hlc)

/-! ### Faithfulness witness: the `xy = 1` asymptote -/

/-- **Faithfulness witness (spec §2.2).** For the hyperbola `xy = 1`
(`h = X₀·X₁ − 1`), the asymptote x-value `0` lies in `InfX h`: the branch `y = 1/x`
over `x → 0⁺` escapes to `+∞`. Concretely, for any `δ > 0` and any height `M`, taking
`x = min (δ/2) (1/(max M 0 + 1))` and `y = 1/x` gives a curve point with `|x| < δ` and
`|y| > M`. This shows the definition genuinely detects vertical asymptotes; combined with
`InfX_subset_yLeadCoeff_zeroSet` and `lc_y(xy−1) = X` (whose only root is `0`), it pins
`InfX (X₀·X₁ − 1) = {0}` exactly — the corrected cut producing the two monotone branches
`x < 0`, `x > 0`. -/
theorem mem_InfX_hyperbola : (0 : ℝ) ∈ InfX (MvPolynomial.X 0 * MvPolynomial.X 1 - 1) := by
  rw [mem_InfX]
  intro δ hδ M
  -- Choose `x` small positive with `x < δ` and `1/x > max M 0`.
  set R : ℝ := max M 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  set x : ℝ := min (δ / 2) (1 / R) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  refine ⟨x, 1 / x, ?_, ?_, ?_⟩
  · -- `|x − 0| = x ≤ δ/2 < δ`.
    rw [sub_zero, abs_of_pos hxpos]
    calc x ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  · -- `M < |1/x|`: from `x ≤ 1/R` we get `R ≤ 1/x`, and `M < R`.
    rw [abs_of_pos (by positivity)]
    have hxle : x ≤ 1 / R := min_le_right _ _
    have hRle : R ≤ 1 / x := by
      rw [le_div_iff₀ hxpos]
      calc R * x ≤ R * (1 / R) := by nlinarith [hxle, hRpos.le]
        _ = 1 := by field_simp
    have hMR : M < R := by rw [hR]; have := le_max_left M 0; linarith
    linarith
  · -- `evalPlane (X₀·X₁ − 1) (x, 1/x) = x·(1/x) − 1 = 0`.
    simp only [evalPlane, map_sub, map_mul, MvPolynomial.eval_X, map_one,
      if_true, if_neg (by decide : ¬ (1 : Fin 2) = 0)]
    rw [mul_one_div, div_self (ne_of_gt hxpos), sub_self]

end PachDeZeeuw.Algebraic
