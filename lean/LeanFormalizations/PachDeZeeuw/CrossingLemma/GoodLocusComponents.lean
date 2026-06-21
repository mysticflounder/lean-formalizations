/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs

/-!
# The good locus as a finite disjoint union of open intervals (`goodlocus-components`)

The generic real-line / order-topology leaf of Edge B's monotone graph decomposition
(`docs/corollary24-assembly-skeleton.md` §1.3, FLAG `goodlocus-components`). It carries
**no curve content**: the only fact used is that the cut set `Bad h` is finite.

## Statement

For a finite set `S ⊆ ℝ`, the complement `Sᶜ` is a finite, pairwise-disjoint union of open
intervals. Each component is an open interval with extended-real endpoints
`{x : ℝ | a < x ∧ x < b}` (`a b : EReal`); the two unbounded ends are absorbed by `a = ⊥`
and `b = ⊤`. The number of components is `≤ |S| + 1` (in fact exactly `|S| + 1`).

The packaging is then specialized to `S = Bad h` to give the `GoodLocus h = (Bad h)ᶜ`
component decomposition the final piece-count consumes. The specialization takes the
finiteness of `Bad h` as a hypothesis (discharged downstream by D1, `decomp_D1_bad_finite`);
nothing here re-derives it.

## Construction

Enumerate `S` in increasing order, `e = S.orderEmbOfFin : Fin n ↪o ℝ` with `n = |S|`. The
`n` "walls" `e 0 < e 1 < ⋯ < e (n-1)` split `ℝ` into `n + 1` open gaps. Index the gaps by
`Fin (n + 1)`; gap `j` is `(E j, E (j+1))` where the endpoint sequence `E : ℕ → EReal` is
`E 0 = ⊥`, `E i = e (i-1)` for `1 ≤ i ≤ n`, and `E i = ⊤` for `i ≥ n+1`. `E` is monotone, so
consecutive gaps are disjoint; the union is `Sᶜ` because a real `x` lies in exactly the gap
indexed by its rank `r = #{s ∈ S | s < x}` (the `endpt_rank` characterization below).
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open Set Finset

/-! ### The crux: rank characterization of a strictly monotone enumeration -/

/-- For a strictly monotone `e : Fin n ↪o ℝ` and a threshold `x`, the value `e i` lies below
`x` exactly when the index `i` is below the rank `r = #{i | e i < x}`. This is the statement
that `{i | e i < x}` is the initial segment `{0, …, r-1}` of `Fin n` — the engine driving both
the disjointness and the union below. -/
theorem orderEmb_lt_iff_lt_rank {n : ℕ} (e : Fin n ↪o ℝ) (x : ℝ) (i : Fin n) :
    e i < x ↔ (i : ℕ) < (Finset.univ.filter (fun j => e j < x)).card := by
  constructor
  · intro hlt
    -- every index `≤ i` qualifies, so the rank is `≥ i + 1`.
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => e j < x) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (e.monotone (Finset.mem_Iic.mp hj)) hlt
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra hge
    rw [not_lt] at hge
    -- if `x ≤ e i`, every qualifying index is `< i`, so the rank is `≤ i`.
    have hsub : Finset.univ.filter (fun j => e j < x) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      exact (e.lt_iff_lt).mp (lt_of_lt_of_le hj hge)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-! ### The endpoint sequence and its monotonicity -/

/-- The extended-real endpoint sequence for the enumeration `e : Fin n ↪o ℝ`:
`endpt n e 0 = ⊥`, `endpt n e i = e (i-1)` for `1 ≤ i ≤ n`, and `endpt n e i = ⊤` for
`i ≥ n+1`. The `n+1` gaps `(endpt n e j, endpt n e (j+1))`, `j : Fin (n+1)`, are the
components of the complement of `range e`. -/
noncomputable def endpt (n : ℕ) (e : Fin n ↪o ℝ) (i : ℕ) : EReal :=
  if i = 0 then ⊥
  else if h : i - 1 < n then ((e ⟨i - 1, h⟩ : ℝ) : EReal)
  else ⊤

@[simp] theorem endpt_zero (n : ℕ) (e : Fin n ↪o ℝ) : endpt n e 0 = ⊥ := by
  simp [endpt]

/-- For an interior index `1 ≤ i` with `i - 1 < n`, the endpoint is the wall `e (i-1)`. -/
theorem endpt_of_lt {n : ℕ} (e : Fin n ↪o ℝ) {i : ℕ} (hi : i ≠ 0) (h : i - 1 < n) :
    endpt n e i = ((e ⟨i - 1, h⟩ : ℝ) : EReal) := by
  simp [endpt, hi, h]

/-- Past the last wall the endpoint is `⊤`. -/
theorem endpt_top {n : ℕ} (e : Fin n ↪o ℝ) {i : ℕ} (hi : i ≠ 0) (h : ¬ i - 1 < n) :
    endpt n e i = ⊤ := by
  simp [endpt, hi, h]

/-- The wall `e i₀` is the endpoint at position `i₀ + 1`. -/
theorem endpt_succ {n : ℕ} (e : Fin n ↪o ℝ) (i₀ : Fin n) :
    endpt n e (i₀ + 1) = ((e i₀ : ℝ) : EReal) := by
  have hi₀ : (i₀ : ℕ) < n := i₀.isLt
  have hne : (i₀ : ℕ) + 1 ≠ 0 := by omega
  have hlt : (i₀ : ℕ) + 1 - 1 < n := by omega
  rw [endpt_of_lt e hne hlt]
  have hidx : (⟨(i₀ : ℕ) + 1 - 1, hlt⟩ : Fin n) = i₀ := by
    apply Fin.ext; show (i₀ : ℕ) + 1 - 1 = (i₀ : ℕ); omega
  rw [hidx]

/-- The endpoint sequence is monotone on `ℕ` (`⊥ ≤ e 0 ≤ ⋯ ≤ e (n-1) ≤ ⊤ ≤ ⊤ ≤ ⋯`). -/
theorem endpt_monotone (n : ℕ) (e : Fin n ↪o ℝ) : Monotone (endpt n e) := by
  apply monotone_nat_of_le_succ
  intro i
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0; simp
  · -- i ≥ 1: compare e (i-1) (or ⊤) with the next endpoint.
    have hine : i ≠ 0 := by omega
    by_cases hlt : i - 1 < n
    · -- endpt i = e (i-1); split on whether i < n.
      rw [endpt_of_lt e hine hlt]
      by_cases hlt' : i < n
      · -- endpt (i+1) = e i.
        have hne' : i + 1 ≠ 0 := by omega
        have h' : i + 1 - 1 < n := by omega
        rw [endpt_of_lt e hne' h']
        apply EReal.coe_le_coe_iff.mpr
        apply e.monotone
        simp only [Fin.mk_le_mk]; omega
      · -- i ≥ n, but i - 1 < n forces i = n; endpt (i+1) = ⊤.
        have hne' : i + 1 ≠ 0 := by omega
        have h' : ¬ i + 1 - 1 < n := by omega
        rw [endpt_top e hne' h']
        exact le_top
    · -- endpt i = ⊤ = endpt (i+1).
      rw [endpt_top e hine hlt]
      have hne' : i + 1 ≠ 0 := by omega
      have h' : ¬ i + 1 - 1 < n := by omega
      rw [endpt_top e hne' h']

/-! ### The generic real-line decomposition -/

/-- **Complement of a finite set in `ℝ` is a finite disjoint union of open intervals.**
For finite `S ⊆ ℝ`, there is a finite index family `I : ι → Set ℝ` of pairwise-disjoint open
intervals (extended-real endpoints) whose union is `Sᶜ`, with `≤ |S| + 1` components. -/
theorem finite_compl_eq_iUnion_Ioo {S : Set ℝ} (hS : S.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
      (∀ j, ∃ a b : EReal, I j = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∧
      Pairwise (Function.onFun Disjoint I) ∧
      Sᶜ = ⋃ j, I j ∧
      Fintype.card ι = hS.toFinset.card + 1 := by
  classical
  set F : Finset ℝ := hS.toFinset with hF
  set n : ℕ := F.card with hn
  set e : Fin n ↪o ℝ := F.orderEmbOfFin rfl with he
  -- `x ∈ S ↔ x ∈ range e`.
  have hmemS : ∀ x : ℝ, x ∈ S ↔ ∃ i : Fin n, e i = x := by
    intro x
    have hSF : x ∈ S ↔ x ∈ (F : Set ℝ) := by rw [hF]; simp
    have hrange : x ∈ (F : Set ℝ) ↔ ∃ i : Fin n, e i = x := by
      rw [← Finset.range_orderEmbOfFin F (rfl : F.card = n)]
      rw [he]; exact Set.mem_range
    rw [hSF, hrange]
  refine ⟨Fin (n + 1), inferInstance, fun j => {x : ℝ | endpt n e j < (x : EReal) ∧ (x : EReal) < endpt n e (j + 1)}, ?_, ?_, ?_, ?_⟩
  · -- each component is in the required EReal-Ioo form.
    intro j
    exact ⟨endpt n e j, endpt n e (j + 1), rfl⟩
  · -- pairwise disjoint: consecutive gaps cannot overlap.
    intro j j' hjj'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩
    -- WLOG j < j'; then endpt (j+1) ≤ endpt j', contradicting x < endpt (j+1) ≤ endpt j' < x.
    rcases lt_or_gt_of_ne (by exact fun h => hjj' (Fin.ext h) : (j : ℕ) ≠ (j' : ℕ)) with hlt | hlt
    · have hmono : endpt n e ((j : ℕ) + 1) ≤ endpt n e (j' : ℕ) :=
        endpt_monotone n e (by omega)
      have : ((x : EReal)) < (x : EReal) := lt_of_lt_of_le hx2 (le_trans hmono (le_of_lt hx1'))
      exact (lt_irrefl _ this)
    · have hmono : endpt n e ((j' : ℕ) + 1) ≤ endpt n e (j : ℕ) :=
        endpt_monotone n e (by omega)
      have : ((x : EReal)) < (x : EReal) := lt_of_lt_of_le hx2' (le_trans hmono (le_of_lt hx1))
      exact (lt_irrefl _ this)
  · -- union = Sᶜ.
    apply Set.eq_of_subset_of_subset
    · -- Sᶜ ⊆ ⋃: place x in the gap indexed by its rank.
      intro x hx
      rw [Set.mem_compl_iff, hmemS, not_exists] at hx
      set r : ℕ := (Finset.univ.filter (fun j => e j < x)).card with hr
      have hrle : r ≤ n := by
        rw [hr]
        calc (Finset.univ.filter (fun j => e j < x)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = n := by simp
      simp only [Set.mem_iUnion]
      refine ⟨⟨r, by omega⟩, ?_, ?_⟩
      · -- endpt r < x.
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · rw [show ((⟨r, by omega⟩ : Fin (n + 1)) : ℕ) = 0 from hr0, endpt_zero]
          exact EReal.bot_lt_coe x
        · have hrne : r ≠ 0 := by omega
          have hrm1 : r - 1 < n := by omega
          rw [show ((⟨r, by omega⟩ : Fin (n + 1)) : ℕ) = r from rfl, endpt_of_lt e hrne hrm1]
          apply EReal.coe_lt_coe_iff.mpr
          -- e ⟨r-1⟩ < x since (r-1) < r = rank.
          exact (orderEmb_lt_iff_lt_rank e x ⟨r - 1, hrm1⟩).mpr (by simp; omega)
      · -- x < endpt (r+1).
        rw [show ((⟨r, by omega⟩ : Fin (n + 1)) : ℕ) + 1 = r + 1 from rfl]
        by_cases hrn : r = n
        · have hne : r + 1 ≠ 0 := by omega
          have hnlt : ¬ r + 1 - 1 < n := by omega
          rw [endpt_top e hne hnlt]
          exact EReal.coe_lt_top x
        · have hrltn : r < n := by omega
          have hne : r + 1 ≠ 0 := by omega
          have hrm1 : r + 1 - 1 < n := by omega
          rw [endpt_of_lt e hne hrm1]
          apply EReal.coe_lt_coe_iff.mpr
          -- x ≤ e ⟨r⟩ (¬ e⟨r⟩ < x since ¬ r < r), and x ≠ e⟨r⟩ since x ∉ S.
          have hle : ¬ e ⟨r, by simpa using hrltn⟩ < x := by
            rw [orderEmb_lt_iff_lt_rank e x ⟨r, by simpa using hrltn⟩,
              show ((⟨r, by simpa using hrltn⟩ : Fin n) : ℕ) = r from rfl]
            omega
          have hne2 : x ≠ e ⟨r, by simpa using hrltn⟩ := fun h => hx _ h.symm
          have : x ≤ e ⟨r, by simpa using hrltn⟩ := not_lt.mp hle
          have hxlt : x < e ⟨r, by simpa using hrltn⟩ := lt_of_le_of_ne this hne2
          simpa using hxlt
    · -- ⋃ ⊆ Sᶜ: a gap point is not a wall.
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hx1, hx2⟩ := hx
      rw [Set.mem_compl_iff, hmemS]
      rintro ⟨i₀, rfl⟩
      -- e i₀ = endpt (i₀+1); monotonicity squeezes j between i₀ and i₀, contradiction.
      rw [← endpt_succ e i₀] at hx1 hx2
      have hlt1 : (j : ℕ) < (i₀ : ℕ) + 1 := by
        by_contra hge
        rw [not_lt] at hge
        exact absurd (endpt_monotone n e hge) (not_le.mpr hx1)
      have hlt2 : (i₀ : ℕ) + 1 < (j : ℕ) + 1 := by
        by_contra hge
        rw [not_lt] at hge
        exact absurd (endpt_monotone n e hge) (not_le.mpr hx2)
      omega
  · -- cardinality = |S| + 1.
    simp [hn, hF]

/-! ### Specialization to the good locus -/

/-- **(D1c) The good locus is a finite disjoint union of open intervals.** Specializing
`finite_compl_eq_iUnion_Ioo` to `S = Bad h` (with `GoodLocus h = (Bad h)ᶜ` definitionally):
the components are open intervals with extended-real endpoints, pairwise disjoint, finitely
many (`≤ |Bad h| + 1`), and their union is the good locus. The finiteness of `Bad h` is taken
as a hypothesis — supplied downstream by D1 (`decomp_D1_bad_finite`). -/
theorem decomp_D1_goodLocus_components (h : PlanePoly) (hbad : (Bad h).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
      (∀ j, ∃ a b : EReal, I j = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∧
      Pairwise (Function.onFun Disjoint I) ∧
      GoodLocus h = ⋃ j, I j ∧
      Fintype.card ι = hbad.toFinset.card + 1 := by
  exact finite_compl_eq_iUnion_Ioo hbad

end PachDeZeeuw.Algebraic
