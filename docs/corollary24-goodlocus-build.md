# `goodlocus-components` build record — good locus as a finite disjoint union of open intervals

Author: Adam McKenna (adam-apple@flounder.net)
Date: 2026-06-20
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`

**Status: CLOSED (PROVEN).** The generic real-line / order-topology leaf of Edge B's
monotone graph decomposition (`docs/corollary24-assembly-skeleton.md` §1.3, FLAG
`goodlocus-components`) is proven, sorry-free and axiom-clean. It carries no curve content;
the only input is finiteness of the cut set.

File: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/GoodLocusComponents.lean`
Wired via: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean` (aggregator import, after
`DecompositionDefs`).

---

## 1. Formulation chosen

The deliverable is the FLAG's `decomp_D1_goodLocus_components` shape: a finite index family of
pairwise-disjoint open intervals (extended-real endpoints) whose union is the complement.
Two theorems:

1. a **curve-agnostic** generic lemma `finite_compl_eq_iUnion_Ioo` over an arbitrary finite
   `S ⊆ ℝ`, and
2. the **specialization** `decomp_D1_goodLocus_components` to `S = Bad h`, using
   `GoodLocus h = (Bad h)ᶜ` definitionally.

Endpoints are `EReal` so the two unbounded ends `(−∞, min S)` and `(max S, +∞)` are expressed
uniformly (`a = ⊥`, `b = ⊤`); the component predicate is
`{x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}`, matching the FLAG byte-for-byte. The index type
is `Fin (n + 1)` with `n = |S|`, so the component count is reported as the exact equality
`Fintype.card ι = |S| + 1` (hence `≤ |S| + 1`).

### Final signatures

```lean
namespace PachDeZeeuw.Algebraic

/-- Complement of a finite set in `ℝ` is a finite disjoint union of open intervals. -/
theorem finite_compl_eq_iUnion_Ioo {S : Set ℝ} (hS : S.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
      (∀ j, ∃ a b : EReal, I j = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∧
      Pairwise (Function.onFun Disjoint I) ∧
      Sᶜ = ⋃ j, I j ∧
      Fintype.card ι = hS.toFinset.card + 1

/-- (D1c) The good locus is a finite disjoint union of open intervals.
`(Bad h).Finite` is a hypothesis — supplied downstream by D1 (`decomp_D1_bad_finite`). -/
theorem decomp_D1_goodLocus_components (h : PlanePoly) (hbad : (Bad h).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
      (∀ j, ∃ a b : EReal, I j = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∧
      Pairwise (Function.onFun Disjoint I) ∧
      GoodLocus h = ⋃ j, I j ∧
      Fintype.card ι = hbad.toFinset.card + 1
```

### Deviation from the FLAG's exact signature (stated, not smuggled)

The FLAG draft of `decomp_D1_goodLocus_components` took `(hirr) (hdeg) (hpy)` and re-derived
finiteness internally. That re-derivation is `decomp_D1_bad_finite`, which is **not landed**
(it routes through the in-flight `B-crit` + `chart-bridge`). To keep this file fully closed
and sorry-free, the specialization instead takes `(hbad : (Bad h).Finite)` directly. This is
strictly the faithful packaging: it isolates the only nontrivial input (finiteness) as a named
hypothesis to be discharged by D1 when it lands, and it changes nothing about the conclusion.
The generic lemma `finite_compl_eq_iUnion_Ioo` is unconditional.

---

## 2. Supporting declarations (all in-file, sorry-free)

| Declaration | Statement |
|---|---|
| `orderEmb_lt_iff_lt_rank` | for strict-mono `e : Fin n ↪o ℝ`: `e i < x ↔ (i:ℕ) < #{j | e j < x}` |
| `endpt` | the `EReal` endpoint sequence `ℕ → EReal`: `⊥`, then walls `e (i-1)`, then `⊤` |
| `endpt_zero`/`endpt_of_lt`/`endpt_top`/`endpt_succ` | the four defining cases of `endpt` |
| `endpt_monotone` | `Monotone (endpt n e)` on `ℕ` (`⊥ ≤ e 0 ≤ ⋯ ≤ e (n-1) ≤ ⊤`) |

---

## 3. Proof structure

Let `F = hS.toFinset`, `n = |F|`, `e = F.orderEmbOfFin rfl : Fin n ↪o ℝ` (strict mono, with
`Set.range e = F`). The `n` walls `e 0 < ⋯ < e (n-1)` split `ℝ` into `n+1` open gaps, indexed
by `Fin (n+1)`; gap `j` is `(endpt j, endpt (j+1))`.

- **Rank engine (`orderEmb_lt_iff_lt_rank`).** `{i | e i < x}` is a down-set in `Fin n`
  (strict monotonicity), hence an initial segment of size `r = #{i | e i < x}`. Both
  directions are pure counting against `Fin.card_Iic`/`Fin.card_Iio` (`Iic i ⊆ filter` forces
  `r ≥ i+1`; `filter ⊆ Iio i` forces `r ≤ i`).
- **Monotonicity (`endpt_monotone`).** `monotone_nat_of_le_succ` over the four index regimes
  (`0`, interior, the `i=n` step to `⊤`, and `≥ n+1`), index arithmetic by `omega`.
- **Predicate form.** Immediate: gap `j` is `{x | endpt j < x ∧ x < endpt (j+1)}`, witnesses
  `a = endpt j`, `b = endpt (j+1)`.
- **Disjointness.** For `j < j'`, `endpt (j+1) ≤ endpt j'` by monotonicity, so a common point
  gives `x < endpt (j+1) ≤ endpt j' < x` — contradiction.
- **Union = `Sᶜ`.**
  - `⊇`: a gap point `x` is not a wall, since `e i₀ = endpt (i₀+1)` and monotonicity squeezes
    the gap index `j` to satisfy `i₀ < j ≤ i₀`.
  - `⊆`: for `x ∉ S`, the gap index is the rank `r = #{i | e i < x}` (`r ≤ n`); the left
    bound `endpt r < x` and right bound `x < endpt (r+1)` come from the rank engine, with the
    right bound's strictness using `x ∉ S` (so `x ≠ e ⟨r⟩`).

The argument uses **finiteness of `S`** essentially (to enumerate via `orderEmbOfFin` and to
get `Fintype (Fin (n+1))`); no other structural assumption.

---

## 4. Verification

Build (green, zero warnings):

```
./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.GoodLocusComponents
# Build completed successfully (8482 jobs).
```

Axiom closure (`#print axioms`, via a scratch probe, since removed):

```
'PachDeZeeuw.Algebraic.finite_compl_eq_iUnion_Ioo'    depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.decomp_D1_goodLocus_components' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.orderEmb_lt_iff_lt_rank'        depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.endpt_monotone'                 depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or custom axioms anywhere in the file.

---

## 5. Downstream

`decomp_D1_goodLocus_components` is the component-decomposition form the final piece-count
packaging consumes. It is non-blocking for D2/D3 (those are stated against "any `Ioo α β`
disjoint from `Bad`", per the assembly skeleton). Its sole open dependency is the
`(Bad h).Finite` hypothesis, discharged by `decomp_D1_bad_finite` (FLAGs `infroot-finite` +
`crit-finite-projection`) once those land.
