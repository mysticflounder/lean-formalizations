/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultigraph

/-!
# `WellDrawn` for the Edge-B drawn multigraph

The curve port of the line-case `stMultigraph_wellDrawn`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean`), generalizing the line case's
"≤ 1 intersection per distinct pair" to "≤ M intersections per distinct curve
pair." Goal:

    edgeBMultigraph_wellDrawn : (edgeBMultigraph d M P Γ).WellDrawn

i.e. `crossingCount (edgeBMultigraph d M P Γ) ≤ M * Γ.card ^ 2`. The crossings
field is already `M * Γ.card ^ 2`, so `WellDrawn` reduces to
`crossingCount ≤ M * Γ.card ^ 2`.

See `docs/corollary24-edgeB-welldrawn-build.md` for the build record and the
hypothesis-form decision.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma
open scoped Classical

/-! ### 1. Strict `x`-sortedness of `pointsOnSheet` over a good interval

The curve port of the line case's `pointsOnLine_pairwise_lt` / `pointsOnLine_getElem_lt`
(`SzemerediTrotter.lean`): the sort key is the `x`-coordinate `(·.1)` (not `lineKey`),
and the strict-separation replacement for `lineKey_injOn` is `sheetRank_injOn_fibre`
— two rank-`j` on-curve points of `P` over the same good `x` have equal `y`, hence are
equal. -/

/-- `pointsOnSheet P h α β j` is sorted (non-strict) by the `x`-coordinate. Direct
from `List.pairwise_mergeSort` for the transitive total comparator
`decide (p.1 ≤ q.1)`. -/
lemma pointsOnSheet_pairwise_le (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (pointsOnSheet P h α β j).Pairwise (fun p q => p.1 ≤ q.1) := by
  unfold pointsOnSheet
  have hs := List.pairwise_mergeSort
      (l := (P.filter (fun p => p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j)).toList)
      (le := fun p q => decide (p.1 ≤ q.1))
      (trans := by intro a b c h1 h2; simp only [decide_eq_true_eq] at h1 h2 ⊢; linarith)
      (total := by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total a.1 b.1)
  exact hs.imp (fun {a b} hab => by simpa using hab)

/-- **Strict `x`-sortedness.** Over a good interval `(α,β)` (`hgood`), distinct points
of `pointsOnSheet P h α β j` have distinct `x`-coordinates (`sheetRank_injOn_fibre`),
so the list is *strictly* sorted by `x`. -/
lemma pointsOnSheet_pairwise_lt {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) :
    (pointsOnSheet P h α β j).Pairwise (fun p q => p.1 < q.1) := by
  have hLE := pointsOnSheet_pairwise_le P h α β j
  have hND : (pointsOnSheet P h α β j).Pairwise (fun a b => a ≠ b) := pointsOnSheet_nodup P h α β j
  have hBoth := hLE.and hND
  apply hBoth.imp_of_mem
  intro a b ha hb ⟨hle, hne⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso; apply hne
    rw [mem_pointsOnSheet] at ha hb
    obtain ⟨_, ha_curve, ha_io, ha_rank⟩ := ha
    obtain ⟨_, hb_curve, _, hb_rank⟩ := hb
    -- `a.1 = b.1 =: x` is good, both points are on the fibre at rank `j`.
    have hbad : a.1 ∉ Bad h := hgood a.1 ha_io
    have ha_fib : a.2 ∈ Fibre h a.1 := by
      rw [Fibre, Set.mem_setOf_eq]; simpa using (mem_evalPlaneZeroSet.mp ha_curve)
    have hb_fib : b.2 ∈ Fibre h a.1 := by
      rw [Fibre, Set.mem_setOf_eq, heq]; simpa using (mem_evalPlaneZeroSet.mp hb_curve)
    have hrank : sheetRank h a.1 a.2 = sheetRank h a.1 b.2 := by rw [ha_rank, heq, hb_rank]
    have hy : a.2 = b.2 := sheetRank_injOn_fibre h hbad ha_fib hb_fib hrank
    exact Prod.ext heq hy

/-- **Strict sortedness, indexed form.** For `i < j` into `pointsOnSheet`, the
`x`-coordinates are strictly ordered. -/
lemma pointsOnSheet_getElem_lt {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) {i k : ℕ}
    (hi : i < (pointsOnSheet P h α β j).length) (hk : k < (pointsOnSheet P h α β j).length)
    (hik : i < k) :
    (pointsOnSheet P h α β j)[i].1 < (pointsOnSheet P h α β j)[k].1 :=
  (List.pairwise_iff_getElem.mp (pointsOnSheet_pairwise_lt hgood)) i k hi hk hik

/-! ### 2. Same-class (same curve, interval, rank) x-interval disjointness

Distinct consecutive edges of one `edgesOnSheet P h α β j` have disjoint open
`x`-intervals. Curve port of `edgesOnLine_lineKey_separated` /
`edgesOnLine_interior_disjoint` / `edgesOnLine_bare_disjoint`, with the `x`-coordinate
`(·.1)` as the sort key. -/

/-- An edge of `edgesOnSheet` is the consecutive `pointsOnSheet` pair at its index.
Curve port of `edgesOnLine_getElem` (`edgesOnSheet` has the identical `zip … tail`
shape). -/
theorem edgesOnSheet_getElem (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) (i : ℕ)
    (hi : i < (edgesOnSheet P h α β j).length) :
    ∃ (_ : i < (pointsOnSheet P h α β j).length) (_ : i + 1 < (pointsOnSheet P h α β j).length),
      (edgesOnSheet P h α β j)[i] = ((pointsOnSheet P h α β j)[i], (pointsOnSheet P h α β j)[i+1]) := by
  set l := pointsOnSheet P h α β j with hl
  have hilen : i < (l.zip l.tail).length := hi
  rw [List.length_zip] at hilen
  have hkl : i < l.length := lt_of_lt_of_le hilen (min_le_left _ _)
  have hktail : i < l.tail.length := lt_of_lt_of_le hilen (min_le_right _ _)
  rw [List.length_tail] at hktail
  have hk1 : i + 1 < l.length := by omega
  refine ⟨hkl, hk1, ?_⟩
  have hget : (edgesOnSheet P h α β j)[i] = (l.zip l.tail)[i]'(by rw [List.length_zip]; exact hilen) := rfl
  rw [hget, List.getElem_zip]
  congr 1
  rw [List.getElem_tail]

/-- **Separation between distinct same-class edges (indexed).** For `i < k`, the
right `x`-endpoint of edge `i` is `≤` the left `x`-endpoint of edge `k`. -/
lemma edgesOnSheet_xseparated {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) {i k : ℕ}
    (hi : i < (edgesOnSheet P h α β j).length) (hk : k < (edgesOnSheet P h α β j).length)
    (hik : i < k) :
    ((edgesOnSheet P h α β j)[i]).2.1 ≤ ((edgesOnSheet P h α β j)[k]).1.1 := by
  obtain ⟨hi₁, hi₂, hgeti⟩ := edgesOnSheet_getElem P h α β j i hi
  obtain ⟨hj₁, _, hgetj⟩ := edgesOnSheet_getElem P h α β j k hk
  rw [hgeti, hgetj]
  -- Need `pts[i+1].1 ≤ pts[k].1`. Sortedness with `i + 1 ≤ k`: strict if `i+1<k`, eq if `i+1=k`.
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hik) with hlt | heq
  · exact le_of_lt (pointsOnSheet_getElem_lt hgood hi₂ hj₁ hlt)
  · subst heq; exact le_refl _

/-- **Same-class x-interval disjointness (indexed).** Two distinct edges of one
`edgesOnSheet P h α β j` have disjoint open `x`-intervals. -/
lemma edgesOnSheet_xIntervals_disjoint_idx {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) {i k : ℕ}
    (hi : i < (edgesOnSheet P h α β j).length) (hk : k < (edgesOnSheet P h α β j).length)
    (hik : i ≠ k) :
    Disjoint (Set.Ioo ((edgesOnSheet P h α β j)[i]).1.1 ((edgesOnSheet P h α β j)[i]).2.1)
             (Set.Ioo ((edgesOnSheet P h α β j)[k]).1.1 ((edgesOnSheet P h α β j)[k]).2.1) := by
  rw [Set.disjoint_left]
  intro x hxi hxk
  -- Symmetrize: w.l.o.g. `i < k`.
  wlog hik' : i < k generalizing i k with H
  · exact H hk hi hik.symm hxk hxi (lt_of_le_of_ne (Nat.le_of_not_lt hik') (Ne.symm hik))
  -- Separation `edge i .2.1 ≤ edge k .1.1`, but `x < edge i .2.1` and `edge k .1.1 < x`.
  have hsep : ((edgesOnSheet P h α β j)[i]).2.1 ≤ ((edgesOnSheet P h α β j)[k]).1.1 :=
    edgesOnSheet_xseparated hgood hi hk hik'
  exact absurd (lt_of_lt_of_le hxi.2 (le_trans hsep hxk.1.le)) (lt_irrefl _)

/-- **Same-class x-interval disjointness (bare).** Two distinct edges
`e₁ ≠ e₂` of `edgesOnSheet P h α β j` have disjoint open `x`-intervals. Conveniently
shaped for the same-curve disjointness argument. -/
lemma edgesOnSheet_xIntervals_disjoint {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {e₁ e₂ : (ℝ × ℝ) × (ℝ × ℝ)}
    (he₁ : e₁ ∈ edgesOnSheet P h α β j) (he₂ : e₂ ∈ edgesOnSheet P h α β j) (hne : e₁ ≠ e₂) :
    Disjoint (Set.Ioo e₁.1.1 e₁.2.1) (Set.Ioo e₂.1.1 e₂.2.1) := by
  rw [List.mem_iff_getElem] at he₁ he₂
  obtain ⟨i, hi, hgi⟩ := he₁
  obtain ⟨k, hk, hgk⟩ := he₂
  have hik : i ≠ k := by intro hkeq; subst hkeq; rw [hgi] at hgk; exact hne hgk
  have hcore := edgesOnSheet_xIntervals_disjoint_idx hgood hi hk hik
  rw [hgi, hgk] at hcore
  exact hcore

/-! ### 3. Good-interval brackets: no overlap ⟹ equal bracket

Two entries of `goodIntervalsBundle H` whose open brackets share a point `x` have the
same bracket value. This is the structural fact that lets the same-curve case avoid
threading the component index into the per-edge payload: a shared interior point pins
both edges to the same `(α,β)`, hence the same `edgesOnSheet` list. The proof unfolds
the bundle, recovers each entry's good-locus component `I (component j)`, and uses the
`Pairwise (onFun Disjoint)` of `decomp_D1_goodLocus_components` to force the same
component, hence the same deterministic `realBracketOfEReal` bracket. -/

/-- The canonical good-locus component index type of a curve `H`, as extracted by
`goodIntervalsBundle` from `decomp_D1_goodLocus_components` via `Classical.choose`.
Two references to this are the same term, so component indices are comparable. -/
noncomputable def compIdx {d : ℕ} (H : EdgeBCurve d) : Type :=
  Classical.choose (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H))

/-- The canonical `Fintype (compIdx H)` instance from `decomp_D1_goodLocus_components`
(its second `Classical.choose`). Matches the instance `goodIntervalsBundle` uses. -/
noncomputable instance compFintype {d : ℕ} (H : EdgeBCurve d) : Fintype (compIdx H) :=
  Classical.choose (Classical.choose_spec
    (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H)))

/-- The canonical good-locus component family `I : compIdx H → Set ℝ` of `H`. -/
noncomputable def compSet {d : ℕ} (H : EdgeBCurve d) : compIdx H → Set ℝ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H))))

/-- The deterministic real bracket of component `jcomp`: `realBracketOfEReal (xBound P)`
of the chosen EReal endpoints of `compSet H jcomp`. The bracket `goodIntervalsBundle P H`
stores for an entry from `jcomp` is exactly this — so `jcomp` (with `P`) determines the
bracket value. Threads `P` to match the `P`-aware brackets. -/
noncomputable def bracketOfComp {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    (jcomp : compIdx H) : ℝ × ℝ :=
  let hIfull := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H))))
  (realBracketOfEReal (xBound P) (Classical.choose (hIfull.1 jcomp))
    (Classical.choose (Classical.choose_spec (hIfull.1 jcomp)))).1

/-- `compSet H jcomp` is the open EReal-bracket interval whose `realBracketOfEReal (xBound P)`
is `bracketOfComp P H jcomp`. -/
lemma compSet_eq {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) (jcomp : compIdx H) :
    ∃ a b : EReal, compSet H jcomp = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} ∧
      bracketOfComp P H jcomp = (realBracketOfEReal (xBound P) a b).1 ∧
      Set.Ioo (bracketOfComp P H jcomp).1 (bracketOfComp P H jcomp).2 ⊆ compSet H jcomp := by
  set hIfull := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H)))) with hh
  refine ⟨Classical.choose (hIfull.1 jcomp),
    Classical.choose (Classical.choose_spec (hIfull.1 jcomp)), ?_, rfl, ?_⟩
  · exact Classical.choose_spec (Classical.choose_spec (hIfull.1 jcomp))
  · -- `Ioo bracket ⊆ {x | a<x<b} = compSet H jcomp`.
    have hbr := (realBracketOfEReal (xBound P) (Classical.choose (hIfull.1 jcomp))
      (Classical.choose (Classical.choose_spec (hIfull.1 jcomp)))).2
    have hcomp : compSet H jcomp = {x : ℝ | (Classical.choose (hIfull.1 jcomp)) < (x : EReal) ∧
        (x : EReal) < (Classical.choose (Classical.choose_spec (hIfull.1 jcomp)))} :=
      Classical.choose_spec (Classical.choose_spec (hIfull.1 jcomp))
    rw [hcomp]; exact hbr

/-- `compSet H` is pairwise disjoint. -/
lemma compSet_pairwise_disjoint {d : ℕ} (H : EdgeBCurve d) :
    Pairwise (Function.onFun Disjoint (compSet H)) := by
  have hfull := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H))))
  exact hfull.2.1

/-- **Distinct bundle positions have disjoint open brackets.** Two entries of
`goodIntervalsBundle H` at distinct list positions have disjoint `Ioo` brackets
(`compSet_pairwise_disjoint` + each bracket `⊆` its component). The structural fact
behind `allCurveEdges` nodup. -/
lemma goodIntervalsBundle_pairwise_disjoint_Ioo {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (goodIntervalsBundle P H).Pairwise
      (fun gi₁ gi₂ => Disjoint (Set.Ioo gi₁.1.1 gi₁.1.2) (Set.Ioo gi₂.1.1 gi₂.1.2)) := by
  -- Pairwise over the underlying `univ.toList` (nodup) mapped to entries; distinct
  -- component indices give disjoint components, hence disjoint sub-brackets.
  rw [goodIntervalsBundle, List.pairwise_map]
  have hnd : (Finset.univ : Finset (compIdx H)).toList.Pairwise (· ≠ ·) := Finset.nodup_toList _
  apply hnd.imp_of_mem
  intro jc₁ jc₂ _ _ hjne
  obtain ⟨_, _, _, _, hsub₁⟩ := compSet_eq P H jc₁
  obtain ⟨_, _, _, _, hsub₂⟩ := compSet_eq P H jc₂
  have hdisjC : Disjoint (compSet H jc₁) (compSet H jc₂) := compSet_pairwise_disjoint H hjne
  -- The mapped entry's `.1` bracket is `bracketOfComp H jc` by `rfl` (same choose chain).
  refine Set.disjoint_left.mpr (fun x hx₁ hx₂ => ?_)
  exact (Set.disjoint_left.mp hdisjC) (hsub₁ hx₁) (hsub₂ hx₂)

/-- For each entry `gi` of `goodIntervalsBundle H`, there is a component index `jcomp`
with `gi.1 = bracketOfComp H jcomp` and `Ioo gi.1 ⊆ compSet H jcomp`. Re-derives the
component containment `goodIntervalsBundle`'s own proof discards. -/
lemma goodIntervalsBundle_mem_component {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    {gi : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1}
    (hgi : gi ∈ goodIntervalsBundle P H) :
    ∃ jcomp : compIdx H, gi.1 = bracketOfComp P H jcomp ∧
      Set.Ioo gi.1.1 gi.1.2 ⊆ compSet H jcomp := by
  rw [goodIntervalsBundle, List.mem_map] at hgi
  obtain ⟨jcomp, _hjcomp, hgieq⟩ := hgi
  refine ⟨jcomp, ?_, ?_⟩
  · -- `gi.1 = (realBracketOfEReal (xBound P) a b).1 = bracketOfComp P H jcomp`, by unfolding both.
    rw [← hgieq]; rfl
  · obtain ⟨a, b, _hcompeq, hval, hsub⟩ := compSet_eq P H jcomp
    have hgi1 : gi.1 = bracketOfComp P H jcomp := by rw [← hgieq]; rfl
    rw [hgi1]; exact hsub

/-- **No overlap ⟹ equal bracket.** Two entries `gi₁, gi₂` of `goodIntervalsBundle H`
whose open brackets both contain `x` have equal bracket value `gi₁.1 = gi₂.1`. -/
lemma goodIntervalsBundle_no_overlap {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    {gi₁ gi₂ : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1}
    (hgi₁ : gi₁ ∈ goodIntervalsBundle P H) (hgi₂ : gi₂ ∈ goodIntervalsBundle P H)
    {x : ℝ} (hx₁ : x ∈ Set.Ioo gi₁.1.1 gi₁.1.2) (hx₂ : x ∈ Set.Ioo gi₂.1.1 gi₂.1.2) :
    gi₁.1 = gi₂.1 := by
  obtain ⟨jc₁, hval₁, hsub₁⟩ := goodIntervalsBundle_mem_component P H hgi₁
  obtain ⟨jc₂, hval₂, hsub₂⟩ := goodIntervalsBundle_mem_component P H hgi₂
  -- Shared `x` lands in both components, so they coincide by pairwise disjointness.
  have hxc₁ : x ∈ compSet H jc₁ := hsub₁ hx₁
  have hxc₂ : x ∈ compSet H jc₂ := hsub₂ hx₂
  have hjeq : jc₁ = jc₂ := by
    by_contra hjne
    exact (Set.disjoint_left.mp (compSet_pairwise_disjoint H hjne)) hxc₁ hxc₂
  rw [hval₁, hval₂, hjeq]

/-! ### 4. Provenance recovery from `allCurveEdges`

For an edge `Ed ∈ allCurveEdges d P Γ`, recover the curve `H ∈ Γ` it came from and
the good-interval bundle entry `gi ∈ goodIntervalsBundle H` whose bracket is
`(Ed.α, Ed.β)`. Unfolds the double `flatMap`/`map`/`attach` of `allCurveEdges` and
`classKeys`. This is what lets the same-curve case apply `goodIntervalsBundle_no_overlap`
(which needs genuine bundle entries, not just the stored bracket values). -/

/-- **Provenance.** Every `Ed ∈ allCurveEdges d P Γ` comes from some `H ∈ Γ` with
`Ed.h = H.1` and some bundle entry `gi ∈ goodIntervalsBundle H` whose bracket is
`(Ed.α, Ed.β)`. -/
lemma allCurveEdges_provenance {d : ℕ} {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {Ed : EdgeBEdge P} (hEd : Ed ∈ allCurveEdges d P Γ) :
    ∃ H ∈ Γ, Ed.h = H.1 ∧
      ∃ gi : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1,
        gi ∈ goodIntervalsBundle P H ∧ Ed.α = gi.1.1 ∧ Ed.β = gi.1.2 := by
  rw [allCurveEdges, List.mem_flatMap] at hEd
  obtain ⟨H, hHmem, hEd2⟩ := hEd
  rw [List.mem_flatMap] at hEd2
  obtain ⟨key, hkeymem, hEd3⟩ := hEd2
  rw [List.mem_map] at hEd3
  obtain ⟨se, _hsemem, hEdeq⟩ := hEd3
  -- `key ∈ classKeys d H`: unfold to its bundle entry `gi` and rank.
  rw [classKeys, List.mem_flatMap] at hkeymem
  obtain ⟨gi, hgimem, hkey2⟩ := hkeymem
  rw [List.mem_map] at hkey2
  obtain ⟨jr, _hjrmem, hkeyeq⟩ := hkey2
  -- `Ed = { h := H.1, α := key.1.1, β := key.1.2, … }`, `key = ⟨gi.1, ⟨gi.2, jr⟩⟩`.
  refine ⟨H, Finset.mem_toList.mp hHmem, ?_, gi, hgimem, ?_, ?_⟩
  · rw [← hEdeq]
  · rw [← hEdeq]; simp only; rw [← hkeyeq]
  · rw [← hEdeq]; simp only; rw [← hkeyeq]

/-- `edgesOnSheet P h α β j` is `Nodup`: distinct indices give distinct consecutive
pairs (`pointsOnSheet_nodup`). Curve port of `edgesOnLine_nodup`. -/
lemma edgesOnSheet_nodup (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (edgesOnSheet P h α β j).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i k hi hk hik
  obtain ⟨_, _, hgeti⟩ := edgesOnSheet_getElem P h α β j i hi
  obtain ⟨_, _, hgetk⟩ := edgesOnSheet_getElem P h α β j k hk
  rw [hgeti, hgetk]
  intro hcontra
  have h1 : (pointsOnSheet P h α β j)[i] = (pointsOnSheet P h α β j)[k] := by
    have := congrArg Prod.fst hcontra; simpa using this
  have hnd := pointsOnSheet_nodup P h α β j
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
  exact hnd i k _ _ hik h1

/-- The innermost per-(curve, bracket, rank) edge list of `allCurveEdges`, factored
out so the reassociated triple `flatMap` for the nodup proof reads cleanly. -/
noncomputable def innerEdgeList {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    (gi : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) (j : ℕ) : List (EdgeBEdge P) :=
  (edgesOnSheet P H.1 gi.1.1 gi.1.2 j).attach.map (fun se =>
    { h := H.1, α := gi.1.1, β := gi.1.2, hgood := gi.2, j := j, e := se.1, hmem := se.2 })

/-- Every edge of `innerEdgeList` has its stored fields pinned to `(H, gi, j)`. -/
lemma innerEdgeList_fields {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    (gi : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) (j : ℕ)
    {Ed : EdgeBEdge P} (hEd : Ed ∈ innerEdgeList P H gi j) :
    Ed.h = H.1 ∧ Ed.α = gi.1.1 ∧ Ed.β = gi.1.2 ∧ Ed.j = j := by
  rw [innerEdgeList, List.mem_map] at hEd
  obtain ⟨se, _, hEdeq⟩ := hEd
  rw [← hEdeq]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- `innerEdgeList` is `Nodup`: `attach` is nodup (`edgesOnSheet_nodup`), and the map
is injective (equal `EdgeBEdge` ⟹ equal `.e`). -/
lemma innerEdgeList_nodup {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    (gi : Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) (j : ℕ) :
    (innerEdgeList P H gi j).Nodup := by
  rw [innerEdgeList, List.nodup_map_iff_inj_on]
  · intro se₁ _ se₂ _ heq
    exact Subtype.ext (congrArg EdgeBEdge.e heq)
  · exact (edgesOnSheet_nodup P H.1 gi.1.1 gi.1.2 j).attach

/-- The per-curve edge block of `allCurveEdges` reassociated: the inner `classKeys`
`flatMap` equals a `goodIntervalsBundle`-then-`range` double `flatMap` of
`innerEdgeList`. From `classKeys`'s definition + `flatMap`/`map` reassociation. -/
lemma curveBlock_eq {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    ((classKeys d P H).flatMap (fun key =>
      (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).attach.map (fun se =>
        ({ h := H.1, α := key.1.1, β := key.1.2, hgood := key.2.1, j := key.2.2,
           e := se.1, hmem := se.2 } : EdgeBEdge P))))
      = (goodIntervalsBundle P H).flatMap (fun gi =>
          (List.range (d + 1)).flatMap (fun j => innerEdgeList P H gi j)) := by
  rw [classKeys, List.flatMap_assoc]
  congr 1; ext gi
  rw [List.flatMap_map]
  rfl

/-- **Per-curve block nodup.** The edge block of a single curve `H` is `Nodup`.
Distinct ranks give different `.j` (`nodup_range`); distinct bundle positions give
disjoint brackets (`goodIntervalsBundle_pairwise_disjoint_Ioo`), so a shared edge —
whose left endpoint lies in both brackets — is impossible. -/
lemma curveBlock_nodup {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    ((goodIntervalsBundle P H).flatMap (fun gi =>
      (List.range (d + 1)).flatMap (fun j => innerEdgeList P H gi j))).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · -- For each `gi`, the `range`-`flatMap` of `innerEdgeList` is nodup.
    intro gi _
    rw [List.nodup_flatMap]
    refine ⟨fun j _ => innerEdgeList_nodup P H gi j, ?_⟩
    -- Distinct ranks ⟹ disjoint (different `.j`).
    apply (List.nodup_range (n := d + 1)).imp_of_mem
    intro j₁ j₂ _ _ hjne
    rw [Function.onFun, List.disjoint_left]
    intro Ed hEd₁ hEd₂
    have hf₁ := innerEdgeList_fields P H gi j₁ hEd₁
    have hf₂ := innerEdgeList_fields P H gi j₂ hEd₂
    exact hjne (by rw [← hf₁.2.2.2, hf₂.2.2.2])
  · -- Distinct bundle positions ⟹ disjoint brackets ⟹ disjoint edge blocks.
    apply (goodIntervalsBundle_pairwise_disjoint_Ioo P H).imp_of_mem
    intro gi₁ gi₂ _ _ hdisj
    rw [Function.onFun, List.disjoint_left]
    intro Ed hEd₁ hEd₂
    -- `Ed` in both blocks ⟹ its bracket is both `gi₁.1` and `gi₂.1`; its left endpoint
    -- lies in both `Ioo`, contradicting their disjointness.
    rw [List.mem_flatMap] at hEd₁ hEd₂
    obtain ⟨j₁, _, hEd₁'⟩ := hEd₁
    obtain ⟨j₂, _, hEd₂'⟩ := hEd₂
    have hf₁ := innerEdgeList_fields P H gi₁ j₁ hEd₁'
    have hf₂ := innerEdgeList_fields P H gi₂ j₂ hEd₂'
    -- The edge's left endpoint `Ed.e.1.1 ∈ Ioo Ed.α Ed.β` (from `edgesOnSheet_mem`).
    have hio : Ed.e.1.1 ∈ Set.Ioo Ed.α Ed.β :=
      (edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.2.2.1
    have hio₁ : Ed.e.1.1 ∈ Set.Ioo gi₁.1.1 gi₁.1.2 := by rwa [hf₁.2.1, hf₁.2.2.1] at hio
    have hio₂ : Ed.e.1.1 ∈ Set.Ioo gi₂.1.1 gi₂.1.2 := by rwa [hf₂.2.1, hf₂.2.2.1] at hio
    exact (Set.disjoint_left.mp hdisj) hio₁ hio₂

/-- **`allCurveEdges` is `Nodup`.** No edge repeats: within a curve, `curveBlock_nodup`;
across curves, distinct `H₁ ≠ H₂` give distinct `.1` (proof-irrelevant `EdgeBCurve`),
hence different `.h`, so the curve blocks are disjoint. -/
theorem allCurveEdges_nodup {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (allCurveEdges d P Γ).Nodup := by
  rw [allCurveEdges, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · -- Per-curve block nodup, via the reassociation `curveBlock_eq`.
    intro H _
    rw [curveBlock_eq]; exact curveBlock_nodup P H
  · -- Distinct curves ⟹ disjoint blocks.
    apply (Finset.nodup_toList Γ).imp_of_mem
    intro H₁ H₂ _ _ hHne
    rw [Function.onFun, List.disjoint_left]
    intro Ed hEd₁ hEd₂
    -- An edge in `H₁`'s block has `.h = H₁.1`; in `H₂`'s block, `.h = H₂.1`.
    rw [curveBlock_eq, List.mem_flatMap] at hEd₁ hEd₂
    obtain ⟨gi₁, _, hEd₁'⟩ := hEd₁
    obtain ⟨gi₂, _, hEd₂'⟩ := hEd₂
    rw [List.mem_flatMap] at hEd₁' hEd₂'
    obtain ⟨j₁, _, hEd₁''⟩ := hEd₁'
    obtain ⟨j₂, _, hEd₂''⟩ := hEd₂'
    have hh₁ := (innerEdgeList_fields P H₁ gi₁ j₁ hEd₁'').1
    have hh₂ := (innerEdgeList_fields P H₂ gi₂ j₂ hEd₂'').1
    have hHeq1 : H₁.1 = H₂.1 := by rw [← hh₁, hh₂]
    exact hHne (by apply PSigma.ext hHeq1; apply proof_irrel_heq)

/-! ### 5. Same-curve interior disjointness

Two edges on the *same* curve with distinct endpoint pairs have disjoint arc
interiors. A shared interior point `z` would (1) force the same sheet rank
(`sheetRank_const_of_continuous_onCurve`, the mechanism of `export_4b_interior_disjoint`),
and (2) force the same good-interval bracket (`goodIntervalsBundle_no_overlap`, via
provenance). Both edges then live in one `edgesOnSheet P h α β j` list; distinct
endpoint pairs there have disjoint open `x`-intervals (`edgesOnSheet_xIntervals_disjoint`),
contradicting the shared point's `x`-coordinate lying in both. No Bézout. -/

/-- The left/right good-interval bounds of an `EdgeBEdge`: `Ed.α < Ed.e.1.1` and
`Ed.e.2.1 < Ed.β` (from `edgesOnSheet_mem`). -/
lemma EdgeBEdge.lt_fst {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : Ed.α < Ed.e.1.1 :=
  ((edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.2.2.1).1

lemma EdgeBEdge.snd_lt {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : Ed.e.2.1 < Ed.β :=
  ((edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).2.2.2.1).2

/-- The sheet rank along an `EdgeBEdge`'s arc, anchored at the left endpoint, equals
the class rank `Ed.j`. From `sheetRank_const_of_continuous_onCurve` and the rank-`j`
membership of the left endpoint. -/
lemma EdgeBEdge.sheetRank_interior {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P)
    {x : ℝ} (hx : x ∈ Set.Icc Ed.e.1.1 Ed.e.2.1) :
    sheetRank Ed.h x (Ed.chi x) = Ed.j := by
  have hconst := sheetRank_const_of_continuous_onCurve Ed.h Ed.hgood Ed.lt_fst Ed.snd_lt
    Ed.chi_spec.1 Ed.chi_spec.2.2.2 x hx
  -- Anchor: `χ e.1.1 = e.1.2`, `sheetRank h e.1.1 e.1.2 = j`.
  have hanchor : Ed.chi Ed.e.1.1 = Ed.e.1.2 := Ed.chi_spec.2.1
  have hrankP : sheetRank Ed.h Ed.e.1.1 Ed.e.1.2 = Ed.j :=
    ((edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.2.2.2)
  rw [hconst, hanchor, hrankP]

/-- **Same-curve shared-point parameters.** If two `allCurveEdges` edges on the same
curve (`Ed₁.h = Ed₂.h`) share an interior point `z`, then their rank and good-interval
bracket agree: `Ed₁.j = Ed₂.j`, `Ed₁.α = Ed₂.α`, `Ed₁.β = Ed₂.β`. Rank from
`sheetRank_const_of_continuous_onCurve`; bracket from `goodIntervalsBundle_no_overlap`
via provenance. This is the shared core of same-curve disjointness and the
diagonal-empty count. -/
lemma edgeB_same_curve_shared_point_params {d : ℕ} {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {Ed₁ Ed₂ : EdgeBEdge P} (hEd₁ : Ed₁ ∈ allCurveEdges d P Γ) (hEd₂ : Ed₂ ∈ allCurveEdges d P Γ)
    (hhe : Ed₁.h = Ed₂.h) {z : ℝ × ℝ}
    (hz₁ : z ∈ interiorOfArc Ed₁.arc) (hz₂ : z ∈ interiorOfArc Ed₂.arc) :
    Ed₁.j = Ed₂.j ∧ Ed₁.α = Ed₂.α ∧ Ed₁.β = Ed₂.β := by
  -- Interior x-projection of both arcs at `z`.
  obtain ⟨hz1a, hz1b, hzχ₁⟩ := curveArc_interior_xproj Ed₁.fst_lt Ed₁.chi_spec.1 hz₁
  obtain ⟨hz2a, hz2b, hzχ₂⟩ := curveArc_interior_xproj Ed₂.fst_lt Ed₂.chi_spec.1 hz₂
  have hzIcc₁ : z.1 ∈ Set.Icc Ed₁.e.1.1 Ed₁.e.2.1 := ⟨hz1a.le, hz1b.le⟩
  have hzIcc₂ : z.1 ∈ Set.Icc Ed₂.e.1.1 Ed₂.e.2.1 := ⟨hz2a.le, hz2b.le⟩
  -- (1) Same rank.
  have hχeq : Ed₁.chi z.1 = Ed₂.chi z.1 := by rw [← hzχ₁, ← hzχ₂]
  have hrank₁ : sheetRank Ed₁.h z.1 (Ed₁.chi z.1) = Ed₁.j := Ed₁.sheetRank_interior hzIcc₁
  have hrank₂ : sheetRank Ed₂.h z.1 (Ed₂.chi z.1) = Ed₂.j := Ed₂.sheetRank_interior hzIcc₂
  have hjeq : Ed₁.j = Ed₂.j := by rw [← hrank₁, ← hrank₂, hhe, hχeq]
  -- (2) Same bracket via provenance + no_overlap.
  obtain ⟨H₁, _, hH₁h, gi₁, hgi₁, hα₁, hβ₁⟩ := allCurveEdges_provenance hEd₁
  obtain ⟨H₂, _, hH₂h, gi₂, hgi₂, hα₂, hβ₂⟩ := allCurveEdges_provenance hEd₂
  have hHeq1 : H₁.1 = H₂.1 := by rw [← hH₁h, hhe, hH₂h]
  have hHeq : H₁ = H₂ := by apply PSigma.ext hHeq1; apply proof_irrel_heq
  subst hHeq
  have hz1_io₁ : z.1 ∈ Set.Ioo Ed₁.α Ed₁.β :=
    ⟨lt_trans Ed₁.lt_fst hz1a, lt_trans hz1b Ed₁.snd_lt⟩
  have hz1_io₂ : z.1 ∈ Set.Ioo Ed₂.α Ed₂.β :=
    ⟨lt_trans Ed₂.lt_fst hz2a, lt_trans hz2b Ed₂.snd_lt⟩
  have hz1_gi₁ : z.1 ∈ Set.Ioo gi₁.1.1 gi₁.1.2 := by rwa [hα₁, hβ₁] at hz1_io₁
  have hz1_gi₂ : z.1 ∈ Set.Ioo gi₂.1.1 gi₂.1.2 := by rwa [hα₂, hβ₂] at hz1_io₂
  have hbracket : gi₁.1 = gi₂.1 :=
    goodIntervalsBundle_no_overlap P H₁ hgi₁ hgi₂ hz1_gi₁ hz1_gi₂
  exact ⟨hjeq, by rw [hα₁, hα₂, hbracket], by rw [hβ₁, hβ₂, hbracket]⟩

/-- **Same-curve disjointness.** Two edges of `allCurveEdges` on the same curve
(`Ed₁.h = Ed₂.h`) with distinct endpoint pairs (`Ed₁.e ≠ Ed₂.e`) have disjoint arc
interiors. -/
lemma edgeB_same_curve_arcs_disjoint {d : ℕ} {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {Ed₁ Ed₂ : EdgeBEdge P} (hEd₁ : Ed₁ ∈ allCurveEdges d P Γ) (hEd₂ : Ed₂ ∈ allCurveEdges d P Γ)
    (hhe : Ed₁.h = Ed₂.h) (hene : Ed₁.e ≠ Ed₂.e) :
    Disjoint (interiorOfArc Ed₁.arc) (interiorOfArc Ed₂.arc) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  obtain ⟨hz1a, hz1b, _⟩ := curveArc_interior_xproj Ed₁.fst_lt Ed₁.chi_spec.1 hz₁
  obtain ⟨hz2a, hz2b, _⟩ := curveArc_interior_xproj Ed₂.fst_lt Ed₂.chi_spec.1 hz₂
  obtain ⟨hjeq, hαeq, hβeq⟩ := edgeB_same_curve_shared_point_params hEd₁ hEd₂ hhe hz₁ hz₂
  -- Both edges live in the SAME `edgesOnSheet P Ed₁.h Ed₁.α Ed₁.β Ed₁.j`.
  have hmem₁ : Ed₁.e ∈ edgesOnSheet P Ed₁.h Ed₁.α Ed₁.β Ed₁.j := Ed₁.hmem
  have hmem₂ : Ed₂.e ∈ edgesOnSheet P Ed₁.h Ed₁.α Ed₁.β Ed₁.j := by
    rw [hhe, hαeq, hβeq, hjeq]; exact Ed₂.hmem
  have hxdisj := edgesOnSheet_xIntervals_disjoint Ed₁.hgood hmem₁ hmem₂ hene
  exact (Set.disjoint_left.mp hxdisj) ⟨hz1a, hz1b⟩ ⟨hz2a, hz2b⟩

/-- **Same-curve shared point ⟹ equal edge.** If two `allCurveEdges` edges on the same
curve share an interior point, they are equal as `EdgeBEdge` values. (Same rank,
bracket by `…_shared_point_params`; then equal `.e` because distinct `.e` would force
disjoint interiors by `edgeB_same_curve_arcs_disjoint`.) -/
lemma edgeB_same_curve_shared_point_imp_eq {d : ℕ} {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {Ed₁ Ed₂ : EdgeBEdge P} (hEd₁ : Ed₁ ∈ allCurveEdges d P Γ) (hEd₂ : Ed₂ ∈ allCurveEdges d P Γ)
    (hhe : Ed₁.h = Ed₂.h) {z : ℝ × ℝ}
    (hz₁ : z ∈ interiorOfArc Ed₁.arc) (hz₂ : z ∈ interiorOfArc Ed₂.arc) :
    Ed₁ = Ed₂ := by
  obtain ⟨hjeq, hαeq, hβeq⟩ := edgeB_same_curve_shared_point_params hEd₁ hEd₂ hhe hz₁ hz₂
  -- `.e` must be equal: else `edgeB_same_curve_arcs_disjoint` makes the shared point impossible.
  have heeq : Ed₁.e = Ed₂.e := by
    by_contra hene
    exact (Set.disjoint_left.mp (edgeB_same_curve_arcs_disjoint hEd₁ hEd₂ hhe hene)) hz₁ hz₂
  -- All data fields agree; `hgood`/`hmem` are proofs (proof-irrelevant).
  cases Ed₁ with
  | mk h₁ α₁ β₁ hgood₁ j₁ e₁ hmem₁ =>
    cases Ed₂ with
    | mk h₂ α₂ β₂ hgood₂ j₂ e₂ hmem₂ =>
      simp only at hhe hjeq hαeq hβeq heeq
      subst hhe; subst hαeq; subst hβeq; subst hjeq; subst heeq
      rfl

/-! ### 6. The curve of an edge, and arc-interior ⊆ curve zero-set

`curveOf i ∈ Γ` is the `EdgeBCurve` the `i`-th global edge came from (its `.h` equals
`(curveOf i).1`). Every interior point of an `i`-arc lies on `(curveOf i).1`'s zero-set
`{z | evalPlane (curveOf i).1 z = 0}` — from `curveArc_interior_xproj` (giving
`z.2 = χ z.1`) composed with the on-curve fact of `export_4a`. This feeds the
cross-curve sub-case. -/

/-- The `i`-th global edge of `allCurveEdges d P Γ`, as an element of the list. -/
noncomputable def edgeOfIdx {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) : EdgeBEdge P :=
  (allCurveEdges d P Γ)[i]

lemma edgeOfIdx_mem {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) : edgeOfIdx P Γ i ∈ allCurveEdges d P Γ :=
  List.getElem_mem _

/-- The curve `H ∈ Γ` the `i`-th global edge comes from (via `allCurveEdges_provenance`),
chosen by `Classical.choose`. -/
noncomputable def curveOf {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) : EdgeBCurve d :=
  Classical.choose (allCurveEdges_provenance (edgeOfIdx_mem P Γ i))

lemma curveOf_mem {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) : curveOf P Γ i ∈ Γ :=
  (Classical.choose_spec (allCurveEdges_provenance (edgeOfIdx_mem P Γ i))).1

/-- The `i`-th edge's stored polynomial equals `(curveOf i).1`. -/
lemma curveOf_h {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) : (edgeOfIdx P Γ i).h = (curveOf P Γ i).1 :=
  (Classical.choose_spec (allCurveEdges_provenance (edgeOfIdx_mem P Γ i))).2.1

/-- **Arc interior lies on the curve zero-set.** Every interior point of the `i`-th
arc lies on `{z | evalPlane (curveOf i).1 z = 0}`. -/
lemma edgeOfIdx_interior_subset_zeroSet {d : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (i : Fin (allCurveEdges d P Γ).length) {z : ℝ × ℝ}
    (hz : z ∈ interiorOfArc (edgeOfIdx P Γ i).arc) :
    z ∈ {w : ℝ × ℝ | evalPlane (curveOf P Γ i).1 w = 0} := by
  set Ed := edgeOfIdx P Γ i with hEd
  -- `z = (z.1, χ z.1)`, `z.1 ∈ Icc e.1.1 e.2.1`, and `χ` is on-curve there.
  obtain ⟨hz1a, hz1b, hzχ⟩ := curveArc_interior_xproj Ed.fst_lt Ed.chi_spec.1 hz
  have hzIcc : z.1 ∈ Set.Icc Ed.e.1.1 Ed.e.2.1 := ⟨hz1a.le, hz1b.le⟩
  have honcurve : evalPlane Ed.h (z.1, Ed.chi z.1) = 0 := Ed.chi_spec.2.2.2 z.1 hzIcc
  -- Rewrite `z` as `(z.1, χ z.1)` and the polynomial via `curveOf_h`.
  rw [Set.mem_setOf_eq, ← curveOf_h P Γ i]
  have hzeq : z = (z.1, Ed.chi z.1) := by
    ext
    · rfl
    · exact hzχ
  rw [hzeq]; exact honcurve

/-! ### 7. The crossing set and its fibre over a curve pair

`crossingFinset` collects the crossing index pairs `(i,j)`, `i<j`. The fibre over a
curve pair `(H,H')` is bounded by `M`: the diagonal `(H,H)` is *empty* (same-curve
arcs are disjoint, using `allCurveEdges` nodup so `i<j` gives distinct edges), and an
off-diagonal `(H,H')` injects (via the shared crossing point) into the curve–curve
intersection `γ_H ∩ γ_{H'}`, whose `encard ≤ M` by the curve–curve clause `hcc`. -/

variable {d : ℕ} {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}

/-- The crossing index-pair Finset of `edgeBMultigraph _ _ P Γ`, transported to
`Fin (allCurveEdges d P Γ).length` (defeq to `Fin numEdges`). Depends only on the
arcs, not on the `crossings` budget. -/
noncomputable def crossingFinset (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    Finset (Fin (allCurveEdges d P Γ).length × Fin (allCurveEdges d P Γ).length) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧
    (interiorOfArc (edgeOfIdx P Γ ij.1).arc ∩ interiorOfArc (edgeOfIdx P Γ ij.2).arc).Nonempty)

/-- **The fibre map.** Each crossing pair maps to the ordered curve pair
`(curveOf i, curveOf j) ∈ Γ ×ˢ Γ`. -/
noncomputable def crossingCurvePair (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (ij : Fin (allCurveEdges d P Γ).length × Fin (allCurveEdges d P Γ).length) :
    EdgeBCurve d × EdgeBCurve d :=
  (curveOf P Γ ij.1, curveOf P Γ ij.2)

/-- The fibre map lands in `Γ ×ˢ Γ`. -/
lemma crossingCurvePair_mem (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (ij : Fin (allCurveEdges d P Γ).length × Fin (allCurveEdges d P Γ).length) :
    crossingCurvePair P Γ ij ∈ Γ ×ˢ Γ :=
  Finset.mem_product.mpr ⟨curveOf_mem P Γ ij.1, curveOf_mem P Γ ij.2⟩

/-- **Diagonal fibre is empty.** Using `allCurveEdges` nodup `hnd`, a crossing pair on
the diagonal (`curveOf i = curveOf j`) is impossible: the shared crossing point forces
the two edges equal (`edgeB_same_curve_shared_point_imp_eq`), so `i = j`, contradicting
`i < j`. -/
lemma crossing_diagonal_empty (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hnd : (allCurveEdges d P Γ).Nodup)
    {ij : Fin (allCurveEdges d P Γ).length × Fin (allCurveEdges d P Γ).length}
    (hmem : ij ∈ crossingFinset d P Γ) (hdiag : curveOf P Γ ij.1 = curveOf P Γ ij.2) :
    False := by
  rw [crossingFinset, Finset.mem_filter] at hmem
  obtain ⟨_, hlt, hcross⟩ := hmem
  -- Same curve polynomial for the two edges.
  have hhe : (edgeOfIdx P Γ ij.1).h = (edgeOfIdx P Γ ij.2).h := by
    rw [curveOf_h P Γ ij.1, curveOf_h P Γ ij.2, hdiag]
  -- Shared crossing point.
  obtain ⟨z, hz₁, hz₂⟩ := hcross
  have hedeq : edgeOfIdx P Γ ij.1 = edgeOfIdx P Γ ij.2 :=
    edgeB_same_curve_shared_point_imp_eq (edgeOfIdx_mem P Γ ij.1) (edgeOfIdx_mem P Γ ij.2) hhe hz₁ hz₂
  -- Nodup ⟹ equal list entries at equal indices, contradicting `i < j`.
  have hidx : ij.1 = ij.2 := by
    have hnd' := hnd
    rw [List.nodup_iff_injective_getElem] at hnd'
    have := hnd' (a₁ := ij.1) (a₂ := ij.2) hedeq
    exact this
  exact absurd hidx (Fin.ne_of_lt hlt)

/-- **Within-curve index injectivity.** If a point `z` is an interior point of both
the `i`-th and `i'`-th arcs and the two edges are on the same curve
(`(edgeOfIdx i).h = (edgeOfIdx i').h`), then `i = i'`. (Edges equal by
`edgeB_same_curve_shared_point_imp_eq`; indices equal by `allCurveEdges` nodup.) -/
lemma edgeIdx_unique_of_interior (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hnd : (allCurveEdges d P Γ).Nodup) {i i' : Fin (allCurveEdges d P Γ).length} {z : ℝ × ℝ}
    (hz : z ∈ interiorOfArc (edgeOfIdx P Γ i).arc) (hz' : z ∈ interiorOfArc (edgeOfIdx P Γ i').arc)
    (hhe : (edgeOfIdx P Γ i).h = (edgeOfIdx P Γ i').h) :
    i = i' := by
  have hedeq : edgeOfIdx P Γ i = edgeOfIdx P Γ i' :=
    edgeB_same_curve_shared_point_imp_eq (edgeOfIdx_mem P Γ i) (edgeOfIdx_mem P Γ i') hhe hz hz'
  rw [List.nodup_iff_injective_getElem] at hnd
  exact hnd hedeq

/-- **Off-diagonal fibre bound.** For a curve pair `(H, H')` with `H ≠ H'`, the crossing
pairs mapping to `(H, H')` number at most `M`. Each such crossing pair has a shared
interior point `z`, which lies on both `γ_H` and `γ_{H'}` (`edgeOfIdx_interior_subset_zeroSet`);
the map `(i,j) ↦ z` is injective on the fibre (within each curve, `z` pins the index by
`edgeIdx_unique_of_interior`), so the fibre injects into `γ_H ∩ γ_{H'}`, whose `encard ≤ M`
(`hcc`). -/
lemma crossing_offdiagonal_fibre_le {M : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hnd : (allCurveEdges d P Γ).Nodup)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞))
    {HH : EdgeBCurve d × EdgeBCurve d} (hHH : HH ∈ Γ ×ˢ Γ) (hne : HH.1 ≠ HH.2) :
    (Finset.filter (fun ij => crossingCurvePair P Γ ij = HH) (crossingFinset d P Γ)).card ≤ M := by
  set Fb := Finset.filter (fun ij => crossingCurvePair P Γ ij = HH) (crossingFinset d P Γ) with hFb
  -- The crossing-point map on the fibre.
  -- For each `ij ∈ Fb`, extract the crossing's nonempty intersection.
  have hcross : ∀ ij ∈ Fb, (interiorOfArc (edgeOfIdx P Γ ij.1).arc ∩
      interiorOfArc (edgeOfIdx P Γ ij.2).arc).Nonempty := by
    intro ij hij
    rw [hFb, Finset.mem_filter, crossingFinset, Finset.mem_filter] at hij
    exact hij.1.2.2
  -- The point map.
  let g : Fin (allCurveEdges d P Γ).length × Fin (allCurveEdges d P Γ).length → ℝ × ℝ :=
    fun ij => if h : (interiorOfArc (edgeOfIdx P Γ ij.1).arc ∩
        interiorOfArc (edgeOfIdx P Γ ij.2).arc).Nonempty then h.choose else (0, 0)
  -- `g ij ∈ γ_{HH.1} ∩ γ_{HH.2}` for `ij ∈ Fb`.
  have hgmem : ∀ ij ∈ Fb, g ij ∈ ({z : ℝ × ℝ | evalPlane HH.1.1 z = 0} ∩
      {z | evalPlane HH.2.1 z = 0}) := by
    intro ij hij
    have hijc := hcross ij hij
    have hcp : g ij = hijc.choose := by simp only [g, dif_pos hijc]
    obtain ⟨hzm1, hzm2⟩ := hijc.choose_spec
    rw [hFb, Finset.mem_filter] at hij
    have hcurve : crossingCurvePair P Γ ij = HH := hij.2
    have hc1 : curveOf P Γ ij.1 = HH.1 := congrArg Prod.fst hcurve
    have hc2 : curveOf P Γ ij.2 = HH.2 := congrArg Prod.snd hcurve
    rw [hcp]
    refine ⟨?_, ?_⟩
    · have := edgeOfIdx_interior_subset_zeroSet P Γ ij.1 hzm1
      rw [hc1] at this; exact this
    · have := edgeOfIdx_interior_subset_zeroSet P Γ ij.2 hzm2
      rw [hc2] at this; exact this
  -- `g` is injective on `Fb`.
  have hginj : Set.InjOn g Fb := by
    intro ij₁ hij₁ ij₂ hij₂ hgeq
    rw [Finset.mem_coe] at hij₁ hij₂
    have hc₁ := hcross ij₁ hij₁
    have hc₂ := hcross ij₂ hij₂
    have hcp₁ : g ij₁ = hc₁.choose := by simp only [g, dif_pos hc₁]
    have hcp₂ : g ij₂ = hc₂.choose := by simp only [g, dif_pos hc₂]
    have hz₁ := hc₁.choose_spec
    have hz₂ := hc₂.choose_spec
    -- Same curve pair for both crossing pairs.
    have hcurve₁ : crossingCurvePair P Γ ij₁ = HH := (Finset.mem_filter.mp hij₁).2
    have hcurve₂ : crossingCurvePair P Γ ij₂ = HH := (Finset.mem_filter.mp hij₂).2
    have hc1eq : curveOf P Γ ij₁.1 = curveOf P Γ ij₂.1 := by
      rw [show curveOf P Γ ij₁.1 = HH.1 from congrArg Prod.fst hcurve₁,
          show curveOf P Γ ij₂.1 = HH.1 from congrArg Prod.fst hcurve₂]
    have hc2eq : curveOf P Γ ij₁.2 = curveOf P Γ ij₂.2 := by
      rw [show curveOf P Γ ij₁.2 = HH.2 from congrArg Prod.snd hcurve₁,
          show curveOf P Γ ij₂.2 = HH.2 from congrArg Prod.snd hcurve₂]
    -- The shared point `z := g ij₁ = g ij₂` is interior to all four arcs.
    have hzeq : hc₁.choose = hc₂.choose := by rw [← hcp₁, ← hcp₂, hgeq]
    -- First coordinates: same curve, shared point ⟹ equal index.
    have hi1 : ij₁.1 = ij₂.1 :=
      edgeIdx_unique_of_interior P Γ hnd hz₁.1 (by rw [hzeq]; exact hz₂.1)
        (by rw [curveOf_h P Γ ij₁.1, curveOf_h P Γ ij₂.1, hc1eq])
    have hi2 : ij₁.2 = ij₂.2 :=
      edgeIdx_unique_of_interior P Γ hnd hz₁.2 (by rw [hzeq]; exact hz₂.2)
        (by rw [curveOf_h P Γ ij₁.2, curveOf_h P Γ ij₂.2, hc2eq])
    exact Prod.ext hi1 hi2
  -- `Fb.card = (Fb.image g).card ≤ encard(γ ∩ γ') ≤ M`.
  have hcardeq : Fb.card = (Fb.image g).card := (Finset.card_image_of_injOn hginj).symm
  have hsub : (↑(Fb.image g) : Set (ℝ × ℝ)) ⊆
      {z : ℝ × ℝ | evalPlane HH.1.1 z = 0} ∩ {z | evalPlane HH.2.1 z = 0} := by
    intro z hz
    rw [Finset.coe_image, Set.mem_image] at hz
    obtain ⟨ij, hij, rfl⟩ := hz
    exact hgmem ij hij
  have hHH1 : HH.1 ∈ Γ := (Finset.mem_product.mp hHH).1
  have hHH2 : HH.2 ∈ Γ := (Finset.mem_product.mp hHH).2
  have hbound : (↑(Fb.image g) : Set (ℝ × ℝ)).encard ≤ (M : ℕ∞) :=
    le_trans (Set.encard_le_encard hsub) (hcc HH.1 hHH1 HH.2 hHH2 hne)
  have hcardle : ((Fb.image g).card : ℕ∞) ≤ (M : ℕ∞) := by
    rwa [Set.encard_coe_eq_coe_finsetCard] at hbound
  have hfin : (Fb.image g).card ≤ M := by exact_mod_cast hcardle
  rw [hcardeq]; exact hfin

/-! ### 8. The top-level `WellDrawn` -/

/-- `crossingCount` of `edgeBMultigraph` equals `crossingFinset.card` (the crossing
filter, with `G.arc i` unfolded to `(edgeOfIdx i).arc`). -/
lemma crossingCount_eq_card (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).crossingCount = (crossingFinset d P Γ).card := rfl

/-- **The combined fibre bound.** Every fibre of `crossingCurvePair` over `Γ ×ˢ Γ` has
`≤ M` crossing pairs: the diagonal (`H = H`) is empty (`crossing_diagonal_empty`), the
off-diagonal `≤ M` (`crossing_offdiagonal_fibre_le`). -/
lemma crossing_fibre_le {M : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hnd : (allCurveEdges d P Γ).Nodup)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞))
    (HH : EdgeBCurve d × EdgeBCurve d) (hHH : HH ∈ Γ ×ˢ Γ) :
    (Finset.filter (fun ij => crossingCurvePair P Γ ij = HH) (crossingFinset d P Γ)).card ≤ M := by
  by_cases hne : HH.1 = HH.2
  · -- Diagonal: the fibre is empty.
    rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le M
    · rw [Finset.filter_eq_empty_iff]
      intro ij hij hpair
      have h1 : curveOf P Γ ij.1 = HH.1 := congrArg Prod.fst hpair
      have h2 : curveOf P Γ ij.2 = HH.2 := congrArg Prod.snd hpair
      exact crossing_diagonal_empty P Γ hnd hij (by rw [h1, h2, hne])
  · exact crossing_offdiagonal_fibre_le P Γ hnd hcc hHH hne

/-- **`edgeBMultigraph_wellDrawn`.** The Edge-B drawn multigraph is well-drawn:
`crossingCount ≤ M * Γ.card ^ 2`. Curve port of `stMultigraph_wellDrawn`, with the
line case's "≤ 1 intersection per distinct pair" replaced by the curve–curve clause
`hcc` ("≤ M intersections per distinct curve pair"), counted by
`Finset.card_le_mul_card_image_of_maps_to` over the `Γ ×ˢ Γ` fibres.

* `hnd` (`allCurveEdges` nodup) makes the diagonal fibre empty.
* `hcc` is the curve–curve 2-degrees-of-freedom clause in the `PlanePoly`/`ℝ × ℝ`
  representation: distinct curves in `Γ` meet in `≤ M` points. (The conversion from
  `PachSharir.TwoDegreesOfFreedom` over `EuclideanSpace ℝ (Fin 2)` via the chart bridge
  is a separate downstream node.) -/
theorem edgeBMultigraph_wellDrawn {M : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞)) :
    (edgeBMultigraph d M P Γ).WellDrawn := by
  rw [DrawnMultigraph.WellDrawn, crossingCount_eq_card,
    show (edgeBMultigraph d M P Γ).crossings = M * Γ.card ^ 2 from rfl]
  have hnd := allCurveEdges_nodup P Γ
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := crossingCurvePair P Γ) (s := crossingFinset d P Γ) (t := Γ ×ˢ Γ)
    (fun ij _ => crossingCurvePair_mem P Γ ij) M
    (fun HH hHH => crossing_fibre_le P Γ hnd hcc HH hHH)
  rwa [Finset.card_product, ← pow_two] at hcard

end PachDeZeeuw.Algebraic
