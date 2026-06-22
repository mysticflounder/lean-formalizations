/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBWellDrawn
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter

/-!
# Edge-B multigraph multiplicity bound `≤ M` (task #43 discharge (iv))

The curve port of the line-case `stMultigraph_multiplicity_le_one`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:1221`), generalizing the line case's
terminal `≤ 1` (at most one line through two distinct points) to `≤ M` (at most `M`
curves of `Γ` through two distinct points). This is the discharge that **changes
shape** (`1 → M`) relative to the line case.

Goal:

    edgeBMultigraph_multiplicity_le_M (M P Γ)
      (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
        (Γ.filter (fun H => p ∈ {z | evalPlane H.1 z = 0} ∧
          q ∈ {z | evalPlane H.1 z = 0})).card ≤ M) :
      ∀ p q, (edgeBMultigraph d M P Γ).multiplicity p q ≤ M

`hpp` is the point–point 2-degrees-of-freedom clause in the `PlanePoly` / `ℝ × ℝ`
representation — the verbatim PlanePoly image of `TwoDegreesOfFreedom`'s second
conjunct. The conversion from `PachSharir.TwoDegreesOfFreedom` over
`EuclideanSpace ℝ (Fin 2)` (via the chart bridge + component reduction) is a separate
downstream node; within this file `hpp` is an explicit hypothesis.

This file is GLUE over already-landed, axiom-clean leaves. The only genuinely new
content is `edgeB_same_curve_match_imp_eq` (the M2 core), which mirrors the landed
`edgeB_same_curve_shared_point_imp_eq` (`EdgeBWellDrawn.lean`) but pivots on the
**left endpoint** (a genuine point of `P`, on the curve, in the bracket, at rank `j`)
rather than an interior arc point — orientation by `EdgeBEdge.fst_lt`, rank by
left-endpoint rank, bracket by `goodIntervalsBundle_no_overlap` via provenance.

See `docs/corollary24-edgeB-multiplicity-build.md` for the build record (now against
the P-aware fixed def).
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma
open PachSharir.SzemerediTrotter
open scoped Classical

variable {d : ℕ}

/-! ### 1. The per-curve edge block and its structural facts

`curveBlock P H` is one curve's contribution to `allCurveEdges` (the inner
`classKeys`/`edgesOnSheet` double `flatMap`); `allCurveEdges = Γ.toList.flatMap
(curveBlock P)` by `rfl`. The reassociation `curveBlock_eq` and the nodup
`curveBlock_nodup` (both landed in `EdgeBWellDrawn.lean`) discharge `curveBlock`'s
own nodup. -/

/-- The per-curve edge block of `allCurveEdges`: the inner `classKeys`/`edgesOnSheet`
double `flatMap` for a single curve `H`. `allCurveEdges = Γ.toList.flatMap (curveBlock P)`
by `rfl`. -/
noncomputable def curveBlock (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) : List (EdgeBEdge P) :=
  (classKeys d P H).flatMap (fun key =>
    (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).attach.map (fun se =>
      { h := H.1, α := key.1.1, β := key.1.2, hgood := key.2.1, j := key.2.2,
        e := se.1, hmem := se.2 }))

/-- `allCurveEdges` is the `flatMap` of the per-curve blocks. By `rfl`. -/
theorem allCurveEdges_eq_flatMap (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    allCurveEdges d P Γ = Γ.toList.flatMap (fun H => curveBlock P H) := rfl

/-- **Per-curve block nodup.** A single curve's block is `Nodup`, via the landed
`curveBlock_eq` reassociation + `curveBlock_nodup`. -/
theorem curveBlock_nodup' (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (curveBlock P H).Nodup := by
  rw [curveBlock, curveBlock_eq]; exact curveBlock_nodup P H

/-- Every edge of `curveBlock P H` has its stored polynomial equal to `H.1`. -/
theorem curveBlock_h (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    {Ed : EdgeBEdge P} (hEd : Ed ∈ curveBlock P H) : Ed.h = H.1 := by
  rw [curveBlock, List.mem_flatMap] at hEd
  obtain ⟨key, _, hEd2⟩ := hEd
  rw [List.mem_map] at hEd2
  obtain ⟨se, _, hEdeq⟩ := hEd2
  rw [← hEdeq]

/-- An edge of `curveBlock P H` for `H ∈ Γ` is an edge of `allCurveEdges d P Γ`. -/
theorem curveBlock_subset_allCurveEdges {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {H : EdgeBCurve d} (hHΓ : H ∈ Γ) {Ed : EdgeBEdge P} (hEd : Ed ∈ curveBlock P H) :
    Ed ∈ allCurveEdges d P Γ := by
  rw [allCurveEdges_eq_flatMap, List.mem_flatMap]
  exact ⟨H, Finset.mem_toList.mpr hHΓ, hEd⟩

/-! ### 2. Multiplicity as a per-curve `countP` sum -/

/-- **Multiplicity as a `countP`.** `(edgeBMultigraph d M P Γ).multiplicity p q` counts
the edge indices whose endpoint pair is `(p,q)` or `(q,p)`; this is the `countP` of
`matchPair p q` over the global edge list `allCurveEdges d P Γ`. Curve analogue of
`multiplicity_eq_countP`. -/
theorem edgeBMultigraph_multiplicity_eq_countP
    (M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) (p q : ℝ × ℝ) :
    (edgeBMultigraph d M P Γ).multiplicity p q
      = (allCurveEdges d P Γ).countP (fun Ed => matchPair p q Ed.e) := by
  show (Finset.univ.filter (fun i : Fin (allCurveEdges d P Γ).length =>
        (allCurveEdges d P Γ)[i].e = (p, q) ∨ (allCurveEdges d P Γ)[i].e = (q, p))).card = _
  set l := allCurveEdges d P Γ with hl
  set Pr : EdgeBEdge P → Bool := fun Ed => matchPair p q Ed.e with hPr
  have hfilt : (Finset.univ.filter (fun i : Fin l.length =>
        (l[i].e = (p, q) ∨ l[i].e = (q, p)))).card
      = (Finset.univ.filter (fun i : Fin l.length => Pr (l[i]) = true)).card := by
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [hPr]; unfold matchPair; rw [decide_eq_true_eq]
  rw [hfilt, finFilterCard_eq_countP]

/-- **`countP` over `allCurveEdges` is a `Finset.sum` over curves.** `allCurveEdges` is
the `flatMap` of the per-curve blocks (`allCurveEdges_eq_flatMap`), so by
`List.countP_flatMap` the total count is `Σ_{H∈Γ} (curveBlock P H).countP (matchPair p q ·.e)`.
Curve analogue of `multiplicity_flatMap_sum`. -/
theorem edgeB_countP_flatMap_sum
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) (p q : ℝ × ℝ) :
    (allCurveEdges d P Γ).countP (fun Ed => matchPair p q Ed.e)
      = ∑ H ∈ Γ, (curveBlock P H).countP (fun Ed => matchPair p q Ed.e) := by
  rw [allCurveEdges_eq_flatMap, List.countP_flatMap]
  simp only [Function.comp_def]
  rw [Finset.sum_map_toList]

/-! ### 3. Left-endpoint pivot data for the M2 core -/

/-- The left endpoint's `x`-coordinate lies in the edge's open good-interval bracket:
`Ed.e.1.1 ∈ Set.Ioo Ed.α Ed.β` (from `edgesOnSheet_mem`). -/
theorem EdgeBEdge.fst_mem_Ioo {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) :
    Ed.e.1.1 ∈ Set.Ioo Ed.α Ed.β :=
  (edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.2.2.1

/-- The class rank equals the left endpoint's sheet rank:
`Ed.j = sheetRank Ed.h Ed.e.1.1 Ed.e.1.2` (from `edgesOnSheet_mem`). -/
theorem EdgeBEdge.fst_rank {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) :
    Ed.j = sheetRank Ed.h Ed.e.1.1 Ed.e.1.2 :=
  ((edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.2.2.2).symm

/-- **Pinned orientation.** Two edges that both match the unordered pair `{p, q}` have
equal endpoint pairs `Ed₁.e = Ed₂.e`. A matching edge has strict `x`-increase
(`EdgeBEdge.fst_lt`), so its endpoint pair `Ed.e ∈ {(p,q),(q,p)}` must take the
orientation with increasing `x`; both edges then take the same orientation. (The
`x`-equal cross cases are ruled out by `fst_lt`.) -/
theorem edgeB_match_orientation {P : Finset (ℝ × ℝ)} {Ed₁ Ed₂ : EdgeBEdge P} {p q : ℝ × ℝ}
    (h₁ : matchPair p q Ed₁.e = true) (h₂ : matchPair p q Ed₂.e = true) :
    Ed₁.e = Ed₂.e := by
  have hlt₁ := Ed₁.fst_lt
  have hlt₂ := Ed₂.fst_lt
  unfold matchPair at h₁ h₂
  rw [decide_eq_true_eq] at h₁ h₂
  rcases h₁ with he₁ | he₁ <;> rcases h₂ with he₂ | he₂
  · rw [he₁, he₂]
  · -- Ed₁ = (p,q) ⟹ p.1 < q.1; Ed₂ = (q,p) ⟹ q.1 < p.1: contradiction.
    exfalso; rw [he₁] at hlt₁; rw [he₂] at hlt₂
    simp only at hlt₁ hlt₂; linarith
  · -- symmetric contradiction.
    exfalso; rw [he₁] at hlt₁; rw [he₂] at hlt₂
    simp only at hlt₁ hlt₂; linarith
  · rw [he₁, he₂]

/-- **Same-curve match ⟹ equal edge (the M2 core, `1 → M` shape change).** Two
`allCurveEdges` edges on the same curve (`Ed₁.h = Ed₂.h`) that both match the
unordered pair `{p, q}` are equal as `EdgeBEdge` values. Endpoint pairs equal by
`edgeB_match_orientation`; the left endpoint then pins the rank
(`EdgeBEdge.fst_rank`) and — sharing the left `x` in both brackets
(`EdgeBEdge.fst_mem_Ioo`) — the good-interval bracket
(`goodIntervalsBundle_no_overlap` via `allCurveEdges_provenance`); the remaining
proof fields are proof-irrelevant. Mirror of the landed
`edgeB_same_curve_shared_point_imp_eq`, pivoting on the left endpoint. -/
theorem edgeB_same_curve_match_imp_eq {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {Ed₁ Ed₂ : EdgeBEdge P} (hEd₁ : Ed₁ ∈ allCurveEdges d P Γ) (hEd₂ : Ed₂ ∈ allCurveEdges d P Γ)
    (hhe : Ed₁.h = Ed₂.h) {p q : ℝ × ℝ}
    (h₁ : matchPair p q Ed₁.e = true) (h₂ : matchPair p q Ed₂.e = true) :
    Ed₁ = Ed₂ := by
  -- (0) Equal endpoint pairs from pinned orientation.
  have heeq : Ed₁.e = Ed₂.e := edgeB_match_orientation h₁ h₂
  -- (1) Equal rank: rank is the left endpoint's sheet rank; equal `.h` and `.e` give equal `.j`.
  have hjeq : Ed₁.j = Ed₂.j := by
    rw [Ed₁.fst_rank, Ed₂.fst_rank, hhe, heeq]
  -- (2) Equal bracket via provenance + no_overlap; the shared left `x` lies in both brackets.
  obtain ⟨H₁, _, hH₁h, gi₁, hgi₁, hα₁, hβ₁⟩ := allCurveEdges_provenance hEd₁
  obtain ⟨H₂, _, hH₂h, gi₂, hgi₂, hα₂, hβ₂⟩ := allCurveEdges_provenance hEd₂
  have hHeq1 : H₁.1 = H₂.1 := by rw [← hH₁h, hhe, hH₂h]
  have hHeq : H₁ = H₂ := by apply PSigma.ext hHeq1; apply proof_irrel_heq
  subst hHeq
  -- The left endpoint `x := Ed₁.e.1.1 = Ed₂.e.1.1` lies in both edges' open brackets.
  have hx₁ : Ed₁.e.1.1 ∈ Set.Ioo Ed₁.α Ed₁.β := Ed₁.fst_mem_Ioo
  have hx₂ : Ed₁.e.1.1 ∈ Set.Ioo Ed₂.α Ed₂.β := by rw [heeq]; exact Ed₂.fst_mem_Ioo
  have hx_gi₁ : Ed₁.e.1.1 ∈ Set.Ioo gi₁.1.1 gi₁.1.2 := by rwa [hα₁, hβ₁] at hx₁
  have hx_gi₂ : Ed₁.e.1.1 ∈ Set.Ioo gi₂.1.1 gi₂.1.2 := by rwa [hα₂, hβ₂] at hx₂
  have hbracket : gi₁.1 = gi₂.1 :=
    goodIntervalsBundle_no_overlap P H₁ hgi₁ hgi₂ hx_gi₁ hx_gi₂
  have hαeq : Ed₁.α = Ed₂.α := by rw [hα₁, hα₂, hbracket]
  have hβeq : Ed₁.β = Ed₂.β := by rw [hβ₁, hβ₂, hbracket]
  -- All data fields agree; `hgood`/`hmem` are proofs (proof-irrelevant).
  cases Ed₁ with
  | mk h₁' α₁ β₁ hgood₁ j₁ e₁ hmem₁ =>
    cases Ed₂ with
    | mk h₂' α₂ β₂ hgood₂ j₂ e₂ hmem₂ =>
      simp only at hhe hjeq hαeq hβeq heeq
      subst hhe; subst hαeq; subst hβeq; subst hjeq; subst heeq
      rfl

/-! ### 4. The per-curve indicator bounds and the diagonal/off-`P` zeros -/

/-- **M2 (per-curve).** Within one curve's block a fixed unordered pair `{p,q}` is
carried by at most one edge: `(curveBlock P H).countP (matchPair p q ·.e) ≤ 1`.
Proved by `countP_le_one_of_index_inj`: two block edges that both match are equal as
`EdgeBEdge` values (`edgeB_same_curve_match_imp_eq`, same curve since both blocks are
`H`'s by `curveBlock_h`), and the block is `Nodup` (`curveBlock_nodup'`), so equal
entries sit at equal indices. -/
theorem curveBlock_countP_le_one {P : Finset (ℝ × ℝ)} {Γ : Finset (EdgeBCurve d)}
    {H : EdgeBCurve d} (hHΓ : H ∈ Γ) (p q : ℝ × ℝ) :
    (curveBlock P H).countP (fun Ed => matchPair p q Ed.e) ≤ 1 := by
  apply countP_le_one_of_index_inj
  intro i j hi hj hPi hPj
  set l := curveBlock P H with hl
  have hmemi : l[i] ∈ curveBlock P H := List.getElem_mem _
  have hmemj : l[j] ∈ curveBlock P H := List.getElem_mem _
  -- Both edges on the same curve `H`.
  have hhe : l[i].h = l[j].h := by
    rw [curveBlock_h P H hmemi, curveBlock_h P H hmemj]
  -- Lift to `allCurveEdges`, apply the M2 core, then nodup.
  have hedeq : l[i] = l[j] :=
    edgeB_same_curve_match_imp_eq
      (curveBlock_subset_allCurveEdges hHΓ hmemi)
      (curveBlock_subset_allCurveEdges hHΓ hmemj) hhe hPi hPj
  have hnd := curveBlock_nodup' P H
  exact (hnd.getElem_inj_iff (hi := hi) (hj := hj)).mp hedeq

/-- **M1 support (per-curve).** A curve not through both `p` and `q` contributes no
matching edge: every edge endpoint of `curveBlock P H` is on the curve `H.1`'s
zero-set (`edgesOnSheet_mem` + `curveBlock_h` + `mem_evalPlaneZeroSet`), so a match
would force `p, q ∈ {z | evalPlane H.1 z = 0}`. -/
theorem countP_curveBlock_eq_zero_of_not_mem {P : Finset (ℝ × ℝ)} (H : EdgeBCurve d)
    {p q : ℝ × ℝ}
    (h : ¬ (p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧ q ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0})) :
    (curveBlock P H).countP (fun Ed => matchPair p q Ed.e) = 0 := by
  rw [List.countP_eq_zero]
  intro Ed hEd
  unfold matchPair
  simp only [decide_eq_true_eq]
  intro hcontra
  apply h
  -- Both endpoints of `Ed` lie on `H.1`'s zero-set.
  have hmem := edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem
  have hhe := curveBlock_h P H hEd
  have hfst : Ed.e.1 ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} := by
    rw [Set.mem_setOf_eq, ← hhe]; exact mem_evalPlaneZeroSet.mp hmem.1.2.1
  have hsnd : Ed.e.2 ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} := by
    rw [Set.mem_setOf_eq, ← hhe]; exact mem_evalPlaneZeroSet.mp hmem.2.2.1
  rcases hcontra with heq | heq
  · rw [heq] at hfst hsnd; exact ⟨hfst, hsnd⟩
  · rw [heq] at hfst hsnd; exact ⟨hsnd, hfst⟩

/-- A degenerate pair `{p, p}` contributes no edge: edges of `curveBlock` join
*distinct* points (`edgesOnSheet_distinct` via `Ed.hmem`), so no edge has
`Ed.e = (p,p)`. -/
theorem countP_curveBlock_eq_zero_of_eq {P : Finset (ℝ × ℝ)} (H : EdgeBCurve d) (p : ℝ × ℝ) :
    (curveBlock P H).countP (fun Ed => matchPair p p Ed.e) = 0 := by
  rw [List.countP_eq_zero]
  intro Ed _
  unfold matchPair
  simp only [or_self, decide_eq_true_eq]
  intro hcontra
  have hdist := edgesOnSheet_distinct P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem
  rw [hcontra] at hdist
  exact hdist rfl

/-- A pair `{p, q}` with `p` or `q` not in `P` contributes no edge: a matching edge has
both endpoints in `P` (`EdgeBEdge.fst_mem`, `EdgeBEdge.snd_mem`), so a match forces
`p, q ∈ P`. This branch lets the conclusion range over arbitrary points while `hpp`
constrains only `p, q ∈ P`. -/
theorem countP_curveBlock_eq_zero_of_not_memP {P : Finset (ℝ × ℝ)} (H : EdgeBCurve d)
    {p q : ℝ × ℝ} (h : ¬ (p ∈ P ∧ q ∈ P)) :
    (curveBlock P H).countP (fun Ed => matchPair p q Ed.e) = 0 := by
  rw [List.countP_eq_zero]
  intro Ed _
  unfold matchPair
  simp only [decide_eq_true_eq]
  intro hcontra
  apply h
  have hfst := Ed.fst_mem
  have hsnd := Ed.snd_mem
  rcases hcontra with heq | heq
  · rw [heq] at hfst hsnd; exact ⟨hfst, hsnd⟩
  · rw [heq] at hfst hsnd; exact ⟨hsnd, hfst⟩

/-! ### 5. The deliverable -/

/-- **Edge-B multigraph multiplicity bound `≤ M` (discharge (iv)).** The multiplicity
of the Edge-B drawn multigraph between any two points is `≤ M`, given the point–point
2-degrees-of-freedom clause `hpp` in the `PlanePoly` / `ℝ × ℝ` representation (at most
`M` curves of `Γ` pass through any two distinct points of `P`).

Curve port of `stMultigraph_multiplicity_le_one`, generalizing the terminal `≤ 1`
(line case: at most one line through two points) to `≤ M`. The multiplicity reduces
(`edgeBMultigraph_multiplicity_eq_countP` / `edgeB_countP_flatMap_sum`) to
`Σ_{H∈Γ} (curveBlock P H).countP (matchPair p q ·.e)`; then:

* `p = q`: edges join distinct points (`countP_curveBlock_eq_zero_of_eq`); sum `= 0`.
* `p ≠ q`, not both in `P`: a matching edge forces `p, q ∈ P`
  (`countP_curveBlock_eq_zero_of_not_memP`); sum `= 0`.
* `p ≠ q`, both in `P`: a curve not through both contributes `0`
  (`countP_curveBlock_eq_zero_of_not_mem`), otherwise `≤ 1` (`curveBlock_countP_le_one`,
  the M2 fact); the indicator sum `= (Γ.filter (p∈γ_H ∧ q∈γ_H)).card ≤ M` by `hpp`.

`hpp` is the verbatim PlanePoly image of `TwoDegreesOfFreedom`'s second conjunct; the
bridge from `PachSharir.TwoDegreesOfFreedom` is a separate downstream node. -/
theorem edgeBMultigraph_multiplicity_le_M
    (M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M) :
    ∀ p q, (edgeBMultigraph d M P Γ).multiplicity p q ≤ M := by
  intro p q
  rw [edgeBMultigraph_multiplicity_eq_countP, edgeB_countP_flatMap_sum]
  by_cases hpq : p = q
  · -- Diagonal: every per-curve term is `0`.
    subst hpq
    rw [Finset.sum_eq_zero (fun H _ => countP_curveBlock_eq_zero_of_eq H p)]
    exact Nat.zero_le M
  · by_cases hmemP : p ∈ P ∧ q ∈ P
    · -- Both in `P`: per-curve indicator bound, then `hpp`.
      obtain ⟨hpP, hqP⟩ := hmemP
      have hterm : ∀ H ∈ Γ, (curveBlock P H).countP (fun Ed => matchPair p q Ed.e)
          ≤ (if p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧ q ∈ {z | evalPlane H.1 z = 0}
              then 1 else 0) := by
        intro H hHΓ
        by_cases hmem : p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧ q ∈ {z | evalPlane H.1 z = 0}
        · rw [if_pos hmem]; exact curveBlock_countP_le_one hHΓ p q
        · rw [if_neg hmem, countP_curveBlock_eq_zero_of_not_mem H hmem]
      calc ∑ H ∈ Γ, (curveBlock P H).countP (fun Ed => matchPair p q Ed.e)
          ≤ ∑ H ∈ Γ, (if p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
              q ∈ {z | evalPlane H.1 z = 0} then 1 else 0) := Finset.sum_le_sum hterm
        _ = (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
              q ∈ {z | evalPlane H.1 z = 0})).card := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]; simp
        _ ≤ M := hpp p hpP q hqP hpq
    · -- Not both in `P`: every per-curve term is `0`.
      rw [Finset.sum_eq_zero (fun H _ => countP_curveBlock_eq_zero_of_not_memP H hmemP)]
      exact Nat.zero_le M

end PachDeZeeuw.Algebraic
