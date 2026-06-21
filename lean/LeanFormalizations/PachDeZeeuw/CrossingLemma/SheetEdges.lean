/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetRank

/-!
# Per-sheet incident-point bookkeeping over a good interval (Edge B)

The curve analogue of the line-case `pointsOnLine` / `edgesOnLine` bookkeeping
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:322–438`), with the per-line key
`lineKey` replaced by the fibrewise sheet selector
`(on-curve ∧ x ∈ (α,β) ∧ sheetRank h x y = j)`. This realizes the FLAG
`edgesOnSheet-bookkeeping` of the Edge-B assembly design
(`docs/corollary24-E1E2-assembly-design.md` §4.2, §6): it provides the sorted /
nodup / on-curve / in-interval bookkeeping the consecutive-sheet pairing
(`export_4a_edge_is_arc`) consumes. No new analysis — the analytic content is in
the landed leaves (`SheetRank.lean`, `SheetCount.lean`).

The sort comparator is `p.1 ≤ q.1` (sort the rank-`j` class by `x`), not a
direction-projection key: within one sheet-rank class the points are ordered by
their `x`-coordinate. The nodup / membership / length proofs port unchanged from
the line case, since they use only the `mergeSort`-permutation and `Nodup`, not
the comparator or the filter shape; only `mem_pointsOnSheet`'s right-hand-side
conjunction differs from `mem_pointsOnLine`.

See `docs/corollary24-sheetedges-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Classical

/-- The points of `P` incident to the curve `γ = evalPlaneZeroSet h` over a good
interval `(α,β)` with fibrewise sheet rank `j`, sorted by `x`-coordinate. Returned
as a `List` so consecutive pairs are well-defined; the underlying multiset is the
filter of `P` to the rank-`j` class. Curve analogue of `pointsOnLine`. -/
noncomputable def pointsOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    List (ℝ × ℝ) :=
  (P.filter (fun p => p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j)).toList.mergeSort
    (fun p q => decide (p.1 ≤ q.1))

/-- `pointsOnSheet` is a permutation of the rank-`j` incident-point list
`(P.filter <pred>).toList`. -/
lemma pointsOnSheet_perm (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (pointsOnSheet P h α β j).Perm
      (P.filter (fun p => p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j)).toList :=
  List.mergeSort_perm _ _

/-- Membership in `pointsOnSheet` ⇔ membership in `P`, on the curve, in the good
interval `(α,β)`, and at sheet rank `j`. The only place the filter conjunction
shows through (the line case's right side is the single condition `p ∈ ℓ`). -/
lemma mem_pointsOnSheet {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ} {p : ℝ × ℝ} :
    p ∈ pointsOnSheet P h α β j ↔
      p ∈ P ∧ p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j := by
  rw [(pointsOnSheet_perm P h α β j).mem_iff, Finset.mem_toList, Finset.mem_filter]

/-- `pointsOnSheet` has no repeated points (it is a sort of a `Finset`'s element
list). -/
lemma pointsOnSheet_nodup (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (pointsOnSheet P h α β j).Nodup := by
  rw [(pointsOnSheet_perm P h α β j).nodup_iff]; exact Finset.nodup_toList _

/-- `|pointsOnSheet P h α β j| = |{p ∈ P : on-curve ∧ x ∈ (α,β) ∧ sheetRank = j}|`:
the sorted list keeps every rank-`j` incident point exactly once. -/
lemma length_pointsOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (pointsOnSheet P h α β j).length =
      (P.filter (fun p => p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j)).card := by
  rw [(pointsOnSheet_perm P h α β j).length_eq, Finset.length_toList]

/-- Consecutive (point, point) pairs along one sheet-rank class: `k` incident
points give `k - 1` segment edges. Analogue of `edgesOnLine`. -/
noncomputable def edgesOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnSheet P h α β j).zip (pointsOnSheet P h α β j).tail

/-- **Consecutive points are distinct.** Each edge of `edgesOnSheet` joins two
different points, because `pointsOnSheet` is `Nodup`: adjacent entries sit at the
consecutive indices `k, k+1`, which are distinct by nodup. Ports
`edgesOnLine_distinct` unchanged — the distinctness proof uses only nodup, not the
comparator or the filter shape. -/
lemma edgesOnSheet_distinct (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    ∀ e ∈ edgesOnSheet P h α β j, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨x, y⟩ := e
  have hnd := pointsOnSheet_nodup P h α β j
  set l := pointsOnSheet P h α β j with hl
  change (x, y) ∈ l.zip l.tail at he
  rw [List.mem_iff_getElem] at he
  obtain ⟨k, hk, hget⟩ := he
  rw [List.length_zip] at hk
  have hkl : k < l.length := lt_of_lt_of_le hk (min_le_left _ _)
  have hktail : k < l.tail.length := lt_of_lt_of_le hk (min_le_right _ _)
  rw [List.length_tail] at hktail
  have hk1 : k + 1 < l.length := by omega
  rw [List.getElem_zip, Prod.mk.injEq] at hget
  obtain ⟨hx, hy⟩ := hget
  have htaileq : l.tail[k] = l[k + 1] := by rw [List.getElem_tail]
  rw [htaileq] at hy
  intro hcontra
  rw [← hx, ← hy] at hcontra
  have := (hnd.getElem_inj_iff (i := k) (hi := hkl) (j := k + 1) (hj := hk1)).mp hcontra
  omega

/-- Both endpoints of every edge of `edgesOnSheet P h α β j` lie in `P`, on the
curve, in the good interval `(α,β)`, and at sheet rank `j` (the curve analogue of
`edgesOnLine_mem`). -/
lemma edgesOnSheet_mem (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    ∀ e ∈ edgesOnSheet P h α β j,
      (e.1 ∈ P ∧ e.1 ∈ evalPlaneZeroSet h ∧ e.1.1 ∈ Set.Ioo α β ∧ sheetRank h e.1.1 e.1.2 = j) ∧
      (e.2 ∈ P ∧ e.2 ∈ evalPlaneZeroSet h ∧ e.2.1 ∈ Set.Ioo α β ∧ sheetRank h e.2.1 e.2.2 = j) := by
  intro e he
  obtain ⟨x, y⟩ := e
  set l := pointsOnSheet P h α β j with hl
  change (x, y) ∈ l.zip l.tail at he
  have hx : x ∈ l := List.of_mem_zip he |>.1
  have hy : y ∈ l := by
    have := List.of_mem_zip he |>.2
    exact List.mem_of_mem_tail this
  exact ⟨mem_pointsOnSheet.mp hx, mem_pointsOnSheet.mp hy⟩

/-- **Edge-count identity.** A sheet-rank class with `k` incident points
contributes `k - 1` segment edges (and none when `k = 0`). Ports
`length_edgesOnLine`. -/
lemma length_edgesOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (edgesOnSheet P h α β j).length + 1 = (pointsOnSheet P h α β j).length
      ∨ edgesOnSheet P h α β j = [] := by
  unfold edgesOnSheet
  rcases Nat.eq_zero_or_pos (pointsOnSheet P h α β j).length with hcard | hcard
  · right
    rw [List.length_eq_zero_iff] at hcard
    rw [hcard]; rfl
  · left
    rw [List.length_zip, List.length_tail]
    omega

/-- The consecutive-segment edges of a single sheet-rank class, each bundled with a
proof that its two endpoints are distinct (so it can become a non-degenerate
connecting arc). Analogue of `edgesOnLineWithProof`. -/
noncomputable def edgesOnSheetWithProof (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    List (Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2) :=
  (edgesOnSheet P h α β j).pmap (fun e he => ⟨e, he⟩) (edgesOnSheet_distinct P h α β j)

/-- A bundled edge's underlying pair is a genuine edge of its sheet-rank class. -/
lemma mem_edgesOnSheetWithProof {P : Finset (ℝ × ℝ)} {h : PlanePoly} {α β : ℝ} {j : ℕ}
    {s : Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2} (hs : s ∈ edgesOnSheetWithProof P h α β j) :
    s.1 ∈ edgesOnSheet P h α β j := by
  unfold edgesOnSheetWithProof at hs
  rw [List.mem_pmap] at hs
  obtain ⟨e, he, heq⟩ := hs
  rw [← heq]; exact he

/-- `|edgesOnSheetWithProof P h α β j| = |edgesOnSheet P h α β j|` (the `pmap` only
attaches distinctness proofs, it does not drop or duplicate edges). -/
lemma length_edgesOnSheetWithProof (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    (edgesOnSheetWithProof P h α β j).length = (edgesOnSheet P h α β j).length := by
  unfold edgesOnSheetWithProof; rw [List.length_pmap]

end PachDeZeeuw.Algebraic
