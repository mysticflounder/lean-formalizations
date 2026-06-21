/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetEdges
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ConnectingArc

/-!
# Each consecutive sheet edge is a pinned connecting arc (Edge B, export-4a)

This file realizes the FLAG `edge-is-arc (export-4a)` of the Edge-B assembly design
(`docs/corollary24-E1E2-assembly-design.md` §4.2): for every consecutive pair
`(p, q) ∈ edgesOnSheet P h α β j` over a good interval `(α, β)`, there is a
continuous on-curve graph `χ` from `p` to `q` over `[p.1, q.1]` — a
`SimpleCurveArc`-ready connecting arc.

It is GLUE over already-landed leaves; no new analysis:

* `SheetEdges.lean` supplies the per-sheet bookkeeping (`edgesOnSheet_mem`,
  `edgesOnSheet_distinct`, `pointsOnSheet_nodup`, `mem_pointsOnSheet`, and the
  `mergeSort` comparator `p.1 ≤ q.1`).
* `SheetRank.lean` supplies the analytic content: `continuation_reaches` (the
  continuation lands on any same-rank curve point) and `sheetRank_injOn_fibre`
  (rank is injective on a good fibre).
* `ConnectingArc.lean` supplies `export_3_connecting_arc` (the `decomp_arc_on_good`
  continuation graph, pinned to `q` via the supplied reach predicate).

The one supporting lemma proved here that is not pure plumbing is
`edgesOnSheet_fst_lt`: along consecutive edges the `x`-coordinate strictly
increases. The `≤` half is `List.pairwise_mergeSort` (the `mergeSort` output is
`Pairwise` for its comparator); strictness rules out `p.1 = q.1` because two
distinct same-rank points over a shared good `x` would violate
`sheetRank_injOn_fibre`.

See `docs/corollary24-edgearc-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Classical

/-- **Strict `x`-increase along a consecutive sheet edge.** For every consecutive
pair `(p, q) ∈ edgesOnSheet P h α β j` over a good interval `(α, β)`, the first
coordinates strictly increase: `p.1 < q.1`.

The `≤` half is `List.pairwise_mergeSort` applied to the comparator
`fun p q => decide (p.1 ≤ q.1)` (`≤` on the first coordinate is `le_trans` /
`le_total` on `ℝ`): the `mergeSort` output is `Pairwise` for that comparator, so
adjacent entries `pointsOnSheet[k], pointsOnSheet[k+1]` satisfy `p.1 ≤ q.1`.
Strictness rules out `p.1 = q.1`: if it held, `edgesOnSheet_mem` gives both
endpoints on the curve over the shared `x = p.1` with `sheetRank … = j`, and
`p.1 ∈ Ioo α β` with `hgood` gives `p.1 ∉ Bad h`, so `sheetRank_injOn_fibre`
forces `p.2 = q.2`, hence `p = q` — contradicting `edgesOnSheet_distinct`. -/
theorem edgesOnSheet_fst_lt (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β : ℝ} (j : ℕ)
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p q : ℝ × ℝ} (hpq : (p, q) ∈ edgesOnSheet P h α β j) :
    p.1 < q.1 := by
  -- Keep the raw membership for the distinctness / on-curve facts (the index
  -- extraction below destructures the working copy `hpq`).
  have hpq0 : (p, q) ∈ edgesOnSheet P h α β j := hpq
  -- (1) `≤` half: consecutive entries of the sorted `pointsOnSheet` satisfy `p.1 ≤ q.1`.
  set l := pointsOnSheet P h α β j with hl
  have hpw : l.Pairwise (fun a b => decide (a.1 ≤ b.1) = true) := by
    rw [hl, pointsOnSheet]
    exact List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total a.1 b.1) _
  -- Extract the consecutive indices `k, k+1` of `(p, q)` in `l.zip l.tail`.
  change (p, q) ∈ l.zip l.tail at hpq
  rw [List.mem_iff_getElem] at hpq
  obtain ⟨k, hk, hget⟩ := hpq
  rw [List.length_zip] at hk
  have hkl : k < l.length := lt_of_lt_of_le hk (min_le_left _ _)
  have hktail : k < l.tail.length := lt_of_lt_of_le hk (min_le_right _ _)
  rw [List.length_tail] at hktail
  have hk1 : k + 1 < l.length := by omega
  rw [List.getElem_zip, Prod.mk.injEq] at hget
  obtain ⟨hpk, hqtail⟩ := hget
  have htaileq : l.tail[k] = l[k + 1] := by rw [List.getElem_tail]
  rw [htaileq] at hqtail
  -- `p = l[k]`, `q = l[k+1]`, and the Pairwise comparator gives `p.1 ≤ q.1`.
  have hle_dec : decide (l[k].1 ≤ l[k + 1].1) = true :=
    (List.pairwise_iff_getElem.mp hpw) k (k + 1) hkl hk1 (by omega)
  have hle : p.1 ≤ q.1 := by
    rw [← hpk, ← hqtail]; exact of_decide_eq_true hle_dec
  -- (2) `p ≠ q` from distinctness.
  have hne : p ≠ q := edgesOnSheet_distinct P h α β j (p, q) hpq0
  -- (3) rule out `p.1 = q.1` via `sheetRank` injectivity on the good fibre over `p.1`.
  rcases lt_or_eq_of_le hle with hlt | heqx
  · exact hlt
  · exfalso
    obtain ⟨hpmem, hqmem⟩ := edgesOnSheet_mem P h α β j (p, q) hpq0
    obtain ⟨_, hp_curve, hp_io, hp_rank⟩ := hpmem
    obtain ⟨_, hq_curve, _, hq_rank⟩ := hqmem
    -- `p.1 ∉ Bad h`.
    have hbad : p.1 ∉ Bad h := hgood p.1 hp_io
    -- Both `p.2` and `q.2` lie in the fibre over `p.1` (using `q.1 = p.1`).
    have hp2_fib : p.2 ∈ Fibre h p.1 := by
      rw [Fibre, Set.mem_setOf_eq]
      have := mem_evalPlaneZeroSet.mp hp_curve
      simpa using this
    have hq2_fib : q.2 ∈ Fibre h p.1 := by
      rw [Fibre, Set.mem_setOf_eq, heqx]
      have := mem_evalPlaneZeroSet.mp hq_curve
      simpa using this
    -- Equal sheet rank over the shared `x = p.1`.
    have hrank_eq : sheetRank h p.1 p.2 = sheetRank h p.1 q.2 := by
      rw [hp_rank, heqx, hq_rank]
    -- Injectivity on the fibre forces `p.2 = q.2`, hence `p = q`.
    have hy : p.2 = q.2 := sheetRank_injOn_fibre h hbad hp2_fib hq2_fib hrank_eq
    exact hne (Prod.ext heqx hy)

/-- **export-4a (each consecutive edge is a pinned connecting arc).** For every
consecutive pair `(p, q) ∈ edgesOnSheet P h α β j` over a good interval `(α, β)`,
there is a continuous on-curve graph `χ` from `p` to `q` over `[p.1, q.1]`.

Pure glue: `edgesOnSheet_mem` gives both endpoints on the curve, in the interval,
and at the common rank `j`; `edgesOnSheet_fst_lt` gives `p.1 < q.1`. Feeding
`export_3_connecting_arc` with the reach predicate `continuation_reaches` (which
consumes equal rank `sheetRank h p.1 p.2 = sheetRank h q.1 q.2` and the curve fact
at `q`) produces the pinned connecting arc. -/
theorem export_4a_edge_is_arc
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β : ℝ} (j : ℕ)
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p q : ℝ × ℝ} (hpq : (p, q) ∈ edgesOnSheet P h α β j) :
    ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc p.1 q.1) ∧ χ p.1 = p.2 ∧ χ q.1 = q.2 ∧
      (∀ x ∈ Set.Icc p.1 q.1, evalPlane h (x, χ x) = 0) := by
  -- Endpoint facts from the per-sheet bookkeeping.
  obtain ⟨hpmem, hqmem⟩ := edgesOnSheet_mem P h α β j (p, q) hpq
  obtain ⟨_, hp_curve0, hp_io, hp_rank⟩ := hpmem
  obtain ⟨_, hq_curve0, hq_io, hq_rank⟩ := hqmem
  -- On-curve facts in `(·.1, ·.2)` form for `export_3` / `continuation_reaches`.
  have hPcurve : evalPlane h (p.1, p.2) = 0 := by
    have := mem_evalPlaneZeroSet.mp hp_curve0; simpa using this
  have hQcurve : evalPlane h (q.1, q.2) = 0 := by
    have := mem_evalPlaneZeroSet.mp hq_curve0; simpa using this
  -- Interval/ordering data.
  have hP : α < p.1 := hp_io.1
  have hQ : q.1 < β := hq_io.2
  have hxlt : p.1 < q.1 := edgesOnSheet_fst_lt P h j hgood hpq
  -- Equal rank: both classes are `j`.
  have hrank : sheetRank h p.1 p.2 = sheetRank h q.1 q.2 := by rw [hp_rank, hq_rank]
  -- Assemble: `export_3` fed by the `continuation_reaches` pin.
  exact export_3_connecting_arc h hgood hP hQ hxlt hPcurve
    (fun ψ hψc hψP hψcurve =>
      continuation_reaches h hgood hP hQ hxlt hψc hψP hψcurve hQcurve hrank)

end PachDeZeeuw.Algebraic
