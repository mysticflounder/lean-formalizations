# Corollary 24 — each consecutive sheet edge is a pinned connecting arc (Edge B, `EdgeArc.lean`)

Author: math-prover
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic`. File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeArc.lean`.

## Scope

This realizes the FLAG `edge-is-arc (export-4a)` of the Edge-B assembly design
(`docs/corollary24-E1E2-assembly-design.md` §4.2): for every consecutive pair
`(p, q) ∈ edgesOnSheet P h α β j` over a good interval `(α, β)`, there is a
continuous on-curve graph `χ` from `p` to `q` over `[p.1, q.1]` — a
`SimpleCurveArc`-ready connecting arc.

It is GLUE over already-landed leaves; no new analysis. The analytic content
lives in the landed `SheetRank.lean` (`continuation_reaches`, the order-preserving
continuation; `sheetRank_injOn_fibre`, rank injective on a good fibre) and
`ConnectingArc.lean` (`export_3_connecting_arc`, the `decomp_arc_on_good`
continuation graph pinned to `q`). This file only (A) proves the one supporting
sortedness lemma `edgesOnSheet_fst_lt` (strict `x`-increase along consecutive
edges), and (B) composes the landed leaves into `export_4a_edge_is_arc`.

It does **not** prove `export_4b_interior_disjoint`, `component_no_second_sheet`,
or any new arc/reach statement. Nothing here depends on
`component_no_second_sheet`.

## Status: COMPLETE. No `sorry`, no `native_decide`, no `unsafe`, no `@[implemented_by]`, no `@[extern]`, no `#print`/`#check`/`#eval`.

Build target: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeArc`
(from repo root) — `Build completed successfully (8487 jobs)`. My module:
`Built LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeArc (3.4s)` with no
warnings, no errors, no `sorry`. (The `info:` traces in the full build log are
pre-existing `#check` outputs replayed from the unrelated `CrossingLemma.lean`
module — `CrossingLemmaMultigraphStatement`, `vertexRotation`,
`rotation_wellDefined`, etc. — not from this file.)

Worktree note: the build reuses the parent project's `.lake` build cache (oleans +
mathlib) via a gitignored `.lake` symlink at the worktree root, so dependency
oleans (`SheetEdges.olean`, `ConnectingArc.olean`, `SheetRank.olean`,
`Mathlib.olean`) are replayed rather than rebuilt; only `EdgeArc` itself
elaborates (~3–4s). Base commit `a267c60` (worktree fast-forwarded to it; all
dependencies — `SheetRank`, `SheetEdges`, `ConnectingArc` — landed there).

### `#print axioms` (verbatim) — both shipped theorems

```
'PachDeZeeuw.Algebraic.edgesOnSheet_fst_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.export_4a_edge_is_arc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exactly `[propext, Classical.choice, Quot.sound]` for both. No `sorryAx`, no
`Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom axioms.
(Captured from a transient `#print axioms` block appended to the file, built, then
removed; the shipped file contains no `#print` commands.)

## The two shipped declarations and their proof strategy

### (A) `edgesOnSheet_fst_lt` — strict `x`-increase along consecutive edges

```lean
theorem edgesOnSheet_fst_lt (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β : ℝ} (j : ℕ)
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p q : ℝ × ℝ} (hpq : (p, q) ∈ edgesOnSheet P h α β j) :
    p.1 < q.1
```

Proof, in three steps:

1. **`≤` half via the `mergeSort` sortedness lemma.** `pointsOnSheet` is
   `(… filter …).toList.mergeSort (fun p q => decide (p.1 ≤ q.1))`. The mathlib /
   Lean-core lemma used is **`List.pairwise_mergeSort`** (the canonical name;
   `List.sorted_mergeSort` is a deprecated `abbrev` for it since 2025-10-23, and
   `Mathlib.Data.List.Sort`'s `sorted_mergeSort'` is also deprecated in favor of
   `pairwise_mergeSort'`). Its signature is
   `pairwise_mergeSort (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a) (l) : (mergeSort l le).Pairwise le`,
   here with `le = fun p q => decide (p.1 ≤ q.1)`. The two side conditions are
   discharged from `ℝ`'s order: `trans` is `le_trans` after
   `simp only [decide_eq_true_eq]`, `total` is `le_total a.1 b.1` after
   `simp only [Bool.or_eq_true, decide_eq_true_eq]`. This yields
   `(pointsOnSheet …).Pairwise (fun a b => decide (a.1 ≤ b.1) = true)`.
   From `(p, q) ∈ l.zip l.tail` (the `change`/`List.mem_iff_getElem` extraction
   ported byte-for-byte from the landed `edgesOnSheet_distinct`), `p` and `q` sit
   at consecutive indices `k, k+1` of `l` (`p = l[k]`, `q = l.tail[k] = l[k+1]` via
   `List.getElem_zip`/`List.getElem_tail`). **`List.pairwise_iff_getElem`**
   (`Pairwise R l ↔ ∀ i j (hi) (hj), i < j → R l[i] l[j]`) applied at `(k, k+1)`
   gives `decide (l[k].1 ≤ l[k+1].1) = true`, and `of_decide_eq_true` plus the two
   index equalities give `p.1 ≤ q.1`.

2. **`p ≠ q`** from the landed `edgesOnSheet_distinct P h α β j (p, q)` (fed the raw
   membership, saved as `hpq0` before the index extraction destructures the working
   copy `hpq`).

3. **Rule out `p.1 = q.1`** (the strict-ordering argument). From
   `lt_or_eq_of_le hle`, the `<` case is the goal; in the `=` case
   (`heqx : p.1 = q.1`) derive a contradiction: the landed
   `edgesOnSheet_mem P h α β j (p, q)` gives both endpoints on the curve, in the
   interval, and at rank `j` — in particular `evalPlane h p = 0`, `evalPlane h q = 0`,
   `p.1 ∈ Ioo α β`, `sheetRank h p.1 p.2 = j`, `sheetRank h q.1 q.2 = j`. Then
   `p.1 ∉ Bad h` from `hgood p.1 hp_io`; both `p.2` and `q.2` lie in `Fibre h p.1`
   (`mem_evalPlaneZeroSet` + the `Fibre`/`setOf` unfold, using `heqx` to move `q`'s
   curve fact over `q.1` to one over `p.1`); and `sheetRank h p.1 p.2 = sheetRank h p.1 q.2`
   (both `= j` via `heqx`). **`sheetRank_injOn_fibre h hbad`** (`Set.InjOn`) then
   forces `p.2 = q.2`, so `p = q` by `Prod.ext heqx hy`, contradicting step (2).

### (B) `export_4a_edge_is_arc` — pure glue

```lean
theorem export_4a_edge_is_arc
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β : ℝ} (j : ℕ)
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p q : ℝ × ℝ} (hpq : (p, q) ∈ edgesOnSheet P h α β j) :
    ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc p.1 q.1) ∧ χ p.1 = p.2 ∧ χ q.1 = q.2 ∧
      (∀ x ∈ Set.Icc p.1 q.1, evalPlane h (x, χ x) = 0)
```

Proof: `edgesOnSheet_mem` gives `evalPlane h p = 0`, `evalPlane h q = 0`,
`p.1 ∈ Ioo α β`, `q.1 ∈ Ioo α β`, `sheetRank h p.1 p.2 = j`, `sheetRank h q.1 q.2 = j`.
The two curve facts are rewritten into `(·.1, ·.2)` form
(`evalPlane h (p.1, p.2) = 0`, `evalPlane h (q.1, q.2) = 0`) by
`mem_evalPlaneZeroSet.mp … |> simpa` (Prod eta collapses `p`↔`(p.1, p.2)`). Set
`hP : α < p.1 := hp_io.1`, `hQ : q.1 < β := hq_io.2`,
`hxlt : p.1 < q.1 := edgesOnSheet_fst_lt P h j hgood hpq`,
`hrank : sheetRank h p.1 p.2 = sheetRank h q.1 q.2 := by rw [hp_rank, hq_rank]`.
Then
```lean
exact export_3_connecting_arc h hgood hP hQ hxlt hPcurve
  (fun ψ hψc hψP hψcurve =>
    continuation_reaches h hgood hP hQ hxlt hψc hψP hψcurve hQcurve hrank)
```
The `∃ χ` `export_3_connecting_arc` returns is over `Icc xP xQ = Icc p.1 q.1` with
`xP=p.1, yP=p.2, xQ=q.1, yQ=q.2`, matching the goal exactly.

## Landed API consumed (read from source this session)

- `SheetEdges.lean`: `pointsOnSheet` (def — its `mergeSort` comparator
  `fun p q => decide (p.1 ≤ q.1)` is unfolded in step (A.1)), `edgesOnSheet`
  (def, `= (pointsOnSheet …).zip (pointsOnSheet …).tail`),
  `edgesOnSheet_distinct` (explicit args, `∀ e ∈ edgesOnSheet, e.1 ≠ e.2`),
  `edgesOnSheet_mem` (explicit args, the 4-fold predicate for both endpoints).
- `SheetRank.lean`: `sheetRank` (def), `sheetRank_injOn_fibre (h) (hx : x ∉ Bad h) : Set.InjOn (sheetRank h x) (Fibre h x)`,
  `continuation_reaches (h) (hgood) (hPα : α < xP) (hQβ : xQ < β) (hxlt : xP < xQ) (hψ_cont) (hψ_xP) (hψ_curve) (hQcurve) (hrank) : ψ xQ = yQ`.
- `ConnectingArc.lean`: `export_3_connecting_arc (h) (hgood) (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ) (hPcurve) (hreach) : ∃ χ, …`.
  **Note (deviation from the task brief's stated signature):** the source
  `export_3_connecting_arc` does **not** take `hQcurve` as a top-level argument —
  `yQ`/`hQcurve` enter only through the `hreach` predicate's conclusion. So
  `hQcurve` is consumed inside the `continuation_reaches` closure passed as
  `hreach`, not as a separate positional argument. (See "Deviations" below.)
- `LocalArc.lean`: `evalPlaneZeroSet`, `mem_evalPlaneZeroSet` (the `@[simp]`
  `Iff.rfl` membership lemma).
- `DecompositionDefs.lean`: `Fibre h x = {y | evalPlane h (x, y) = 0}`, `Bad`,
  `PlanePoly`, `evalPlane`.
- mathlib / Lean core: `List.pairwise_mergeSort`, `List.pairwise_iff_getElem`,
  `List.mem_iff_getElem`, `List.length_zip`, `List.getElem_zip`,
  `List.getElem_tail`, `List.length_tail`, `decide_eq_true_eq`, `Bool.or_eq_true`,
  `of_decide_eq_true`, `le_trans`, `le_total`, `lt_or_eq_of_le`, `Prod.mk.injEq`,
  `Prod.ext`, `min_le_left`, `min_le_right`.

## Structural assumptions / where finiteness enters

- **Sortedness (A.1) uses no analytic hypothesis.** `List.pairwise_mergeSort` needs
  only that the comparator's underlying relation is transitive and total — supplied
  by `le_trans`/`le_total` on `ℝ`'s first coordinate. The `mergeSort` comparator and
  the consecutive-index extraction are predicate-agnostic, exactly as the landed
  `edgesOnSheet_distinct` is.
- **The strict-ordering step (A.3) uses the good-interval hypothesis.** Ruling out
  `p.1 = q.1` requires `p.1 ∉ Bad h`, obtained from `hgood` applied to the
  in-interval datum `p.1 ∈ Ioo α β` carried by `edgesOnSheet_mem`. `sheetRank`
  injectivity (`sheetRank_injOn_fibre`) is itself a good-fibre statement (finite
  fibre over a good `x`); its finiteness lives in the landed `SheetRank.lean`
  (`finite_fibre_iio`), not re-proved here.
- **The arc (B) uses the good-interval hypothesis** through both landed leaves:
  `export_3_connecting_arc` (which calls `decomp_arc_on_good`) and
  `continuation_reaches` both require `hgood`, `α < p.1`, `q.1 < β`, `p.1 < q.1`.
  All the analytic finiteness/continuity content is inside those landed leaves.
- **Finiteness of `P`** enters only through `edgesOnSheet`/`pointsOnSheet` being a
  `mergeSort` of a `Finset`'s `.toList` (a finite list), inherited from
  `SheetEdges.lean`. No new finiteness is introduced.

## PROVEN / CONJECTURED classification

| Item | Statement | Status |
|---|---|---|
| `edgesOnSheet_fst_lt` (A) | consecutive edge `⟹` `p.1 < q.1` | **PROVEN** (axiom-clean) |
| `export_4a_edge_is_arc` (B) | each consecutive edge is a pinned connecting arc | **PROVEN** (axiom-clean) |
| `export_4b_interior_disjoint` | cross-sheet / cross-interval interiors disjoint | **OUT OF SCOPE — separate FLAG (design §4.3), not in this file** |
| `component_no_second_sheet` | single-valued band-good strip component | **OPEN — not consumed here, off critical path** |

Both shipped rows are PROVEN with kernel-checked axiom closure exactly
`[propext, Classical.choice, Quot.sound]`. Neither is EMPIRICALLY VERIFIED,
CONJECTURED, or HEURISTIC; neither depends on `component_no_second_sheet` or on any
`sorry`. (The design doc previously listed `export_4a_edge_is_arc` as
"CONJECTURED-constructible"; this file discharges it to PROVEN — the construction
is the composition above.)

## Deviations from the design §4.2 signatures

- **`export_4a_edge_is_arc` and `edgesOnSheet_fst_lt` statements match the task
  brief verbatim** (same binders, same implicit/explicit split, same conclusion).
- **`edgesOnSheet_fst_lt` is the added supporting helper** the brief asked for; it
  is not in the design §4.2 code block (the design's §4.2 `sorry` comment only
  *names* the "`p.1 < q.1` (sorted, nodup)" datum). The brief's suggested name and
  signature are used unchanged.
- **One composition-call deviation, forced by the landed source (not a change to
  any statement):** the brief's spelled-out `exact` line passed `hQcurve` as a
  positional argument to `export_3_connecting_arc`. The actual landed
  `export_3_connecting_arc` (read from `ConnectingArc.lean:46`) takes no `hQcurve`
  argument — its `yQ` is pinned solely through the `hreach` predicate. So the
  realized call passes `hQcurve` into the `continuation_reaches` closure (the
  `hreach` argument) instead. Functionally identical to the brief's intent; only
  the argument position differs.
- **Prod-eta rewrites (`simpa`):** the curve facts from `edgesOnSheet_mem` are
  `evalPlane h p = 0` (with `p : ℝ × ℝ`); `export_3`/`continuation_reaches` want
  `evalPlane h (p.1, p.2) = 0`. These are definitionally equal (Prod eta), bridged
  by `mem_evalPlaneZeroSet.mp … |> simpa`. The brief anticipated this ("Prod eta;
  `evalPlane h p = evalPlane h (p.1, p.2)`").
- **`hpq0` save:** the raw membership `(p, q) ∈ edgesOnSheet …` is saved under
  `hpq0` before the index extraction in (A) destructures the working copy `hpq`, so
  `edgesOnSheet_distinct`/`edgesOnSheet_mem` get a live membership argument. A
  proof-engineering detail, not a statement change.

## Relationship to the design doc and what next

`edgesOnSheet_fst_lt` + `export_4a_edge_is_arc` are the design §4.2 / §6 FLAG
`edge-is-arc (export-4a)`. With this landed, the remaining Edge-B steps (unchanged
from the `sheetedges-build` record) are:

1. **`export_4b_interior_disjoint`** (design §4.3): cross-sheet / cross-interval
   interiors disjoint; route through landed `decomp_D1_goodLocus_components` +
   `sheetRank` injectivity.
2. **`edgeBMultigraph` + `edgeB_crossingInput`** (design §5): the curve analogue of
   `stMultigraph` and its six crossing-lemma discharge facts; `ArcsJoinEndpoints`
   ← `export_4a_edge_is_arc` (each edge's arc joins its endpoints, now available).

Wiring `EdgeArc` into the `LeanFormalizations.lean` aggregator and the
`CrossingLemma.lean` import is left to the assembly/validation step (out of this
file's scope; the orchestrator wires the import).
