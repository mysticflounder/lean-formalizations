# Corollary 24 — per-sheet edge bookkeeping build record (Edge B, `SheetEdges.lean`)

Author: math-prover
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic`. File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/SheetEdges.lean`.

## Scope

This realizes the FLAG `edgesOnSheet-bookkeeping` of the Edge-B assembly design
(`docs/corollary24-E1E2-assembly-design.md` §4.2, §6): the curve analogue of the
landed line-case `pointsOnLine` / `edgesOnLine` bookkeeping
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:322–453`), with the per-line key
`lineKey` replaced by the fibrewise sheet selector
`(p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Ioo α β ∧ sheetRank h p.1 p.2 = j)` and the
mergeSort comparator `p.1 ≤ q.1` (sort each rank-`j` class by `x`).

It is a ROUTINE port: no new analysis. The analytic content (sheet rank, its
fibre-injectivity, the order-preserving continuation) lives in the landed
`SheetRank.lean`; this file only assembles the sorted / nodup / on-curve /
in-interval / length bookkeeping the consecutive-sheet pairing
(`export_4a_edge_is_arc`, a SEPARATE FLAG with its own `sorry`, OUT of scope here)
consumes.

It does **not** prove `export_4a_edge_is_arc`, `component_no_second_sheet`, or any
arc / reach statement. Nothing here depends on `component_no_second_sheet`.

## Status: COMPLETE. No `sorry`, no `native_decide`, no `unsafe`, no `@[implemented_by]`, no `@[extern]`.

Build target: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetEdges`
(from repo root) — `Build completed successfully (8484 jobs)`. My module:
`Built LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetEdges` with no warnings,
no errors, no `sorry`. (The `info:` traces in the full build log are pre-existing
`#check` outputs replayed from the unrelated `CrossingLemma.lean` module, not from
this file.)

Worktree note: the build reuses the parent project's `.lake` build cache (oleans +
mathlib) via a gitignored `.lake` symlink at the worktree root, so the dependency
`SheetRank.olean` and `Mathlib.olean` are replayed rather than rebuilt; only
`SheetEdges` itself elaborates (~20s).

### `#print axioms` (verbatim) — every shipped declaration

```
'PachDeZeeuw.Algebraic.pointsOnSheet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.pointsOnSheet_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.mem_pointsOnSheet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.pointsOnSheet_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.length_pointsOnSheet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.edgesOnSheet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.edgesOnSheet_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.edgesOnSheet_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.length_edgesOnSheet' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.edgesOnSheetWithProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.mem_edgesOnSheetWithProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.length_edgesOnSheetWithProof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exactly `[propext, Classical.choice, Quot.sound]` for all 12. No `sorryAx`, no
`Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom axioms.
(Captured from a transient `#print axioms` block appended to the file, built, then
removed; the shipped file contains no `#print` commands.)

## Definitions

```lean
noncomputable def pointsOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    List (ℝ × ℝ) :=
  (P.filter (fun p => p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Set.Ioo α β ∧ sheetRank h p.1 p.2 = j)).toList.mergeSort
    (fun p q => decide (p.1 ≤ q.1))

noncomputable def edgesOnSheet (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnSheet P h α β j).zip (pointsOnSheet P h α β j).tail
```

Both match the design §4.2 signatures verbatim. `pointsOnSheet` is the rank-`j`
incident points of `P` on `γ = evalPlaneZeroSet h` over `(α,β)`, sorted by `x`;
`edgesOnSheet` zips it with its tail to get consecutive pairs.

Decidability of the `Finset.filter` predicate (membership in the `Set`
`evalPlaneZeroSet h`, plus `sheetRank … = j`) comes from `open scoped Classical`
at file scope — exactly as the line-case file `SzemerediTrotter.lean:32` does it.

## The shipped declarations and their one-line proof strategy

| # | Name | Conclusion | Proof strategy (ports `…`) |
|---|---|---|---|
| def | `pointsOnSheet` | sorted rank-`j` incident list | mergeSort of the filtered `.toList` |
| 1 | `pointsOnSheet_perm` | `Perm` of the filtered `.toList` | `List.mergeSort_perm` (ports `pointsOnLine_perm`) |
| 2 | `mem_pointsOnSheet` | `p ∈ …` ⇔ `p∈P ∧ on-curve ∧ p.1∈Ioo α β ∧ sheetRank=j` | `perm.mem_iff` + `Finset.mem_toList` + `Finset.mem_filter` (ports `mem_pointsOnLine`; the **only** decl whose RHS conjunction differs) |
| 3 | `pointsOnSheet_nodup` | `Nodup` | `perm.nodup_iff` + `Finset.nodup_toList` (ports `pointsOnLine_nodup`) |
| 4 | `length_pointsOnSheet` | `length = (P.filter <pred>).card` | `perm.length_eq` + `Finset.length_toList` (ports `length_pointsOnLine`) |
| def | `edgesOnSheet` | consecutive pairs | `zip` with tail |
| 5 | `edgesOnSheet_distinct` | `∀ e, e.1 ≠ e.2` | nodup + adjacent-index `getElem_inj_iff` (ports `edgesOnLine_distinct` **unchanged**) |
| 6 | `edgesOnSheet_mem` | both endpoints satisfy the full predicate | `List.of_mem_zip` + `mem_of_mem_tail` + `mem_pointsOnSheet` (ports `edgesOnLine_mem`) |
| 7 | `length_edgesOnSheet` | `length+1 = pts.length ∨ edges = []` | `List.length_zip`/`length_tail` + `omega` (ports `length_edgesOnLine`) |
| def | `edgesOnSheetWithProof` | edges bundled with `e.1 ≠ e.2` | `pmap` over `edgesOnSheet_distinct` (ports `edgesOnLineWithProof`) |
| 8a | `mem_edgesOnSheetWithProof` | bundled `.1` is a genuine edge | `List.mem_pmap` (ports `mem_edgesOnLineWithProof`) |
| 8b | `length_edgesOnSheetWithProof` | `length = edgesOnSheet.length` | `List.length_pmap` (ports `length_edgesOnLineWithProof`) |

The task asked for the nine line-case analogues (the two defs + lemmas 1–7) and
the **bonus** `WithProof` family (#8a/#8b) "only if it ports trivially." It ports
trivially — the distinctness obligation `edgesOnSheet_distinct` is already proven,
so the `pmap` and its two facts are free — so the bonus is included. 12 shipped
declarations total.

### Why the port is verbatim except in two places

The two structural changes vs the line case are confined exactly where the design
predicts:

- **Filter predicate** is a conjunction `(on-curve ∧ x∈Ioo α β ∧ sheetRank=j)`
  instead of the single `p ∈ ℓ`. This shows through **only** in `mem_pointsOnSheet`
  (#2), whose right-hand side is the 4-fold conjunction `p∈P ∧ on-curve ∧ … ∧ …`.
  `pointsOnSheet_perm`, `pointsOnSheet_nodup`, and `length_pointsOnSheet` carry the
  predicate opaquely (the `Perm` / `Nodup` / `length` facts of a mergeSort of a
  Finset's `.toList` are independent of *which* predicate filtered it).
- **Comparator** is `decide (p.1 ≤ q.1)` instead of `decide (lineKey ℓ p ≤ lineKey ℓ q)`.
  No nodup / membership / length proof inspects the comparator: `List.mergeSort_perm`
  holds for any comparator, and distinctness (#5) uses only `Nodup`. So
  `edgesOnSheet_distinct`, `edgesOnSheet_mem`, `length_edgesOnSheet`, and the
  `WithProof` family are byte-for-byte structural ports.

## Landed API consumed (read from source this session)

- `evalPlaneZeroSet`, `mem_evalPlaneZeroSet` (`LocalArc.lean:48,51`, the `Iff.rfl`
  membership simp lemma — the design brief misattributed this to
  `DecompositionDefs.lean`; it is in `LocalArc.lean`, transitively imported via
  `SheetRank → SheetCount → MonotoneArc → … → LocalArc`).
- `sheetRank` (`SheetRank.lean:30`), `Fibre`, `Bad`, `PlanePoly`, `evalPlane`
  (`DecompositionDefs.lean`, `LocalArc.lean`) — used only inside the filter
  predicate; no `sheetRank` *lemma* is invoked here (the bookkeeping is
  predicate-agnostic, so `sheetRank_injOn_fibre` etc. are NOT consumed by this file
  — they enter at `export_4a_edge_is_arc`, the next step).
- mathlib (all already used by the line-case model, so available in this toolchain):
  `List.mergeSort_perm`, `List.Perm.mem_iff`/`.nodup_iff`/`.length_eq`,
  `Finset.mem_toList`, `Finset.mem_filter`, `Finset.nodup_toList`,
  `Finset.length_toList`, `List.mem_iff_getElem`, `List.length_zip`,
  `List.getElem_zip`, `List.getElem_tail`, `List.length_tail`,
  `List.Nodup.getElem_inj_iff`, `List.of_mem_zip`, `List.mem_of_mem_tail`,
  `List.length_eq_zero_iff`, `List.mem_pmap`, `List.length_pmap`.

## Structural assumptions / where finiteness enters

- **No analytic hypothesis is used.** Unlike `SheetRank.lean`, this file proves no
  statement that needs `x ∉ Bad h` / a good interval / finite fibres. `α`, `β`, `j`
  are free parameters; `sheetRank h p.1 p.2 = j` is just a decidable predicate on
  points. The good-interval condition `p.1 ∈ Ioo α β` is carried as data in the
  filter and re-exported by `mem_pointsOnSheet` / `edgesOnSheet_mem`, but it is not
  *assumed* as a hypothesis and nothing here proves anything from it. (`sheetRank`
  is defined as an `ncard`, total over all `x,y`; over a bad `x` it may be the
  `ncard` of an infinite set, i.e. `0` by the mathlib `ncard` convention — irrelevant
  here, since the bookkeeping never evaluates it.)
- **Finiteness** enters only through `P : Finset (ℝ × ℝ)`: `Finset.filter` of a
  Finset is a Finset, `.toList` is a finite list, and all length / nodup facts are
  about that finite list. This is the same finiteness the line case uses.

## PROVEN / CONJECTURED classification

| Item | Statement | Status |
|---|---|---|
| `pointsOnSheet` | def: sorted rank-`j` incident list | DEFINITION |
| `pointsOnSheet_perm` (1) | `Perm` of the filtered `.toList` | **PROVEN** (axiom-clean) |
| `mem_pointsOnSheet` (2) | membership ⇔ in-`P` ∧ on-curve ∧ in-interval ∧ rank `j` | **PROVEN** (axiom-clean) |
| `pointsOnSheet_nodup` (3) | no repeats | **PROVEN** (axiom-clean) |
| `length_pointsOnSheet` (4) | `length = filtered card` | **PROVEN** (axiom-clean) |
| `edgesOnSheet` | def: consecutive pairs | DEFINITION |
| `edgesOnSheet_distinct` (5) | every edge has distinct endpoints | **PROVEN** (axiom-clean) |
| `edgesOnSheet_mem` (6) | both endpoints satisfy the full predicate | **PROVEN** (axiom-clean) |
| `length_edgesOnSheet` (7) | `k` points → `k−1` edges (or empty) | **PROVEN** (axiom-clean) |
| `edgesOnSheetWithProof` | def: edges bundled with distinctness | DEFINITION |
| `mem_edgesOnSheetWithProof` (8a) | bundled `.1` is a genuine edge | **PROVEN** (axiom-clean) |
| `length_edgesOnSheetWithProof` (8b) | `pmap` preserves length | **PROVEN** (axiom-clean) |
| `export_4a_edge_is_arc` | each consecutive edge is a pinned arc | **OUT OF SCOPE — separate FLAG (design §4.2), not in this file** |
| `component_no_second_sheet` | single-valued band-good strip component | **OPEN — not consumed here, off critical path** |

Every non-definition row is PROVEN with kernel-checked axiom closure exactly
`[propext, Classical.choice, Quot.sound]`. None is EMPIRICALLY VERIFIED,
CONJECTURED, or HEURISTIC; none depends on `component_no_second_sheet` or on any
`sorry`.

## Deviations from the design §4.2 signatures

None for the in-scope items. The two defs (`pointsOnSheet`, `edgesOnSheet`) are
verbatim the design §4.2 code. The lemma names follow the task's suggested names
and the line-case names with `Line→Sheet`. One difference from the line-case
*shape* (not the design, which does not spell the lemmas): `edgesOnSheet_mem`'s
conclusion is the **4-fold** predicate `(e.i ∈ P ∧ on-curve ∧ x∈Ioo α β ∧ rank=j)`
for each endpoint, where the line case's `edgesOnLine_mem` has the **2-fold**
`(e.i ∈ P ∧ e.i ∈ ℓ)` — this is forced by the richer filter predicate and is
exactly the curve analogue the design §4.2 calls for ("on-curve, in-interval").

Every item that did NOT port cleanly: **none.** All 12 declarations ported; the
bonus `WithProof` trio that the task said to include "only if trivial" was trivial
(its sole obligation `edgesOnSheet_distinct` is already discharged) and is included.

## Relationship to the design doc and what next

`pointsOnSheet` / `edgesOnSheet` are the design §4.2 / §6 FLAG `edgesOnSheet-bookkeeping`,
and the `sheetrank-build` record's "What next" item #2. With this landed, the next
steps (unchanged from that record) are:

1. **`export_4a_edge_is_arc`** (design §4.2, the `sorry` in §4.2): each consecutive
   edge `(p,q) ∈ edgesOnSheet` is a pinned connecting arc. Glue over
   `export_3_connecting_arc` + `continuation_reaches` (landed in `SheetRank.lean`)
   + the `edgesOnSheet_mem` / `edgesOnSheet_distinct` facts landed here (these give
   `p,q` on-curve, in-interval, same rank `j`, and `p ≠ q`; the missing `p.1 < q.1`
   ordering datum comes from the mergeSort `p.1 ≤ q.1` comparator and nodup — a
   sortedness lemma not in this bookkeeping scope, to be added where the arc
   direction is needed).
2. **`export_4b_interior_disjoint`** (design §4.3): cross-sheet / cross-interval
   interiors disjoint; route through landed `decomp_D1_goodLocus_components` +
   `sheetRank` injectivity.
3. **`edgeB_crossingInput`** (design §5): the top-level multigraph discharge.

Wiring `SheetEdges` into the `LeanFormalizations.lean` aggregator and the
`CrossingLemma.lean` import is left to the assembly/validation step (out of this
file's scope; the orchestrator wires the import).
