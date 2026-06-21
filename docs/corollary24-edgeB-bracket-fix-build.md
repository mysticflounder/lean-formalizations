# Corollary 24 — Edge-B bracket-coverage fix (build record, phase 1)

Author: Adam McKenna
Date: 2026-06-21
Status: **LANDED (phase 1)** — the `P`-aware bracketing fix is implemented and green.
The coverage lemma `goodIntervalsBundle_covers` is PROVEN (sorry-free). Discharges
(v) `arcsJoinEndpoints` and (vi) `WellDrawn` re-validated green against the fixed
definition. E1 (`EdgeBE1.lean`) and Multiplicity (`EdgeBMultiplicity.lean`) remain
separate later phases.

Implements the fix specified in `corollary24-edgeB-bracket-coverage-fix.md`. That doc
holds the verified diagnosis of the defect; this doc records the implementation.

## Threading decision: `P` (not bare `R`)

The brackets are threaded with the **point set `P`**, and the bound `R` is derived
internally as `R := xBound P`. Rationale:

* The coverage lemma is stated `goodIntervalsBundle_covers (P) (H)`, so
  `goodIntervalsBundle` must take `P`.
* `allCurveEdges d P Γ` already has `P` in scope, so `classKeys d P H` slots in with
  no new top-level argument and `allCurveEdges` is unchanged in its argument list.
* The real `(α,β)` interface of `pointsOnSheet`/`edgesOnSheet` (`SheetEdges.lean`) is
  **unchanged** — only the bracket *values* and the `goodIntervalsBundle`/`classKeys`/
  `bracketOfComp`/`compSet_eq` *signatures* change.

### The `P`-bound `R = xBound P`

```
noncomputable def xBound (P : Finset (ℝ × ℝ)) : ℝ :=
  (insert (0 : ℝ) (P.image (fun p => |p.1|))).max' (Finset.insert_nonempty _ _)

theorem xBound_spec (P) : ∀ p ∈ P, |p.1| ≤ xBound P
```

The `insert 0` keeps the finset nonempty even when `P = ∅`, so `max'` is total without
a nonemptiness side-goal. `xBound_spec` is `Finset.le_max'` composed with
`Finset.mem_insert_of_mem ∘ Finset.mem_image_of_mem`.

## The P-aware bracket design

`realBracketOfEReal` gains a real parameter `R`; only the three **unbounded** cases
change (bounded `(r,s) ↦ (r,s)` and the unsatisfiable `(0,0)` cases are unchanged):

| EReal component | old bracket (defective) | new bracket (`R`-aware) |
|---|---|---|
| `(⊥, ⊤)` | `(0, 0)` = ∅ | `(-(R+1), R+1)` |
| `(⊥, s)` | `(s-1, s)` | `(-(R+1), s)` |
| `(r, ⊤)` | `(r, r+1)` | `(r, R+1)` |

The unsatisfiable EReal shapes (`(⊥,⊥)`, `(⊤,_)`, `(r,⊥)`) keep `(0,0)` (their
component is empty, so `Ioo 0 0 = ∅ ⊆ ∅` discharges the subset obligation vacuously).

### Subset obligation preserved (re-proved with new witnesses)

`realBracketOfEReal`'s existing payload
`Set.Ioo ab.1 ab.2 ⊆ {x | a < ↑x ∧ ↑x < b}` still holds: each new bracket is still
inside its open EReal component.

* `(⊥,⊤)`: lower `⊥ < ↑x` always (`EReal.bot_lt_coe`), upper `↑x < ⊤` always
  (`EReal.coe_lt_top`).
* `(⊥,s)`: lower always; upper `↑x < ↑s` from `x < s` (`EReal.coe_lt_coe_iff`).
* `(r,⊤)`: lower `↑r < ↑x` from `r < x`; upper always.

(The old `(0,0)` cases for these three used the vacuous `Set.Ioo_self` route; the new
proofs are the genuine in-component containments.)

## What changed in each file

### `EdgeBMultigraph.lean` (definitional layer, discharge i/ii)

* **NEW** `xBound` / `xBound_spec` (the `P`-bound).
* `realBracketOfEReal (a b)` → `realBracketOfEReal (R : ℝ) (a b)`; three unbounded
  cases rebracketed to `R+1` form (above).
* **NEW** `realBracketOfEReal_covers (R) (a b) {x} (hxR : |x| ≤ R) (hcomp : a < ↑x ∧ ↑x < b) :
  x ∈ Ioo (realBracketOfEReal R a b).1.1 (realBracketOfEReal R a b).1.2` — the converse
  of the subset obligation (per-component coverage core). Case analysis mirrors the
  bracket `match`; unsatisfiable shapes are vacuous via `not_lt_bot` / `not_top_lt`; the
  three unbounded cases use `|x| ≤ R ⟹ -R ≤ x ≤ R` plus `linarith`; bounded/half-bounded
  use `EReal.coe_lt_coe_iff`.
* `goodIntervalsBundle {d} (H)` → `goodIntervalsBundle {d} (P) (H)`; the `let br :=`
  binding now reads `realBracketOfEReal (xBound P) a b`. The stored `hgood`
  (`Bad`-avoidance) proof is unchanged in structure (it only uses bracket-⊆-component).
* **NEW** `goodIntervalsBundle_covers` (the coverage payoff — statement and proof below).
* `classKeys (d) (H)` → `classKeys (d) (P) (H)`; passes `P` to `goodIntervalsBundle`.
* `allCurveEdges`: the `classKeys d H` call → `classKeys d P H` (argument list of
  `allCurveEdges` itself unchanged — it already took `P`).
* `edgeBMultigraph_numEdges_eq_sum`: the `classKeys d H` in its statement → `classKeys d P H`.
* **Survived (only `hgood`-dependent, bracket-value-independent):** `EdgeBEdge` and all
  its lemmas (`fst_mem`, `snd_mem`, `fst_lt`, `chi`, `chi_spec`, `arc`, `arc_endAnchor`);
  `edgeBMultigraph` itself; `edgeBMultigraph_card_V` (rfl); `edgeBMultigraph_numEdges`
  (rfl); the `edgeBMultigraph_numEdges_eq_sum` *proof* (shape-only, unchanged).

### `EdgeBWellDrawn.lean` (discharge vi)

Re-threaded (signature only; proof bodies transfer because they rest on
bracket-⊆-component + pairwise-disjoint components ⟹ pairwise-disjoint brackets, both
preserved):

* `bracketOfComp {d} (H) (jcomp)` → `bracketOfComp {d} (P) (H) (jcomp)`;
  `realBracketOfEReal …` → `realBracketOfEReal (xBound P) …`.
* `compSet_eq (H) (jcomp)` → `compSet_eq (P) (H) (jcomp)` (statement + the `realBracketOfEReal`
  / `bracketOfComp` references inside it carry `P` / `xBound P`).
* `goodIntervalsBundle_pairwise_disjoint_Ioo (H)` → `(P) (H)` (statement + its internal
  `compSet_eq P H` calls).
* `goodIntervalsBundle_mem_component (H)` → `(P) (H)` (statement + `compSet_eq P H`).
* `goodIntervalsBundle_no_overlap (H)` → `(P) (H)` (statement + `goodIntervalsBundle_mem_component P H`).
* `allCurveEdges_provenance`: statement `goodIntervalsBundle H` → `goodIntervalsBundle P H`
  (proof unchanged — `rw [allCurveEdges]` / `rw [classKeys]` unfold the P-threaded defs).
* `curveBlock_eq`: `classKeys d H` / `goodIntervalsBundle H` → `… P …`.
* `curveBlock_nodup`: statement `goodIntervalsBundle H` → `goodIntervalsBundle P H`;
  body `goodIntervalsBundle_pairwise_disjoint_Ioo H` → `… P H`.
* `edgeB_same_curve_shared_point_params`: body `goodIntervalsBundle_no_overlap H₁` → `… P H₁`.
* **UNCHANGED (EReal-component facts, bracket-independent):** `compIdx`, `compFintype`,
  `compSet`, `compSet_pairwise_disjoint`. Also unchanged: everything in §1–2 and §6–8
  (`pointsOnSheet_*`, `edgesOnSheet_*`, the crossing-injection / fibre-bound machinery,
  `edgeBMultigraph_wellDrawn` itself), and `allCurveEdges_nodup`.

### `EdgeBArcsJoin.lean` (discharge v)

**No edits.** `edgeBMultigraph_arcsJoinEndpoints` uses only `allCurveEdges d P Γ` (argument
list unchanged) and `EdgeBEdge.arc_endAnchor` (unchanged). Builds green untouched.

## The coverage lemma (PROVEN, sorry-free)

```
theorem goodIntervalsBundle_covers {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    ∀ p ∈ P, p.1 ∉ Bad H.1 →
      ∃ gi ∈ goodIntervalsBundle P H, p.1 ∈ Set.Ioo gi.1.1 gi.1.2
```

Proof sketch:
1. `p.1 ∉ Bad H.1` is `p.1 ∈ GoodLocus H.1` definitionally (`GoodLocus h := (Bad h)ᶜ`).
2. Reconstruct the `Classical.choose` chain of `decomp_D1_goodLocus_components`
   (`h0 → ι → instι → I → hI`); `hI.2.2.1 : GoodLocus H.1 = ⋃ k, I k`, so
   `p.1 ∈ ⋃ k, I k`, giving a component index `jcomp` with `p.1 ∈ I jcomp`
   (`Set.mem_iUnion`).
3. `I jcomp = {x | a < ↑x ∧ ↑x < b}` (the per-component EReal-shape witness `hI.1 jcomp`,
   `a`/`b` its chosen endpoints), so `a < ↑p.1 ∧ ↑p.1 < b`.
4. `|p.1| ≤ xBound P` (`xBound_spec`), so `realBracketOfEReal_covers (xBound P) a b` gives
   `p.1 ∈ Ioo (realBracketOfEReal (xBound P) a b).1.1 .1.2`.
5. The `goodIntervalsBundle P H` entry at `jcomp` is the `.map` image of `jcomp ∈ univ`
   (`List.mem_map_of_mem ∘ Finset.mem_toList`), and its `.1` bracket is exactly
   `(realBracketOfEReal (xBound P) a b).1` **definitionally** (`a`/`b` are the chosen
   endpoints for `jcomp`), so the membership target reduces to step 4's `hcov`.

This is the concrete witness that the fix achieves coverage: every good-`x` `P`-point
lands in a bundle bracket. The defect was that for unbounded components the old finite
bracket missed `Θ(|P|)` such points (the `h = y`, `P = {(1,0),…,(k,0)}` counterexample
in the diagnosis doc); with `R = xBound P` none escape.

## Gate results

Built with `./lake-build.sh <Module>` (Lean v4.30.0, mathlib v4.30.0), worktree
`.lake/build` copied from parent + `.lake/packages` symlinked.

| Target | Result |
|---|---|
| `…CrossingLemma.EdgeBMultigraph` | green, 8494 jobs |
| `…CrossingLemma.EdgeBWellDrawn`  | green, 8495 jobs |
| `…CrossingLemma.EdgeBArcsJoin`   | green, 8495 jobs |
| `…CrossingLemma.CrossingLemma` (aggregator) | green, 8475 jobs |

No `sorry`, no `native_decide`, no `unsafe`/`@[implemented_by]`/`@[extern]`, no `axiom`.

### Axiom closures (independent `#print axioms`, throwaway `lake env lean` file)

All four required declarations:

```
edgeBMultigraph                 : [propext, Classical.choice, Quot.sound]
edgeBMultigraph_wellDrawn       : [propext, Classical.choice, Quot.sound]
edgeBMultigraph_arcsJoinEndpoints : [propext, Classical.choice, Quot.sound]
goodIntervalsBundle_covers      : [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`/`Lean.ofReduceNat`, no custom axioms — Lean core
only.

## Blast radius confirmation

A codebase-wide search for consumers of the re-threaded names (`goodIntervalsBundle`,
`classKeys`, `realBracketOfEReal`, `bracketOfComp`, `compSet_eq`,
`goodIntervalsBundle_{pairwise_disjoint_Ioo,no_overlap,mem_component}`) outside the three
target files returns **nothing**. E1 and Multiplicity are not yet landed, so no other
module depended on these signatures.

## Classification

* **PROVEN** (kernel-checked, core axioms only): `xBound_spec`, the new
  `realBracketOfEReal` subset obligation, `realBracketOfEReal_covers`,
  `goodIntervalsBundle_covers`, and the full re-validated (v)/(vi) discharges
  (`edgeBMultigraph_arcsJoinEndpoints`, `edgeBMultigraph_wellDrawn`).
* The fix achieves coverage as designed; the **downstream E1 bound that consumes
  `goodIntervalsBundle_covers`** is a separate phase (not in this build) and remains
  CONJECTURED until `EdgeBE1.lean` is landed with the `c(d)` from the diagnosis doc.
