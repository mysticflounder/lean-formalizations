# Corollary 24 — the Edge-B drawn multigraph definitional layer (`edgeBMultigraph`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in
an isolated worktree, ported + gated on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open CrossingLemma`, `open scoped Classical`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBMultigraph.lean`.

## Scope

The definitional layer of task #43: the curve analogue of the line-case `stMultigraph`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:482`) and its two glue discharges
`stMultigraph_card_V` (`:494`) / `numEdges_eq_sum` (`:992`). This file PRODUCES the
`DrawnMultigraph` that the already-landed M-form incidence endgame
`incidence_bound_of_multigraphCrossingLemma` (`MultigraphIncidenceEndgame.lean`)
consumes; it does NOT bound incidences (that is the E1/WellDrawn/multiplicity discharge
surface, out of scope here). It realizes the design
`docs/corollary24-edgeB-assembly-construction-design.md` §1.1, §1.2, §4 (i),(ii), and
the FLAG `classKeys-enum`.

Pure assembly over already-landed, axiom-clean leaves; no new analysis. The single
risk point (per the task) — the `arc` field, which must be constructed without
`sorry` — closed.

## Declarations (all PROVEN, Lean-accepted)

Listed in dependency order; every one is `[propext, Classical.choice, Quot.sound]`.

* `abbrev EdgeBCurve (d : ℕ) : Type` —
  `Σ' h : PlanePoly, Irreducible h ∧ h.totalDegree ≤ d ∧ MvPolynomial.pderiv (1 : Fin 2) h ≠ 0`.
  The post-shear curve carrier (design §1.1, verbatim).
* `theorem edgeBCurve_bad_finite {d} (H : EdgeBCurve d) : (Bad H.1).Finite` —
  `decomp_D1_bad_finite H.1 H.2.1 H.2.2.1 H.2.2.2`. The `(Bad h).Finite` hypothesis
  `decomp_D1_goodLocus_components` needs, discharged from the `EdgeBCurve` proof fields.
* `structure EdgeBEdge (P : Finset (ℝ × ℝ))` — the **enriched per-edge payload**
  (see "the `arc` field" below): fields `h : PlanePoly`, `α β : ℝ`,
  `hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h`, `j : ℕ`, `e : (ℝ × ℝ) × (ℝ × ℝ)`,
  `hmem : e ∈ edgesOnSheet P h α β j`.
* `EdgeBEdge.fst_mem / snd_mem` — `Ed.e.1 ∈ P`, `Ed.e.2 ∈ P` (from `edgesOnSheet_mem`).
* `EdgeBEdge.fst_lt` — `Ed.e.1.1 < Ed.e.2.1` (from the landed `edgesOnSheet_fst_lt`).
* `EdgeBEdge.chi` (`noncomputable def : ℝ → ℝ`) / `EdgeBEdge.chi_spec` —
  the chosen on-curve graph `χ` and its `Classical.choose_spec` (continuity, the two
  endpoint pins `χ e.1.1 = e.1.2`, `χ e.2.1 = e.2.2`, on-curve), from the landed
  `export_4a_edge_is_arc`.
* `EdgeBEdge.arc` (`noncomputable def : SimpleCurveArc`) — **the risk point.**
  `curveArc Ed.chi Ed.e.1 Ed.e.2 Ed.fst_lt Ed.chi_spec.1`.
* `EdgeBEdge.arc_endAnchor` — `endAnchor Ed.arc false = Ed.e.1 ∧ endAnchor Ed.arc true = Ed.e.2`
  (from the landed `endAnchor_curveArc_{false,true}`). Confirms the arc genuinely
  anchors at the declared endpoints (semantic, not just type, correctness) — the
  `ArcsJoinEndpoints` ingredient, proved here for free.
* `realBracketOfEReal (a b : EReal) : Σ' ab : ℝ × ℝ, Set.Ioo ab.1 ab.2 ⊆ {x | a < ↑x ∧ ↑x < b}` —
  the `EReal → real` bracket extraction (the `classKeys-enum` core; see below).
* `goodIntervalsBundle {d} (H : EdgeBCurve d) : List (Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1)` —
  the good-locus components as real-endpoint good intervals with bundled `hgood`.
* `classKeys (d : ℕ) (H : EdgeBCurve d) : List (Σ' ab : ℝ × ℝ, PProd (∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) ℕ)` —
  each good interval paired with every rank `j ∈ List.range (d+1)`.
* `allCurveEdges (d) (P) (Γ : Finset (EdgeBCurve d)) : List (EdgeBEdge P)` — the global
  edge list, a double `flatMap` over `Γ.toList` and `classKeys`, inner edges via
  `(edgesOnSheet …).attach`.
* `allCurveEdges_mem` — `∀ Ed ∈ allCurveEdges d P Γ, Ed.e.1 ∈ P ∧ Ed.e.2 ∈ P` (analogue
  `allEdges_mem`).
* `edgeBMultigraph (d M : ℕ) (P) (Γ : Finset (EdgeBCurve d)) : DrawnMultigraph` — the
  multigraph: `V := P`, `numEdges := (allCurveEdges d P Γ).length`,
  `endpoints i := (allCurveEdges d P Γ)[i].e`, `arc i := (allCurveEdges d P Γ)[i].arc`,
  `crossings := M * Γ.card ^ 2`.
* `edgeBMultigraph_card_V` — `(edgeBMultigraph d M P Γ).V.card = P.card := rfl` (discharge (i)).
* `edgeBMultigraph_numEdges` — `numEdges = (allCurveEdges d P Γ).length := rfl`.
* `edgeBMultigraph_numEdges_eq_sum` — discharge (ii): the double-sum identity
  `numEdges = ∑ H ∈ Γ, ((classKeys d H).map (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum`.

## The `arc` field (the risk point) — closed by payload enrichment

`DrawnMultigraph.arc : Fin numEdges → SimpleCurveArc`. To build edge `i`'s arc via
`curveArc ∘ export_4a_edge_is_arc`, that edge must be a *consecutive* `edgesOnSheet`
pair over a good interval `(α,β)` at rank `j`, with the good-interval proof
`hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h` AND the membership `(p,q) ∈ edgesOnSheet P h α β j`.
The line case's `allEdges` element `Σ' e, e.1 ≠ e.2` is **insufficient** — it carries
neither `hgood` nor the membership.

**Resolution (the enrichment the task anticipated):** the per-edge payload is the
structure `EdgeBEdge P`, carrying exactly `(h, α, β, hgood, j, e, hmem)`. From it,
`export_4a_edge_is_arc P Ed.h Ed.j Ed.hgood Ed.hmem` applies verbatim, yielding (via
`Classical.choose` / `_spec`) the graph `χ` (`EdgeBEdge.chi`) with its pins; `fst_lt`
(from `edgesOnSheet_fst_lt P Ed.h Ed.j Ed.hgood Ed.hmem`) supplies `p.1 < q.1`; and
`curveArc Ed.chi Ed.e.1 Ed.e.2 Ed.fst_lt Ed.chi_spec.1` is the arc. **No `sorry`.**
`edgeBMultigraph.arc` is `[propext, Classical.choice, Quot.sound]`, and
`arc_endAnchor` independently proves the anchoring.

`hmem` is supplied at construction by `(edgesOnSheet P H.1 …).attach` — each attached
element `se` carries `se.2 : se.1 ∈ edgesOnSheet …`, used directly as `hmem`. (An
earlier attempt mapped `edgesOnSheetWithProof` and tried `mem_edgesOnSheetWithProof se.2`,
which type-errors: `se.2` there is the *distinctness* proof, not list membership.
`.attach` is the clean source of the membership.)

## The `classKeys` encoding — the EReal / unbounded-component issue, and WHY it is correct

`decomp_D1_goodLocus_components H.1 hbad` (`GoodLocusComponents.lean:253`) returns the
good locus as a finite disjoint union of open intervals with **`EReal`** endpoints,
inside a **`Prop`-level `∃`** over a `Type` `ι` and the family `I : ι → Set ℝ`:

```
∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
  (∀ j, ∃ a b : EReal, I j = {x | a < ↑x ∧ ↑x < b}) ∧ Pairwise (onFun Disjoint I) ∧
  GoodLocus h = ⋃ j, I j ∧ Fintype.card ι = hbad.toFinset.card + 1
```

Two distinct subtleties had to be resolved, and a third was discovered during the build:

1. **Real endpoints from `EReal` (FLAG `classKeys-enum`).** `realBracketOfEReal (a b : EReal)`
   produces a real bracket `(α,β)` with `Set.Ioo α β ⊆ {x | a < ↑x ∧ ↑x < b}`, by a
   3×3 case analysis on `(a, b) ∈ {⊥, ⊤, coe r}²`:
   - `(coe r, coe s) ↦ (r, s)` — the bracket equals the component;
   - `(⊥, coe s) ↦ (s-1, s)`, `(coe r, ⊤) ↦ (r, r+1)` — the two **unbounded** components,
     bracketed to a finite sub-interval (`bot_lt_coe` / `coe_lt_top` make the unbounded
     side's constraint vacuous);
   - the unsatisfiable cases (`a = ⊤` or `b = ⊥`, where `{x | …} = ∅`) ↦ `(0, 0)`, with
     `Set.Ioo 0 0 = ∅` giving the subset vacuously.
   Correctness: the subset `Ioo α β ⊆ I j`, composed with `I j ⊆ ⋃ I = GoodLocus h = (Bad h)ᶜ`,
   yields the bundled `hgood`. The `Bad`-avoidance proof is what the `arc` field consumes;
   for the multigraph *definition* (this file's scope) the exact endpoints do not matter,
   only that each emitted interval is genuinely good. **The bracket therefore certifies
   `hgood` for every component, including the two unbounded ones, with no `sorry`.**

2. **`Prop`-level `∃` over `Type` data (discovered; not in the design).**
   `decomp_D1_goodLocus_components` packages `ι : Type` and `I` inside `Exists`, which is
   a `Prop`. Building a `List` (in `Type`) by `obtain`/`cases` on it is **forbidden**
   (`recursor Exists.casesOn can only eliminate into Prop` — no large elimination). The
   extraction route is `Classical.choose` / `Classical.choose_spec`, which legitimately
   pull `Type`-level witnesses out of a `Prop`-level `∃` (this is why `Classical.choice`
   appears in the axiom set, as expected). `goodIntervalsBundle` chains four
   `Classical.choose`s for `ι, Fintype ι, I,` and the conjunction, then maps over
   `(@Finset.univ ι instι).toList`, applying `realBracketOfEReal` per component and
   discharging `hgood` through the `GoodLocus h = ⋃ I` clause (`hI.2.2.1`).

The encoding chosen is **faithful** (each `classKeys` entry is a genuine good-locus
component as a real interval, so the landed leaves `edgesOnSheet` / `export_4a` apply
verbatim) and **forward-usable** (the E1 coverage discharge, out of scope here, can be
built on `goodIntervalsBundle` rather than discarding it). It is not a vacuous/empty
`classKeys` (which would type-check but move the obligation).

## A third, environment-level pitfall (resolved): the `E` binder collides with `ChartBridge`'s notation

`ChartBridge.lean:59` declares `@[inherit_doc] scoped notation "E" => chartEquiv` in the
**same namespace** `PachDeZeeuw.Algebraic`. Because this file transitively imports
`ChartBridge` (via `DecompositionD1`), the scoped notation `E` is active here, making `E`
a reserved token. Every `(E : EdgeBEdge P)` binder failed to parse
(`unexpected token 'E'; expected '_' or identifier`), and the resulting parse desync
produced spurious `EdgeBEdge.fst_mem/arc` "environment does not contain" cascades far
downstream. **Fix:** the projection binder is named `Ed`, not `E`. (Isolated probes that
did not import `ChartBridge` did not exhibit this, which is why the issue only surfaced
in the full-import build.)

## Glue proofs of the two discharges

* **(i) `edgeBMultigraph_card_V`** — `rfl` (`V := P`), exactly as `stMultigraph_card_V`.
* **(ii) `edgeBMultigraph_numEdges_eq_sum`** — `rw [edgeBMultigraph_numEdges, allCurveEdges]`
  then `simp only [List.length_flatMap, List.length_map, List.length_attach]` (the
  outer + inner `flatMap` lengths collapse; the inner `.map` and `.attach` lengths
  rewrite the per-class count to `(edgesOnSheet …).length`), then `rw [Finset.sum_map_toList]`
  to fold the outer `toList` into the `Finset` sum. Ports `numEdges_eq_sum` (`:992`) to the
  double `flatMap`.

## Gate

* `EdgeBMultigraph.lean` builds green standalone (`./lake-build.sh
  LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultigraph`, **8494 jobs**) and via
  the `CrossingLemma.lean` aggregator (**8525 jobs**, after wiring the import in
  `CrossingLemma.lean`). The file is warning-free; the aggregator's warnings are
  pre-existing drift in other files (`PLCollarSeparation.lean:1341` `unusedSimpArgs`;
  `SzemerediTrotter.lean:4533` parked `sorry` of the `SimpleCrossingLemmaStatement`
  base) — none in this file.
* Independent `#print axioms` on `edgeBMultigraph`, `edgeBMultigraph_card_V`,
  `edgeBMultigraph_numEdges_eq_sum`, `allCurveEdges`, `allCurveEdges_mem`, `classKeys`,
  `goodIntervalsBundle`, `realBracketOfEReal`, `EdgeBEdge.arc`, `EdgeBEdge.arc_endAnchor`,
  `edgeBCurve_bad_finite` = **`[propext, Classical.choice, Quot.sound]`** for all
  (no `sorryAx`, no `native_decide`, no `Lean.ofReduceBool`, no custom axioms).
  `Classical.choice` enters via the `Classical.choose` extraction of the `Prop`-level
  components (intended).
* No shipped `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` /
  `#print` (the only `sorry` token is the word inside one docstring).

## Classification

| Declaration | Status |
|---|---|
| `EdgeBCurve`, `edgeBCurve_bad_finite` | **PROVEN (Lean-accepted)** |
| `EdgeBEdge` + `fst_mem`/`snd_mem`/`fst_lt`/`chi`/`chi_spec` | **PROVEN** |
| `EdgeBEdge.arc` (the risk point) + `arc_endAnchor` | **PROVEN — `arc` field closed, no `sorry`** |
| `realBracketOfEReal`, `goodIntervalsBundle`, `classKeys` | **PROVEN** |
| `allCurveEdges`, `allCurveEdges_mem` | **PROVEN** |
| `edgeBMultigraph`, `edgeBMultigraph_card_V` (i), `edgeBMultigraph_numEdges_eq_sum` (ii) | **PROVEN** |

## Remaining (out of this file's scope — the discharge surface)

The multigraph and its two glue discharges (i),(ii) are landed. The remaining Edge-B
discharges that *consume* `edgeBMultigraph` (FLAGs in
`docs/corollary24-edgeB-assembly-construction-design.md` §4, §6) are separate nodes:
`edgeBMultigraph_multiplicity_le_M` (iv), `edgeBMultigraph_wellDrawn` (vi),
`edgeBMultigraph_arcsJoinEndpoints` (v) (its per-edge content is the already-proven
`EdgeBEdge.arc_endAnchor`), and `edgeB_incidence_le_numEdges_add` (iii, E1) with its
`bad-ncard` / `fibre-card-le-at-bad` inputs. Then `edgeB_crossingInput` composes them
with the landed `incidence_bound_of_multigraphCrossingLemma`.
