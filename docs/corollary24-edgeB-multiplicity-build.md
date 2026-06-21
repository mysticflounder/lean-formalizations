# Edge-B multiplicity `≤ M` build record (task #43 leaf, discharge (iv))

**File:** `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBMultiplicity.lean`
**Namespace:** `PachDeZeeuw.Algebraic` (`open CrossingLemma`)
**Status:** PROVEN, sorry-free, axiom-clean.
**Toolchain:** Lean 4 v4.30.0, mathlib v4.30.0.

Curve port of the line-case `stMultigraph_multiplicity_le_one`
(`PachSharir/SzemerediTrotter.lean:1221`), generalizing the line case's terminal
`≤ 1` (at most one line through two distinct points) to `≤ M` (at most `M` curves of
`Γ` through two distinct points). This is the discharge that **changes shape** (`1 → M`)
relative to the line case (design `docs/corollary24-edgeB-assembly-construction-design.md`
§2.1 / §4 (iv)).

## Shipped signature (the deliverable)

```lean
theorem edgeBMultigraph_multiplicity_le_M
    (M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M) :
    ∀ p q, (edgeBMultigraph d M P Γ).multiplicity p q ≤ M
```

(`d : ℕ` is a section variable.) `multiplicity p q` is the `DrawnMultigraph` field
`#{i : Fin numEdges | endpoints i = (p,q) ∨ endpoints i = (q,p)}`
(`CrossingLemma.lean:64`); for `edgeBMultigraph` the `endpoints` are
`fun i => (allCurveEdges d P Γ)[i].e`.

## The hypothesis-form decision (`hpp`), and why it is the right interface

`hpp` is the **point–point 2-degrees-of-freedom clause** stated in the
PlanePoly / `ℝ × ℝ` representation: any two distinct points `p, q ∈ P` lie on the
plane zero-set `{z | evalPlane H.1 z = 0}` of at most `M` curves `H ∈ Γ`, measured as
`(Γ.filter (p ∈ … ∧ q ∈ …)).card ≤ M`.

This **follows the (vi) WellDrawn `hcc` precedent** (`edgeBMultigraph_wellDrawn` in
`EdgeBWellDrawn.lean`, which took the curve–curve clause as
`∀ H₁∈Γ, ∀ H₂∈Γ, H₁≠H₂ → (…∩…).encard ≤ M`). Reasons this is the correct cut point:

1. **It is the verbatim PlanePoly image of `TwoDegreesOfFreedom`'s second conjunct.**
   `PachSharir.TwoDegreesOfFreedom` (`Theorem23.lean:45`) is
   `(curve–curve encard ≤ M) ∧ (∀ p₁∈P, ∀ p₂∈P, p₁≠p₂ → (Γ.filter (p₁∈γ ∧ p₂∈γ)).card ≤ M)`.
   `hpp` is exactly the second conjunct with `γ := {z | evalPlane H.1 z = 0}` and the
   curve family `Γ.image (fun H => evalPlaneZeroSet H.1)` re-expressed as a filter over
   `Γ` itself. The `p ∈ P`, `q ∈ P`, `p ≠ q` preconditions are carried verbatim.
2. **`(Γ.filter …).card ≤ M` is exactly the bound the count needs.** The
   indicator sum `Σ_{H∈Γ} (if p,q ∈ γ_H then 1 else 0)` collapses to
   `(Γ.filter (p ∈ γ_H ∧ q ∈ γ_H)).card` (`Finset.sum_ite` + `Finset.sum_const`),
   which `hpp` bounds directly — no `encard`/`card` conversion needed (contrast the
   curve–curve clause, which is stated in `encard` because its fibre injects into a
   `Set` intersection).
3. **Representation match.** Every endpoint the proof touches is a point of `ℝ × ℝ`,
   on the curve iff `evalPlane H.1 p = 0` (`mem_evalPlaneZeroSet`). So the per-curve
   "both endpoints on the curve" facts land directly in `hpp`'s predicate. No chart
   transport inside this lemma.
4. **NOT `PachSharir.TwoDegreesOfFreedom` directly.** That `Prop` is typed over
   `Finset (Set (EuclideanSpace ℝ (Fin 2)))`. Converting it to this `ℝ × ℝ` /
   `evalPlane`-zero-set form is the chart-bridge + component-reduce node, **out of scope
   here** (per the task and design §5.3, node `edgeB-curve-bridge`). `hpp` is the
   strongest thing this lemma needs and the weakest thing the bridge must produce.

**Associate / shared-zero-set curves.** `hpp` keys on points, not curve identity, so
nothing is silently assumed about distinct `EdgeBCurve` values that share a zero-set:
if two such curves both pass through `p, q`, they are two of the `≤ M` filtered curves
and are (over-)counted like any other. The per-curve `≤ 1` (M2) is about a *single*
curve value `H`, so it is unaffected by associates elsewhere in `Γ`.

## Proof structure (≤1-per-curve M2 + 2-DOF point–point injection)

The multiplicity reduces (curve analogues of `multiplicity_eq_countP` /
`multiplicity_flatMap_sum`) to a `Finset.sum` over `Γ`:

```
multiplicity p q
  = (allCurveEdges d P Γ).countP (matchPair p q ·.e)           -- edgeBMultigraph_multiplicity_eq_countP
  = Σ_{H∈Γ} (curveBlock P H).countP (matchPair p q ·.e)        -- edgeB_countP_flatMap_sum
```

where `curveBlock P H` is a single curve's contribution to `allCurveEdges` (the inner
`classKeys`/`edgesOnSheet` double `flatMap`); `allCurveEdges = Γ.toList.flatMap curveBlock`
by `rfl`. Then case on `p, q`:

* **`p = q`** (`countP_curveBlock_eq_zero_of_eq`): edges join *distinct* points
  (`edgesOnSheet_distinct`), so every per-curve term is `0`; sum `= 0 ≤ M`.
* **`p ≠ q`, not both in `P`** (`countP_curveBlock_eq_zero_of_not_memP`): a matching
  edge has both endpoints in `P` (`EdgeBEdge.fst_mem`, `EdgeBEdge.snd_mem`), so a match
  forces `p, q ∈ P`; absent that, every term is `0`. (This branch is what lets the
  conclusion be `∀ p q` over arbitrary points while `hpp` only constrains `p, q ∈ P`.)
* **`p ≠ q`, both in `P`**: per-curve indicator bound, then `hpp`:
  - a curve not through both contributes `0` (`countP_curveBlock_eq_zero_of_not_mem`:
    every edge endpoint is on the curve, via `edgesOnSheet_mem` + `mem_evalPlaneZeroSet`);
  - otherwise `≤ 1` (`curveBlock_countP_le_one`, the **M2 fact**);
  - sum of indicators `= (Γ.filter (p∈γ_H ∧ q∈γ_H)).card ≤ M` by `hpp`.

### The M2 core: `curveBlock_countP_le_one` (the `1 → M` shape change lives here)

Within one curve's block a fixed unordered pair `{p,q}` is carried by **at most one**
edge. Proved by `countP_le_one_of_index_inj` (the line case's generic
`countP ≤ 1` from index-injectivity) over `curveBlock P H`, whose index-injectivity is:
two block edges that both match are **equal as `EdgeBEdge` values**
(`edgeB_same_curve_match_imp_eq`), and the block is `Nodup` (`curveBlock_nodup'`, via the
landed `curveBlock_eq` reassociation + `curveBlock_nodup`), so equal entries sit at equal
indices.

`edgeB_same_curve_match_imp_eq` mirrors the landed
`edgeB_same_curve_shared_point_imp_eq` (EdgeBWellDrawn.lean) but pivots on the **left
endpoint** (a genuine point of `P`, on the curve, in the bracket, at rank `j`) rather than
an interior arc point:

- **Pinned orientation** (`edgeB_match_orientation`): a matching edge has strict
  `x`-increase (`EdgeBEdge.fst_lt`), so `Ed.e ∈ {(p,q),(q,p)}` must take the orientation
  with increasing `x`. If `p.1 < q.1` then `Ed.e = (p,q)`; if `q.1 < p.1` then `(q,p)`;
  `p.1 = q.1` is impossible for a matching edge. Hence equal endpoint pairs `Ed₁.e = Ed₂.e`.
- **Same rank**: `Ed.j = sheetRank Ed.h Ed.e.1.1 Ed.e.1.2` (the left endpoint's rank,
  `EdgeBEdge.fst_rank` = `(edgesOnSheet_mem …).1.2.2.2`); equal `.e` and `.h` give equal `j`.
- **Same bracket**: both left endpoints share `x = Ed₁.e.1.1 = Ed₂.e.1.1`, which lies in
  both open brackets (`EdgeBEdge.fst_mem_Ioo`); provenance (`allCurveEdges_provenance`)
  exposes the `goodIntervalsBundle` entry behind each stored `(α,β)`, and
  `goodIntervalsBundle_no_overlap` forces equal bracket value.
- All data fields then agree; `hgood`/`hmem` are proof-irrelevant, so the edges are equal.

This is the only genuinely new content; everything else is glue over landed leaves.

## Landed leaves consumed (read, not re-proved)

| Leaf | File | Role |
|---|---|---|
| `edgeBMultigraph`, `EdgeBEdge`, `allCurveEdges`, `classKeys`, `EdgeBEdge.{e,h,α,β,j,hmem,fst_lt,fst_mem,snd_mem}` | `EdgeBMultigraph.lean` | the object discharged over; `curveBlock` is its inner `flatMap` |
| `allCurveEdges_provenance` (:294) | `EdgeBWellDrawn.lean` | recover the `goodIntervalsBundle` entry behind an edge's `(α,β)` |
| `goodIntervalsBundle_no_overlap` (:268) | `EdgeBWellDrawn.lean` | shared `x` in two brackets ⟹ equal bracket |
| `curveBlock_eq` (:361), `curveBlock_nodup` (:377) | `EdgeBWellDrawn.lean` | per-curve block reassociation + nodup |
| `edgesOnSheet_mem` (:112), `edgesOnSheet_distinct` (:86) | `SheetEdges.lean` | endpoint on-curve/in-bracket/rank facts; distinct endpoints |
| `mem_evalPlaneZeroSet` | `LocalArc.lean` | `p ∈ evalPlaneZeroSet h ↔ evalPlane h p = 0` |
| `matchPair` (:1047), `finFilterCard_eq_countP` (:1054), `countP_le_one_of_index_inj` (:1073) | `SzemerediTrotter.lean` | the `Finset.card → List.countP` bridge + generic `countP ≤ 1` |
| `DrawnMultigraph.multiplicity` (:64) | `CrossingLemma.lean` | the quantity bounded |
| `Finset.sum_map_toList`, `List.countP_flatMap`, `Finset.sum_ite`, `Finset.sum_eq_zero` | mathlib | sum/flatMap plumbing |

The terminal `lines_through_two_points_le_one` (line case) is replaced by `hpp`; the
M2 step's `edgesOnLine_countP_le_one` is replaced by `curveBlock_countP_le_one` (which
goes through equal-`EdgeBEdge` + block nodup rather than a `pointsOnSheet`-index argument,
because the per-curve block spans several `(α,β,j)` classes, not one sorted list).

## Declarations (16)

`curveBlock`, `allCurveEdges_eq_flatMap`, `curveBlock_nodup'`, `curveBlock_h`,
`curveBlock_subset_allCurveEdges`, `edgeBMultigraph_multiplicity_eq_countP`,
`edgeB_countP_flatMap_sum`, `EdgeBEdge.fst_mem_Ioo`, `EdgeBEdge.fst_rank`,
`edgeB_match_orientation`, `edgeB_same_curve_match_imp_eq`, `curveBlock_countP_le_one`,
`countP_curveBlock_eq_zero_of_not_mem`, `countP_curveBlock_eq_zero_of_eq`,
`countP_curveBlock_eq_zero_of_not_memP`, **`edgeBMultigraph_multiplicity_le_M`**
(deliverable).

## Gate results

- **Build:** `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultiplicity`
  → `Build completed successfully (8520 jobs)`. A forced rebuild of the file (touch +
  build) produces **zero diagnostics on this file** (no errors, no warnings, no linter
  hits).
- **Axiom closure (independent `#print axioms`):** `edgeBMultigraph_multiplicity_le_M`,
  `edgeB_same_curve_match_imp_eq`, `curveBlock_countP_le_one`,
  `edgeBMultigraph_multiplicity_eq_countP`, `edgeB_countP_flatMap_sum` all →
  `[propext, Classical.choice, Quot.sound]`. **No `sorryAx`, no `Lean.ofReduceBool`, no
  custom axioms.** This confirms the proof does not depend on the pre-existing
  `sorry`-declarations in the parked crossing-lemma base
  (e.g. `SzemerediTrotter.lean:4533`, `PLArc.lean`, `ResidualMapProperties.lean`,
  `CrossingLemmaAmplification.lean`) — a `sorryAx` would surface in the closure if it did.
  `Classical.choice` is expected (from `goodIntervalsBundle` / `allCurveEdges_provenance`
  and `open scoped Classical`).
- **Forbidden-token scan:** no `sorry`, `native_decide`, `unsafe`, `@[implemented_by]`,
  `@[extern]`, or `axiom` in the file.
- **`E`-binder pitfall:** avoided — `scoped notation "E" => chartEquiv` is in scope; the
  edge binders are `Ed`, `H₁`/`H₂`, `gi₁`/`gi₂`, never `E`.

## PROVEN / CONJECTURED classification

All 16 declarations are **PROVEN** (complete, gap-free, kernel-checked, axiom closure
`[propext, Classical.choice, Quot.sound]`).

**Conditionality.** `edgeBMultigraph_multiplicity_le_M` is **conditional on `hpp`** (the
point–point `(Γ.filter …).card ≤ M` clause). This is by design (task scope): `hpp` is the
`ℝ × ℝ` / `evalPlane`-form interface that a separate downstream node will supply from
`PachSharir.TwoDegreesOfFreedom` (second conjunct) via the chart bridge + component
reduction. Within this file `hpp` is an explicit hypothesis, not an axiom or `sorry`.
