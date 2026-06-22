# Node A1 — Edmonds same-region producer: structure, isolation, and proof sketches

Status (this session): the monolithic `sorry` at the old `SzemerediTrotter.lean:4644`
is **replaced by structured Lean** that consumes a sorry-free recursion harness.
Sub-obligation **B0 (the mutually-recursive `dr`) is fully discharged sorry-free**,
and so are the B2 region-equality transport and the `poolRegion` injectivity.
The **new file `EdmondsSameRegion.lean` is entirely sorry-free and axiom-clean.**
The single remaining open obligation is the per-step producer
`hgeo : CrossingLemma.PerStepCrosscutInput` in ST — true with the new-edge endpoint
data in scope; it carries only the extractor `hsplit` (B1) and the partition
geometry (B2 witness existence + global-side distinctness).

All file:line references below are to the worktree copy under
`lean/LeanFormalizations/…`. New file: `…/CrossingLemma/EdmondsSameRegion.lean`.

A correctness note (caught during this session): the naive abstract restatement of
B1 — "the bundle's predecessor corners `c₁, c₂` collapse to one split-pool class" —
is **provably false** (`insertedFaceSplitPoolEquiv (Sum.inl c₁) = Sum.inr 0`,
`(Sum.inl c₂) = Sum.inr 1`; the corners land on *opposite* sides). The true B1 is
the extractor's `hsplit` on the *entered-sector* corners. B1 is therefore **not**
introduced as a standalone `sorry` leaf (that would be a false-statement `sorry`);
it lives as the extractor's existing `hsplit` argument, discharged inside `hgeo`.

## 0. What changed and where

| Item | Location | State |
|---|---|---|
| New file `EdmondsSameRegion.lean` | `CrossingLemma/EdmondsSameRegion.lean` | **builds, 0 `sorry`** |
| B0 recursion harness `exists_dr_hstepCrosscut` | `EdmondsSameRegion.lean:~497` | **sorry-free, axiom-clean** |
| Per-step bundle assembler `mkPrefixStepCrosscutData` | `~327` | **sorry-free, axiom-clean** |
| B2 region-equality transport `prefixStepSameRegion` | `~180` | **sorry-free, axiom-clean** |
| `poolRegion` injectivity combinator `prefixStepSameRegion_poolRegion_injective` | `~216` | **sorry-free, axiom-clean** |
| `hconst` transport `stepRegionFamily_hconst` | `~406` | **sorry-free, axiom-clean** |
| Composition witness `nonempty_prefixStepCrosscut_of_data` | `~378` | **sorry-free** |
| B1 (`hsplit`) | extractor `ResidualMapProperties.lean:5785`, lines 5813–5867 | open, in `hgeo` |
| ST A1 block rewired to `exists_dr_hstepCrosscut` | `SzemerediTrotter.lean:4608`–`:4650` | builds; one `hgeo` `sorry` at `:4649` |

`#print axioms` for every sorry-free piece (`exists_dr_hstepCrosscut`,
`mkPrefixStepCrosscutData`, `prefixStepSameRegion`,
`prefixStepSameRegion_poolRegion_injective`, `stepRegionFamily_hconst`,
`nonempty_prefixStepCrosscut_of_data`), all identical:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axioms.
`#print axioms straightLineCanonicalComponentResidualMapPlanarityOfARR` =
`[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` is the single
`hgeo` `sorry`).

## 1. The target existential and its consumer (unchanged)

The A1 block must produce
```
h_exists_target1 : ∃ (dr : ∀ m, m ≤ N → (Fin m × Bool) → Set (ℝ×ℝ))
  (hstepCrosscut : ∀ m (hm' : m+1 ≤ N), start ≤ m →
    PrefixStepCrosscutData G' m _ hm' _ _ (dr m _) (dr (m+1) hm')), True
```
where `N = G'.numEdges`, `G' = G.permuteEdges π`, `start = lvertex.length - 1`.
Downstream (`SzemerediTrotter.lean:4719`/`:4731`) consumes `dr` and the bundle's
fields `c₁,c₂,hc,hregion,hvertex` through the **already sorry-free**
`regionSeparates_prefix_of_crosscut` (`EdmondsConstruction.lean:148`). The bundle
fields `poolRegion,hinj,hfactor` are consumed *inside* that iteration. None of the
downstream consumers were modified.

## 2. The `PrefixStepCrosscutData` bundle (recap)

`PrefixStepCrosscutData G m hm hm' hARRm hARRm1 drm drm1`
(`EdmondsConstruction.lean:91`) fields:

- `c₁ c₂ : Fin m × Bool`, `hc : c₁ ≠ c₂` — the two predecessor splice corners;
- `hregion : drm c₁ = drm c₂` — both corners face the same predecessor region;
- `hvertex` — vertex-perm splice tying `insertedEdgeMap … c₁ c₂` to `R_{m+1}`;
- `poolRegion : ({f : R_m.Face // f ≠ R_m.Face_mk c₁} ⊕ Fin 2) → Set`;
- `hinj : Function.Injective poolRegion`;
- `hfactor : ∀ hsame, ∀ d, drm1 d = poolRegion (insertedFaceSplitPoolEquiv R_m c₁ c₂ hc hsame (insertedEdgeMap…Face_mk (prefixStepDartEquiv.symm d)))`.

The codomain of `poolRegion` is the split-pool of the inserted-edge face split
(`EdgeInsertion.lean:1704`): `Sum.inl ⟨f,_⟩` = old non-cut faces; `Sum.inr 0` =
the `c₁`/`dartB` side; `Sum.inr 1` = the `c₂`/`dartA` side.

## 3. The decomposition (B0 / B1 / B2)

### B0 — `dr` is forced and mutually-recursive — **DISCHARGED**

`hfactor` pins `dr (m+1) = poolRegion ∘ splitClass`, and `hinj` makes `poolRegion`
injective, so `dr (m+1)` is a function of `dr m` plus the per-step `poolRegion`.
The harness `exists_dr_hstepCrosscut` builds `dr` by a **simultaneous recursion**
(`Nat.le_induction`, carried under `Nonempty` of a `Σ'`/`PProd` because mathlib's
`Nat.le_induction` has a `Prop`-valued motive) that maintains, at every level
`start ≤ k ≤ n`, three invariants:

- the region family `dr k`,
- `hconst k` (`facePerm`-constancy: same cycle ⇒ same region),
- `hsep k` (region-separation: same region ⇒ same cycle).

**Base** (`k = start`): `dr := ∅` everywhere. The spanning-tree prefix has a
single face (`hcard1`), so `hsep` is `facePerm_sameCycle_of_card_face_eq_one`
(`RegionFaceBridge.lean:286`) and `hconst` is `rfl` (constant `∅`).

**Step** (`m → m+1`, `start ≤ m`): feed `dr m` + `hconst m` + `hsep m` to the
per-step producer `hgeo`, obtain a bundle `data` with successor family `drm1`.
Re-point `dr` at level `m+1` to `drm1`. Then
- `hsame := hsep m c₁ c₂ data.hregion` (predecessor co-faciality from `hsep`);
- `hsep (m+1)` is `region_separates_prefixStep_sameFace_concrete`
  (`RegionFaceBridge.lean:436`) applied to `data` (sorry-free transport);
- `hconst (m+1)`: same cycle ⇒ same successor face (`Quotient.sound`) ⇒ same split
  class (`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq`,
  `ResidualMapProperties.lean:844`) ⇒ `drm1` agrees via `hfactor` + `congrArg`.

The harness needs no injectivity for `hconst`, only the split-pool iff; injectivity
is used only inside `hsep` (via `region_separates_prefixStep_sameFace_concrete`).

This is the net reduction in target freedom: the original `sorry` had to produce
`dr` (a global recursive object) **and** all bundles simultaneously. After the
harness, the residual obligation is the per-step producer `hgeo` — one bundle from
`dr m` + invariants — with B0 fully removed.

### B1 — angular co-faciality (single-face crosscut) — the extractor's `hsplit`

B1 is **not** introduced as a standalone Lean leaf. It is the `hsplit` hypothesis
of the general-step extractor
`exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq`
(`ResidualMapProperties.lean:5785`, lines 5813–5867), discharged inside `hgeo`.

**Why no standalone leaf.** A naive abstract restatement "the bundle's predecessor
corners `c₁, c₂` land on one split-pool class," i.e.
```
insertedFaceSplitPoolEquiv R_m c₁ c₂ hc hsame (Face_mk (Sum.inl c₁))
  = insertedFaceSplitPoolEquiv R_m c₁ c₂ hc hsame (Face_mk (Sum.inl c₂))
```
is **provably FALSE**: by `insertedFaceSplitPoolEquiv_mk_inl_left`
(`EdgeInsertion.lean:1751`) the LHS is `Sum.inr 0`, and by
`insertedFaceSplitPoolEquiv_mk_inl_right` (`:1854`) the RHS is `Sum.inr 1` — the
two old cut corners are on *opposite* sides of the split (that is the *point* of
the inserted edge). Stating it as a `sorry` leaf would be a false-statement
`sorry`. The correct content is about the **rotation-chosen entered-sector corners
at the two endpoints** (`e₁ ∈ incidentEnds p₁`, `e₂ ∈ incidentEnds p₂`, each the
incident slot the new dart rotates into), not the bundle corners.

**The true statement (extractor `hsplit`, lines 5860–5867).** Given the two angular
`vertexRotationAtRadius` antecedents (`e₁`, `e₂` are the slots whose rotation image
is the new dart at `p₁`, `p₂`), conclude
```
insertedFaceSplitPoolEquiv R_m s₁ s₂ … (Face_mk ((prefixStepDartEquiv m).symm e₁.1))
  = insertedFaceSplitPoolEquiv R_m s₁ s₂ … (Face_mk ((prefixStepDartEquiv m).symm e₂.1))
```
i.e. the two *entered* sectors land on the same split side.

**Paper proof sketch (PROVEN-on-paper modulo a mathlib gap).** The new cotree edge
is a single crossing-free arc between two prefix vertices; at each endpoint the
rotation system (`ArcsRotationRegular`) selects exactly one entered sector. Since
the arc crosscuts one face (its interior lies in a single residual region — the
region form is B2), the two entered sectors are the two ends of one face-boundary
walk, hence on the same side of the cut. The repo gap is the identification of the
*angular-rotation-chosen* corner with the arc's collar side; closing it needs the
`PlaneArcSeparation` first-crossing-germ machinery, not a combinatorial step.
Pinned mathlib v4.30 has no Jordan/Schoenflies for curved arcs; the straight-line
case routes through the sorry-free PL collar layer
(`exists_twoSidedPartition_prefixStep`), but the *identification* with the entered
sector is the remaining design.

### B2 — region separation (the Edmonds direction) — `prefixStepSameRegion`

`EdmondsSameRegion.lean:~180`, **sorry-free transport**. The lemma takes the
genuine geometric witness as hypotheses — sector points `q₁, q₂` with
`drm c₁ = regionAt … q₁`, `drm c₂ = regionAt … q₂`, and a common preconnected
complement subset `S ∋ q₁, q₂` with `S ⊆ drawingComplementIn (prefixEdges m) R₀`
— and concludes `drm c₁ = drm c₂` by `regionAt_eq_of_mem_isPreconnected`
(`RegionFaceBridge.lean:131`). It is **provable, not a `sorry`**: stating it with a
`True` placeholder for the geometry (as a first draft did) would make
`drm c₁ = drm c₂` *false* for arbitrary corners — so the real hypotheses are
threaded instead.

**Paper proof sketch for the remaining existence (the witness `S`/`q₁`/`q₂`), which
`hgeo` supplies (PROVEN-on-paper).** The cotree arc's open interior is disjoint
from every prefix arc (it is inserted last; the prefix arcs are the only ones
present at level `m`), so the open arc lies in one connected component of
`drawingComplementIn (prefixEdges m) R₀`. Both endpoints are limit points of that
one component. Take `S` = (open arc interior) ∪ (short collar segments at the two
corner sector points `q₁, q₂`); `S ⊆ drawingComplementIn (prefixEdges m) R₀` is the
only nontrivial input (disjointness of the open arc from the prefix arc union).
Feeding this `S, q₁, q₂` to `prefixStepSameRegion` gives `drm c₁ = drm c₂`.

**Hypothesis note: `hregion` does NOT require crossing-freeness `hfree`.** It needs
only (i) the cotree arc's open interior avoids the prefix arcs, and (ii) the two
endpoints are prefix vertices. `hfree` (no two arcs of the *full* drawing cross) is
strictly stronger and irrelevant here. The surrounding proof correctly does not
consume `hfree`; threading it through B2 would be over-hypothesizing. (Confirmed
by the deep-thinker pass; corrects the earlier framing that B2 is "the genuine use
of `hfree`".)

### B2 injectivity — `prefixStepSameRegion_poolRegion_injective` — **sorry-free combinator**

`EdmondsSameRegion.lean:~216`. The per-step `poolRegion = stepPoolRegion drm hconst
c₁ Wleft Wright` is injective, given three facts:

- old-face injectivity: distinct old faces ⇒ distinct regions = the predecessor
  region-separation `hsep` (the recursion's IH) — **available**;
- `hWne : Wleft ≠ Wright` — the two new sides are distinct global regions;
- `hWold` — every old region differs from `Wleft` and `Wright`.

The combinator is **sorry-free**; `hWne`/`hWold` are inputs the producer must
discharge.

**Correction to the naive construction (important).** `poolRegion` must NOT send
`Sum.inr 0/1` to the raw local sides `U,V` of `exists_twoSidedPartition_prefixStep`.
Those are *local tube fragments*: as literal sets `U` and `V` both sit inside the
*same* global old region (they only become distinct after the new arc is added),
so the raw map is not injective against the old global regions. The correct
`Wleft, Wright` are the two **global successor** regions
`regionAt (G'.prefixEdges (m+1)) (point in U)` and `… (point in V)`; the local
partition's role is solely to **certify** `Wleft ≠ Wright` (the local separation
inside the simply-connected tube propagates to a global separation of the
crosscut face). This local→global certification is the genuine geometric content
behind `hWne`/`hWold`:

```
-- NEEDS-DESIGN (illustrative; the content `hgeo` discharges to supply hWne/hWold —
-- NOT a created Lean declaration this session):
--   U,V the two-sided partition of regionMinusArc(tube, new arc);
--   u ∈ U∩F, v ∈ V∩F  (F = the old crosscut face)
--   ⟹  regionAt (G'.prefixEdges (m+1)) R₀ u ≠ regionAt (G'.prefixEdges (m+1)) R₀ v
```
This is the planar single-face-split fact viewed region-theoretically; it is the
**same content as B1 (`hsplit`) viewed angularly**. Either form, once proved,
yields the other through the proven split-pool machinery. The region form needs a
global-separation argument; the angular form (B1) stays combinatorial once
`vertexRotationAtRadius` is fixed and is the more tractable target in mathlib.

### `hfactor` is `rfl` — confirmed

`mkPrefixStepCrosscutData` (`:327`) defines `drm1 := stepRegionFamily …` =
`stepPoolRegion ∘ splitClass`, so `hfactor` is `fun hsame' d => rfl`. The
`∀ hsame` quantifier is honoured by proof irrelevance of `Perm.SameCycle` (a
`Prop`): `insertedFaceSplitPoolEquiv`'s only dependence on the witness is through
`insFacePermStep1_sameCycle_inl_dartA_of_sameCycle … hsame`, a proof of a `Prop`,
so the two `Equiv` terms are definitionally equal and `rfl` closes. **This `rfl`
elaborates** (the deep-thinker flagged it as needing verification; it builds).

## 4. How `hgeo` reduces to the leaves (the residual ST obligation)

The single remaining ST `sorry` (`SzemerediTrotter.lean:4649`) has type
`CrossingLemma.PerStepCrosscutInput G' start hARRprefix`
(`EdmondsSameRegion.lean:~470`): for each step `start ≤ m`, given `dr m` + `hconst m`
+ `hsep m`, produce `Nonempty (Σ' drm1, PrefixStepCrosscutData …)`.

The sorry-free composition witness `nonempty_prefixStepCrosscut_of_data` (`~378`)
shows this is exactly `mkPrefixStepCrosscutData` re-packaged. So discharging `hgeo`
requires, per step:

1. **Extract `c₁,c₂,hc,hsame,hvertex`** from the SameFaceData extractor
   `exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq`
   — this consumes **B1**, the extractor's `hsplit` argument (lines 5813–5867),
   plus the per-step endpoint/`π` plumbing (mechanical, not novel).
2. **Produce `Wleft,Wright,hWne,hWold`** from `exists_twoSidedPartition_prefixStep`
   (`PLCollarSeparation.lean:879`, closed) at the new edge's endpoints, promoting
   the local sides to the two distinct global successor regions (the region form of
   **B1/B2** — local separation propagated to global components).
3. **Produce `hregion`** from **B2** by building the witness `S, q₁, q₂` (open arc
   interior + corner collars) and applying the sorry-free `prefixStepSameRegion`.

`hgeo` is thus a clean composition of the two genuine geometric obligations (B1
`hsplit`, B2 witness existence + global-side distinctness) with the sorry-free
`exists_twoSidedPartition_prefixStep`, `prefixStepSameRegion`, and the SameFaceData
extractor. It is strictly smaller than the former monolith (B0 removed; region
transport + injectivity discharged). It was left as one ST-level `sorry` rather than
fully wired because the extractor's per-step endpoint/`π` plumbing (matching the
entered-sector corners to the partition sides) is bulk mechanical code that is not
the novel content and would not change the open mathematical obligation.

## 5. Remaining `sorry` inventory (file:line)

Exactly **one** `sorry` on the A1 path; the new file `EdmondsSameRegion.lean` is
**entirely sorry-free**.

| `sorry` | Location | Label | Content |
|---|---|---|---|
| `hgeo` (per-step producer) | `SzemerediTrotter.lean:4649` (in `straightLineCanonicalComponentResidualMapPlanarityOfARR`) | NEEDS-DESIGN | `PerStepCrosscutInput`: one bundle per cotree step. Reduces to: B1 = extractor `hsplit` (`ResidualMapProperties.lean:5785`, 5813–5867); B2 = witness existence for `prefixStepSameRegion` + global-side distinctness `hWne`/`hWold`; + mechanical extractor/partition wiring. |

No other `sorry` was added anywhere. The B1 `hsplit` and B2 witness existence are
two faces (angular / region-theoretic) of the same planar single-face-crosscut
fact; either, once proved, yields the other through the proven split-pool
machinery.

## 6. Axiom report

```
exists_dr_hstepCrosscut                         : [propext, Classical.choice, Quot.sound]
mkPrefixStepCrosscutData                        : [propext, Classical.choice, Quot.sound]
prefixStepSameRegion                            : [propext, Classical.choice, Quot.sound]
prefixStepSameRegion_poolRegion_injective       : [propext, Classical.choice, Quot.sound]
stepRegionFamily_hconst                         : [propext, Classical.choice, Quot.sound]
nonempty_prefixStepCrosscut_of_data             : [propext, Classical.choice, Quot.sound]
straightLineCanonicalComponentResidualMapPlanarityOfARR : [propext, sorryAx, Classical.choice, Quot.sound]
```
(`sorryAx` on the main theorem is the single `hgeo` `sorry`.)

## 7. What next (ranked, hardest first)

1. **B1 — the extractor `hsplit`** (angular single-face crosscut). The single
   genuinely-open node. Closing it likely also yields the region-form global-side
   distinctness (B2's `hWne`/`hWold`) through the proven split-pool equiv, so it
   unblocks both the extractor use and the injectivity inputs. Route:
   `PlaneArcSeparation` first-crossing germ order → identify the rotation-chosen
   corner with the arc's collar side. Needs the
   arc-separation machinery, not combinatorial plumbing.
2. **`hgeo` extractor wiring** (mechanical): per-step invoke the SameFaceData
   extractor (fed B1) + `exists_twoSidedPartition_prefixStep`, assemble via
   `nonempty_prefixStepCrosscut_of_data`. No new mathematics; bulk plumbing.
3. **B2 witness existence** (PROVEN-on-paper; the transport `prefixStepSameRegion`
   is already sorry-free): build the preconnected witness `S` (open arc interior +
   corner collars) and the sector points `q₁, q₂`, discharge
   `S ⊆ drawingComplementIn (prefixEdges m)`, then feed `prefixStepSameRegion`.
   Smaller than B1; depends on the arc→region collar setup. Folds into item 2.
4. After all three, A2 (`ST:4486 → … → :4867`) closes automatically (every link is
   already sorry-free), yielding the straight-line `SzemerediTrotterStatement`.
