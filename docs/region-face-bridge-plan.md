# The Region↔Face Bridge — implementation plan

Captures the design pass (2026-06-13) for the bridge that closes the two
remaining `sorry`s in `straightLineCanonicalComponentResidualMapPlanarityOfARR`
(`SzemerediTrotter.lean`). Both sorries reduce to **one** geometric input; this
plan specifies the bridge that supplies it.

Files: `ST` = `LeanFormalizations/PachDeZeeuw/PachSharir/SzemerediTrotter.lean`,
`RM` = `…/CrossingLemma/ResidualMapProperties.lean`,
`VG` = `…/Combinatorics/CombinatorialMap/VertexGraph.lean`,
`PAS` = `…/CrossingLemma/PlaneArcSeparation.lean`,
`PLC` = `…/CrossingLemma/PLCollarSeparation.lean`,
`RMap` = `…/CrossingLemma/ResidualMap.lean`.

---

## 0. Status / START HERE

- **The two target sorries:** `ST:4562` (`stComponentDrawing_residualMap_isPlanar_geometricResidual`,
  decl `ST:4551` — residual 1, `IsPlanar`/Euler `≥2`) and `ST:4713` (the `hface`
  argument of the step lemma called at `ST:4698`, `RM:9670`, hypothesis shape
  `RM:9711–9760` — residual 2, per-step cotree co-faciality).
- **Both reduce to ONE geometric core.** Residual 1 and residual 2 are the same
  input wearing two hats: residual 2 = "before the cotree crosscut, both
  endpoints' splice corners lie on the same residual region"; residual 1 = "after
  the crosscut, the two sides are different regions" (the Euler-increment). They
  share **one** `IsTwoSidedPartition` per cotree edge. Do **not** build them as
  separate monoliths.
- **The single load-bearing lemma is step 2** (§5): a well-defined
  `residualFaceRegion` + the Edmonds-correspondence direction
  `sameRegion ⇒ facePerm.SameCycle`. **This is the genuinely novel, irreducible
  content — not in Mathlib, not in the repo.** Budget the bulk of effort here.
  Everything else is a thin consumer once step 2 exists.
- **Concurrent dependency:** the geometric instantiation (Track B) consumes
  `exists_twoSidedPartition_of_polyArc` (built in `PLC`/`PLArc`). Track A (the
  hard core + abstract-hypothesis consumers) proceeds without it.

---

## 1. The correspondence the bridge asserts

`residualMap G hARR` (`RMap:104`) is built from local angular order only
(`vertexRotation` ← `ArcsRotationRegular`). Its `Face` (`Basic.lean:201`) is a
`facePerm`-cycle of darts, `facePerm = vertexPerm⁻¹ * edgePerm` (`RMap:120`) — the
standard "turn maximally clockwise" boundary walk. Geometrically each dart-cycle
traces the boundary of one connected component of `ℝ² \ ⋃ₑ Set.range (G.arc e)`.

Target correspondence (the full Edmonds bijection — **too much to ask in full;
each residual needs only a one-directional consequence**):

```
(residualMap G hARR).Face  ≃  { components of  ℝ² \ ⋃ₑ Set.range (G.arc e) }
```

Type alignment is native: `Plane := ℝ × ℝ` (`PAS:309`) is the same type as
`DrawnMultigraph.V` elements and `dartAnchor` outputs (`RMap:47`). Consumable
componentology already present in `PAS`: `IsTwoSidedPartition` (`:100`),
`regionMinusArc` (`:340`), `SplitsIntoTwo` (`:229`),
`connectedComponentIn_left/right_eq` (`:193`/`:211`),
`exactly_two_of_isTwoSidedPartition` (`:237`), `arc_src/tgt_mem_closure`
(`:160`/`:172`). **No existing face↔region lemma or partial bridge** exists
(exhaustive grep: no `drawingComplement`/`faceRegion`/`regionOf`).

---

## 2. Residual 1: crosscut ⇒ `IsPlanar` (`≥2`)

`≤2` is proven (`eulerCharacteristic_le_two`, `EulerBound.lean:523`). For `≥2`,
the repo already reduces to **dual-cotree acyclicity**:
`faceGraphOnEdgeSet_isTree_of_not_mem_range_vertexLeafOrder` (`VG:1305`) proves
the dual-complement subgraph is a tree but **takes `hplanar` as hypothesis**
(uses it only for the edge count `VG:829`); connectivity is free
(`VG:1152`). So the only missing fact is acyclicity = `≥2`.

**Do not route through the circular `VG:1305`.** Instead produce `IsPlanar` by the
Euler-increment over insertions: start from the spanning tree (1 face,
`residualMap_face_card_one_permuted_treePrefix_of_leafOrder`, `RM:8990`); each of
the `E−(V−1)` cotree edges, being a crosscut of its current region, splits one
face into two (`card Face += 1`). After all: `card Face = E−V+2 ⇒ χ = 2`. This is
**exactly the existing insertion assembler**:
`exists_residualMap_isPlanar_of_prefix_insertions_connected` (`RM:10358`),
`residualMap_isPlanar_prefixStep_of_insertion` (`RM:1757`), whose `.sameFace` step
preserves `IsPlanar` given `hsame : facePerm.SameCycle c₁ c₂` (`RM:1768`).

⇒ **Residual 1 needs no separate geometry.** With per-step co-faciality (residual
2) available for all cotree steps, residual 1 is the assembled sum. Currently
`ST:4654–4655` derives `hgeo : IsPlanar` *from residual-1's own sorry* to build the
index for residual 2 — circular. The fix (step 6) re-derives residual 1 from the
assembled prefix insertions.

---

## 3. Residual 2: crosscut ⇒ per-step co-faciality `hface`

Goal (`RM:9759`): `(residualMap (prefixEdges (a+j.1) hm) hARR).Face_mk c₁.1 =
…Face_mk c₂.1`, where `c₁,c₂` are the two angular splice corners at the endpoints
`p₁,p₂` of cotree edge `j` in the **prefix** map, under the rotation-match
conditions `RM:9737–9758`.

Geometric statement: in the partial drawing `prefixEdges (a+j.1)`, edge `j`'s arc
connects `p₁` to `p₂` within a single complement component — both splice corners
lie on the boundary of the *same* region (the one edge `j` is about to crosscut).
Same-region-before = `R` connected, both endpoints in its closure
(`arc_src/tgt_mem_closure`, `PAS:160/172`, proven). Split-after = the
`IsTwoSidedPartition` itself.

Instantiation chain (the new, hard direction — easy half of §1's bijection,
contrapositive): splice corners have anchors `dartAnchor` near `p₁,p₂` pointing
into sectors `sectorPlus/Minus` (`PLArc.lean:2645/2651`) ⊆ collar sides
`collarPlus ⊆ U`, `collarMinus ⊆ V`
(`exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets_with_collar_sides`,
`PLC:151`; sector→collar containments `sectorPlus_subset_collarPlus_of_sliver_budgets`,
docs `planar-tree-cotree.md:180–195`). **Missing piece** (`planar-tree-cotree.md:322–328`):
identify the vertex-rotation-chosen corner `c₁₀` (`exists_endpoint_splice_incidentAngle`,
`ST:2966`) with a collar side — `hchoose`, logically `⇔ hface` via injectivity of
`insertedFaceSplitPoolEquiv` (`RM:1469`).

---

## 4. Mathlib support / gaps (v4.30)

Present: `connectedComponentIn`, `IsPreconnected.subset_left_of_subset_union`,
`isPreconnected_connectedComponentIn` (already driving `PAS:193–223`);
`Equiv.Perm.SameCycle`, `Quotient` for `Face`; `Complex.arg`/`angleAt`
(`CrossingLemma.lean:358`).

Genuine gaps (no Mathlib shortcut): **no Jordan / Schoenflies / Riemann mapping**
(why the general `exists_twoSidedPartition_of_arc` stays sorried; PL route handles
polygonal arcs); **no combinatorial-map ↔ planar-embedding (Edmonds)
correspondence** — this is §1, entirely absent. Sidestep sphere
compactification by working inside a fixed open disk `R₀ ⊇ ⋃arcs` (all
`stComponentDrawing` arcs are segments ⇒ PL machinery applies natively); the outer
face is the unbounded-relative component of `R₀ \ ⋃arcs`.

---

## 5. Step list (ordered, anchored)

New file **`LeanFormalizations/PachDeZeeuw/CrossingLemma/RegionFaceBridge.lean`**,
between the geometry (`PAS`/`PLC`) and the consumer (`ST`).

1. **[Track A, new]** `def residualFaceRegion (G) (hARR) (f : (residualMap G hARR).Face) : Set Plane`
   = `connectedComponentIn (R₀ \ ⋃ₑ Set.range (G.arc e)) (interior pt of the face-walk)`,
   + well-definedness (representative-independent). The core new definition.
2. **[Track A, new, HARD — the load-bearing lemma]**
   `facePerm_sameCycle_of_sameRegion` (and converse half `sameRegion_of_facePerm_sameCycle`):
   the Edmonds direction. Build inductively: base = tree prefix (1 face = 1
   region, trivial via `RM:8990`); step mirrors `residualMap_isPlanar_prefixStep_of_insertion`
   (`RM:1757`). **Budget the bulk of effort here; do not assume it is free.**
3. **[Track B, new]** `cotreeEdge_crosscuts_residualFaceRegion`: cotree edge `j`'s
   segment arc is a crosscut of its face-region; instantiate
   `exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets`
   (`PLC:260`). **Needs the concurrent `exists_twoSidedPartition_of_polyArc`.**
4. **[Track A, new]** Lemma B `residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition`:
   consumes an abstract `IsTwoSidedPartition` + sector-side containments + step 2,
   yields `Face_mk c₁ = Face_mk c₂`. State against abstract crosscut now.
5. **[Track A, consumer]** Discharge `ST:4713` `hface` via Lemma B (step 4)
   instantiated by step 3. Short once Lemma B exists (goal is just `Face_mk c₁ = Face_mk c₂`).
6. **[Track A, consumer]** Discharge `ST:4562`. **De-circularize:** replace its
   standalone proof by driving `exists_residualMap_isPlanar_of_prefix_insertions_connected`
   (`RM:10358`) from the per-step co-faciality (step 5); removes the
   `hgeo`-from-sorry-1 dependency at `ST:4654`.
7. **[cleanup]** Update `planar-tree-cotree.md:315–328` and
   `cotree-formalization-plan.md` VERDICT; confirm `sorryAx` drops repo-wide.

### Dependency / track summary
- Steps 1, 2, 4 → **Track A**, proceed now against abstract crosscut hypotheses;
  **step 2 is the long pole.**
- Steps 3, 5, 6 → statements + wiring writable now against an abstract
  `∃ U V, IsTwoSidedPartition …`; full discharge needs the concurrent
  `exists_twoSidedPartition_of_polyArc`.
- Make **step 2** the single load-bearing bridge lemma; both residuals are then
  thin consumers sharing one `IsTwoSidedPartition` per cotree edge.

### Risk
- Tractable plumbing (given step 2): steps 1, 3, 4, 5, 6.
- The hard, novel sub-problem: **step 2** — tractable via the prefix-induction
  structure (base `RM:8990`, step `RM:1757`) but a multi-session lemma, the
  conceptual heart. Do not assume the Edmonds bijection is free.
