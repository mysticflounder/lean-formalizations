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

---

## 6. Execution status (2026-06-13) — three-agent results

Three import-disjoint agents ran on the warm cache. Net: the problem is now a
**proven, axiom-clean bridge backbone + two precisely-typed remaining targets**.
Neither ST sorry is closed yet; both targets are de-risked (no NO-GO, clear
shape). Build green at HEAD-equivalent.

### 6.1 LANDED — bridge backbone (commits `2909bb6`, `15de041`)
`RegionFaceBridge.lean`, 19 decls, **zero `sorry`/`admit`, axiom-clean**
(`propext`/`Classical.choice`/`Quot.sound`; no `sorryAx` leak — Lemma B takes
`IsTwoSidedPartition` as a *hypothesis*, never calls the `PAS:377` sorry):
- `residualFaceRegion` (step 1) + representative-independence — PROVEN.
- `facePerm_sameCycle_of_card_face_eq_one` / `edmondsCompatibleOfCardFaceOne`
  (step-2 **base case**, tree prefix 1-face) — PROVEN unconditionally.
- step-2 **inductive transport**: `region_separates` preserved across a
  same-face prefix insertion via `RM:844`
  (`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq`),
  instantiating the genuine `insertedFaceSplitPoolEquiv` — PROVEN.
- `sameRegion_of_facePerm_sameCycle` (converse) — PROVEN.
- Lemma B `residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition`
  (+`_of_collar_sides`, step 4) — PROVEN against abstract `IsTwoSidedPartition`.
- The hard Edmonds direction is honestly **isolated** into the
  `EdmondsCompatible.region_separates` structure field — not sorried, not faked.

### 6.2 TARGET 1 (Track A, the conceptual heart) — concrete `EdmondsCompatible`
Build a concrete `EdmondsCompatible G hARR R₀` for the *actual* `residualMap`
from `ArcsRotationRegular`, by cotree-prefix induction. Three fields:
- `dartRegion` — assign each dart the complement component its splice corner
  (`dartAnchor`) faces (candidate: `regionAt G R₀ (dartAnchor …)`).
- `dartRegion_isComponent` — each is a genuine `drawingComplementIn` component.
- `face_constant` (easy half) — invariant under `facePerm` (walking a face stays
  on one region's boundary).
- `region_separates` (hard half) — discharged by the **proven** base case
  (`edmondsCompatibleOfCardFaceOne`) + inductive transport (§6.1), where the
  per-step split consumes the inserted cotree edge's two-sided partition.

**LANDED (the iteration, commit pending) — `EdmondsConstruction.lean`, axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`; no `sorryAx`).** The cotree-prefix
induction is proved sorry-free, reducing the **global** `region_separates` clause
to a **per-cotree-step** datum + a one-face base:
- `PrefixStepCrosscutData` — the per-step abstract crosscut bundle: exactly the
  inputs of `region_separates_prefixStep_sameFace_concrete` *minus* the
  predecessor co-faciality `hsame` (the induction derives it from the predecessor
  region-separation) and the successor region assignment (the supplied family
  `dr`). Fields: `c₁ c₂`, `hc`, `hregion` (abstract "same region before"),
  `hvertex`, `poolRegion` (the two crosscut sides on split-pool classes), `hinj`,
  `hfactor`.
- `regionSeparates_prefix_of_crosscut` — the `Nat.le_induction` (mirrors the
  planarity induction `RM:1779`) chaining the **proven** per-step transport from
  the card-1 base (`facePerm_sameCycle_of_card_face_eq_one` ← `RM:8990`) to every
  prefix level. **This is the genuine new content of Target 1.**
- `edmondsCompatibleAtPrefix` — packages region-separation + the region family
  `dr` + `hcomp` + `hconst` into an `EdmondsCompatible` at every prefix level.

**Remaining for Target 1 (per-step geometric discharge, no longer the iteration):**
instantiate the five abstract hypotheses of `regionSeparates_prefix_of_crosscut`
/ `edmondsCompatibleAtPrefix` for the *actual* geometry —
- `dr` — **NOT `regionAt ∘ dartAnchor`** (degenerate: `dartAnchor d ∈ G.V` lies on
  an arc endpoint ⇒ `∈ arcUnion` ⇒ `∉ drawingComplementIn` ⇒
  `regionAt … (dartAnchor d) = ∅`; confirmed Agent §7.1). Instead
  `dr m hm d := regionAt (prefixEdges m hm) R₀ (dartSectorPoint … d)` where
  `dartSectorPoint` is a **new** off-vertex sector witness: the vertex
  `v = dartAnchor d`, the first-crossing direction of `d`, and that of its
  `vertexRotation`-successor, give a `vertexPlus a v b ∩ ball v ε` wedge; the
  point lands in `drawingComplementIn` for ε small (a new membership lemma). **No
  existing dart→sector-point function** (`sectorPlus` is per-`PolyArc`-segment, not
  per-incident-arc). Keep `dr` abstract in `EdmondsConstruction`; instantiate it in
  a **downstream file importing `PLArc`**.
- `hcard1` ← `RM:8990` on the spanning-tree prefix (direct, bridge-side).
- `hcomp` — `rfl` modulo the `dartSectorPoint ∈ drawingComplementIn` membership lemma.
- `hconst` — **NOT residual-side-only** (correction): needs a complement-connector
  (a thin collar strip alongside the edge joining the two corners' sector points
  around the same face), so it pulls in PL/collar geometry. Driving lemmas:
  `dartAnchor_residualMap_vertexPerm` (RMP:371), `residualMap_edgePerm_apply`
  (RMP:391), `residualMap_vertexPerm_apply_of_mem` (RMP:379), `facePerm_eq`
  (Basic:70), `regionAt_eq_of_mem_isPreconnected` (RFB:127). Tractable (single
  same-face connectivity, no Euler increment) but genuine geometry.
- each `PrefixStepCrosscutData` ← the cotree edge's two-sided partition realised as
  an injective `poolRegion` — **needs Target 2's output**
  (`exists_twoSidedPartition_of_polyArc`).
The iteration being closed, what was the "risk-bearing novel content" is now the
`dartSectorPoint` + its membership/connector geometry (`dr`/`hcomp`/`hconst`) plus
Target 2 (`PrefixStepCrosscutData`). **Buildable against abstract per-edge crosscut
data** — confirmed by the landed file; does NOT need Target 2 *proven*, only its
per-edge statement. Note `dr`/`hcomp`/`hconst` are sector-geometry, not pure
residual-side plumbing — they belong in the downstream PL-importing file.

### 6.3 REMAINING TARGET 2 (Track B) — `exists_twoSidedPartition_of_polyArc`
The PL crosscut for straight segments. The existing collar machinery is
**vacuous** (`sectorPlus/Minus := ball(verts, ρ)` forces unsatisfiable budgets
`ρ ≤ δ₀` ∧ `δ₀+2αL < ρ`). Fix = redefine sector as δ₀-corner-tube overlap
`vertexPlus ∩ {infDist · (segCarrier i) < δ₀} ∩ {infDist · (segCarrier i+1) < δ₀}`
(δ₀-governed, ρ-untied). Validated on paper (Agent-X, WIP in `git stash@{0}`,
recall nthdegree `mem2`). **Impact map (mapping agent, full report in session
transcript)**: ~200 line-references, **15–20 proof rewrites**:
- BREAKS (ball load-bearing): `sectorPlus_subset_taperedTube` (PLArc:8061),
  `overlap_sectorPlus_bandStripPlus_src/tgt` (6111/6171),
  `mem_sectorPlus_or_sectorMinus_of_ball` (2924),
  `disjoint_sectorPlus_sectorMinus_diff/_all` (3456/3795), `isOpen_sector*`
  (2816), `isPreconnected_collarPlus/Minus` (5070/7707) `hO1/hO2` overlaps.
- SURVIVES (angle-only): `disjoint_sectorPlus_sectorMinus` (3089). **Correction
  (§7.3):** `sectorPlus_subset_compl_carrier` (8289) survives only in its
  *incident-edge* sub-cases; its *nonincident* branch (8323) is ball-load-bearing
  and needs the strip-disjointness rewrite (`disjoint_stripSupport_nonadjacent`).
- DEEP obstruction (paper-resolved, not yet Lean): **P2-cover rework** — the
  existing `taperedTube_subset_midBands_union_disks` routes near-vertex points
  into a large disk a corner-tube can't capture; fix = split foot∈(0,1)→band vs
  outer-cone-behind-vertex→corner-tube (both `infDist` to incident edges = `dist`
  to shared vertex `v`, captured iff `dist(z,v) < δ₀`).
- Helper keystones still valid: `exists_delta_corner_confine` (PLArc:2635),
  `exists_pos_infDist_compl_of_isCompact` (3999).
- Public `exists_twoSidedPartition_of_arc` (PAS:377) stays sorried (general
  Schoenflies NO-GO); `_of_polyArc` is the new public PL entry to build.

### 6.4 Sequencing
Target 1 and Target 2 are **independent until final wiring** (Target 1 builds
against Target 2's *statement*, mirroring Agent-Y's abstract Lemma B). Per
hardest-first: **Target 1 (concrete `EdmondsCompatible`) is the risk-bearing,
novel content — attack it first**; if it closes against abstract crosscuts, the
goal reduces to the known-tractable Target-2 grind. Final wiring (steps 5–6):
instantiate Target 1's hypotheses with Target 2, then `ST:4713` via Lemma B and
`ST:4562` via `RM:10358`; `#print axioms` ST (target: drop `sorryAx`).

---

## 7. Three-agent intel (2026-06-14, read-only) — `dr` design, ST wiring, Target-2 gate

Iteration landed (§6.2); three read-only agents then mapped the three remaining
fronts. All file:line verified against the current tree.

### 7.1 `dr` faced-point design (the real `dartRegion`)
- `regionAt ∘ dartAnchor` is **degenerate** — see §6.2 correction. The faced point
  must be **off the vertex**, in the angular sector between the dart's two
  consecutive incident arcs.
- **No existing dart→sector-point function.** `sectorPlus`/`vertexPlus`
  (PLArc:2752/2384) are per-`PolyArc`-*segment*, and there is **no bridge** from a
  `DrawnMultigraph`'s `G.arc e` to the `PolyArc` collar machinery. The load-bearing
  new object is `dartSectorPoint` (vertex + first-crossing dirs of `d` and of its
  `vertexRotation`-successor ⇒ `vertexPlus a v b ∩ ball v ε`) + membership lemma
  `dartSectorPoint ∈ drawingComplementIn` (ARR first-crossing + finitely many arcs
  ⇒ small wedge off `v` misses `arcUnion`). This is genuine PL/angular geometry.
- Decision: keep `dr` abstract in `EdmondsConstruction.lean` (already so);
  instantiate it `regionAt … (dartSectorPoint …)` in a **downstream file importing
  `PLArc`**, leaving the landed file untouched. `hcomp` then `rfl`-trivial modulo
  membership; `hconst` needs a same-face collar-strip connector (driving lemmas in
  §6.2). Anchor index: `dartAnchor` RM:47, `vertexRotation` CrossingLemma.lean:574,
  `incidentEnds` CL:350, `convexSector_nonempty` PLArc:214.

### 7.2 ST consumer wiring (both sorries live in `hstep`'s cotree branch)
- **Entanglement:** main thm `straightLineCanonicalComponentResidualMapPlanarityOfARR`
  (ST:4571) gets `IsPlanar` from `exists_residualMap_isPlanar_of_prefix_insertions_connected`
  (RM:10358) at ST:4714–4719, fed `hstep` (ST:4616–4713). The residual-1 lemma
  (decl ST:4551) is consumed at **exactly one site** (ST:4655), purely as a
  *counting* device: its `IsPlanar` → Euler → `hcount` → the cotree index `j`.
  Both sorries sit inside `hstep`'s cotree branch — they are **one task: fix
  `hstep`.** RM:10358's other hyps (`hjoin`/`hconn`/`hv`/`hARR` family) are already
  in scope (ST:4716–4719); only `hstep`'s sorries block it.
- **De-circularize residual-1:** derive `hcount` **combinatorially** — tree prefix
  has `card Face = 1` (RM:8990); each cotree step splits one face (`+1`, via RM:844
  / the sameFace step) ⇒ `card Face = lface.length` ⇒
  `(lvertex.length−1)+(lface.length−1) = numEdges`, **no planarity assumed**. Then
  the residual-1 lemma is dead weight — re-prove it as a corollary of the main thm,
  or delete. **TODO (not yet written):** the packaged `card Face = lface.length`
  face-count-increment induction (only the 1-face base RM:8990 + per-step RM:844
  exist).
- **Residual-2 discharge** (goal at ST:4713 = `Face_mk c₁.1 = Face_mk c₂.1` over
  `(G.permuteEdges π).prefixEdges (a+j.1) hm`, with `a = lvertex.length−1`,
  `a+j.1 = m`):
  ```
  Quotient.sound (regionSeparates_prefix_of_crosscut
    (G := G.permuteEdges π) (start := lvertex.length-1) hARRprefix dr hcard1
    hstepCrosscut (n := a+j.1) hstartn hm c₁.1 c₂.1 hregion)
  ```
  Type-aligns **at the prefix level** (no `permuteEdges` transport — instantiate
  the bridge's `G := G.permuteEdges π`, `n := a+j.1`). `c₁.1, c₂.1 : Fin (a+j.1) ×
  Bool` are the incident-end projections.
- **The one real call-site obligation:** identify the `hface`-bound `c₁,c₂`
  (arbitrary incident ends + rotation-match RM:9737–9758) with the crosscut
  datum's *specific* corners, to get `hregion : dr (a+j.1) hm c₁.1 = … c₂.1`.
  Bridge-side/combinatorial, but non-mechanical.
- **Prereq step 0:** ST does **not** import the bridge yet (and uses none of its
  API); add `import …CrossingLemma.EdmondsConstruction` to ST.

### 7.3 Target-2 gate verdict: **GO** (`exists_twoSidedPartition_of_polyArc`)
- **OLD ball sector: provably UNSAT.** The collision is in
  `isPreconnected_collarPlus_of_sliver_budgets` (PLArc:8667), which for an interior
  vertex carries both `hρδ : ρ(succ i) ≤ δ₀` (8695) and
  `htgt : δ₀+2αL < ρ(succ i)` (8700) ⇒ `2αL < 0`. (Matches the machine-verified
  `False`-from-bundle finding.)
- **NEW δ₀-corner-tube sector: jointly SATISFIABLE** (concrete assignment given) —
  **but with a subtlety**: reusing the *narrowed band* foot witness (`1−2α`) in the
  rewritten `overlap_…_src/tgt` reintroduces the wall (`‖Δ‖₁·‖Δ‖∞/‖Δ‖₂² < 1/4`,
  impossible by `l1_linf ≥ l2sq`). **Resolution:** the corner-tube admits a **free
  off-edge witness** along the bisector toward `v`, decoupling δ₀ from `αL` ⇒ Group
  B reduces to `δ₀ > 0`. SAT holds; the redefinition is sound.
- **Two residual PROOF obligations** (not satisfiability obstructions): {{NEEDS_PROOF}}
  (i) the δ₀-only (ε-free) witness reconstruction in `overlap_sectorPlus_bandStripPlus_src/tgt`
  (PLArc:6111/6171) — genuine proof, not signature surgery; (ii) a new
  `infDist_segment_eq_dist_endpoint_of_footParam_le_zero` lemma for the P2-cover
  outer-cone branch.
- **`stash@{0}` = first third done** (+102/−69, PLArc.lean only, up to ~3700): new
  `sectorPlus/Minus` defs, `isOpen_sector*`, `collar*` call sites,
  `disjoint_sectorPlus_sectorMinus` + `_diff`, the adjacent band↔sector glue, the 4
  endcap↔sector lemmas (ball→infDist-budget). **Missing:** reach lemmas (6111/6171),
  P2-cover (2505/2924/2956), `isPreconnected_sectorPlus/Minus` (4690/4697, **need a
  new `0 < δ₀` hyp**), `sectorPlus_subset_taperedTube` (8061), the bundle (8667),
  and PLCollarSeparation (151/260). Do **not** `git stash pop` blind — re-apply
  selectively after the def surgery.
- **P2-cover rework confirmed:** split near-vertex points by foot sign on the near
  edge — foot ∈ (0,1) ⇒ band; foot ≤ 0 (outer cone behind `v`) ⇒ both incident
  `infDist = dist(·,v)`, captured by corner-tube iff `dist(z,v) < δ₀`; retire
  `mem_sectorPlus_or_sectorMinus_of_ball` (2924) → `_of_cornerTube`.

## 8 · δ₀-tube grind — session 2026-06-14 (cascade GREEN + reach crux diagnosed)

Applied `stash@{1}` (the def surgery), then built the **whole disjointness cascade**
for the δ₀-tube model. **Validated GREEN** (the entire 3777–4111 region compiles):

- **New helpers** `disjoint_stripSupport_sectorPlus/Minus_nonincident`: a non-incident
  edge `i ∉ {j,j+1}` is non-adjacent to at least one of the corner's incident edges
  (incoming `j` or outgoing `j+1`); route through that strip via `hsep`. Replaces the
  obsolete vertex-ball `disjoint_stripSupport_vertexBall_nonincident`.
- **7 `_all` aggregators rewritten** ball→strip/budget, dropping the dead `ρ`/`hρsep`:
  band↔sector (nonincident via the new helpers); sector↔sector (`hballs`→`hsep`+`hδ₀sep`,
  incoming-of-smaller-corner vs outgoing-of-larger, gap ≥ 2); the 4 cap↔sector
  (`hballs`→`hbudsrc`/`hbudtgt`; src cap needs the `j=0` outgoing-edge special case,
  tgt cap always uses the incoming edge `j ≤ numSegs-2`).
- **Master `disjoint_collarPlus_collarMinus`** dropped `hρsep` (now dead); `hballs`
  survives only for the two endpoint cap↔cap pairings. Caller updated.

**Reach lemma = the genuine crux** (`overlap_sectorPlus_bandStripPlus_src`, PLArc:6222).
The δ₀-tube sector additionally needs the witness within δ₀ of the **outgoing** edge i+1.
The naive on-edge band witness (foot `1−2α` or `1−α`, near `v`) **provably hits a wall
for gentle corners**: the joint reach `αL·sinφ < δ₀` and band-thinness `hδin`
(`δ₀ < α·(L²/‖Δ‖₁)·|tanφ|`) reduce to **`|cos φ| < ‖Δ‖₂/‖Δ‖₁`**, which fails when the
corner turn `φ ≈ 0` and edge `i` is diagonal (`‖Δ‖₂/‖Δ‖₁ → 1/√2`). This *supersedes*
§7.3's hand-wavy "free bisector witness ⇒ reach reduces to δ₀>0" — that claim was not
verified and the wall is real for that witness family.

**ROOT CAUSE + FIX LEAD (concrete, not a dead end):** the wall is *entirely* from the
**`‖Δ‖₁` L1-norm** in `hδin`, which enters via `thin_of_infDist_incoming` (≈PLArc:3284,
used by `bandStrip_incoming_mem_vertexPlus` 3263). If `thin_of_infDist_incoming` can be
reproven with **`‖Δ‖₂`** (L2) instead of `‖Δ‖₁`, the joint condition becomes
`|cos φ| < 1` — true for **every** genuine corner (`φ ∈ (0,π)`, `φ≠0`) — and the wall
dissolves. {{NEEDS_PROOF}}: verify `thin_of_infDist_incoming` admits the L2 bound
(depends on whether its `‖Δ‖₁` is a coordinate-wise-essential estimate or a soft
Cauchy–Schwarz step that tightens to `‖Δ‖₂`). **This is the next action.** If L2 holds,
the reach goes through with the existing on-edge witness (re-pointed at the δ₀-tube,
`hbud` δ₀+2αL<ρ replaced by a δ₀-only `2αL·sinφ < δ₀`-type condition); if not,
the bisector witness must be built and re-analysed against the L2 threshold.

**WIP location:** `stash@{0}` (backup) AND the live working tree (PLArc.lean, +242/−131).
The cascade is done; remaining errors are all downstream of the reach resolution or
independent-but-mechanical (`isPreconnected_sector*` convexity 4801/4811,
`sectorPlus_subset_taperedTube` 8172, the bundle 8634, P2-cover 2946). Do these *after*
the reach is settled (the reach may change δ₀/α constraints feeding the bundle).

## 9 · §8's fix-lead is DEAD; the intersection-tube walls structurally; pivot to a union tube (2026-06-14, later)

§8's `{{NEEDS_PROOF}}` (tighten `‖Δ‖₁ → ‖Δ‖₂` in `thin_of_infDist_incoming`) is now
**resolved NEGATIVE — provably impossible** — and the diagnosis sharpened to a
*structural* wall in the intersection-tube model. Verified by reading, no longer
conjectural.

**(a) `Plane = ℝ×ℝ` carries the L∞ (sup/max) product metric** (`Prod.dist_eq`), not
Euclidean. So `Metric.infDist` is the L∞ distance `d∞`.

**(b) The L2 tightening is impossible.** The cross-product identity is
`|sideForm v b z| = ‖b−v‖₂ · d₂(z, line)` with `d₂` the *Euclidean* perpendicular
distance. But for every vector `‖x‖∞ ≤ ‖x‖₂`, so `d∞ ≤ d₂` *always*. Hence
`|sideForm| ≤ ‖Δ‖₂ · d∞` would require `d₂ ≤ d∞` — false. The existing
`abs_sideForm_le_M_infDist` with `M = ‖Δ‖₁` is in fact the **sharp** bound for this
metric (`‖Δ‖₂ ≤ ‖Δ‖₁ ≤ √2‖Δ‖₂`). The norm cannot be improved. §8's "wall dissolves"
lead is dead.

**(c) The wall is structural to intersection-tube + α-margin bands.** Two constraints
on the single shared `δ₀` at a corner (turn ψ = π−θ, edge length L):
- **Reach** (`sectorPlus i ∩ bandStripPlus i ≠ ∅`, needed for collar connectivity):
  `bandStripPlus` forces `footParam ∈ (α,1−α)`, so every band point is `≥ αL` from the
  shared vertex *along edge i, on the far side of v from the outgoing edge*. For a gentle
  corner the foot onto edge i+1 falls outside the segment, so
  `infDist∞(z, edge i+1) ≥ αL − δ₀`; the δ₀-tube sector needs that `< δ₀` ⟹ **δ₀ > αL/2**.
  (Sharper than §8's `αL·sinφ`: that mis-modelled it as perp-to-*line*; the foot is
  outside the *segment*, so there is **no sinφ rescue**.)
- **Adjacent disjointness** (the glue): `thin_of_infDist_incoming`'s sharp `‖Δ‖₁` bound
  forces **δ₀ < α·|tanψ|·‖Δ‖₂²/‖Δ‖₁**.

For gentle corners `|tanψ|→0` drives δ₀→0 while reach keeps δ₀ ≳ αL > 0. **The α
cancels** (linear on both sides) — no budget choice closes it. Empty δ₀-window whenever
`|tanψ| ≲ ‖Δ‖₁/‖Δ‖₂ ∈ [1,√2]`, i.e. for **every turn gentler than ~45°**. The
intersection-tube model (`sectorPlus = vertexPlus ∩ {δ₀ of i} ∩ {δ₀ of i+1}`) is a
NO-GO. The doc comment at `sectorPlus` (PLArc:2758) claiming decoupling δ₀ from ρ
"escapes the wall `L₂² ≤ L₁·L∞`" is right for the disjointness cascade but **the reach
lemma re-imports the wall**.

**(d) Decision (Adam, 2026-06-14): switch to the UNION tube.**
`sectorPlus = vertexPlus ∩ ({δ₀ of edge i} ∪ {δ₀ of edge i+1})`. The reach wall is
entirely from the *intersection* demanding a band-overlap point (near one edge) also be
near the other; the union drops that. Reach: a band-i point is δ₀-close to edge i, so the
`{δ₀ of i}` disjunct holds — any δ₀ > 0 works.

**(e) Gate VERIFIED — consecutive sector⁺/sector⁻ disjointness CLOSES.** Worry: under a
union each sector is a *two-strip* set, so strip-separation no longer isolates sectors
sharing edge i+1; disjointness must come from the **angular sign on the shared edge**,
and `reflexSector` is an OR that does not obviously pin it. **Resolved** via the existing
`overlap_mem_convexSector_iff` / `overlap_mem_reflexSector_iff` (+ `_incoming`,
PLArc:1959–2033): on a thin overlap with positive foot, the reflex OR **collapses** to
the single thin-edge sign (`pos_turn_sideForm_of_overlap` kills the other disjunct). Then
with σ := `sideForm(v_{i+1}, v_{i+2}, z)` on the shared edge:
- `z ∈ sectorPlus_i` (thin to edge i+1 as *outgoing*, interior foot) ⟹ **σ > 0** in
  *both* τ_i>0 (convex) and τ_i<0 (reflex) cases — the τ-selection and convex/reflex sign
  exactly compensate;
- `z ∈ sectorMinus_{i+1}` (thin to edge i+1 as *incoming*) ⟹ **σ < 0** in both cases.

Contradiction. **Orientation coherence**: the collar sign on *any* edge is +1 on the +
side and −1 on the − side, independent of corner type. Gate passes → **GO**.

**(f) Rework scope (obstruction-free, multi-session).** The union breaks the green
cascade's single-strip subset lemmas (`sectorPlus_subset_stripSupport_incoming =
fun _ hz => hz.1.2` etc. — now a two-strip union) and complicates *all* sector
disjointness (closest strip-pair of two unions can be adjacent, not just for consecutive
corners — gap-2 sectors meeting at a shared vertex also need the σ-sign argument, not
strip-separation). Plan:
  1. **Lynchpin first** (hardest): a reverse-glue σ-sign lemma packaging (e) —
     `z ∈ sectorPlus/Minus_i ∧ thin to a shared edge ∧ interior foot ⟹ definite σ sign`
     — built on the existing `overlap_mem_*_iff` lemmas.
  2. New sector def (union); re-prove the subset lemmas as "in stripSupport_i ∪
     stripSupport_{i+1}" + the σ-sign lemma.
  3. Re-prove the disjointness aggregators: far pairs via strip-separation (unchanged
     idea, now over the union), adjacent/shared-vertex pairs via the σ-sign lemma.
  4. Reach lemmas: drop ρ/`hbud`, conclude union-tube membership (trivial — band point is
     δ₀-close to its own edge).
  5. Downstream connectivity / cover / bundle, then green build → COMMIT.
**Boundary cases** (z near a shared vertex, foot→0/1): open sectors exclude the corner
locus (σ=0 there), and near a vertex z is thin to both incident edges — handled by the
incident corner's structure. No wall, normal formalization.

## 10 · UNION-tube GREEN BASELINE landed (2026-06-14) — `sorry` worklist for the rework

`PLArc.lean` now **compiles green** under the union sector
(`sectorPlus = vertexPlus ∩ ({δ₀ of i} ∪ {δ₀ of i+1})`); `PLCollarSeparation` (its only
consumer) builds unchanged — the rework is **fully contained in `PLArc`, no external API
churn** (verified: no file outside `PLArc` references any changed/removed name). This is a
*baseline*: the genuinely-union-reworked proofs are explicit `sorry`s with in-line specs, so
the file gives a build signal and a per-hole worklist instead of a non-compiling 8700-line
blob. Each `sorry` carries a `-- §9 UNION …` comment stating its goal and route.

**LANDED (proven green, not sorried):**
- The 4 reverse-glue σ-sign lynchpin lemmas (`vertexPlus/Minus_sideForm_outgoing/incoming_*`).
- Def + `isOpen_sector*` (union shape); the two `*_subset_stripSupport_union` lemmas.
- **All 4 reach lemmas** (`overlap_sector{Plus,Minus}_bandStrip{…}_{src,tgt}`) — the union
  *trivialised* them: the witness is δ₀-close to one incident edge, so sector membership is
  `⟨hmemV, Or.inl/Or.inr hinf⟩`; `hball`/`ρ`/`hbud` are now redundant (reach for any δ₀>0).
- Same-vertex / band↔sector angular disjointness (`disjoint_sectorPlus_sectorMinus`,
  `disjoint_bandStrip{Plus,Minus}_sector{Minus,Plus}_{in,out}going`) — survived via the
  `hz.1.1 → hz.1` projection reshape (union drops one nesting level).
- `*_subset_compl_carrier` incident-edge branches; `isPreconnected_collar{Plus,Minus}` +
  chain assembly (kept valid — `isPreconnected_sector*` no longer needs `0<δ₀`: empty when
  δ₀≤0, so the hypothesis was dropped and callers are unchanged).

**`sorry` worklist (20 decls) — the remaining union rework, grouped:**
1. **σ-sign disjointness (the lynchpin's consumers).** `disjoint_sectorPlus_sectorMinus_all`
   (far pairs |j−k|≥3 via 4-way strip-sep over the union; |j−k|∈{1,2} via the σ-sign lemmas
   on the shared edge — ADD a per-corner `hturn`); the two
   `disjoint_stripSupport_sector{Plus,Minus}_nonincident` (RESTATE for `bandStrip` + foot-
   margin — the `stripSupport` form is too strong now); `disjoint_sectorPlus_sectorMinus_diff`
   (hypothesis now too weak — likely subsumed by `_all`).
2. **cap↔sector (8 decls).** `disjoint_{endCap…_sectorMinus, sectorPlus_endCap…}` per-lemmas
   and their `_all` aggregators — RESTATE with a second-arm (edge `j+1`) budget; separate the
   cap from BOTH arm strips via `sector*_subset_stripSupport_union`.
3. **P2 cover (2 decls).** `mem_sectorPlus_or_sectorMinus_of_ball` is **FALSE** under the
   union (a vertex-ball point need not be δ₀-close to an incident edge) → RETIRE to a
   `…_of_cornerTube` with the foot-sign split (`footParam∈(0,1) ⇒ band`; `footParam≤0`
   behind `v` ⇒ both incident `infDist = dist(·,v)`, caught iff `dist(z,v)<δ₀`); the
   interior-vertex branch of `union_collarPlus_collarMinus` consumes the reworked routing.
4. **sector connectivity (2 decls).** `isPreconnected_sector{Plus,Minus}` — `vertexPlus`
   cone ∩ (two strips through the apex `v`); star-connect through the shared apex wedge.
5. **sector ground-set containment (2 decls).** `sector{Plus,Minus}_subset_taperedTube` —
   route through the strip (like `bandStrip…_subset_taperedTube`), not the gone vertex ball;
   budgets `hρδ`/`hρR` become unnecessary.
6. **`compl_carrier` non-incident branch (2 decls).** separate the two arm strips from the
   non-incident carrier edge `k` via `disjoint_stripSupport_nonadjacent` (foot-margin/σ-sign
   for an adjacent arm).

**Handoff note.** Items 1–2 are the load-bearing σ-sign work (the lynchpin is the tool); 3
is the known P2 rework; 4–6 are localized. None has an identified NO-GO. A filler should work
hole-by-hole against `lake-build.sh` (no LSP); each `sorry`'s goal is stated in its comment.
Some statements in items 1–2 need *signature* revision (extra `hturn` / second-arm budget) —
flagged in-comment — so they are not pure body-fills.

## §11 — Arc-endpoint containment blocker + clipped-sector resolution (2026-06-14)

While filling item 5, the `sector*_subset_taperedTube` `sorry` was found to be **genuinely
false**, not a body-fill — the §10 "route via strip" note under-estimated it. The fix is a new
collar-facing **clipped sector** def. Decision recorded in nthdegree
(`01KV4XMHHZA6FKC03FPYK80KGD`).

**The blocker (verified).** `vertexPlus` is an *unbounded* wedge, so `sectorPlus`'s strip arm
runs the full incident edge down to the arc endpoints `verts 0` / `verts last`, which sit on
`∂R` where the tapered tube radius `min δ₀ (½·infDist Rᶜ)` → 0. So the raw union sector pokes
*outside* the tube at the two arc-endpoint corners (`i=0` incoming arm; `i=numSegs−2` outgoing
arm), and `sectorPlus_subset_taperedTube` (PLArc:8619) cannot hold. The wedge provably reaches
`verts0`: `τ·sideForm(verts1,verts2,verts0) = τ² > 0` (via `sideForm_cyclic`), so the wedge's
second half-plane condition holds there. A parameter-free or fixed foot margin provably fails
(the margin must scale with `α`); shrinking `δ₀` doesn't help (the taper is a ratio, always wins
at the frontier).

**Fix — keep `sectorPlus` (arity 3, unclipped); add `sectorPlusClipped` (arity 4, `+α`).** A
per-arm asymmetric `footParam` clip trims only the FAR (non-shared) end of each arm —
incoming edge `i` (shared vertex at foot 1) keeps `α < foot`; outgoing edge `i+1` (shared vertex
at foot 0) keeps `foot < 1−α` — preserving the shared-corner reach (the union's purpose).
`collarPlus`/`collarMinus` switch to the clipped sector. Bridges:
- `sectorPlusClipped ⊆ sectorPlus` ⇒ **every `sectorPlus` disjointness lemma (items 1–2) feeds
  the clipped collar UNCHANGED via `Disjoint.mono`** — so the disjointness worklist is unaffected
  and was handed to a worktree agent against the arity-3 def.
- containment `sectorPlusClipped ⊆ tube`: now provable (witness `foot > α/2 > 0` ⇒ interior
  carrier ⇒ R-bound; the `foot ≳ 1−α/2` / past-`v` range uses the shared-vertex budget).
- `isPreconnected (sectorPlusClipped)`: apex hub near `v` survives the clip (`foot_i ≈ 1 > α`,
  `foot_{i+1} ≈ 0 < 1−α`).
- cover: the trimmed far-tip is ceded to the adjacent corner's sector (its other arm keeps that
  edge's shared-vertex end) or to the end cap (arc endpoints) — the P2 cover lemma (item 3).

**Status.** Landed: `sectorPlusClipped`/`sectorMinusClipped` defs + `isOpen` + the two
`⊆ sectorPlus` bridges. Remaining clip-core (mine, regions disjoint from the disjointness agent):
clipped containment, `isPreconnected_collar` rework to the clipped piece, overlap/`compl_carrier`,
collar-def switch, cover. The arity-3 disjointness block (3549–4049) is untouched by this.

## §12 — Clip-core execution (2026-06-15): mono-fails correction, step 1 GREEN, parallel dispatch

**Correction to §11's mono claim.** §11 asserted *every* `sectorPlus` disjointness lemma transfers
to the clipped collar via `Disjoint.mono`. That is true only for the NON-degenerate cells (same
corner, far corners ≥2 apart, nonincident bands). The prior disjointness agent established that the
**6 degenerate sub-cases are genuinely FALSE for the unclipped sectors** (near the shared vertex the
two opposite-sign wedges overlap), so `Disjoint.mono` cannot transfer them — they must be proven
**clipped-direct**, where the clip's foot bounds on the shared edge supply the missing certificate.
The 6 live at the `sector↔sector |j−k|∈{1,2}` aggregator (2 sorries) and the 4 `cap↔sector` arc-endpoint
arms.

**Step 1 — clipped containment — DONE (commit `71f1b93`, build green, 8476 jobs).**
`sectorPlusClipped_subset_taperedTube` + `sectorMinusClipped_subset_taperedTube`. The proof routes
each clipped arm through its carrier foot-point exactly like `bandStripPlus_subset_taperedTube`, but
with an **asymmetric safe window** instead of a vertex-ball budget: incoming arm `[α/2, 1]` (the upper
end is the interior shared vertex `verts(i+1)`, NEVER an arc endpoint since `0 < i+1 < numSegs`),
outgoing arm `[0, 1−α/2]`. The OPEN window end is closed by `footParam_mem_Icc_of_mem_segment` (a
carrier point has foot in `[0,1]`). Hypotheses per arm: a Lipschitz budget `hsmall_*`, and
`hS_*`/`hR_*` over the asymmetric window. The clip keeps every foot-point off the tube-vanishing arc
endpoints, so the false unclipped `sectorPlus_subset_taperedTube` is simply retired (deleted in
integration). **Subtlety learned:** after `rcases` of the clip disjuncts, the strip/foot facts stay
raw `setOf` memberships (`z ∈ {z | …}`), which `linarith` will NOT read — coerce first with
`simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at h2`.

**Parallel dispatch (worktree agents, additive, disjoint regions):**
- **Agent P** — `isPreconnected_sectorPlusClipped`/`Minus` (step 2): extend the `isPreconnected_sectorPlus`
  apex-hub proof with the convex foot half-plane factor; apex near `v` satisfies the clip for small ε.
  Added hyps `0 < α`, `α < 1`.
- **Agent D** — clipped degenerate disjointness aggregators (step 5):
  `disjoint_sectorPlusClipped_sectorMinusClipped_all` + 4 `cap↔clipped-sector`. Per-combo recipe:
  index-distance ≥2 arm pairs → `hsep`; adjacent-edge combos → corner-confinement (`not_mem_adjacent_band_strip*`
  pattern) + the clip foot bound; the single shared-edge combo (k=j+1) → σ-sign
  (`vertexPlus_sideForm_outgoing_pos` vs `vertexMinus_sideForm_incoming_neg` on the same edge).

**Integration (mine, serial, after P+D land):** swap `sectorPlus→sectorPlusClipped` in `collarPlus`,
`collarChainPlus` (and Minus); rewire `isPreconnected_collarChainPlus`/`isPreconnected_collarPlus`/`Minus`
+ `_of_sliver_budgets` (`hsectorW`→clipped containment with the new window hyps; `isPreconnected_sector*`→clipped;
`hO1`/`hO2`→clipped overlap); rewire master `disjoint_collarPlus_collarMinus` (mono for non-degenerate
cells, the new clipped aggregators for degenerate); retire the false unclipped `sector*_subset_taperedTube`;
clipped-direct `sector*Clipped_subset_compl_carrier`; cover rework (`mem_…_of_ball` → `_of_cornerTube`,
disk-routing into the clipped sector union).

## §13 — Integration restructured into Phase 1 (additive) + Phase 2 (big-bang flip) (2026-06-15)

Reading every consumer of the collar defs showed step-7 integration is an **atomic serial def-switch**:
`collarPlus`/`collarMinus` feed master / cover / `exists_collar_disjoint` / sliver wrappers
simultaneously, so the file is broken until the *entire* flip lands — there is no green-verifiable island
for a parallel agent **except support lemmas that do not reference the collar**. So the work split:

**Phase 1 — additive support lemmas (green-incremental, parallelizable). DONE, merged to main, green.**
- Clipped overlap witnesses x4 (`overlap_sectorPlusClipped_bandStripPlus_src/tgt`,
  `overlap_sectorMinusClipped_bandStripMinus_src/tgt`) — same witness as the unclipped twins; the foot-clip
  falls out of the existing `hfoot` since `1-2a > a` and `2a < 1-a` under `hα3`.
- Clipped off-carrier x2 (`sector{Plus,Minus}Clipped_subset_compl_carrier`) — **non-incident case fully
  closed, no sorry, axiom-clean** (`propext, Classical.choice, Quot.sound`). Adjacent sub-cases
  (incoming arm `k=i-1`, outgoing arm `k=i+2`) close via `footParam_lt_of_confined_src` /
  `footParam_gt_of_confined_tgt` fed by a confinement budget; signature carries the **agent-D budget family**
  `(hα)(hd0)(hdsep)(hd0sep)(hsep)(r)(hconf)(hLr)`.
- Clipped `diff_carrier` x2 (`sector*Clipped_subset_taperedTube_diff_carrier`) — thin combinator of the
  clipped tube lemma (window-style `hsmall_*`/`hS_*`/`hR_*`) and the clipped off-carrier lemma.

**Two Phase-2 simplifications found:**
1. `exists_corner_delta` (~5430) **already computes** `r := a/(1+Lc+Lc1)`, `hLcr`/`hLc1r` (the Lipschitz
   budgets) and `hconf` (via `exists_delta_corner_confine`) internally — used and discarded. So the master's
   new `r`/`hconf`/`hLr` are obtained by *exposing them in `exists_corner_delta`'s existential* and threading
   through `exists_collar_disjoint`. **No new geometry.**
2. The cover `union_collarPlus_collarMinus` (~3099) **typechecks unchanged** after the flip: band-point and
   endpoint cases route into the band/cap components (clip-independent); the only sector-touching case is
   already the `sorry` at ~3160. `mem_sectorPlus_or_sectorMinus_of_ball` (~3081) is a false, unused lemma —
   just delete it (-1 sorry).

**Phase-2 OPEN ISSUE (flag for the flip):** the clipped tube lemma needs `hR_in`/`hS_in` over the foot
window `Icc(a/2) 1` (carrier points up to the shared vertex `verts(succ i)`), but the sliver wrapper's
`hRband` only covers `Icc(a/2)(1-a/2)`. The wrapper rewiring must **bridge the gap foot in (1-a/2, 1]** near
the shared vertex (via the vertex R-budget `hρR` + a closeness argument, or by widening `hRband`).

**Phase 2 — the big-bang flip (serial, NEXT, fresh window):** full edit list + the
master/`exists_corner_delta` plumbing recipe is in the nthdegree decision memory linked from `ws:next`
(`01KV5BX1SF...`). Sorry budget: 13 -> retire false-tube x2 + sorried aggregators x6 + `mem_..._of_ball` x1
+ unclipped `compl_carrier` x2 (replaced by green clipped) => target ~2 sorries (union disk-routing ~3160,
plus the unclipped-`compl_carrier` line if not deleted).

## §14 — Phase 2 COMPLETE (2026-06-15) — collar flipped to clipped sectors, GREEN

The big-bang flip landed: `PLArc.lean` builds GREEN (`LAKE_EXIT=0`) with **exactly one `sorry`**
(`union_collarPlus_collarMinus` interior-vertex disk-routing, ~3140 — the designated keep). Commit
`58e0a98`, fast-forwarded onto `152619c`; diffstat **149 insertions / 425 deletions**, only `PLArc.lean`.

**Axiom-clean (verified by `#print axioms`, not just claimed):** `disjoint_collarPlus_collarMinus`,
`exists_collar_disjoint`, `isPreconnected_collarPlus` each report exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. The flipped collar chain is sorry-clean; the
lone remaining `sorry` lives only in the downstream cover.

**What changed:**
- `collarPlus`/`collarMinus`/`collarChainPlus`/`collarChainMinus` (+ `iUnion_collarChain*`, `isOpen_collar*`)
  now use `sectorPlusClipped β δ₀ α`/`sectorMinusClipped β δ₀ α` instead of the unclipped union sectors.
- Master `disjoint_collarPlus_collarMinus` grew by 5 hyps (`r`/`hconf`/`hLr`/`hballSrc`/`hballTgt`); its
  sector-touching branches route into the proven clipped aggregators (sector×sector, cap×sector) and into
  the proven *unclipped* band×sector leaves via the `sectorClipped_subset_sector` bridge + `Disjoint.mono`.
- `exists_corner_delta` now **exposes `r` in its `∃`** and appends the confinement + two Lipschitz conjuncts
  (E/F/G, all already proven internally); `exists_collar_disjoint` `choose`s `rfun`, extends the `M5` min
  with `α/L_firstSeg`, `α/L_lastSeg`, and supplies the master's new hyps. No new geometry.
- `isPreconnected_collar{Plus,Minus}` and `isPreconnected_collarChain{Plus,Minus}` gained `(hα)(hα1)` and
  use `isPreconnected_sectorPlusClipped`/`Minus`.

**OPEN-ISSUE resolution (the §13 window-gap).** Rather than bridge `foot ∈ (1-a/2, 1]` inside the wrapper,
the sliver wrappers `isPreconnected_collar{Plus,Minus}_of_sliver_budgets` now take the clipped sector
ground-containment as a **direct hypothesis**
`hsectorW : ∀ i hi1, sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier` (plus `hα1 : α < 1`).
The window/confinement obligation is therefore discharged **at the call site** (the ST/Target-1 consumer)
via the proven `sectorPlusClipped_subset_taperedTube_diff_carrier` — the natural home for the concrete
geometry. This is the binding constraint the downstream map independently flagged; the direct-hyp design
sidesteps it cleanly. The band keeps its original `hSband`/`hRband` (`Icc(a/2)(1-a/2)`), unchanged.

**Retired (deleted, zero live references):** `mem_sectorPlus_or_sectorMinus_of_ball`;
`disjoint_sectorPlus_sectorMinus_all`; the 4 unclipped sector↔cap aggregators; `sector{Plus,Minus}_subset_taperedTube`
(the false/sorried tube lemmas); `sector{Plus,Minus}_subset_compl_carrier` (unclipped, replaced by clipped);
`sector{Plus,Minus}_subset_taperedTube_diff_carrier` + the 2 dead `..._of_sliver_budgets` bridge lemmas. The
4 `sector*_subset_collar*` bridge lemmas were flipped to clipped (still live).

**Next:** post-flip Target-1 phase — see `ws:target1-map`. The remaining cover `sorry` (~3140) and the
downstream `exists_twoSidedPartition_of_polyArc` packaging + `dartSectorPoint` + EC instantiation are the
path to discharging the two ST cotree-theorem sorries.
