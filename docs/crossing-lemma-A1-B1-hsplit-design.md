# Node A1 — B1 (`hsplit`) construction design for the straight-line drawing

Scope: a Lean-targeted construction design for the extractor obligation **B1 =
`hsplit`** of
`DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq`
(`ResidualMapProperties.lean:5785`, `hsplit` at lines 5813–5867), for the
straight-line / PL drawing only. Every file:line and lemma name below was read
against the worktree source; the verdicts are classified PROVEN / EMPIRICALLY
VERIFIED / CONJECTURED / HEURISTIC. The conclusion that matters is in §6.

This builds on `docs/crossing-lemma-A1-edmonds-sameregion.md` (the A1 structure)
and corrects two framings in it (§3 and §7) that the source does not support.

> **CORRECTION (2026-06-22), see `docs/crossing-lemma-A1-N1-dartsectorpoint.md`.**
> A follow-up prover pass (validated against source) found two errors in §5/§8/§9
> below, both PROVEN:
> 1. **The N1a target object `convexSector a p b ∩ Metric.ball p ε` is the wrong
>    shape (REFUTED).** `convexSector` is the `< π` convex cone (`PolygonalArc.lean:198`,
>    intersection of two half-planes through the apex). It is **∅** for a
>    collinear apex — a degree-2 collinear vertex, i.e. an interior point of a
>    single line, which is the Szemerédi–Trotter main case — and it selects the
>    **wrong** wedge (containing other incident rays, so `q ∈ arcUnion`) whenever
>    the cyclic-successor angular gap exceeds π. No `IsCorner` side condition
>    repairs it. The correct, downstream-sufficient object is the **`angleAt`-interval
>    wedge** (N1a′ in the follow-up doc), still mathlib-v4.30-constructible (no
>    Jordan), but it needs a new thin `angleAt`/`Complex.arg`-interval API.
> 2. **`hgeo` has TWO open geometric nodes, not one (§8's "only genuinely-open
>    node" is wrong).** Besides N1a′ (the arc-free sector point), maintaining the
>    realization invariant `hreal` across the harness step is a SECOND, larger
>    open node — the cross-level Edmonds correspondence (`stepPoolRegion ∘
>    splitClass = regionAt ∘ dartSectorPoint`), requiring a non-`∅` base, cross-level
>    non-cut-face region invariance, and local→global identification of
>    `Wleft/Wright` with sector-point components. It shares only `dartSectorPoint`
>    with N1a′. The §9 "mechanical once N1a is proven" claim is REFUTED.
>
> §1–§4, §6, §7 below stand as written (the reroute around the `:5785` extractor,
> the circularity finding, and the hWne-vs-B1 refutation are all source-confirmed).
> Only the N1a object spec (§5, §8 Node N1, §9) and the node count are corrected.

---

## 0. Definitions and notation (self-contained)

All in `CrossingLemma` namespace unless noted. `Plane := ℝ × ℝ`.

- **`incidentEnds G p`** (`CrossingLemma.lean:351`): `Finset (Fin G.numEdges ×
  Bool)`, the oriented ends `(i,b)` whose anchored endpoint is `p`. `b = false` =
  param-`0` end, `b = true` = param-`1` end.
- **`vertexRotationAtRadius G p α r hinj`** (`CrossingLemma.lean:418`):
  `Equiv.Perm ↥(incidentEnds G p)`, `= rotationOfOrder (LinearOrder.lift'
  (endAngleKey G p α r) hinj)`. `endAngleKey G p α r e = α e r` is the
  first-crossing angle of end `e` on `∂B(p,r)`. `rotationOfOrder L`
  (`CrossingLemma.lean:256`) is the **cyclic successor** in the order `L`
  (`rotationOfOrder_apply_isoFin`, `:262`: sends the `i`-th smallest to the
  `(i+1 mod n)`-th). Under `ArcsRotationRegular`, `arrAngle` equals
  `angleAt p (arc point) = Complex.arg`, so the order is increasing-`arg` =
  **CCW**; the rotation is the CCW angular successor.
- **`vertexRotation G hARR hp`** (`CrossingLemma.lean:576`):
  `vertexRotationAtRadius` at the ARR radius. The residual map's vertex
  permutation is built from these per-vertex rotations.
- **`residualMap G hARR`** (`ResidualMap.lean:104`): `CombinatorialMap (Fin
  G.numEdges × Bool)` with `vertexPerm = (dartSigmaEquiv).symm.permCongr
  (sigmaVertexPerm)` (block-diagonal per-vertex `vertexRotation`), `edgePerm` =
  swap the two ends, **`facePerm = vertexPerm⁻¹ * edgePerm`** (`CombinatorialMap`
  invariant `facePerm = vP⁻¹·eP`, `Basic.lean:70`). A **face** is a `facePerm`
  cycle; `Face_mk d` is the cycle class of dart `d`.
- **`insertedEdgeMap M c₁ c₂`** (`EdgeInsertion.lean:1246`): the inserted-edge
  combinatorial map. `insVertexPerm = swap(M.vertexPerm c₁, dartA) · swap(M.vertexPerm
  c₂, dartB) · (M.vertexPerm ⊕ 1)` (`:1204`) — threads `dartA = Sum.inr 0` right
  after `M.vertexPerm c₁` and `dartB = Sum.inr 1` after `M.vertexPerm c₂` in the
  rotation. `insFacePerm = insVertexPerm⁻¹ · insEdgePerm` (`:1210`).
- **`insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame`** (`EdgeInsertion.lean:1704`):
  `(insertedEdgeMap M c₁ c₂).Face ≃ ({f : M.Face // f ≠ M.Face_mk c₁} ⊕ Fin 2)`.
  Pinned values: `Face_mk (Sum.inl c₁) ↦ Sum.inr 0`
  (`insertedFaceSplitPoolEquiv_mk_inl_left`, `:1751`); `Face_mk (Sum.inl c₂) ↦
  Sum.inr 1` (`_mk_inl_right`, `:1854`); a non-cut old corner `x` (`¬
  M.facePerm.SameCycle x c₁`) ↦ `Sum.inl (M.Face_mk x)` (`_mk_inl_of_not_sameCycle`,
  `:1716`).
- **`prefixEdges m hm`**, **`prefixStepDartEquiv m`** (`ResidualMapProperties.lean:414`):
  the ordered-prefix sub-drawing and the dart relabeling `Fin m × Bool ⊕ (new) ≃
  Fin (m+1) × Bool` for one insertion.
- **`drawingComplementIn (prefixEdges m) R₀`**, **`regionAt (prefixEdges m) R₀ q`**
  (`RegionFaceBridge.lean:97`, `:118`): the open complement `R₀ \ arcUnion` and the
  connected component of it containing `q`.

The full A1 obligation is the per-step producer
`hgeo : CrossingLemma.PerStepCrosscutInput G' start hARRprefix`
(`SzemerediTrotter.lean:4648`, the lone A1-path `sorry` at `:4649`); the recursion
harness `exists_dr_hstepCrosscut` (`EdmondsSameRegion.lean:496`) is sorry-free.

---

## 1. What `hsplit` actually asserts (PROVEN reduction)

### 1.1 The literal statement

`hsplit` (`:5813`–`:5867`) quantifies over the new edge's two endpoints
`p₁,p₂`, takes **two angular antecedents**, and concludes a split-pool equality.
The new edge is the last edge of the longer prefix `(m+1)+1`; its two ends are the
`false`-end at `p₁` and `true`-end at `p₂` (via
`permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv`, `:5477`,
`:5880`).

The two antecedents (`:5836`–`:5859`) are, for each endpoint `pₖ` and the
corner `cₖ ∈ incidentEnds (prefixEdges (m+1)) pₖ`:

```
vertexRotationAtRadius (prefixEdges ((m+1)+1)) pₖ … ((old_equiv … cₖ).1)
  = incident_ends_prefix_step_endpoint_new_dart … pₖ
```

i.e. **`rotation(cₖ) = new_dartₖ`**: the CCW rotation image of `cₖ` (carried into
the longer prefix by `incident_ends_prefix_step_endpoint_old_equiv`,
`CrossingLemma.lean:1108`) is the new dart at `pₖ`. Equivalently `cₖ` is the
**rotation predecessor** of the new dart — the incident arc immediately CW of the
new arc at `pₖ`. (`exists_vertexRotationAtRadius_prefix_step_endpoint_splice`,
`:2484`, produces exactly this `cₖ`; these are the FORCED corners, unique by the
rotation order.)

The conclusion (`:5860`–`:5867`) is

```
insertedFaceSplitPoolEquiv (residualMap (prefixEdges m)) s₁ s₂ hs hsame
    (Face_mk ((prefixStepDartEquiv m).symm c₁.1))
  = insertedFaceSplitPoolEquiv … (Face_mk ((prefixStepDartEquiv m).symm c₂.1))
```

where `s₁,s₂ : Fin m × Bool` and `hsame : facePerm(prefixEdges m).SameCycle s₁ s₂`
are the *previous* step's same-face data, and the `insertedEdgeMap … s₁ s₂` is the
level-`m → m+1` insertion.

### 1.2 The PROVEN reduction to a co-faciality statement

**Proposition 1 (PROVEN).** Under the `hsplit` hypotheses, the conclusion is
*equivalent* to

```
(residualMap (prefixEdges (m+1)) hARR').Face_mk c₁.1
  = (residualMap (prefixEdges (m+1)) hARR').Face_mk c₂.1,
```

i.e. **the two entered corners `c₁` (at `p₁`), `c₂` (at `p₂`) are co-facial in the
residual map of the prefix at level `m+1`.**

*Proof.* This is the already-proven iff
`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq`
(`ResidualMapProperties.lean:844`), instantiated at `x := c₁.1`, `y := c₂.1`. That
lemma states, for the level-`m → m+1` insertion with corners `s₁,s₂`,
`Face_mk x = Face_mk y` (in `prefixEdges (m+1)`) ↔ the two
`insertedFaceSplitPoolEquiv … (Face_mk (symm x/y))` agree. It `simpa`s from
`residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq` (`:785`) and is
sorry-free. The right-hand side of that iff is *verbatim* the `hsplit` conclusion.
∎

This is exactly how the next layer down consumes it: in
`exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_current_splitPool_eq`
(`:4594`, sorry-free body), line `:4694`–`:4698` derives
`hsame' : facePerm(prefixEdges (m+1)).SameCycle c₁.1 c₂.1` from
`hsplit c₁ c₂ hc hpred₁ hpred₂` via this iff and `Quotient.eq''.mp`. So **B1 ≡
"the entered corners are co-facial in the level-`m+1` (PRE-crosscut) map."**

The new edge is edge `m+1` (0-indexed), *added* at the `m+1 → m+2` step. In
`prefixEdges (m+1)` it is **not yet present**; `p₁,p₂` are existing vertices, and
the entered corners border the single face the new arc is *about to* crosscut.

### 1.3 The naive "same split side" framing is a sign-flip trap — neither plainly
true nor plainly false without the convention

The level-`m+1` `facePerm = vertexPerm⁻¹·edgePerm` convention determines *which
dart label* names the wrap-around face. Two scratch models (EMPIRICALLY VERIFIED;
scope below) bracket the situation:

- **EMPIRICALLY VERIFIED (20000 random *abstract* finite combinatorial maps with
  the repo's exact `insVertexPerm = swap(σc₁,A)·swap(σc₂,B)·(σ⊕1)`):** post-insertion
  co-faciality of the two new darts `A,B` (and of the predecessor corners `c₁,c₂`)
  holds **iff `c₁,c₂` are NOT co-facial in the base map** — the face split/merge
  dichotomy. Buckets: `(pre¬cofacial → post cofacial) 9939`, `(pre cofacial →
  post ¬cofacial) 10061`, exhaustive.
- **EMPIRICALLY VERIFIED (3000 honest *planar* convex-polygon + chord configs):**
  for a chord that *splits* one face (the cotree situation, where `hsame` for the
  predecessor holds), in the **POST-chord** map the rotation-predecessor entered
  corners `c₁,c₂` are co-facial in **0/3000**; their reverses `eP c₁, eP c₂` are
  co-facial in **3000/3000**. In the **PRE-chord** map (the level the iff actually
  asks about) the entered corners `c₁,c₂` are co-facial in **3000/3000**.

Reading: under the literal CCW-predecessor identification, the geometrically
co-facial pair in the POST-chord map is the *reverse* darts, not `c₁,c₂`; but B1
asks about the PRE-chord (level `m+1`) map, where `c₁,c₂` ARE co-facial. Because
the harness around `hsplit` compiles sorry-free and the iff (Prop 1) is proven,
**`hsplit` is a satisfiable, TRUE statement** — its conclusion is the
combinatorially-consistent name, in the level-`m`-insertion split-pool, of "the
two entered corners share the level-`m+1` face." The doc §3 phrase "the two
entered sectors land on the same split *side*" is therefore misleading: the
content is *co-faciality in the pre-crosscut map*, i.e. **"same region before,"**
not a same-half-plane fact. (The first geometric scratch model — "same side of
line `p₁p₂`" — gave OPPOSITE sides in 20000/20000, confirming the half-plane
reading is the wrong object.)

*Scope caveat.* All four scratch runs are EMPIRICALLY VERIFIED on finite random
samples (seeds fixed; `atan2`/`Complex.arg` agree on CCW order). They establish
the *shape* of the true statement and that B1 is satisfiable; they are **not** a
proof of B1 and do not promote any claim to PROVEN.

---

## 2. The geometric content of B1, located precisely

By §1, B1 = co-faciality of the two entered corners in `prefixEdges (m+1)`. The
honest geometric statement is recorded in the repo plan (`region-face-bridge-plan.md`
§3, handle `8S659N`):

> in the partial drawing `prefixEdges (m+1)`, the new arc connects `p₁` to `p₂`
> within a single complement component — both entered corners lie on the boundary
> of the **same** region (the one the new arc is about to crosscut).

The route from this geometric fact to the combinatorial `Face_mk c₁ = Face_mk c₂`
is the **forward Edmonds direction**
`facePerm_sameCycle_of_sameRegion` (`RegionFaceBridge.lean:273`): given an
`EdmondsCompatible (prefixEdges (m+1)) hARR' R₀` assignment `E` and
`E.dartRegion c₁ = E.dartRegion c₂`, conclude `facePerm.SameCycle c₁ c₂`. This is
**not** an unconditional theorem; it is the `region_separates` clause of
`EdmondsCompatible` (`:166`), which must be *built*.

So B1, in region form, is the conjunction:

1. **(geometric)** both entered corners face the *same* complement-region of
   `prefixEdges (m+1)` (`E.dartRegion c₁ = E.dartRegion c₂`); and
2. **(structural)** an `EdmondsCompatible (prefixEdges (m+1)) hARR' R₀` exists.

---

## 3. The circularity obstruction: why B1 cannot be discharged at the level where
`hgeo` needs it

This is the load-bearing structural finding; it determines the route.

**Proposition 2 (PROVEN, by reading the harness).** The recursion harness
`exists_dr_hstepCrosscut` (`EdmondsSameRegion.lean:496`) invokes the per-step
producer `hgeo` at index `m` with **only** the level-`m` invariants `hconst m`,
`hsep m` in scope (`:554`–`:556`):

```
obtain ⟨⟨drm1, data⟩⟩ := hgeo m hm' hstartm (dr m …)
  (fun … => hconst m … d₁ d₂ h)         -- level m
  (fun … => hsep   m … d₁ d₂ h)         -- level m
```

The successor separation `hsep (m+1)` is produced **after** `data`, at `:599`–`:602`,
via `region_separates_prefixStep_sameFace_concrete` consuming `data.poolRegion`,
`data.hinj`. ∎

Consequence: `hgeo` at step `m` **cannot** use the level-`(m+1)` Edmonds direction
(`hsep (m+1)` / `EdmondsCompatible (prefixEdges (m+1))`); it does not exist yet,
and assuming it would be circular. Therefore the §2-route-(2)
(`EdmondsCompatible` at level `m+1`) is **unavailable** to discharge the deeper
extractor's `hsplit` from inside `hgeo`.

**This is the precise point at which the previous (prover) agent stopped, and it
is a genuine ordering obstruction, not a missing-lemma gap.**

---

## 4. The resolution: the deeper extractor's `hsplit` is NOT on `hgeo`'s critical
path

The doc (`crossing-lemma-A1-edmonds-sameregion.md` §4 item 1, §7 item 1) asserts
`hgeo` "extracts `c₁,c₂,hc,hsame,hvertex` from the SameFaceData extractor — this
consumes B1 `hsplit`." Reading the assembler signatures shows this is **stronger
than necessary**, and the genuine residual is different.

**Proposition 3 (PROVEN, by reading the assembler signatures).** The bundle the
harness consumes is built by `nonempty_prefixStepCrosscut_of_data`
(`EdmondsSameRegion.lean:380`) / `mkPrefixStepCrosscutData` (`:334`). Their inputs
are exactly:

`c₁,c₂ : Fin m × Bool`, `hc`, `hsame : facePerm(prefixEdges m).SameCycle c₁ c₂`,
`hvertex` (the vertex-perm splice identity at level `m → m+1`),
`hregion : drm c₁ = drm c₂`, and `Wleft,Wright,hWne,hWold`.

None of these is the deeper extractor's level-`m+1` `hsplit`. In particular:

- **`hsame` is FREE**: the harness itself derives it at `:563`–`:565` as
  `hsep m c₁ c₂ data.hregion` — the level-`m` Edmonds direction applied to
  `hregion`. (So `hgeo` need not even supply `hsame` independently; it is implied
  by `hregion` + the in-scope `hsep m`.)
- **`hvertex`** is available from
  `exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`
  (`ResidualMapProperties.lean:4326`): given the new edge's endpoint incidence
  (`hold₁,hold₂` — the cotree edge's two endpoints are old vertices) and
  `ArcsJoinEndpoints`, it returns the FORCED corners `c₁,c₂`, `hc`, the angular
  identities `hpred₁,hpred₂`, **and** a conditional
  `(facePerm.SameCycle c₁ c₂ → ResidualMapPrefixStepInsertion … m …)` (`:4360`).
  The `.sameFace` constructor of `ResidualMapPrefixStepInsertion` carries the
  `hvertex` field. Feeding `hsame` (= the SameCycle, from `hsep m` + `hregion`)
  into the conditional yields `hvertex`. **This lemma is sorry-free.**

Hence **`hgeo`'s genuine residual content is exactly `hregion` and `hWne/hWold`**
— both at level `m` — and the SameFaceData extractor of `:5785` (with its
level-`m+1` `hsplit`) is *not* required on this path. The doc's "extract via the
extractor" framing conflates the available `_of_old_endpoint_incident` lemma with
the deeper `_of_..._splitPool_eq` extractor.

(If one *does* route through the deeper extractor — the doc's stated plan — its
`hsplit` is exactly the circular level-`m+1` co-faciality of §3 and bottoms out at
the same geometric residual as `hregion` below, so nothing is gained.)

---

## 5. The single irreducible residual: `dr m c = regionAt … (sector point of c)`

Both genuine residuals (`hregion`, and the `hWne/hWold` separation) bottom out at
**one** missing geometric identification.

### 5.1 `hregion` via `prefixStepSameRegion` needs `dr m = regionAt ∘ sector point`

The B2 transport `prefixStepSameRegion` (`EdmondsSameRegion.lean:186`, sorry-free)
concludes `drm c₁ = drm c₂` from:

```
(hq₁) drm c₁ = regionAt (prefixEdges m) R₀ q₁
(hq₂) drm c₂ = regionAt (prefixEdges m) R₀ q₂
(S, hS : IsPreconnected S, hSsub : S ⊆ drawingComplementIn (prefixEdges m) R₀,
 q₁ ∈ S, q₂ ∈ S)
```

The preconnected witness `S` (open arc interior + two corner collars) and its
complement-containment are the "easy" geometric half (the arc is inserted last, so
its open interior avoids `arcUnion (prefixEdges m)`; PROVEN-on-paper, see
`crossing-lemma-A1-edmonds-sameregion.md` §B2). The **hard** hypotheses are
`hq₁,hq₂`:

> the recursion's region family `dr m` **at the splice corner `cₖ`** equals the
> *geometric* region `regionAt (prefixEdges m) R₀ qₖ` at a plane sector point `qₖ`.

But the recursion **defines** `dr m` (= `drm1` of the previous step) as
`stepRegionFamily G drm hconst c₁ c₂ hc hsame Wleft Wright`
(`EdmondsSameRegion.lean:314`), i.e.

```
dr m d = stepPoolRegion … (insertedFaceSplitPoolEquiv … (Face_mk (symm d))),
```

a **combinatorial split-pool realization**. The recursion maintains only `hconst`
(`facePerm`-constancy) and `hsep` (region-separation) of `dr m` *abstractly*; it
**never** proves `dr m = regionAt ∘ (geometric sector point)`. So `hqₖ` is **not**
derivable from the recursion's invariants. It requires a fresh object:

> **`dartSectorPoint`** — from a vertex `v` and the first-crossing directions of a
> dart `d` and of its `vertexRotation`-successor, produce a plane point in
> `convexSector a v b ∩ Metric.ball v ε` (the angular wedge the face occupies),
> together with the membership lemma
> `dartSectorPoint ∈ drawingComplementIn (prefixEdges m) R₀`
> (ARR first-crossing + finitely many arcs ⇒ a small wedge off `v` misses
> `arcUnion`), and the realization `dr m d = regionAt (prefixEdges m) R₀
> (dartSectorPoint …)`.

This object is **absent**. The PL angular wedge machinery it would build on
*does* exist and is the right shape — `convexSector a v b`
(`PolygonalArc.lean:198`, open, convex, preconnected, nonempty for `IsCorner`),
`vertexPlus/vertexMinus` (`:2391/:2395`), `sectorPlus/Minus`
(`:2849/:2856`), with the sector→collar containments
`sectorPlus_subset_collarPlus_of_subset_ground` (`:11071`) — but **no bridge from
a `DrawnMultigraph`'s `G.arc e` / `vertexRotation` to this PL wedge** is present.
`DartSectorPoint.lean`'s header (2026-06-16) records that an earlier
`dart → sector-point` map was **removed**, with the stated reason "the
`Classical.choose` region map cannot satisfy `PrefixStepCrosscutData.hinj`/
`hfactor`." That objection is about a *freely chosen* region family; it does
**not** apply to a *forced* identification `dr m = regionAt ∘ dartSectorPoint`,
which is still needed and still missing.

### 5.2 `hWne/hWold` need the same identification

`hWne : Wleft ≠ Wright` and `hWold : oldFaceRegion ≠ Wleft, ≠ Wright`
(`prefixStepSameRegion_poolRegion_injective`, `EdmondsSameRegion.lean:217`) are
about *global successor* regions: `Wleft = regionAt (prefixEdges (m+1)) R₀ u`,
`Wright = regionAt … v` for `u ∈ U`, `v ∈ V` of the two-sided partition. The
*local* separation `IsTwoSidedPartition (regionMinusArc R β) U V` from
`exists_twoSidedPartition_prefixStep` (`PLCollarSeparation.lean:879`,
**PROVEN sorry-free**, region = `Metric.ball`, confirmed below) certifies the two
sides are distinct *inside the tube*. Promoting that to distinct *global*
components, and excluding the old regions, again needs each region to be named as
`regionAt … (a sector point)` and the sector points to lie in distinct global
components — i.e. the same `dartSectorPoint`-style identification (now at level
`m+1`), plus the local→global propagation. This is a *separate* fact from B1's
co-faciality (`hWne` is a **distinctness** = split, B1 is a **co-faciality** =
shared-before), so closing B1 does **not** automatically give `hWne` (see §7).

### 5.3 The PL collar layer is sorry-free for what it covers — but it does not
cover the identification

EMPIRICALLY (memory `38R2S1`/`G2GJCE`, 2026-06-17/18, "kernel-checked
`[propext, Classical.choice, Quot.sound]`") and per `crossing-lemma-route-fork.md`:
`exists_twoSidedPartition_prefixStep` (`PLCollarSeparation.lean:879`) and
`exists_twoSidedPartition_of_straightArc` (`:480`) are **PROVEN sorry-free** for
the straight single-segment arc. The remaining `sorry`s in the PL layer
(`PlaneArcSeparation.lean:385` `exists_twoSidedPartition_of_arc`,
`PolygonalArc.lean:3148` interior-vertex disk branch) are in the **curved/multi-segment**
branch, which is out of scope. **CONJECTURED (not independently re-verified here):**
the specific straight path is sorry-free; this rests on the cited memory claim and
the route-fork doc, not on a build I can run. A `lake`/`#print axioms` check is the
only way to certify it (FLAG below).

---

## 6. The load-bearing answer

> **Does the straight-line / PL B1 route entirely through the existing sorry-free
> PL collar layer, or does it require arc-separation infrastructure that mathlib
> v4.30 lacks?**

**Verdict (PROVEN by source-reading for the structural half; CONJECTURED for the
mathlib-coverage half):**

1. **B1 does NOT route entirely through the existing PL collar layer.** The
   collar layer (`exists_twoSidedPartition_prefixStep` et al.) supplies the
   **separation** datum (`IsTwoSidedPartition`, the `hWne` raw material). It does
   **not** supply the **identification** `dr m c = regionAt (prefixEdges m) R₀
   (dartSectorPoint c)` that B1 (via `hregion`/`prefixStepSameRegion`) and
   `hWne/hWold` both require. That identification — the `dartSectorPoint` object
   plus its `drawingComplementIn` membership and its `dr m`-realization — is the
   single irreducible residual, and it is **absent from the repo** (and was
   previously removed). It is genuine PL/angular geometry, **not** combinatorial
   plumbing.

2. **This residual does NOT need anything mathlib v4.30 lacks.** It is *not* a
   Jordan/Schoenflies statement. `dartSectorPoint` is built from mathlib-available
   pieces already present in the repo's PL layer: `convexSector` (sign conditions
   on `sideForm` cross-products, open/convex/preconnected — all proven),
   `Metric.ball`, ARR's first-crossing data (`arrAngle_firstCrossing`,
   `CrossingLemma.lean:469`), and finiteness of `arcUnion` (`exists_point_in_complement`,
   `DartSectorPoint.lean:106`, already proves compactness/boundedness of
   `arcUnion`). The membership `dartSectorPoint ∈ drawingComplementIn` is a
   small-wedge-off-vertex argument (finitely many arcs, each leaving a
   neighborhood of `v` along a definite first-crossing direction) — within
   mathlib v4.30's metric/topology API. The genuinely Jordan-strength fact (the
   (MS) two-sided partition for the straight arc) is **already discharged**
   sorry-free in the PL layer; B1 does not re-invoke it.

3. **Therefore the previous agent's stop point (§3 circularity) is real but
   side-steppable**: by §4, `hgeo` does not need the level-`m+1` extractor `hsplit`
   at all; it needs `hregion` and `hWne/hWold` at level `m`, both of which reduce
   to constructing `dartSectorPoint` (§5). The blocked design is unblocked by
   building that one object rather than by finding new mathlib infrastructure.

In one line: **B1 (and the rest of `hgeo`) bottoms out at one missing PL object —
`dartSectorPoint` with its complement-membership and `dr = regionAt` realization —
which mathlib v4.30 fully supports but the repo has not built; it is not blocked
on any absent Jordan/Schoenflies/germ statement.**

---

## 7. Does closing B1 also yield `hWne`/`hWold`? (refute the doc §3 conjecture)

The doc (`crossing-lemma-A1-edmonds-sameregion.md` §3, §B2) conjectures B1 (`hsplit`)
and the region-form global-side distinctness `hWne`/`hWold` are "two faces of the
same fact" via the proven split-pool equiv, so that closing one yields the other.

**Verdict: REFUTE (with sketch).** They are *complementary*, not *equal*:

- **B1 = co-faciality** of the two entered corners in the **PRE-crosscut** map
  `prefixEdges (m+1)` (§1.2): `Face_mk c₁ = Face_mk c₂`. Region form: both entered
  corners face the *same* region *before* the arc.
- **`hWne` = distinctness** of the two new sides *after* the arc:
  `Wleft ≠ Wright`, `Wleft/Wright = regionAt (prefixEdges (m+1)) R₀ (u/v)` for the
  two `IsTwoSidedPartition` sides — a *split* statement.

The proven iff `..._current_face_eq_iff_splitPool_eq` (Prop 1) converts *between*
co-faciality and split-pool *equality*; it does **not** convert a co-faciality
(equality) into a *distinctness* (inequality). Concretely: B1 gives
`splitPoolEquiv(Face_mk(symm c₁)) = splitPoolEquiv(Face_mk(symm c₂))` (both entered
corners on one *combinatorial* side); the pinned values
`insertedFaceSplitPoolEquiv_mk_inl_left/right` give that the *predecessor* corners
`s₁,s₂` are on `Sum.inr 0` vs `Sum.inr 1` (opposite sides). Neither yields
`Wleft ≠ Wright` as *plane regions* — that is the local→global propagation of the
`IsTwoSidedPartition` (a genuinely separate geometric input). The empirical models
(§1.3) make the split/co-faciality duality precise but also show co-faciality
(same-before) and side-distinctness (split-after) are logically independent facts.

What B1 and `hWne` **share** is the *upstream* object `dartSectorPoint` (§5): both
need it (B1 to name the shared pre-region via `hregion`; `hWne` to name `Wleft,
Wright` and place `u,v` in distinct components). So closing B1 *develops the
machinery* that `hWne` also uses, but does **not** *imply* `hWne`. The doc's "same
fact" claim is HEURISTIC and, taken literally (equality ⇒ inequality), false.

---

## 8. Named sub-lemma DAG for the math-prover (hardest node first)

All nodes target the straight-line drawing only. `M = prefixEdges m`,
`M' = prefixEdges (m+1)`. The hardest node is the one missing object; everything
above it is sorry-free transport already in the repo.

**Node N1 (`dartSectorPoint` + its two properties).** ⚠ **The `convexSector` target
below is REFUTED — see the 2026-06-22 CORRECTION banner and
`docs/crossing-lemma-A1-N1-dartsectorpoint.md`. Use the `angleAt`-interval wedge
(N1a′) instead. N1 is NOT the only open node: the `hreal` realization (Node N5
below) is a second, larger one.**
Define `dartSectorPoint G hARR hp d : Plane` for a dart `d ∈ incidentEnds (prefixEdges k) p`:
the apex `p`, with `a,b` the first-crossing points (at ARR radius) of `d` and of
its `vertexRotation`-successor; take a point of
~~`convexSector a p b ∩ Metric.ball p ε`~~ → the `angleAt`-interval wedge
`{z ∈ ball p ε | (angleAt p z − α d) mod 2π ∈ (0, (α succ − α d) mod 2π)} \ arcUnion`
for small `ε ≤ arrRadius` (whole punctured ball when the vertex has one incident
end). Prove:
- **N1a (membership).** `dartSectorPoint … ∈ drawingComplementIn (prefixEdges k) R₀`.
  Sketch: each of the finitely many arcs of `prefixEdges k` incident to `p` leaves
  `B(p,ε)` along its first-crossing direction (ARR clause (a),
  `arrAngle_firstCrossing`); a wedge strictly between two consecutive first-crossing
  directions, intersected with a small `ε`-ball, meets no arc (the consecutive
  directions bound the angular gap; the non-incident arcs are bounded away from `p`
  by compactness, `exists_point_in_complement`'s boundedness argument).
  For the `convexSector` target this is REFUTED (the object is ∅ / wrong-side); for
  the corrected `angleAt`-wedge target (N1a′) it is PROVEN-on-paper and
  mathlib-constructible (the `angleAt`/`Complex.arg`-interval API is thin and must be
  built; metric + δ-separation via `infDist`; no Jordan). See
  `docs/crossing-lemma-A1-N1-dartsectorpoint.md` §2–§3.
- **N1b (realization).** For the *forced* region family `dr` of the recursion,
  `dr k d = regionAt (prefixEdges k) R₀ (dartSectorPoint … d)`. This is the
  identification that ties the combinatorial `stepRegionFamily` to geometry. It must
  be proved *as an added invariant of the recursion* (carry it alongside `hconst`,
  `hsep`), with base case the single-face prefix (`dr = ∅` is degenerate — see
  caveat) and step case the split-pool compatibility (`face_constant` ⇒ a `facePerm`
  step keeps the sector point in one region). **This changes the recursion's carried
  data**; see §9. PROVEN-on-paper for the step; the base case needs the region
  family to be a genuine `regionAt` not `∅` (the current `dr := ∅` base is a
  placeholder that N1b would replace).

**Node N2 (depends on N1). `hregion : dr m c₁ = dr m c₂` for the entered corners.**
From N1b at level `m`: `dr m cₖ = regionAt M R₀ (dartSectorPoint cₖ)`. Build the
preconnected `S` = (open new-arc interior) ∪ (collar segment at `q₁`) ∪ (collar at
`q₂`), `qₖ = dartSectorPoint cₖ`; `S ⊆ drawingComplementIn M R₀` (the new arc is
edge `m`, inserted last, so its open interior avoids `arcUnion M` — the disjointness
is the only nontrivial input). Apply `prefixStepSameRegion` (`:186`, sorry-free).
PROVEN-on-paper given N1.

**Node N3 (depends on N1, parallel to N2). `Wleft,Wright,hWne,hWold`.**
Take `(R,U,V)` from `exists_twoSidedPartition_prefixStep p₁ p₂ hne`
(`:879`, PROVEN sorry-free). Set `Wleft = regionAt M' R₀ u`, `Wright = regionAt M'
R₀ v` for chosen `u ∈ U`, `v ∈ V`. `hWne`: the local separation `U,V` (open,
disjoint, in `regionMinusArc R β`) propagates to distinct *global* components of
`drawingComplementIn M' R₀` — the local→global step (the simply-connected tube
`R` forces the two `regionMinusArc` sides into different ambient components once
the arc is present). `hWold`: each old region is `regionAt M' R₀ (dartSectorPoint
…)` (N1b at level `m+1`) and is disjoint from `Wleft,Wright` (an old face's sector
point is bounded away from the new tube). PROVEN-on-paper given N1; the local→global
propagation is the residual analytic content (uses `IsSimplyConnected R` =
`convex_ball`).

**Node N4 (sorry-free assembly — already exists). Build the bundle, discharge `hgeo`.**
With N2 (`hregion`), `hsame := hsep m c₁ c₂ hregion`, `hvertex` from
`exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`
(`:4326`) + `hsame`, and N3 (`Wleft,Wright,hWne,hWold`), call
`nonempty_prefixStepCrosscut_of_data` (`:380`). This is sorry-free assembly. The
`SzemerediTrotter.lean:4649` `sorry` closes. (If one prefers the doc's
deeper-extractor route, N4 instead feeds N2/N3 into the `:5785` extractor whose
`hsplit` is discharged by Prop 1 applied to N2 at level `m+1` — but that re-introduces
the §3 circularity and is strictly harder; **prefer the `_of_old_endpoint_incident`
route**.)

Dependency order: **N1 → {N2, N3} → N4**. N1 is the only node needing new
mathematics; N2,N3 are PROVEN-on-paper transport given N1; N4 is existing
sorry-free code.

---

## 9. Caveat that the prover must confront before N1b

The current recursion carries `dr := ∅` at the base and `stepRegionFamily ∘
splitClass` at the step, with `hconst`/`hsep` as the *only* invariants. **N1b
(`dr = regionAt ∘ dartSectorPoint`) is not a free add-on**: it requires the base
region family to be a genuine geometric assignment (a single-face prefix has one
complement-region; `dr := the unbounded region` or `regionAt … (any complement
point)`, not `∅`), and the step to *preserve* the realization through the
split-pool. This means N1 changes `exists_dr_hstepCrosscut`'s carried `Σ'` (adds a
third invariant `hreal k : ∀ d, dr k d = regionAt (prefixEdges k) R₀
(dartSectorPoint … d)`), which is a non-trivial edit to the otherwise-frozen
sorry-free harness. The edit is mechanical *once* N1a (membership) is proven; N1a
is the irreducible mathematical content.

**FLAG FOR IMPLEMENTER:** N1b requires modifying `exists_dr_hstepCrosscut`
(`EdmondsSameRegion.lean:496`) to carry a geometric-realization invariant `hreal`
alongside `hconst`/`hsep`, and replacing the `dr := ∅` base with a genuine
`regionAt` assignment. Re-`#print axioms` the harness after the edit to confirm it
stays `[propext, Classical.choice, Quot.sound]`.

**FLAG FOR IMPLEMENTER:** certify the straight-arc PL path is sorry-free by
`#print axioms exists_twoSidedPartition_prefixStep` and
`exists_twoSidedPartition_of_straightArc` (expect `[propext, Classical.choice,
Quot.sound]`); §5.3's sorry-free claim for these is CONJECTURED from memory
`38R2S1`/`G2GJCE`, not from a build run here.

**FLAG FOR IMPLEMENTER (spec for N1a, the one new lemma):**
Compute/prove: for `G` a `DrawnMultigraph`, `hARR : ArcsRotationRegular G`,
`p ∈ G.V`, dart `d ∈ incidentEnds G p`, there is `ε > 0` and a point
`q ∈ convexSector a p b ∩ Metric.ball p ε` with `q ∉ arcUnion G`, where `a,b` are
the first-crossing points of `d` and `vertexRotation`-successor of `d` at radius
`ε`. Inputs: the ARR first-crossing data (`arrAngle_firstCrossing`,
`CrossingLemma.lean:469`), `convexSector` API (`PolygonalArc.lean:198`–`244`),
compactness of `arcUnion` (`DartSectorPoint.lean:106`). Output: the point `q`
(noncomputable witness) + membership proof. This is the irreducible geometric
residual of all of B1/B2 for the straight-line drawing.

---

## 10. Summary table (evidence levels)

| Claim | Level | Basis |
|---|---|---|
| B1 (`hsplit`) ≡ co-faciality of entered corners in `prefixEdges (m+1)` | **PROVEN** | iff `…_current_face_eq_iff_splitPool_eq` (`RM:844`), source-read |
| `hsplit` is a TRUE/satisfiable statement | **PROVEN** | harness around it compiles sorry-free; iff proven |
| "same split *side*"/half-plane framing is the wrong object | **EMPIRICALLY VERIFIED** | 20000 abstract + 3000 planar scratch configs |
| `hgeo` does not need the deeper `:5785` extractor `hsplit` | **PROVEN** | assembler signatures `:334`/`:380`, `_of_old_endpoint_incident` `:4326`, source-read |
| `hsame` is free from `hsep m` + `hregion` | **PROVEN** | harness `:563`–`:565` |
| §3 circularity (no level-`m+1` Edmonds in `hgeo`) | **PROVEN** | harness `:554`–`:556`, `:599`–`:602` |
| Single irreducible residual = `dartSectorPoint` + membership + `dr = regionAt` | **SUPERSEDED** → TWO residuals (N1a′ + `hreal`) | corrected 2026-06-22; `prefixStepSameRegion` `:186` hyps, `dr` def `:314`, `DartSectorPoint.lean` header |
| `convexSector a p b ∩ ball` is the right N1a target object | **REFUTED** | `convexSector` is the `<π` cone (`PolygonalArc.lean:198`/`:233`): ∅ for collinear apex, wrong wedge when gap `>π`; see N1-dartsectorpoint doc §1 |
| `angleAt`-interval wedge (N1a′) needs **no** mathlib-v4.30-absent infra (no Jordan) | **CONJECTURED** | `Complex.arg` API present; thin `angleAt` API + δ-separation, not built; N1-dartsectorpoint doc §3 |
| `hreal` step-maintenance is a SECOND open node (Edmonds bridge), not mechanical | **PROVEN** | `∅` base (`:541`) refutes add-on; `stepPoolRegion∘splitClass` = cross-level Edmonds equality; N1-dartsectorpoint doc §5 |
| `exists_twoSidedPartition_prefixStep` straight path is sorry-free | **CONJECTURED** | memory `38R2S1`/`G2GJCE`, route-fork doc; not build-verified here |
| Closing B1 yields `hWne`/`hWold` ("two faces of one fact") | **REFUTED** | co-faciality (=) vs distinctness (≠) are independent; share only `dartSectorPoint` |
