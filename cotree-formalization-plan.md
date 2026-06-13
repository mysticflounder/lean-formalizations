# Closing the cotree `sorry` in `SzemerediTrotter.lean`

Target: the single remaining `sorry` at
`LeanFormalizations/PachDeZeeuw/PachSharir/SzemerediTrotter.lean` in
`straightLineCanonicalComponentResidualMapPlanarityOfARR`, in the
`hstep` later-cotree branch (`lvertex.length - 1 < m`).

This is a Lean **formalization** task. The mathematics (planar tree/cotree
decomposition: complementary primal/dual spanning trees, dual-map incidence,
reverse leaf-peeling face splitting) is settled and already scaffolded in the
repo. There is no missing *theorem* in the literature to find — only formal
packaging to assemble. Every building-block lemma named below exists.

---

## Location index — START HERE (file:line, as of `d410ea9`)

Line numbers are valid as of commit `d410ea9` (2026-06-12); `ST` and `RM` are
large, actively-edited files, so a number may drift by a few lines. **If a line
is off, do not re-read the file front-to-back — grep the name.** The
declaration keyword (`theorem` / `private theorem` / `def`) sits on the line
*above* the name when the name is long (it wraps):

```
grep -nE "(^|\.)<unqualified-name>\b" <file>        # finds decl + call sites
```

Files:
- `ST` = `LeanFormalizations/PachDeZeeuw/PachSharir/SzemerediTrotter.lean`
- `RM` = `LeanFormalizations/PachDeZeeuw/CrossingLemma/ResidualMapProperties.lean`
- `VG` = `LeanFormalizations/Combinatorics/CombinatorialMap/VertexGraph.lean`

### Target
| What | Location |
|---|---|
| `theorem straightLineCanonicalComponentResidualMapPlanarityOfARR` | `ST:4530` |
| the open `sorry` (later-cotree branch `hgt : lvertex.length - 1 < m`) | `ST:4610` |
| `m = lvertex.length - 1` base case (already closed, mirror for shape) | `ST:4604` |
| `obtain ⟨…, π, hπtree, hπrest⟩` destructure of the position permutation | `ST:4555` |

### The permutation `π` and the selector set `Sₑ`
| What | Location |
|---|---|
| `DrawnMultigraph.exists_treeCotreePositionPermutation_of_graphConnected` (produces `π`) | `RM:9741` |
| cotree-block conjunct of its statement (the placement `hπrest` proves) | `RM:9781`–`9788` |

`Sₑ` (the edge set the cotree block is selected over) is **exactly**:
```
{e | residualMapEdgeEquiv G hARRG e ∉
      Set.range (G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
        parentVertex hparentVertex)}
```
(`RM:9760`–`9762`, repeated `9785`–`9787`). In `ST`, `hTface_sub` /
`hπrest` already use this set — reuse them, do not rebuild it.

### Seed and base (§2)
| What | Location |
|---|---|
| `…_exists_residualMapPrefixStepSameFaceData_of_treePrefix_next` (the SameFaceData seed, `t = 0`) | decl `ST:4308`, called `ST:4454` |
| `…_exists_residualMapPrefixStepInsertion_sameFace_of_treePrefix_next` (Insertion variant used by the `m = a` branch) | decl `ST:4392`, used `ST:4605` |

### Successor wrapper (§3) — the OnEdgeSet entry point
| What | Location |
|---|---|
| `…_exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_choose_splitPool_eq` | decl `ST:4044` |

### The chain the wrapper rides (selector → block → workhorse)
| What | Location |
|---|---|
| `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_current_splitPool_eq` (block lemma) | `RM:6261` |
| `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq` (selector-agnostic workhorse, takes a bare dart) | `RM:6022` |
| `DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block` | `RM:5393` |
| `DrawnMultigraph.permuted_prefix_last_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block` | `RM:5302` |

### `hcoverage` producer (§4.1 — AVAILABLE)
| What | Location |
|---|---|
| `DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le` | `RM:8521` |

### `hchoose` ingredients (§4.2 — the hard core, producer NOT yet written)
| What | Location |
|---|---|
| split-pool eq **from** `hadj`, face-pair form (consumes `hadj`, gives the wrapper's `hchoose` shape) | `RM:1209` |
| split-pool eq **from** `hadj`, plain form | `RM:1033` |
| reverse-prefix label transport (residual layer) | `RM:1089` |
| **the `hadj` hypothesis shape** (read this to know what must be proven) | `RM:1235`–`1243` (inside the `RM:1209` signature) |
| CombinatorialMap-layer label transport | `VG:1871` |
| CombinatorialMap-layer face-pair label eq | `VG:2114` |

### Selectors and structures (definitions)
| What | Location |
|---|---|
| `faceEdgeOfLeafOrderOnEdgeSetReverse` (def) | `VG:1563` |
| `faceEdgeOfLeafOrderReverse` (def) | `VG:1701` |
| `structure ResidualMapPrefixStepSameFaceData` (fields: `c₁ c₂ hc hsame hvertex`) | `RM:1732` |
| `ResidualMapPrefixStepSameFaceData.toInsertion` | `RM:1747` |

---

## 0. Status (2026-06-13, later) — CIRCULARITY FOUND in the cotree-tail approach

**SHIPPED & building (committed `6e13e51`):** two OnEdgeSet siblings via the
proven plain-string transform —
`exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block`
(transform of `RM:7632`) and the **self-contained** cotree step
`…_block_of_treePrefix_incidence` (transform of `RM:9437`). The self-contained
one produces `ResidualMapPrefixStepInsertion (G.permuteEdges π) (a+j.1) …`
directly, discharges coverage internally
(`incidentCoverage_permuted_treePrefix_of_leafOrder_of_le`), and needs **only**
the geometric co-faciality `hface` (`Face_mk c₁ = Face_mk c₂`) — **no
label/hadj/sector** (unlike `RM:7154`). This is the right step lemma to drive
the induction. Both build (8485 jobs).

**BLOCKER (traced, not asserted):** wiring the induction to the `sorry`
(`ST:4610`, branch `lvertex.length-1 < m`) requires mapping each `m ∈ [a+1, E-1]`
to a cotree index `j : Fin (lface.length-1)` via `m = a + j.1`, which needs
`m < a + b`, i.e. (with `hblock : a+b ≤ E`) the **equality**
`a + b = numEdges` where `a = lvertex.length-1`, `b = lface.length-1`. But:
- `a = V_M - 1` (since `residualMapVertexEquivOfIncident : M.Vertex ≃ G.V`),
  `b = F_M - 1` (`lface.length = card M.dual.Vertex`), `E = E_M`
  (`residualMap_edge_card`, `RM:7845`). So
  `a + b = E  ⟺  V_M − E_M + F_M = 2  ⟺  M.IsPlanar` (M is connected:
  `residualMap_connected`). **The needed equality IS the theorem's conclusion.**
- The only lemma giving the dual-minus-tree tree structure that would yield it,
  `faceGraphOnEdgeSet_isTree_of_not_mem_range_vertexLeafOrder` (`VG:1305`),
  **takes `hplanar : M.IsPlanar` as a hypothesis.** So using it here is circular.
- The `_of_prefix_insertions` consumers (`EdgeSetDrawing:797/823`,
  `exists_residualMap_isPlanar_of_prefix_insertions_connected`, `RM:10358`)
  all *assume* `hstep ∀ m∈[1,E-1]` with `CrossingFree G` in scope — none prove
  it. So `CrossingFree` is the intended source of genus-0, but **no lemma in the
  repo turns no-crossing straight-line geometry into genus-0 / `a+b=E`**
  (greps over `NoCrossingPairsInEdgeSet`, `genus`, `IsPlanar` producers).

**CONCLUSION:** the cotree `sorry` cannot be closed by formalization-packaging
of existing lemmas. Closing it requires the genuine remaining theorem:
**no-crossing straight-line drawing ⇒ genus-0 residual map** (equivalently
`a+b=numEdges`, the cotree tail is empty). Candidate home: the
`drawing→genus-0-map bridge` flagged in `CrossingLemma.lean:211` (§4/§6).
{{NEEDS_ADAM_INPUT}} — confirm the intended genus-0 source before building it.

---

## 0. Status (2026-06-13)

**DONE & building (committed `1ee54b5`):** the OnEdgeSet **sector-sideLabels
block-step bridge** `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_sector_sideLabels`
(`RM:7154`). OnEdgeSet sibling of the unrestricted `RM:6924`: reads the
edge / position-pin / face-pair off `faceEdgeOfLeafOrderOnEdgeSetReverse_spec`
(`VG:1577`) and `permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block`
(`RM:5393`), widens the carried containment via `faceGraphOnEdgeSet_le_faceGraph`
(`VG:1012`), forwards to the selector-agnostic face-pair lemma `RM:6395`. Body
is a faithful transform of `RM:6924`'s 4-line proof.

**PARKED (not committed) — ST-layer sideLabels wrapper.** A `stComponentDrawing`
wrapper mirroring `ST:3710` onto the OnEdgeSet selector + `RM:7154` was written
and **diff-verified correct** against the working OnEdgeSet `splitPool_eq`
wrapper — only the heavy sideLabels signature differs. It hits a
**non-terminating `whnf`** at the OnEdgeSet selector application in `hπcotree`
(`…:4088:12`), *identical failure at `maxHeartbeats` 200k / 800k / 3.2M* (so
structural, not budget). Diagnosis: `splitPool_eq`+OnEdgeSet compiles and
`sideLabels`+`faceGraph` (`ST:3710`) compiles, but `sideLabels`+OnEdgeSet
together wedge the elaborator on `faceEdgeOfLeafOrderOnEdgeSetReverse Sₑ … T hTsub`.
Reverted to keep the repo green.

**Next (resumption):** the cotree step does **not** need that ST wrapper — call
the committed `RM:7154` **directly** from the `Nat.le_induction` (`RM:7154`
compiles; the pathology is specific to re-wrapping the selector in
`stComponentDrawing`'s heavy signature). If a wrapper is still wanted, abstract
the selector behind a `let` or feed a bare-dart pin to dodge the signature-level
`whnf`. Genuine remaining content unchanged: the cross-map `label` (full
`residualMap.Face` → prefix split-pool, via the face-merge correspondence) and
its `hadj` invariant (`VG:2114` shape), then the induction.

## 0. Status (2026-06-12)

**DONE & building (committed):** the OnEdgeSet cotree-block plumbing. This
cleared the first hard blocker, described next.

**The blocker that was cleared — selector mismatch.** The tree/cotree position
permutation `π` (from `exists_treeCotreePositionPermutation_of_graphConnected`)
places the cotree block using the **edge-set-restricted** selector
`faceEdgeOfLeafOrderOnEdgeSetReverse {non-tree edges} …`, with the cotree tree
`Tface ≤ faceGraphOnEdgeSet {non-tree edges}`. But every block lemma originally
consumed the **unrestricted** `faceEdgeOfLeafOrderReverse` (with
`T ≤ faceGraph`).

There is **no bridge** `faceEdgeOfLeafOrderOnEdgeSetReverse = faceEdgeOfLeafOrderReverse`
and one cannot exist: `Edge.ends` is many-to-one on dual edges (a 4-cycle's two
faces share all four edges), and the two selectors are independent
`Classical.choose` calls that agree only on the *face pair*, not on edge
identity. So the unrestricted block lemma could **never** be invoked with the
real `π`. (This was a latent mis-statement, now fixed.)

**Fix applied (the workhorse is selector-agnostic).** The deepest workhorse
`exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq`
consumes a *bare dart* `d`, not a selector. So the selector only enters at two
mechanical spots. We:

1. Added `DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block`
   in `ResidualMapProperties.lean` (analog of the unrestricted `_next_` lemma,
   reducing to the already-present OnEdgeSet `_last_` lemma).
2. Retargeted the block lemma
   `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_current_splitPool_eq`
   (was `…faceEdgeOfLeafOrderReverse…`) to the OnEdgeSet selector
   (`Sₑ : Set …Edge`, `T ≤ faceGraphOnEdgeSet Sₑ`, selector in `hπcotree`+`hsplit`).
   The ~660-line internals are untouched.
3. Retargeted the stComponentDrawing wrapper
   `stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_choose_splitPool_eq`
   the same way (edge set named `Sₑ` to avoid the existing `S : Finset (ℝ×ℝ)`).

The whole library builds (only the target `sorry` warning + pre-existing
`simpa` lints remain). This wrapper's `hπcotree` now matches `hπrest` exactly.

---

## 1. Index bookkeeping (unchanged, verified)

```
a := lvertex.length - 1          -- tree block size
b := lface.length  - 1           -- cotree block size  (a + b = numEdges, Euler)
t := m - a                       -- cotree offset; later branch ⇒ 1 ≤ t ≤ b-1

-- to PRODUCE the step at global offset m (SameFaceData at offset m):
i : Fin b := ⟨t - 1, _⟩          -- predecessor edge   (NOT t)
j : Fin b := ⟨t,     _⟩          -- current edge
m = a + i.1 + 1 = a + j.1
hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1     -- holds: both = b - t + 1
```

The OnEdgeSet wrapper produces `ResidualMapPrefixStepSameFaceData … (a+i.1+1)`
= SameFaceData at offset `m`, from predecessor same-face data at offset
`a + i.1 = m - 1`.

---

## 2. The seed (offset `a`, `t = 0`)

Use, as the induction base, the **SameFaceData** tree-prefix lemma (NOT the
Insertion variant the `m = a` branch already uses):

```
stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_treePrefix_next
```

It yields `Nonempty (ResidualMapPrefixStepSameFaceData (G.permuteEdges π) (lvertex.length-1) …)`
— the predecessor data the first successor (`t = 1`, `i.1 = 0`) consumes.

---

## 3. The successor — DECIDED ARCHITECTURE (2026-06-13)

**Key discovery: the step wrapper is selector-agnostic.**
`DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels`
(`RM:6395`, the `Nonempty (…SameFaceData)` sibling of the Insertion-valued
`RM:6660`) does **not** pin to either selector. It takes a bare dart `d`, a
single-edge pin `hπ`, and a **face-pair** hypothesis `hdpair`
(`RM:6694`–`6704`). So the OnEdgeSet π (pinned by `hπrest` to
`faceEdgeOfLeafOrderOnEdgeSetReverse`) feeds it directly — **no new VG/RM
OnEdgeSet analog is needed** (the original concern that we'd have to mirror the
whole `sector_sideLabels` family to OnEdgeSet is void).

`RM:6395` inputs (only the first three are selector-touching; the rest are the
verbatim `ST:3710` template):
- `d`, `hπ : π (castLE hm'' (Fin.last (a+i.1+1))) = residualMapEdgeEquiv G hARRG (Edge_mk d)`;
- `hdpair : s(Face_mk d, Face_mk (edgePerm d)) = s(dualVertexEquivFace (l[rev j +1]), dualVertexEquivFace (parent (rev j +1)))`;
- `hTsub : Tface ≤ (residualMap …).faceGraph` — from `hTface_sub : Tface ≤ faceGraphOnEdgeSet Sₑ`
  composed with `faceGraphOnEdgeSet_le_faceGraph` (`VG:1012`);
- reused verbatim from `ST:3710`: `hadj` (§4.1), `sideLabel, label, hsideLabel,
  hl_nodup, hsector_direct, hsector_swapped, hcoverage`, predecessor SameFaceData
  fields `s₁ s₂ hs hsame hvertex`, indices `i, j, hprefix`, `hARR/hARR'/hARR''`.

(The unrestricted wrapper `ST:3710` / `RM:7142` is unusable: its `hπcotree`
pins π to `faceEdgeOfLeafOrderReverse`, which the real π is **not** — π is
OnEdgeSet. `ST:4044` is OnEdgeSet but consumes the raw splice-form `hchoose`;
routing through the face-pair core `RM:6395` is cleaner.)

---

## 4. The four pieces to write (concrete, bounded — literature formalization)

The combinatorial backbone is already proven
(`TreeOrder.lean:582/618/727`, commit 355a1e4). No missing theorem — four
formalization pieces.

**4.1 — the `hadj` producer (the one substantive lemma).** For the actual
split-pool `label` (`label (Face_mk d) = insertedFaceSplitPoolEquiv … (Sum.inl d)`),
establish the **local** invariant: for dual-tree-adjacent faces `u,v` of the
unpeeled prefix whose shared edge is *not* the split edge inserted at step `i`,
`label (dualVertexEquivFace u) = label (dualVertexEquivFace v)`. This is the
face-splitting fact — inserting one edge splits exactly one face, so the
side-label is constant across every dual adjacency except the split edge.
Built from `insertedFaceSplitPoolEquiv`'s definition + co-faciality (`hsame`).
The **global** propagation across the prefix is already done by
`reverse_leafOrder_prefix_apply_eq_of_forall_adj_ne_current_parent` (`TO:727`)
/ `VG:1871`, which *consume* this local `hadj`; only the local form is new.

**4.2 — `hdpair` for the OnEdgeSet selector.** Prove
`s(Face_mk d, Face_mk (edgePerm d)) = s(dualVertexEquivFace (l[rev j +1]), dualVertexEquivFace (parent …))`
for any dart `d` realizing `faceEdgeOfLeafOrderOnEdgeSetReverse Sₑ Tface … j` (it
picks `faceGraphOnEdgeSetEdge` between `l[rev j +1]` and its parent, whose
`Edge.ends` *is* that face pair). Look for an existing
`faceEdgeOfLeafOrder…_edge_face_pair`-style lemma to reuse; else a short
selector-unfolding lemma. The dart `d` + pin `hπ` come from `Quotient.exists_rep`
on `hπrest`, exactly as `RM:6261` (≈`6368`–`6380`).

**4.3 — ST-layer OnEdgeSet wrapper.** Mirror `ST:3710` with `Sₑ`,
`hTsub : Tface ≤ faceGraphOnEdgeSet Sₑ`, `hπcotree := hπrest`, the
`hchoose_direct/swapped` guards retargeted to the OnEdgeSet selector. Body:
derive `d, hπ` from `hπcotree`; prove `hdpair` (4.2); compose `hTsub` to
`faceGraph` via `VG:1012`; call `RM:6395` with the sector helpers
(`ST:3157/3347`, selector-independent) unchanged.

**4.4 — cotree-offset induction.** `a := lvertex.length-1`, `b := lface.length-1`,
`t := m - a`. `Nat.le_induction` on `t` producing
`Nonempty (ResidualMapPrefixStepSameFaceData (G.permuteEdges π) (a+t) …)`,
carrying `hadj` for prefix `t` in the motive. Base `t=0` = the seed (`ST:4308`).
Step `t→t+1` = the 4.3 wrapper with `i.1=t`, `j.1=t+1`, `hprefix` (verified: both
sides `= b-t`, holds for `1 ≤ t ≤ b-1`). `hcoverage` from
`incidentCoverage_permuted_treePrefix_of_leafOrder_of_le` (`RM:8521`). At the
`sorry` (`ST:4610`): `t := m - a`; `(induction t …).choose.toInsertion`.

---

## 5. Effort

- 4.2 / 4.3 / 4.4: formalization assembly reusing `RM:6395` and the `ST:3710`
  template; index/`Fin.rev` bookkeeping is the main friction.
- 4.1 (`hadj` producer): the one substantive lemma — face-splitting side-label
  constancy from `insertedFaceSplitPoolEquiv` + `hsame`. The focus of the first
  implementation session.

Verification: `./lake-build.sh LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter`,
then `#print axioms straightLineCanonicalComponentResidualMapPlanarityOfARR`
(expect only Lean core axioms; no `sorryAx`).

Verification: `./lake-build.sh LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter`,
then `#print axioms straightLineCanonicalComponentResidualMapPlanarityOfARR`
(expect only Lean core axioms; no `sorryAx`).
