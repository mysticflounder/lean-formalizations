# Node A1 — Edmonds-bridge realization node: feasibility verdict

Scope: the decisive feasibility question for the **larger** of A1's two open
geometric nodes — the *realization / Edmonds-bridge node* that maintains the
invariant

  `hreal k : ∀ d, dr k d = regionAt (prefixEdges k) R₀ (dartSectorPoint k d)`

across one harness step `m → m+1`, i.e. proving

  `stepPoolRegion(splitClass d) = regionAt (prefixEdges (m+1)) R₀ (dartSectorPoint (m+1) d)`

together with a non-`∅` base. The predecessor (the N1-dartsectorpoint doc §5)
established this is a SECOND open node; this task asks whether it is
**constructible from the existing sorry-free straight-arc PL collar layer** or
**requires a Mathlib-v4.30-absent statement**.

Every file:line and lemma name below was read against the worktree source. Claims
are labelled PROVEN / CONSTRUCTIBLE / CONJECTURED / HEURISTIC / EMPIRICALLY
VERIFIED. The load-bearing verdict is in §2; the sub-obligation breakdown is §4–§6.

---

## 0. The headline verdict

> **SPLIT VERDICT — two of three sub-obligations are CONSTRUCTIBLE from the
> existing PL layer; the third (global side-distinctness) is a NAMED OBSTRUCTION
> requiring a planar-separation lemma absent from mathlib v4.30 and from the
> repo's *applicable* lemmas.** Decomposed into the three sub-obligations of the
> N1-doc §5:
>
> 1. **Non-cut-face cross-level region invariance — CONSTRUCTIBLE** from
>    arc-disjointness + mathlib `connectedComponentIn` API. No separation theorem.
>    (§4.)
> 2. **Local→global side identification — SPLITS into an *equality* half and a
>    *distinctness* half:**
>    - the **equality** `Wleft = regionAt … (dartSectorPoint d)` is **CONSTRUCTIBLE**
>      (`regionAt_eq_of_mem_isPreconnected` on a collar segment; §5.5), given N1a′;
>    - the **distinctness** `Wleft ≠ Wright` is the **NAMED OBSTRUCTION** (§5.4).
>      The in-tube `IsTwoSidedPartition` from `exists_twoSidedPartition_prefixStep`
>      gives the two sides *inside the tube `R`*; promoting their distinctness to
>      *distinct components of the global complement* is the *separating* direction.
>      It does **not** reduce to the `sideForm` half-planes (a complement path can
>      cross the supporting **line** off the chord; PROVEN it fails, §5.4) and it
>      does **not** reduce to the in-tube partition (a global component's tube-trace
>      can be disconnected; §5.2). What it needs is the **crosscut-separation
>      theorem for a simply-connected planar domain** (removing a crosscut raises
>      π₀ by one), distinctness half — which mathlib v4.30 lacks and the repo has
>      not built (only the unusable general sorry `exists_twoSidedPartition_of_arc`
>      and the *local* partition exist).
> 3. **Non-`∅` base — CONSTRUCTIBLE** (single-face prefix; face-indexed `dr`;
>    `hconst` via `faceMk_facePerm`; membership from N1a′). No separation theorem.
>    (§6.)
>
> **Therefore: NAMED OBSTRUCTION.** The realization node does **NOT** route
> entirely through the existing sorry-free PL layer. The missing statement is:
>
>   **`crosscut_separates_global` (§5.4):** for the simply-connected tube `R`, the
>   straight chord `β` with endpoints on `∂R`, and the two sides `U,V` of the
>   in-tube partition `R \ β`, no preconnected subset of `drawingComplementIn
>   (prefixEdges (m+1)) R₀` contains a point of `U` and a point of `V`. (The
>   distinctness/≥2-components half of the (MS) crosscut theorem.)
>
> Why mathlib v4.30 lacks it: no plane separation, no π₀-of-complement, no
> Mayer–Vietoris, no Jordan/Schoenflies/Riemann (`PlaneArcSeparation.lean:398–467`,
> verified). It is **strictly weaker** than the general sorry
> `exists_twoSidedPartition_of_arc` (`:382`) — the local partition is already
> built; only the *global distinctness for a straight chord in a ball* remains —
> but "weaker than that sorry" is **not** "constructible from the existing PL
> layer." It is a new planar-separation lemma the repo must build, of the same
> family.

**Scope of what *is* delivered by the PL layer (§2.2):** the in-tube
`IsTwoSidedPartition` (`exists_twoSidedPartition_prefixStep`, sorry-free), the
`sideForm`-side memberships `U ⊆ {sideForm > 0}`, `V ⊆ {sideForm < 0}` (proven),
and the §5.2 point-set facts. These reduce the obstruction to its sharpest form
(distinctness only, straight chord only) but do not discharge it.

---

## 1. Definitions and notation (self-contained, from source)

`Plane := ℝ × ℝ`. Path prefix for source:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/`. All in `CrossingLemma`
namespace unless noted.

- `arcSet G e := Set.range (G.arc e).param` (`RegionFaceBridge.lean:90`); closed
  carrier, includes endpoints.
- `arcUnion G := ⋃ₑ arcSet G e` (`:93`).
- `drawingComplementIn G R₀ := R₀ \ arcUnion G` (`:97`); open when `R₀` open
  (`isOpen_drawingComplementIn`, `:104`, PROVEN, each carrier compact ⇒ closed).
- `regionAt G R₀ p := connectedComponentIn (drawingComplementIn G R₀) p`
  (`:118`); open (`isOpen_regionAt`, `:124`, via
  `IsOpen.connectedComponentIn`, ℝ×ℝ locally connected).
- `regionAt_eq_of_mem_isPreconnected` (`:131`, PROVEN): `S` preconnected,
  `S ⊆ drawingComplementIn`, `p,q ∈ S` ⇒ `regionAt p = regionAt q`. The **only**
  region-equality combinator in the repo. There is **no** `regionAt ≠`
  (distinctness) lemma anywhere (confirmed by grep).
- `prefixEdges m hm` (`ResidualMapProperties.lean:414`): the ordered-prefix
  sub-drawing keeping the first `m` edges; `prefixStepDartEquiv m` the
  `Fin m × Bool ⊕ (new) ≃ Fin (m+1) × Bool` relabel for one insertion.
- `EdmondsCompatible G hARR R₀` (`RegionFaceBridge.lean:166`): the bundled
  predicate. Fields: `dartRegion`, `dartRegion_isComponent`,
  **`face_constant`** (`:174`, the easy half), **`region_separates`** (`:177`,
  the hard Edmonds direction). `facePerm_sameCycle_of_sameRegion` (`:273`) is the
  **structure projection** of `region_separates` — it is **CONDITIONAL on a
  supplied `E`**, not an unconditional theorem.
- `edmondsCompatibleOfCardFaceOne` (`:298`, PROVEN sorry-free): when the residual
  map has a single face, *any* `facePerm`-invariant component-valued `dartRegion`
  is `EdmondsCompatible` (`region_separates` free, all darts share one face).
  **This is the base-case generator and it is unconditional.**
- The harness `exists_dr_hstepCrosscut` (`EdmondsSameRegion.lean:496`): carries
  `dr`, `hconst`, `hsep`; **base `dr := fun _ _ => ∅`** (`:541`); base `hsep` is
  `facePerm_sameCycle_of_card_face_eq_one` (`:547`); the open node is the
  `PerStepCrosscutInput` producer `hgeo` (`:471`).
- `stepRegionFamily = stepPoolRegion ∘ insertedFaceSplitPoolEquiv ∘ …`
  (`EdmondsSameRegion.lean:314`); `stepPoolRegion` (`:117`): `Sum.inl f ↦
  oldFaceRegion drm f`, `Sum.inr 0 ↦ Wleft`, `Sum.inr 1 ↦ Wright`.
- `exists_twoSidedPartition_prefixStep p₁ p₂ hne` (`PLCollarSeparation.lean:879`,
  PROVEN sorry-free): returns `R, U, V` with `R = ball((p₁+p₂)/2, ‖p₁p₂‖/2)`,
  `IsOpen R`, `IsSimplyConnected R` (`convex_ball.contractibleSpace`), `p₁,p₂ ∈
  Rᶜ`, and `IsTwoSidedPartition (regionMinusArc R (straightPolygonalArc p₁ p₂).toSimpleArc) U V`.
  **The partition is of the TUBE `R \ β.carrier`, NOT of the global complement.**
- `IsTwoSidedPartition W U V` (`PlaneArcSeparation.lean:104`): `U,V` ambient-open,
  disjoint, `U ∪ V = W`, both nonempty, both preconnected.
- `regionMinusArc R β := R \ β.carrier` (`PlaneArcSeparation.lean:344`); open
  (`regionMinusArc_isOpen`, `:362`).
- `exists_twoSidedPartition_of_arc` (`PlaneArcSeparation.lean:382`): **the only
  `sorry` in `PlaneArcSeparation`** — the general Jordan-strength crosscut
  theorem. Its gap report (`:398–467`) documents that mathlib v4.30 lacks Riemann
  mapping, Jordan curve, Schoenflies, Mayer–Vietoris. **This sorry is NOT on the
  straight path.**

---

## 2. The load-bearing answer

### 2.1 The node is genuinely open and is the larger of the two (PROVEN, by source)

Restating the N1-doc §5 finding, re-verified here:

- The harness base is `dr := ∅` (`EdmondsSameRegion.lean:541`). Adding `hreal
  start` demands `∅ = regionAt (prefixEdges start) R₀ (dartSectorPoint start d)`,
  which is **false** (the RHS is a nonempty component for a complement point). So
  the base must be **replaced** — a genuine edit to the otherwise-frozen
  sorry-free harness.
- The step identity `stepPoolRegion(splitClass d) = regionAt (prefixEdges (m+1))
  R₀ (dartSectorPoint (m+1) d)` unfolds (`stepPoolRegion`, `:117`) into:
  - **Old non-cut face** (`Sum.inl f`): needs the *cross-level* equality
    `regionAt (prefixEdges m) R₀ q = regionAt (prefixEdges (m+1)) R₀ q` for a
    non-cut point `q` (sub-obligation 1, §4);
  - **New sides** (`Sum.inr 0/1 = Wleft/Wright`): needs `Wleft/Wright` (global
    successor components) to be **named** by `dartSectorPoint (m+1) d` and to be
    **distinct global components** (sub-obligation 2, §5).
  Neither is a `rw`/`simp`. This is the geometric Edmonds correspondence
  (`region_separates`) as an *equality of named regions*. PROVEN that it is
  required, by unfolding the definitions.

### 2.2 What the existing PL layer supplies, exactly (PROVEN, by source)

`exists_twoSidedPartition_prefixStep` (`:879`, sorry-free) supplies, per cotree
edge with distinct endpoints `p₁ ≠ p₂`:

  `R = ball(midpoint, L/2)`, `IsOpen R`, `IsSimplyConnected R`, `p₁,p₂ ∈ Rᶜ`,
  `IsTwoSidedPartition (R \ β.carrier) U V`.

This is the **LOCAL, in-tube separation datum**. It is genuinely sorry-free and
axiom-clean (re-verified by the task prompt; the file contains no `sorry`/`admit`
in any proof body — the only matches are docstring text; §3). It does **not**
supply:

- (a) any statement about `drawingComplementIn (prefixEdges (m+1)) R₀` (the
  *global* complement) — `U,V` are subsets of the *tube* `R`, and as bare sets
  both `U` and `V` sit inside the **same** global component until the new arc is
  present (the N1-doc §5.2 / region-face-bridge-plan §6.2 correction);
- (b) any `regionAt = …` realization tying `dr m` to a geometric point;
- (c) any `dartSectorPoint` object (the companion node owns N1a′; the standalone
  dart→point map was **removed**, `DartSectorPoint.lean` header, 2026-06-16).

### 2.3 The verdict

The realization node is a **NAMED OBSTRUCTION**: it does **not** route entirely
through the existing PL layer.

- Sub-obligations 1 (§4), 3 (§6), and the *equality* half of sub-obligation 2
  (§5.5) are **CONSTRUCTIBLE** — point-set / `connectedComponentIn` arguments plus
  the companion node's N1a′ sector point, with no separation content.
- The *distinctness* half of sub-obligation 2 (§5.4), `Wleft ≠ Wright` as **global**
  components, is the **NAMED OBSTRUCTION**: the crosscut-separation theorem for a
  simply-connected planar domain (distinctness half), which mathlib v4.30 lacks and
  the repo has not built. The in-tube partition reduces it to its sharpest form
  (straight chord, distinctness only) but does not discharge it.

**Why the obstruction is real and not a mathlib-naming gap (PROVEN, §5.4).** Two
candidate point-set reductions both provably fail to close `Wleft ≠ Wright`:
(i) the global `sideForm` half-planes — a complement path can cross the supporting
*line* off the chord (the plane minus a *segment* is connected; EMPIRICALLY
VERIFIED grid shape); (ii) the in-tube partition — a global component's trace
`W ∩ R` can be disconnected. The genuine content is *separation* (excluding a
re-entry path), which is the Jordan-family fact `PlaneArcSeparation.lean:398–467`
documents as absent.

**What the PL layer DOES reduce it to (the value delivered).** The general arc
sorry `exists_twoSidedPartition_of_arc` (`:382`) is **never invoked**; the straight
case has the *local* partition `exists_twoSidedPartition_prefixStep` sorry-free,
plus `U ⊆ {sideForm > 0}`, `V ⊆ {sideForm < 0}` proven, plus the §5.2 point-set
facts. So the residual is **strictly weaker** than `:382` (local part done;
distinctness only; straight chord only) — but still a planar-separation lemma to
be built.

---

## 3. Provenance / axiom status of the PL layer (re-verified)

- `PLCollarSeparation.lean` has **no `sorry`/`admit` in any proof body**
  (`grep "sorry\|admit"` returns only docstring lines `:97,:100,:104,:839,:851,:1015`).
  So `exists_twoSidedPartition_prefixStep` (`:879`) and
  `exists_twoSidedPartition_of_straightArc` (`:480`) are sorry-free in body.
  **PROVEN** (source read) that they are sorry-free; **CONJECTURED** (not freshly
  `#print axioms`-checked here; I cannot run `lake`) that they are axiom-clean
  `[propext, Classical.choice, Quot.sound]` — the task prompt states a fresh
  re-verification, which I take at face value.
- **Stale-memory correction (recorded, `nthdegree 01KVR6TKGN…`).** Memory
  `5SYE9W` (2026-06-17) claimed `exists_twoSidedPartition_of_straightArc` has
  jointly-unsatisfiable hypotheses (so `exists_twoSidedPartition_prefixStep`
  "can never be completed"). That is **NO LONGER VALID**: the `5SYE9W`
  `example : False` relied on an `hSrcNear_L` conclusion containing an upper
  bound `footParam ∈ Ioc 0 cSrc`, `cSrc ≤ 2α < 2/3`. The **current** `hSrcNear_L`
  (`:496–502`) conclusion is only `p ∈ segCarrier ∧ 0 < footParam ∧ dist p
  (verts 0) = footParam · dist(segSrc)(segTgt)` — **no `cSrc` upper bound** — and
  that distance identity is the genuine geometric fact, discharged at `:1050`.
  `exists_twoSidedPartition_prefixStep` sets `S` = whole open segment, `R` =
  midpoint ball, and discharges `hSband` (`:1007`), `hSrcNear_L` (`:1039`) with no
  `sorry`. The signature was fixed after 2026-06-17. This is **load-bearing for
  the verdict**: the local separation datum is real and applicable.

---

## 4. Sub-obligation 1 — non-cut-face cross-level region invariance

> **Claim.** For a non-cut face named by point `q` whose `prefixEdges m`
> component is disjoint from the new arc's carrier `K`,
> `regionAt (prefixEdges m) R₀ q = regionAt (prefixEdges (m+1)) R₀ q`.

**Verdict: CONSTRUCTIBLE (PROVEN-on-paper, clean point-set).**

Let `D := drawingComplementIn (prefixEdges m) R₀` and `D' :=
drawingComplementIn (prefixEdges (m+1)) R₀`. By the prefix structure,
`arcUnion (prefixEdges (m+1)) = arcUnion (prefixEdges m) ∪ arcSet (prefixEdges
(m+1)) eₙ`, where `eₙ` is the new edge (the prefix keeps all old edges and adds
one). Hence

  `D' = D \ K`, where `K := arcSet (prefixEdges (m+1)) eₙ`

(the complement only **shrinks** by removing the new carrier; `R₀` and all old
carriers are identical at the two levels).

If `C := connectedComponentIn D q` satisfies `C ∩ K = ∅`, then:

- `C ⊆ D \ K = D'` (since `C ⊆ D` and `C ∩ K = ∅`).
- `C` is preconnected (`isPreconnected_connectedComponentIn`) and `q ∈ C`, so
  `C ⊆ connectedComponentIn D' q` (`IsPreconnected.subset_connectedComponentIn`).
- Conversely `connectedComponentIn D' q ⊆ D' ⊆ D` is preconnected and contains
  `q`, so `connectedComponentIn D' q ⊆ connectedComponentIn D q = C`.
- Antisymmetry ⇒ equality.

All four steps are existing mathlib lemmas (`connectedComponentIn_subset`,
`isPreconnected_connectedComponentIn`, `IsPreconnected.subset_connectedComponentIn`,
`Set.Subset.antisymm`). **No separation theorem.** The only nontrivial input is
`C ∩ K = ∅` — i.e. the new arc's carrier is disjoint from the non-cut face's
component. For the straight drawing this is the geometric fact "the inserted
chord lies in *one* old face and is disjoint from every other face's component,"
which reduces to: the new arc's carrier is contained in the single crosscut
face's closure and the open arc avoids `arcUnion (prefixEdges m)` (the arc is
inserted last; PROVEN-on-paper in `crossing-lemma-A1-edmonds-sameregion.md` §B2).

EMPIRICALLY VERIFIED (the abstract set-theoretic *shape* only): a finite-graph
model of "component disjoint from removed set ⇒ component invariant" gave 0
failures / 20261 trials (`/tmp/cc_logic.py`). This checks the direction of the
implication, not the ℝ² content.

**Mathlib gap: NONE.** **Sub-obligation 1 is CONSTRUCTIBLE.**

FLAG FOR IMPLEMENTER: the standalone lemma
`regionAt_eq_of_arcUnion_eq_sdiff` (informal): given `D' = D \ K`, `q ∈ D'`,
`connectedComponentIn D q ∩ K = ∅` ⇒ `connectedComponentIn D q =
connectedComponentIn D' q`. Pure `connectedComponentIn` API; ~15 lines.

---

## 5. Sub-obligation 2 — local→global side identification (the crux)

> **Claim.** The two sides `U,V` of the in-tube `IsTwoSidedPartition (R \
> β.carrier) U V` (from `exists_twoSidedPartition_prefixStep`) name **two
> distinct global components** of `drawingComplementIn (prefixEdges (m+1)) R₀`,
> identified with the `dartSectorPoint (m+1)` components, giving `Wleft ≠ Wright`
> and the `Sum.inr 0/1` realization.

**Verdict: NEEDS-ABSENT-INFRA — the global distinctness `Wleft ≠ Wright` is a
planar-separation fact not in mathlib v4.30 and not in the repo's applicable
lemmas.** This is the single place the *separating* direction lives, and it does
**not** reduce to the existing PL layer. Details in §5.4.

### 5.1 Why the in-tube partition does NOT give global distinctness (PROVEN)

`U,V ⊆ R \ β.carrier ⊆ R`. As bare subsets of `drawingComplementIn (prefixEdges
(m+1)) R₀`, both `U` and `V` lie in the global complement (once §5.2's
`oldArcs_avoid_openTube` holds the open tube avoids old arcs), but **distinctness
of their global components is a *separating* statement**: one must exclude a path
in the global complement that leaves `R`, goes around an endpoint, and re-enters
on the other side.

EMPIRICALLY VERIFIED (abstract shape only): "separated inside `R` but joined in
the ambient" occurs in 3539/5058 finite-graph trials (`/tmp/cc_logic.py`) — so
local separation alone is **insufficient** by pure set theory; extra structure is
mandatory. This is exactly the obstruction `PlaneArcSeparation.lean:398–467`
flags for the general arc.

### 5.2 A supporting point-set fact that IS constructible (but does not suffice)

The one piece of the local→global story that *is* mathlib-constructible is the
identity that the global complement, *restricted to the open tube*, is the
tube-minus-arc. It is needed for §4 (non-cut invariance) and §5.5
(sector-point identification), but — per §5.4 — it does **not** by itself yield
distinctness.

> **`globalComplement_inter_tube_eq` ({{NEEDS_PROOF}}, CONSTRUCTIBLE).**
>   `drawingComplementIn (prefixEdges (m+1)) R₀ ∩ R = R \ β.carrier`,
> for the `exists_twoSidedPartition_prefixStep` tube `R` and the new chord `β`.

*Why it holds (PROVEN-on-paper):* `R ⊆ R₀` (a containment the producer must
arrange — the tube is a small ball about the new chord ⊆ convex hull of the
arrangement ⊆ `R₀`; *flagged*), so
`drawingComplementIn M' R₀ ∩ R = R \ arcUnion M'`. The new arc contributes
`β.carrier`. The remaining content is:

> **`oldArcs_avoid_openTube` ({{NEEDS_PROOF}}, CONSTRUCTIBLE — δ-separation).**
>   `(arcUnion (prefixEdges m)) ∩ R ⊆ β.carrier`.

*Why it holds:* the tube `R = ball(midpoint, L/2)` is a thin ball about the chord;
every old prefix arc is compact and meets the closed chord only at the two
endpoints (crossing-freeness), so shrinking the radius to `min(L/2, δ)` (`δ` the
old-arc δ-separation) keeps every old arc's interior out of the open tube. Same
finiteness+compactness δ-separation as the companion node's §3.1–§3.2; **not
Jordan.** *Flagged:* this couples the producer's tube radius to `δ`.

These are CONSTRUCTIBLE. But note (§5.4): the global-component distinctness does
**not** follow from "`D' ∩ R = R\β` and `U,V` are the two sides of `R\β`," because
a global component `W` with `W ∩ R ⊇ {u,v}` can have `W ∩ R` disconnected (a path
in `W` may leave `R`). The set-theoretic reduction stalls exactly there.

### 5.3 (deleted — the tube-trace routes do not close; see §5.4)

The reduction "global distinctness from the in-tube partition + `D' ∩ R = R\β`"
does not close: `Wleft = Wright` gives a preconnected `W ⊆ D'` with `u,v ∈ W`, and
`W ∩ R ⊆ R\β`, but `W ∩ R` need not be connected, so no contradiction with `U ≠
V`. The honest residual is the *separation* statement of §5.4.

### 5.4 The genuine residual — global distinctness is a planar-separation fact (NEEDS-ABSENT-INFRA)

The distinctness `Wleft ≠ Wright` requires ruling out a global preconnected
`P ⊆ drawingComplementIn M' R₀` containing both `u ∈ U` and `v ∈ V`. This is the
*separating* direction, and it does **not** reduce to the tube partition or to the
`sideForm` half-planes. The precise residual:

> **`crosscut_separates_global` ({{NEEDS_PROOF}}, the irreducible separating fact).**
> No preconnected `P ⊆ drawingComplementIn (prefixEdges (m+1)) R₀` contains both a
> point of `U` (a side of `R \ β`) and a point of `V` (the other side).

**The `sideForm` half-plane shortcut does NOT close it (PROVEN that it fails).**
With `ℓ := {sideForm p₁ p₂ z = 0}`, `ℓ⁺/ℓ⁻` the open half-planes (convex,
preconnected — repo `convex_mul_sideForm_gt`, `PolygonalArc.lean:149`/`:134`), and
`U ⊆ ℓ⁺`, `V ⊆ ℓ⁻` (repo `collarPlus/Minus_subset_pos/neg_sideForm_of_numSegs_one`,
`PLCollarSeparation.lean:417/444`): the contradiction `P ⊆ ℓ⁺ ∪ ℓ⁻` would need
`P ∩ ℓ = ∅`, i.e. `P` avoids the **whole line** `ℓ`. But `P ⊆ drawingComplementIn
M' R₀` only avoids `β.carrier = segment ℝ p₁ p₂ = ℓ ∩ closure R` (the **chord**,
not the line). `P` may cross `ℓ` on either open ray beyond `p₁` or `p₂`. To
salvage the argument one would need `ℓ \ β.carrier ⊆ arcUnion M' ∪ R₀ᶜ` (the line
off the chord is covered) — **FALSE in general**: a cotree chord's supporting
line, extended past an endpoint, generically runs through open complement inside
`R₀`. So the half-plane argument is genuinely insufficient, not merely missing a
mathlib lemma name.

EMPIRICALLY VERIFIED (abstract grid shape, `/tmp/halfplane_crossing.py`): "disk
minus the chord only" has the two sides **joined** (a path goes around an
endpoint); "disk minus the whole line" has them separated. So global distinctness
holds **iff `ℓ` is covered off the chord** — which it is not — confirming the
shortcut fails and the genuine content is separation.

**Is `crosscut_separates_global` mathlib-v4.30-constructible?** **No, not from the
existing PL layer.** It is the crosscut theorem "removing a crosscut from a
simply-connected planar domain raises the number of components by exactly one,"
restricted to the *distinctness* (≥2) half. The local partition
(`exists_twoSidedPartition_prefixStep`) supplies the *two open sides inside the
tube*; promoting their distinctness to the **global** complement is precisely the
separation content that `PlaneArcSeparation.lean:398–467` documents as absent from
mathlib v4.30 (no plane separation, no π₀-of-complement, no Mayer–Vietoris, no
Jordan/Schoenflies/Riemann). The **straight** specialisation does *not* make it
elementary: even disk-minus-chord = two convex half-disks gives only the *local*
split; the global join is blocked only by a re-entry-crosses-the-arc argument,
which is the separating direction itself.

**This is strictly weaker than the §382 general sorry** (the local partition is
already built; only global distinctness remains, and only for a straight chord in
a ball), but **"weaker than §382" is not "constructible from the existing PL
layer."** It is a new planar-separation lemma the repo must build, of the same
family as §382.

**Verdict on sub-obligation 2: NEEDS-ABSENT-INFRA (a planar-separation lemma not
in mathlib v4.30 and not in the repo's applicable lemmas).** This is the
load-bearing finding and it **corrects** the headline: the realization node does
**not** route entirely through the existing sorry-free PL layer.

### 5.5 Identification with `dartSectorPoint (m+1)` (the *equality* half — CONSTRUCTIBLE)

Distinct from the distinctness obstruction (§5.4), the realization also needs the
*equality* `Wleft = regionAt … (dartSectorPoint (m+1) d)` for the new darts `d` on
the `Wleft` side (and symmetrically). This **is** CONSTRUCTIBLE: it is
`regionAt_eq_of_mem_isPreconnected` applied to a preconnected `S` containing both
the partition point `u ∈ U` and `dartSectorPoint(m+1) d`, with `S` a collar
segment on the `U`-side of the chord (the open collar `collarPlus`, which is
preconnected — `isPreconnected_collarPlus_of_sliver_budgets`, used at
`PLCollarSeparation.lean:841` — and lies in `drawingComplementIn M' R₀` once
§5.2 holds), provided `dartSectorPoint (m+1) d` lands on the same side. That side
assignment (the new dart's sector point sits in the successor-side collar) is the
**N1a′ / companion-node** content. So the *equality* half is CONSTRUCTIBLE given
N1a′ + §5.2; only the *distinctness* half (§5.4) is the obstruction.

---

## 6. Sub-obligation 3 — non-`∅` base

> **Claim.** At `prefixEdges start` (the single-face tree prefix, `hcard1`),
> build a genuine `regionAt` base assignment and prove `dartSectorPoint start d`
> lands in that one face for every dart `d`.

**Verdict: CONSTRUCTIBLE (PROVEN-on-paper).**

- The base prefix has **one face** (`hcard1`, supplied to the harness at `:500`;
  `RM:8990` upstream). So `drawingComplementIn (prefixEdges start) R₀` has the
  relevant single component containing every sector point.
- `exists_point_in_complement` (`DartSectorPoint.lean:106`, PROVEN sorry-free)
  already gives a complement point `p₀`. Define the base
  `dr start _ d := regionAt (prefixEdges start) R₀ (dartSectorPoint start d)`.
- `hreal start` is then `regionAt … (dartSectorPoint start d) = regionAt …
  (dartSectorPoint start d)` — `rfl` **once the base `dr` is defined this way**.
  The real content is that this base `dr` satisfies the harness's `hconst`/`hsep`:
  - `hconst` (face-constancy): **shape, not geometry**. Index the base by the
    **face**: `dr start _ d := regionAt … (faceSectorPoint (Face_mk d))` (the
    region-face-bridge-plan §16 finding). Then `hconst` is a one-line `congrArg`
    of `faceMk_facePerm` (`EulerBound.lean:75`, `Face_mk (facePerm d) = Face_mk
    d`). PROVEN-on-paper; zero geometry.
  - `hsep` (single-face): `facePerm_sameCycle_of_card_face_eq_one` — exactly the
    harness's existing base `hsep` (`:547`). PROVEN.
- The remaining content is "`dartSectorPoint start d ∈ drawingComplementIn
  (prefixEdges start) R₀` for every dart `d`" — the `card`-dependent membership of
  **N1a′** (the punctured-ball case when a vertex has one incident end, the
  wedge case otherwise). This is the companion node's N1a′-membership, restricted
  to level `start`. CONSTRUCTIBLE given N1a′.

**Mathlib gap: NONE.** The non-`∅` base is CONSTRUCTIBLE; it consumes the
*membership* half of N1a′ (companion node) and the `faceMk_facePerm` shape trick.

Note the harness edit: `exists_dr_hstepCrosscut` must carry `hreal` as a fourth
invariant and replace the `dr := ∅` base. This is the FLAG already recorded in
`crossing-lemma-A1-B1-hsplit-design.md` §9. The edit is mechanical *once* the
three sub-obligations are lemmatised; re-`#print axioms` after.

---

## 7. Named sub-lemma DAG (hardest node first)

`M := prefixEdges m`, `M' := prefixEdges (m+1)`, `ℓ := {sideForm p₁ p₂ = 0}`.
The companion-node object **N1a′** (the `angleAt`-wedge sector point + its
`drawingComplementIn` membership) is an **input** to this DAG, not part of it.

```
[N1a′]  (companion node — sector point q_d at the dart's successor wedge,
         q_d ∈ drawingComplementIn, q_d on the correct sideForm-sign side)
   │            owns: angleAt-interval wedge API, δ-separation §3.1/§3.2
   ▼
NODE R5a  oldArcs_avoid_openTube                                {{NEEDS_PROOF}}
          (arcUnion M) ∩ R ⊆ β.carrier      [δ-sep; HARDEST analytic piece]
          chains: exists_point_in_complement-style compactness
                  (DartSectorPoint.lean:106), Metric.infDist_pos,
                  IsCompact.isClosed, finiteness of Fin m.
                  COUPLES to the producer's tube radius (use min(L/2, δ)).
   │
   ▼
NODE R5b  globalComplement_inter_tube_eq                        {{NEEDS_PROOF}}
          drawingComplementIn M' R₀ ∩ R = R \ β.carrier
          chains: R5a, R ⊆ R₀ (producer must arrange), Set.ext / sdiff algebra.
   │
   ├─────────────┐
   ▼             ▼
NODE R5c  crosscut_separates_global   ◀── THE OBSTRUCTION (NEEDS-ABSENT-INFRA)
          Wleft ≠ Wright as GLOBAL components
          NOT closed by: sideForm half-planes (path crosses line off chord; §5.4),
                         in-tube partition (global comp trace can disconnect; §5.2).
          NEEDS: crosscut-separation theorem for simply-connected planar domain
                 (distinctness half) — absent from mathlib v4.30 (no plane
                 separation / π₀-of-complement / Mayer–Vietoris) and from the repo
                 (only the general sorry :382 + the local partition exist).
   │             │
   ▼             ▼
NODE R5d  noncut_region_invariance              (CONSTRUCTIBLE, §4)
          regionAt M R₀ q = regionAt M' R₀ q   when comp(q) ∩ β.carrier = ∅
          chains: connectedComponentIn_subset, isPreconnected_connectedComponentIn,
                  IsPreconnected.subset_connectedComponentIn, Subset.antisymm.
   │
   ▼
NODE R5e  hreal_step  (the step identity, assembled)   (CONSTRUCTIBLE modulo R5c)
          stepPoolRegion(splitClass d) = regionAt M' R₀ (dartSectorPoint (m+1) d)
          inl-branch: R5d + hreal m + dartSectorPoint coherence (N1a′ side).
          inr-branch: R5c (distinctness) + §5.5 equality + R5b.
   │
   ▼
NODE R5f  hreal_base  (non-∅ base)                               (CONSTRUCTIBLE, §6)
          face-indexed dr; hconst via faceMk_facePerm; hsep via card-1;
          membership via N1a′ at level start.
   │
   ▼
NODE R5g  carry hreal across exists_dr_hstepCrosscut             (mechanical edit)
          add 4th invariant; replace ∅ base; re-#print axioms.
```

Dependency order: `N1a′ → R5a → R5b → {R5c, R5d} → R5e → R5f → R5g`.

- **R5c is THE OBSTRUCTION** — NEEDS-ABSENT-INFRA. It is the global crosscut
  separation (distinctness half). It does **not** reduce to the `sideForm`
  half-planes or the in-tube partition (both shown insufficient, §5.4/§5.2). It is
  the only node that is not constructible from the existing PL layer; everything
  else gates on it only through R5e.
- **R5a** is the hardest *constructible* analytic piece (δ-separation /
  compactness, same family as the companion node §3.1–§3.2). It is needed for R5d,
  §5.2, and §5.5, but it does **not** discharge R5c.
- **R5b, R5d, R5e (modulo R5c), R5f, R5g** are point-set / shape / mechanical.

---

## 8. Where mathlib v4.30 is and is NOT invoked

| Need | Status | Lemma / gap |
|---|---|---|
| `connectedComponentIn` shrink-invariance (R5d) | mathlib-present | `connectedComponentIn_subset`, `IsPreconnected.subset_connectedComponentIn` |
| open complement / open region | mathlib-present | `IsOpen.connectedComponentIn`, `IsOpen.sdiff` |
| δ-separation of old arcs from tube (R5a, R5b) | mathlib-present | `Metric.infDist_pos_iff_notMem_closure`, `IsCompact.isClosed`, finite min |
| `regionAt_eq` equality on collar segment (R5e equality / §5.5) | repo-present, PROVEN | `regionAt_eq_of_mem_isPreconnected` (`RegionFaceBridge.lean:131`), `isPreconnected_collarPlus…` |
| `faceMk_facePerm` for `hconst` (R5f) | repo-present | `EulerBound.lean:75` |
| `collar± ⊆ {sideForm ≷ 0}` (sharpens R5c, does not close it) | repo-present, PROVEN | `PLCollarSeparation.lean:417/444` |
| in-tube `IsTwoSidedPartition` (the LOCAL partition) | repo-present, PROVEN | `exists_twoSidedPartition_prefixStep:879` |
| **global crosscut distinctness `Wleft ≠ Wright`** (R5c) | **mathlib-ABSENT + repo-ABSENT** | the (MS) crosscut-separation theorem, distinctness half — §5.4 |
| general crosscut separation (`exists_twoSidedPartition_of_arc`) | mathlib-ABSENT (Jordan) | `PlaneArcSeparation.lean:382` sorry — NOT invoked, but R5c is its weaker sibling |
| Riemann mapping / Schoenflies / Mayer–Vietoris / plane separation | mathlib-ABSENT | documented `:426–467` |

**The general arc sorry `exists_twoSidedPartition_of_arc` (`:382`) is never
*invoked*** — the straight path has its own local partition. But R5c
(`Wleft ≠ Wright` as **global** components) is the **distinctness half of the same
(MS) crosscut theorem**, and it is **absent** from mathlib v4.30 and from the
repo's applicable lemmas. The `sideForm` half-planes sharpen the obstruction (they
fix the two sides) but do **not** close it (§5.4). So unlike the *local* partition
— which `exists_twoSidedPartition_of_straightArc` discharges by `sideForm`
side-separation — the *global* distinctness has no analogous `sideForm`-only
discharge.

---

## 9. Structural assumptions used (stated explicitly)

- **Straightness** (every arc a `segmentArc`): essential, and it is what makes R5c
  the *weakest possible* form of the obstruction — the chord lies on a line `ℓ`,
  the two sides are fixed by `sideForm` sign (`U ⊆ ℓ⁺`, `V ⊆ ℓ⁻`, proven). But
  straightness does **not** eliminate R5c: a global complement path may still cross
  `ℓ` off the chord (§5.4). For a curved arc the obstruction is the full §382 sorry.
- **Crossing-free cotree insertion** (the new arc's open interior avoids
  `arcUnion (prefixEdges m)`): essential for R5a and R5d. PROVEN-on-paper in
  `crossing-lemma-A1-edmonds-sameregion.md` §B2.
- **Finiteness + compactness** (`Fin m` arcs, each compact): essential for R5a/R5b
  δ-separation (constructible) — NOT for R5c.
- **Simple connectivity of the tube** (`convex_ball ⇒ IsSimplyConnected R`):
  consumed by `exists_twoSidedPartition_prefixStep` to produce the *local*
  partition. The **global** distinctness R5c is *also* a simply-connected-domain
  crosscut fact (the (MS) theorem for the tube `R`), but mathlib v4.30 cannot
  execute it (no plane-separation API), so simple-connectivity-of-`R` being
  available as a hypothesis does **not** make R5c constructible. This is the
  obstruction.
- **`R ⊆ R₀`** (tube inside the ambient disk): a containment the producer must
  arrange. Flagged for the producer (needed for §5.2, constructible).
- **Not used / not needed for the constructible parts**: any Jordan curve /
  Schoenflies / Riemann mapping / Mayer–Vietoris; the §382 general-arc sorry. But
  R5c (the obstruction) **does** need a planar-separation statement of that family
  (distinctness half, straight chord).

---

## 10. What next (ranked)

1. **Confront R5c `crosscut_separates_global` — the obstruction — as a standalone
   planar-separation lemma.** This is the decisive item. Two sub-routes to scope
   (both are bespoke developments, not mathlib lookups):
   - **(a) Build the (MS) crosscut-separation theorem (distinctness half) for the
     simply-connected ball.** This is what `PlaneArcSeparation.lean:382`'s gap
     report calls residual sub-obligation 1 ("≥2 components"), specialised to a
     straight chord in a ball. The disk-minus-chord = two convex half-disks gives
     the *local* split for free; the global distinctness needs the re-entry
     argument. A from-scratch π₀/separation development.
   - **(b) Sidestep distinctness entirely** by checking whether the **combinatorial
     `hinj`** the harness actually consumes can be met without the *geometric*
     `Wleft ≠ Wright`. The region-face-bridge-plan §16 finding (`poolRegion` forced
     injective) suggests the regions must be distinct, but it is worth verifying
     whether a *combinatorial* distinctness (the two new split-pool classes
     `Sum.inr 0 ≠ Sum.inr 1`) plus the *equality* facts (§5.5) suffice for the
     harness's `hinj`/`hfactor`, reserving the geometric distinctness for a single
     downstream use. **This is the only route that could avoid the absent infra;
     scope it before committing to (a).**
2. **Build N1a′ (companion node).** Gates the *constructible* parts (R5a/R5d/R5e
   equality/R5f). Independent of R5c.
3. **R5a `oldArcs_avoid_openTube` + R5b `globalComplement_inter_tube_eq`** —
   CONSTRUCTIBLE δ-separation; needed for §4/§5.5.
4. **R5d, R5e (equality half), R5f** — CONSTRUCTIBLE point-set / shape.
5. **R5e (distinctness half) + R5g** — blocked on R5c; do last.

---

## 11. Summary table (evidence levels)

| Claim | Level | Basis |
|---|---|---|
| The realization node is a SECOND open node, larger than N1a′, requiring a non-`∅` base + step identity | **PROVEN** | `EdmondsSameRegion.lean:541` (`∅` base), `:117/:314` unfold; N1-doc §5 re-verified |
| In-tube `IsTwoSidedPartition` is supplied sorry-free; partition is of the TUBE not the global complement | **PROVEN** | `exists_twoSidedPartition_prefixStep:879`, conclusion `regionMinusArc R β` |
| `exists_twoSidedPartition_prefixStep`/`_of_straightArc` sorry-free in body | **PROVEN** | grep: no `sorry`/`admit` in proof bodies of `PLCollarSeparation.lean` |
| …and axiom-clean `[propext, Classical.choice, Quot.sound]` | **CONJECTURED** | task-prompt fresh re-verification; not `lake`-run here |
| Memory `5SYE9W` unsatisfiability finding is STALE (no longer valid vs current `hSrcNear_L`) | **PROVEN** | current `:496–502` has no `cSrc` bound; discharged at `:1050`; recorded `nthdegree 01KVR6TKGN…` |
| Sub-obl 1 (non-cut-face cross-level invariance) — CONSTRUCTIBLE | **PROVEN-on-paper** | §4; `connectedComponentIn` shrink-invariance, mathlib-present; shape EMPIRICALLY VERIFIED 0/20261 |
| Sub-obl 2 distinctness needs the *separating* direction; in-tube partition alone insufficient | **PROVEN** | §5.1; shape EMPIRICALLY VERIFIED 3539/5058 local-sep-but-global-join |
| The `sideForm` half-plane shortcut does NOT close `Wleft ≠ Wright` (path crosses line off chord) | **PROVEN** | §5.4; plane-minus-segment is connected — EMPIRICALLY VERIFIED grid (`/tmp/halfplane_crossing.py`) |
| Sub-obl 2 distinctness `Wleft ≠ Wright` (global) is a NAMED OBSTRUCTION — absent from mathlib v4.30 and repo | **PROVEN** (that it is the residual; that mathlib lacks it) | §5.4; (MS) crosscut-separation distinctness half; `PlaneArcSeparation.lean:398–467` |
| Sub-obl 2 *equality* half (`Wleft = regionAt ∘ dartSectorPoint`) — CONSTRUCTIBLE | **PROVEN-on-paper** | §5.5; `regionAt_eq_of_mem_isPreconnected` on a collar segment, given N1a′ |
| R5a/R5b `oldArcs_avoid_openTube`/`globalComplement_inter_tube_eq` — CONSTRUCTIBLE δ-sep (no Jordan) | **CONSTRUCTIBLE** ({{NEEDS_PROOF}}) | §5.2; compactness + `infDist_pos` + finiteness, same family as N1a′ §3.1/§3.2 |
| Sub-obl 3 (non-`∅` base) — CONSTRUCTIBLE | **PROVEN-on-paper** | §6; face-indexed `dr`, `faceMk_facePerm` (`EulerBound.lean:75`), card-1 `hsep`, N1a′ membership |
| The general sorry `exists_twoSidedPartition_of_arc` is never *invoked*, but R5c is its weaker sibling | **PROVEN** | §8; straight path has the local partition; the global distinctness is the (MS) distinctness half |
| **Overall: realization node is a NAMED OBSTRUCTION (R5c global crosscut distinctness); 2 of 3 sub-obligations + the equality half ARE constructible from the PL layer** | **NAMED-OBSTRUCTION** | §0/§2; DAG §7 |

---

## 12. Orchestrator validation (2026-06-22) — the obstruction is potentially SIDESTEPPABLE

The §10 route-(b) premise is **CONFIRMED against source** (orchestrator read of
`SzemerediTrotter.lean:4651–4752`): A1's conclusion
`(residualMap G hARRG).IsPlanar` is proved entirely through

  `hstepCrosscut` (the bundle) → `regionSeparates_prefix_of_crosscut`
  (`EdmondsConstruction.lean:148`, `SzemerediTrotter.lean:4725/:4738`) → `SameCycle`
  → `ResidualMapPrefixStepInsertion.sameFace`
  → `exists_residualMap_isPlanar_of_prefix_insertions_connected` (`:4743`).

It **never invokes `edmondsCompatibleAtPrefix`** (`EdmondsConstruction.lean:194`),
so it **never needs the `hcomp` field** (`:200`, `dr m hm d = regionAt … p`, the
geometric realization). `regionSeparates_prefix_of_crosscut` consumes ONLY the
combinatorial `PrefixStepCrosscutData` (`hregion`/`hinj`/`hvertex`/`hfactor`), not
geometric `dr`. The harness already produces `dr` with a `∅` base and no `hcomp`.

**Consequence:** the named obstruction R5c (`crosscut_separates_global`, geometric
region-*distinctness*) is **needed only if `hinj` forces geometric `Wleft ≠ Wright`.**
Since `hgeo` *supplies* `Wleft,Wright`, and no A1 consumer requires them to be
`regionAt` sets, they can in principle be **formal distinct sets**, making
`hinj`/`hWne`/`hWold` combinatorial. Then `hgeo`'s only remaining geometric content
is `hregion` = **co-faciality of the entered corners** — an *equality* (the
connectedness direction), NOT the distinctness R5c blocks on.

**The single remaining make-or-break question** (next dispatch): can `hgeo` be
discharged with a formal `dr`, i.e.
  (1) can `hgeo` supply formal distinct `Wleft/Wright` meeting the harness `hinj`
      (`prefixStepSameRegion_poolRegion_injective`), or does
      `region-face-bridge-plan §16` ("`poolRegion` forced injective") or another
      consumer force them geometric?
  (2) is `hregion` (co-faciality of the entered corners) constructible from
      same-region connectedness WITHOUT routing through
      `facePerm_sameCycle_of_sameRegion` (`RegionFaceBridge.lean:273`), which needs
      `EdmondsCompatible` → `hcomp` → potential circularity?
If both YES: A1 closes WITHOUT `crosscut_separates_global`. If (1) or (2) forces
geometry, R5c stands and A1 is blocked on the (MS) crosscut-separation distinctness
half. **This is the routing decision for A1 closure.**
