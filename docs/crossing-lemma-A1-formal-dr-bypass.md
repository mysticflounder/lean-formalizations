# Node A1 — can `hgeo` be discharged with a FORMAL `dr`, bypassing `crosscut_separates_global`?

Settles the single routing decision left for A1 (`SzemerediTrotter.lean:4649`,
the producer `hgeo : CrossingLemma.PerStepCrosscutInput`). Builds on the
orchestrator-verified premise of
`docs/crossing-lemma-A1-edmonds-bridge-feasibility.md` §12.

Every file:line and lemma name below was read against the worktree source
(Lean v4.30, mathlib cached). Claims are labelled PROVEN / CONSTRUCTIBLE /
CONJECTURED / HEURISTIC. The load-bearing verdict is in §0; the two
sub-questions are §2 (combinatorial `hinj` / formal `Wleft,Wright`) and §3
(co-faciality `hregion` without circularity). §4 resolves the
`region-face-bridge-plan §16` tension. No Lean was built for this analysis
(the worktree is cold; a full `CrossingLemma` build is multi-session) — the
verdict is by source-reading plus two adversarial cross-model audits; the one
thing that would benefit from a build (type-checking the formal-`dr`
instantiation) is identified in §6 as a low-risk confirmation, not a load-bearing
gap.

> **2026-06-22 skeptic validation + label correction.** A math-skeptic adversarial
> pass (`docs/skeptic-crossing-lemma-A1-formal-dr-bypass-2026-06-22` — returned
> inline, not written to file) confirmed the technical findings (§2/§3/§4 PROVEN
> by source) and the orchestrator independently re-verified the load-bearing
> mechanism: `face_mk_eq_iff` (`PlanarEdgeBound.lean:229`) is sorry-free, and the
> harness passes `_hconst` into `hgeo` (`EdmondsSameRegion.lean:475`), so
> `hregion := _hconst c₁ c₂ (face_mk_eq_iff.mp A1★)` — the single geometric input
> is co-faciality **A1★** (`Face_mk c₁ = Face_mk c₂` at level `m`); everything else
> (`hsame`, `hregion`, `hvertex`, `hinj` via formal `Wleft,Wright`, `hfactor`)
> assembles combinatorially. **Net validated result:** A1 does **not** CLOSE — A1★
> is an open obligation (CONJECTURED-constructible, residual leaf N1a′). What the
> formal `dr` *does* establish is that the distinctness obstruction
> `crosscut_separates_global` **and** the `hreal` realization node are both
> eliminated from the A1 path; `hgeo` reduces to A1★ alone. The headline word
> "CLOSES" below is corrected to "REDUCES to A1★".
>
> **2026-06-22 follow-up (math-professor feasibility, validated) — A1★'s residual
> is the region↔face bridge, NOT a thin `regionAt` transport.** A deep pass
> (`docs/crossing-lemma-A1star-equality-feasibility.md`, orchestrator-validated
> against source) refutes the §5.2 label "A1★ is CONSTRUCTIBLE via
> `regionAt_eq_of_mem_isPreconnected`, no Jordan": that combinator
> (`RegionFaceBridge.lean:131`) concludes a **region** equality
> `regionAt q₁ = regionAt q₂`, whereas A1★ is a **face** equality
> `Face_mk c₁ = Face_mk c₂`. The only repo/mathlib bridge from region-equality to
> face-equality is `facePerm_sameCycle_of_sameRegion` (`RegionFaceBridge.lean:273`)
> = the `EdmondsCompatible.region_separates` clause = the project's pre-existing
> **geometric Edmonds direction** (RM:8990 base / RM:1757 step), which needs a
> geometric assignment `E`. Exhaustive grep returns NO other region→face/`SameCycle`
> producer; the N1a′ `angleAt` sector point feeds route α (the region layer), so it
> does NOT by itself deliver the face-level A1★. **Net:** A1★ is
> CONJECTURED-constructible with one identified residual = the region↔face equality
> bridge under ARR (equivalently: single-pair co-faciality proven combinatorially
> from the arc germ + rotation system, region-free — the right target, but OPEN; no
> repo producer, and using `IsPlanar` at level `m` is PROVEN circular). The
> distinctness elimination still holds and A1★ is logically distinct from
> `crosscut_separates_global`, but A1★ is NOT yet shown mathlib-v4.30-closable. The
> §5.2 / §7 "CONSTRUCTIBLE" claims are too strong for the face-level statement: read
> them as "the **region sub-fact** is constructible; the region→face step is the
> open Edmonds bridge."
>
> **Label convention.** "CONSTRUCTIBLE" below means one of two distinct tiers:
> (a) **PROVEN-on-paper modulo a named trivial mathlib assembly** (e.g. §2.3
> fresh-set existence) — not yet built but with the lemmas name-checked; or
> (b) **CONJECTURED, no absent infra** (A1★) — believed constructible in
> mathlib v4.30 with no missing foundational theory, but not yet proven even on
> paper to the leaf. The A1★ row is tier (b) = **CONJECTURED**.

---

## 0. The headline verdict

> **A1 REDUCES to a single open co-faciality equality (A1★); the named
> obstruction `crosscut_separates_global` is eliminated from the A1 path.** (A1★ =
> `Face_mk c₁ = Face_mk c₂` at level `m`, CONJECTURED-constructible — A1 is NOT
> closed; see the 2026-06-22 correction banner above.) Both sub-questions resolve
> in favour of a formal (non-geometric) `dr`:
>
> 1. **Combinatorial `hinj` (`Wleft,Wright` formal) — CONSTRUCTIBLE.** `hgeo` has
>    full freedom to supply `Wleft,Wright` as **formal fresh sets** (two distinct
>    sets outside `drm`'s finite image). `hinj` is consumed by the A1 path **only
>    combinatorially** (`RegionFaceBridge.lean:418`, `hinj hregion`); the set
>    *values* of `poolRegion` are never inspected geometrically. The §16 tension
>    ("`poolRegion` forced injective") was **conditional on `hcomp`** (the dead
>    `regionAt`-realization); with `hcomp` off the A1 path, injectivity of a
>    set-valued `poolRegion` is met by **any** distinct sets. No geometric
>    distinctness `Wleft ≠ Wright`, so **`crosscut_separates_global` is never
>    invoked**.
> 2. **Co-faciality `hregion` without circularity — CONSTRUCTIBLE, with one
>    residual geometric fact.** For the formal family `drm c = poolRegion_{prev}
>    (splitClass c)`, the bundle field `hregion : drm c₁ = drm c₂` is
>    **equivalent** to co-faciality `Face_mk c₁ = Face_mk c₂` at level `m` (the
>    injective-`poolRegion` algebra = the in-scope `hsep`/`hconst` pair). `hgeo`
>    produces `hregion` **from** co-faciality via the in-scope `hconst m`
>    (`SameCycle → drm eq`); this is **NOT circular** (co-faciality is the input,
>    not re-derived from `hregion`). The route **never touches**
>    `facePerm_sameCycle_of_sameRegion` / `EdmondsCompatible` / `hcomp` (all dead
>    on the A1 path). The single residual is **co-faciality of the entered corners
>    at level `m`** — the SameRegion **equality / connectedness** direction,
>    provably **distinct** from the distinctness obstruction
>    `crosscut_separates_global`.
>
> **Therefore:** the obstruction R5c (`crosscut_separates_global`, the (MS)
> crosscut-separation *distinctness* half) **does not stand on the A1 path**. The
> remaining geometric obligation is the **equality** half — co-faciality
> `Face_mk c₁ = Face_mk c₂` of the two entered corners in `residualMap
> (prefixEdges m)` (the new straight arc connects `p₁,p₂` through one complement
> region of `prefixEdges m`). It is CONSTRUCTIBLE (mathlib-sufficient, no
> Jordan/Schoenflies) and is the same residual the project already isolated as
> "Residual 2 / `hregion`" (`region-face-bridge-plan §3`, deepseek-prompt
> `HW03DB`).
>
> **Net change to the A1 obstruction map:** the larger of the two open nodes —
> the `hreal` realization invariant `dr m = regionAt ∘ dartSectorPoint` and its
> attendant `crosscut_separates_global` distinctness (the
> `edmonds-bridge-feasibility` doc's NAMED OBSTRUCTION) — is **eliminated** by the
> formal `dr`. What is left is one EQUALITY: cotree co-faciality at level `m`.

### Harness edit required

**NONE.** The harness `exists_dr_hstepCrosscut` (`EdmondsSameRegion.lean:496`)
already produces `dr` with the `∅` base (`:541`) and no `hcomp`, no `hreal`. It
consumes only `PerStepCrosscutInput`. The formal-`dr` discharge of `hgeo` plugs
into the **existing** harness unchanged. (The `region-face-bridge-plan §9` /
`edmonds-bridge-feasibility §6` FLAG "the harness must carry `hreal` and replace
the `∅` base" was a consequence of the *geometric* `dr` design; the formal `dr`
**avoids that edit entirely** — the `∅` base survives.) So there is no sorry-free
decl to re-verify on the harness side; `#print axioms` on the harness is
unchanged from its current `[propext, Classical.choice, Quot.sound]`.

---

## 1. Definitions and the A1 path (self-contained, from source)

Path prefix `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/`. `Plane := ℝ × ℝ`.

- **`PerStepCrosscutInput G start hARR`** (`EdmondsSameRegion.lean:471`): for each
  cotree step `m ≥ start`, given the recursion's family `drm : (Fin m × Bool) →
  Set (ℝ×ℝ)` and its two invariants
  - `_hconst : ∀ d₁ d₂, facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂` (`:475`),
  - `_hsep : ∀ d₁ d₂, drm d₁ = drm d₂ → facePerm.SameCycle d₁ d₂` (`:478`),
  produce `Nonempty (Σ' drm1, PrefixStepCrosscutData G m … drm drm1)`. **`drm` is
  typed `Set (ℝ×ℝ)` — arbitrary sets, no geometric constraint at the type level.**
- **`PrefixStepCrosscutData`** (`EdmondsConstruction.lean:91`): fields `c₁ c₂ :
  Fin m × Bool`, `hc : c₁≠c₂`, **`hregion : drm c₁ = drm c₂`** (`:106`), `hvertex`
  (vertex-perm splice, `:109`), `poolRegion : ({Face // ≠ Face_mk c₁} ⊕ Fin 2) →
  Set (ℝ×ℝ)` (`:115`), **`hinj : Function.Injective poolRegion`** (`:119`),
  `hfactor : ∀ hsame, ∀ d, drm1 d = poolRegion (insertedFaceSplitPoolEquiv … (Face_mk
  (symm d)))` (`:124`). **No `hcomp` field, no `regionAt`, no
  `drawingComplementIn` anywhere in the bundle.**
- **`regionSeparates_prefix_of_crosscut`** (`EdmondsConstruction.lean:148`): the
  `Nat.le_induction` chaining `region_separates_prefixStep_sameFace_concrete` from
  the card-1 base. At the step (`:175`): `hsame := ih data.c₁ data.c₂
  data.hregion` — co-faciality is the **image of `hregion`** under the level-`m`
  separation IH.
- **`region_separates_prefixStep_sameFace`** (`RegionFaceBridge.lean:398`): the
  **only** use of `hinj` is line **`418`**: `have hpooleq : splitPool d₁ =
  splitPool d₂ := hinj hregion`. Reads `poolRegion` only as an injective map; the
  *sets* it returns are opaque.
- **`exists_dr_hstepCrosscut`** (`EdmondsSameRegion.lean:496`): sorry-free harness.
  Base `dr := fun _ _ => ∅` (`:541`); base `hconst` is `rfl` (`:542`); base `hsep`
  is `facePerm_sameCycle_of_card_face_eq_one` (`:547`). Step (`:554`) feeds `dr m`
  + invariants to `hgeo`, derives `hsame := hsep m c₁ c₂ data.hregion` (`:563`),
  re-points `dr (m+1) := drm1` (`:559`). The successor `hsep` (`:599`) is produced
  via `region_separates_prefixStep_sameFace_concrete` from `data.hinj`,
  `data.hfactor` — **combinatorially**.

**The A1 consumer** (`SzemerediTrotter.lean:4721`–`4740`): both cotree sub-cases do
exactly
```
have hs_data := hstepCrosscut m hm' hstart_m                       -- the bundle
have hsame_cotree := regionSeparates_prefix_of_crosscut … hs_data.c₁ hs_data.c₂
                       hs_data.hregion                              -- SameCycle from hregion
exact ResidualMapPrefixStepInsertion.sameFace hs_data.c₁ hs_data.c₂
        hs_data.hc hsame_cotree hs_data.hvertex
```
**Fields read: `c₁,c₂,hc,hregion,hvertex` only.** `hinj`/`hfactor`/`poolRegion` are
used *inside* `regionSeparates_prefix_of_crosscut` and only at the combinatorial
line `418`. `hcomp` does not exist on the bundle.

---

## 2. Sub-question 1 — combinatorial `hinj` with FORMAL `Wleft,Wright`

> **Can `hgeo` supply `Wleft,Wright` as formal distinct sets so that
> `prefixStepSameRegion_poolRegion_injective`'s `hWne`/`hWold` hold
> combinatorially, or does some consumer force them to be geometric `regionAt`
> sets?**

**Verdict: CONSTRUCTIBLE. Formal fresh sets suffice; no consumer forces geometry.**

### 2.1 The set values of `poolRegion` are never inspected (PROVEN, by source)

The injectivity combinator `prefixStepSameRegion_poolRegion_injective`
(`EdmondsSameRegion.lean:217`, proof `:230`–`:258`) discharges injectivity using
**only**:
- `hsep` (the level-`m` separation, in scope) for the `inl/inl` case (`:231`–`:239`);
- `hWold : ∀ f, oldFaceRegion drm hconst f.1 ≠ Wleft ∧ ≠ Wright` for the `inl/inr`
  and `inr/inl` cases (`:240`–`:255`);
- `hWne : Wleft ≠ Wright` for the `inr/inr` case (`:256`–`:258`).

It **never** looks at what `Wleft,Wright` *are* — only that they are distinct from
each other and from every `oldFaceRegion` value. (PROVEN: I read the full proof
body.) Downstream, the only consumer of `poolRegion`'s injectivity on the A1 path
is `region_separates_prefixStep_sameFace:418` (`hinj hregion`), again treating
`poolRegion` as an opaque injective map. (PROVEN, §1.)

### 2.2 `oldFaceRegion` values are in `drm`'s finite image (PROVEN)

`oldFaceRegion G drm hconst (Face_mk d) = drm d` by `rfl` (`oldFaceRegion_mk`,
`EdmondsSameRegion.lean:100`). Every `f : {f : Face // …}` is `Face_mk d` for some
dart `d` (a `Face` is a `Quotient`), so every value `hWold` quantifies over lies
in `Set.range drm`. Since the dart type `Fin m × Bool` is a `Fintype`,
`Set.range drm` is **finite** (`Set.finite_range`, mathlib
`Data/Set/Finite/Range.lean:89`).

### 2.3 Fresh distinct sets always exist (CONSTRUCTIBLE)

`hWold ∧ hWne` reduce to: pick `Wleft ≠ Wright`, both `∉ Set.range drm`. The
ambient type `Set (ℝ×ℝ)` is **infinite** — the singleton family `fun x =>
({x} : Set (ℝ×ℝ))` injects `ℝ×ℝ` (infinite) into it
(`Infinite.of_injective (fun x => {x}) Set.singleton_injective`, both mathlib).
Then:
- `(Set.range drm)ᶜ.Infinite` from `Set.Finite.infinite_compl`
  (`Data/Set/Finite/Basic.lean:848`, requires `Infinite (Set (ℝ×ℝ))`);
- `((Set.range drm)ᶜ).Nontrivial` from `Set.Infinite.nontrivial`
  (`Data/Set/Finite/Basic.lean:631`) — two distinct elements `Wleft ≠ Wright`,
  both outside `Set.range drm`, hence `≠` every `oldFaceRegion` value.

All four mathlib lemma names are **CONFIRMED present in the cached mathlib v4.30**
(grep'd the worktree's `.lake/packages/mathlib` source). This is a ~10–15 line
`hgeo`-side argument; no recursion invariant beyond "the level-`m` image is finite"
(automatic from the finite dart type — nothing to carry).

**Verdict 1: CONSTRUCTIBLE.** Formal fresh `Wleft,Wright` satisfy `hWne`/`hWold`
with no geometry. The A1 path's use of `hinj` is purely combinatorial, so the
*sets* never need to be `regionAt` components. **`crosscut_separates_global`
(geometric `Wleft ≠ Wright` as global complement components) is NOT invoked.**

---

## 3. Sub-question 2 — co-faciality `hregion` without circularity

> **Is `hregion : drm c₁ = drm c₂` (the entered corners) constructible from the
> connectedness direction WITHOUT routing through
> `facePerm_sameCycle_of_sameRegion` (which needs `EdmondsCompatible` → `hcomp` →
> the geometric realization, i.e. circular)?**

**Verdict: CONSTRUCTIBLE. `hregion` is produced from co-faciality `Face_mk c₁ =
Face_mk c₂` at level `m` via the in-scope `hconst m`, with NO geometric `dr`, NO
`facePerm_sameCycle_of_sameRegion`, NO circularity. The single residual is the
co-faciality EQUALITY itself.**

### 3.1 The geometric Edmonds chain is DEAD on the A1 path (PROVEN, by grep)

The structures the question worries about — `facePerm_sameCycle_of_sameRegion`
(`RegionFaceBridge.lean:273`), `EdmondsCompatible` (`:166`),
`edmondsCompatibleAtPrefix` (`EdmondsConstruction.lean:194`, the `hcomp`
consumer), and Lemma B `residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition`
(`RegionFaceBridge.lean:331`) — have, on the A1 path, the following call-site
counts (grep over `lean/`, excluding their own definitions and docstrings):

| decl | A1-path call sites |
|---|---|
| `edmondsCompatibleAtPrefix` (the `hcomp` consumer) | **0** (dead everywhere) |
| `facePerm_sameCycle_of_sameRegion` | 1, inside Lemma B only |
| Lemma B (`…cotree_sameFace_of_twoSidedPartition`/`_of_collar_sides`) | **0** |
| `EdmondsCompatible` constructed in `SzemerediTrotter.lean` | **0** |
| `prefixStepSameRegion` (geometric `regionAt` `hregion` route) | **0** (only docstrings) |

(PROVEN by grep.) So the geometric chain `regionAt → EdmondsCompatible →
facePerm_sameCycle_of_sameRegion → hcomp` is **never executed** to close A1. The
A1 path is exclusively `hgeo` → bundle → `regionSeparates_prefix_of_crosscut` →
`region_separates_prefixStep_sameFace_concrete` → `Quotient.eq''.mp` of a face
equality, with `hinj` used combinatorially (§1).

### 3.2 `hregion ⟺ co-faciality` for the formal family (PROVEN)

For the recursion's formal family at level `m`, `drm = stepRegionFamily` of the
previous step (or `∅` at base): `drm c = stepPoolRegion … (splitClass c) =
poolRegion_{prev}(splitClass_{prev} c)`, with `poolRegion_{prev}` **injective**
(the previous step's `hinj`) and `splitClass` factoring face equality. Equivalently
— and this is the clean statement, available **without** unfolding `drm` — the two
recursion invariants in scope are
```
hconst m : facePerm.SameCycle c₁ c₂ → drm c₁ = drm c₂        (EdmondsSameRegion.lean:475)
hsep   m : drm c₁ = drm c₂ → facePerm.SameCycle c₁ c₂        (:478)
```
Together they are a **both-directions bridge** `drm c₁ = drm c₂ ⟺ SameCycle c₁ c₂`,
and `SameCycle c₁ c₂ ⟺ Face_mk c₁ = Face_mk c₂` by `face_mk_eq_iff`
(`PlanarEdgeBound.lean:229`, sorry-free, pure quotient). So
```
hregion : drm c₁ = drm c₂   ⟺   Face_mk c₁ = Face_mk c₂   (level m co-faciality)
```
(PROVEN: the `⟸` is `hconst m c₁ c₂ ∘ (face_mk_eq_iff).mp ∘ .symm`; the `⟹` is the
symmetric composite.)

### 3.3 The production of `hregion` is non-circular (PROVEN)

`hgeo` produces `hregion` by the `⟸` direction:
```
hcofacial : Face_mk c₁ = Face_mk c₂                 -- the residual (an EQUALITY)
  ⟶ SameCycle c₂ c₁        via face_mk_eq_iff.mp
  ⟶ SameCycle c₁ c₂        via .symm
  ⟶ drm c₁ = drm c₂ = hregion   via hconst m       -- in scope, combinatorial
```
The harness then recovers `hsame := hsep m c₁ c₂ hregion` (`EdmondsSameRegion.lean:563`)
and the consumer recovers `hsame_cotree` likewise (`SzemerediTrotter.lean:4725`).
**No loop:** co-faciality is the *input*; `hregion` is derived from it by `hconst`;
the later `hsep`-derivation of `hsame` recovers the same `SameCycle` (since
`hsep ∘ hconst` is the identity on `SameCycle` evidence, up to proof irrelevance).
At no point does the chain consume an object at level `m+1`, and at no point does
it consume `facePerm_sameCycle_of_sameRegion` or any `EdmondsCompatible`. The §3
circularity of `crossing-lemma-A1-B1-hsplit-design.md` (no level-`m+1` Edmonds
inside `hgeo`) is **respected** — the entire argument lives at level `m`.

### 3.4 `hvertex` is unconditional; `c₁,c₂` are region-silent (PROVEN)

The forced corners `c₁,c₂` come from
`exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`
(`ResidualMapProperties.lean:4326`, sorry-free): its conclusion (`:4339`–`:4361`)
is the angular rotation-predecessor data plus a **conditional**
`(SameCycle c₁ c₂ → ResidualMapPrefixStepInsertion)` — it asserts nothing about
regions. The `hvertex` field is built by
`prefixStepDartEquiv_permCongr_insertedEdgeMap_vertexPerm`
(`ResidualMapProperties.lean:3310`), invoked at `:4313`–`:4315` **without `hsame`**
(verified: its hypotheses are the angular `hmono₁,hmono₂,hpred₁,hpred₂`, not the
co-faciality). So `hvertex` is available **unconditionally** once ARR is in scope.

**Consequence:** the *only* gate on assembling the entire bundle (formal `Wleft,
Wright` from §2, `hregion`/`hsame` from §3.3, `hvertex` unconditional) is the
single fact `hcofacial : Face_mk c₁ = Face_mk c₂` at level `m`.

### 3.5 The residual is the EQUALITY direction, distinct from the obstruction (PROVEN)

`hcofacial : Face_mk c₁ = Face_mk c₂` is the SameRegion **equality / connectedness**
direction: geometrically, "the new straight arc connects `p₁` to `p₂` within one
complement component of `prefixEdges m`; both entered corners bound the same
region." This is the project's "Residual 2" (`region-face-bridge-plan §3`, handle
`NQWP7T`/`8S659N`) and the deepseek-prompt's first hard obligation (`HW03DB`:
"the two splice corners face the **same** predecessor face — `Face_mk c₁ =
Face_mk c₂` at level `m`").

It is **provably distinct** from `crosscut_separates_global` (the distinctness
`Wleft ≠ Wright`): `crossing-lemma-A1-B1-hsplit-design.md §7` REFUTES the "two
faces of one fact" conjecture — co-faciality (same-before, an *equality*) and
side-distinctness (split-after, an *inequality*) are logically independent. The
formal-`dr` route needs only the **equality** (and gets distinctness combinatorially
from formal fresh sets, §2). **The distinctness obstruction is bypassed.**

---

## 4. Resolving the `region-face-bridge-plan §16` tension

§16 ("Step-3 design pass") concluded:

> "`hfactor` pins `dr_{m+1} d = poolRegion(splitClass d)`, and `hinj` makes
> `poolRegion` **injective**, so `dr_{m+1}` must take **distinct** values on
> distinct split-pool classes ⇒ `faceSectorPoint` is **forced** to be
> poolRegion-derived, not an abstract per-face `Classical.choose`. … `dr` must be
> built **inductively from the per-step crosscut partitions**."

**Resolution (PROVEN): §16's forcing was conditional on `hcomp`, which is dead on
the A1 path; it does not force geometry here.**

§16's chain "`hinj` ⇒ `faceSectorPoint` forced poolRegion-derived ⇒ `dr` from
crosscut partitions" is correct **only** under the additional demand `dr m d =
regionAt R₀ (faceSectorPoint (Face_mk d))` — i.e. the `hcomp`/`hreal` realization
(its "Sanity check: a constant/abstract `faceSectorPoint` collapses `dr`, which is
incompatible with an injective `poolRegion`"). That sanity check is about a
`regionAt`-valued family: if `dr` must be `regionAt ∘ point`, then injective
`poolRegion` forces the *points* to be distinct, hence non-constant.

But **injectivity of a *set-valued* `poolRegion` carries no geometric content** —
any distinct sets satisfy it (§2.1, §2.3). Once `hcomp` is removed (the
orchestrator premise §12, confirmed: `edmondsCompatibleAtPrefix` has 0 call sites,
§3.1), there is no demand `dr = regionAt ∘ point`, so §16's "forced" conclusion
**does not apply**. The §16 finding is not *wrong*; it is **inert** on the A1 path
— it was a true statement about the *geometric* `dr` design that the formal `dr`
sidesteps.

**Cross-model note (one audit disagreed; resolved against it).** A second
adversarial audit argued §16's forcing *survives* because "the only producer of
the next step's `hregion` is `prefixStepSameRegion`, which demands `dr (m+1) cₖ =
regionAt qₖ`." This is **refuted by source**: (i) `prefixStepSameRegion`
(`EdmondsSameRegion.lean:186`) has **zero call sites** (only docstring mentions) —
it is the *intended geometric* route, not a forced one; (ii) for the formal family
`hregion` is produced by `hconst m` from co-faciality (§3.3), which `prefixStepSameRegion`
is not involved in. The audit conflated the *intended* geometric design (where
`hgeo` would call `prefixStepSameRegion` with `dr = regionAt ∘ sectorpoint`) with
*necessity*. The formal route bypasses `prefixStepSameRegion` entirely; the
`hreal` realization is **not** required. (PROVEN by the call-site grep + the
`hconst`-route construction §3.3.)

---

## 5. The single residual, stated precisely (the answer to "what next")

> **Residual A1★ (co-faciality of the entered corners — CONSTRUCTIBLE).** For the
> cotree step `m → m+1` with forced corners `c₁ ∈ incidentEnds (prefixEdges m) p₁`,
> `c₂ ∈ incidentEnds (prefixEdges m) p₂` (the rotation-predecessors of the new
> dart, from `_of_old_endpoint_incident`, `RM:4326`):
> ```
> (residualMap (prefixEdges m) hARRm).Face_mk c₁.1
>   = (residualMap (prefixEdges m) hARRm).Face_mk c₂.1
> ```
> i.e. the new straight arc (edge `m`, inserted last) connects `p₁,p₂` through a
> single complement region of `prefixEdges m`, so both entered corners bound the
> same face.

This is an **equality** (the SameRegion connectedness direction). It is the
*only* geometric input the formal-`dr` `hgeo` needs; everything else (formal fresh
`Wleft,Wright`, `hregion` via `hconst m`, `hsame`, `hvertex`, the bundle assembly
via `nonempty_prefixStepCrosscut_of_data`) is sorry-free / combinatorial.

### 5.1 Two CONSTRUCTIBLE routes to A1★ (both mathlib-sufficient, no Jordan)

**Route β (combinatorial-target, preferred).** Supply `Face_mk c₁ = Face_mk c₂`
directly and convert via `hconst m` (§3.3). The combinatorial cotree machinery
already in the repo is built around exactly this shape:
- `exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block_of_treePrefix_incidence`
  (`RM:9670`, sorry-free) takes the co-faciality `Face_mk c₁ = Face_mk c₂` as its
  `hface` hypothesis (`:9759`) and produces the step. **It consumes co-faciality;
  it does not produce it** — so it relocates the obligation to `hface`, the same
  EQUALITY. (This lemma currently has 0 callers — it is an available alternative
  to the `dr`/`hgeo` route, also gated on A1★.)
- The split-pool transport lemmas `VertexGraph.lean:2149`/`:2210`
  (`faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_…`) likewise
  **take `hsame : SameCycle c₁ c₂` as a hypothesis** (`:2162`/`:2214`). The whole
  combinatorial cotree layer consumes co-faciality.

  ⇒ **There is no purely-combinatorial *producer* of A1★ in the repo** (PROVEN by
  the consumer-only structure of `RM:9670`, `VG:2149`, `VG:2210`). Co-faciality is
  a genuine geometric input (the arc bounding one region). It is **not** circular
  and **not** the distinctness obstruction.

**Route α (geometric-target).** Prove `drm c₁ = drm c₂` via `prefixStepSameRegion`
(`EdmondsSameRegion.lean:186`, sorry-free) + an `EdmondsCompatible (prefixEdges m)`
**at level `m`** (available — `m < m+1`, the induction is on increasing `m`, so
this is NOT the §3 level-`m+1` circularity). This is the original geometric design;
it needs the `hreal`/`dartSectorPoint` realization (`regionAt ∘ sector point`) and
hence the larger of the two open nodes. **Route β avoids this** by targeting the
combinatorial co-faciality directly. Route α is strictly more work; prefer β.

### 5.2 Is A1★ CONSTRUCTIBLE (no absent infra)? CONSTRUCTIBLE (mathlib-sufficient)

The geometric content of A1★ is the **equality/connectedness** half of the (MS)
crosscut correspondence: "the arc's interior lies in one component." Per
`edmonds-bridge-feasibility §5.5` and `B1-hsplit-design §6.2`, the equality half is
CONSTRUCTIBLE via `regionAt_eq_of_mem_isPreconnected` (`RegionFaceBridge.lean:131`,
sorry-free) on a preconnected witness `S` = open-arc-interior ∪ corner collars,
all inside `drawingComplementIn (prefixEdges m) R₀` (the arc is inserted last, so
its open interior avoids `arcUnion (prefixEdges m)`). This needs **no
Jordan/Schoenflies/Mayer–Vietoris** — it is the *equality* direction, where mathlib
v4.30 suffices. (The *distinctness* direction `crosscut_separates_global`, which
WOULD need absent infra, is the one the formal `dr` bypasses, §2.)

The honest residual *within* A1★ is the same `dartSectorPoint`/N1a′ sector-point
content already isolated in `crossing-lemma-A1-N1-dartsectorpoint.md` §2–§3
(the `angleAt`-interval wedge with its `drawingComplementIn` membership), needed to
name the entered corners' region for `regionAt_eq_of_mem_isPreconnected`. That is
CONSTRUCTIBLE (CONJECTURED no-absent-infra per the N1 doc) and is the **one**
geometric leaf the formal-`dr` route still consumes — but it is the *equality*
leaf, not the distinctness obstruction, and the `∅`-base harness is untouched.

---

## 6. What a Lean build would (and would not) confirm

I did **not** build (worktree cold; full `CrossingLemma` chain is multi-session).
The verdict rests on source-reading + two cross-model audits + confirmed mathlib
lemma names. A build would confirm one thing and is LOW-RISK:

- **Type-checking the formal-`dr` `hgeo` skeleton** — instantiate
  `nonempty_prefixStepCrosscut_of_data` (`EdmondsSameRegion.lean:380`) with formal
  fresh `Wleft,Wright` (the §2.3 construction), `hregion := hconst m c₁ c₂
  (face_mk_eq_iff.mp hcofacial).symm` with `hcofacial` a `sorry`-stub, and the
  unconditional `hvertex`. **Expected residual: exactly one `sorry`, `hcofacial :
  Face_mk c₁ = Face_mk c₂` (= A1★).** This would mechanically confirm §2+§3 (that
  formal sets + `hconst` discharge everything except A1★). It is a probe, not a
  proof — the `hcofacial` stub is the genuine residual, not a faked step.

This probe was **not** run here (cold worktree); it is the recommended first action
for the implementer and is expected to succeed by the type analysis above. It does
**not** alter the verdict — the residual it would expose (A1★) is already the
verdict's residual.

CONJECTURED (not build-verified here, consistent with the cited memories
`38R2S1`/`G2GJCE` and `route-fork §5`): the straight-arc PL-collar layer feeding
the eventual A1★ discharge (`exists_twoSidedPartition_of_straightArc`,
`exists_twoSidedPartition_prefixStep`) is sorry-free and axiom-clean. This does not
affect the §2/§3 verdicts (those concern the bundle algebra, not the partition).

---

## 7. Summary table (evidence levels)

| Claim | Level | Basis |
|---|---|---|
| A1 path reads bundle fields `c₁,c₂,hc,hregion,hvertex` only; `hinj` used combinatorially (`418`); `hcomp` not on bundle | **PROVEN** | `SzemerediTrotter.lean:4721-4740`, `RegionFaceBridge.lean:398-424`, `EdmondsConstruction.lean:91-128` |
| `edmondsCompatibleAtPrefix`/Lemma B/`EdmondsCompatible`-construction/`prefixStepSameRegion` have 0 A1-path call sites | **PROVEN** | grep over `lean/` |
| `prefixStepSameRegion_poolRegion_injective` inspects no geometry of `Wleft,Wright` | **PROVEN** | proof body `EdmondsSameRegion.lean:230-258` |
| `oldFaceRegion` values ∈ `drm`'s finite image | **PROVEN** | `oldFaceRegion_mk:100` (rfl) + `Set.finite_range` |
| Formal fresh `Wleft,Wright` satisfying `hWne`/`hWold` exist & are CONSTRUCTIBLE | **CONSTRUCTIBLE** | `Set.Finite.infinite_compl`, `Set.Infinite.nontrivial`, `Infinite.of_injective ∘ singleton_injective` — all confirmed in cached mathlib v4.30 |
| §16 "`poolRegion` forced injective ⇒ geometry" is conditional on `hcomp`; inert once `hcomp` dead | **PROVEN** | §16 text (`region-face-bridge-plan:801-812`) + `hcomp` 0 call sites |
| `hregion ⟺ co-faciality Face_mk c₁=Face_mk c₂` at level `m` (formal family) | **PROVEN** | `hconst`/`hsep` (`:475`/`:478`) + `face_mk_eq_iff` (`PlanarEdgeBound.lean:229`) |
| `hgeo` produces `hregion` from co-faciality via `hconst m`, non-circular, no `facePerm_sameCycle_of_sameRegion` | **PROVEN** | §3.3 construction; `hconst m` in scope; level-`m` only |
| `hvertex` is unconditional (no `hsame`) | **PROVEN** | `RM:3310` invoked at `RM:4313` without `hsame` |
| Co-faciality A1★ is the SameRegion EQUALITY, distinct from `crosscut_separates_global` (distinctness) | **PROVEN** | `B1-hsplit-design §7` (REFUTE "two faces of one fact"); equality vs inequality |
| No purely-combinatorial *producer* of A1★ in repo (cotree layer consumes co-faciality) | **PROVEN** | `RM:9670`/`VG:2149`/`VG:2210` take co-faciality as hypothesis |
| A1★ believed constructible (equality half, `regionAt_eq_of_mem_isPreconnected`, no Jordan); residual leaf = N1a′ sector point | **CONJECTURED** (no absent infra; not yet proven to leaf) | `RFB:131` sorry-free; `N1-dartsectorpoint §2-§3` |
| Harness needs NO edit (formal `dr` plugs into the existing `∅`-base harness) | **PROVEN** | `exists_dr_hstepCrosscut` consumes only `PerStepCrosscutInput`; `∅` base survives |
| **Overall: A1 REDUCES to one open co-faciality equality A1★ (CONJECTURED-constructible); `crosscut_separates_global` distinctness + `hreal` realization eliminated from the A1 path** | **VERDICT** | §0; §2 + §3 + §4 |

---

## 8. Structural assumptions used (stated explicitly)

- **Straightness** (every arc a `segmentArc`): used only for the eventual A1★
  discharge (the equality half via the PL-collar layer); the §2/§3 bundle algebra
  is straightness-independent.
- **Finiteness** (`Fin m × Bool` a `Fintype`): essential for §2.3 (`drm` finite
  image ⇒ fresh sets exist). Stated.
- **`Set (ℝ×ℝ)` infinite**: essential for §2.3; PROVEN from the singleton injection.
- **Crossing-free cotree insertion** (new arc's open interior avoids
  `arcUnion (prefixEdges m)`): used by A1★'s equality witness `S`. PROVEN-on-paper
  (`edmonds-sameregion §B2`).
- **NOT used / not needed**: any Jordan/Schoenflies/Mayer–Vietoris/plane-separation;
  the `crosscut_separates_global` distinctness; the `hcomp`/`hreal` realization
  invariant; any harness edit. These were required by the *geometric* `dr` design
  and are **eliminated** by the formal `dr`.
