# A1★ — is the "equality half" constructible in mathlib v4.30, and does it genuinely avoid `crosscut_separates_global`?

Stress-test of the orchestrator/`formal-dr-bypass` characterization of **A1★**:

> **A1★** := `(residualMap (prefixEdges m) hARRm).Face_mk c₁ = (residualMap (prefixEdges m) hARRm).Face_mk c₂`
> (the two ARR-rotation-chosen entered corners at the endpoints `p₁, p₂` of the newly inserted
> crossing-free cotree edge are **co-facial** in the level-`m` residual map).

Every file:line below was read against worktree `main` (HEAD `f115d37`, Lean v4.30). Claims are
labelled PROVEN / CONJECTURED / EMPIRICALLY VERIFIED / HEURISTIC. No `lake`/`lean` build was run
(read-only analysis); one toy-logic scratch check (`/tmp/a1star_logic.py`) is EMPIRICALLY VERIFIED
in scope and promotes nothing.

The load-bearing result is in §0 and §3. **It does not match the `formal-dr-bypass §5.2` claim**: the
candidate route's step (b) is the Edmonds region→face bridge, not a thin transport, so A1★ as posed
is **CONJECTURED-constructible-but-with-an-identified-gap**, and the cleanest honest target is the
**combinatorial** co-faciality A1★ proven from the arc germ + rotation system directly, bypassing the
region layer entirely (§4). The distinctness obstruction `crosscut_separates_global` is genuinely
eliminated from the live path (§1); that part of the prior analysis holds.

---

## 0. Headline verdict (the three adjudications)

**(1) Is A1★ the "equality half," provably distinct in difficulty from the distinctness half?**
**PARTLY.** A1★ is distinct *as a statement* from `crosscut_separates_global` — it is an equality
(`Face_mk c₁ = Face_mk c₂`) versus an inequality (`Wleft ≠ Wright` as global components), and they are
logically independent (PROVEN, §3.4). The distinctness obstruction is genuinely off the live A1 path
(PROVEN, §1). **But the candidate *proof* of A1★ in `formal-dr-bypass §5.2` does NOT avoid plane
topology by the route stated there.** That route proves a **region** equality
(`regionAt q₁ = regionAt q₂`) and then must cross to a **face** equality (`Face_mk c₁ = Face_mk c₂`);
the only repo/mathlib bridge for that crossing is `facePerm_sameCycle_of_sameRegion` = the
`EdmondsCompatible.region_separates` clause (PROVEN by exhaustive grep, §3.1), which is the *same*
Edmonds direction the project has flagged for the whole development. So step (b) of the candidate
route **re-encounters a region↔face bridge** — it is NOT a thin transport. (§3.2–§3.3.)

**(2) Is the candidate route's step (b) — region-equality ⇒ Face_mk-equality under ARR — constructible
in mathlib v4.30, or is it `facePerm_sameCycle_of_sameRegion` in disguise?** **It is
`facePerm_sameCycle_of_sameRegion` in disguise (PROVEN by grep + signature reading, §3).** There is no
other decl in the repo, and no mathlib lemma, that concludes `Face_mk =`/`SameCycle` from a
`regionAt`/`connectedComponentIn`/`IsPreconnected` hypothesis (§3.1, grep returns empty). The
`region_separates` clause is exactly the geometric Edmonds correspondence; constructing it for the
actual residual map is the multi-session open content the project isolated long ago
(`RegionFaceBridge §2`, `region-face-bridge-plan §16`). So **route α (geometric-target) does not
sidestep the bridge** — it consumes it.

**(3) Is there a route that avoids step (b) entirely — proving Face_mk co-faciality directly from the
ARR rotation system + arc germ, combinatorially/locally?** **This is the right target, and it is
OPEN (CONJECTURED-constructible, no proof, not even a paper proof to the leaf).** The honest A1★ is
the **combinatorial** statement "the two predecessor corners selected by the rotation system at the
two endpoints of a single arc that bounds one face are co-facial." The N1a′ `angleAt` sector point
(`N1-dartsectorpoint §2`) is a *device for naming a complement point in a face* — it is geared to the
**region** route (α), so it does **not by itself** deliver the combinatorial A1★; it would only feed
route α (and thus the bridge). A genuinely region-free producer of A1★ does **not exist in the repo**:
every cotree-layer lemma (`RM:4326`, `RM:9670`, `VG:2149/2210`) **consumes** co-faciality, never
produces it (PROVEN, §4.1). Whether the planar arc germ gives co-faciality without *any* region/plane
separation is **UNSETTLED** — I give the only candidate sketch I can construct (§4.2) and mark every
step that touches plane topology. The tempting shortcut "use `IsPlanar` at level `m`" is **PROVEN
circular** for any cotree `m` (planarity-at-`m` is downstream of A1★; §4.2 step 2), so it does not
rescue a combinatorial route.

**Net:** A1★ does reduce `hgeo` to a single open obligation, and `crosscut_separates_global`
distinctness + the `hreal` realization are off the live path (these prior findings are PROVEN and
hold). But the prior docs' label "A1★ is CONSTRUCTIBLE via `regionAt_eq_of_mem_isPreconnected`,
mathlib-sufficient, no Jordan" (`formal-dr-bypass §0/§5.2`, `edmonds-bridge-feasibility §5.5`) is
**too strong for the face-level statement**: that combinator proves region equality, and the region→face
step is the open Edmonds bridge. A1★ is best classified **CONJECTURED-constructible with one identified
residual = the region↔face equality bridge under ARR** (equivalently: prove co-faciality combinatorially
from the germ, §4). This is *lighter* than the distinctness obstruction in one precise sense (§5) but is
**not yet shown** to be mathlib-v4.30-closable.

---

## 1. The distinctness obstruction IS off the live A1 path (PROVEN — prior finding re-confirmed)

This part of the prior analysis is correct; I re-verified it independently.

- **`edmondsCompatibleAtPrefix` (the `hcomp` "genuine complement component" consumer,
  `EdmondsConstruction.lean:194`) has 0 call sites.** Grep over `lean/` returns only the docstring
  mention at `EdmondsConstruction.lean:43`. (PROVEN.) So the `hcomp` field
  (`:200`, `dr m hm d = regionAt … p`) — the geometric realization that drags in
  `crosscut_separates_global` — is never demanded.
- **The live SzemerédiTrotter cotree path** (`SzemerediTrotter.lean:4716–4740`, both sub-cases)
  consumes the bundle fields `c₁, c₂, hc, hregion, hvertex` only, via
  `regionSeparates_prefix_of_crosscut … hs_data.hregion` → `SameCycle` →
  `ResidualMapPrefixStepInsertion.sameFace`. (PROVEN, read.) `hinj`/`hfactor`/`poolRegion` are used
  *inside* `regionSeparates_prefix_of_crosscut` and only at the **combinatorial** line
  `RegionFaceBridge.lean:418` (`hinj hregion`). No field reads the *set values* of `poolRegion`.
- **Formal `Wleft, Wright`.** `prefixStepSameRegion_poolRegion_injective`
  (`EdmondsSameRegion.lean:217`, proof `:230–258`) discharges `hinj` using only `hsep`, `hWold`, `hWne`
  — never the *values* of `Wleft, Wright` (PROVEN, read full body). `oldFaceRegion` values lie in
  `drm`'s finite image (`oldFaceRegion_mk:100` is `rfl`; `Fin m × Bool` is a `Fintype`), so
  `hWold`/`hWne` are met by any two distinct sets outside that finite image; `Set (ℝ×ℝ)` is infinite,
  so such sets exist. (CONJECTURED-constructible — the four mathlib lemma names in `formal-dr-bypass
  §2.3` are plausible and standard, but I did not re-grep them this pass; tier (a)
  PROVEN-on-paper-modulo-trivial-assembly.)

**Consequence (PROVEN):** the larger node `crosscut_separates_global` (`Wleft ≠ Wright` as global
complement components, the (MS) crosscut-separation *distinctness* half, mathlib-/repo-absent per
`PlaneArcSeparation.lean:398–467`) is **not invoked** on the live path. `hgeo` does **not** need it.
This is real and is the value the formal-`dr` routing delivers.

---

## 2. What `hgeo` actually has to produce (PROVEN, from source)

The lone A1 `sorry` is `hgeo : CrossingLemma.PerStepCrosscutInput G' start hARRprefix`
(`SzemerediTrotter.lean:4648–4649`). Unfolding `PerStepCrosscutInput` (`EdmondsSameRegion.lean:471`):
for each cotree step `m ≥ start`, given the recursion's `drm : (Fin m × Bool) → Set (ℝ×ℝ)` and its two
invariants

```
_hconst : ∀ d₁ d₂, facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂     (EdmondsSameRegion.lean:475)
_hsep   : ∀ d₁ d₂, drm d₁ = drm d₂ → facePerm.SameCycle d₁ d₂     (:478)
```

produce `Nonempty (Σ' drm1, PrefixStepCrosscutData G m … drm drm1)`. The bundle
(`EdmondsConstruction.lean:91`) needs: `c₁, c₂`, `hc`, **`hregion : drm c₁ = drm c₂`** (`:106`),
`hvertex` (`:109`), `poolRegion`, `hinj`, `hfactor`. The assembler
`nonempty_prefixStepCrosscut_of_data` (`EdmondsSameRegion.lean:380`) reduces this to:
`c₁, c₂, hc, hsame, hvertex, hregion, Wleft, Wright, hWne, hWold` — all sorry-free downstream.

**`hregion` from A1★ via `_hconst` (PROVEN, logic verified).** With `c₁, c₂` the predecessor corners,
`A1★ : Face_mk c₁ = Face_mk c₂`, and `face_mk_eq_iff` (`PlanarEdgeBound.lean:229`, sorry-free:
`Face_mk a = Face_mk d₀ ↔ facePerm.SameCycle d₀ a`):

```
A1★ : Face_mk c₁ = Face_mk c₂
  ⟶ SameCycle c₂ c₁     (face_mk_eq_iff.mp, with a:=c₁, d₀:=c₂)
  ⟶ SameCycle c₁ c₂     (Equiv.Perm.SameCycle.symm, mathlib)
  ⟶ drm c₁ = drm c₂ = hregion   (_hconst, passed into hgeo by the harness)
```

The argument order and the symmetry step were checked on a toy quotient (`/tmp/a1star_logic.py`,
EMPIRICALLY VERIFIED on that model; the two mathlib facts are sorry-free). **This is non-circular at
the logic level:** `_hsep ∘ _hconst` recovers the same `SameCycle` evidence (up to proof
irrelevance); it does not manufacture a *new* A1★. So **A1★ is sufficient to build `hregion`** (and
hence, with formal `Wleft/Wright` from §1, the whole bundle), assuming `hvertex` is available
unconditionally — which it is: the corners and their angular `hpred₁/hpred₂` come region-silently from
`exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident` (`RM:4326`, conclusion
`:4339–4361`), whose only region-dependent output is the **conditional**
`(SameCycle c₁ c₂ → ResidualMapPrefixStepInsertion)` (PROVEN, read).

**So the reduction "hgeo ⇐ A1★" is PROVEN-on-paper** (modulo the formal-set assembly of §1). The open
question is entirely whether **A1★ itself** is constructible. That is §3–§4.

---

## 3. Adjudication of the candidate route (a)→(b): step (b) is the Edmonds bridge

The candidate route in the task and in `formal-dr-bypass §5.2`:

> (a) the new arc's interior lies in a single complement region of `prefixEdges m` (crossing-free ⇒
> preconnected interior ⊆ `drawingComplementIn`), giving **same-`regionAt`** at sector points near both
> corners via `regionAt_eq_of_mem_isPreconnected` (RFB:131);
> (b) bridge **"same `regionAt`" ⇒ "same `Face_mk`"** (co-facial).

### 3.1 There is exactly one region→face bridge in the repo, and it is `region_separates` (PROVEN by grep)

`regionAt_eq_of_mem_isPreconnected` (`RegionFaceBridge.lean:131`) has conclusion (read at `:134`):

```
regionAt G R₀ p = regionAt G R₀ q
```

a **region** (set) equality. To reach A1★ (a **face/Quotient** equality) one needs a decl of the shape
`regionAt … = regionAt … ⟹ facePerm.SameCycle …` (or `⟹ Face_mk … = Face_mk …`).

**Grep over all of `lean/` for any decl with a `regionAt`/`connectedComponentIn`/`IsPreconnected`
hypothesis concluding `SameCycle`/`Face_mk =` returns EMPTY** (excluding the unconditional card-1 base).
The *only* decls whose conclusion is `Face_mk d₁ = Face_mk d₂` in the bridge file are Lemma B
(`RegionFaceBridge.lean:336, :356`), and both are:

```
residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition … (E : EdmondsCompatible …)
  (hregion : E.dartRegion d₁ = E.dartRegion d₂) : Face_mk d₁ = Face_mk d₂
  := Quotient.sound (facePerm_sameCycle_of_sameRegion G E hregion)          -- :337
```

i.e. they route through `facePerm_sameCycle_of_sameRegion` (`:273`), which is **definitionally** the
`region_separates` structure projection of a *supplied* `EdmondsCompatible E` (`:278`,
`E.region_separates d₁ d₂ h`). (PROVEN, read.)

### 3.2 Therefore step (b) = `facePerm_sameCycle_of_sameRegion`, the open Edmonds direction (PROVEN)

Step (b), instantiated with `dr m c = regionAt … (sector point of c)`, is exactly: from
`regionAt q₁ = regionAt q₂` (= `E.dartRegion c₁ = E.dartRegion c₂` for the realization `E`) conclude
`SameCycle c₁ c₂`. That is `E.region_separates c₁ c₂` — **the hard Edmonds half**. It is **not**
constructible "from local rotation + arc-germ connectedness" by any existing lemma; constructing it
for the actual residual map is precisely the multi-session geometric track the project named
"genuinely novel content … not in Mathlib (no combinatorial-map ↔ planar-embedding / Edmonds
correspondence) and not in the repo" (`RegionFaceBridge.lean:30–33`). And `region_separates` for the
*concrete* residual map is the one whose inductive construction (`region-face-bridge-plan §16`,
re-derived in `edmonds-bridge-feasibility §5`) drags in the `hcomp` realization and the global
side-distinctness — i.e. it loops straight back into `crosscut_separates_global`.

**This is the gap in `formal-dr-bypass §5.2`.** That section asserts A1★ "is CONSTRUCTIBLE via
`regionAt_eq_of_mem_isPreconnected` … This needs no Jordan/Schoenflies/Mayer–Vietoris — it is the
*equality* direction, where mathlib v4.30 suffices." That sentence is **correct for the *region*
equality** `regionAt q₁ = regionAt q₂` and **incorrect as stated for the *face* equality A1★**: the
combinator delivers the former, and the doc silently identifies it with the latter. The face-level
A1★ is one Edmonds-bridge application past where `regionAt_eq_of_mem_isPreconnected` stops. (PROVEN by
the conclusion type at `:134` + the grep of §3.1.)

### 3.3 Is the region→face step *easier* for the entered corners than the full `region_separates`?

The full `region_separates` quantifies over **all** dart pairs; A1★ needs it only for **one** pair
`(c₁, c₂)` whose two anchor points are joined by the new arc inside one region. One could hope this
single instance is special enough to avoid the general bridge. I could not find an argument that it is.
The difficulty in `region_separates` is **not** the universal quantifier — it is the single implication
"same region ⇒ same face" for **any** pair, which already requires knowing that a complement component
corresponds to a unique face cycle (the Edmonds correspondence). Specializing to a pair joined by an
arc does not remove that: you still must convert "the two corners face the same component" into "the
two corners lie on the same face-boundary walk," and the face-boundary walk is a `facePerm`-cycle, not
a plane object. **No reduction of the single-pair region→face step to elementary mathlib is known
(HEURISTIC that it is hard; PROVEN only that no existing lemma does it).**

### 3.4 A1★ is logically distinct from `crosscut_separates_global` (PROVEN — distinctness ≠ equality)

This the prior docs get right and I confirm. A1★ is `Face_mk c₁ = Face_mk c₂` (an **equality**:
same-before-the-cut). `crosscut_separates_global` is `Wleft ≠ Wright` as global components (an
**inequality**: distinct-after-the-cut). `crossing-lemma-A1-B1-hsplit-design §7` refutes the "two
faces of one fact" conjecture (the two are logically independent). So **A1★ is not the distinctness
obstruction**, and discharging A1★ would not by itself discharge `crosscut_separates_global` (nor vice
versa). But "distinct from the distinctness obstruction" does **not** entail "avoids plane topology":
§3.2 shows the candidate *equality* route still hits the Edmonds bridge, whose concrete construction is
itself entangled with the same separation infrastructure (§3.2 last sentence).

---

## 4. The route that *could* avoid step (b): combinatorial co-faciality from the germ (OPEN)

### 4.1 No region-free producer of A1★ exists in the repo (PROVEN by grep)

Every cotree-layer lemma that mentions the predecessor corners **consumes** co-faciality:

- `exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident` (`RM:4326`): conclusion is
  the conditional `(SameCycle c₁ c₂ → step)` (`:4360`) — consumes A1★, does not produce it.
- `…_of_splice_face_eq` (`RM:4465`): takes `hface : Face_mk = Face_mk` (= A1★) as a **hypothesis**
  (`:4478`), converts to `SameCycle` (`Quotient.eq''.mp`, `:4509`). Consumer.
- The OnEdgeSet block lemma
  `exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block_of_treePrefix_incidence`
  (`RM:9670`) takes `hface` and has **0 callers** (grep) — a dead alternative, also gated on A1★.
- `faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_…` (`VG:2149/2210`) take
  `hsame : SameCycle c₁ c₂` as hypotheses. Consumers.

(PROVEN.) So **the entire combinatorial cotree layer treats A1★ as an *input*.** A1★ is a genuine new
obligation — it is neither circular (it is not derived from the harness's region(drm)⇒face producer,
§2) nor already proven anywhere. The watch for circularity the task asks for: **passed** — A1★ is not
derived from anything needing A1★, and the harness `_hconst`/`_hsep` only *transport* it, they do not
*establish* it.

### 4.2 The one candidate combinatorial sketch, with every plane-topology step flagged (HEURISTIC)

A region-free proof of A1★ would have to read co-faciality off the **face-boundary walk** of the
residual map at level `m`, using only: the rotation system (`ArcsRotationRegular`), the inserted arc's
two endpoints `p₁, p₂`, and the local germ of the arc at each endpoint (the N1a′ entered sector). The
combinatorial face is the orbit of `facePerm = σ ∘ α` (vertex-rotation ∘ edge-involution). A1★ says
`c₁` and `c₂` are in one `facePerm`-orbit. The honest difficulty:

1. **Identify each entered corner with a dart.** The entered sector at `pᵢ` (N1a′) selects an incident
   end; the rotation predecessor of the new dart there is `cᵢ` (`RM:4326` `hpredᵢ` does exactly this,
   region-silently). **No plane topology** — pure rotation-system bookkeeping. (PROVEN-available:
   `RM:4326` supplies `c₁, c₂` and `hpred₁, hpred₂`.)
2. **Show `c₁, c₂` lie on a common `facePerm`-orbit at level `m`.** This is the crux, and **this is
   where every candidate I can construct uses a plane fact.** The standard argument is: the arc bounds
   *one* face of the *planar* level-`m` map, and the two corners are the two ends of that face's
   boundary walk that the arc connects. "The arc bounds one face" is a **planar-embedding** statement —
   it presupposes the very combinatorial-map↔plane correspondence (Edmonds) that `region_separates`
   encodes. Without it, two corners joined by a plane arc through one *complement component* need not be
   on one *combinatorial* face unless the map is already known to be a faithful planar embedding at
   level `m`. **FLAG: plane topology (Edmonds correspondence at level `m`).** I have no combinatorial
   substitute.
   - **`IsPlanar (residualMap (prefixEdges m))` is NOT freely available here, and assuming it is
     circular (PROVEN).** One is tempted to use planarity-at-`m` as the missing combinatorial
     ingredient (Euler-genus-0 ⇒ face-walk structure). But in the live proof, planarity of the
     permuted map is derived at `SzemerediTrotter.lean:4741–4742` **from** `h_exists_target1` (built
     at `:4601`, containing the `hgeo` sorry at `:4648`) — planarity is **downstream** of `hgeo`.
     Per-prefix-level planarity for `m` in the cotree range is obtained via
     `residualMap_isPlanar_prefix_of_insertions_*`, whose cotree steps require
     `ResidualMapPrefixStepInsertion.sameFace` = `SameCycle` = A1★. So **getting planarity at level
     `m` (cotree range) already requires A1★** for all prior cotree steps. The only planarity↔
     co-faciality lemmas (`EdgeInsertion.lean:2088` `isPlanar_insertedEdgeMap_of_sameCycle`, `:2098`
     `sameCycle_of_isPlanar_insertedEdgeMap`) **consume** `SameCycle`, or produce it only from
     planarity of *both* the map and the inserted map — no producer of co-faciality from planarity-of-
     the-old-map-alone exists (PROVEN by read + grep). Hence a "use planarity-at-`m`" route is circular
     for any cotree `m`; only the **tree-prefix base** (`card Face = 1`, unconditional planarity) is
     genuinely available, and that base is already the harness's unconditional base case — it does not
     reach the cotree steps where A1★ lives.
   - One *might* try induction: the level-`m` map is built by the same prefix insertions, and at the
     tree base (`card Face = 1`) co-faciality is unconditional
     (`facePerm_sameCycle_of_card_face_eq_one`, sorry-free). But propagating co-faciality of the *new*
     arc's corners across each *prior* cotree insertion is exactly what
     `region_separates_prefixStep_sameFace` does **using `hinj`** — i.e. it needs the predecessor
     bundle's injectivity, which (for a *geometric* `dr`) reduces to side-distinctness =
     `crosscut_separates_global`. With a *formal* `dr`, `hinj` is free (§1), **but then the recursion's
     `drm` carries no geometric meaning, so "the new arc's corners are co-facial" cannot be read off
     `drm` — it must be supplied as A1★ at *each* step.** The recursion does not bootstrap A1★ for the
     current step from earlier steps; it only *transports* a supplied A1★. (PROVEN, from the harness
     structure §2 — the harness consumes one `hgeo` per step, each producing its own `hregion`.) So the
     induction does not eliminate the per-step A1★ obligation; it relocates it into `hgeo`, which is
     where we are.

**Conclusion of §4 (CONJECTURED / HEURISTIC):** a fully combinatorial, plane-topology-free producer of
A1★ is **not known and not in the repo**. The N1a′ sector point (§4.2 step 1) handles the *naming* of
the corners region-silently, but the *co-faciality* itself (step 2) has no region-free proof I can
construct; every route passes through the Edmonds correspondence at level `m`. The N1a′ object is
therefore **necessary but not sufficient** for A1★ — it feeds route α (the region route, §3), which
then needs the bridge.

---

## 5. In what precise sense A1★ is "lighter" than the distinctness obstruction (the steelman)

The prior docs' intuition that A1★ is *easier* than `crosscut_separates_global` is not baseless; here is
the defensible version (CONJECTURED).

- The **region equality** half of A1★ — `regionAt q₁ = regionAt q₂` — is genuinely
  mathlib-v4.30-constructible **without** Jordan/Schoenflies: it is `regionAt_eq_of_mem_isPreconnected`
  (`RFB:131`, sorry-free) on the preconnected witness `S` = open-arc-interior ∪ two corner collars,
  inside `drawingComplementIn (prefixEdges m) R₀`. The crossing-free insertion gives `S ⊆
  drawingComplementIn` (the new arc is added last; its open interior avoids `arcUnion (prefixEdges m)`;
  PROVEN-on-paper, `edmonds-sameregion §B2`). This needs only `IsPreconnected` + `connectedComponentIn`
  API and δ-separation (`infDist_pos`, finiteness) — **no separation theorem.** (CONJECTURED-
  constructible; this is the part the prior docs correctly identify as light, and it is real.)
- The **distinctness** obstruction `crosscut_separates_global` needs the *opposite* — that no
  preconnected complement set joins the two sides — which is the (MS) separation/π₀ content mathlib
  v4.30 lacks. Equality (find one connecting set) is constructive; distinctness (rule out all
  connecting sets) is the separation fact. So **at the region level**, A1★'s equality genuinely sits on
  the easy side. (PROVEN that equality vs distinctness have this asymmetry: `subset_connectedComponentIn`
  gives equality from a witness; there is no dual giving distinctness without separation.)

**The catch (§3.2):** A1★ is a **face** equality, not a region equality, and the region→face crossing
is the Edmonds bridge, which is *not* on the easy side. So the steelman establishes that **the region
sub-fact of A1★ is light**, not that **A1★** is light. The residual difficulty of A1★ is concentrated
entirely in the region→face bridge `region_separates` for the entered-corner pair (§3.3) — which is
open.

---

## 6. What is PROVEN vs CONJECTURED vs HEURISTIC (summary table)

| Claim | Level | Basis |
|---|---|---|
| `crosscut_separates_global` distinctness is OFF the live A1 path (`edmondsCompatibleAtPrefix`/`hcomp` 0 call sites; `hinj` combinatorial at RFB:418; formal `Wleft/Wright`) | **PROVEN** | grep + read `EdmondsConstruction:194/200/43`, `SzemerediTrotter:4716–4740`, `EdmondsSameRegion:217–258` |
| `hgeo ⇐ A1★`: with A1★ + formal sets, the whole bundle assembles; `hregion := _hconst c₁ c₂ (face_mk_eq_iff.mp A1★).symm` | **PROVEN-on-paper** | `EdmondsSameRegion:380/471–478`, `PlanarEdgeBound:229`, toy check `/tmp/a1star_logic.py` (logic only) |
| `c₁, c₂` + `hvertex` are produced region-silently (conditional on `SameCycle`) | **PROVEN** | `RM:4326` conclusion `:4339–4361` (conditional `:4360`), `hpred₁/hpred₂` angular |
| `regionAt_eq_of_mem_isPreconnected` concludes a REGION equality, not a face equality | **PROVEN** | `RegionFaceBridge:134` |
| The ONLY repo region→face bridge is `facePerm_sameCycle_of_sameRegion` = `EdmondsCompatible.region_separates`; no `regionAt-eq ⟹ SameCycle` decl exists | **PROVEN** | grep (empty); `RegionFaceBridge:273/278/336–337` |
| Candidate route step (b) ("same regionAt ⇒ same Face_mk") = the open Edmonds bridge, NOT a thin transport; `formal-dr-bypass §5.2` conflates region-eq with face-eq | **PROVEN** | §3.1–§3.2 (conclusion type + grep) |
| A1★ (equality) is logically distinct from `crosscut_separates_global` (inequality) | **PROVEN** | `B1-hsplit-design §7`; equality vs inequality |
| The REGION sub-fact of A1★ (`regionAt q₁ = regionAt q₂`) is mathlib-v4.30-constructible, no Jordan | **CONJECTURED-constructible** | `RFB:131` sorry-free + δ-separation; `edmonds-sameregion §B2` for `S ⊆ complement` |
| No region-free / purely-combinatorial producer of A1★ exists in the repo; the cotree layer consumes co-faciality | **PROVEN** | grep: `RM:4326/4465/9670` (`RM:9670` 0 callers), `VG:2149/2210` all consume |
| A1★ at the FACE level is constructible in mathlib v4.30 | **CONJECTURED, with an identified residual** (the region↔face equality bridge under ARR; no proof, no paper proof to leaf) | §3.3, §4.2 — every candidate hits the Edmonds correspondence at level `m` |
| The N1a′ `angleAt` sector point suffices for A1★ | **REFUTED as "suffices"** (it names the corners region-silently but does not give co-faciality; it feeds route α which needs the bridge) | §4.2 step 1 vs step 2 |
| A1★ is "the equality half, lighter than the distinctness half" | **PARTLY (CONJECTURED)** — true for its region sub-fact; the face-level statement still needs the Edmonds bridge | §3.2, §5 |
| "Use `IsPlanar (residualMap (prefixEdges m))` to get A1★ combinatorially" is circular for cotree `m` | **PROVEN circular** | `SzemerediTrotter:4741` (planarity from the `:4601` `hgeo` block); `EdgeInsertion:2088/2098` consume `SameCycle`; cotree planarity-at-`m` needs prior A1★ |

---

## 7. Structural assumptions (stated explicitly)

- **Straightness** (every arc a `segmentArc`): used by the region sub-fact's witness `S` (open arc
  interior ∪ collars ⊆ complement) and by N1a′. The bundle algebra of §1–§2 is straightness-independent.
- **Crossing-free last insertion** (new arc's open interior avoids `arcUnion (prefixEdges m)`):
  essential for the region sub-fact (`S ⊆ drawingComplementIn`). PROVEN-on-paper, `edmonds-sameregion §B2`.
- **Finiteness** (`Fin m × Bool` a `Fintype`): used for formal-set existence (§1) and δ-separation (§5).
- **NOT eliminated**: the region→face Edmonds bridge for the entered-corner pair (§3.2). Whether A1★ can
  be closed **without** it (combinatorially, §4) is the open question; if it cannot, A1★ needs
  `region_separates` for the actual residual map, whose construction re-touches the separation
  infrastructure the formal `dr` was meant to bypass.

---

## 8. What next (ranked)

1. **Settle §3.3 / §4.2-step-2 first: is single-pair co-faciality A1★ derivable from the planar
   level-`m` map without the full Edmonds `region_separates`?** This is the decisive fork and it is the
   hardest part, so it goes first (per project policy). Two concrete sub-questions, both UNKNOWN:
   - (a) Is there a `facePerm`-walk argument that places `c₁, c₂` on one orbit using only the rotation
     system + the arc germ? **NOTE: do NOT route this through `IsPlanar (residualMap (prefixEdges m))`
     — that is circular for cotree `m` (§4.2 step 2: planarity-at-`m` is downstream of A1★ for all prior
     cotree steps; confirmed by the `:4741`-after-`:4601` ordering and the consume-only planarity↔
     co-faciality lemmas `EdgeInsertion:2088/2098`).** The only non-circular structure available at the
     `hgeo` call site is: the tree-prefix base is planar/single-face (unconditional), and the level-`m`
     map is that base plus the *already-inserted* cotree arcs (each of whose co-faciality was the prior
     step's A1★). A region-free A1★ producer, if it exists, must read co-faciality off the
     **`facePerm = σ ∘ α` orbit combinatorics + the entered sectors** without invoking
     genus-0/planarity-at-`m`. I did not find such an argument and have no evidence one exists; this is
     UNKNOWN/OPEN combinatorics, not a known lemma. Treat (a) as a genuine open combinatorial question,
     not a lookup.
   - (b) If (a) has no answer, A1★ requires the region→face bridge ⇒ the geometric `region_separates`
     ⇒ `crosscut_separates_global` re-enters via the *concrete* `dr`. In that case the formal-`dr`
     bypass does **not** remove the obstruction; it only relocates it from `hinj` (distinctness) to
     `hregion` (the bridge). State that plainly and re-open `crosscut_separates_global` as on-path.

2. **Type-check the `hgeo ⇐ A1★` skeleton** (the `formal-dr-bypass §6` probe), with `A1★` a `sorry`-stub:
   instantiate `nonempty_prefixStepCrosscut_of_data` with formal fresh `Wleft/Wright`,
   `hregion := _hconst c₁ c₂ (face_mk_eq_iff.mp hcofacial).symm`, unconditional `hvertex`. **Expected
   residual: exactly one `sorry` = A1★.** This confirms §1–§2 mechanically and isolates A1★ as the
   single leaf. **FLAG FOR IMPLEMENTER: build and verify a scratch file with this skeleton; do not ship
   it — it is a probe.** Low risk; orchestrator's job (I did not run `lake`).

3. **Independently, prove the REGION sub-fact** `regionAt q₁ = regionAt q₂` (the light half, §5) as a
   standalone sorry-free lemma via `regionAt_eq_of_mem_isPreconnected` + δ-separation + the `S ⊆
   complement` witness. It is needed by route α regardless, and confirms the equality/connectedness
   direction is mathlib-sufficient. **FLAG FOR IMPLEMENTER:** lemma `regionAt_entered_corners_eq`
   (informal): the two entered-corner sector points lie in one preconnected `S ⊆ drawingComplementIn
   (prefixEdges m) R₀` ⇒ `regionAt q₁ = regionAt q₂`. This does **not** close A1★ (it stops one Edmonds
   step short, §3.2) but it is a grounded sublemma and de-risks route α.

4. **Do NOT ship N1a′ as if it closes A1★.** Per §4.2 it names the corners but does not give
   co-faciality. Build it only after fork (1) decides whether route α (region, needs N1a′ + bridge) or a
   combinatorial route (no N1a′) is the target.

Honest bottom line: **A1★ reduces `hgeo` to a single open obligation, and the distinctness obstruction
is off the live path — but A1★ is not yet shown to avoid the region↔face Edmonds bridge, and the
candidate `regionAt_eq_of_mem_isPreconnected` route proves a region equality that stops one Edmonds
step short of the face equality A1★ asserts.** The "equality half is mathlib-sufficient" label is
correct for the region sub-fact and not established for A1★ itself.
