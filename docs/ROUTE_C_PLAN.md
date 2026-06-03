# Route (c) plan — discharging `exists_twoSidedPartition_of_arc`

**Target.** The sole on-path `sorry` of the crossing-lemma geometric residual:

```
theorem exists_twoSidedPartition_of_arc {A R : Set Plane} {β : SimpleArc Plane}
    (h : ArcInRegion A R β) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β) U V
```
(`LeanFormalizations/PachDeZeeuw/CrossingLemma/PlaneArcSeparation.lean:377`)

**Route (c)** = *direct plane topology*: build a side-invariant `σ : R∖β → ℤ/2`
and read the two sides off as `σ⁻¹{0}, σ⁻¹{1}`. The two competing routes —
(a) Riemann mapping + Carathéodory boundary correspondence, (b) Jordan/Schoenflies
— both rest on mathlib API that does **not** exist in v4.30 (verified below) and are
out of scope.

This document fixes (i) the **decisive precondition** that makes route (c)
tractable, (ii) the **node DAG** of the proof for PL arcs, (iii) a complete
**external-dependency ledger** (every mathlib declaration relied on, marked
PRESENT or ABSENT/FROM-SCRATCH), (iv) the **architectural gap** this residual does
*not* close, and (v) sequencing + go/no-go.

Verified against mathlib `v4.30.0` (`lean-toolchain`, `lake-manifest.json`), source
at `.lake/packages/mathlib/Mathlib`, on 2026-06-02.

---

## 0. The decisive precondition: restrict to PL arcs

For an **arbitrary continuous** simple arc `β`, the local node L3 below (two-sided
collar / normal form of the arc near an interior point) is Schoenflies-strength —
flagship-adjacent, **no mathlib support**, a research project in itself. Route (c)
is **NO-GO solo** for arbitrary continuous arcs.

For a **polygonal (PL)** arc, L3 collapses to explicit half-plane geometry (sign
of a 2×2 determinant) and the whole residual becomes PROVEN-tractable. The lever
is therefore: **restrict `SimpleArc` to a PL subtype for this lemma and never pay
the Schoenflies cost.**

This is free downstream **only if** the consumer of the crossing lemma can be
restricted to PL/straight-line drawings. {{UNVALIDATED}} Status of that check:
- The Szemerédi–Trotter consumer (`SzemerediTrotter.lean`) builds its multigraph
  with `stMultigraph`, whose edges are `segmentArc` — affine
  `(1-t)•p + t•q`, i.e. **straight segments**. So the ST application is PL-only:
  restricting the crossing lemma to PL arcs costs ST nothing. **VERIFIED**
  (`SzemerediTrotter.lean:373` `segmentArc`, `:449` `stMultigraph`).
- {{NEEDS_PROOF}} The crossing lemma's **amplification** path
  (`CrossingLemmaAmplification.lean`: `WeakAveragedBound → CrossingLemmaMultigraphStatement`)
  and the **drawing→map bridge** must preserve PL-ness of the drawings they
  manipulate. Not yet traced. See §4 risk R1.

**Action 0.** Introduce `structure PolyArc` (or `def IsPL (β : SimpleArc Plane)`):
a finite vertex list `p₀,…,pₙ` (`n ≥ 1`), consecutive segments, simple. Provide the
coercion `PolyArc → SimpleArc` and a PL variant of `ArcInRegion`. The residual is
then stated and proved for `PolyArc`. No external dependency (pure definition over
`ℝ × ℝ`; segments via `affineSegment`/`segment`, both in mathlib).

---

## 1. What route (c) does — and does NOT — finish

**Critical, easy to overclaim.** Discharging `exists_twoSidedPartition_of_arc`
does **not** by itself make the crossing lemma unconditional. Verified facts:

- `exists_twoSidedPartition_of_arc` / `PlaneArcSeparation.lean` is currently
  **unwired**: nothing imports it except the root aggregator
  (`grep`: the only hit outside its own file is
  `PachDeZeeuw/CrossingLemma.lean:14`, a re-export). The bridge files
  (`Abstractize`, `ResidualMap`, `ResidualMapProperties`, `RotationCoherence`)
  reach the planar/Euler edge bound through the **ARR rotation-system** route
  (`ArcsRotationRegular`, `residualMap`), **not** through arc separation.
- `WeakAveragedBound` has **no producer**: `crossingLemma_of_weakBound` consumes
  it as a hypothesis (`CrossingLemmaAmplification.lean:160`); nothing in the repo
  proves it. The span *geometry → faces → genus-0/Euler → planar edge bound on the
  crossing-free subgraph → `WeakAveragedBound`* is **unbuilt**.
- `ArcsRotationRegular` (ARR) is a **threaded, undischarged** hypothesis
  (`CrossingLemma.lean:241`).

So the dependency picture for an *unconditional* `CrossingLemmaMultigraphStatement`
is (each `←` = "needs"):

```
CrossingLemmaMultigraphStatement
  ← WeakAveragedBound                         [NO producer — unbuilt]
      ← planar/Euler edge bound on crossing-free subgraph   [PlanarEdgeBound exists]
          ← genus-0 combinatorial map of the drawing        [bridge: ARR route OR faces route]
              ← (faces route)   exists_twoSidedPartition_of_arc   ← THIS PLAN
              ← (ARR route)     ArcsRotationRegular discharge      [separate, undischarged]
```

**Conclusion.** This plan addresses the *faces-route* geometric residual. Even on
full success, two further large obligations remain before the crossing lemma is
unconditional: **(B)** wire faces → genus-0 → `WeakAveragedBound` (or discharge
ARR for the other route), and **(C)** confirm/produce `WeakAveragedBound`. Those
are out of scope here but are listed in §4 so the path is honest end-to-end.

---

## 2. The route-(c) node DAG (PL arcs)

The §3 componentology of `PlaneArcSeparation.lean` is already PROVEN sorry-free and
reduces the goal: once we exhibit a `σ` giving a `SplitsIntoTwo (regionMinusArc R β)`,
`splitsIntoTwo_iff_isTwoSidedPartition` (PROVEN, `:293`) hands back the
`IsTwoSidedPartition`. `regionMinusArc_isOpen` (PROVEN, `:358`) supplies openness,
and `Plane` is locally connected (`IsOpen.locPathConnectedSpace`, PRESENT). So the
**entire remaining content is constructing `σ` and proving its three properties.**

### Local nodes — the collar (where PL pays off)

- **L1 — segment side functional.** For an open segment `s` with endpoints `a,b`,
  the signed area form `D(z) = (b₁−a₁)(z₂−a₂) − (b₂−a₂)(z₁−a₁)` is a nonzero
  continuous **linear** functional whose sign splits a tubular slab around `s` into
  two open half-slabs. *No inner product needed* — and note **`ℝ × ℝ` (the `Prod`
  type used as `Plane`) carries NO `InnerProductSpace` instance** (the inner
  product lives on `WithLp 2 (ℝ×ℝ)` / `EuclideanSpace`, see ledger D7); the
  determinant form sidesteps that entirely. *From scratch, trivial.*

- **L2 — corner local model. CORE PROVEN ✅ (2026-06-02, `PLArc.lean` §L2).** At a PL
  vertex `a → v → b` with genuine turn `τ := sideForm a v b ≠ 0` (`IsCorner`), the
  complement of the two rays splits *globally* into `convexSector` (inside the turn,
  `{0 < τ·sideForm a v z ∧ 0 < τ·sideForm v b z}`) and `reflexSector` (outside,
  `{τ·sideForm a v z < 0 ∨ τ·sideForm v b z < 0}`). Both proven **open, disjoint,
  nonempty, and connected** (`isOpen_/disjoint_/isConnected_convexSector` &
  `_reflexSector`) — the convex sector via half-plane intersection convexity, the
  reflex sector via `IsPreconnected.union` of two half-planes meeting at the
  reflected point `3v − a − b`. **Fully algebraic, no `arg`/`Complex`/disk** — much
  cleaner than the originally-anticipated angular/sector analysis (the reflex side
  was the feared part; it reduces to "union of two convex sets sharing a point").
  Axiom-clean `[propext, Classical.choice, Quot.sound]`. *Remaining L2 piece:* the
  corner-locus identity `(convexSector ∪ reflexSector)ᶜ = ray(v→a) ∪ ray(v→b)`
  (mechanical ray parametrisation), deferred to the L3 tube localisation.

- **L3 — global collar of `arcInterior β`.** Glue L1 over each open segment and L2
  over each interior vertex into a single open neighborhood `T ⊇ arcInterior β` with
  `T ∖ β = T⁺ ⊔ T⁻`, each piece open, **connected**, with a continuous side map
  `T ∖ β → ℤ/2`. This is the PL "tubular neighborhood theorem for an arc." **No
  mathlib analog** (no tubular-neighborhood API for plane sets). *From scratch — the
  bulk of the local work, ~2 sessions.* Note: endpoints of `β` lie on `∂R`, i.e.
  **outside** `R`, so the collar only ever needs the *interior* of the arc — no
  endpoint normal form is required (this is the simplification the crosscut
  hypothesis buys).

### Global nodes — the invariant

> **R2 resolved (2026-06-02) — the covering construction, corrected.** The prior
> framing (covering "lives on `R∖β`", crux = "odd-crossing loop not
> null-homotopic", risk of needing PL transversality) was **wrong on the engine**.
> The corrected, mathlib-supported construction below makes the side cover a genuine
> covering map of **all of `R`** and obtains homotopy-invariance for free. See §4 R2
> and the memory `nthdegree recall "R2 covering construction"`.

- **G1 — the side double cover of `R` (corrected).** Cover `R` by two open charts:
  `U₁ :=` the collar `T` (an open neighborhood **containing all of `β`**, connected,
  from L3) and `U₀ := R∖β`. Then `U₀ ∪ U₁ = R` (β's endpoints are on `∂R`, outside
  `R`) and `U₀ ∩ U₁ = T∖β = T⁺ ⊔ T⁻`. Build `E → R` by gluing the trivial double
  covers `U₀×ℤ/2` and `U₁×ℤ/2` along the overlap with transition `0` on `T⁺` and the
  flip on `T⁻` (locally constant; trivial cocycle — only two charts). **Crucially `E`
  is a covering map over *all* of `R`, including over `β`, because over the collar
  chart `U₁ ⊇ β` the cover is trivial** — the nontriviality is entirely in the
  overlap transition. No branching; mathlib's covering API applies to `R` directly.
  *Construction from scratch (give the two `Trivialization`s ⇒ `IsCoveringMap`,
  D3a), elementary given L3.*

- **G3 — `σ` is well-defined and takes both values (was "the crux"; now plumbing).**
  `R` is `SimplyConnectedSpace` (`IsSimplyConnected.simplyConnectedSpace`, D1) and
  `LocPathConnectedSpace` (`IsOpen.locPathConnectedSpace`, D7). Apply
  `IsCoveringMap.existsUnique_continuousMap_lifts` (D5) to the **identity**
  `id : R → R` to get a global continuous section `F : R → E` with `p∘F = id` — i.e.
  the cover is trivial. Define `τ : E → ℤ/2` by `τ(e) = 0 ↔ e = F(p e)`; it is
  continuous because two continuous lifts agree on a **clopen** set
  (`IsCoveringMap.eqOn_of_comp_eq` / `isSeparatedMap` + `isLocalHomeomorph`, D5a).
  Set `σ := τ ∘ s₀` where `s₀` is the construction sheet-`0` section over `U₀=R∖β`.
  The overlap transition forces `σ|T⁺ = c` and `σ|T⁻ = c+1` (both values attained).
  **`IsSimplyConnected R` is consumed exactly once, at the lift of `id`; homotopy
  invariance is automatic — no monodromy bookkeeping, no intersection number, no
  transversality.**

- **G2 — `σ` is locally constant** (continuous into discrete `ℤ/2`). Immediate: `τ`
  is continuous (G3) and `s₀` is continuous, so `σ` is continuous. *Follows from G3.*

- **G4 — each side is connected / at most two components** (Node D). Every
  `z ∈ R∖β` is joined inside `R∖β` to `T⁺` or `T⁻`: `R` is open & connected (a
  component of `Aᶜ`), hence path-connected (`IsOpen.isConnected_iff_isPathConnected`,
  D6); take a path in `R` from `z` to a collar point and cut it at first entry to the
  closed collar — the initial segment avoids `β` (β meets `R` only inside `T`), landing
  in `T⁺` or `T⁻`. With `σ` locally constant (G2), `σ⁻¹{c}` and `σ⁻¹{c+1}` are then
  exactly the two path-components. *From scratch; supported by the path API (D6, D8) +
  L3. Hardest remaining after L3.*

### Assembly

- **Z1.** `U := σ⁻¹{0}`, `V := σ⁻¹{1}`; assemble `SplitsIntoTwo` from G2–G4, then
  `splitsIntoTwo_iff_isTwoSidedPartition` (PROVEN) closes the goal. *Plumbing.*

```
L1 ┐
L2 ┼─► L3 ─► G1 ─► G3 ─► G2 ┐
   │         (cover)  (lift id)  ├─► Z1 ─► exists_twoSidedPartition_of_arc
   └─► L3 ───────────► G4 ───────┘
(G3 consumes IsSimplyConnected R once — the lift of id:R→R; G4 consumes R path-connected.
 L3 = the collar = the only node needing PL; everything right of it is mathlib-supported.)
```

---

## 3. External-dependency ledger

Every non-trivial mathlib declaration route (c) relies on, each **VERIFIED PRESENT**
against the v4.30 source or **CONFIRMED ABSENT**. Absent ⇒ from-scratch ⇒ it is a
real external dependency to formalize.

### PRESENT — the engine is in mathlib v4.30

| # | Declaration | File (`.lake/packages/mathlib/Mathlib/…`) | Used by |
|---|---|---|---|
| D1 | `IsSimplyConnected`, `IsSimplyConnected.simplyConnectedSpace` | `AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:132,134` | hypothesis plumbing |
| D2 | `simply_connected_iff_paths_homotopic'` | `…/SimplyConnected.lean:94` | G3 |
| D3 | `IsCoveringMap := ∀ x, IsEvenlyCovered f x …` (construct via two `Trivialization`s) | `Topology/Covering/Basic.lean:287,40` | G1 |
| D3a | `Trivialization`, `IsEvenlyCovered`, `Trivialization.mk` (the chart data for G1) | `Topology/Covering/Basic.lean:40`; `Topology/FiberBundle/…` | G1 |
| D4 | `existsUnique_continuousMap_lifts [SimplyConnectedSpace A] [LocPathConnectedSpace A]` | `Topology/Homotopy/Lifting.lean:421` | G3 (lift `id : R→R`) |
| D5 | `IsCoveringMap.existsUnique_continuousMap_lifts` (covering-map form of D4) | `Topology/Homotopy/Lifting.lean:421` (via `IsLocalHomeomorph`) | G3 |
| D5a | section/lift agreement is clopen: `IsCoveringMap.eq_of_comp_eq`, `eqOn_of_comp_eq`, `const_of_comp`, `isSeparatedMap`, `isLocalHomeomorph` | `Topology/Covering/Basic.lean:369,377,373,348,339` | G3 (`τ` continuity) |
| D5b | *(unused now)* `monodromy_theorem`, `monodromy_bijective` | `Topology/Homotopy/Lifting.lean:152,400` | not needed by the corrected G3 |
| D6 | `IsOpen.isConnected_iff_isPathConnected` | `Topology/Connected/LocPathConnected.lean:163` | G4 |
| D7 | `IsOpen.locPathConnectedSpace` (⇒ `LocPathConnectedSpace` on open subsets of `Plane`) | `…/LocPathConnected.lean:160` | G1, G4, lifting hyps |
| D8 | `isPathConnected_iff_pathConnectedSpace`, `pathComponentIn`, path API | `Topology/Connected/PathConnected.lean:576,…` | G4 |
| D9 | `connectedComponentIn` / `IsPreconnected` API; `splitsIntoTwo_iff_isTwoSidedPartition` (in-repo, PROVEN) | `Topology/Connected/…`; `PlaneArcSeparation.lean:293` | Z1, §3 core |
| D10 | (optional) `BranchLogRoot.exists_continuousOn_eqOn_exp_comp`, `exists_continuousOn_pow_eq` | `Analysis/Complex/BranchLogRoot.lean:37,67` | alt. analytic `σ` (not primary) |

### ABSENT — from-scratch, the genuine external dependencies

| # | Needed fact | mathlib status (v4.30, verified) | Where |
|---|---|---|---|
| E1 | **PL two-sided collar / tubular nbhd of an arc** (L3) | No tubular-neighborhood API for plane sets; nothing comparable | L3 — bulk |
| E2 | **Corner local model** (L2) | None | L2 |
| E3 | **Construction of the side double cover** (two charts) + proof it `IsCoveringMap` (G1) | `IsCoveringMap`/`Trivialization` def/API present (D3/D3a); *this two-chart construction* absent | G1 |
| E4 | **`σ` definition + both-values** from the trivializing section `F` and the transition flip (G3) | lifting + clopen-agreement present (D4/D5/D5a); *this assembly* absent | G3 |
| E5 | **Each side connected via path-cut at first collar entry** (G4) | path API present (D6,D8); *the cut/push-off lemma* absent | G4 |
| ~~E6~~ | ~~PL general position / transversality / mod-2 intersection number~~ | **ABSENT** in mathlib — but **NO LONGER NEEDED**: R2's corrected covering construction gets homotopy-invariance from `existsUnique_continuousMap_lifts` (D4), so route (c) never builds intersection theory **or** needs simplicial approximation | *eliminated 2026-06-02* |

### Confirmed-absent flagships (out of scope, never attempted)

All verified by `grep` over the full `Mathlib/` tree returning **no declaration**:
Jordan curve theorem; Jordan–Schoenflies; Carathéodory boundary correspondence;
winding number; singular Mayer–Vietoris / excision (singular `H₀` and `π₀≃ZerothHomotopy`
exist, but no MV); Brouwer fixed point (not needed); o-minimal / `IsSemialgebraic`
plane separation. The partial private Riemann mapping (`RiemannMapping.lean`, step-2
only, all lemmas private) does **not** reach a biholomorphism-to-disk and is unusable
for route (a).

**Stale doc to fix:** the §6 gap report inside `PlaneArcSeparation.lean:393–463`
still cites v4.27 ("no `RiemannMapping`", "no `BranchLogRoot`"). It is partially
stale for v4.30 and should be corrected when L-nodes land. (Tracked, not yet done.)

---

## 4. Risks / unverified preconditions

- **R1 — PL preservation downstream — RESOLVED ✅ (2026-06-02).** Verified by
  source trace: the *only* arc constructor is `segmentArc` (straight,
  `SzemerediTrotter.lean:373`); the *only* `hCL` application site is `stMultigraph`
  (`SzemerediTrotter.lean:173`/`1231`); `crossingLemma_of_weakBound` and the bridge
  files (`Abstractize`/`ResidualMap`/`RotationCoherence`) construct **no** arcs (only
  numeric/abstract data). Restricting the crossing lemma to PL/straight drawings is
  **free end-to-end**.
- **R2 — cover vs simple connectivity — RESOLVED ✅ (2026-06-02), engine corrected.**
  The earlier worry (cover only on `R∖β`; need PL transversality / simplicial
  approximation) is **dissolved** by the two-chart construction: the collar chart
  `U₁ ⊇ β` is trivially covered, so `E → R` is a covering of **all of `R`**. Then
  `IsSimplyConnected R` ⇒ lift `id : R→R` (D4) ⇒ trivial cover ⇒ continuous `τ`
  (clopen agreement, D5a) ⇒ side function `σ`. Homotopy-invariance is free; **E6
  eliminated**. Residual mathematical risk now concentrated in **L3 (the collar)**.
- **R3 — `Plane = ℝ × ℝ` has no inner product (verified, D7 note).** Use the
  determinant form (L1), or transport to `EuclideanSpace ℝ (Fin 2)`. Decided: stay
  in `ℝ × ℝ` with the determinant form; no transport.
- **R4 — architectural gap (B)/(C) of §1 {{NEEDS_PROOF}}.** Even full success leaves
  `WeakAveragedBound` unproduced and the faces→genus-0→Euler span unbuilt. Route
  (c) is necessary, not sufficient, for an unconditional crossing lemma. *Unchanged.*

---

## 5. Sequencing & go/no-go

Estimate (sessions = ~150–200k context → one `/compact`):

0. **R1 + R2 gate — DONE ✅ (2026-06-02).** Both resolved; route (c) is GO. R2's
   resolution removed E6 and reduced the residual to L3 + plumbing.
1. **Action 0 + L1** (PL types, segment determinant functional) — DONE ✅
   (`PLArc.lean` §L1 + §Action 0, 2026-06-02).
2. **L2 core** (corner model: two sectors open/disjoint/connected) — DONE ✅
   (`PLArc.lean` §L2, 2026-06-02). Remaining: corner-locus complement identity,
   folded into L3. **L3** (global collar) — ~2 sessions, **the genuine hardest
   node**; the only node needing PL.
3. **G1** (two-chart side double cover ⇒ `IsCoveringMap`) — ~1 session.
4. **G3** (lift `id`, build `τ`, `σ`, both-values) — ~1 session. Now plumbing.
5. **G2 + G4 + Z1** (locally constant, each side connected, assembly) — ~1–2
   sessions.

**Total ~6–10 sessions** for `exists_twoSidedPartition_of_arc` on PL arcs;
**hardest node L3 (the collar); dominant variance now L3, not G3.** Discharging
the residual does **not** finish the crossing lemma (§1, R4).

**Work order (per project rules — hardest first):** with the gate cleared, the
honest hardest node is **L3 (the collar)**; G1/G3 reduce to it. Design L3 carefully,
then build bottom-up L→G→Z. Action 0 + L1 are the immediate first coding step.

---

## 6. L3 — detailed design (the hardest node, in progress)

Verified target shapes (read from `PlaneArcSeparation.lean` on 2026-06-02):

- `IsTwoSidedPartition W U V` requires: `IsOpen U`, `IsOpen V` (**ambient**, in
  the plane), `Disjoint U V`, `U ∪ V = W`, `U.Nonempty`, `V.Nonempty`,
  `IsPreconnected U`, `IsPreconnected V`. (Structure, 8 fields.)
- `ArcInRegion A R β` gives: `IsOpen R`, `R` a component of `Aᶜ`,
  `IsSimplyConnected R`, `arcInterior β ⊆ R`, `Disjoint (arcInterior β) A`,
  both endpoints `∈ frontier R` (crosscut).
- `regionMinusArc R β = R \ β.carrier`; `regionMinusArc_isOpen` PROVEN.

So the **end deliverable** is: a continuous `σ : ↥(regionMinusArc R β) → ZMod 2`
that (i) takes both values and (ii) has each fibre `σ⁻¹{c}` **preconnected**; then
`U := σ⁻¹{0}`, `V := σ⁻¹{1}` (pushed to ambient-open subsets of the plane via
`regionMinusArc_isOpen` + `σ` continuous into discrete `ZMod 2`).

### Minimal-need analysis (what each downstream node truly consumes)

- **G1 (cover) needs only**: `T` open with `arcInterior β ⊆ T ⊆ R`, `T` *connected*,
  and a *locally constant, non-constant* `g : ↥(T \ β.carrier) → ZMod 2` (i.e.
  `T \ β = T⁺ ⊔ T⁻`, both **open** and **nonempty** — **NOT** required connected).
  Then the two-chart double cover `E → R` (charts `R∖β`, `T`; transition `g`).
- **G3 (both values)**: `R` simply connected ⇒ cover trivial ⇒ coboundary
  `g = h₀|_overlap + h₁|_overlap`. `T` connected ⇒ `h₁` constant ⇒ `h₀ = σ` is
  non-constant on `R∖β` (because `g` is). *This is exactly where `T` connected and
  `g` non-constant are spent; `T⁺/T⁻` connectedness is never used here.*
- **G4 (each side preconnected)**: every `z ∈ R∖β` joins **within `R∖β`** by a path
  to `T⁺` or `T⁻` (path in `R` by `IsOpen.isConnected_iff_isPathConnected`, cut at
  first entry to the closed collar; the initial segment avoids `β`). `σ` constant on
  each path ⇒ `σ⁻¹{c}` path-connected ⇒ preconnected. **This** is the node that
  needs the side-reaching/path-cut lemma (E5).

### L3 sub-nodes (build order; hardest = the collar + local separation)

1. **`PolyArc → SimpleArc Plane` coercion** (PL parametrisation): continuous,
   injective piecewise-affine `Icc 0 1 → Plane`; relate `carrier`/`arcInterior` to
   `PolyArc.carrier` and the endpoint set. Plumbing, real. *(deps: none external)*
   **DONE (a)+(b)+(c) 2026-06-02, sorry-free, axiom-clean
   `[propext, Classical.choice, Quot.sound]`:**
   - (a) `PolyArc` carries the no-self-crossing fields `nonadjacent_disjoint`
     (non-consecutive closed segments disjoint) **and now `consecutive_meet`**
     (adjacent segments meet only at the shared vertex). Metric backbone PROVEN:
     `segCarrier_isCompact`, `exists_pos_nonadjacent_sep` (uniform `d_sep > 0`).
   - (b) **The parametrisation is built and PROVEN.** Ramp-sum form: `ramp` (clamp to
     `[0,1]`), `paramRaw` / `param` with `continuous_param`; `vertAt` telescoping
     helpers + `paramRaw_collapse_of` (per-interval affine collapse). Index
     assignment `idx` (clamped floor) with `locCoord ∈ [0,1]`, `param_mem_segCarrier`,
     `idx_mono`. Affine injectivity `affine_inj`/`affine_eq_left`/`affine_eq_right`.
     `injective_param` via the three-case argument (same segment / adjacent via
     `consecutive_meet` / non-adjacent via `nonadjacent_disjoint`). Coercion
     `PolyArc.toSimpleArc : SimpleArc Plane`.
   - (c) **Carrier relation PROVEN:** `range_toSimpleArc : Set.range β.toSimpleArc =
     β.carrier` (via `segCarrier_subset_range_param`). *Still TODO for sub-node 1:*
     the `arcInterior`/endpoint-set relations (relate `arcInterior β.toSimpleArc` to
     the open segments / interior vertices and the two endpoints `src`/`tgt`).
2. **The collar `T`**: open, connected, `arcInterior β ⊆ T ⊆ R`.
   **DONE 2026-06-02, sorry-free, axiom-clean `[propext, Classical.choice,
   Quot.sound]`.** Construction settled on the cleaner **tapered tube**
   `taperedTube R S δ₀ := ⋃ p ∈ S, ball p (min δ₀ (½·infDist p Rᶜ))` over the spine
   `S = arcInterior β` (NOT the per-segment slab / per-vertex disk union originally
   sketched — the union-of-balls form makes all four properties one-liners and the
   point-dependent radius `½·dist(p, Rᶜ)` keeps `T ⊆ R` even near the endpoints).
   Proved (all `Set`-generic in `S`, `R`):
   - `isOpen_taperedTube` — union of open balls.
   - `taperedTube_subset : taperedTube R S δ₀ ⊆ R` — **unconditional** (radius
     `≤ ½·infDist p Rᶜ` forces any `Rᶜ` ball-point to violate `infDist`).
   - `taperedRadius_pos` / `subset_taperedTube : S ⊆ taperedTube R S δ₀` — needs
     `S ⊆ R`, `R` open, `Rᶜ.Nonempty`, `δ₀ > 0` (positivity of `infDist p Rᶜ` via
     `IsClosed.notMem_iff_infDist_pos`).
   - `isPreconnected_taperedTube` / `isConnected_taperedTube` — additionally needs
     `S` preconnected + nonempty; each ball glued to the connected spine through a
     common base point (`isPreconnected_of_forall` + `IsPreconnected.union`).
   Spine facts for a generic `SimpleArc` also proved: `arcInterior_nonempty`,
   `isPreconnected_arcInterior` (continuous image of the connected `(0,1)`, via
   `isPreconnected_setOf_mem_unitIoo`). *(deps: `Metric.ball`/`infDist`, `IsOpen`,
   `convex_ball`, `isPreconnected_of_forall`, `IsInducing.subtypeVal`.)*
   **Still needed at assembly:** `Rᶜ.Nonempty` (from `frontier R ≠ ∅` via the
   crosscut endpoints) and `arcInterior β ⊆ R` (from `ArcInRegion.interior_subset`).
3. **Local separation `T \ β = T⁺ ⊔ T⁻`, both open & nonempty** (the crux). Glue:
   over a segment slab use L1 `leftSide/rightSide`; over a vertex disk use L2
   `convexSector/reflexSector`; consistency on overlaps via the sign of the shared
   segment's `sideForm` (L2's `cornerTurn` orientation). Sectors avoid the incident
   segments — **DONE** (`segment_av/vb_subset_compl_sectors`). Corner-locus
   complement `(convexSector ∪ reflexSector)ᶜ = cornerLocus` (the two rays,
   algebraic form) — **DONE** (`compl_sectors_eq_cornerLocus`). Disk-localisation
   `ball v r ∩ cornerLocus a v b = ball v r ∩ (segment[v,a] ∪ segment[v,b])` for
   `r ≤ dist v a, dist v b` — **DONE** (`ball_inter_cornerLocus`, §L3.1, axiom-clean;
   the one piece of genuine 2-D linear algebra is `exists_param_of_sideForm_eq_zero`:
   a point on the line through `a ≠ v` is the affine combination `(1-t)•v + t•a`).
   So the *per-vertex disk* algebra is complete: on a thin disk around `v`,
   `disk \ β = (disk ∩ convexSector) ⊔ (disk ∩ reflexSector)` — the two sectors are
   exactly the two sides. Non-emptiness of `T⁺,T⁻`: the sector points (e.g.
   `a+b−v`, `3v−a−b`) lie in `T` for a thin enough disk. *(deps: §L1/§L2 of
   `PLArc.lean`, all PROVEN.)*

   **CORRECTED GLOBAL DESIGN (2026-06-02) — the slabs must dodge the vertices.**
   A coordinate check refutes the naive "slab side = `sign(εᵢ·sideForm_i)` over the
   whole open edge" plan: with `v=0, b=(3,0), a=(2,1)` (convex left turn), the point
   `z=(0.1,0.2)` is on the `sideForm_(v,b)`-positive side of edge `(v,b)` yet lies in
   the **reflex** sector — near `v` the *other* edge `(v,a)` cuts across, so the slab
   label would contradict the disk's sector label. **Fix:** each segment slab covers
   only the *middle* of its edge, `slabᵢ := {z | αᵢ < footParam sᵢ tᵢ z < βᵢ}` with
   `0 < αᵢ`, `βᵢ < 1` chosen past the two vertex disks; the per-vertex **disk** owns
   the vertex neighbourhood; overlaps `slabᵢ ∩ diskᵥ` then sit where the foot is
   bounded away from `v`, where the two labels provably agree. Also: `Plane = ℝ×ℝ`
   has the **sup** norm and **no `InnerProductSpace`**, so do NOT use metric
   nearest-point (its foot is not the perpendicular); use the algebraic `sideForm`
   for the transverse side and an explicit-coordinate `dotp`/`footParam` for the
   tangential slab cut. There is **no** single global continuous side function (a PL
   arc has no continuous normal field — the normal jumps by the exterior angle at
   each corner), so `g` is *necessarily* glued from slab + disk pieces. The
   union-of-balls tube `T` (sub-node 2) is kept for topology; `T⁺/T⁻` are defined as
   a *separate* partition of `T\β` over the slab/disk pieces.

   **Foundation DONE (2026-06-02, sorry-free, axiom-clean):** `dotp`,
   `dotp_smul_left`, `dotp_self_pos`, `footParam`, `continuous_footParam`,
   `footParam_src = 0`, `footParam_tgt = 1`, and the key
   `footParam_affineComb : footParam s t ((1−c)•s + c•t) = c` (reads off the affine
   coefficient, so `footParam ∈ (α,β)` selects the middle of an edge). Foot
   decomposition recorded: with `d=t−s`, `sideForm s t z = μ·dotp d d` for
   `z−s = λd + μ·rot90 d`, so `sign(sideForm) = sign μ` is the perpendicular side.

   **OVERLAP-CONSISTENCY ENGINE DONE (2026-06-02, sorry-free, axiom-clean) — the
   genuine crux.** The single identity driving the corner glue (verified by `ring`):

       sideForm a v z · dotp(b−v,b−v)
         = sideForm a v b · dotp(z−v,b−v) + dotp(v−a,b−v) · sideForm v b z

   (`sideForm_cross_identity`).  From it, `pos_turn_sideForm_of_overlap`: on the
   overlap — foot strictly along edge `(v,b)` (`0 < dotp(z−v,b−v)`) and disk thin
   enough that `|dotp(v−a,b−v)|·|sideForm v b z| < |sideForm a v b|·dotp(z−v,b−v)` —
   one gets `0 < sideForm a v b · sideForm a v z`, i.e. `z` is pinned to the turn
   side w.r.t. the incoming edge.  Hence on the overlap
   `z ∈ convexSector ⟺ 0 < (sideForm a v b)·(sideForm v b z)`, so the slab label
   (`sign sideForm v b z`) and the disk label (convex/reflex) coincide.  This is
   exactly the vertex-region conflict resolved.  Proof is pure ordered-field
   algebra: the `τ·G` term dominates `|K·S|` via the thinness hypothesis (an `abs`
   bound + the identity, closed by `nlinarith`).

   **Remaining in sub-node 3:** (i) **DONE** — `exists_radius_thin`: for `b ≠ v`,
   `0 < α`, and a nonzero turn `sideForm a v b ≠ 0`, there is `r > 0` such that on the
   overlap `dist v z ≤ r ∧ α·‖b−v‖² ≤ dotp(z−v,b−v)` the thinness hypothesis of
   `pos_turn_sideForm_of_overlap` holds (explicit `r = |τ|·α·‖b−v‖² /
   (|dotp(v−a,b−v)|·(|b.1−v.1|+|b.2−v.2|)+1)`; proof via `abs_sideForm_le_dist` +
   ordered-field algebra). So a sufficiently small vertex disk makes the slab and disk
   labels agree on their overlap. (ii) **PARTIAL** — the per-edge local model is
   DONE: `edgeBand s t = {z | footParam s t z ∈ (0,1)}` (the slab strictly between the
   two endpoints, bounded away from the vertices) splits into the two open sides
   `edgePlus`/`edgeMinus` (`isOpen_*`, `disjoint_edgePlus_edgeMinus`,
   `edgePlus_union_edgeMinus : edgePlus ⊔ edgeMinus = edgeBand ∖ {sideForm = 0}`, and
   both `*_nonempty` via the midpoint pushed off by the edge normal, foot `= 1/2`,
   `sideForm = ±‖t−s‖²`).  The per-vertex sides are the existing L2 corner sectors
   (`convexSector`/`reflexSector`).  STILL TODO in (ii): the per-vertex `diskᵥ` (ball
   small enough to invoke `exists_radius_thin`) and the assembly of slabs+disks into a
   single global label `g`; (iii) show the pieces **cover** `T\β`; (iv) assemble
   `T⁺,T⁻` open, disjoint, union `= T\β`, both nonempty (the disk non-emptiness via the
   sector witnesses `a+b−v`, `3v−a−b`).
4. **G1** two-chart cover ⇒ `IsCoveringMap` (D3/D3a). 5. **G3** lift `id`, build
   `σ`, both values (D4/D5/D5a). 6. **G4** fibre-preconnected via path-cut (D6/D8,
   E5). 7. **Z1** assemble `IsTwoSidedPartition`; close
   `exists_twoSidedPartition_of_polyArc` (the PL form of the residual).

**Status (2026-06-02):** L1, L2 (incl. corner-locus complement
`compl_sectors_eq_cornerLocus`), sub-node-3's "sectors avoid incident segments",
**and the metric disk-localisation `ball_inter_cornerLocus`** are PROVEN sorry-free
and axiom-clean in `PLArc.lean`. **Sub-node 3 (local separation) is now
algebraically complete.** **Sub-node 1 — the `PolyArc → SimpleArc Plane` coercion —
is now PROVEN (parts (a)+(b)+(c)):** the `consecutive_meet` simplicity field, the
ramp-sum parametrisation with continuity (`continuous_param`) and injectivity
(`injective_param`), the coercion `toSimpleArc`, and the carrier relation
`range_toSimpleArc = carrier`; all sorry-free, axiom-clean
`[propext, Classical.choice, Quot.sound]`. **The only loose end in sub-node 1** is
the `arcInterior`/endpoint relations (not yet needed downstream). **Sub-node 2 — the
tapered collar tube `taperedTube` — is now PROVEN** (open, `T ⊆ R`, `S ⊆ T`,
connected; plus generic `arcInterior_nonempty`/`isPreconnected_arcInterior`), all
sorry-free and axiom-clean. What remains in L3 is **sub-node 3's metric assembly**
(realise `T \ β = T⁺ ⊔ T⁻` on the actual tube — the algebra is done, the glue of the
disk-localisation across the whole spine is not), then the global `g` and the
G-nodes.

### Tube + global side-function design (decided 2026-06-02, before coding sub-node 2)

The global side map `g : ↥(T \ β) → ZMod 2` is built **piecewise by the
sector/slab decomposition with a propagated orientation — NOT by nearest-point
projection** (the nearest point to a polyline is genuinely non-unique on the angle
bisectors, so a projection-based `g` is not even well-defined there; the
sector/slab `g` is, because both candidate nearest points give the same side).

- **Per-segment orientation `εᵢ ∈ {±1}`** propagated along the arc: fix `ε₀ := +1`;
  at each interior vertex `vᵢ` the turn `cornerTurn` fixes `εᵢ` from `εᵢ₋₁` so that
  "inside the turn" (`convexSector`) carries a single `g`-value across the corner.
  Because the arc is a **tree (no cycle)**, propagation has **no consistency
  obstruction** — this is why an arc, unlike a loop, needs no monodromy here.
- `g(z) := ⟦sign(εᵢ · sideForm(segᵢ, z))⟧` where `i` indexes the local link
  (slab or disk) containing `z`. Local constancy is a local property; overlaps
  (`disk ∩ slab`) agree by the §L2 algebra (`convexSector ⊆ τ-positive side of each
  incident segment`). Non-constancy: exhibit one point each side (sector witnesses
  `a+b−v`, `3v−a−b`). **Connectedness of `T⁺,T⁻` is NOT needed** (minimal-need
  analysis above) — only that `g` is locally constant and non-constant.
- **Tube radius is tapered, not uniform.** A uniform tube pokes outside `R` near the
  endpoints (which lie on `∂R`, so `dist(·, Rᶜ) → 0` there). Use a point-dependent
  radius `ρ(p) = min(δ₀, ½·dist(p, Rᶜ))` over `p ∈ arcInterior β`:
  `T := ⋃_{p ∈ arcInterior β} ball p (ρ p)`. Then `ρ p > 0` (as `p ∈ R` open),
  `ball p (ρ p) ⊆ R` (gives `T ⊆ R`), `arcInterior β ⊆ T`, `T` open, and `T`
  **connected** (each ball meets the connected `arcInterior β`). The cap `δ₀` is
  `< ½·` (min non-adjacent segment distance) and `< ½·` (min incident edge length),
  so each disk/slab sees only its own incident segment(s) — this is where the
  disk-localisation `ball_inter_cornerLocus` and the *no-self-crossing simplicity
  field* of `PolyArc` (sub-node 1, still TODO) are spent. {{NEEDS_PROOF}} the
  positivity of "min non-adjacent segment distance" needs that simplicity field
  (closed non-adjacent segments disjoint ⇒ positive distance by compactness).

Next concrete step: sub-node 1 (the `PolyArc → SimpleArc` coercion + the
no-self-crossing simplicity field that makes `d_sep > 0`), then sub-node 2 (the
tapered tube `T` with the four properties above).

---

*Verification basis:* all PRESENT/ABSENT rows checked against
`.lake/packages/mathlib/Mathlib` at `v4.30.0` on 2026-06-02 (`grep` over the source
tree; declaration line numbers cited inline). Full route-(c) evaluation:
`nthdegree recall "Route (c) end-to-end evaluation"`.
