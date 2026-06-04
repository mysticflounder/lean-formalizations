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
   `sideForm = ±‖t−s‖²`).  Also DONE: the band's zero locus is exactly the open
   segment — `edgeBand_inter_sideForm_zero_eq_openSegment : edgeBand s t ∩
   {sideForm = 0} = openSegment ℝ s t` (per-edge analogue of `ball_inter_cornerLocus`,
   the part of the arc the band must exclude), resting on the collinearity lemma
   `sub_eq_footParam_smul_of_sideForm_zero : sideForm s t z = 0 → z − s =
   footParam s t z • (t − s)`.  The per-vertex sides are the existing L2 corner sectors
   (`convexSector`/`reflexSector`).  Also DONE: the **corner glue** packaged as
   `overlap_mem_convexSector_iff` / `overlap_mem_reflexSector_iff` — on the slab/disk
   overlap the incoming half-plane condition is automatic
   (`pos_turn_sideForm_of_overlap`), so sector membership is decided purely by the
   outgoing-edge sign `sign(τ·sideForm v b z)`; this is the bridge that makes a single
   global `g` well-defined across each corner.  Also DONE (cover foundations, the
   metric tooling that converts the tube radius into a foot-parameter change):
   `abs_dotp_sub_le_dist : |dotp(z−p,t−s)| ≤ (|t.1−s.1|+|t.2−s.2|)·dist p z` (metric
   companion of `abs_sideForm_le_dist`), `footParam_sub : footParam s t z − footParam
   s t p = dotp(z−p,t−s) / ‖t−s‖²`, and the Lipschitz bound `abs_footParam_sub_le :
   |footParam s t z − footParam s t p| ≤ (|t.1−s.1|+|t.2−s.2|)/‖t−s‖² · dist p z` —
   so a tube point within `δ₀` of a mid-edge spine point stays in the edge band once
   `δ₀` is small relative to the edge length and the slab cutoffs `αᵢ`.  Also DONE:
   the **Case A core** `mem_edgeBand_of_footParam_mem` — if `footParam s t p ∈ [α,1−α]`
   and `(|t.1−s.1|+|t.2−s.2|)·dist p z < α·‖t−s‖²` then `z ∈ edgeBand s t` (the
   tube-radius ⇒ band membership step) — and the **segment-coordinate bridge**:
   `footParam_mem_Icc_of_mem_segment` (`p ∈ segment ℝ s t ⇒ footParam ∈ [0,1]`),
   `dist_affineComb_src : dist (a•s+b•t) s = |b|·dist t s`, `dist_affineComb_tgt :
   dist (a•s+b•t) t = |a|·dist s t` (convert "foot near a vertex" into "metrically near
   that vertex" for the disk case).  **(iii) DONE** — the cover itself:
   `taperedTube_subset_bands_union_disks` proves `taperedTube R S δ₀ ⊆ (⋃ᵢ edgeBand
   (segSrc i)(segTgt i)) ∪ (⋃ⱼ ball (verts j) (ρ j))` for any spine `S ⊆ carrier`,
   under the explicit radius budget (three families of inequalities, `hband`/`hsrc`/
   `htgt`, parametrised by a cutoff `α>0` and per-vertex radii `ρⱼ`): trichotomy on the
   barycentric coordinate `b = footParam` of the spine point — middle `[α,1−α]` ⇒ edge
   band, `b<α` ⇒ source-vertex disk, `b>1−α` ⇒ target-vertex disk; axiom-clean.  The
   budget inequalities are deliberately left as hypotheses so the assembly discharges
   them by choosing `δ₀` small.  Helper `PolyArc.segTgt_ne_segSrc` (each edge
   non-degenerate).  **Budget step DONE:** `exists_delta_cover_budget` — given `α>0`
   and radii `ρⱼ` already exceeding `α·distᵢ` for each incident edge (`hρsrc`/`hρtgt`),
   there is a single `δ₀>0` satisfying all three budget families at once (`δ₀` = half
   the finite `Finset.inf'` over edges of `min(α·‖Δ‖²/‖Δ‖₁, ρ−α·distᵢ, ρ−α·distᵢ)`);
   plus `segDir_l1_pos` (each edge has positive ℓ¹ length).  So the cover now reduces
   to choosing `α` and `ρⱼ` (with `ρⱼ > α·distᵢ`).  **Incoming-edge glue DONE** (each
   edge's band overlaps *two* disks — its source disk where it is the corner's outgoing
   edge, and its target disk where it is the incoming edge): `convexSector_swap` /
   `reflexSector_swap` (sector symmetric under `a↔b`) and
   `overlap_mem_convexSector_iff_incoming` / `overlap_mem_reflexSector_iff_incoming`
   (apply the outgoing glue to the reversed corner `(b,v,a)`; pins the sector to the
   *incoming*-edge sign `sign(τ·sideForm a v z)`).  **(iv) IN PROGRESS — concrete
   plan (2026-06-02), 7 checkpoints C1–C7, hardest first.** The Plan pass found **three
   corrections** to the original sketch: (a) the standalone "tube witness is on edge 0"
   lemma is *false* (an adjacent edge-1 spine point near `v₀`'s perpendicular foot can
   be within `ρ₀+δ₀` of the endpoint for obtuse turns) — instead **fuse the pinch into
   the cover's `b<α` branch** (routing to `ball(verts 0)(ρ₀)` only happens via `hsrc`
   with `i=0`, where `p ∈ segCarrier 0` is in scope); (b) the edge slabs must be
   **narrowed to `footParam ∈ (α′,1−α′)`** (full `(0,1)` only gives `footParam<1`, but
   the glue thin-hyp needs `footParam ≤ 1−α` to get `α·‖a−v‖² ≤ dotp(z−v,a−v) =
   ‖a−v‖²·(1−footParam)`) — use a double cutoff `α′=α/2`; (c) choose `α` from a **global
   geometric minimum** (`α ≤ Rmin/(2(Lmax+1))`) to reconcile cover-wants-`ρ`-large vs
   disk-localisation-wants-`ρ`-small, and add hypotheses `IsCorner` at each interior
   vertex (not derivable from `PolyArc`) and `ρ₀ ≤ infDist(verts 0)(segCarrier 1)`.
   **C1 DONE (the endpoint pinch — highest-risk):** `l1_linf_le_two_l2sq`
   (`(|x|+|y|)·max|x| |y| ≤ 2(x²+y²)`), `l1_mul_dist_le_two_dotp` (geometric form:
   `(|t.1−s.1|+|t.2−s.2|)·dist s t ≤ 2·‖t−s‖²`), and
   `footParam_pos_of_close_to_seg` (`p ∈ segment ℝ s t` and `dist z p < dist p s / 2`
   ⇒ `0 < footParam s t z`) — at a call site the half-distance budget comes from the
   tube taper `dist z p < infDist p Rᶜ/2 ≤ dist p s/2` once the endpoint `s ∈ Rᶜ`; all
   sorry-free, axiom-clean.  **C2 DONE (narrowed bands + τ-selected sectors + glue):**
   `edgeBandMid s t α = {footParam ∈ (α,1−α)}` with `edgePlusMid`/`edgeMinusMid`
   (`isOpen_*`); `vertexPlus a v b = if 0<cornerTurn a v b then convexSector else
   reflexSector` and `vertexMinus` the other (`isOpen_*`,
   `disjoint_vertexPlus_vertexMinus`); the two algebraic bridges `dotp_sub_src`
   (`dotp(z−s,t−s) = ‖t−s‖²·footParam`) and `dotp_sub_tgt` (`dotp(z−t,s−t) =
   ‖t−s‖²·(1−footParam)`) that turn band foot bounds into the overlap-gate
   `0 < dotp(z−v,·−v)`; and the **four consistency lemmas**
   `mem_vertexPlus/Minus_of_outgoing/incoming` — on the band/disk overlap (gate + thin
   hyp) a `sideForm`-signed band point lands in the matching τ-selected sector (proof:
   `overlap_mem_*Sector_iff[_incoming]` + sign of `cornerTurn·sideForm` via
   `mul_pos`/`mul_neg_of_*`); all sorry-free, axiom-clean.  **C3a/C3b DONE (the
   narrowed-band cover keystone):** `mem_edgeBandMid_of_footParam_mem` (double-cutoff
   core: spine foot `∈ [α,1−α]` + `α/2` closeness budget ⇒ `z ∈ edgeBandMid s t (α/2)`,
   foot in the OPEN `(α/2,1−α/2) ⊇ [α,1−α]`); `footParam_swap_eq` (`footParam t s z =
   1−footParam s t z`); and **`taperedTube_subset_midBands_union_disks`** — every tube
   point lands in a narrowed edge band, an *interior*-vertex disk, or (at the two arc
   endpoints) an endpoint disk on the **forward** side of the incident edge (`footParam
   > 0` at the source, `< 1` at the target).  The endpoint forward sign is the **fused
   pinch**: routing to an endpoint disk happens only through the `b<α`/`b>1−α` branch of
   the endpoint-incident edge, where the spine witness `p` is on that edge and the tube
   taper gives `dist z p < infDist p Rᶜ/2 ≤ dist p (endpoint)/2`
   (`footParam_pos_of_close_to_seg` from C1, with `Metric.infDist_le_dist_of_mem` and
   `hsrc0 : verts 0 ∈ Rᶜ` / `hsrcL : verts (last) ∈ Rᶜ`); the target endpoint uses
   `footParam_swap_eq` on the reversed edge.  All sorry-free, axiom-clean.

   **ROUTING CHANGE (2026-06-03, Adam-approved).**  The planned "assemble `T⁺/T⁻` from
   local band+sector pieces glued by `exists_radius_thin`" (old C3c–C7) is **abandoned —
   it provably cannot close union(P2)+disjoint(P3) with one global `α/ρ/δ₀`.**  The
   metric vertex *disk* `ball(v,ρ_v)` is pinned **large** by the cover (`ρ_v > α·edgelen`)
   yet must be **small** for the glue to fire on the band/disk overlap (`ρ_v ≤ r =
   (α/2)·|sf|·P/(K·M+1)`); these reduce to the fixed condition `edgelen < |sf|·P/(2(K·M+1))
   ≈ (tan θ/2)·Q`, satisfiable only for `tan θ ≳ 2` and long edges — **not uniform**.  Both
   escapes fail (full sectors ⇒ disjoint breaks via mid-edge points in the opposite reflex
   sector; disk-confined sectors ⇒ union gap, since `L₂² ≤ L₁·L∞` always).  Verified by
   self-derivation + adversarial Plan pass.

   **NEW route — global orientation / corner-overlap sign function.**  (Literal mitered
   normal field `n(t)` + `sign(s)` is infeasible: `Plane` has the SUP norm and no
   `InnerProductSpace`, so no `orthogonalProjection`/`rot90`/injective-offset API.)  The
   side label is a single global sign: per-edge `sideForm` where `z` is near one edge,
   reconciled at corners by the existing L2 convex/reflex sector model where `z` is near a
   vertex.  The vertex region is the **corner-tube overlap** `{infDist z (edge i) < δ₀} ∩
   {infDist z (edge i+1) < δ₀}` — controlled by the **free** `δ₀`, not by `ρ_v`, which is
   what escapes the wall.  **KEYSTONE DONE:** `exists_delta_corner_confine` — for any
   target radius `r>0`, ∃ `δ>0` s.t. a point within `δ` of both incident edges is within
   `r` of the shared vertex (compactness: trim each edge to its `≥ r/2`-from-`v` part,
   disjoint compacts by `consecutive_meet`, separated by `σ`, take `δ = min(r/2, σ/2)`);
   sorry-free, axiom-clean.  So choosing `δ₀ ≤ δ(r)` with `r` the glue radius from
   `exists_radius_thin` makes the corner glue fire **by construction** on the only overlap
   it is needed.  STILL TODO: the per-edge "near one edge ⇒ `sideForm` sign well-defined"
   lemma; the global `collarPlus/Minus` defs (per-edge sign ∪ corner-overlap sector);
   OPEN + NONEMPTY (P1/P4); UNION `= T\carrier` (P2, via the C3b cover); DISJOINT (P3, via
   the keystone + the C2 glue); the `δ₀` budget choice.  Hypotheses: `IsCorner` at interior
   vertices (gives the finite `sin θ` min) + endpoints in `Rᶜ`.

   **THE `tan θ` WALL IS AN ARTIFACT — DISSOLVED (2026-06-03).**  Re-examining the wall:
   it came entirely from discharging the glue's thinness `hthin` via `exists_radius_thin`,
   whose bound `|sideForm v b z| ≤ M·dist v z` measures to the **vertex** (so `r ≈
   tan θ·edgelen`, angle-dependent).  But the literature's normal-distance estimate measures
   to the edge **line**: since `sideForm v b q = 0` for every `q ∈ [v,b]` (affine combo),
   `|sideForm v b z| ≤ M·infDist z [v,b] < M·δ₀` in a `δ₀`-tube — **independent of the corner
   angle** (the geometry is Euclidean via `dotp`/`sideForm`; only the metric `dist` is sup).
   The glue lemmas take `hthin` as a hypothesis, agnostic to its source, so we feed it from
   the strip width instead.  **PROVEN this session, sorry-free + axiom-clean:**
   `abs_sideForm_le_dist_of_mem_segment` (`|sideForm v b z| ≤ M·dist q z`, any `q ∈ [v,b]`);
   `abs_sideForm_le_M_infDist` (`≤ M·infDist z [v,b]`); `thin_of_infDist_outgoing` (produces
   the exact outgoing-glue `hthin` from `α ≤ footParam v b z ∧ infDist z [v,b] < δ₀` under an
   **angle-free** threshold `K·M·δ₀ < |τ|·α·P`); and `thin_of_infDist_incoming` (the `a↔b`
   mirror feeding `mem_vertexPlus/Minus_of_incoming`, proved as a direct instantiation of the
   outgoing lemma with its two arms swapped — both PROVEN sorry-free + axiom-clean 2026-06-03).
   CONSEQUENCE: the collar no longer needs metric vertex disks pinned to `r ≈ tan θ·edgelen`;
   the band/sector reconciliation fires from the tube half-width alone, uniformly.  Mathlib
   has no Jordan/crosscut/arc-separation lemma to import (searched) — the collar must be
   built, but this estimate removes the obstruction.  STILL TODO unchanged below, now with a
   clear path: bands carry an `infDist z (segCarrier i) < δ₀` strip certificate, vertex
   pieces are `τ`-selected sectors, all glued by `thin_of_infDist_*` (no `ρ_v` wall);
   `exists_delta_nonadjacent_tube_sep` kills non-adjacent overlaps; `exists_delta_corner_confine`
   remains available for the adjacent band–band case.

   **COLLAR ASSEMBLY — DEFINITIONS + P1 DOWN (2026-06-03).**  The two collar sides are
   now defined sorry-free + axiom-clean.  Ground set `W = taperedTube R S δ₀ \ β.carrier`
   (`isClosed_carrier` added).  `collarPlus/Minus β R S δ₀ α ρ := W ∩ (⋃ᵢ bandStrip±ᵢ ∪
   ⋃ᵥ sector±ᵥ ∪ endCapSrc± ∪ endCapTgt±)` where `bandStrip±ᵢ = edge±Mid(segSrc i)(segTgt
   i) α ∩ {infDist z (segCarrier i) < δ₀}` (strip certificate), `sector±ᵢ (hi1:(i)+1<n) =
   vertex±(segSrc i, segTgt i, segTgt (i+1)) ∩ ball(verts (i+1), ρ (i+1))` (interior shared
   vertices, indexed by the LEFT segment `i`), and the two end caps `ball(end, ρ) ∩ {foot in
   range} ∩ {±sideForm}` (single incident edge `firstSeg`/`lastSeg`, no corner).  **P1**
   (`isOpen_collarPlus/Minus`) PROVEN via per-piece openness lemmas.  STILL TODO: **P4**
   nonempty (scaled-edge witness), **P2** union `=W` (via `taperedTube_subset_midBands_union_disks`
   with cover-α := 2α, disk branch ⇒ sector via `compl_sectors_eq_cornerLocus` +
   `ball_inter_cornerLocus`, endpoint branches ⇒ end caps), **P3** disjoint (case bash:
   same-edge sideForm contradiction; non-adjacent via `exists_delta_nonadjacent_tube_sep`;
   adjacent band↔band / band↔sector / sector↔sector via `thin_of_infDist_*` glue +
   `disjoint_vertexPlus_vertexMinus` + ball disjointness; `δ₀` from a global min of the
   angle-free thresholds + non-adjacent-sep + corner-confine).

   **P3 PROGRESS (2026-06-03).**  Clean cases: `disjoint_bandStripPlus_bandStripMinus`
   (same edge), `disjoint_sectorPlus_sectorMinus` (same vertex), `stripSupport` +
   `disjoint_stripSupport_nonadjacent` (non-consecutive bands).  Adjacent band↔band:
   `not_mem_adjacent_band_strip` (corner-confine + footParam-Lipschitz, threshold
   `L_i·r ≤ α`, angle-free).  Adjacent band↔sector (the corner glue showcase):
   `bandStrip_incoming_mem_vertex±` / `bandStrip_outgoing_mem_vertex±` reconcile the
   band's `sideForm` sign with the sector side via `thin_of_infDist_incoming/outgoing`
   + `mem_vertex*_of_incoming/outgoing` (the outgoing case bridges `segSrc(j+1)=segTgt j`),
   giving `disjoint_bandStrip±_sector∓_incoming/outgoing` — each takes the angle-free `hδ`
   threshold as a hypothesis.  Separation cases: `infDist_lt_of_mem_vertexBall`,
   `disjoint_sectorPlus_sectorMinus_diff` (different vertices, ball budget),
   `disjoint_stripSupport_vertexBall_nonincident` (non-incident band↔sector via
   non-adjacent sep).  End caps (sign/ball): `disjoint_endCap*Plus_endCap*Minus`,
   `disjoint_endCap*±_bandStrip∓_self` (same-edge sign), `disjoint_endCapSrc*_endCapTgt*`
   (ball budget).

   **P3 COMPLETE (2026-06-03).**  Added the last cases and the master.  End-cap ↔
   non-incident band: `disjoint_vertexBall_stripSupport_of_budget` (infDist 1-Lipschitz,
   budget `ρ_end + δ₀ ≤ infDist v (segCarrier i)`) ⇒ `disjoint_endCap*±_bandStrip∓_nonincident`.
   End-cap ↔ sector: ball separation (`disjoint_endCap*Plus_sectorMinus`,
   `disjoint_sectorPlus_endCap*Minus`).  Mirror corner lemma `not_mem_adjacent_band_strip_src`
   (outgoing arm, shared vertex = edge `(i+1)`'s source, `footParam 0`) needed because
   band⁺↔band⁻ adjacency occurs in both orderings.  Then per-cell **all-indices** lemmas,
   each doing its index case analysis once: `disjoint_bandStripPlus_bandStripMinus_all`
   (trichotomy: same/adjacent×2/non-adjacent), `disjoint_bandStripPlus_sectorMinus_all` &
   `disjoint_sectorPlus_bandStripMinus_all` (incident incoming/outgoing + non-incident),
   `disjoint_sectorPlus_sectorMinus_all`, the cap↔band & cap↔sector `_all` wrappers.
   **MASTER `disjoint_collarPlus_collarMinus`**: shares the ground `taperedTube\carrier`,
   so reduces to the union-parts; `rcases` both 4-piece unions, dispatch the 4×4 grid.
   Admissibility bundle: `hα`, `hsep`/`hδ₀sep`/`hρsep` (non-adjacent sep at `δsep` ≥ `δ₀`
   and all disk radii), `hadj_tgt`/`hadj_src`, `hτ`/`hδin`/`hδout`, `hballs`,
   `hbudsrc`/`hbudtgt`.  Verified axiom-clean via `#print axioms`.

   **P3 EXISTENCE COMPLETE (2026-06-03), step (3) DONE.**  `exists_collar_disjoint`:
   for any `α > 0`, given the arc has no straight corners (`hturn`: `cornerTurn ≠ 0` at
   every interior vertex — a non-degeneracy the residual closure supplies), there exist
   `δ₀ > 0` and a constant disk radius `ρ` with `Disjoint (collarPlus …) (collarMinus …)`.
   Supporting pieces: `src_notMem_segCarrier`/`tgt_notMem_segCarrier` (endpoint on no
   non-incident edge); `exists_pos_disk_radius` (pairwise-disjoint disks, `inf'` over
   `offDiag`), `exists_pos_{src,tgt}_edge_sep` (endpoint-edge gaps), `not_mem_adjacent_band_strip_src`
   (the outgoing-arm mirror), `exists_corner_delta` (per-corner threshold: confine at
   `r = α/(1+L_c+L_{c+1})` + the `M/(K+1)` thinness thresholds, `M = ±cornerTurn·α·‖edge‖² > 0`).
   The assembly skolemizes the corner thresholds and sets `δ₀ = ρ = M5/2` (`M5` = min of
   corner-`inf'`, `δsep`, `dsrc/2`, `dtgt/2`, `ρ₀`).  All `#print axioms`-clean.

   **P2 COMPLETE (2026-06-03), step (4) DONE.**  `union_collarPlus_collarMinus`:
   `collarPlus ∪ collarMinus = taperedTube R S δ₀ ∖ carrier`.  Reverse inclusion is
   definitional (each side `= ground ∩ pieces`).  Forward runs the narrowed-band cover
   **at cover-`α` = `2α`** (so the cover's `α/2` narrowing lands in the collar's `α`-bands)
   and assigns each routed point a side.  The cover (`taperedTube_subset_midBands_union_disks`)
   was strengthened to additionally emit the band-strip metric certificate
   `infDist z (segCarrier i) < δ₀` (the spine witness `p ∈ segCarrier i` is in scope).
   Supporting: `vertexPlus_union_vertexMinus` (the τ-pair exhausts convex∪reflex);
   `mem_openSegment_of_sideForm_zero_ball`/`…'` (a `sideForm=0` ball point with the forward
   foot pinch is forced onto the segment — kills the endpoint `sideForm=0` case once
   `ρ_end ≤ ‖incident edge‖`); `mem_sectorPlus_or_sectorMinus_of_ball` (interior-vertex
   disk → sector via `compl_sectors_eq_cornerLocus` + `ball_inter_cornerLocus`, needs
   `hturn` + `ρ_v ≤` both incident edge lengths).  Band points: off-carrier ⇒ `sideForm ≠ 0`
   on the open-segment locus (`edgeBand_inter_sideForm_zero_eq_openSegment`), sign picks
   the strip.  All `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`.

   **P4 COMPLETE (2026-06-03), step (5) DONE — COLLAR FINISHED.**  `collarPlus_nonempty`
   / `collarMinus_nonempty`: each side contains the first-edge midpoint `firstMid β`
   (foot `1/2`) pushed `ε` along the edge normal (`±` chooses the side).  Needs
   `firstMid β ∈ S`, `0 < infDist (firstMid β) Rᶜ` (midpoint interior to `R`), `α < 1/2`.
   Witness validity is coordinate-free in `firstMid_push_in_ground` (point within the
   tube cap + region clearance + every-other-edge separation, off edge-0's line ⇒ in
   `taperedTube ∖ carrier` and `< δ₀` from edge 0); the push radius `B` comes from
   `exists_firstMid_radius` (`inf'` over edges, guarded at `firstSeg`), positivity from
   `firstMid_notMem_segCarrier` (the midpoint lies on no other edge: gap≥2 ⇒
   `nonadjacent_disjoint`; `k=1` ⇒ `consecutive_meet` forces `= verts 1`, but foot `1/2≠1`).
   The `ε·‖edge‖₁ < B` bound is sup-norm-safe (`Prod.dist_eq` + `max_le`).  All
   `#print axioms`-clean `[propext, Classical.choice, Quot.sound]`, 8477 jobs.

   **COLLAR (task iv) COMPLETE.**  All four `IsTwoSidedPartition`-style properties of the
   two collar charts are proved with concrete parameters (modulo the `hturn` no-straight-
   corners non-degeneracy + the per-instantiation hypotheses the assembly discharges):
   P1 `isOpen_collar{Plus,Minus}`, P2 `union_collarPlus_collarMinus`, P3
   `disjoint_collarPlus_collarMinus`/`exists_collar_disjoint`, P4 `collar{Plus,Minus}_nonempty`.
   NOTE: the collar charts are *not* connected — they feed the covering-map G-nodes
   (G1/G3/G4/Z1), which produce the connected `U,V` for `IsTwoSidedPartition`.
   **NEXT: G1/G3/G4/Z1** (two-chart cover ⇒ covering map; lift `id`; assemble
   `SplitsIntoTwo`; discharge the sorry at `PlaneArcSeparation.lean:377`).
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

## 7. G-node implementation — the abstract ℤ/2 separation lemma (in progress, 2026-06-03)

**Collar (L3) is COMPLETE** (`PLArc.lean`, `main` ≥ `19caa19`): `collarPlus`,
`collarMinus` open, disjoint, union `= taperedTube ∖ carrier`, each nonempty.
The G-nodes are now under construction in a **new file
`LeanFormalizations/PachDeZeeuw/CrossingLemma/PLCover.lean`**.

### Architecture refinement (supersedes the §6 piecewise-`g` and the §2 `Z1` framing)

The R2-resolved covering route is kept, but two framings are corrected:

- **Sides are connected COMPONENTS, not level sets `σ⁻¹{c}` (fixes a real gap).**
  A locally constant `σ : ↥(R∖β) → ZMod 2` has only *clopen* level sets — NOT
  obviously connected — so `IsTwoSidedPartition.preconnected_left/right` would
  **not** follow from `U := σ⁻¹{0}`. Instead set
  `U := connectedComponentIn (regionMinusArc) p⁺`,
  `V := connectedComponentIn (regionMinusArc) p⁻` for `p⁺ ∈ collarPlus`,
  `p⁻ ∈ collarMinus`. Preconnectedness is then **free**
  (`isPreconnected_connectedComponentIn`). `σ` is used **only** to prove `U ≠ V` /
  `Disjoint U V` (a path `p⁺ ⤳ p⁻` in `R∖β` would force `σ` constant —
  contradiction).
- **This ADDS one collar obligation the §6 design dropped: `collarPlus`,
  `collarMinus` each `IsPreconnected` (new "P5").** Needed so that "`z` reaches
  the collar by a path in `R∖β`" lands `z` in `U` or `V` exactly (not some third
  component). Geometric, via band↔sector overlap budgets; **not yet proved**.
  (The old §6 line "connectedness of `T⁺,T⁻` is NOT needed" applied only to the
  superseded `σ⁻¹`-as-sides framing.)

### The abstract lemma (all covering theory + simple connectivity isolated here)

> `B` open with `SimplyConnectedSpace ↥B` (+ `LocPathConnectedSpace`, free on
> `Plane`), `V₀ V₁ : Set B` open, `V₀ ∪ V₁ = univ`, `V₀ ∩ V₁ = Pp ⊔ Pm`
> (disjoint opens) ⟹ ∃ continuous `σ : ↥V₀ → ZMod 2`, `σ = 0` on `Pp`, `= 1` on `Pm`.

Proof = build the ℤ/2 double cover `E → B` by gluing the two trivial charts
`↥V₀ × ZMod 2`, `↥V₁ × ZMod 2` with transition `g` (`1` on `Pm`, `0` else), as
`E := Quotient (Setoid.ker key)`, `key (inl(x,s)) = (x,s)`,
`key (inr(y,t)) = (y, t+g y)`. `key` is surjective (`E ≅ B × ZMod 2` as a set,
with the coinduced cover topology); `p := fst ∘ key` is continuous (no `g`).
Then: `IsCoveringMap p` via `IsOpen.trivializationDiscrete` (`Covering/Basic.lean`)
on each chart + `IsFiberBundle.isCoveringMap`; lift `id : C(↥B,↥B)` with
`IsCoveringMap.existsUnique_continuousMap_lifts` (`Lifting.lean:421`, needs
`SimplyConnectedSpace`+`LocPathConnectedSpace`) ⇒ global section `F` ⇒ `σ` from the
clopen-agreement lemma `IsCoveringMap.eqOn_of_comp_eqOn` (`Covering/Basic.lean:375`).

**The `open_iff` (sheet-homeomorphism) condition works because a point forced into
both `W ⊆ V₀` and `V₁` lands in the overlap `Pp ⊔ Pm`, turning the apparent (non-open)
`W ∖ Pm` into the open `W ∩ Pp`.** This is the crux that makes the coinduced
topology a genuine cover.

**Status (2026-06-03):** `PLCover.lean` builds (8475 jobs, axiom-clean
`[propext, Classical.choice, Quot.sound]`). **The abstract separation lemma
`GlueData.exists_separating_fun` is COMPLETE** — the entire covering-theory +
simple-connectivity content (G1+G3) is done and geometry-free:

> `[SimplyConnectedSpace ↥B] [LocPathConnectedSpace ↥B]`, `hV₁ : IsPreconnected V₁`
> ⟹ `∃ σ : ↥V₀ → ZMod 2, Continuous σ ∧ ∀ x x', ↑x∈Pp → ↑x'∈Pm → σ x ≠ σ x'`.

Built: `GlueData`, `g`/`key`/`E`/`p`/`q`/`q₁`, `mk0`/`mk1`/`sheet0`/`sheet1` + all
coordinate & gluing lemmas; both charts' `trivializationDiscrete` conditions incl.
the `open_iff` crux; `triv0`/`triv1`; `isCoveringMap_p : IsCoveringMap p`;
`mem_sheet0_iff_q`/`mem_sheet1_iff_q1`; and `exists_separating_fun` (lift `id` via
`existsUnique_continuousMap_lifts` ⇒ section `F`; `σ := q∘F` locally constant on
`V₀` via open sheet-fibers; `q₁∘F` constant on connected `V₁`; the `g`-shift on the
overlap forces `σ` to differ across `Pp`/`Pm`). Note the **`IsPreconnected V₁`
hypothesis** (the collar `taperedTube` is connected — already proven in `PLArc`).

NEXT (instantiation + assembly, the remaining work): set `B = ↥R`, `V₀ =`
restriction of `regionMinusArc`, `V₁ =` collar, `Pp = collarPlus`,
`Pm = collarMinus`; supply the residual closure (PL representation of `β` + collar
budget bundles; `V₀ ∪ V₁ = univ`, `V₀ ∩ V₁ = Pp ⊔ Pm`), then assemble
`IsTwoSidedPartition` via **components** (G4 path-cut + collar connectedness P5;
`U = connectedComponentIn (regionMinusArc) p⁺`, etc.; disjoint via
`exists_separating_fun`) and discharge `PlaneArcSeparation.lean:377`.

## 8. Assembly — the abstract collar ⇒ partition reduction (DONE, 2026-06-03)

`LeanFormalizations/PachDeZeeuw/CrossingLemma/PLAssembly.lean` is sorry-free,
axiom-clean `[propext, Classical.choice, Quot.sound]`. It contains the single
theorem

```
exists_twoSidedPartition_of_collar
  {R C T Tp Tm : Set Plane}
  (hR : IsOpen R) (hRsc : IsSimplyConnected R) (hC : IsClosed C)
  (hT_open : IsOpen T) (hTR : T ⊆ R) (hT_pre : IsPreconnected T)
  (hTp_open …) (hTm_open …) (hdisj : Disjoint Tp Tm)
  (hpart : Tp ∪ Tm = T \ C)
  (hTp_pre : IsPreconnected Tp) (hTm_pre : IsPreconnected Tm)   -- P5
  (hTp_ne …) (hTm_ne …)
  (hcover : R ∩ C ⊆ T)
  (hG4 : ∀ z ∈ R \ C, (connectedComponentIn (R \ C) z ∩ (T \ C)).Nonempty)  -- G4
  : ∃ U V, IsTwoSidedPartition (R \ C) U V
```

It is **geometry-free** (no `PolyArc` dependency): it takes the collar sides `Tp`,
`Tm`, the tube `T`, and their topological facts as hypotheses, builds the
`PLCover.GlueData` over `B = ↥R` (`V₀ = R∖C`, `V₁ = T`, `Pp = Tp`, `Pm = Tm`),
runs `exists_separating_fun` to get `σ`, and assembles the partition as the two
**connected components** of `R∖C` through a `Tp`-point and a `Tm`-point — `σ` forces
them disjoint, `P5 + G4` force them to cover. `IsPreconnected ↥V₁` is transported
from `IsPreconnected T` via `IsInducing.subtypeVal.isPreconnected_image`; the
`σ`-on-the-shared-component contradiction goes through `IsLocallyConstant` pulled
back along the continuous lift `↥(R∖C) → ↥V₀`.

This **pins, with no slack, the only remaining geometric obligations**:

* **P5 — DONE (2026-06-03, `PLArc.lean`, sorry-free, axiom-clean `[propext,
  Classical.choice, Quot.sound]`).** `isPreconnected_collarPlus` /
  `isPreconnected_collarMinus`: each collar side is preconnected. Method (the "no-taper"
  regime): the geometric pieces are convex (bands = `edge±Mid ∩ Metric.thickening δ₀
  (segment)` via `Convex.thickening`; end caps = ball ∩ half-planes) or preconnected
  (sectors = `vertex± ∩ ball`, reflex case = two convex half-plane∩ball pieces meeting at
  the scaled reflected point); the pieces form a **linear chain** assembled by
  `isPreconnected_iUnion_fin_chain` over `collarChain±` (each band grouped with its
  successor connector). The four consecutive **overlaps** are explicit witnesses
  `liftPlus` (the foot-`c` point of an edge lifted ±ε along the normal): end-cap↔band
  (`overlap_endCap{Src,Tgt}{Plus,Minus}_bandStrip*`, foot `2α`/`1−2α`) and sector↔band
  (`overlap_sector*_bandStrip*_{src,tgt}` via the `mem_vertex*_of_{incoming,outgoing}`
  glue, ε chosen small enough for the glue's thin condition). Each side reduces to the
  hypothesis **`hsub`** (pieces ⊆ `taperedTube∖carrier` — the no-taper containment,
  `δ₀ ≤ ½·infDist over S`) plus the overlap budgets `ρ(succ i) > δ₀ + 2α·‖edge‖` and
  `α < 1/3`. `hsub` is discharged at instantiation (next bullet).
* **G4** — every `z ∈ R∖carrier` has its relative component meet `taperedTube∖carrier`
  (component-boundary-in-carrier topology; tractable, not Jordan-strength).
* **Collar instantiation** — produce one parameter bundle `(δ₀, α, ρ, S=arcInterior)`
  simultaneously satisfying P2 (`union_collarPlus_collarMinus`), P3
  (`exists_collar_disjoint`), P4 (`collar±_nonempty`), the **P5 side-conditions**
  (`hsub` no-taper containment `δ₀ ≤ ½·infDist over S`; overlap budgets
  `ρ(succ i) > δ₀+2α·‖edge‖`, which coincide with the existing P2 `hsrc`/`htgt`; `α<1/3`),
  and **G4**, feeding `exists_twoSidedPartition_of_collar` with `C = β.carrier`. Regime
  consistency checked on paper: pick `ρ` from P3, then `α` small (`< ρ/maxedge` and
  `< 1/3`), then `δ₀` small (no-taper + separation).
* **Residual closure (separate, NOT-attempted NO-GO)** — representing an arbitrary
  `SimpleArc` satisfying `ArcInRegion` as a `PolyArc` is Schoenflies-strength. The
  PL route discharges `exists_twoSidedPartition_of_polyArc`; wiring it to the
  arbitrary-arc `exists_twoSidedPartition_of_arc` at line 377 needs either that
  bridge or a signature change restricting the consumer to PL arcs (an Adam-level
  decision; see §0).

---

*Verification basis:* all PRESENT/ABSENT rows checked against
`.lake/packages/mathlib/Mathlib` at `v4.30.0` on 2026-06-02 (`grep` over the source
tree; declaration line numbers cited inline). Full route-(c) evaluation:
`nthdegree recall "Route (c) end-to-end evaluation"`.
