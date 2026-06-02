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

- **L2 — corner local model.** At a PL vertex where two segments meet at angle, the
  punctured neighborhood splits into the "inside-the-angle" and "outside-the-angle"
  open sectors. *From scratch, elementary 2-D geometry; fiddlier than L1.*

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
1. **Action 0 + L1** (PL types, segment determinant functional) — ~1 session.
2. **L2 + L3** (corner model, global collar) — ~2–3 sessions. **The bulk and the
   genuine hardest node now.** L3 is the only node needing PL.
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

*Verification basis:* all PRESENT/ABSENT rows checked against
`.lake/packages/mathlib/Mathlib` at `v4.30.0` on 2026-06-02 (`grep` over the source
tree; declaration line numbers cited inline). Full route-(c) evaluation:
`nthdegree recall "Route (c) end-to-end evaluation"`.
