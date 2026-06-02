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

- **G1 — define `σ : R∖β → ℤ/2`.** Recommended engine: the **side double cover**.
  Build a 2-sheeted space realizing the L3 side-flip across `β` and trivial sheets
  away from `β`; `σ` is the sheet-choice. *Construction from scratch* (mathlib has
  the `IsCoveringMap` *definition and lifting API* — ledger D3/D4 — but not this
  construction). The covering engine is what discharges the crux node G3 cleanly;
  see the route note below.

- **G2 — `σ` is locally constant** (continuous into discrete `ℤ/2`). Away from `β`:
  `σ` is constant on the trivial sheets. Across `β`: continuity is exactly the L3
  continuous side map. *From scratch, follows from L3 + G1.*

- **G3 — `σ` is well-defined / takes both values (the crux).** Equivalently: **a
  loop in `R` crossing the crosscut `β` an odd number of times is not
  null-homotopic in `R`.** This is the single irreducible hard fact; it is where
  `IsSimplyConnected R` is consumed. *Engine:* `monodromy_theorem` +
  `IsCoveringMapOn.existsUnique_continuousMap_lifts` — a null-homotopic loop has
  trivial monodromy in the side cover, but an odd-crossing loop flips the sheet
  (L3), contradiction. **mathlib supplies the monodromy/lifting machinery (D3–D5);
  the application to *this* cover is from scratch.** This node replaces the
  mod-2-intersection-number argument, which would otherwise require PL
  transversality / general position — **ABSENT** from mathlib (ledger D9). Choosing
  the covering engine is precisely what lets route (c) avoid building intersection
  theory.

- **G4 — each side is connected** ("at most two components", Node D). Every
  `z ∈ R∖β` is joined inside `R∖β` to `T⁺` or `T⁻`: take a path in `R`
  (`IsOpen.isConnected_iff_isPathConnected`, D6) from `z` to a collar point and
  push it off `β` into the collar (L3). Hence `σ⁻¹{i}` is path-connected.
  *From scratch; supported by the path API (D6, D8). Hardest after G3.*

### Assembly

- **Z1.** `U := σ⁻¹{0}`, `V := σ⁻¹{1}`; assemble `SplitsIntoTwo` from G2–G4, then
  `splitsIntoTwo_iff_isTwoSidedPartition` (PROVEN) closes the goal. *Plumbing.*

```
L1 ┐
L2 ┼─► L3 ─► G2 ┐
   │       │    ├─► Z1 ─► exists_twoSidedPartition_of_arc
   └─► G1 ─┴─► G3┤
            └─► G4┘
(G3, G4 consume IsSimplyConnected R via the monodromy engine / path-pushing)
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
| D3 | `IsCoveringMap`; `Circle.isCoveringMap_exp` | `Topology/Covering*`; `Analysis/SpecialFunctions/Complex/Circle.lean:401` | G1, G3 |
| D4 | `monodromy_theorem`, `liftPath`, `monodromy_bijective`, `monodromy_map` | `Topology/Homotopy/Lifting.lean:152,257,400,376` | G3 |
| D5 | `IsCoveringMapOn.existsUnique_continuousMap_lifts`, `existsUnique_continuousMap_lifts` | `Topology/Homotopy/Lifting.lean:480,421` | G3 |
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
| E3 | **Construction of the side double cover** + proof it `IsCoveringMap` (G1) | `IsCoveringMap` *def/API* present (D3); *this construction* absent | G1 |
| E4 | **"odd-crossing loop ⇏ null-homotopic"** wired through the side cover (G3) | monodromy engine present (D4–D5); *this application* absent | G3 |
| E5 | **Each side connected via path-pushing off `β`** (G4) | path API present (D6,D8); *the push-off lemma* absent | G4 |
| E6 | *(avoided)* PL **general position / transversality** + **mod-2 intersection number** of a path with a PL arc and its homotopy invariance | **ABSENT** (only smooth `Bordism.lean` exists; no transversality, no intersection number) | would be needed only by the *intersection-parity* variant of G3 — the covering engine (E3/E4) is chosen specifically to **avoid** this |

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

- **R1 — PL preservation downstream {{NEEDS_PROOF}}.** The PL restriction is free
  for ST (verified, §0) but not yet traced through the amplification + bridge. If
  some intermediate construction needs non-PL arcs, the lever weakens. *Verify
  before committing to L-nodes.* Low risk (drawings stay straight-line) but must be
  checked.
- **R2 — the cover lives on `R∖β`, simple connectivity is of `R` {{NEEDS_PROOF}}.**
  G3 must bridge `π₁(R∖β)` data to `IsSimplyConnected R`. The intended bridge:
  loops in `R∖β` are loops in `R`; null-homotopy *in `R`* lifts via the cover
  extended appropriately. The exact formulation that mathlib's `monodromy_theorem`
  accepts (it is stated for a covering of the *base* the loop lives in) is **not yet
  pinned down** — this is the highest-uncertainty design point. Resolve on paper
  before coding G1/G3.
- **R3 — `Plane = ℝ × ℝ` has no inner product (verified, D7 note).** Use the
  determinant form (L1), or transport to `EuclideanSpace ℝ (Fin 2)`. Decided: stay
  in `ℝ × ℝ` with the determinant form; no transport.
- **R4 — architectural gap (B)/(C) of §1.** Even full success leaves
  `WeakAveragedBound` unproduced and the faces→genus-0→Euler span unbuilt. Route
  (c) is necessary, not sufficient, for an unconditional crossing lemma.

---

## 5. Sequencing & go/no-go

Estimate (sessions = ~150–200k context → one `/compact`):

0. **R1 + R2 paper resolution** (½–1 session). **Go/no-go gate.** If R2 has no
   clean mathlib-acceptable formulation, route (c) stalls at G3 and we reassess.
1. **L1 + Action 0** (PL types, segment functional) — ~1 session.
2. **L2 + L3** (corner model, global collar) — ~2 sessions. The local bulk.
3. **G1** (side double cover + `IsCoveringMap`) — ~1–2 sessions.
4. **G3** (crux: monodromy ⇒ well-defined/both-valued) — ~2 sessions. Highest risk.
5. **G2 + G4 + Z1** (locally constant, each side connected, assembly) — ~1–2
   sessions.

**Total ~6–12 sessions** for `exists_twoSidedPartition_of_arc` on PL arcs,
hardest node G3, dominant variance R2. Discharging it does **not** finish the
crossing lemma (§1, R4).

**Work order (per project rules — hardest first):** the honest hardest node is G3
(crux) resting on L3 (collar). Do the R2 paper resolution and L3 design *first*
(they gate G3), then build bottom-up L→G→Z. Do **not** start L1 coding before the
R1/R2 gate clears.

---

*Verification basis:* all PRESENT/ABSENT rows checked against
`.lake/packages/mathlib/Mathlib` at `v4.30.0` on 2026-06-02 (`grep` over the source
tree; declaration line numbers cited inline). Full route-(c) evaluation:
`nthdegree recall "Route (c) end-to-end evaluation"`.
