# Crossing-lemma route fork — faces vs ARR for obligation B

**Question.** For an *unconditional* `CrossingLemma.CrossingLemmaMultigraphStatement`
(the M-form `e³ ≤ 64·M·v²·cr`, `CrossingLemma/CrossingLemma.lean:154`, consumed by
the downstream M-form bridge), which route — faces or ARR — should carry obligation B
(genus-0 combinatorial map → planar/Euler edge bound → `WeakAveragedBound` →
`CrossingLemmaMultigraphStatement`), and what is the complete remaining obligation
list on that route?

All file:line references are to `/Users/adam/projects/math-projects/lean-formalizations/lean/LeanFormalizations/…`.
No Lean build was run; claims are from reading source and grepping the dependency
graph. Where a fact is "PROVEN", it means the cited Lean term is `sorry`-free *in
its own body* (transitive `sorry`-freeness is stated separately when checked).

---

## 0. Executive summary

The fork as posed in the brief — "faces vs ARR, two competing routes to the same
target" — does **not** match the repository's actual wiring. Three findings
override the framing:

1. **The M-form `WeakAveragedBound` (`CrossingLemmaAmplification.lean:128`) has ZERO
   producers.** The only theorem mentioning it as a conclusion does not exist;
   `crossingLemma_of_weakBound` (`:220`) *consumes* it as a hypothesis. The entire
   span *geometry → genus-0 map → Euler edge bound → M-form `WeakAveragedBound`* is
   **unbuilt**. (PROVEN by exhaustive grep, §1.)

2. **The ARR route, as wired, does NOT reach the M-form.** The chain from the ARR
   residual `straightLineCanonicalComponentResidualMapPlanarityOfARR`
   (`SzemerediTrotter.lean:4533`, `sorry` at `:4644`) terminates at
   `LocalSimpleWeakAveragedBound (stMultigraph P L)` and thence Szemerédi–Trotter —
   the **M = 1, straight-line-only** target. It is structurally incapable of
   producing the universally-M-quantified `WeakAveragedBound` (`:128`), because
   every link in the chain (`StraightLineInducedWeakBound`, the `*Simple*`
   averaged-bound family) is hardcoded to `stMultigraph` and `multiplicity ≤ 1`.
   (PROVEN by tracing the chain, §2.)

3. **Faces and ARR are not competitors; they are two LAYERS of one route.** The
   faces PL-collar work (`exists_twoSidedPartition_of_straightArc`,
   `PLCollarSeparation.lean:480`, `sorry`-free) is the *plane-separation input* that
   the ARR residual's open sorry (`:4644`, "Obligation B") is meant to consume to
   build the genus-0 combinatorial map. `SzemerediTrotter.lean` imports
   `PLCollarSeparation` (line 11). The arbitrary-arc residual
   `exists_twoSidedPartition_of_arc` (`PlaneArcSeparation.lean:382`, `sorry` at
   `:385`) is a **separate, unwired** statement (the Schoenflies "residual closure"
   NO-GO of `ROUTE_C_PLAN.md §0`); nothing consumes it except a same-file
   re-export. (PROVEN by forward-consumer trace, §3.)

**Recommendation (decisive reason).** Carry obligation B on the **ARR route**
(the residual-map / Edmonds genus-0 construction), built **on top of** the faces
PL-collar layer that already feeds it. Decisive reason: the Euler/edge-bound half
of obligation B is *already M-tolerant and `sorry`-free* (`planar_multigraph_edge_bound`,
`PlanarEdgeBound.lean:479`, M-form; `EulerBound` χ ≤ 2 PROVEN), and the genus-0 map
is produced from the drawing's rotation system *only* through the residualMap/ARR
machinery (`abstractize` + `HasGenusZeroSimplePlanarization`); there is no second
mechanism in the repo. The faces residual `exists_twoSidedPartition_of_arc` (`:385`)
is the wrong object to invest in — it is the arbitrary-continuous-arc Schoenflies
statement, off the wired path, and its closure is flagged NO-GO solo.

**But the recommendation comes with a hard caveat (§4):** even the ARR route, fully
closed for straight lines, produces only the **M = 1** target. To reach the M-form
that the downstream M-form consumer needs, an **additional unbuilt span** is required: lift the
residualMap/genus-0/edge-bound/averaging chain from `stMultigraph` (M = 1) to a
*curved, multiplicity-M* `DrawnMultigraph`, then run the M-form averaging
`WeakAveragedBound`. That span is genuinely unbuilt and is listed in §6.

---

## 1. The M-form target and its (missing) producer

`CrossingLemmaMultigraphStatement` (`CrossingLemma.lean:154`):

```
∀ G M, 0 < M → (∀ p q, G.multiplicity p q ≤ M) → G.ArcsJoinEndpoints →
  G.WellDrawn → 4*M*G.V.card ≤ G.numEdges →
    G.numEdges^3 ≤ 64 * M * G.V.card^2 * G.crossings
```

This is the statement `IncidenceAssembly.…_of_crossingLemma` consumes (Bridge.lean
docstring) and the one the curved Edge-B endgame needs
(`docs/corollary24-multigraph-endgame-build.md`: "the curve (Edge-B) construction
produces multiplicity up to M … and consumes the M-form crossing inequality
`CrossingLemmaMultigraphStatement` (`CrossingLemma.lean:154`)").

**Producer.** Exactly one, `sorry`-free:

- `crossingLemma_of_weakBound (hweak : WeakAveragedBound) : CrossingLemmaMultigraphStatement`
  (`CrossingLemmaAmplification.lean:220`). PROVEN `sorry`-free in its own body
  (pure ℕ arithmetic, substitution `a = 4Mv, b = e`; `nlinarith` + cancellation,
  lines 222–244). **Confirmed it does NOT use `vertexSubsetAveraging_bound`** — that
  lemma sits in a separate `IntegerRoute` section and the docstring at `:95`/`:1576`
  states it is "not used by `crossingLemma_of_weakBound`."

**Its input `WeakAveragedBound` (`:128`):**

```
∀ G M, 0 < M → (∀ p q, G.multiplicity p q ≤ M) → G.ArcsJoinEndpoints → G.WellDrawn →
  ∀ a b, 0 < a → a ≤ b →
    M*a²*b²*G.numEdges ≤ a⁴*G.crossings + 3*M²*a*b³*G.V.card
```

**Producer search result (PROVEN by grep).** Searching `: WeakAveragedBound :=`,
`WeakAveragedBound := by`, and every `theorem … : WeakAveragedBound` over all of
`LeanFormalizations/`:

- The **only** occurrence with `WeakAveragedBound` in a *conclusion* position is the
  hypothesis of `crossingLemma_of_weakBound`.
- The two `_of_` theorems returning a weak-averaged bound
  (`CrossingLemmaAmplification.lean:1464`, `:1570`) return
  **`IndependentSimpleWeakAveragedBound`** — a *different* Prop (`multiplicity ≤ 1`
  + `CrossingsAreIndependent`, `:170`), not the M-form.

**Conclusion (PROVEN).** No theorem in the repo produces the M-form
`WeakAveragedBound`. The span feeding it is unbuilt. This is independent of the
faces-vs-ARR choice.

---

## 2. Wiring reality — the ARR route reaches only M = 1 / Szemerédi–Trotter

Forward-consumer chain from the ARR residual (each link verified `sorry`-free in
its own body, §5):

```
straightLineCanonicalComponentResidualMapPlanarityOfARR   ST:4533  [sorry @ 4644]
  → straightLineCrossingFreeComponentwisePlanarization_of_canonical_component_…OfARR  ST:4486
  → straightLineCrossingFreeEdgeBound_of_componentwise_planarization               ST:4770
       (here the genus-0 map → Euler bound is applied:
        planar_multigraph_edge_bound, PlanarEdgeBound.lean:479, sorry-free)
  → straightLineInducedWeakBound_of_crossingFreeEdgeBound                          ST:4822
  → localWeakAveragedBound_stMultigraph_of_straightLineInducedWeakBound            ST:4839
       ⇒ LocalSimpleWeakAveragedBound (stMultigraph P L)                            (M = 1)
  → simpleCrossingBound_of_localWeakAveragedBound                                  Ampl:248
  → stMultigraph_crossingBound_of_straightLineInducedWeakBound                     ST:4851
  → szemerediTrotter_of_straightLineInducedWeakBound                               ST:4867
       ⇒ SzemerediTrotterStatement
```

`StraightLineInducedWeakBound` (`ST:4814`) is quantified over `stMultigraph P L` and
its `S ⊆ V`; `LocalSimpleWeakAveragedBound G` (`Ampl:184`) fixes the single drawing
`G := stMultigraph P L`. Neither carries an `M` parameter; both are M = 1 surfaces.

**Conclusion (PROVEN).** Closing the `sorry` at `ST:4644` makes **Szemerédi–Trotter
unconditional**, not the M-form `CrossingLemmaMultigraphStatement`. The ARR route as
wired does not touch the M-form. (This corrects the brief's "ARR route which is
wired" — it is wired to a *different, weaker* target.)

### 2a. Correction to the brief: `ArcsRotationRegular` is discharged for `stMultigraph`

The brief states the ARR route is "gated on the undischarged hypothesis
`ArcsRotationRegular` (`CrossingLemma.lean:241`)." That is **inaccurate for the
straight-line drawing** (and `:241` is not the def; the def is `CrossingLemma.lean:389`).
ARR is *discharged* — `sorry`-free — for every drawing the ST chain uses:

- `stMultigraph_arcsRotationRegular` (`ST:2085`) — PROVEN `sorry`-free (delegates to
  `…_of_incidentAnglesDistinct` + `straightLineIncidentAnglesDistinct`).
- `stComponentDrawing_arcsRotationRegular` (`ST:2225`) — PROVEN.
- `permuteEdges_arcsRotationRegular` (`CrossingLemma.lean:786`) — PROVEN.
- `prefixEdges_arcsRotationRegular` (`CrossingLemma.lean:1197`) — PROVEN.

So `ArcsRotationRegular` is **not** the open obligation on the straight-line ARR
route. The single open obligation there is the `sorry` at `ST:4644` (Obligation B,
the region-family / Edmonds gluing). `ArcsRotationRegular` *would* become an open
obligation again only on the (unbuilt) curved/multiplicity-M lift, where the arcs
are algebraic, not straight — its discharge for algebraic arcs is the threaded-
hypothesis question deferred in `CrossingLemma.lean:387`.

---

## 3. Faces residual `exists_twoSidedPartition_of_arc` is a separate, unwired statement

`exists_twoSidedPartition_of_arc {A R β} (h : ArcInRegion A R β) :
∃ U V, IsTwoSidedPartition (regionMinusArc R β) U V`
(`PlaneArcSeparation.lean:382`, `sorry` at `:385`). This is stated for an **arbitrary
continuous** `SimpleArc`.

**Forward-consumer trace (PROVEN).** The only consumer is `local_arc_separation`
(`PlaneArcSeparation.lean`, a same-file re-export). `ROUTE_C_PLAN.md §1` states the
same: "nothing imports it except the root aggregator (`CrossingLemma.lean:14`, a
re-export)." Nothing on the path to any weak bound consumes it.

**What the faces PL work actually feeds.** The *PL* (polygonal-arc) layer is a
distinct chain that DOES connect to ARR:

- `exists_twoSidedPartition_of_straightArc` (`PLCollarSeparation.lean:480`) — PROVEN
  `sorry`-free (routes the single-segment case through
  `union_collarPlus_collarMinus_of_numSegs_one`, `sorry`-free; see §3a). Witnessed
  non-vacuous by `exists_twoSidedPartition_unitSegment` (`PLCollarSeparation.lean:1117`,
  `sorry`-free).
- `exists_twoSidedPartition_prefixStep` (`PLCollarSeparation.lean:879`) — PROVEN
  `sorry`-free; consumes `…_of_straightArc` (`:1111`).
- These are referenced by the ARR residual's open-`sorry` comment block at
  `ST:4597` (Obligation B mentions `exists_twoSidedPartition_of_straightArc`) and
  `ST:4630` (mentions `exists_twoSidedPartition_prefixStep`). The downstream
  consumers (`hcard1` `ST:4647`, the bridge `regionSeparates_prefix_of_crosscut`,
  the cotree branch of `hstep`) are already wired to consume the `dr` / `hstepCrosscut`
  bundle that the `sorry` is meant to produce.

**Conclusion (PROVEN).** The faces work that matters for the wired route is the
**PL-collar straight-arc** separation, which is `sorry`-free and already feeds the
ARR residual. The **arbitrary-arc** `exists_twoSidedPartition_of_arc` (`:385`) is off
the path. Investing in `:385` does not advance the M-form (or even Szemerédi–Trotter).

### 3a. `PolygonalArc.lean:3148` is OFF the straight-line path

`union_collarPlus_collarMinus` (`PolygonalArc.lean:3087`) carries a `sorry` at `:3148` (the
interior-vertex disk branch of the P2 union, for `numSegs ≥ 2`). The straight-line
ST graph builds edges as single segments (`segmentArc`, `numSegs = 1`), so the
PL-collar entry point used by ARR routes through the **single-segment** variant
`union_collarPlus_collarMinus_of_numSegs_one` (`PLCollarSeparation.lean:138`,
`sorry`-free, per its docstring at `:102`). The general multi-segment
`union_collarPlus_collarMinus` is referenced only at `PLCollarSeparation.lean:81`
(the multi-segment collar, not the straight-arc entry).

**Conclusion (PROVEN).** `PolygonalArc.lean:3148` does **not** gate the straight-line ARR
planarization. It is the `ROUTE_C_PLAN.md §7` "BLOCKED for numSegs ≥ 2" residual of
the *arbitrary-PolygonalArc* collar (with the machine-checked `L₂² ≤ L₁·L∞` budget
collision documented there), needed only if one closes
`exists_twoSidedPartition_of_polygonalArc` for general PolygonalArcs — which is *also* off the
wired path.

---

## 4. The M = 1 → M-form gap (why even the recommended route is not sufficient)

The Euler/edge-bound half of obligation B is M-ready and `sorry`-free:

- `planar_multigraph_edge_bound (G) (M) (hpl : HasGenusZeroSimplePlanarization G)
  (hmult : PairMultiplicityBound G M) (hv : 3 ≤ card Vertex) :
  card Edge ≤ M*(3*card Vertex − 6)` (`PlanarEdgeBound.lean:479`) — PROVEN
  `sorry`-free; M-tolerant by construction (fiberwise collapse of the multiplicity-M
  fibers onto the simple present-pair graph).
- `HasGenusZeroSimplePlanarization` (`:468`) requires a simple, connected, genus-0
  (`IsPlanar`) `CombinatorialMap` on the same vertex set with ≥ the present-pair
  count. `EulerBound`'s "connected ⟹ χ ≤ 2" (`EulerBound.lean:520`) is PROVEN
  `sorry`-free, supplying the `e ≤ 3v−6` simple bound.
- `abstractize` (`Abstractize.lean:26`) — the forgetful drawing→abstract map — and
  `abstractize_pairMultiplicityBound` (M-cap transfer) are PROVEN `sorry`-free.

What is **missing** to reach the M-form `WeakAveragedBound`:

(M-1) **A genus-0 combinatorial map of a CURVED, multiplicity-M drawing.** The
  existing genus-0 construction (`HasGenusZeroSimplePlanarization` for the actual
  drawing) is produced from the rotation system *only* through the residualMap/ARR
  development, and it is currently instantiated *only* for the straight-line
  `stComponentDrawing` (`StraightLineCanonicalComponentResidualMapPlanarityOfARR`).
  No `DrawnMultigraph`-generic or curved-arc instance exists.

(M-2) **The M-form averaging lift.** Even granting a genus-0 map and the M-form Euler
  bound for a curved drawing, there is **no** repo theorem of shape
  `(M-form crossing-free edge bound) → WeakAveragedBound`. The existing averaging
  lift `localSimpleWeakAveragedBound_of_inducedWeakBound` (`Ampl:1347`) and
  `independentSimpleWeakAveragedBound_of_inducedWeakBound` (`Ampl:1464`) are M = 1.
  The M-form averaging (random vertex subset with the single-`M` sharpening
  `cr ≥ M·p²·e − 3M²·p·v`, per `Ampl:91`/`:125`) is unbuilt. The integer-route
  `vertexSubsetAveraging_bound` (`Ampl:1605`, `sorry` at `:1612`) is **PROVEN-obstructed
  for the exact constant** (docstring `:1594` "CANNOT close the exact 1/64 constant by
  integer averaging") and is explicitly not the producer.

**Honest classification.** The brief's "obligation B" — as a path to the M-form —
is genuinely **unbuilt** on both routes. The ARR route is the right *substrate*
(it owns the genus-0 mechanism and the M-tolerant edge bound), but a straight-line
ARR closure delivers Szemerédi–Trotter, not the M-form. The M-form requires (M-1)
and (M-2) on top.

---

## 5. Verified `sorry`-freeness of the wired chain links

Confirmed by reading the theorem headers/bodies (no `sorry` tactic in body):

- `planar_multigraph_edge_bound` `PlanarEdgeBound.lean:479` — `sorry`-free (whole
  file `sorry`-free).
- `crossingLemma_of_weakBound` `Ampl:220` — `sorry`-free.
- `stMultigraph_arcsRotationRegular` `ST:2085`, `stComponentDrawing_arcsRotationRegular`
  `ST:2225` — `sorry`-free.
- `straightLineCrossingFreeComponentwisePlanarization_of_canonical_component_…OfARR`
  `ST:4486`, `straightLineCrossingFreeEdgeBound_of_componentwise_planarization` `ST:4770`,
  `straightLineInducedWeakBound_of_crossingFreeEdgeBound` `ST:4822`,
  `localWeakAveragedBound_stMultigraph_of_straightLineInducedWeakBound` `ST:4839` —
  `sorry`-free.
- `exists_twoSidedPartition_of_straightArc` `PLCollarSeparation.lean:480`,
  `exists_twoSidedPartition_prefixStep` `:879`, `union_collarPlus_collarMinus_of_numSegs_one`
  (via `:138`), `exists_twoSidedPartition_unitSegment` `:1117` — `sorry`-free.
- `RegionFaceBridge.lean` (Edmonds region↔face core) — `sorry`-free, axiom-clean
  (per memory `01KV24MN…`; the genuinely-novel inductive geometric step is
  *isolated* into the `ST:4644` sorry, not faked here).

Complete `sorry`-tactic inventory in the relevant files:

| File:line | Enclosing decl | Blocks |
|---|---|---|
| `SzemerediTrotter.lean:4644` | `straightLineCanonicalComponentResidualMapPlanarityOfARR` (`:4533`) | Obligation B: region family `dr` + per-step `hstepCrosscut` (Edmonds same-region⇒same-cycle) for the straight-line residual map |
| `PlaneArcSeparation.lean:385` | `exists_twoSidedPartition_of_arc` (`:382`) | arbitrary-continuous-arc crosscut separation (Schoenflies-strength; OFF the wired path) |
| `PolygonalArc.lean:3148` | `union_collarPlus_collarMinus` (`:3087`) | multi-segment (numSegs ≥ 2) PolygonalArc collar P2 interior-vertex disk branch (OFF the straight-line path) |
| `CrossingLemmaAmplification.lean:1612` | `vertexSubsetAveraging_bound` (`:1605`) | integer-averaging double count; PROVEN-obstructed for exact constant; NOT a producer |
| `ComponentSplit.lean:72` | `componentCount_le_totalDegree` (`:69`) | ≤ d distinct irreducible factors of a degree-d curve |
| `ComponentSplit.lean:96` | `lineCircle_components_meet_finite` (`:86`) | line/circle components meet a no-3-collinear set in O_d(1) points |
| `ComponentSplit.lean:117` | `exists_genuine_component_rich` (`:106`) | pigeonhole: a rich non-line/non-circle component carries ≳ m/polylog points |

---

## 6. RECOMMENDED route — complete ordered obligation list (ARR substrate → M-form)

Carry obligation B on the ARR / residualMap genus-0 substrate. Ordered from the
geometric residual up to a proof of `WeakAveragedBound` and thence
`CrossingLemmaMultigraphStatement`. Labels: **PROVEN-TRACTABLE** (a named in-repo or
mathlib lemma closes it; cited), **NEEDS-DESIGN** (statement exists or is obvious but
the proof object must be designed; no blocking obstruction known), **OPEN-DIFFICULT**
(genuinely novel combinatorics/geometry, no in-repo or mathlib closer; a real
obstruction is documented).

### Tier A — finish the straight-line ARR closure (delivers Szemerédi–Trotter, M = 1)

A1. **`SzemerediTrotter.lean:4644` — Obligation B (Edmonds same-region ⇒ same-cycle).**
    Build the region family `dr` over every prefix level plus the per-step
    `PrefixStepCrosscutData` (`hstepCrosscut`). Sub-obligations per the `:4615`–`:4639`
    comment: (B0) `dr` is forced mutually-recursive via `poolRegion`/`hfactor`;
    (B1) per-step combinatorial witness `c₁,c₂,hc,hvertex` (the extractor
    `exists_residualMapPrefixStepSameFaceData_…` gives these only at the FIRST cotree
    step, `card Face = 1`; the general step needs the angular co-faciality identity
    `hsplit`, `ResidualMapProperties` RM:5813-5867); (B2) the region gluing from the two
    sides `U,V` of `exists_twoSidedPartition_prefixStep`. **Label: OPEN-DIFFICULT.**
    Why: the inductive direction "new edge inserted across a single region splits
    exactly the face whose region it crosses" is the Edmonds correspondence; it is
    **not in mathlib** (no combinatorial-map ↔ planar-embedding theorem) and **not in
    the repo** (`RegionFaceBridge.lean` proves the base case and the easy converse, and
    isolates exactly this step into the `:4644` sorry). It is the only genuinely-novel
    node of the straight-line route.

    *Already-discharged inputs A1 may assume (all `sorry`-free):*
    `exists_twoSidedPartition_of_straightArc` (`PLCollarSeparation.lean:480`),
    `exists_twoSidedPartition_prefixStep` (`:879`), the base case
    `facePerm_sameCycle_of_card_face_eq_one` / `edmondsCompatibleOfCardFaceOne`
    (`RegionFaceBridge`), `stComponentDrawing_arcsRotationRegular` (`ST:2225`),
    `planar_multigraph_edge_bound` (`PlanarEdgeBound.lean:479`).

A2. **(closes automatically once A1 lands)** Tier-A chain `ST:4486 → :4770 → :4822 →
    :4839 → :4867`. **Label: PROVEN-TRACTABLE** (every link is already `sorry`-free,
    §5; closing A1 discharges the only open dependency, yielding
    `SzemerediTrotterStatement`).

### Tier B — lift from M = 1 straight-line to curved multiplicity-M (delivers the M-form)

These are required *in addition* to Tier A to reach the M-form that the downstream consumer needs.
None of them exists in the repo today.

B1. **Genus-0 combinatorial map for a curved DrawnMultigraph
    (`HasGenusZeroSimplePlanarization (abstractize G)` for a curved, multiplicity-M
    `G`).** Generalize `StraightLineCanonicalComponentResidualMapPlanarityOfARR` from
    `stComponentDrawing` to an arbitrary `DrawnMultigraph` whose arcs are the curve
    sub-arcs of the Edge-B construction. **Label: OPEN-DIFFICULT.** Why: this re-runs
    A1's Edmonds construction with curved arcs and re-discharges `ArcsRotationRegular`
    (now non-straight). The plane-separation input would need a curved analogue of
    `exists_twoSidedPartition_of_straightArc`; the only candidate is
    `exists_twoSidedPartition_of_arc` (`:385`, the arbitrary-arc residual), which is
    itself OPEN-DIFFICULT (Schoenflies; `ROUTE_C_PLAN §0` NO-GO solo). No in-repo
    closer.

B2. **`ArcsRotationRegular` for the Edge-B algebraic arcs.** The threaded hypothesis
    deferred at `CrossingLemma.lean:387`. **Label: OPEN-DIFFICULT.** Why: requires
    that incident algebraic-curve ends have distinct, radius-stable first-crossing
    angles on a small circle (`ArcsRotationRegular` def, `:389`); no in-repo discharge
    for non-straight arcs, and the project notes the arcs are "never assumed
    semialgebraic," so the standard finite-angle argument is not directly available.

B3. **M-form crossing-free edge bound → M-form `WeakAveragedBound`** (the M-form
    averaging lift). A theorem of shape: from the curved-drawing M-form Euler bound
    (B1 + `planar_multigraph_edge_bound`), derive `WeakAveragedBound` (`:128`) via the
    single-`M`-sharpened random-vertex-subset averaging
    `cr ≥ M·p²·e − 3M²·p·v`. **Label: NEEDS-DESIGN.** Why: the M = 1 analogues exist
    and are `sorry`-free (`localSimpleWeakAveragedBound_of_inducedWeakBound` `Ampl:1347`,
    `independentSimpleWeakAveragedBound_of_inducedWeakBound` `Ampl:1464`; the Bernoulli
    survival-probability finite-sum double counts `E[v_p]=pv, E[e_p]=p²e, E[cr_p]=p⁴cr`
    are documented `sorry`-free at `Ampl:83`). The M-form is a parallel construction
    with the `3M²` coefficient; the obstruction is engineering (build the M-form
    induced-weak-bound deletion step and re-run the averaging), not a known
    impossibility — but the *integer* route to it is PROVEN-obstructed for the exact
    constant (`vertexSubsetAveraging_bound` docstring), so the design must use the
    real-`p`/rational `a/b` form, matching `WeakAveragedBound`'s cleared shape.

B4. **(closes automatically once B3 lands)** `crossingLemma_of_weakBound`
    (`Ampl:220`) ∘ B3 ⇒ `CrossingLemmaMultigraphStatement`. **Label:
    PROVEN-TRACTABLE** (`crossingLemma_of_weakBound` is `sorry`-free, §5).

**Critical-path ranking (hardest first, per project rules):** A1 = B1 (the Edmonds
genus-0 construction, straight then curved) ≻ B2 (ARR for algebraic arcs) ≻ B3
(M-form averaging design) ≻ {A2, B4} (mechanical, auto-close). A1 is the prerequisite
*technique* for B1; do A1 first because its inputs are already `sorry`-free, then
generalize to B1.

---

## 7. The four flagged sorries — on the recommended route?

For each of {the 3 `ComponentSplit.lean` sorries, `vertexSubsetAveraging_bound`}:

- **`componentCount_le_totalDegree` (`ComponentSplit.lean:72`) — NO.** It is a
  plane-algebraic-curve component-counting lemma (≤ d normalized irreducible factors).
  It feeds the Pach–de Zeeuw incidence *decomposition* (Gap B in `Bridge.lean`,
  `auxCurve` family), not the crossing lemma's genus-0/edge-bound/averaging span.
  No path from it to `WeakAveragedBound` or `CrossingLemmaMultigraphStatement`.

- **`lineCircle_components_meet_finite` (`ComponentSplit.lean:96`) — NO.** Same:
  no-3-collinear/no-4-concyclic intersection counting for the incidence decomposition,
  not the crossing lemma.

- **`exists_genuine_component_rich` (`ComponentSplit.lean:117`) — NO.** Same:
  pigeonhole richness for the incidence decomposition.

  (All three are on the *separate* downstream M-form obligation — the
  `PositiveAuxiliaryIncidenceCardBound`/Gap-B incidence assembly — which `Bridge.lean`
  reaches *given* `CrossingLemmaMultigraphStatement`. They are downstream consumers of
  the crossing lemma's output region, not inputs to producing it.)

- **`vertexSubsetAveraging_bound` (`CrossingLemmaAmplification.lean:1612`) — NO.** Two
  independent reasons: (i) it is explicitly **not used** by `crossingLemma_of_weakBound`
  (docstring `:95`, `:1576`; it lives in the isolated `IntegerRoute` section); (ii) it
  is **PROVEN-obstructed for the exact 1/64 constant** (docstring `:1594`), so it cannot
  be a producer of `WeakAveragedBound` even in principle. The recommended route (B3)
  uses the real-`p` averaging form, not this integer double count.

---

## 8. Structural assumptions used

- **Finiteness.** All multigraphs are `DrawnMultigraph` (finite vertex `Finset`,
  `Fin numEdges` edges); `planar_multigraph_edge_bound` and the averaging arguments
  are finite. The genus-0 `CombinatorialMap` is on a `Fintype` dart set.
- **Genus-0 / connectedness.** `HasGenusZeroSimplePlanarization` demands `Connected`
  and `IsPlanar` (χ = 2) of the witness map; `EulerBound` supplies χ ≤ 2 from
  connectedness alone (genus g ≥ 0). The crossing-free *subgraph* must be the object
  whose map is genus-0 — the M-form bound is then a multiplicity collapse.
- **Multiplicity cap.** The M-form everywhere uses `∀ p q, multiplicity p q ≤ M`,
  transferred to `PairMultiplicityBound` by `abstractize_pairMultiplicityBound`. The
  straight-line route hardcodes M = 1; the curved Edge-B route needs M = 16d⁴
  (`Bridge.lean`), so the M-form is load-bearing and the M = 1 ST route does not
  substitute for it.
- **PL restriction.** The wired plane-separation input is *polygonal* arcs
  (`PolygonalArc`, `exists_twoSidedPartition_of_straightArc`); `ROUTE_C_PLAN §0` notes this
  is free for straight-line ST but the arbitrary-arc residual (`:385`) is
  Schoenflies-strength and unwired. The curved Edge-B lift (B1) re-opens this as
  OPEN-DIFFICULT.

---

## 9. What next (ranked)

1. **A1 (`ST:4644`, Edmonds same-region ⇒ same-cycle, straight-line).** OPEN-DIFFICULT
   but the single highest-value node: it unblocks unconditional Szemerédi–Trotter
   immediately (Tier A auto-closes), validates the genus-0 mechanism end-to-end on a
   concrete drawing, and is the prerequisite technique for B1. Inputs already
   `sorry`-free. This is the correct "hardest part first" target *within the wired
   region*.

2. **B3 (M-form averaging lift, real-`p`).** NEEDS-DESIGN, lowest obstruction-risk of
   the Tier-B nodes; mirrors the existing `sorry`-free M = 1 averaging with the `3M²`
   coefficient. Can be designed in parallel with A1 since it is downstream-independent
   (it consumes a *hypothetical* M-form edge bound). Closing it + B4 means only B1/B2
   stand between geometry and the M-form.

3. **B1 (curved genus-0 map) + B2 (ARR for algebraic arcs).** OPEN-DIFFICULT; the
   genuine remaining content for the M-form. B1 reuses A1's construction with curved
   arcs and needs a curved plane-separation input (the unwired `:385` or a curved
   substitute) — this is where the Schoenflies/arbitrary-arc cost actually lands, and
   it is unavoidable for a *curved* drawing. B2 is the algebraic-arc rotation
   regularity. Sequence after A1.

4. **Do NOT invest in `exists_twoSidedPartition_of_arc` (`:385`) or `PolygonalArc.lean:3148`
   as standalone targets.** `:385` is the arbitrary-arc Schoenflies statement, off the
   wired path; `:3148` is the multi-segment PolygonalArc collar, off the straight-line path.
   Neither advances Szemerédi–Trotter or the M-form on its own. (`:385` becomes
   relevant only *inside* B1, as the curved plane-separation input, where it would be
   restated for the specific Edge-B arcs.)

**Net.** The recommended route is ARR (residualMap genus-0), built on the existing
`sorry`-free PL-collar straight-arc layer. Its straight-line closure (A1) is one
OPEN-DIFFICULT node away and delivers Szemerédi–Trotter. The M-form that the downstream consumer
needs requires the additional Tier-B span (B1–B4), which is genuinely unbuilt; B1/B2
are OPEN-DIFFICULT, B3 is NEEDS-DESIGN, B4 is PROVEN-TRACTABLE. The faces arbitrary-arc
residual is not a competing route — it is, at most, the curved plane-separation input
*inside* B1.
