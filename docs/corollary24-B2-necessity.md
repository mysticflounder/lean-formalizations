# B2 necessity — does Edge B's Székely-for-curves crossing count require the global injective arc?

**Scope.** One question. The prior viability analysis
(`docs/corollary24-B2-viability.md`) concluded that node B2 — a global injective
arc / global per-component linear ordering of incident points along a real
algebraic curve component (a 1-manifold parametrization) — is absent from mathlib
v4.30 and is a wall for Edge B *under the per-component intrinsic-order strategy it
analyzed*. This document tests whether Edge B's crossing count **genuinely
requires** that primitive, or whether a weaker substitute, constructible from
mathlib v4.30 + the in-repo seeds, carries the count. It evaluates the three
candidate substitutes named in the task (generic-functional sweep order;
local-arc + Bézout pairwise bound only; minimal-combinatorial-object analysis of
what Székely consumes) and delivers a precise verdict.

**This document does not modify the prior verdict's correctness; it sharpens its
scope.** The viability doc's "wall" is real *for the strategy it priced*. The
present analysis finds a different strategy (the **ℓ-monotone-piece
decomposition**) that **dissolves the primary obstruction the viability doc named
(the path→injective-arc / loop-revisit problem, its node 4c, and the
singular-endpoint Puiseux problem, its 4d)** and **relocates the residual to a
single, strictly narrower from-scratch theorem** (a "generic monotone graph
decomposition"). The headline is therefore neither "B2 dissolves" nor "B2 is an
unconditional wall"; it is: **the global injective arc is an artifact of one
strategy; a weaker substitute removes most of B2 but leaves one named
real-algebraic-curve-topology lemma that is still absent from mathlib v4.30.**

**Verification basis.** Every "PROVEN in-repo" claim cites a declaration whose
statement and (where load-bearing) proof I read directly in
`PachSharir/SzemerediTrotter.lean`, `PachSharir/Theorem23.lean`,
`CrossingLemma/CrossingLemma.lean`, `Bezout.lean`, or `AlgebraicPrelim.lean`.
mathlib lemma names were confirmed against this repo's pinned corpus (v4.30) via
the project search index; those are labeled EMPIRICALLY VERIFIED (search) where I
did not read the mathlib source line. I did **not** run `lake build`. Two scratch
computations (`/tmp/curve_sweep.py`, `/tmp/single_psi.py`, run with `uv`)
support specific structural claims and are labeled EMPIRICALLY VERIFIED with their
scope. An independent deep-reasoning pass (Codex / gpt-5.5, read-only, same
extracted facts) reached the same verdict on every load-bearing point and
corrected two errors in a draft of §5 below (the piece-count formula and the
same-curve cross-piece bound); those corrections are incorporated and attributed.

Date: 2026-06-20.

---

## 1. What the crossing inequality actually consumes (read from source)

The abstract finite-multigraph crossing inequality is
`CrossingLemmaMultigraphStatement` (`CrossingLemma/CrossingLemma.lean:154`):

```
∀ (G : DrawnMultigraph) (M : ℕ),
  0 < M → (∀ p q, G.multiplicity p q ≤ M) →
  G.ArcsJoinEndpoints → G.WellDrawn →
  4 * M * G.V.card ≤ G.numEdges →
    G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings
```

Its hypotheses, **exactly** (read from the file):

* **H1** `∀ p q, multiplicity p q ≤ M` — `multiplicity` counts edge indices with
  endpoint-pair `{p,q}` (`CrossingLemma.lean:64`).
* **H2** `ArcsJoinEndpoints` — `param 0`, `param 1` of each arc equal the declared
  endpoint pair (`CrossingLemma.lean:108`).
* **H3** `WellDrawn` — the `crossings` field is `≥ crossingCount`, where
  `crossingCount` counts index pairs `i<j` with
  `interiorOfArc (arc i) ∩ interiorOfArc (arc j) ≠ ∅` (`CrossingLemma.lean:86,98`).
* **H4** threshold `4·M·|V| ≤ numEdges`.

**The statement mentions no ordering, no per-component structure, no Bézout, no
parametrization.** The only object property of an arc it reads is, via `H2` and
`H3`, the two endpoint anchors and the *interior set* `interiorOfArc` (the open-
interval image). `SimpleCurveArc.inj` (global injectivity, `CrossingLemma.lean:46`)
is used internally only to guarantee an arc is not a loop
(`endpoints_ne_of_arcsJoinEndpoints`, `CrossingLemma.lean:115`) and that the two
endpoint parameters are distinct. (PROVEN, in-repo, read directly.)

**Consequence (PROVEN, from the statement).** The crossing inequality is
*indifferent* to how edges are ordered or grouped by curve. The global injective
arc / global ordering can therefore only be *required*, if at all, on the
**construction side**: in building a `DrawnMultigraph` from the point–curve
incidence data and discharging two derived facts that drive the incidence bound:

* **E1** `numEdges ≥ I(P,Γ) − (slack)` (so that a lower bound on edges feeds the
  cube).
* **E2** `crossingCount ≤ M·|Γ|²` (so the `crossings` field may be set to `M|Γ|²`
  and `H3` holds).

`Theorem23Statement` itself (`Theorem23.lean:76`) is stated *purely
combinatorially*: a curve is a `Set`, incidence is membership, `TwoDegreesOfFreedom`
is "two curves meet in ≤M points; two points lie on ≤M curves," and the conclusion
is `incidenceCount ≤ C · incidenceBoundTerm`. There is **no `DrawnMultigraph`, no
arc, no ordering in the target**. The crossing-lemma machinery is the *proof route*
(Edge B), not the statement. So "does Edge B require the global arc?" is a question
about this one route, and B2 is internal to it. (PROVEN, read from `Theorem23.lean`.)

---

## 2. The line template, dissected: what makes its crossing bound work

The fully-formalized line case (`SzemerediTrotter.lean`) is the blueprint Edge B
generalizes. Its construction (read from source):

* `pointsOnLine P ℓ` (line 322): incident points of `ℓ`, **sorted by the linear
  functional** `lineKey ℓ` (`= −b·x + a·y`, the projection along `ℓ`'s direction;
  `lineKey`, line 281). This is *exactly* a "generic-functional sweep order"
  (candidate 1) — for a line.
* `edgesOnLine` (line 348): consecutive pairs `zip(pts, pts.tail)`. `k` points →
  `k−1` edges (`length_edgesOnLine`, line 393).
* `segmentArc p q h` (line 412): the **straight** segment, a `SimpleCurveArc`;
  injective because affine with `p ≠ q`.
* `stMultigraph` (line 482): `V := P`, edges `= allEdges` (concatenation over
  lines), `arc := segmentArc`, `crossings := |L|²`.

The incidence inputs:

* **E1 (line)** `incidences_le_numEdges_add` (line 1024):
  `I ≤ numEdges + |L|`. Proof: per line, `k` incident points give `≥ k−1` edges
  (`filter_card_le_edges`, line 1007); sum, slack `≤ |L|`. **The order is used only
  through `length_edgesOnLine` — i.e. only its order *structure* (it produces a
  list with `k−1` consecutive pairs).** A geometrically meaningless order would
  give the same count. (PROVEN, read.)

* **E2 (line)** `stMultigraph_wellDrawn` (line 1781): `crossingCount ≤ |L|²`, by
  injecting each crossing pair `(i,j)` into `(lineForEdge i, lineForEdge j) ∈ L×ˢL`.
  The injectivity of that map (read from the proof, lines 1804–1863) consumes
  **exactly two geometric facts**:
  1. **W3** `stMultigraph_same_line_disjoint` (line 1671): distinct **same-line**
     edges have **disjoint arc interiors**. Used to force `i₁=i₂`, `j₁=j₂` (within a
     line, ≤1 edge contains a given interior point).
  2. **`encard_inter_le_one_of_lines`** (line ~98): two distinct lines meet in
     ≤1 point. Makes the crossing point unique per line-pair (the Bézout analog).

**The engine of W3** (`edgesOnLine_interior_disjoint`, line 1440; read directly)
is the decisive structural fact. It uses, and *only* uses:

* **(W3-a)** `pointsOnLine_pairwise_lt` (line 1328): the incident points are
  **strictly sorted by `lineKey`** — which holds because `lineKey` is **injective on
  the whole line** (`lineKey_injOn`, line 307) and the list is `Nodup`.
* **(W3-b)** `lineKey_of_mem_interior` (line 1299): an interior point's `lineKey`
  value is a **strict convex combination** of the two endpoints' `lineKey` values,
  i.e. lies **strictly between** them — because `lineKey` is *affine along the
  segment* (`lineKey_affine_combination`, line 1283).
* Then consecutive open `lineKey`-intervals are disjoint (`edgesOnLine_lineKey_separated`,
  line 1421), so the interiors are disjoint.

**This is the crux for the whole question.** The line crossing bound does **not**
use a global 1-manifold parametrization. It uses *order-by-a-functional that is
injective and monotone along each edge-arc*. For a line, `lineKey` is injective on
the entire line and affine along every chord, so both (W3-a) and (W3-b) hold
globally and trivially. The question for curves is whether a functional with these
two properties — injective along the relevant arc, monotone (hence value-strictly-
between) along each edge — is **constructible on a curve** without a global
parametrization. (All of §2: PROVEN, read from `SzemerediTrotter.lean`.)

---

## 3. Candidate 1 verbatim (order by ℓ-value on the whole curve) FAILS

Order the incident points on a curve component by the value of a generic linear
functional ℓ restricted to the curve, globally, and pair consecutive-by-ℓ-value
points.

**This fails**, for a reason that is the curve-specific obstruction to (W3-b).

> **Counterexample (EMPIRICALLY VERIFIED, `/tmp/curve_sweep.py`).** On the unit
> circle `x²+y²=1` (one compact component) with ℓ = x-projection, take 8 incident
> points at angles `{10°,80°,100°,170°,190°,260°,280°,350°}`. Sorting by `x` value
> interleaves the upper and lower semicircles. The x-consecutive pair `(100°, 280°)`
> has **3 incident points strictly inside the short on-curve arc and 3 inside the
> long on-curve arc** between them. Therefore **no on-curve arc between this
> x-consecutive pair has interior free of other incident vertices.** More
> fundamentally: ℓ is *not injective along the curve* (the two semicircles share
> every x-value in `(−1,1)`), so "ℓ-consecutive on the curve" is not "adjacent
> along the curve," and a single curve-arc realizing the ℓ-edge with interior on
> the curve does not exist.

The obstruction is precisely the failure of (W3-a)/(W3-b): a generic linear
functional is **not injective along a curve** and **not monotone along an arbitrary
chord of the curve** — the curve revisits ℓ-values at turning points. So
candidate 1 *as stated* (global ℓ-order on the whole component) does not give the
disjoint-arc property the crossing bound needs, and does not even give arcs that
are sub-arcs of the curve. **Classification: FAILS (counterexample).** This is also
why Pach–de Zeeuw's intrinsic-order strategy uses the curve's *own* order, which is
what forces the parametrization the viability doc analyzed.

---

## 4. Candidate 2 (local arc + Bézout pairwise, no global order) is INSUFFICIENT alone

Can the crossing count be carried using only (i) the local IFT arc at nonsingular
points (Proposition L of the viability doc, PROVEN-tractable) and (ii) Bézout's
pairwise ≤(deg) intersection bound (`bezout`, in-repo), with **no** per-curve order?

**No — but the gap is precise and is *not* H3 itself.** Two distinct obligations
genuinely need an order or its substitute:

* **E1 needs a consecutive pairing that achieves `k−1` edges from `k` incident
  points on the curve, with each edge an *on-curve arc***. Without *some* order on
  the incident points of the curve (delivering `k−1` consecutive pairs) and an arc
  realizing each pair, there is no `numEdges ≥ I − slack`. The local arc (i) only
  produces arcs through *one IFT chart*, covering a short piece; two prescribed
  incident points generically do not lie in one chart. So (i)+(ii) alone do not
  produce the `k−1` edges. (PROVEN: the local arc's image is `g '' Metric.ball`
  for one ε-ball, `Bezout.lean:645`; two arbitrary incident points need not co-occur
  in one ball.)
* **E2/W3 needs same-curve consecutive arcs to have disjoint interiors**, which the
  Bézout pairwise bound *cannot supply*: two arcs that are sub-arcs of the **same**
  curve satisfy the same polynomial, so the algebraic intersection of their
  carriers is the whole curve, not a finite set. **Bézout (no-common-component) is
  vacuous for same-curve pairs.** (PROVEN: `bezout` requires
  `NoCommonCurveComponent`, `AlgebraicPrelim.lean:66,79`; two sub-arcs of one curve
  share that curve as a common component, so the hypothesis fails.) Same-curve
  interior-disjointness must come from the *order* (W3-style), exactly as in the
  line case — it is structurally a different fact from Bézout. (Corroborated by the
  independent pass, Q4.)

So candidate 2 alone is insufficient: the crossing count is **not** an artifact-
free consequence of local arcs + Bézout. A per-curve order (or a substitute giving
the same two facts: consecutive on-curve arcs, and their interior-disjointness) is
a **genuine** requirement of E1+E2, not of the abstract inequality H1–H4. The
viability doc's framing ("the order is cheap, the arc is the wall," its §6) is
*correct that the order need not be intrinsic*, but **incomplete**: the order must
still be one for which (W3-a)/(W3-b) hold, i.e. *one along which the chosen
functional is injective and monotone over each edge-arc*. That constraint is the
real content, and it is what candidate 3 below supplies.

---

## 5. Candidate 3 — the minimal object Székely consumes, and the ℓ-monotone-piece substitute

### 5.1 The minimal combinatorial object

From §1–§2, the crossing-number inequality (H1–H4) needs, per curve `γ`, exactly:

> an **interiorly-disjoint decomposition of (part of) `γ` into arcs whose endpoints
> are consecutive incident points**, such that (a) the arcs are `SimpleCurveArc`s
> with carrier ⊆ `γ` and interior in the nonsingular locus, (b) distinct arcs of
> the **same** curve have disjoint interiors, and (c) the number of arcs is
> `≥ |P ∩ γ| − (constant in deg γ)`.

It does **not** need a single globally-ordered sequence of all incident points on
`γ`, nor a global injective parametrization of `γ`. (PROVEN, by §1–§2: the
inequality reads only `interiorOfArc` and endpoints; W3 in the line case is a
*per-arc-pair* disjointness, assembled by an order whose only role is to make the
functional injective/monotone along each arc.) This is the answer to the task's
sub-question 3: **the per-edge object is an interiorly-disjoint arc decomposition,
not a global order.** A global order is *one way* to produce it; it is not the
minimal requirement.

### 5.2 The ℓ-monotone-piece construction

Pick a generic linear functional ℓ; after a generic rotation, take ℓ = the
x-projection. **Cut `γ` at** (i) its singular points (finite, in-repo bounded), and
(ii) its **ℓ-critical points** — points where the tangent is ℓ-vertical, i.e.
`∂₁h = 0` while on `γ` (`∇h ∥ ∇ℓ`), which is `{h = 0} ∩ {∂₁h = 0}`, a finite
Bézout-bounded set when `h` is irreducible (the two curves `h`, `∂₁h` share no
component). On each resulting **piece**, the curve has no ℓ-vertical tangent, so
(pointwise) `∂₁h ≠ 0` and ℓ = x is a graph coordinate; **ℓ is strictly monotone
along the piece**, hence **injective on the piece**. Order the incident points
*within each piece* by ℓ-value; edges = consecutive-within-piece pairs.

This restores both (W3-a) and (W3-b) **on each piece**, because on a piece ℓ is
injective (W3-a) and the edge-arc is a graph `y = ψ(x)` with x affine, so an
interior point's ℓ-value is strictly between the endpoints' (W3-b). So W3 transfers
verbatim. (PROVEN-modulo-the-decomposition; see 5.4 for what is and is not free.)

### 5.3 What this dissolves (relative to the viability doc)

The viability doc's primary obstruction **G-B2-arc (its node 4c)** was: *upgrade a
path to an injective topological arc / construct a strictly-monotone global
parameter to kill loop-revisits.* On an ℓ-monotone piece this **is gone**:

* **No loop-revisit / injectivity problem.** Distinct x-values give distinct points
  (ℓ injective on the piece), so the graph map `t ↦ (x(t), ψ(x(t)))` is injective
  via its **first coordinate** — the same trivial injectivity the in-repo local arc
  already uses (`Bezout.lean:640`, `hg_inj` via the first coordinate) and the line
  `segmentArc` uses. **The global monotone parameter the viability doc §5 said was
  "the analytic core of a missing 1-manifold theorem" is, on a monotone piece,
  ℓ itself — supplied for free by the cut.** (PROVEN: injectivity-via-first-
  coordinate is already in-repo; the only new input is that the *whole edge-arc*
  lies in one monotone piece, which is what the cut guarantees.)
* **No turning-point chart-switch inside a piece** (viability §5 item 3): a piece
  has no ℓ-vertical tangent by construction, so there is never a graph-over-x ↔
  graph-over-y switch *inside* a piece. The switch happens only *at* cut points,
  which become vertices, never arc interiors.

It also **sidesteps the secondary obstruction G-B2-sing (its 4d, singular
endpoints / Puiseux):** singular incident points are *cut points*, hence treated as
extra vertices and **excluded from edge endpoints**, charged to the constant (5.5).
No local real-branch decomposition at a singularity is needed for this route.
(PROVEN-modulo the edge-count accounting in 5.5.)

### 5.4 What survives — the single relocated obligation (CONJECTURED / ABSENT)

The reframe does **not** make the whole thing free. The surviving from-scratch
content is one statement, strictly narrower than the viability doc's wall:

> **Generic monotone graph decomposition (the surviving obligation).** For an
> irreducible degree-`d` real plane curve `γ` and a generic linear functional ℓ,
> the set `γ ∖ (singular ∪ ℓ-critical ∪ ∞-cut)` is a **finite disjoint union of
> ℓ-graph pieces**, each of which is a connected set on which ℓ is injective and
> over which `γ` is the graph of a single continuous `ψ`, with the number of pieces
> bounded by a constant `c(d)` depending only on `d`.

Two sub-points, both confirmed by the independent pass and by scratch analysis:

* **Building the single ψ on a closed sub-interval is a clopen continuation over
  the x-INTERVAL, not over the curve.** (EMPIRICALLY VERIFIED structure,
  `/tmp/single_psi.py`.) Define
  `S = {x ∈ [x_P,x_Q] : ∃ continuous ψ on [x_P,x] with ψ(x_P)=y_P, graph ⊆ γ,
  agreeing with the local IFT solution near each point}`. `S` is **open** (local IFT
  + the *bidirectional* IFT local-uniqueness lemma
  `ContDiffAt.eventually_apply_eq_iff_implicitFunction`, present in v4.30 per the
  viability table, forces the extension to agree), **closed** (ψ bounded on the
  no-vertical-tangent band ⟹ limit exists; `γ` closed ⟹ limit point on `γ`; IFT
  there extends), and **nonempty** (`x_P ∈ S` by the in-repo local arc). Since
  `[x_P,x_Q]` is a **connected interval** (PROVEN in mathlib), `S = [x_P,x_Q]`.
  - **Why this is *not* the viability doc's §5 obstruction.** The viability doc ran
    the clopen argument **over the curve component**, which simultaneously
    reconstructs arc-connectedness (its 4a) *and* needs a global monotone parameter
    to kill loop-revisits (its 4c). Here the clopen runs over `[x_P,x_Q] ⊆ ℝ`,
    which is *already* connected (no curve-topology needed for connectedness), and
    ℓ = x *is* the monotone parameter by the no-vertical-tangent cut, so there are
    **no revisits to kill** — distinct x ⟹ distinct points. The two hardest pieces
    of the viability §5 argument (establish connectedness/arc-connectedness of the
    curve piece; construct a strictly-monotone global parameter) are replaced by
    "the interval is connected" and "ℓ is the parameter." What remains is the
    *infrastructure* (open + closed + connected) plus the analytic input "no
    vertical tangent on the band ⟹ ψ continuable and bounded." That infrastructure
    is genuine Lean work but is **bounded and chart-local**, not a 1-manifold
    classification. (Classification: **CONJECTURED-constructible, bounded**; no
    single mathlib lemma packages it, but every step is a named mathlib brick:
    `IsPreconnected.image`, the bidirectional IFT, `isHomeomorph_iff_continuous_
    bijective` for the compact-piece homeomorphism, `ContinuousOn.strictMonoOn_of_
    injOn_Icc` for the converse direction. EMPIRICALLY VERIFIED (search) that these
    bricks exist in v4.30.)
  - **Honest caveat (do not overstate).** I have **not** discharged this clopen
    argument in Lean, and the "closed" step's analytic input (ψ stays bounded /
    continuable up to the closed endpoint *because* the endpoint is interior to one
    monotone piece, so `∂₁h ≠ 0` there) must be threaded carefully — it is true on
    an *open* monotone piece but requires the endpoints `x_P,x_Q` to be strictly
    inside one piece, which is exactly why cut points are excluded as endpoints. The
    decomposition theorem above is what guarantees "the whole `[x_P,x_Q]` stays in
    one monotone piece." So 5.4 and the decomposition are **mutually entangled**:
    the per-arc ψ-construction is clean *given* the decomposition, and the
    decomposition is the actual missing theorem.

* **The piece-count bound `c(d)` must include unbounded ("∞") pieces — my first
  formula was wrong.** (PROVEN-counterexample, supplied by the independent pass.)
  The naive `#pieces ≤ #critical + #singular + 1` is **false**: `xy = 1` has **two
  real components** (the two hyperbola branches), each ℓ = x-monotone with **no
  affine x-critical points and no singular points**, yet **2 pieces**. The correct
  constant must also count unbounded pieces / pieces separated "at infinity":
  `c(d) = B_sing(d) + B_crit(d) + U_∞(d)`, with `B_sing(d) ≤ (d+1)^5` (in-repo
  `finite_singularities_of_irreducible_bound`), `B_crit(d)` a crude Bézout bound for
  `{h=0} ∩ {∂₁h=0}`, and `U_∞(d)` a degree-bounded count of unbounded pieces —
  the last of which has **no in-repo or mathlib lemma** and is part of the
  surviving from-scratch theorem.

### 5.5 The edge-count and crossing-count survive the cut (PROVEN-modulo-decomposition)

Given the decomposition (5.4), the rest is bookkeeping that ports from the line case
and is corroborated by the independent pass (Q3, Q4):

* **E1 corrected.** Per curve, `edges(γ) ≥ incidences(γ) − |cut(γ)| − #pieces(γ)`,
  so `numEdges ≥ I − c(d)·|Γ|` with `c(d)` as in 5.4. **The asymptotic survives.**
  If `I ≤ 2c(d)|Γ|`, the bound `I = O(|Γ|)` is absorbed into the `|Γ|` term of
  `incidenceBoundTerm`. If `I > 2c(d)|Γ|`, then `numEdges ≥ I/2`, and the cube
  `numEdges³ ≤ 64M|V|²·crossings` yields the same `|P|^{2/3}|Γ|^{2/3}` term with the
  constant enlarged by `c(d), M` — exactly the structure of the line-case
  `szemerediTrotter_of_*` lemmas (`SzemerediTrotter.lean:166–225`). (PROVEN given
  the decomposition; the algebra is the in-repo line algebra with an enlarged
  additive slack.)
* **E2 corrected.** Crossings split by curve-pair:
  - `γ ≠ γ'`: the crossing point lies in `γ ∩ γ'`, which has `≤ M` points by
    `TwoDegreesOfFreedom`; injecting crossing pairs into `Γ×ˢΓ` with `≤ M` per pair
    gives `≤ M|Γ|²`. (PROVEN given W3 per curve; structurally the line `wellDrawn`
    injection with `encard_inter_le_one_of_lines` replaced by the 2-DOF `≤ M`.)
  - `γ = γ'`, same piece: interior-disjoint by W3 on the monotone piece (5.2). Zero
    crossings. (PROVEN given the monotone-piece W3.)
  - `γ = γ'`, different pieces: the arc interiors lie inside **disjoint open pieces**
    (components of `γ ∖ cut`), so they can meet only at cut points, which are
    endpoints not interiors ⟹ **zero interior crossings**. (PROVEN **given the
    decomposition's disjoint-partition property** — which is the surviving
    obligation; a resultant/Bézout count is the *wrong tool* here, since both pieces
    satisfy the same polynomial, so disjointness must come from the decomposition,
    not from Bézout. Corroborated, Q4.)

So E1+E2 hold **conditionally on the generic monotone graph decomposition** and
otherwise reduce to the in-repo line algebra. (Classification: **PROVEN-modulo the
decomposition theorem of 5.4.**)

---

## 6. Verdict

| Object | Status | Evidence |
|---|---|---|
| Crossing inequality needs a global order/arc | **NO (PROVEN)** | `CrossingLemmaMultigraphStatement` reads only endpoints + `interiorOfArc`; `Theorem23Statement` is purely combinatorial (§1) |
| Candidate 1: global ℓ-order on the whole curve | **FAILS (counterexample)** | `/tmp/curve_sweep.py`: ℓ not injective along curve; ℓ-consecutive ≠ curve-adjacent; no vertex-free on-curve arc (§3) |
| Candidate 2: local arc + Bézout pairwise only | **INSUFFICIENT (PROVEN)** | local arc covers one chart; Bézout vacuous for same-curve pairs (`NoCommonCurveComponent` fails); same-curve disjointness must come from an order (§4) |
| Candidate 3: ℓ-monotone-piece order | **DISSOLVES the primary + singular obstructions; relocates residual** | W3 transfers on a monotone piece; ℓ = the monotone parameter for free; singular pts charged to constant (§5) |
| Viability 4c (path→injective arc / loop-revisit) | **DISSOLVED on a monotone piece** | injectivity via first coordinate; no revisits since ℓ injective on piece (§5.3) |
| Viability 4d / G-B2-sing (singular endpoints) | **SIDESTEPPED** | singular pts are cut vertices, excluded from edge endpoints (§5.3) |
| Per-arc ψ on a closed sub-interval | **CONJECTURED-constructible, bounded** | clopen continuation over the *interval* (not the curve) + named mathlib bricks; **not discharged in Lean** (§5.4) |
| **Generic monotone graph decomposition** (the surviving theorem) | **CONJECTURED / ABSENT from mathlib v4.30** | finite ℓ-graph-piece partition with degree-bounded count *including unbounded pieces* `U_∞(d)`; no in-repo or mathlib lemma; `xy=1` shows the naive count is wrong (§5.4) |
| E1, E2 (edge/crossing counts) | **PROVEN modulo the decomposition** | port of line algebra with enlarged additive slack + 2-DOF `≤ M` per pair (§5.5) |

**Headline.** The global injective-arc / global per-component linear-ordering
primitive (B2 as the viability doc framed it) is **NOT a genuine requirement of
Edge B's crossing count.** It is an **artifact of the intrinsic-order strategy.**
A weaker substitute — the **ℓ-monotone-piece decomposition** — carries the crossing
count and **dissolves the two obstructions the viability doc named as the wall**
(the path→injective-arc / loop-revisit problem 4c, by using ℓ as the global monotone
parameter on each piece for free; and the singular-endpoint Puiseux problem 4d, by
charging singular/critical points to a degree-bounded additive constant). What
*survives* is **a single, strictly narrower from-scratch theorem**: the **generic
monotone graph decomposition** of a real plane curve into a degree-bounded finite
disjoint union of ℓ-graph pieces (§5.4). This is **absent from mathlib v4.30 and
from the in-repo seeds** (the repo has no curve-component / arc-connectedness /
monotone-on-curve content — EMPIRICALLY VERIFIED by search), so it is still a
closure blocker unless taken as a Tier-B interface; but it is materially **smaller**
than the viability doc's wall (no Moore arc theorem, no 1-manifold classification,
no Puiseux), and several of its steps are named mathlib bricks.

**So the task's binary resolves as a refinement, not a clean (i) or (ii):**

* It is **not** deliverable (i) in full — I cannot give a reformulated crossing
  count whose *every* step cites a named in-repo/mathlib lemma, because the
  decomposition theorem of §5.4 has no such lemma and is not discharged.
* It is **not** deliverable (ii) in the strong form either — the global injective
  arc is **not** a true wall for Edge B; a mathlib-constructible-direction substitute
  removes it.
* The accurate deliverable is **(ii′): the minimal surviving primitive is the
  "generic monotone graph decomposition" of §5.4**, which is *narrower* than B2 as
  previously stated, *partially* built from mathlib bricks (the per-arc ψ and W3),
  but whose core finite-piece-partition statement (with the `U_∞(d)` unbounded-piece
  count) is from-scratch real-algebraic-curve topology absent from v4.30. Closure of
  Edge B must route through either *that* development or a (smaller, sharper) Tier-B
  interface axiom — **not** through the larger B2 arc primitive, and **not**
  necessarily through polynomial partitioning.

This **sharpens** the prior verdict: the prior "wall" (Moore arc theorem +
1-manifold parametrization + Puiseux) is **larger than necessary**; the genuine
minimal obstruction is the monotone graph decomposition, and the path→arc /
singular-endpoint pieces of the prior wall are **avoidable**.

---

## 7. What next (ranked)

1. **(GO sub-brick — unchanged, do regardless) Formalize the per-arc graph
   `SimpleCurveArc` from a single IFT chart (Proposition L).** Already PROVEN-
   tractable in the viability doc; it is the atom every later step consumes, and the
   ℓ-monotone route uses it *unchanged* (the local arc + first-coordinate
   injectivity). On the Edge-B critical path. *FLAG FOR IMPLEMENTER:* extract
   `Continuous ψ` on an open subinterval from `contDiffAt_implicitFunction`; restrict
   to a closed subinterval; package as `SimpleCurveArc` with carrier ⊆ `γ`.

2. **(The decisive scoping target — new, replaces the viability doc's "Moore arc
   theorem first" recommendation) Pin and attempt the per-arc clopen continuation
   over the x-interval (§5.4 first bullet).** Statement to formalize: *given an
   irreducible `h`, a generic rotation making ℓ = x, two points `P=(x_P,y_P)`,
   `Q=(x_Q,y_Q)` on `γ` with `x_P < x_Q` and `∂₁h ≠ 0` everywhere on the band
   `γ ∩ {x ∈ [x_P,x_Q]}` over which they lie on one branch, there is a single
   continuous `ψ : [x_P,x_Q] → ℝ` with `ψ(x_P)=y_P`, `ψ(x_Q)=y_Q`, and graph ⊆ `γ`.*
   Proof skeleton: clopen `S ⊆ [x_P,x_Q]`, OPEN by the **bidirectional** IFT
   uniqueness lemma, CLOSED by boundedness on the no-vertical-tangent band + `γ`
   closed, connected interval ⟹ `S = [x_P,x_Q]`. **This is the part that genuinely
   differs from the viability doc and is the lightest non-trivial Lean target.** It
   is *bounded* (interval connectedness, not curve topology). Do this **before** any
   1-manifold or Moore-arc work — it may show the decomposition's per-arc half is
   wholly in reach, isolating the residual to the finite-piece partition + `U_∞(d)`.

3. **(The actual remaining obligation — scope, then decide) The generic monotone
   graph decomposition (§5.4), with the corrected `c(d) = B_sing + B_crit + U_∞`.**
   The two new ingredients absent from §2's per-arc work are: (a) that the cut set is
   finite and degree-bounded — `B_sing` is in-repo (`(d+1)^5`), `B_crit` is a Bézout
   application (`{h=0}∩{∂₁h=0}`, no common component when `h` irreducible — fits the
   in-repo `bezout` shape); (b) the **finite-piece partition with the unbounded-piece
   count `U_∞(d)`**, which has no in-repo/mathlib lemma. Scope (b) precisely; it is
   the genuine from-scratch core. **Decision input for Adam:** if (b) is too large,
   the Tier-B interface to axiomatize is now *much smaller and sharper* than the
   viability doc's: not "a global injective arc between same-component points," but
   "`γ ∖ (B_sing ∪ B_crit ∪ ∞) =` a `c(d)`-bounded disjoint union of ℓ-graph pieces."
   Surface this as the candidate interface; it is the same *kind* of object as
   Milnor–Thom (a real-algebraic structure theorem), consistent with the existing
   Tier-B treatment, but materially smaller than the previously-named wall.

4. **(Confirm the generic-rotation reduction is free) The "after a generic rotation
   ℓ = x-projection" step** must be a genuine reduction, not a smuggled assumption:
   for a *fixed finite* `P, Γ`, a generic direction simultaneously (i) makes every
   `γ ∈ Γ` have finitely many ℓ-critical points, (ii) separates the incident points'
   ℓ-values per piece, and (iii) avoids ℓ-vertical asymptotes. Each is an
   "avoid finitely many bad directions" argument (the bad directions are a finite/
   measure-zero set for fixed finite data). Confirm this is a clean
   `∃ direction, (finite avoidance)` lemma (it should be — it is finite avoidance in
   the circle of directions) before committing to the route; it is *not* itself a
   curve-topology obstruction, but it must be stated to make E1/E2 unconditional in
   the chosen direction. (Classification: CONJECTURED-tractable, finite-avoidance;
   verify it does not hide a uniformity-over-`Γ` issue.)

**Do not** invest in: (a) the Moore/Menger path→arc theorem or a 1-manifold
classification — the monotone-piece route **avoids** them (§5.3); (b) Puiseux /
local singular-branch decomposition — singular endpoints are charged to the
constant (§5.3); (c) candidate 1 (global ℓ-order) — it fails (§3); (d) carrier-type
changes — `SimpleCurveArc` is already general.
