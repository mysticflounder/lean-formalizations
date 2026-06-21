# B2 viability — is the per-branch `SimpleCurveArc` constructible in mathlib v4.30?

**Scope.** This is an analysis document. It introduces no Lean code, no `sorry`, and adds no
theorems. It answers one question from the Edge-B feasibility scope
(`docs/corollary24-edge-feasibility.md`, §3 / node B2): is the load-bearing B2 object — a
`SimpleCurveArc` whose image lies in a real plane algebraic curve `γ`, joining two consecutive
incident points on a common branch — *constructible* from the in-repo IFT seeds plus mathlib
v4.30, and if so, by what grounded sub-lemmas?

**Verification basis.** All "PRESENT in mathlib v4.30" / "ABSENT in mathlib v4.30" claims below
were checked against this repo's pinned copy at
`.lake/packages/mathlib/Mathlib` (`lean-toolchain` = `leanprover/lean4:v4.30.0`,
`lake-manifest.json` mathlib `inputRev = v4.30.0`, both confirmed). In-repo claims cite a
declaration whose statement I read directly in `Bezout.lean` / `AlgebraicPrelim.lean` /
`CrossingLemma/CrossingLemma.lean`. I did **not** run `lake build`. Source-search results are
labeled as such; an absence found by `grep` over the source tree is recorded as
EMPIRICALLY VERIFIED (search), not as a theorem.

Date: 2026-06-20.

---

## 1. The exact target object

From `CrossingLemma/CrossingLemma.lean:43`:

```
structure SimpleCurveArc where
  param : Set.Icc (0 : ℝ) 1 → ℝ × ℝ
  cont  : Continuous param
  inj   : Function.Injective param
  carrier : Set (ℝ × ℝ) := Set.range param
```

The B2 object the scope reduces to (verbatim from `corollary24-edge-feasibility.md`):

> Between two consecutive incident points on a common branch of the real algebraic curve `γ`, a
> `SimpleCurveArc` (injective continuous `[0,1] → ℝ²`, image ⊆ `γ`) joining them.

So B2 must produce, for the irreducible plane curve `γ = PlaneCurveZeroSet h`
(`h : MvPolynomial (Fin 2) ℝ`, irreducible, `totalDegree ≤ d`) and two prescribed points
`P, Q ∈ P ∩ γ` that are "consecutive on a common branch", a term `a : SimpleCurveArc` with

* `a.param 0 = P`, `a.param 1 = Q` (after the `ℝ × ℝ` / `EuclideanSpace ℝ (Fin 2)` identification;
  `Point2 := EuclideanSpace ℝ (Fin 2)`, `AlgebraicPrelim.lean:22`),
* `a.carrier ⊆ γ` (image in the curve),
* `a.cont`, `a.inj` (continuous, *injective* — this is the load-bearing word).

`SimpleCurveArc` and `DrawnMultigraph` are already general enough for curved arcs (the scope and
the structure docstring both confirm this); **no carrier change is required**. The whole question
is whether the arc *value* exists and can be built.

---

## 2. Notation and the in-repo seeds, read directly

* `PlaneCurveZeroSet h := {z : Point2 | eval (fun i => z i) h = 0}` (`AlgebraicPrelim.lean:118`).
* `SingularPointSet h := PlaneCurveZeroSet h ∩ {∂₀h = 0} ∩ {∂₁h = 0}` (`Bezout.lean:444`) — the
  points of `γ` where *both* partials vanish. Call its complement in `γ` the **nonsingular
  locus** `γ* := γ \ SingularPointSet h`.
* `evalPlane h : ℝ × ℝ → ℝ` (`Bezout.lean:450`), the smooth (`ContDiff ℝ ⊤`) evaluation map whose
  zero set is `γ` (under the `ℝ × ℝ ≃ Point2` identification).

**Seed S1 (PROVEN, in-repo).** `finite_singularities_of_irreducible_bound` (`Bezout.lean:1078`):
for irreducible `h` of degree `≤ d` with some nonzero partial,
`(SingularPointSet h).Finite ∧ ncard ≤ (d+1)^5`. So `γ*` is `γ` minus a finite, degree-bounded
set.

**Seed S2 (PROVEN, in-repo).** `irreducible_has_nonzero_partial` (`Bezout.lean:873`): for
irreducible `h`, `∂₀h ≠ 0 ∨ ∂₁h ≠ 0` (as polynomials). Combined with the local non-vanishing at a
nonsingular point this is what makes IFT applicable.

**Seed S3 (PROVEN, in-repo) — the local arc is already half-built.**
`nonsingular_point_has_infinite_zeroSet_of_partial1` (`Bezout.lean:544`) and its `partial0`
sibling (`Bezout.lean:659`) construct, at a point `z ∈ γ` with `∂₁h(z) ≠ 0` (resp. `∂₀h(z) ≠ 0`):

* the mathlib implicit function `ψ := cdImplicitFunction hcont hn hinv : ℝ → ℝ`
  (`Bezout.lean:629`), via the in-repo adapters `cdImplicitFunction` / `cdApplyImplicitFunction`
  (`Bezout.lean:69–78`) over mathlib's `ContDiffAt.implicitFunction`;
* an honest open ball `Metric.ball a.1 ε` (`Bezout.lean:636`, the germ `∀ᶠ` is already discharged
  to an ε-ball via `Metric.mem_nhds_iff.mp`);
* the map `g : ℝ → Point2 := fun x => mkPoint2 x (ψ x)` with **`Set.InjOn g (Metric.ball a.1 ε)`**
  (`Bezout.lean:640`, injectivity proven *via the first coordinate*) and
  **`g '' Metric.ball a.1 ε ⊆ PlaneCurveZeroSet h`** (`Bezout.lean:645`).

This is, already in the repo, an **injective continuous map from an interval into `γ`** — i.e. a
local `SimpleCurveArc` building block, missing only the `[0,1]`-reparametrization packaging and an
explicit `Continuous` field (the repo currently only needs `InjOn`+image; continuity of `g`
follows from `Continuous ψ`, available but not extracted there — see §3).

---

## 3. The mathlib v4.30 IFT surface, read directly (what is and isn't there)

From `Mathlib/Analysis/Calculus/ImplicitContDiff.lean` and
`Mathlib/Analysis/Calculus/ImplicitFunction/{ProdDomain,Bivariate}.lean`:

| Fact | Lemma | File:line | Gives |
|---|---|---|---|
| ψ passes through the point | `ContDiffAt.implicitFunction_apply_self` | ImplicitContDiff:66 | `ψ u.1 = u.2` |
| ψ is `Cⁿ` at the base point | `ContDiffAt.contDiffAt_implicitFunction` | ImplicitContDiff:90 | `ContDiffAt ℝ n ψ u.1` ⟹ **`ContinuousAt ψ u.1`** |
| local equation | `ContDiffAt.eventually_apply_implicitFunction` | ImplicitContDiff:72 | `∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u` |
| **bidirectional** local graph | `ContDiffAt.eventually_apply_eq_iff_implicitFunction` | ImplicitContDiff:77 | `∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2` |
| bivariate packaging | `eventually_apply_eq_iff_implicitFunctionOfBivariate` | Bivariate:69 | same, curried `ℝ→ℝ→ℝ` |

**PROVEN consequence (local arc).** The bidirectional lemma (ImplicitContDiff:77) says: there is an
open neighborhood `U ∋ z` in `ℝ²` such that `γ ∩ U = graph(ψ) ∩ U`. With
`ContinuousAt ψ` (ImplicitContDiff:90, upgradeable to continuity on an open subinterval since
`evalPlane h` is `C^∞` everywhere, so the IFT hypotheses hold on an open set), the map
`x ↦ (x, ψ x)` restricted to a closed subinterval `[a,b] ⊆ (x₀−ε, x₀+ε)` is:
* continuous (composition with `Continuous ψ`),
* **injective**, because mathlib's `isEmbedding_graph` (`Topology/Constructions/SumProd.lean:602`,
  `Continuous f → IsEmbedding (fun x => (x, f x))`) — or simply projection to the first coordinate —
  makes the graph map injective,
* image in `γ` (the local equation).

Reparametrized from `[a,b]` to `[0,1]` (affine, mathlib `Set.Icc`/`affineHomeomorph` arithmetic),
this **is** a `SimpleCurveArc` with carrier in `γ`. So:

> **Proposition L (local arc).** *Constructible now.* For a nonsingular `z ∈ γ` and a small enough
> closed subinterval of the IFT graph around `z`, there is a `SimpleCurveArc` with carrier ⊆ `γ`
> passing through `z`. **Classification: PROVEN-tractable** — every input is PRESENT (in-repo S3 +
> mathlib `isEmbedding_graph` + interval reparametrization). Confidence: high. This is the genuine
> first brick toward B2 and is the same lemma the scope ranks as its candidate-2 first brick.

What Proposition L does **not** give: an arc between two *prescribed* points `P, Q` unless they
happen to lie in one IFT chart with `P, Q` as its endpoints. In general they do not.

---

## 4. The global gap, isolated precisely

B2 needs an arc between *prescribed consecutive* incident points `P, Q` on a *common branch*. The
local charts of §3 cover `γ*` but each covers only a short piece. Assembling them into one
injective `[0,1] → ℝ²` from `P` to `Q` requires three things in sequence. I classify each against
mathlib v4.30.

### 4a. Local-path-connectedness of `γ*` (or of a component of it)

To talk about "same branch ⟹ joined by a path", the standard route is
`connectedComponent_eq_iff_joined` (`Topology/Connected/LocPathConnected.lean:112`): in a
**locally path-connected** space, two points in the same connected component are `Joined`. Also
`PathConnectedSpace.of_locPathConnectedSpace [ConnectedSpace X]` (line 102) and
`IsOpen.isConnected_iff_isPathConnected` (line 163).

To use any of these on `γ*` we must first establish `LocPathConnectedSpace γ*` (subspace
topology). The mathematically true statement is: `γ*` is locally homeomorphic to an open interval
of `ℝ` (by §3), and `ℝ` is locally path-connected, so `γ*` is locally path-connected.

* **mathlib has `ChartedSpace.locPathConnectedSpace [LocPathConnectedSpace H] : LocPathConnectedSpace M`**
  (`Geometry/Manifold/ChartedSpace.lean:268`). So *if* `γ*` were registered as a
  `ChartedSpace ℝ` (or as `ChartedSpace (interval)`), local path-connectedness would follow.
* **mathlib does NOT have** `IsLocalHomeomorph _ → LocPathConnectedSpace _`, nor
  `LocPathConnectedSpace` for a subset that is merely locally Euclidean. Source search for
  `IsLocalHomeomorph.*locPath` / `Homeomorph.*locPathConnected` (over the whole tree) returned
  nothing. `IsOpen.locPathConnectedSpace` (line 160) requires the subset be **open in `ℝ²`** — but
  `γ` is **closed**, not open, so it does not apply. (EMPIRICALLY VERIFIED by search.)

**Status of 4a.** Establishing `LocPathConnectedSpace γ*` from the IFT charts is **from-scratch**.
The cleanest in-mathlib path is to build a `ChartedSpace ℝ` instance on `γ*` from the local graphs
and invoke `ChartedSpace.locPathConnectedSpace`. Building that instance is itself the
"register the nonsingular real algebraic curve as a 1-chart" development — bounded in principle,
but it requires producing compatible `PartialHomeomorph γ* ℝ` charts at every point, which means
covering both the `∂₁h ≠ 0` (graph over x) and `∂₀h ≠ 0` (graph over y) cases and the transition
maps on overlaps. None of this is packaged; it is multi-lemma. Alternatively, prove
`LocPathConnectedSpace.of_bases` (line 61) directly with the open IFT graphs as the basis — also
from-scratch, also multi-lemma. **Classification: CONJECTURED-constructible (from-scratch, bounded);
no single mathlib lemma; the local-homeomorphism→LocPathConnected transfer is absent.**

### 4b. From `Joined`/`Joined­In` to a *path* — present, but only a path

Given 4a, `JoinedIn γ* P Q` yields `JoinedIn.somePath : Path P Q` with
`JoinedIn.somePath_mem : ∀ t, somePath t ∈ γ*` (`Topology/Connected/PathConnected.lean:183,186`).
That is a **continuous** map `[0,1] → ℝ²` with image in `γ*ⁿ` and the right endpoints.

**It is not injective.** `Path` carries no injectivity. A path produced by `Joined.trans`
(concatenation of chart paths) generically backtracks and revisits points. `SimpleCurveArc.inj`
is exactly what this does not provide.

**Status of 4b.** PRESENT in mathlib (the path exists once 4a is in hand), but it is the *wrong
object*: it is a path, not a simple arc.

### 4c. Upgrading a path to an *injective* arc — the load-bearing absence

The classical theorem that closes the gap is the **Moore / Menger arc theorem**: *in a Hausdorff
space, if `x` and `y` are joined by a path, they are joined by an arc* (an injective continuous
`[0,1] → X`); equivalently, *path-connected Hausdorff ⟹ arc-connected*. `ℝ²` is Hausdorff, so this
would deliver the injective arc inside the image of the path (hence inside `γ`).

* **mathlib v4.30 does NOT have this theorem in any form.** Source search across the whole tree for
  arc-connectedness / Hahn–Mazurkiewicz / Moore / Menger / "path can be replaced by an arc" /
  "injective path from `Joined`" returned **nothing** relevant: the only injective-path content is
  `Path.segment` injectivity (straight segments only, `Analysis/Convex/PathConnected.lean:70`) and
  `SimpleGraph` combinatorial paths. No theorem produces an *injective topological* arc from a
  path. (EMPIRICALLY VERIFIED by search.)
* mathlib also lacks the closely related structure theorems that would give an alternative route:
  **no Jordan curve theorem** (the `Jordan` hits are Jordan–Hölder / Jordan groups, unrelated),
  **no 1-manifold classification** ("a connected 1-manifold is `ℝ` or `S¹`"), **no semialgebraic /
  real-algebraic-geometry library at all**. (EMPIRICALLY VERIFIED by search.)

**Status of 4c.** **ABSENT.** The path→arc upgrade is the single missing mathematical object, and
it is not a one-liner: the standard proof (Moore 1916, via the "arc in a path" / Hausdorff
characterization) is a genuine point-set-topology development (it uses, e.g., a nested-interval /
quotient construction collapsing the path's loops). This is the deepest part of B2.

### 4d. Singular points and "consecutive on a branch"

Two refinements that do **not** rescue 4c but do shape what must be proven:

* **"Branch" must mean a component of `γ*`, not of `γ`.** A connected component of the *full* curve
  `γ` can pass from one local branch to another *only through* a singular point (at a node, the two
  local branches are joined precisely at the node; the node-deleted neighborhood is disconnected).
  So if "branch" meant "component of `γ`", a within-branch arc could be forced through a node, and
  the local-graph route (§3) would break there. The correct definition is **branch = connected
  component of the nonsingular locus `γ* = γ \ SingularPointSet h`**. With that definition the local
  graph charts cover each branch and chart-continuation stays in `γ*`. (This is the refinement the
  cross-check surfaced; it does not remove any obstruction but it fixes the statement.)
* **Avoiding singularities (interior).** "Consecutive on a branch" (branch = component of `γ*`) is
  then defined so the *interior* of each arc lies in `γ*` (avoids the finite `SingularPointSet h`).
  The crossing lemma only needs `interiorOfArc ⊆ γ` and consecutiveness; routing arc interiors
  through `γ*` is legitimate. So the *interior* never needs to pass a node/cusp.
* **Endpoints that are singular.** If an incident point `P ∈ P` is *itself* a singular point of `γ`
  (a node or cusp), the local-graph route (§3) **fails at `P`**: at a node `γ` is locally two
  crossing branches (not a graph of x, nor of y, as a single function); at a cusp `γ` is locally a
  graph but with a vertical/horizontal tangent and the IFT hypothesis `∂h ≠ 0` is **false** there.
  Delivering even a *one-sided* arc that terminates at such a `P` requires resolving which branch
  through `P` the arc attaches to — i.e. a **local branch decomposition at a singular point of a
  real algebraic curve**, which is Puiseux/Newton-polygon territory and is **absent from mathlib**
  (no Puiseux series over `ℝ`-with-the-real-topology branch analysis; the `RingTheory` Puiseux/
  Hahn-series content is algebraic, not a real-topological branch separation). So singular incident
  points are a *second* from-scratch obstruction, on top of 4a/4c.
  - One can try to *push this into the definition*: define the incident-point ordering so that
    singular points are treated as shared vertices and the arcs are per-branch one-sided pieces.
    This is exactly the "treat a singular point as a vertex shared by the incident branches" clause
    the scope flags. It still requires the local branch count/decomposition at the singular point to
    even *state* which one-sided pieces exist, so it does not remove the Puiseux-grade need; it
    relocates it.

### 4e. Shape mismatch and non-compact / loop components

`SimpleCurveArc` is `[0,1] → ℝ²` (a *compact* domain). Real algebraic curve components come in two
topological shapes that both matter:

* **Loop (compact, no boundary)** — e.g. the circle `x²+y²−1`, a single component homeomorphic to
  `S¹`. Two points `P ≠ Q` on it are joined by *two* arcs (the two ways around). "Consecutive"
  must pick the arc with no other incident point inside; this is fine for `[0,1]` *once an arc is
  chosen*, but the choice needs the cyclic order on the loop, which is again 1-manifold structure.
* **Open arc (non-compact, possibly unbounded)** — e.g. a line, or a hyperbola branch `xy−1`. The
  component is homeomorphic to `ℝ`, not to `[0,1]`. A `SimpleCurveArc` between two of its points is
  a *sub-arc* (the closed piece between them), which is fine — but again selecting it needs the
  linear order on the `ℝ`-branch.

In both shapes the `[0,1]` *target* is the right shape *for the sub-arc between P and Q*, so the
shape is not itself an obstruction; but choosing which sub-arc ("consecutive") presupposes the
per-component order (cyclic on a loop, linear on an `ℝ`-branch), which is precisely the structure
4a/4c would have to supply. See §6 for how weak this order can be.

---

## 5. Does the "maximal IFT-continuation" bypass avoid 4c?

The scope and the task ask whether continuing the local graph (maximal interval of IFT-extension)
+ compactness lets one get the injective arc *without* the general path→arc theorem of 4c. I assess
this route concretely.

**The route.** Start at `P` (assume nonsingular), take the IFT graph over `x`; extend `x` as far
as `∂₁h ≠ 0`. At a **turning point** (`∂₁h = 0` but `∂₀h ≠ 0`, e.g. `(±1,0)` on the circle) the
graph-over-`x` chart breaks (vertical tangent) and one must switch to a graph-over-`y` chart. Keep
switching; track a global parameter (arclength, or the curve's intrinsic coordinate) to maintain
injectivity; stop at `Q`.

**Why this is itself from-scratch and not obviously lighter than 4c.**

1. **Maximal-extension scaffolding is absent.** There is no mathlib "maximal interval on which the
   IFT solution extends" object, and no Zorn/connectedness packaging for "the set of points
   reachable by chart-continuation is clopen in the component". One would prove: *the set of points
   of the component reachable from `P` by a chain of overlapping IFT charts is open* (each chart is
   open) *and closed* (limit of reachable points is in a chart, hence reachable), *hence all of the
   connected component* (connectedness). This is a legitimate argument — and it is **exactly a
   hand-rolled proof that the component is path-connected via charts**, i.e. it reconstructs 4a from
   scratch. It does not avoid 4a; it *is* 4a.
2. **Injectivity of the glued map is the same problem as 4c.** Concatenating chart maps gives a
   *path*; the chain can revisit a point (the component could be a loop, or two chart pieces could
   geometrically overlap away from their parameter overlap). To force global injectivity one needs a
   *strictly monotone global parameter* (arclength along the curve, or the cyclic angle). mathlib
   has **no arclength parametrization of a general algebraic curve** and **no intrinsic coordinate**
   for it; one would have to *construct* a strictly monotone parameter and prove the glued map
   strictly monotone in it. Constructing such a parameter and proving strict monotonicity across
   chart switches (graph-over-x ↔ graph-over-y, where the monotone coordinate changes from `x` to
   `y`) is the analytic core of a 1-manifold-parametrization theorem. **This is not lighter than
   4c; it is a different presentation of the same missing structure theorem.**
3. **Turning-point gluing is real work.** At a turning point the two charts share an arc but
   parametrize it by *different* coordinates (`x` vs `y`), one of which is non-monotone there. The
   transition map is a homeomorphism of intervals but reverses/turns orientation; proving the glued
   map stays injective requires the local monotonicity analysis. No mathlib lemma packages
   "glue two graph charts at a turning point into one injective arc."

**Verdict on the bypass.** It does **not** avoid the obstruction. It replaces "Moore arc theorem"
(4c) with "construct a strictly-monotone global parameter and run a clopen maximal-continuation
argument", which is the same 1-manifold-structure content re-expressed. Either way the deliverable
is a *from-scratch real-algebraic / curve-topology development*. The bypass is arguably *more*
in-character with the in-repo IFT seeds (it reuses §3 directly) but it is not shorter and it still
has no mathlib scaffolding for the global parameter or the maximal-continuation clopen argument.

---

## 6. The weakest ordering B3/B4 actually need

The task asks for the weakest "consecutive on a branch" sufficient for the multigraph edge-count
(B3) and crossing-count (B4) steps, and whether *that* is constructible. Reading the in-repo line
template these port from (`SzemerediTrotter.lean`: `edgesOnLine`/`length_edgesOnLine`,
`incidences_le_numEdges_add`, `stMultigraph_wellDrawn`):

* **B3 needs**, per curve `γ`, a list/enumeration of `P ∩ γ` and, for each *consecutive* pair, one
  arc — to get `numEdges = Σ_γ (|P ∩ γ| − 1)_+ ≥ I − |Γ|`. The combinatorial identity needs only
  that the consecutive pairing yields `(k−1)` edges from `k` points, i.e. a *linear order on `P ∩ γ`*
  (or a per-component linear order, summed). It does **not** need a global geometric order on all of
  `ℝ²`; the line template uses a linear order (`lineKey`) but only its order structure is used in
  the count.
* **B4 needs** (a) multiplicity ≤ M — purely from the 2-DOF point–point clause, independent of the
  ordering; and (b) crossings ≤ M·|Γ|² — each arc-interior crossing sits at a point of `γ ∩ γ′`,
  bounded by the 2-DOF curve–curve clause. (b) needs `interiorOfArc(arc) ⊆ γ`, i.e. the arc's
  carrier (minus endpoints) lies in `γ`. It does **not** need the order to be geometrically
  meaningful — only that the arcs are sub-arcs of the respective curves.

**Therefore the weakest sufficient object is:** *for each curve `γ`, a linear order on the finite
set `P ∩ γ` such that every consecutive pair `(p,q)` is joined by a `SimpleCurveArc` with
`carrier ⊆ γ` and interior ⊆ `γ` (ideally ⊆ `γ*`).* The order may be **any** order for which such
consecutive arcs exist — it need not be the curve's intrinsic order, and points on different
components need not be comparable (a per-component order, concatenated arbitrarily across
components, suffices for the *count*; cross-component "consecutive" pairs simply get no edge, which
only *lowers* `numEdges`, and B3 needs `numEdges ≥ I − |Γ|`, so we must be careful: dropping
cross-component pairs is fine **only if** within each component every consecutive pair still gets an
arc, because the per-component contribution is `(k_c − 1)` and `Σ_c (k_c − 1) = |P∩γ| − (#components
hit)`; with ≤ (2d)² components per curve this loses at most `(2d)²` edges per curve, foldable into
the constant — this matches the scope's "per-component ordering" remark).

**Is the weakest object constructible?** The *order* part is cheap (`Finset` admits a linear order;
even an arbitrary one works for the count). **The binding constraint is unchanged:** producing the
**arc** for each consecutive pair is exactly §4 — an injective continuous map into `γ` between two
prescribed points of the same component. The weakening **removes the need for a geometrically
canonical / intrinsic order** (this *is* a genuine simplification — we do not need to prove the
order is "the" curve order), but it **does not remove the arc-existence obligation**, which is the
ABSENT 4a+4c (and 4d at singular endpoints). So:

> The order can be made trivial; the arc cannot. B3/B4 still bottom out on the same global
> arc-between-prescribed-points object. **The weakening helps the bookkeeping, not the wall.**

---

## 7. Verdict

**B2's load-bearing object decomposes as:**

| Sub-object | Status | Evidence |
|---|---|---|
| Local arc at a nonsingular point (Prop L) | **PROVEN-tractable now** | in-repo S3 (`Bezout.lean:544,640,645`) + mathlib `isEmbedding_graph` (SumProd:602) + `contDiffAt_implicitFunction` (ImplicitContDiff:90) + interval reparam |
| `LocPathConnectedSpace γ*` (4a) | **From-scratch, bounded; no single mathlib lemma** | mathlib has `ChartedSpace.locPathConnectedSpace` (ChartedSpace:268) but **no** `IsLocalHomeomorph→LocPathConnected`; `IsOpen.locPathConnectedSpace` needs openness, `γ` is closed (search) |
| Path between same-component points (4b) | **PRESENT given 4a** (but only a *path*) | `JoinedIn.somePath`/`connectedComponent_eq_iff_joined` (PathConnected:183, LocPathConnected:112) |
| Path → **injective** arc (4c) | **ABSENT — research-grade** | no Moore/Menger arc theorem, no arc-connectedness, no Jordan, no 1-manifold classification in v4.30 (search) |
| One-sided arc to a **singular** incident endpoint (4d) | **ABSENT — research-grade** | needs real-topological branch decomposition at a curve singularity (Puiseux/Newton); absent in v4.30 (search) |
| Weakest order for B3/B4 (§6) | order trivial; **arc obligation unchanged** | line-template count uses only order structure + `interiorOfArc ⊆ γ` |

**Cross-model corroboration.** An independent deep-reasoning pass (Codex / gpt-5.5, read-only,
given the same in-repo seeds and mathlib-absence list) reached the same verdict on every
load-bearing point: local IFT arc available; global arc not constructible from the seeds; step (b)
`Joined` present and not the obstruction; step (c) path→injective arc the genuine obstruction
(Moore/Menger-style, substantial, unformalized); the maximal-IFT-continuation route does not avoid
it (it *is* the same missing 1-manifold-continuation content); singular endpoints need a
Puiseux/local-branch theorem also absent; bottom line **WALL**, with the only single viable interface
being a *large* theorem ("real plane algebraic curve branch/arc decomposition"). No point of
disagreement.

**Headline.** The B2 object is **NOT constructible in mathlib v4.30 from the stated seeds.** The
*local* arc is in reach (Proposition L, genuinely PROVEN-tractable, and the right first brick). The
*global* arc between two prescribed consecutive points is blocked by two independent absences, each
of which is a real-algebraic-geometry / curve-topology structure result with **no mathlib v4.30
scaffolding**:

* **G-B2-arc (the primary obstruction): "path → injective topological arc" (Moore/Menger arc
  theorem) for `ℝ²`** — equivalently a strictly-monotone global parametrization of a connected real
  algebraic curve branch obtained by maximal IFT-continuation. The maximal-continuation *bypass*
  (§5) does not avoid this; it re-expresses the same missing 1-manifold-structure content. ABSENT
  from mathlib v4.30 (EMPIRICALLY VERIFIED by source search: no arc-connectedness, no 1-manifold
  classification, no Jordan, no real-algebraic-curve parametrization).
* **G-B2-sing (secondary): local real branch decomposition at a singular point of a real plane
  curve** (needed only when an incident point is itself a node/cusp). Puiseux/Newton-grade; ABSENT
  from mathlib v4.30 (EMPIRICALLY VERIFIED by source search).

This matches and sharpens the feasibility scope's classification of B2 as ABSENT — FROM SCRATCH and
the single hardest node across both edges, and it makes the obstruction precise: it is **not**
"order the points" (the order is cheap, §6) and **not** the carrier type (`SimpleCurveArc` is
general enough). It is the **injective global arc inside the curve** — the path→arc upgrade — plus
the singular-endpoint branch problem.

**This is a genuine wall in mathlib v4.30**, in the precise sense that closing it requires new
mathematical development absent from the library (a point-set / curve-topology theorem, or its
1-manifold-parametrization equivalent), not merely assembly of existing primitives. It is not a
wall in the sense of being mathematically false or impossible — the object exists classically; it is
a wall in the sense relevant to the gate: **Edge B cannot be completed in mathlib v4.30 without
either this from-scratch development or an Adam-decided Tier-B interface axiom**, the latter yielding
a *conditional*, not closed, `Theorem23Statement` (hence conditional top-down `Corollary24Statement`).

---

## 8. What next (ranked)

**Overall verdict: WALL** for the full B2 object in mathlib v4.30, with a real **GO** sub-brick
inside it (Proposition L) and a precisely named missing piece (G-B2-arc). Ranked directions:

1. **(GO sub-brick — do this regardless) Formalize Proposition L: the local IFT arc as a
   `SimpleCurveArc`.** Statement: for irreducible `h`, `z ∈ γ` with `∂₁h(z) ≠ 0` (and the `∂₀`
   sibling), a `SimpleCurveArc` with carrier ⊆ `γ` through `z`, by reparametrizing the in-repo
   `g = fun x => mkPoint2 x (ψ x)` (`Bezout.lean:639–657`) restricted to a closed subinterval of the
   ε-ball, with continuity from `Continuous ψ` (extract from `contDiffAt_implicitFunction`,
   ImplicitContDiff:90) and injectivity from `isEmbedding_graph` (SumProd:602) or the first
   coordinate. **All inputs PRESENT.** Confidence: high. This shrinks B2's freedom from "global arc"
   to "stitch local arcs", produces a concrete reusable object (not a wrapper), and is the furthest
   one can get into B2 with existing machinery. It is on the Edge-B critical path as the atom every
   later step consumes.

   *FLAG FOR IMPLEMENTER:* the local arc lemma's `Continuous` field needs `Continuous ψ` on an open
   subinterval, not just `ContinuousAt ψ z.1`. `evalPlane h` is `ContDiff ℝ ⊤` everywhere and the
   invertible-partial condition is open, so `contDiffAt_implicitFunction` holds on an open set around
   `z.1`; extract `ContinuousOn ψ (open interval)` and restrict to a closed subinterval. Verify by
   building the file (do not ask the analysis agent to run `lake build`).

2. **(Decision input, not code) Escalate G-B2-arc to a Tier-B interface decision.** The honest
   options to *complete* Edge B are: (i) develop the path→arc / 1-manifold-parametrization theorem
   from scratch in Lean (research-grade, large), or (ii) axiomatize a minimal B2 interface `Prop`
   ("for an irreducible real plane curve and two same-component points, a `SimpleCurveArc` with
   carrier ⊆ curve joining them, interior in the nonsingular locus") as a Tier-B input, exactly as
   `MilnorThom22Statement` already is. (ii) yields a *conditional* `Theorem23Statement`. This is an
   **Adam decision**; surface it rather than pre-deciding. Recommended framing: B2 is the same *kind*
   of object as Milnor–Thom (a real-algebraic structure theorem absent from mathlib), so the same
   Tier-B treatment is consistent.

3. **(Scoping, if research route is taken) Pin down the minimal topological theorem.** The lightest
   sufficient statement is **not** full 1-manifold classification but: *the nonsingular locus `γ*` of
   an irreducible real plane curve, with the subspace topology, is locally homeomorphic to `ℝ`*
   (gives `ChartedSpace ℝ` ⟹ `LocPathConnectedSpace` via ChartedSpace:268, ⟹ same-component points
   `Joined`), **plus** a Hausdorff path→arc lemma (Moore). Building the `ChartedSpace ℝ` instance on
   `γ*` from the IFT graphs is the bounded part; the Moore arc theorem is the genuinely new
   point-set-topology lemma. Prove the Moore arc theorem as a standalone mathlib-style contribution
   first (it is reusable and the true bottleneck); the curve-specific `ChartedSpace` instance second.

4. **(Lower priority) Singular-endpoint handling (G-B2-sing).** Defer until 1–3 resolve. If the
   incident-point model can guarantee incident points are nonsingular (e.g. by a generic-position or
   degree argument bounding singular points, of which there are ≤ (d+1)^5, folded into the constant
   as exceptional vertices), G-B2-sing may be sidestepped at the cost of a constant. Worth a separate
   scoping pass, but it is *secondary* to G-B2-arc.

**Do not** invest in: alternative orderings of `P ∩ γ` as a route to B2 (the order is not the
obstruction, §6); a carrier-type change (`SimpleCurveArc` is already general, §1).
