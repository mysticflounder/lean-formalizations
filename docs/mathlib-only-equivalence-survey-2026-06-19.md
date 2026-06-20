# Survey: mathlib-only equivalence lemmas for the excluded headline surface

**Date:** 2026-06-19
**Question that prompted it:** the comparator gate only covers the 19 headlines
whose *statement* is expressible in pure mathlib vocabulary. For every other
headline — the ones whose statement names a project-defined symbol — can we write
a **mathlib-only equivalence/characterization** that brings the statement inside
the comparator-audited surface, or is the underlying object genuinely absent from
mathlib (so only upstreaming would help)?

## Method

For each project symbol an excluded headline quantifies over, read the **verbatim
definition body** and classify by what the body is made of, not by how advanced
the mathematics is:

- **EQUIV** — a `def`/`abbrev`/`Prop`-def whose body is an expression over only
  mathlib primitives (after inlining other transparent project defs). Admits a
  lemma `projectDef = ⟨mathlib expression⟩`, true by `rfl` or a short tactic
  proof. The headline can then be stated mathlib-only by inlining that expression
  into `Challenge.lean`, with the equivalence as the bridge in `Solution.lean`.
- **UNBUNDLE** — a `structure` all of whose fields are mathlib-typed. No
  `= mathlib` lemma exists (it carries data), but a headline quantifying over it
  restates mathlib-only by replacing the structure argument with its fields as
  explicit hypotheses.
- **NEW** — a `structure`/`inductive` introducing a genuinely new mathematical
  object with no mathlib counterpart. No mathlib-only restatement; only
  upstreaming the object (or substituting a mathlib notion) would bring the
  headline into the gate.

The classification calls below are mine; the definition bodies were gathered by
parallel readers and spot-checked against source (`CombinatorialMap.Basic.lean`,
`PachDeZeeuw/AlgebraicPrelim.lean`).

## Verdict by bucket

| Bucket | Symbols | Verdict | Bridge effort |
|---|---|---|---|
| **NearEnemy** | `perpBisector`, `bisectorEnergy`, `rotationEnergy` | EQUIV | `rfl` |
| **Elekes–Sharir geometric core** | `P2`, `Vec2`, `J`, `esLine`, `dist2`, `det2`, `twoPinnedDet`, `Intersect`, `Parallel`, `IsDist2Preserving`, `PairwiseSkewRuling` | EQUIV | `rfl` / short |
| **GL₂ helper** | `Matrix.GeneralLinearGroup.GL2.unipotent` | EQUIV (already mathlib-typed) | short |
| **ESGK base layer** | `Config`, `OrderedMultiplicity`, `OrderedDistanceValues`, `NumDistancesOrdered`, `NumDistances`, `DistanceEnergy`, `EnergyAtLevel`, `Richness`, `IsDirect`, `distinctDistances`, `NonTrilinear`, `InGeneralPosition`, `hIndexed` | EQUIV | `rfl` / short |
| **Pach–de Zeeuw / Bézout** | `XCoeff`, `XFrac`, `Curry0`, `coeffEval`, `Specialized0`, `CoeffRootSet`, `CoeffLineZeroSet`, `PlaneCurveZeroSet`, `FiberCommonZeros`, `IsBoundedDegreeCurve`, `NoCommonCurveComponent`, `BezoutFiniteIntersectionStatement` | EQUIV | `rfl` / short |
| **Unit-distance elimination** | `unitNeighborFinset`, `unitForwardNeighborFinset`, `unitDirectedPairFinset`, `unitPairIndexFinset`, `UnitDistanceEliminationOrder` | EQUIV | `rfl` / short |
| **Simple convex polygon** | `IsCyclicInterval` (EQUIV), `SimpleConvexPolygon` (UNBUNDLE) | UNBUNDLE | unbundle 4 fields |
| **Convex line-slice** | `lineHomeomorph`, `convex_line_slice_ordConnected` | EQUIV but **verbose** | inline a constructed homeomorphism |
| **Combinatorial maps / planar edge bound** | `CombinatorialMap`, `IsSimple`/`Connected`/`IsPlanar` on it, `HasGenusZeroSimplePlanarization`, `AbstractPlanarizedMultigraph` (UNBUNDLE), `planar_multigraph_edge_bound` | **NEW** | not restate-able; needs upstreaming |

## Why the verdicts

**Why almost everything is EQUIV.** These "project-specific" defs are
overwhelmingly transparent abbreviations over mathlib. Representative bodies:

- `perpBisector p q := {x | dist x p = dist x q}` — the literal perpendicular
  bisector; `bisectorEnergy P` is a `Finset.filter (…) |>.card` over `(P×P)×(P×P)`.
- `dist2 p q := (p.1-q.1)^2 + (p.2-q.2)^2`, `det2 u v := u.1*v.2 - u.2*v.1`,
  `P2 := ℝ × ℝ` — pure arithmetic on mathlib pairs.
- `PlaneCurveZeroSet p := {x | MvPolynomial.eval (fun i => x i) p = 0}`,
  `Curry0 p := MvPolynomial.finSuccEquiv ℝ 1 p` — the entire Bézout layer is
  mathlib `MvPolynomial`/`Polynomial` zero-set machinery. The *concept* (Bézout
  for real plane curves) is advanced; the *statement* is mathlib-expressible.
- `OrderedMultiplicity p r := (univ.product univ |>.filter (i≠j ∧ dist (p i)(p j)=r)).card`,
  `DistanceEnergy p := ∑ r, (OrderedMultiplicity p r)^2` — the ESGK energy/distance
  counters are `Finset` sums/cards over `dist`.
- `unitForwardNeighborFinset p i := (univ.filter fun j => dist (p i)(p j)=1).filter (i<j)` —
  unit-distance bookkeeping is filtered `Finset.univ`.

For all of these the bridge lemma is `rfl` or a short `unfold`+`simp`. The headline
goes into `Challenge.lean` with the symbol inlined to its mathlib expression
(verbose, but *more* auditable — the reviewer sees the exact predicate), and
`Solution.lean` discharges it via the project theorem plus the equivalence.

**Why two are UNBUNDLE.** `SimpleConvexPolygon` and `AbstractPlanarizedMultigraph`
are `structure`s whose fields are all mathlib-typed (`List V` + `Nodup` + frontier
/`convexHull` conditions; `Vertex`/`Edge : Type` + `Fintype` + `edgeVerts : Edge →
Sym2 Vertex`). No `= mathlib` lemma, but a headline `(P : SimpleConvexPolygon V) → …`
restates as `(vertices : List V) (hnodup …) (hfrontier …) → …` — pure mathlib
hypotheses. `IsCyclicInterval` (the conclusion of the polygon headline) is itself a
transparent `List.rotate`/`take` predicate, so that whole headline is restate-able.

**Why one is verbose-but-possible.** `lineHomeomorph` is a *constructed*
homeomorphism `ℝ ≃ₜ line[ℝ,A,C]` (composition of `ContinuousLinearEquiv.toSpanNonzeroSingleton`
and `AffineEquiv.vaddConst`). Its headline `convex_line_slice_ordConnected` names
the homeomorphism in a preimage. A mathlib-only restatement must inline the whole
construction — doable, but the statement gets unwieldy; lower priority than the
clean EQUIV cases.

**Why one is genuinely NEW.** `CombinatorialMap D` is a rotation system: three
`Equiv.Perm D` (vertex/edge/face) with `face * edge * vertex = 1`, `edge`
involutive and fixed-point-free. Mathlib has no combinatorial-map / rotation-system
/ genus-zero-planarity theory, so `IsPlanar`, `HasGenusZeroSimplePlanarization`,
and `planar_multigraph_edge_bound` cannot be phrased in mathlib alone. This is the
**only** bucket where the exclusion reflects a real gap in mathlib rather than a
naming/wrapper choice. Bringing it into the gate means upstreaming a planarity
notion (large) or re-proving the edge bound against a mathlib planarity definition
if/when one exists.

## Bottom line

Of the nine excluded buckets, **seven are cleanly restate-able into the
comparator gate** (six EQUIV, one UNBUNDLE), **one is restate-able but verbose**
(line-slice), and **one is genuinely outside mathlib** (combinatorial-map
planarity). My earlier informal guess that the Bézout and convex-polygon layers
were "new mathematics" was wrong — the survey shows their *statements* are
mathlib-expressible; only the combinatorial-map layer is not.

This means the "mathlib-only audited surface" can be expanded to cover nearly all
headline results, not just the current 19, with mostly `rfl`/short bridge lemmas.

## Scope caveat

This surveys the **definitions** the excluded headlines name, not a one-by-one
enumeration of every excluded headline theorem. The bucket verdict transfers to a
headline iff that headline names only symbols in its bucket (the common case). A
headline mixing a NEW symbol with EQUIV ones inherits NEW. The precise per-headline
list and the exact `Challenge.lean` statements are the next step if we act on this.
