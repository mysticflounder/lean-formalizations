# Node A1 — N1 (`dartSectorPoint`) analysis: the `convexSector` membership spec is unsound; corrected spec + SECONDARY verdict

Scope: the PRIMARY task (define `dartSectorPoint` and prove **N1a membership** for the
straight-line drawing, per `docs/crossing-lemma-A1-B1-hsplit-design.md` §9 FLAG) and the
SECONDARY task (verdict on whether maintaining the geometric-realization invariant `hreal`
across one harness step is mechanical transport or a second open node). Every file:line and
lemma name was read against the worktree source. Claims are labelled PROVEN / CONJECTURED /
EMPIRICALLY VERIFIED / HEURISTIC.

The load-bearing finding is in §1 (PRIMARY) and §5 (SECONDARY). **No source file was
modified**; the `DartSectorPoint` module and its dependencies build sorry-free as-is
(confirmed: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.DartSectorPoint`
→ "Build completed successfully (8489 jobs)", only style-linter warnings). I did **not**
ship a `dartSectorPoint` definition because the spec's object (`convexSector a p b`) is
proven below to be the wrong object; shipping it would assert a false membership lemma.

---

## 0. Definitions and notation (self-contained, from source)

All in `CrossingLemma` namespace; `Plane := ℝ × ℝ`. Citations are to
`lean/LeanFormalizations/PachDeZeeuw/…`.

- `SimpleCurveArc` (`CrossingLemma.lean:43`): `param : Icc 0 1 → ℝ×ℝ`, continuous,
  injective. A `DrawnMultigraph` (`:54`) stores `arc : Fin numEdges → SimpleCurveArc` —
  **arbitrary curves in general**.
- `segmentArc p q h` (`SzemerediTrotter.lean:413`): the straight segment, `param t =
  (1−t)•p + t•q`. The ST drawing `stMultigraph` (`:483`) draws **every** edge as a
  `segmentArc` between consecutive sorted collinear points (`allEdges`, `edgesOnLine`,
  `:349`). The A1 producer `hgeo` runs on `G' = G.permuteEdges π` whose arcs are these
  segments.
- `incidentEnds G p` (`CrossingLemma.lean:351`): `Finset (Fin numEdges × Bool)`, the
  oriented ends anchored at `p`.
- `angleAt p q := Complex.arg ⟨q.1−p.1, q.2−p.2⟩` (`:359`), range `(−π, π]`. The repo has
  essentially **no** `angleAt` API beyond the definition and the segment lemma
  `angleAt_segmentArc_param_source` below.
- `IsFirstCrossing G p e r t` (`:366`): `dist(param t, p) = r` **and** `dist(param s,p) <
  r` strictly for all `s` strictly between the start end and `t`. Constrains the arc only
  on the open pre-crossing interval; says **nothing** about the arc running along the
  chord `[p, param t]`.
- `ArcsRotationRegular` (`:389`): per `p∈V`, `rp>0` and `α(e,r)` with (a) `α e r =
  angleAt p (param t)` of a first crossing at `r≤rp`; (b1) `α(·,r)` `InjOn` incidentEnds;
  (b2) the strict `<`-order of `α(·,r)` is constant in `r∈(0,rp]`.
- `vertexRotation G hARR hp` (`:576`) `= rotationOfOrder (LinearOrder.lift' (endAngleKey …)
  hinj)` (`:418`). `rotationOfOrder L` (`:256`) is the **cyclic successor in the linear
  order `L`** (`rotationOfOrder_apply_isoFin`, `:262`: the `i`-th smallest ↦ `(i+1 mod
  n)`-th via `finRotate`). Order key = `α = angleAt = Complex.arg`, so the successor is the
  next-larger-arg incident end, wrapping max→min **at the `±π` branch cut**.
- `convexSector a v b := {z | 0 < τ·sideForm a v z ∧ 0 < τ·sideForm v b z}`, `τ =
  cornerTurn a v b = sideForm a v b` (`PolygonalArc.lean:198`, `:188`). `sideForm a b z =
  (b.1−a.1)(z.2−a.2) − (b.2−a.2)(z.1−a.1)` (signed area / left-of test, `:65`).
  `convex_convexSector` (`:233`): it is `(convex_mul_sideForm_gt a v τ 0).inter
  (convex_mul_sideForm_gt v b τ 0)` — **the intersection of two open half-planes whose
  boundary lines both pass through the apex `v`**, i.e. a convex cone. `IsCorner a v b :=
  τ ≠ 0` (`:191`); `convexSector_nonempty` needs `IsCorner` (`:221`, witness `a+b−v`).
- `arcSet G e := range (G.arc e).param` (closed carrier, **includes the endpoints**, so
  `p ∈ arcSet G e` for an incident `e`); `arcUnion G := ⋃ₑ arcSet G e`
  (`RegionFaceBridge.lean:90,93`); `drawingComplementIn G R₀ := R₀ \ arcUnion G` (`:97`);
  `regionAt G R₀ p := connectedComponentIn (drawingComplementIn G R₀) p` (`:118`).

The spec (design doc §9 FLAG): for `p∈V`, `d∈incidentEnds G p`, `succ :=
vertexRotation(d)`, `a` = first-crossing point of `d` at radius `ε`, `b` = first-crossing
point of `succ` at radius `ε`, produce `ε>0` and `q ∈ convexSector a p b ∩ Metric.ball p ε`
with `q ∉ arcUnion G`.

---

## 1. PRIMARY result — the `convexSector` membership spec is UNSOUND (PROVEN)

> **Proposition 1 (PROVEN).** The N1a statement as drafted —
> `∃ ε>0, ∃ q ∈ convexSector a p b ∩ Metric.ball p ε, q ∉ arcUnion G` with `a,b` the
> first-crossing points of `d` and `vertexRotation(d)` — is **false** for the
> straight-line drawing. It fails in two independent, structurally-forced ways, and **no
> `IsCorner`-type side hypothesis repairs it**.

For the straight drawing, an incident arc to `p` is `segmentArc p w` (or `segmentArc w p`),
and by `angleAt_segmentArc_param_source` (`SzemerediTrotter.lean:561`) and
`dist_segmentArc_param_source` (`:537`) its first crossing of `∂B(p,ε)` is the point
`a = p + (ε/|w−p|)·(w−p)`, lying **on the ray** at the segment direction `α(d) = arg(w−p)`.
So `a = p + ε·û_d`, `b = p + ε·û_succ` with `û_d, û_succ` the unit directions of the two
consecutive incident segments.

### 1.1 Failure mode A — degenerate apex (collinear `a,p,b`): `convexSector = ∅`

**(PROVEN.)** If `û_succ = −û_d` (two incident segments leave `p` in exactly opposite
directions) then `a, p, b` are collinear, `τ = sideForm a p b = 0`, `IsCorner a p b` is
false, and `convexSector a p b = ∅` (it requires `0 < 0·(…)`, impossible — and
`convexSector_nonempty` requires `IsCorner`). The conclusion `q ∈ convexSector a p b` is
**unsatisfiable**.

This case is **structurally forced** in the ST drawing, not a generic-position artifact:

- `edgesOnLine P ℓ` (`SzemerediTrotter.lean:349`) builds the consecutive segments
  `(pts[k], pts[k+1])` of the sorted collinear points `pts = pointsOnLine P ℓ`. An interior
  point `p = pts[k]` (with `0 < k < |pts|−1`) is the shared endpoint of two consecutive
  segments `(pts[k−1], pts[k])` and `(pts[k], pts[k+1])`, which leave `p` in **exactly
  opposite directions along `ℓ`**. If `p` lies on a single line of `L`, these are its only
  two incident ends, so each is the other's `vertexRotation`-successor (only-2-ends ⇒
  mutual cyclic successors). Then for `d` = either end, `a,p,b` are collinear and
  `convexSector a p b = ∅`. **A degree-2 collinear vertex — an interior point of a single
  line — is exactly the ST main case.**
- Single incident end (`|incidentEnds p| = 1`, e.g. a line's extreme point on no other
  line): `Fintype.card = 1`, `finRotate 1 = id`, so `succ = d`, `a = b`, `τ = sideForm a p
  a = 0` (`sideForm_left_endpoint`), `convexSector a p a = ∅`. N1a unsatisfiable.

The generic-rotation / scalar-shear WLOG (`docs/corollary24-generic-rotation-scope.md`)
does **not** remove this: an affine map keeps a degree-2 collinear vertex's two incident
segments on the same image line, hence antipodal. (Confirmed by exact arithmetic:
`/tmp/cs_verify.py`, antipodal `{0°,180°}` gives `τ = 0` exactly; single end gives `τ = 0`.
EMPIRICALLY VERIFIED scope = those exact configs; the structural argument above is PROVEN.)

### 1.2 Failure mode B — wrong wedge when the successor gap exceeds π (membership false even with `IsCorner`)

**(PROVEN, by exact sign arithmetic + the convex-cone structure.)** `convexSector a p b` is
the intersection of two open half-planes through `p` (`convex_convexSector`, `PolygonalArc.lean:233`),
hence a **convex cone**, which subtends exactly the **convex (< π) angular sector** between
the rays `p→a` and `p→b` — blind to which side the cyclic successor sits on. The CCW-open
successor arc from `α(d)` to `α(succ)` is ray-free **by the specification of
`rotationOfOrder`** (no incident end has arg strictly inside it). But:

- when the CCW gap `g = (α(succ)−α(d)) mod 2π` is `< π`, the < π convex sector **equals**
  the successor arc — `convexSector` is correct;
- when `g > π`, the successor arc is the **reflex** side, and `convexSector` selects the
  **complementary < π arc**, which **contains other incident rays**.

Exact verification (`/tmp/cs_verify.py`, `/tmp/cs_iscorner.py`, exact-arithmetic sign tests):
ends `{80°,100°,200°}`, dart `d` at `200°` (arg `−160°`), `succ` at `80°` (the wrap, `g =
240° > π`). Then `τ = sideForm a p b = 0.866 ≠ 0`, so **`IsCorner` HOLDS**, yet
`convexSector(200°,p,80°)` **contains the third incident ray at 100°** (and 90°, 140° — the
< π side through 100°) and **excludes** the successor arc (it does not contain the 0° / −10°
directions). A point of `convexSector a p b ∩ B(p,ε)` therefore lies on the third incident
segment, so `q ∉ arcUnion` is **violated**. Second witness: ends `{−10°,0°,10°}`, pair
`(10°→−10°)`, `g = 340°`, `τ = 0.342 ≠ 0` (`IsCorner` holds), `convexSector` contains the 0°
ray.

The `g > π` case **arises generically**: the CCW gaps of `n≥2` ends sum to `2π`, so at most
one exceeds π; any vertex whose incident directions span a < π cone (a convex-hull vertex of
`P`, or any vertex with all incident lines to "one side") has its complementary gap > π.
EMPIRICALLY ~55% of random 2–6-end configs (27450/50000, `/tmp/wedge_test.py`).

**Consequence (PROVEN): adding `IsCorner a p b` as a hypothesis does NOT make N1a true.**
The membership `q ∉ arcUnion` is false in the `g>π` cases *even though* `IsCorner` holds
there. The only hypothesis that would rescue `convexSector` is "`g < π`", which fails for
ST convex-hull-type vertices. So `convexSector` is the wrong object, full stop — it cannot
be salvaged by a side condition that the straight drawing satisfies.

### 1.3 Independent reason the general-`DrawnMultigraph` statement is false (curved arcs)

**(PROVEN.)** At the general `DrawnMultigraph` level (arbitrary `SimpleCurveArc`),
`convexSector a p b` is the wedge between **straight** rays `p→a`, `p→b`, but
`IsFirstCrossing` (`:366`) constrains a curved arc only on the open pre-crossing interval.
A curved arc can reach `∂B(p,ε)` at `a` while bulging through `convexSector a p b` between
`p` and `a`, so `q ∈ convexSector ∩ B(p,ε)` can lie on that arc. Hence N1a is false at the
`DrawnMultigraph` level the design doc §9 FLAG states it ("for `G` a `DrawnMultigraph`,
`hARR`"). It needs a straightness hypothesis; the design doc's labelling of N1a as
"PROVEN-on-paper; mathlib-constructible" (§8 Node N1a, §10 table) is **incorrect for the
`convexSector` form** and should be downgraded.

---

## 2. The corrected, TRUE, downstream-sufficient statement (N1a′)

The downstream consumer of the sector point is `prefixStepSameRegion`
(`EdmondsSameRegion.lean:186`), whose hypotheses are exactly:

```
(hq₁) drm c₁ = regionAt (prefixEdges m hm) R₀ q₁
(hq₂) drm c₂ = regionAt (prefixEdges m hm) R₀ q₂
(S, hS : IsPreconnected S, hSsub : S ⊆ drawingComplementIn (prefixEdges m hm) R₀,
 q₁ ∈ S, q₂ ∈ S)  ⟹  drm c₁ = drm c₂
```

**It never mentions `convexSector`, `IsCorner`, or any angular predicate** (PROVEN by
signature reading). It needs only (i) the realization `dr m c = regionAt … q` (= N1b, the
separate harder obligation, see §5) and (ii) `q ∈ drawingComplementIn` so that `regionAt … q`
is a genuine face. `convexSector` was merely a *proposed device* to produce a concrete
arc-free `q` at the dart's angular position; any arc-free point in the correct face serves
identically. So `convexSector` can be dropped with **no downstream loss**.

> **N1a′ (corrected sector-point membership — TRUE for the straight drawing; CONJECTURED
> until Lean-checked, PROVEN-on-paper here).** Let `G` be a `DrawnMultigraph` all of whose
> arcs incident to `p` are `segmentArc`s, `hARR : ArcsRotationRegular G`, `hjoin :
> G.ArcsJoinEndpoints`, `p ∈ G.V`, `d ∈ incidentEnds G p`, `succ := vertexRotation G hARR
> hp d`, `α := arrAngle G hARR hp`. Then there exist `ε > 0` (with `ε ≤ arrRadius G hARR
> hp` and `ε ≤ δₚ` of §3.2) and `q : Plane` with:
> 1. `q ∈ Metric.ball p ε`;
> 2. if `2 ≤ (incidentEnds G p).card`: `(angleAt p q − α d ε) mod 2π ∈ (0, (α succ ε − α d
>    ε) mod 2π)` — strictly inside the **CCW-open successor arc**; if `(incidentEnds G
>    p).card = 1`: no angular constraint;
> 3. `q ∉ arcUnion G` (equivalently `q ∈ drawingComplementIn G Set.univ`).

The object is the **`angleAt`-interval wedge** `{z ∈ ball p ε | (angleAt p z − α d) mod 2π
∈ (0, (α succ − α d) mod 2π)} \ arcUnion G`, **not** `convexSector a p b`. It is satisfiable
in **all** cases (no `IsCorner` demand), including the failure modes of §1.

### 2.1 Why N1a′ is true (PROVEN-on-paper for the straight drawing)

- **Incident arcs lie on the rays at `α(e)`** (PROVEN from source): §1 opening, via
  `angleAt_segmentArc_param_source` (`:561`). Each incident segment is contained in the
  closed ray `{p + s·(w−p) | s ≥ 0}` at arg `α(e)`; the open angular wedge between two
  *distinct* args contains none of these rays except possibly at the apex `p`.
- **The successor arc is ray-free** (PROVEN): `rotationOfOrder_apply_isoFin` (`:262`) makes
  `succ` the next-larger-arg end, so no incident end has arg strictly inside `(α(d),
  α(succ))` CCW. ARR (b1) injectivity (`:396`) makes the arc nondegenerate (`α(d) ≠
  α(succ)` when `card ≥ 2`). EMPIRICALLY VERIFIED 0 failures / 200000 (`/tmp/wedge_test.py`).
- **Non-incident arcs are bounded away from `p`** (PROVEN-on-paper, see §3.2): δₚ > 0, so
  `B(p,δₚ) ∩ arcUnion = B(p,δₚ) ∩ (⋃_{e incident} arcSet e)`.
- Hence inside `B(p, min(ε,δₚ))` the only arcs are the incident segments on the rays, the
  open successor wedge misses all of them, and a point of the wedge off the apex satisfies
  `q ∉ arcUnion`.

### 2.2 The right object case-by-case

- `card = 1`: `q ∈ ball p ε \ arcUnion G` (whole punctured ball; no wedge).
- `card = 2`, non-antipodal: the CCW-successor open angular wedge (width `<π` or `>π` —
  both fine, since it is defined by `angleAt`, not `sideForm`).
- `card = 2`, antipodal (degree-2 collinear vertex — the case `convexSector` most clearly
  breaks): the open **half-plane** bounded by the line of the two segments, on the
  successor side. `convexSector` is empty here; the half-plane is correct.
- `card ≥ 3`: the CCW-successor open angular wedge ∩ ball, **regardless of whether its
  width exceeds π**.

Cleanest Lean route (avoids the bulk of branch-cut bookkeeping): rotate coordinates so
`α(d)` becomes the positive real axis (multiply `z−p` by `exp(−i·α(d))`), reducing the
wedge to `{0 < arg < g}`, an honest open `arg`-interval, `g ∈ (0,2π)`.

---

## 3. The genuinely-needed Lean lemmas for N1a′ (ranked), and the missing API

### 3.1 Foundational structural lemma (medium; no analysis) — `p ∉ arcSet G e` for non-incident `e`

**(PROVEN-on-paper.)** For the ST drawing, a vertex `p ∈ V` lies on a carrier `arcSet G e`
**only** when `e` is incident to `p`. Proof: `arcSet G e = [s,t]` with `(s,t) =
(pts[k],pts[k+1])` consecutive in the strictly `lineKey`-sorted `pts = pointsOnLine P ℓ`
(`mem_pointsOnLine`, `:332`; strict sort `:1326`). If `p ∈ {s,t}`, `p` is an endpoint ⇒ `e`
incident (`endAnchor_segmentArc_false/true`, `:498,:502`). If `p` strictly between `s,t` on
`ℓ`, then `p ∈ P ∩ ℓ` ⇒ `p ∈ pts` with `lineKey` strictly between `lineKey s` and `lineKey
t`, contradicting consecutiveness in the strict sort. So no "p in the interior of a
non-incident collinear segment" survives — no general-position assumption needed.
*FLAG:* verify the prefix `prefixEdges m` preserves per-line consecutiveness of retained
edges' endpoints; the argument uses only the edge-intrinsic fact that `s_e,t_e` are
consecutive in the full line sort, which a list-prefix keeps (each edge carries its own
`(pts[k],pts[k+1])` identity). CONFIRMED on reading; not machine-checked.

### 3.2 δ-separation (medium) — `δₚ := min_{e non-incident} infDist p (arcSet G e) > 0`

**(PROVEN-on-paper.)** Each `arcSet G e` is compact (`isCompact_univ.image (arc e).cont`,
the argument reused in `exists_point_in_complement`, `DartSectorPoint.lean:111–117`) hence
closed; `p ∉ arcSet G e` (§3.1) + compact ⇒ `infDist p (arcSet G e) > 0`. Finitely many
edges ⇒ the min of finitely many positives is positive. The one non-repo ingredient is the
standard mathlib `Metric.infDist_pos_iff_notMem_closure` / `IsCompact.exists_infDist_eq_dist
+ dist_pos` — **available in mathlib v4.30, no Jordan content**. *FLAG:* pin the exact
mathlib lemma during Lean.

### 3.3 N1a′ membership at the successor angle (hardest; the irreducible geometric content)

**(PROVEN-on-paper, §2.1.)** Construct `q` at a prescribed `angleAt` inside the open
successor `arg`-interval and inside `ball p ε`, off the incident rays. The work is the
coordinate-rotation reduction to `{0 < arg < g}` and producing a point with given arg. The
**missing API** is `angleAt`/`Complex.arg`-interval openness and membership: the repo has
**no** `angleAt` lemmas beyond the definition and `angleAt_segmentArc_param_source`. Mathlib
v4.30 has `Complex.arg`, `Complex.continuousAt_arg` (away from the cut), `Complex.arg_mul`,
`Complex.arg_real_mul` — enough to build the wedge after rotating the cut away. **No
mathlib-absent infrastructure (no Jordan/Schoenflies/germ).** Estimate: the bulk of one
session, dominated by §3.1 and this construction.

### 3.4 Assembly (easy; existing) — `prefixStepSameRegion`, `nonempty_prefixStepCrosscut_of_data`

Sorry-free combinators (`:186`, `:380`), unchanged by switching `convexSector → angular
wedge`. They consume the realization (§5) and `q ∈ S ⊆ complement`, not `convexSector`.

**Verdict on PRIMARY: N1a as drafted is unsound and must not be shipped; N1a′ (angular
wedge) is the correct sublemma and is PROVEN-on-paper, mathlib-constructible, but is NOT a
one-liner — it needs §3.1–§3.3.** I did not ship a `dartSectorPoint`/N1a Lean definition,
because the only definition matching the spec asserts a false membership lemma (§1), and the
correct replacement (§2) is a multi-lemma development whose exact shape is coupled to N1b
(§5). Building it speculatively, ahead of the N1b decision, risks the wrapper-network
failure mode the project rules forbid.

---

## 4. The design doc FLAG axiom certifications (status)

The design doc §9 asks to certify the straight-arc PL path is sorry-free via `#print axioms`.
I could **not run** these in the worktree: the lean-usage cache-guard hook rejects the
worktree's symlinked `.lake/packages/mathlib` path (false negative — `find` confirms the
oleans are present and the `DartSectorPoint` target replayed 8489 jobs successfully), and
writing an axiom-check module into the **parent** checkout would violate worktree write
isolation. The values below are therefore reported from the prior verified build recorded in
the task prompt and memory `38R2S1`/`G2GJCE`, **CONJECTURED** at the level of "not freshly
re-run here", PROVEN at the level of "documented clean by the cited prior runs":

```
-- documented (task prompt: "I just verified both are axiom-clean"):
exists_twoSidedPartition_prefixStep         : [propext, Classical.choice, Quot.sound]
exists_twoSidedPartition_of_straightArc     : [propext, Classical.choice, Quot.sound]
-- documented (task prompt: harness "sorry-free and axiom-clean"):
exists_dr_hstepCrosscut                     : [propext, Classical.choice, Quot.sound]
prefixStepSameRegion                        : [propext, Classical.choice, Quot.sound]
-- I read this one's full proof; it is sorry-free, Classical-only:
exists_point_in_complement                  : [propext, Classical.choice, Quot.sound]  (expected)
```

To obtain a fresh certification, run from the parent checkout (read-only on built oleans),
or fetch the worktree cache (`LEAN_USAGE_SKIP_CACHE_CHECK=1` does not bypass the hook;
either fix the guard's symlink-path test or run `lake exe cache get` in the worktree). No
source change of mine affects any of these closures.

---

## 5. SECONDARY — verdict on the `hreal` step-maintenance identity

> **Question (task SECONDARY):** is maintaining `hreal k : ∀ d, dr k d = regionAt
> (prefixEdges k) R₀ (dartSectorPoint d)` across one harness step — i.e. proving
> `stepPoolRegion (splitClass d) = regionAt (prefixEdges (m+1)) R₀ (dartSectorPoint d)` —
> genuinely mechanical transport given N1a, or a SECOND open node (the full Edmonds
> bridge)?

### 5.1 Verdict: **SECOND OPEN NODE — NOT mechanical transport. (PROVEN, by source reading.)**

The design doc §9's "mechanical once N1a is proven" is **HEURISTIC and incorrect**. The
step-maintenance identity is the **Edmonds combinatorial-face ↔ geometric-region
correspondence at the inductive step**, of strictly greater content than N1a/N1a′. Two
PROVEN sub-findings establish this.

**(a) The base case alone refutes "mechanical add-on" (PROVEN).** The harness
`exists_dr_hstepCrosscut` (`EdmondsSameRegion.lean:496`) sets the base region family to
`dr := fun _ _ => ∅` (`:541`) and carries **only** `hconst`/`hsep` (`:521–531`); there is no
geometric realization in the carried `Σ'`. Adding `hreal start` requires proving `∅ =
regionAt (prefixEdges start) R₀ (dartSectorPoint d)`, which is **false** (`regionAt` of a
complement point is a nonempty component, `connectedComponentIn … q` with `q` in the set).
So the `∅` base must be **replaced** by a genuine `regionAt` assignment — a non-mechanical
change to the otherwise-frozen sorry-free harness, exactly as the §9 FLAG admits, but it is
not "mechanical": the base prefix is `prefixEdges start` (a tree, single face per
`hcard1`), and one must (i) pick a complement point, (ii) prove `dartSectorPoint d` lands in
that one face for **every** dart `d`, which is itself a single-face instance of the
realization problem.

**(b) The step identity is the cross-level Edmonds equality (PROVEN that it is required, by
unfolding the definitions).** `dr (m+1) = stepRegionFamily = stepPoolRegion ∘ splitClass`
(`stepRegionFamily`, `:314`; `stepPoolRegion`, `:117`), where `splitClass d =
insertedFaceSplitPoolEquiv (Face_mk (symm d))`. Maintaining `hreal (m+1)` means proving, for
each split-pool class, `stepPoolRegion(…)(splitClass d) = regionAt (prefixEdges (m+1)) R₀
(dartSectorPoint (m+1) d)`. Unfolding `stepPoolRegion` (`:127`) splits into:

- **Old non-cut face `Sum.inl f`** (`insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle`,
  the `¬SameCycle x c₁` darts): `stepPoolRegion(inl f) = oldFaceRegion drm f = drm (some
  dart d') = regionAt (prefixEdges m) R₀ (dartSectorPoint m d')` (the last step is `hreal
  m`). So the obligation becomes
  ```
  regionAt (prefixEdges m)   R₀ (dartSectorPoint m   d')
    = regionAt (prefixEdges (m+1)) R₀ (dartSectorPoint (m+1) d).
  ```
  This is a **cross-level region equality**: the same face, named at level `m` and again at
  level `m+1` after inserting the new arc. Adding an arc removes its carrier from the
  complement, so `regionAt (prefixEdges m) R₀ q` and `regionAt (prefixEdges (m+1)) R₀ q`
  **differ in general** (the new arc can cut a component). For a non-cut face the component
  is unchanged as a point-set **iff the new arc does not touch it** — true geometrically
  (the new edge is the single crosscut of the *one* cut face, disjoint from every other
  face) but it is a **genuine geometric lemma**: "inserting the cotree arc leaves every
  non-cut complement component invariant, and the two sector points name that same
  component across the level change." This is precisely the `face_constant` half of
  `EdmondsCompatible` (`RegionFaceBridge.lean:174`) promoted to a *cross-level region
  identity*, plus a consistency between `dartSectorPoint m` and `dartSectorPoint (m+1)`.
- **New sides `Sum.inr 0/1`** (`insertedFaceSplitPoolEquiv_mk_inl_left/right`,
  `EdgeInsertion`): `stepPoolRegion(inr 0/1) = Wleft/Wright`. Maintaining `hreal` here
  requires `Wleft = regionAt (prefixEdges (m+1)) R₀ (dartSectorPoint (m+1) d)` for the darts
  `d` on that side — i.e. the global successor side `Wleft` (from N3 /
  `exists_twoSidedPartition_prefixStep`) **equals** the component named by the new dart's
  sector point. This is the `region_separates` direction (the hard Edmonds half) as an
  *equality of named regions*, exactly the §5.2-of-the-design-doc local→global propagation,
  now tied to `dartSectorPoint`.

Neither branch is a `rw`/`simp` transport. Both are the geometric Edmonds correspondence —
the very content `EdmondsCompatible` (`RegionFaceBridge.lean:166`) packages and that the
design doc §2 route-(2) calls "must be built." The bridge `facePerm_sameCycle_of_sameRegion`
(`:273`) is the `region_separates` clause and is **not unconditional**; it must be
constructed. So `hreal`-maintenance is **a second open node of the same character as the
full Edmonds bridge**, not mechanical.

### 5.2 What `hreal` shares with N1a, and what it does not

`hreal`-maintenance **consumes** N1a′ (it needs the sector point and its complement
membership to even state the RHS) but is **strictly larger**: it additionally needs
(i) cross-level region-invariance of non-cut faces under arc insertion, (ii) the
local→global identification of `Wleft/Wright` with sector-point components, and (iii) a base
case replacing `∅`. (i)–(iii) are the geometric Edmonds correspondence, absent from the repo
(only `EdmondsCompatible` as a *consumed predicate* and the sorry-free *combinatorial*
transport exist). This matches the design doc §5.2/§7 finding that B1 (co-faciality) and
`hWne` (distinctness) "share only `dartSectorPoint`": likewise `hreal` shares `dartSectorPoint`
with N1a but is its own obligation.

### 5.3 Caveat on the route

The design doc §4 already shows `hgeo` does **not** need the deeper `:5785` extractor
`hsplit` (it needs `hregion` + `hWne/hWold` at level `m`, via the
`_of_old_endpoint_incident` lemma `:4326`). That reduction stands and is the right route.
But note: `hregion` via `prefixStepSameRegion` needs the **realization** `dr m c = regionAt
… q` (its `hq₁/hq₂`), which is `hreal m` *restricted to the two entered corners*. So even on
the §4 route, the realization invariant (or at least its instance at the entered corners,
maintained across steps) is unavoidable — confirming `hreal` is on the critical path and is
a genuine second node, not a bookkeeping convenience. The honest statement: **A1 has TWO
open geometric nodes — N1a′ (the arc-free sector point) and the realization/Edmonds-bridge
node (carrying `hreal`, or its entered-corner instance, across the harness with a non-`∅`
base) — and the second is the larger.**

---

## 6. What next (ranked)

1. **Re-spec N1a → N1a′ in `docs/crossing-lemma-A1-B1-hsplit-design.md` (§8 Node N1a, §9
   FLAG).** Replace the target set `convexSector a p b ∩ Metric.ball p ε` with the
   `angleAt`-interval wedge `{z ∈ ball p ε | (angleAt p z − α d) mod 2π ∈ (0, (α succ − α d)
   mod 2π)} \ arcUnion G` (whole punctured ball when `card = 1`). Downgrade the §8/§10
   "PROVEN-on-paper, mathlib-constructible" label on the `convexSector` form to REFUTED, and
   re-attach PROVEN-on-paper to N1a′. This is the load-bearing correction; the drafted
   object is provably wrong on a positive fraction of ST vertices (§1).
2. **Prove §3.1 (`p ∉ non-incident arcSet`) as a standalone Lean lemma** — pure
   `pointsOnLine`/`edgesOnLine` consecutive-sort combinatorics, no analysis, reuses
   `pointsOnLine_nodup` + strict sortedness (`:1326`). Smallest correct first step; useful
   to **any** version of N1a and to δ-separation.
3. **Prove §3.2 (δ-separation) via mathlib `infDist_pos`.** Self-contained given (2).
4. **Build the `angleAt`-interval wedge API + N1a′ membership (§3.3)** with the
   coordinate-rotation-to-`{0<arg<g}` trick. The irreducible geometric residual; needs new
   `Complex.arg`-interval lemmas (constructible from mathlib v4.30 `arg` API, no Jordan).
5. **Then the realization / `hreal` node (§5)** — the larger second open node: replace the
   `∅` base, prove cross-level non-cut-face region-invariance under arc insertion, and
   identify `Wleft/Wright` with sector-point components. Only after this do `hregion` and
   the §4 assembly (`nonempty_prefixStepCrosscut_of_data`, `:380`) close `hgeo` /
   `SzemerediTrotter.lean:4649`.
6. **`convexSector` stays valid for the PL collar layer** (`PolygonalArc.lean`, `PLCollarSeparation`)
   where it is used with a genuine non-degenerate `IsCorner` polyarc vertex and the < π
   convex cone is the intended object. The unsoundness is specifically in repurposing
   `convexSector` as the *dart-face wedge keyed by the cyclic successor*; do not touch its
   collar uses.

---

## 7. Structural assumptions used (stated explicitly)

- **Finiteness**: `Fin G.numEdges` ⇒ finitely many arcs ⇒ δₚ is a min of finitely many
  positives (§3.2). Essential.
- **Compactness**: each `arcSet G e` compact/closed ⇒ `infDist p (arcSet) > 0` when `p ∉
  arcSet` (§3.2). Essential.
- **Straightness**: all incident arcs `segmentArc` ⇒ first crossing on the ray, incident
  arcs on the rays (§1, §2.1). Essential; N1a is FALSE for general curved arcs (§1.3).
- **ARR (b1) injectivity**: distinct ends ⇒ distinct args ⇒ nondegenerate successor arc.
  Essential.
- **Consecutive-sorted-points structure** of `pointsOnLine`/`edgesOnLine`: gives `p ∉
  interior of non-incident same-line segment` (§3.1), replacing any general-position
  assumption. Essential.
- **Not used**: any Jordan curve / Schoenflies / germ statement; any generic-position
  shear (it does not remove the antipodal degree-2 obstruction, §1.1).

---

## 8. Summary table (evidence levels)

| Claim | Level | Basis |
|---|---|---|
| N1a as drafted (`convexSector a p b ∩ ball`) is FALSE for the straight drawing | **PROVEN** | §1; convex-cone structure (`convex_convexSector`, `:233`) + exact sign arithmetic |
| Failure A: degree-2 collinear / single-end vertex ⇒ `convexSector = ∅` (unsatisfiable) | **PROVEN** | `edgesOnLine` consecutive segments (`:349`); `IsCorner` needed for nonempty (`:221`) |
| Failure B: successor gap > π ⇒ `convexSector` is wrong wedge, contains other incident rays | **PROVEN** | exact arithmetic `/tmp/cs_iscorner.py`: `τ≠0` yet third ray ∈ convexSector |
| `IsCorner` hypothesis does NOT rescue `convexSector` | **PROVEN** | Failure B has `IsCorner` true and membership still false |
| failure-B cases (gap > π) arise generically (convex-hull-type vertices) | **EMPIRICALLY VERIFIED** | 27450/50000 random configs; structural argument PROVEN it can occur |
| `prefixStepSameRegion` needs no `convexSector` (only realization + complement membership) | **PROVEN** | signature `:186` |
| Corrected N1a′ (angular-wedge) is TRUE and downstream-sufficient | **PROVEN-on-paper** (CONJECTURED until Lean) | §2; `rotationOfOrder` successor spec + straight-ray + δ-separation |
| N1a′ needs no mathlib-v4.30-absent infra (no Jordan); `angleAt` API is thin but constructible | **CONJECTURED** | mathlib `Complex.arg` API present; `angleAt` lemmas absent (only `:561`) |
| `hreal` step-maintenance is a SECOND open node (Edmonds bridge), not mechanical | **PROVEN** | §5; `∅` base refutes add-on; `stepPoolRegion∘splitClass` = cross-level Edmonds equality |
| `hreal` shares only `dartSectorPoint` with N1a; is strictly larger | **PROVEN** | §5.2; needs cross-level region-invariance + local→global side identification + non-`∅` base |
| straight-arc PL path (`exists_twoSidedPartition_*`) sorry-free, Classical-only | **CONJECTURED** (not freshly re-run here) | task prompt + memory `38R2S1`/`G2GJCE`; worktree cache-guard blocked a fresh `#print axioms` |
| `DartSectorPoint` module + deps build sorry-free as-is | **PROVEN** | `./lake-build.sh …DartSectorPoint` → success, 8489 jobs, style-linter warnings only |
