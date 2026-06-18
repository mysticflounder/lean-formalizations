# Collar work handoff (2026-06-17)

## UPDATE (2026-06-17, end-cap de-vacuification) — READ FIRST

`exists_twoSidedPartition_of_straightArc` was sorry-free but **vacuous** (its
hypothesis bundle proved `False`): the clipped end-cap slice cover was indexed over the
CLOSED foot range `Ioc 0 c_max`, whose boundary slice `c = c_max` is empty, and its
near-source hypothesis `foot ≤ cSrc ≤ 2α` at radius `L` contradicted `hSband`. This was
**fixed** by re-indexing the entire src/tgt × plus/minus cap chain to the OPEN range
`Ioo 0 c_max` (see ROUTE_C_PLAN.md §8(3) "RESOLVED 2026-06-17"). The lemma's interface
changed:

- `cSrc`/`cTgt` and `hcSrc*` are GONE; the internal slice range is `c_max = (ρ₀+δ₀)/L`.
- `hSrcSpine`/`hSrcRpos`/`hTgtSpine`/`hTgtRpos` are now over `Ioo 0 1`.
- `hSrcNear_L`/`hTgtNear_L` now demand the SATISFIABLE geometric relation
  "near-source spine pts are forward edge pts with `dist = foot·L`" (not the old
  unsatisfiable foot bound).
- The SPINE must be the **whole open segment** (the old "middle portion (α,1-α)" S made
  `hcover` unsatisfiable near the endpoints — this doc's item 5 below already flagged it).

Non-vacuity is now witnessed sorry-free by **`exists_twoSidedPartition_unitSegment`**
(R = open sup-ball `ball((1/2,0),1/2)`, S = whole open segment, unit segment;
axiom-clean `[propext, Classical.choice, Quot.sound]`). The general
`exists_twoSidedPartition_prefixStep` was updated to the new interface; its remaining
sorries are now on TRUE statements (the analytic R-facts for the parallelogram tube).

### SPINE FIX LANDED (2026-06-17, commit 9e82e75)

`prefixStep`'s spine was redefined from the middle portion `t ∈ (1/6, 5/6)` to the
**whole open edge `t ∈ (0, 1)`** (item 5 below had already diagnosed this).  With the
old middle-portion S, four open sorries were **false statements** — `hSband`,
`hSrcSpine`, `hTgtSpine`, `hcover` — because `of_straightArc`'s `hSband` requires S to
contain every interior segment point (`footParam ∈ (0,1)`).  All four are now
satisfiable.  `hS_sub_R` and `hfirstMid` were re-proved for `(0,1)` (still green).
**All 13 prefixStep sorries now sit on TRUE statements.**  The discharge template is
`exists_twoSidedPartition_unitSegment`, which uses this same whole-edge S and closes the
full bundle for a concrete instance — the S-dependent sorries port almost verbatim with
`v = p₂ − p₁`; only the R-strip analytic facts need the parallelogram geometry.

The parameter block and per-sorry notes below are now updated to match.

## What's been done

The tube construction (`exists_twoSidedPartition_prefixStep` in
`PLCollarSeparation.lean:865`) is scaffolded and all non-analytic parts are
proved. The ST:4713 sorries are closed via the bridge. Build is clean.

### Proved (sorry-free)

- `isOpen_regionAt` — `RegionFaceBridge.lean:121-123` (one-liner via mathlib's
  `IsOpen.connectedComponentIn`)
- `hv_nonzero`, `h_perp` — perpendicular direction exists, `dotp(v, n) = 0`
- `h_dotp_vv_pos` — `dotp(v, v) > 0` (v ≠ 0)
- `hp₁_notin`, `hp₂_notin` — endpoints excluded from the open strip
- `hS_sub_R` — 1D spine is contained in the tube
- `hfirstMid` — the segment midpoint is in the spine

### Geometric definitions (already in place)

```
L   := dist p₁ p₂                 (segment length, > 0)
v   := p₂ - p₁                    (direction vector)
w   := (-v.2, v.1)                (perpendicular direction, nonzero)
d   := ‖w‖                        (norm, > 0)
n   := (d⁻¹) • w                  (unit normal vector, perpendicular to v)
ε   := L / 6                      (half-width of the tube)
α   := 1/6                        (collar half-margin; `hRband_lb` window [α/2, 1-α/2])
mR  := ε / 4                      (margin for infDist bound)

R   := {p₁ + t•v + s•ε•n | t ∈ Ioo(0,1), s ∈ Ioo(-1,1)}     (open strip)
S   := {p₁ + t•v         | t ∈ Ioo(0, 1)}                   (1D spine, WHOLE open segment)
β   := straightPolyArc p₁ p₂ hne                              (one-segment polyarc)
```

(`cSrc`/`cTgt` were removed with the `Ioc → Ioo` interface change — `of_straightArc`
no longer takes per-end foot windows.)

## What remains (13 sorries)

### 1. `hR_open` — IsOpen R

R is the image of `Ioo(0,1) × Ioo(-1,1)` under the affine map
`(t, s) ↦ p₁ + t•v + s•ε•n`. This map is a homeomorphism (invertible affine
map with nonzero determinant because v and n are linearly independent).
Therefore R is open.

Approach: use `AffineMap.isOpenMap` or construct an explicit `Homeomorph`
between `(0,1) × (-1,1)` and R.

### 2. `hR_sc` — IsSimplyConnected R

R is convex (affine image of a convex rectangle). Any convex open set in ℝ²
is simply connected (contractible). Use `Convex.isConnected` and
homeomorphism to ℝ² or `Convex.isStarConvex` + contractibility lemma.

### 3. `hS_carrier_sub` — S ⊆ β.carrier

S is the whole open segment. `β.carrier` is the closed segment `[p₁, p₂]`.
S ⊆ carrier trivially because every point `p₁ + t•v` with `t ∈ (0, 1)` is on the
open segment, contained in the closed segment.

### 4. `hS_preconnected` — IsPreconnected S

S is the affine image of `Ioo(0, 1)`, an interval. The affine map is
continuous, and the continuous image of a (pre)connected set is preconnected.
Port the witness's `hSpre` (image of `isPreconnected_Ioo`).

### 5. `hSband` — Segment points with foot param in (0,1) are in S  ✅ now satisfiable

`β.segCarrier β.firstSeg` = closed segment `[p₁, p₂]`; `footParam p₁ p₂ (p₁+t•v) = t`.
`hSband` requires: every segment point with `footParam ∈ (0,1)` lies in S.  With the
whole-edge spine `S = {p₁+t•v | t ∈ (0,1)}` (landed 9e82e75) this is **direct** — port
the witness's `hSband`: take `y ∈ [p₁,p₂]`, write it as `(b,0)`-analog `p₁+b•v` with
`b ∈ [0,1]`, rewrite `footParam = b`, and `b ∈ (0,1)` puts `y ∈ S`.  (The old
middle-portion S made this false; that diagnosis is now resolved.)

### 6. `hRband_lb` — margin lower bound (S-independent)

For points y on the segment with footParam ∈ `Icc(α/2, 1-α/2)`:
`mR ≤ Metric.infDist y Rᶜ`.

Interpretation: for points in the safe foot window of the segment, the distance
to the boundary of R is at least mR. Since R is an open strip of half-width ε
and y is on the midline, the distance to Rᶜ (the boundary of the strip) is
at least ε. And mR = ε/4, so the inequality holds.

Approach: for y = p₁ + t•v with t ∈ Icc(α/2, 1-α/2), the closest point on
Rᶜ is at distance at least ε (the perpendicular distance from the midline to
the boundary). Compute `Metric.infDist y Rᶜ ≥ ε > mR`.

### 7. `hSrcSpine` — liftPlus(src, tgt, c, 0) ∈ S, for c ∈ Ioo(0,1)

`liftPlus src tgt c 0 = (1-c)•src + c•tgt = p₁ + c•v` (use `liftPlus_zero_eq_affineComb`).
For c ∈ Ioo(0,1) that is the spine point at param c, in S = whole open edge.  Port the
witness's `hSrcSpine`.

### 8. `hSrcNear_L` — source-near spine characterization (satisfiable form)

For p ∈ S with `dist(p, verts 0) < L`: show `p ∈ segCarrier firstSeg ∧
0 < footParam src tgt p ∧ dist(p, verts 0) = footParam src tgt p · L`.  For
`p = p₁ + c•v` (c ∈ (0,1)): footParam = c > 0, p on the closed segment, and
`dist(p, p₁) = c·L = footParam·L`.  Port the witness's `hSrcNear_L` verbatim.

### 9. `hSrcRpos` — positive infDist for source spine points, c ∈ Ioo(0,1)

`p₁ + c•v` is strictly interior to the open strip for fixed c ∈ (0,1), so
`infDist · Rᶜ > 0`.  (Pointwise positive even though it → 0 as c → 0.)

### 10. `hTgtSpine` — liftPlus(tgt, src, c, 0) ∈ S, for c ∈ Ioo(0,1)

`liftPlus tgt src c 0 = p₁ + (1-c)•v`, the spine point at param (1-c) ∈ (0,1).
Symmetric to #7 with the reversed affine combination.

### 11. `hTgtNear_L` — target-near spine characterization (satisfiable form)

Symmetric to #8, measured from `verts (Fin.last numSegs)` with
`footParam tgt src`.  Port the witness's `hTgtNear_L`.

### 12. `hTgtRpos` — positive infDist for target spine points

Symmetric to #9.

### 13. `hcover` — tapered tube coverage (∀ δ₀ > 0)

`R ∩ carrier ⊆ taperedTube R S δ₀`.  `R ∩ carrier` is the open segment
`{p₁+t•v | t ∈ (0,1)} = S`, so every such point is in S and covered by its own ball.
Port the witness's `hcover` (which calls `subset_taperedTube`).  This is exactly why S
had to be the whole open edge: with a middle-only S, endpoint-adjacent carrier points
escape every ball as δ₀ → 0.

### 14. `h_exists_target1` in `SzemerediTrotter.lean:4615`

Once Obligation A is done, this induction chains `dr` and `hstepCrosscut` from
level `start` to `N`. Each step calls `exists_twoSidedPartition_prefixStep` for
the tube, then Obligation B (local→global gluing) lifts U,V to `poolRegion`,
`hinj`, `hfactor`. The induction scaffolding is understood.

## Key reference points

- `exists_twoSidedPartition_prefixStep` (the target, 13 sorries): `PLCollarSeparation.lean:865`
- Tube `R` / spine `S` definitions and parameters: `PLCollarSeparation.lean:865-1020`
- End of lemma (call to `exists_twoSidedPartition_of_straightArc`): lines 1128-1142
- Lemma `exists_twoSidedPartition_of_straightArc` (proved, non-vacuous): `PLCollarSeparation.lean:480`
  — its 19 hypotheses are what need to be discharged
- **Discharge template** `exists_twoSidedPartition_unitSegment` (sorry-free, closes the
  full bundle for the unit segment with whole-edge S): `PLCollarSeparation.lean:1166`
- `liftPlus_zero_eq_affineComb` (`liftPlus s t c 0 = (1-c)•s + c•t`): `PLArc.lean:7203`
- `PolyArc` namespace for `firstSeg`, `segCarrier`, `segSrc`, `segTgt`, `src`, `tgt`,
  `firstMid`, `carrier`: `PLArc.lean:550-644`
- `dotp` definition: `PLArc.lean:1458` (no associated lemmas beyond `dotp_smul_left`)
- `liftPlus`, `footParam`, `taperedTube`: defined in `PLArc.lean` (search for them)
- `isOpen_regionAt`: `RegionFaceBridge.lean:121-123`
- Bridge wiring (ST:4713): `SzemerediTrotter.lean:4678-4719`

## Build command

```bash
./lake-build.sh LeanFormalizations
```
