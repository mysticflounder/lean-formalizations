# Collar work handoff (2026-06-17)

## What's been done

The tube construction (`exists_twoSidedPartition_prefixStep` in
`PLCollarSeparation.lean:757`) is scaffolded and all non-analytic parts are
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
α   := 1/6                        (spine parameter)
cSrc := α / 2                     (source spine width)
cTgt := α / 2                     (target spine width)
mR  := ε / 4                      (margin for infDist bound)

R   := {p₁ + t•v + s•ε•n | t ∈ Ioo(0,1), s ∈ Ioo(-1,1)}     (open strip)
S   := {p₁ + t•v         | t ∈ Ioo(α, 1-α)}                 (1D spine, middle portion of segment)
β   := straightPolyArc p₁ p₂ hne                              (one-segment polyarc)
```

## What remains (15 sorries)

### 1. `hR_open` (line 900) — IsOpen R

R is the image of `Ioo(0,1) × Ioo(-1,1)` under the affine map
`(t, s) ↦ p₁ + t•v + s•ε•n`. This map is a homeomorphism (invertible affine
map with nonzero determinant because v and n are linearly independent).
Therefore R is open.

Approach: use `AffineMap.isOpenMap` or construct an explicit `Homeomorph`
between `(0,1) × (-1,1)` and R.

### 2. `hR_sc` (line 903) — IsSimplyConnected R

R is convex (affine image of a convex rectangle). Any convex open set in ℝ²
is simply connected (contractible). Use `Convex.isConnected` and
homeomorphism to ℝ² or `Convex.isStarConvex` + contractibility lemma.

### 3. `hS_carrier_sub` (line 931) — S ⊆ β.carrier

S is the middle portion of the straight segment. `β.carrier` is the closed
segment `[p₁, p₂]`. S ⊂ carrier trivially because every point `p₁ + t•v`
with `t ∈ (α, 1-α) ⊂ (0, 1)` is on the open segment which is contained in
the closed segment.

### 4. `hS_preconnected` (line 933) — IsPreconnected S

S is the affine image of `Ioo(α, 1-α)`, an interval. The affine map is
continuous, and the continuous image of a connected set is connected, hence
preconnected.

### 5. `hSband` (line 955) — Segment points with foot param in (0,1) are in S

For `β = straightPolyArc p₁ p₂ hne`, there's one segment (firstSeg = lastSeg).
`β.segCarrier β.firstSeg` = closed segment `[p₁, p₂]`.
`footParam p₁ p₂ y` = scalar t such that `y = p₁ + t•v`. If `t ∈ Ioo(0,1)`
then `y` is on the open segment. But this doesn't guarantee `y ∈ S` — only
if `t ∈ Ioo(α, 1-α)`. The hypothesis `hSband` says: for all y on the
segment with footParam ∈ (0,1), y ∈ S. This is only true if ALL open segment
points are in S, which means α = 0. 

**Wait — this may be a hypothesis mismatch.** Check what `hSband` actually
requires in the context of `exists_twoSidedPartition_of_straightArc`. The call
site passes S as the spine. The hypothesis may need a WIDER S.

**Alternative:** Redefine S to be the FULL open segment (not just the middle).
```
S := {p₁ + t•v | t ∈ Ioo(0, 1)}
```
Then `hSband` is trivially true. But then `hfirstMid` still holds
(t=1/2 ∈ Ioo(0,1)). And `hS_sub_R` still holds. This simplifies everything.

### 6. `hRband_lb` (line 963) — margin lower bound

For points y on the segment with footParam ∈ `Icc(α/2, 1-α/2)`:
`mR ≤ Metric.infDist y Rᶜ`.

Interpretation: for points in the middle portion of the segment, the distance
to the boundary of R is at least mR. Since R is an open strip of half-width ε
and y is on the midline, the distance to Rᶜ (the boundary of the strip) is
at least ε. And mR = ε/4, so the inequality holds.

Approach: for y = p₁ + t•v with t ∈ Icc(α/2, 1-α/2), the closest point on
Rᶜ is at distance at least ε (the perpendicular distance from the midline to
the boundary). Compute `Metric.infDist y Rᶜ ≥ ε > mR`.

### 7. `hSrcSpine` (line 969) — liftPlus(p₁, p₂, c, 0) ∈ S

`liftPlus(s, t, c, 0)` lifts a point perpendicular to the segment at the source
endpoint. For c ∈ Ioc(0, cSrc): the lifted point should be in S (the spine).

### 8. `hSrcNear_L` (line 982) — source-near spine characterization

For p ∈ S, if dist(p, src) < dist(segSrc, segTgt) = L, then p is on the
first segment AND footParam ∈ Ioc(0, cSrc).

### 9. `hSrcRpos` (line 988) — positive infDist for source lifts

### 10. `hTgtSpine` (line 994) — liftPlus for target endpoint

Symmetric to hSrcSpine, using cTgt.

### 11. `hTgtNear_L` (line 1007) — target-near spine characterization

Symmetric to hSrcNear_L.

### 12. `hTgtRpos` (line 1013) — positive infDist for target lifts

Symmetric to hSrcRpos.

### 13. `hcover` (line 1016) — tapered tube coverage

### 14. `h_exists_target1` in `SzemerediTrotter.lean:4615`

Once Obligation A is done, this induction chains `dr` and `hstepCrosscut` from
level `start` to `N`. Each step calls `exists_twoSidedPartition_prefixStep` for
the tube, then Obligation B (local→global gluing) lifts U,V to `poolRegion`,
`hinj`, `hfactor`. The induction scaffolding is understood.

## Key reference points

- Tube definition and parameters: `PLCollarSeparation.lean:757-928`
- End of lemma (call to `exists_twoSidedPartition_of_straightArc`): lines 1017-1032
- Lemma `exists_twoSidedPartition_of_straightArc` (already proved): `PLCollarSeparation.lean:478`
  — its ~20 hypotheses are what need to be discharged
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
