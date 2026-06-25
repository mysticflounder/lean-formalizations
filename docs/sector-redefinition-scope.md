# Sector redefinition — scoping the multi-segment collar residual

*Scoped 2026-06-18. Read-only investigation against `main` (PLCollarSeparation builds:
8492 jobs, exit 0; one genuine `sorry`, `PolygonalArc.lean:3140`).*

## 0. Status correction (read first)

The `ROUTE_C_PLAN.md` §8 "Collar instantiation — BLOCKED (2026-06-13)" note describes the
vertex sector as a **metric disk** `ball(verts(succ i), ρ(succ i)) ∩ vertexPlus`, and frames
the δ₀-corner-tube redefinition as "NOT yet attempted." **Both framings are now stale.**
Source-verified 2026-06-18:

- `sectorPlus`/`sectorMinus` (`PolygonalArc.lean:2842`/`:2849`) are **already** the δ₀-corner-tube
  form, in the **UNION** variant
  `vertexPlus a v b ∩ ({z | infDist z (segCarrier i) < δ₀} ∪ {z | infDist z (segCarrier (i+1)) < δ₀})`.
  The docstring (`:2820`–`:2841`, dated 2026-06-14) explains the union (not the intersection
  the §8 fix-path proposed) is required: the intersection form is a "structural NO-GO for
  gentle corners" (reach forces `δ₀ > αL/2`, glue forces `δ₀ < α·|tanψ|·‖Δ‖₂²/‖Δ‖₁`; the `α`
  cancels ⇒ empty window below ~45°).
- A collar-facing **clipped** variant `sectorPlusClipped`/`sectorMinusClipped`
  (`:2863`/`:2873`) exists and is what `collarPlus`/`collarMinus` (`:2942`/`:2951`) actually use.
- The whole collar (P1–P5) builds against the new sectors. The single remaining `sorry` is
  `PolygonalArc.lean:3140`.

This document scopes **the actual remaining gap**, not the already-completed redefinition.

## 1. The current definitions (source-verified)

```lean
-- PolygonalArc.lean:2384 / :2388  (unchanged — the τ-selected angular wedge)
noncomputable def vertexPlus  (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then convexSector a v b else reflexSector a v b
noncomputable def vertexMinus (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then reflexSector a v b else convexSector a v b

-- PolygonalArc.lean:2842 / :2849  (δ₀-corner-tube UNION form — the redefinition §8 asked for)
noncomputable def sectorPlus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i:ℕ)+1 < β.numSegs) : Set Plane :=
  vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i:ℕ)+1, hi1⟩)
    ∩ ({z | Metric.infDist z (β.segCarrier i) < δ₀}
        ∪ {z | Metric.infDist z (β.segCarrier ⟨(i:ℕ)+1, hi1⟩) < δ₀})
-- sectorMinus: same, vertexMinus.

-- PolygonalArc.lean:2863 / :2873  (clipped, collar-facing — trims the FAR arm by a footParam α-margin)
noncomputable def sectorPlusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i:ℕ)+1 < β.numSegs) : Set Plane :=
  vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i:ℕ)+1, hi1⟩)
    ∩ ( ({z | infDist z (segCarrier i) < δ₀} ∩ {z | α < footParam (segSrc i) (segTgt i) z})
      ∪ ({z | infDist z (segCarrier (i+1)) < δ₀} ∩ {z | footParam (segSrc (i+1)) (segTgt (i+1)) z < 1-α}) )
```

`sectorPlusClipped ⊆ sectorPlus` (`:2883`); both `IsOpen` (`:2897`/`:2907`). This matches the
§8 fix-path signature shape — the only deviation is **union vs intersection** of the two tube
disjuncts, which the source justifies as mandatory (see §0 and `region-face-bridge-plan §9`).

**Conclusion for §1:** no new sector definition is needed. The δ₀-corner-tube redefinition is
already in place. {{UNVALIDATED}} that the union form is mathematically the right choice; the
in-source argument is plausible and the program builds on it, but it is not separately
re-derived here.

## 2. Does it escape the constraint? (the crux)

**The original P5 collision is genuinely gone.** The metric-disk `sectorPlus_subset_taperedTube`
is now documented as **false** and is replaced by `sectorPlusClipped_subset_taperedTube`
(`:10321`), which routes every clipped-arm point through its **carrier foot-point** via the
`footParam`-Lipschitz bound (`abs_footParam_sub_le`) and the smallness
`hsmall : (‖Δ‖₁/‖Δ‖₂²)·δ₀ ≤ α/2`. **It carries no `ρ` and no `ρ ≤ δ₀`.** So P5's side of the
`δ₀ < δ₀+2αL < ρ ≤ δ₀` collision from §8 no longer exists. `isPreconnected_collarPlus`
(`:7040`) takes `hsectorW : sectorPlusClipped ⊆ taperedTube∖carrier` (no `ρ`) and overlaps
`hO1/hO2 : sectorPlusClipped ∩ bandStripPlus ≠ ∅`, discharged by
`overlap_sectorPlusClipped_bandStripPlus_src/tgt` (`:8221`/`:8285`) whose witnesses land in the
δ₀-tube disjunct — the comment at `:8276` confirms `hball`/`ρ`/`hbud` are now redundant.

**But an equivalent collision migrated to P2-vs-P3.** Budget algebra, current source:

- **P2 (cover) demands ρ LARGE.** `union_collarPlus_collarMinus` (`:3079`) and the
  instantiation require `hsrc i : δ₀ + 2α·dist(segSrc i)(segTgt i) < ρ(castSucc i)` and
  `htgt i : … < ρ(succ i)` (lines `:3088`–`3091`). These feed
  `taperedTube_subset_midBands_union_disks` (`:2574`), whose interior-vertex branch (`:2638`,
  `:2662`) routes a tube point to `ball(verts j, ρ j)`.
- **P3 (disjointness) demands ρ SMALL.** `disjoint_collarPlus_collarMinus` (`:4925`) requires
  (non-optional binders `:4939`–`4946`)
  `hballSrc : (‖Δ_first‖₁ / ‖Δ_first‖₂²)·ρ 0 ≤ α` and the `hballTgt` mirror, where
  `‖Δ‖₁ = |Δ.1|+|Δ.2|` and `‖Δ‖₂² = dotp Δ Δ`. Rearranged: `ρ 0 ≤ α·‖Δ_first‖₂²/‖Δ_first‖₁`.
  Load-bearing at `:5015`, `:5017`, `:5024`, `:5034` (clipped-sector ↔ end-cap disjointness).
- **The collision.** For the source/first edge both must hold on `ρ 0`:
  `δ₀ + 2α·‖Δ‖∞ < ρ 0 ≤ α·‖Δ‖₂²/‖Δ‖₁`. (`dist(segSrc)(segTgt) = ‖Δ‖∞` by `Prod.dist_eq`,
  used in `l1_mul_dist_le_two_dotp` `:2281`.) The sup-metric upper bound
  `‖Δ‖₂² ≤ ‖Δ‖₁·‖Δ‖∞` gives `α·‖Δ‖₂²/‖Δ‖₁ ≤ α·‖Δ‖∞`. Then `2α·‖Δ‖∞ < ρ 0 ≤ α·‖Δ‖∞` ⟹
  `2α·‖Δ‖∞ < α·‖Δ‖∞` ⟹ `False` (α, ‖Δ‖∞ > 0).

  This is the **same `‖Δ‖₂² ≤ ‖Δ‖₁·‖Δ‖∞` constraint** as §8, re-expressed: the sign on δ₀
  flipped (δ₀ no longer collides with ρ via P5), but `ρ` is now over-determined by P2-large vs
  P3-end-cap-small.

  {{NEEDS_PROOF}} no standalone `False`-from-hypotheses Lean lemma was compiled for the migrated
  P2/P3 collision the way §8 did for the old P5 one. The derivation is hand-checked against the
  binder text at `:3088`–3097, `:4939`–4946, and the verified sup-metric lemmas `:2269`/`:2281`.
  Status: CONJECTURED at the Lean level, hand-verified at the algebra level.

  Caveat: the collision binds **only the two endpoint radii `ρ 0`, `ρ last`** (where P3's
  `hballSrc/hballTgt` apply). Interior-vertex radii `ρ(succ i)` are bound by P2-large and by
  P3's `hballs`/`hbudsrc`/`hbudtgt` (geometric, not δ₀-tied) — so interior `ρ` are not obviously
  contradictory. The endpoint radii are the live obstruction.

**Why the §8 INTERSECTION redefinition does NOT help.** The current source already supersedes it
with the union form for the documented reason (`:2828`–2837): the intersection demands a band
point be within δ₀ of *both* incident edges, which for a gentle turn forces `δ₀ > αL/2`,
colliding with the glue's `δ₀ < α·|tanψ|·‖Δ‖₂²/‖Δ‖₁`. So adopting the §8 intersection form would
**reintroduce** an angle-dependent `tanψ` window. UNEQUIVOCALLY: the §8 literal fix path is a
regression; the union form already in source is the better choice and it removed the P5
collision — but it did **not** remove the P2 disk-cover's `ρ`-large demand, which is the residual.

**What actually escapes the constraint:** convert the **P2 cover's interior-vertex branch off the
metric disk** — place an interior-vertex tube point into `sectorPlusClipped`/`Minus` via the
δ₀-tube disjunct (`dist(z,v) < δ₀ ⟹ infDist z (segCarrier i) < δ₀`), **not** via
`ball(verts j, ρ j)`. That deletes the need for `hsrc`/`htgt` to pin ρ large (their only
remaining consumer is the interior-disk routing), after which the endpoint `ρ` is free to
satisfy `hballSrc`/`hballTgt` and the collision dissolves. The keystone
`exists_pos_infDist_compl_of_isCompact` (still valid) and `exists_delta_corner_confine` (`:2704`)
/ `exists_delta_nonadjacent_tube_sep` (`:2779`) supply the δ₀ budgets; they exist and are already
used in the disjointness proof.

## 3. Lemma inventory (against current, post-redefinition source)

| Property | Lemma | file:line | Verdict | Reason |
|---|---|---|---|---|
| P1 open | `isOpen_collarPlus`/`Minus` | `:3009`/`:3018` | survives verbatim | Already proven for new clipped sectors via `isOpen_sectorPlusClipped` (`:2897`). |
| P2 union | `union_collarPlus_collarMinus` | `:3079` | **needs full rework** | The interior-vertex disk branch is the sole `sorry` (`:3140`); band/endpoint branches done. Rework per `:3134`–3139 (foot-sign split + corner-tube disjunct), dropping `ball(verts j, ρ j)`. |
| P2 cover | `taperedTube_subset_midBands_union_disks` | `:2574` | needs minor re-proof OR new variant | Currently emits a `ball(verts j, ρ j)` interior disjunct (`:2588`). A δ₀-only variant emitting `dist(z, verts j) < δ₀` (point "behind" both incident feet) lets `:3140` close without ρ. {{NEEDS_PROOF}} that such a variant is provable; the `:3134` comment asserts the geometry but it is unproven. |
| P2 numSegs=1 | `union_collarPlus_collarMinus_of_numSegs_one` | `:3195` | survives | Interior-disk branch vacuous (no interior vertices); sorry-free. Why the single-segment path closes. |
| P3 disjoint | `disjoint_collarPlus_collarMinus` | `:4925` | survives verbatim | Proven for clipped sectors; uses only δ₀-corner-confine, non-adj-sep, angle-free glue `thin_of_infDist_*`, ball disjointness, endpoint separation. No `ρ ≤ δ₀`. |
| P3 4×4 grid | `disjoint_*_all` aggregators | `:4988`–5044 | survives verbatim | Built on clipped-sector lemmas. |
| P3 existence | `exists_collar_disjoint` | `:5524` | survives | Produces a `(δ₀, ρ)` with `ρ = δ₀ = M5/2`; angle-free. (Sets ρ small — fine for P3 alone, conflicts with P2-large; see §2.) |
| P4 nonempty | `collarPlus_nonempty`/`Minus` | (firstMid push) | survives verbatim | First-edge midpoint; independent of sector form. |
| P5 preconnected | `isPreconnected_collarPlus`/`Minus` | `:7040`/`:9828` | survives — already reproved | Uses `sectorPlusClipped` + `hsectorW` (no ρ) + overlaps landing in δ₀-tube disjunct (`:8276`). The §8 P5 collision is gone here. |
| P5 containment | `sectorPlusClipped_subset_taperedTube` | `:10321` | survives — already exists | Replaces the false metric-disk `sectorPlus_subset_taperedTube`. No ρ. |
| P5 sliver wrapper | `isPreconnected_collarPlus_of_sliver_budgets` | `:11210` | needs minor re-proof | Still threads `hsrc`/`htgt` (`:11238`/`11240`) only to feed the now-dead `hbud` arg. Once `:3140` removes the cover's ρ-dependence, drop these binders too. |

**NEW lemmas to build (all serving `:3140`):**

1. {{NEEDS_PROOF}} `taperedTube_interior_disk_near_edge_or_vertex` — a tube point routed to
   interior vertex `v` either has `footParam ∈ (0,1)` on an incident edge (⇒ δ₀-close to that
   edge, `infDist ≤ dist(z, foot-point) < δ₀`) or has `footParam ≤ 0` on both incident edges
   (the outer cone behind `v`), in which case `infDist z (segCarrier ·) = dist(z, v) < δ₀`. The
   genuine new sup-metric geometry (the `:3134`–3139 plan).
2. `mem_sectorClipped_of_corner_tube` — from "`z ∈ vertexPlus/Minus` (via
   `compl_sectors_eq_cornerLocus` + `ball_inter_cornerLocus`) and `z` is δ₀-close to an incident
   edge with the right foot-clip" conclude `z ∈ sectorPlusClipped`/`Minus`. (Mostly assembly of
   existing `ball_inter_cornerLocus` `:408`, `compl_sectors_eq_cornerLocus` `:334`, plus
   union/clip disjunct selection.)
3. Possibly a δ₀-only cover variant of `taperedTube_subset_midBands_union_disks` (or an in-place
   rewrite of its interior-disk disjunct) so `hsrc`/`htgt` can be deleted from
   `union_collarPlus_collarMinus` and the instantiation.

## 4. Relation to `PolygonalArc.lean:3140`

**They are the same problem, not independent.** `:3140` *is* the interior-vertex disk branch of
P2 `union_collarPlus_collarMinus`. The migrated P2-vs-P3 constraint (§2) exists *because* this
branch still routes through the metric `ball(verts j, ρ j)`, which is what forces `hsrc`/`htgt`
(ρ large). Closing `:3140` off the metric disk (per its own comment plan, using the corner-tube
disjunct `dist(z,v) < δ₀`) simultaneously (a) discharges the last `sorry`, and (b) removes the
only remaining consumer of `hsrc`/`htgt` in P2 — which lets the endpoint `ρ` satisfy P3's
`hballSrc`/`hballTgt` and dissolves the constraint.

So the sector redefinition (already done) plus closing `:3140` are jointly the fix; `:3140` is
the load-bearing node. {{NEEDS_PROOF}} that closing `:3140` suffices to drop `hsrc`/`htgt`
everywhere; the instantiation `PLCollarSeparation.lean:317` also threads them through
`_of_sliver_budgets` overlap calls (`:11288`–11301) where they feed the now-dead `hbud` arg.
Those calls need re-plumbing to a budget-free overlap variant.

## 5. Build order, risks, estimate

**Hardest first (project rule):**

1. **New lemma 1** — the sup-metric "disk point ⇒ near an incident edge or within δ₀ of vertex"
   geometry. The genuine residual mathematics (the sup-vs-Euclidean trap that has bitten prior
   end-cap work; see `collar-handoff.md`). Validate with `./lake-build.sh` on a scratch statement.
2. **New lemma 2 + close `:3140`** — assemble into the union/clip sector membership; reuse
   `ball_inter_cornerLocus`, `compl_sectors_eq_cornerLocus`, `vertexPlus_union_vertexMinus`
   (`:3044`).
3. **Drop `hsrc`/`htgt`** from `union_collarPlus_collarMinus`, the cover, and the
   `_of_sliver_budgets` overlap calls; re-derive the endpoint `ρ` window to satisfy
   `hballSrc`/`hballTgt`. Re-prove the instantiation
   `exists_twoSidedPartition_regionMinus_polygonalArc_of_collar_of_sliver_budgets`
   (`PLCollarSeparation.lean:317`) is now satisfiable for numSegs ≥ 2 (the actual unblocking).

**Risks:**

- R-A {{UNVALIDATED}}: the `:3134` cover-rework geometry ("footParam ≤ 0 ⇒ infDist = dist to
  vertex") must hold in the **sup** metric for tilted edges. Prior sup-vs-Euclidean errors
  (handoff doc) make this the highest-risk step.
- R-B: dropping `hsrc`/`htgt` may surface a different consumer; the overlap lemmas keep them as
  dead args, so a follow-on cleanup of the `_of_sliver_budgets` wrappers is needed.
- R-C: P3's `hballs`/`hbudsrc`/`hbudtgt` interior constraints must remain jointly satisfiable
  with the freed endpoint ρ; expected fine (geometric, not δ₀-tied) but unverified end-to-end.

**Estimate: 2–4 sessions** (1 session ≈ one compact): 1 for lemma 1 (the new geometry), 1 for
`:3140` + cover variant, 1–2 for the instantiation budget-bundle re-plumbing and confirming
non-vacuity for numSegs ≥ 2 (the multi-segment analogue of `exists_twoSidedPartition_unitSegment`
`PLCollarSeparation.lean:1124`).

## Critical files

- `LeanFormalizations/PachDeZeeuw/CrossingLemma/PolygonalArc.lean` — sectors `:2842`/`:2863`, cover
  `:2574`, P2 sorry `:3140`, P3 `:4925`, P5 `:7040`, clipped containment `:10321`.
- `LeanFormalizations/PachDeZeeuw/CrossingLemma/PLCollarSeparation.lean` — instantiation `:317`,
  straightArc `:480`.
- `LeanFormalizations/PachDeZeeuw/CrossingLemma/PLAssembly.lean` — geometry-free assembly target.
- `docs/ROUTE_C_PLAN.md` — §6, §8; the BLOCKED note is **stale** and should be updated to point
  here.
- `docs/region-face-bridge-plan.md` — §9, the union-vs-intersection rationale.
