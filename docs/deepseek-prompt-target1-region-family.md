# Task: fix the Target-1 region family — you took a dead-end branch

You are working in `lean-formalizations` (Lean 4, mathlib v4.30.0). Read this in
full before touching anything. The math-projects rule is absolute: **work the
hardest part first; never close an obligation by weakening its statement.** You
violated that rule and must back it out.

## What you did, and the proof that it is wrong

You added `LeanFormalizations/PachDeZeeuw/CrossingLemma/DartSectorPoint.lean` and
rewired `dr` in `SzemerediTrotter.lean` to `dartSectorRegion = regionAt ∘
dartSectorPoint`. The *shape* (`regionAt ∘ dartSectorPoint`) is fine. The problem
is `exists_dartSectorPoint` (DartSectorPoint.lean:145): you closed it by returning
an arbitrary far-away point `(R'+1, 0)` off the arc union, and **the existential
proposition does not mention the dart `d` at all.**

By Lean 4 definitional proof irrelevance, `Classical.choose` then returns the
*same* point for every dart. Both of these typecheck by literal `rfl` (verified):

```lean
example (G : DrawnMultigraph) (m : ℕ) (hm : m ≤ G.numEdges) (c₁ c₂ : Fin m × Bool) :
    dartSectorPoint  G m hm c₁ = dartSectorPoint  G m hm c₂ := rfl   -- ✓ compiles
example (G : DrawnMultigraph) (m : ℕ) (hm : m ≤ G.numEdges) (c₁ c₂ : Fin m × Bool) :
    dartSectorRegion G m hm c₁ = dartSectorRegion G m hm c₂ := rfl   -- ✓ compiles
```

So **`dr` is a constant function of the dart.** Consequences:

1. `h_geometric_region` (SzemerediTrotter.lean:4623) is trivially closable by
   `rfl` — but it is **hollow**. You could not close it only because you were
   trying to prove the *honest* statement while your own `dr` had collapsed.
2. `hstepCrosscut` (:4630) is **provably unsatisfiable**:
   `PrefixStepCrosscutData.hinj` requires `poolRegion` injective, while `hfactor`
   with a constant `dr (m+1)` forces `poolRegion` constant on a domain with ≥ 2
   elements (the `Fin 2` split summand). Injective + constant on ≥ 2 points is a
   contradiction.
3. `EdmondsCompatible.region_separates` is then **false** for any graph with more
   than one face (constant region ⇒ all darts "same region" ⇒ would force a
   single face).

This is exactly the decomposition the 2026-06-15 design pass already ruled out:
*an abstract `Classical.choose` region map cannot satisfy `hinj`/`hfactor`; the
region family is FORCED to be `poolRegion`-derived, not freely chosen.*

## The correct decomposition (decided; do not re-litigate)

`dr` must be built **inductively on prefix length**, with `dr (m+1)` *defined
from* the per-step crosscut partition. The base prefix (spanning tree) has one
face, so `dr start` is unconstrained. For each cotree step `m → m+1`:

1. The new graph edge is a straight segment; realize it as a one-segment
   `PolygonalArc` β. **Keep** your `straightPolygonalArc` / `arcToPolygonalArc` — they are
   correct and reusable.
2. Let `R := residualFaceRegion (level m) (Face_mk c₁)` be the single predecessor
   face the new edge crosscuts (`c₁ c₂` are its two splice corners). Get the two
   sides via the **already-proved**
   `exists_twoSidedPartition_of_straightArc` (PLCollarSeparation.lean:478):
   `∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V`.
3. Define
   `poolRegion : ({f // f ≠ Face_mk c₁} ⊕ Fin 2) → Set (ℝ × ℝ)` by
   - `inl ⟨f, _⟩ ↦ residualFaceRegion (level m) f`  (untouched old faces keep their region)
   - `inr 0 ↦ U`,  `inr 1 ↦ V`                       (the two new sides)
4. Define `dr (m+1) d := poolRegion (splitClass d)`, where `splitClass` is the
   **exact** expression in `PrefixStepCrosscutData.hfactor`
   (`insertedFaceSplitPoolEquiv … (Face_mk ((prefixStepDartEquiv m).symm d))`).
   Then `hfactor` is `rfl` and `region_separates_prefixStep_sameFace_concrete`
   (RegionFaceBridge.lean:432) consumes it directly.
5. Prove `hinj`: `U ≠ V` from `IsTwoSidedPartition.disjoint` + `.nonempty_left/right`;
   and `U, V` differ from every old face region because `U, V ⊆ R` (the split
   face) while distinct old faces are disjoint from `R`.

## The two genuinely hard obligations — do these FIRST

- **`hregion`** (the real content `h_geometric_region` was gesturing at): the two
  splice corners `c₁, c₂` of the new cotree edge face the **same** predecessor
  face — i.e. the new edge is a crosscut of a single face, so `Face_mk c₁ =
  Face_mk c₂` at level `m`. Note the ST:4713 sorries (SzemerediTrotter.lean:4718,
  4724) are *also* "cotree co-faciality" — check whether they share this content.
- **Discharging the collar hypotheses** of `exists_twoSidedPartition_of_straightArc`
  (the long hypothesis list, PLCollarSeparation.lean:478–513) for the straight
  graph edge. This is the irreducible plane-geometry work.

## Guardrails (hard requirements)

- **Delete the entire §2 of `DartSectorPoint.lean`** (lines 118–217:
  `exists_dartSectorPoint`, `dartSectorPoint`, `dartSectorPoint_mem_drawingComplementIn`,
  `dartSectorRegion`, `dartSectorRegion_hcomp`) — wrong decomposition. **Keep §1**
  (`straightPolygonalArc`, `straightPolygonalArc_src/_tgt/_carrier`, `arcToPolygonalArc`). Update
  the file's module docstring so it no longer advertises the deleted region map or
  a `{{NEEDS_PROOF}}` sorry the code no longer contains.
- **Do NOT** close `h_geometric_region` with `rfl` and call it done. It is hollow;
  the value is in `poolRegion`/`hinj`/`hfactor` + `hregion`.
- Never substitute a weaker statement to make a `sorry` go away. If a piece is
  intractable, say so in unequivocal terms and stop — do not paper over it.
- After every compile, run `#print axioms` on the theorems you touched and report
  the exact remaining `sorry` set honestly. Current sorries:
  SzemerediTrotter.lean 4623, 4630, 4718, 4724.
- Build with `./lake-build.sh` (not bare `lake`). 100-char lines.

## Proven helpers you should reuse (do not reprove)

- `region_separates_prefixStep_sameFace_concrete` — RegionFaceBridge.lean:432
  (takes exactly `poolRegion`/`hfactor`/`hinj`; `hpool` already wired).
- `residualFaceRegion`, `residualFaceRegion_mk` — RegionFaceBridge.lean:232 / :240.
- `faceMk_facePerm` — EulerBound.lean:71 (makes `hconst` a one-line `congrArg`).
- `regionSeparates_prefix_of_crosscut`, `edmondsCompatibleAtPrefix` —
  EdmondsConstruction.lean:148 / :194 (the iteration harness consuming your data).
- `IsTwoSidedPartition` fields — PlaneArcSeparation.lean:100.

---

## ADDENDUM (2026-06-16) — the two REAL geometric obligations; blocker corrections

You reported two "topological blockers." Audit: one is a freebie, the other was
mis-scoped into a **false** statement. Read this before scoping any sorries.

### Correction 1 — `IsOpen (regionAt …)` is a one-liner, not a Mathlib gap

Mathlib **has** `IsOpen.connectedComponentIn` (LocallyConnectedSpace;
`Mathlib/Topology/Connected/LocallyConnected.lean:70`). `ℝ × ℝ` is a
`LocallyConnectedSpace`. So (verified compiling):

```lean
theorem isOpen_regionAt (G : DrawnMultigraph) {R₀ : Set (ℝ × ℝ)}
    (hR₀ : IsOpen R₀) (p : ℝ × ℝ) : IsOpen (regionAt G R₀ p) :=
  (isOpen_drawingComplementIn G hR₀).connectedComponentIn
```

Add it to `RegionFaceBridge.lean` and move on. (Process note: "Mathlib lacks X"
needs a `grep` of `.lake/packages/mathlib/` before it counts as a blocker.)

### Correction 2 — DO NOT prove or sorry `IsSimplyConnected (regionAt p)`. It is FALSE.

The faces here are **not** disks. The design works inside a fixed open **disk**
`R₀` (to avoid sphere compactification, see `region-face-bridge-plan.md` §4).
`hcard1` says the spanning-tree prefix has **one** face `= R₀ ∖ tree`, which is
**annular** (`π₁ = ℤ`, a loop around the tree) — not simply connected. The outer
face is never a disk either. Sorrying `IsSimplyConnected (regionAt p)` scaffolds a
false lemma — the forbidden "false foundation."

`IsSimplyConnected R` in `exists_twoSidedPartition_of_straightArc` is **not about
the face**. Its `R` is a simply-connected **tube** around the arc (the arc's
endpoints lie in `Rᶜ`; the SC hypothesis is consumed once at the `id : R→R` lift,
per `ROUTE_C_PLAN.md` tapered-tube design). A tube is simply connected **by
construction**. Do not conflate the tube `R` with the global face `regionAt p`.

### Obligation A — tube instantiation + collar discharge (heavy-mechanical PL)

Construct the SC tube and discharge the ~30 collar hypotheses of
`exists_twoSidedPartition_of_straightArc` (itself sorry-free):

```lean
theorem exists_twoSidedPartition_prefixStep
    (G : DrawnMultigraph) (m : ℕ) (hm' : m + 1 ≤ G.numEdges)
    (p₁ p₂ : ℝ × ℝ)
    (hp : (G.prefixEdges (m + 1) hm').endpoints (Fin.last m) = (p₁, p₂))
    (hne : p₁ ≠ p₂) :
    ∃ R U V : Set (ℝ × ℝ),
      IsOpen R ∧ IsSimplyConnected R ∧ p₁ ∈ Rᶜ ∧ p₂ ∈ Rᶜ ∧
      IsTwoSidedPartition
        (CrossingLemma.PlaneArcSeparation.regionMinusArc R
          (straightPolygonalArc p₁ p₂ hne).toSimpleArc) U V := by
  sorry  -- build tube R; discharge collar hyps; apply exists_twoSidedPartition_of_straightArc
```

Here `IsSimplyConnected R` is TRUE (R is the tube you build) — not a face-disk claim.

### Obligation B — local→global gluing (the conceptual crux; still Jordan-free)

The tube gives two **local** sides `U, V` of the arc. `poolRegion` needs two
**distinct global** complement-components, matched to the combinatorial split-pool
classes `inr 0 / inr 1`, with old faces filling `inl`. From Obligation A's local
partition + the inductive `dr` at level `m`, produce
`poolRegion`/`hinj`/`hfactor` (and `hregion`):

```lean
-- inl ⟨f,_⟩ ↦ residualFaceRegion (level m) f
-- inr 0 ↦ (global region containing U),  inr 1 ↦ (global region containing V)
-- hinj    : U-region ≠ V-region ≠ each old region
-- hfactor : dr (m+1) d = poolRegion (insertedFaceSplitPoolEquiv … d)
-- hregion : dr m c₁ = dr m c₂  (crossing-free segment lies in ONE region)
```

This is `connectedComponentIn` plumbing + the crossing-free hypothesis — **not**
Jordan. It is the heart of the Edmonds direction (combinatorial split ⟺ geometric
side) and is the real remaining math.

### Net
- `isOpen_regionAt`: do it (freebie).
- `IsSimplyConnected (regionAt p)`: FALSE — never sorry it.
- Remaining: Obligation A (heavy-mechanical) + Obligation B (the crux). Both Jordan-free.

---

## ADDENDUM (2026-06-17) — Obligation A's target lemma is VACUOUS; foundation redesign dispatched

**STOP — do not work Obligation A as scoped above.** The lemma it instantiates,
`exists_twoSidedPartition_of_straightArc` (PLCollarSeparation.lean:479), is
sorry-free but **VACUOUS**: its hypothesis bundle is jointly **unsatisfiable**, so
no caller can ever discharge it. Kernel-checked — `False` follows from its own
hypotheses `hSband` + `hSrcNear` (+ `hsrc`, `hballSrc`, `cSrc ≤ 2α`, `α < 1/3`).
The same defect makes the general multi-segment sliver-budget collar chain vacuous
(any `numSegs`), also kernel-checked. DeepSeek's tube work
(`exists_twoSidedPartition_prefixStep`, :766) is correct in shape but points at an
inapplicable lemma.

**Root cause (genuine gap, not a typo):** the source end-cap radius `ρ 0` is forced
`> 2α·L₁` by `hsrc`, but the "near-spine ⇒ first-edge slice" decomposition
(`taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine`, PolygonalArc.lean:7802,
applied at 7820–7851) requires every spine point within `ρ 0 + δ₀` of the endpoint
to have foot-parameter `≤ cSrc ≤ 2α`. The spine (forced ⊇ whole open edge by
`hSband`) has points in the annulus `(cSrc·L₁, ρ 0 + δ₀)` that violate this. The
honest discharge helper `arcInterior_near_src` (PolygonalArc.lean:7278) only reaches radius
`cSrc·L₁ < ρ 0`. The end-cap radius `ρ 0` is conflated with the collar reach budget.

**Blast radius:** contained. Nothing completed/axiom-clean depends on the infected
lemmas — the sole consumer is the sorried, uncalled `exists_twoSidedPartition_prefixStep`.
So the redesign invalidates no standing result.

**Status:** a background math-prover was dispatched (2026-06-17) to redesign the
end-cap/near-spine connectivity — decouple the cap radius from the foot-window
`cSrc` so the lemma becomes genuinely applicable, with a concrete sorry-free
instantiation as the non-vacuity acceptance test. Collar-discharge work (Obligations
A/B) is **on hold** until that lands. See memory facts `01KVA7F09NKJ4GN3C0P9G2GJCE`
(vacuity) and `01KVA86G6E2TWDXKSFS1RG0KWT` (root cause).
