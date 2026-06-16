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
   `PolyArc` β. **Keep** your `straightPolyArc` / `arcToPolyArc` — they are
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
  (`straightPolyArc`, `straightPolyArc_src/_tgt/_carrier`, `arcToPolyArc`). Update
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
