# scratch/ — preserved WIP from deleted agent worktree branches

These `.patch` files preserve unmerged work-in-progress that lived on
`worktree-agent-*` branches. The agent worktrees were cleaned up (2026-06-18);
the branches' unique commits were exported here as patches and the branches then
deleted. This directory is **not** part of the build (it's outside `lean/`).

Re-apply a patch with `git am < scratch/<file>.patch` (preserves the original
commit message + authorship), or inspect it as a plain diff. One patch no longer
applies cleanly onto current `main` because the target files have since diverged
— reconcile by hand if reviving that thread.

| Patch | Orig. commit | Applies onto current main? | Summary |
|-------|-------------|----------------------------|---------|
| `wip-dartSectorPoint-8e9b364.patch` | `8e9b364` (was `worktree-agent-a22f148e097f19bba`) | yes | New `CrossingLemma/DartSectorPoint.lean` (187 lines): `dartSectorPoint` (dart → off-vertex sector point in the drawing complement, via `Classical.choose` of `exists_dartSectorPoint`), its membership lemma, and `straightPolyArc`/`arcToPolyArc` (graph arc → one-segment `PolyArc`, sorry-free). The one genuine plane-geometry fact (a small angular wedge at a drawing vertex misses the finite arc union) is isolated as private `exists_dartSectorPoint` with a `{{NEEDS_PROOF}}` flag; everything else green. |
| `wip-twoSidedPartition-straightArc-e0cb5be.patch` | `e0cb5be` (was `worktree-agent-a3d18b47bfd11fb99`) | no (PLCollarSeparation/PLArc diverged) | `exists_twoSidedPartition_of_straightArc`: single-segment (`numSegs = 1`) two-sided partition that sidesteps the multi-segment endpoint-cap radius contradiction. Disjointness proved directly by side-separation (collar± ⊆ {±sideForm}); adds clean `numSegs = 1` entry points (`union_collarPlus_collarMinus_of_numSegs_one`, etc.) to avoid a pre-existing `sorry` in the general union lemma's interior-vertex-disk branch. Claims kernel-clean closure (`propext, Classical.choice, Quot.sound`). Touches `PLArc.lean` (+105) and `PLCollarSeparation.lean` (+402). |

Both threads target the open crossing-lemma residual
`exists_twoSidedPartition_of_arc` (see `ROUTE_C_PLAN.md` /
`docs/AUDIT_MATRIX.md`).
