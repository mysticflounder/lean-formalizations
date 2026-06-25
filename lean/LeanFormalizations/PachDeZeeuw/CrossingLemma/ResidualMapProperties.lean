/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepCore
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepBulk
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.SameFaceInsertion
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.CotreeBlockStep
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.SimplicityConnectivity

/-!
# Euler witness properties of the residual combinatorial map

This file proves the two EU-witness hypotheses about the residual combinatorial
map `residualMap G hARR` (built in `ResidualMap.lean`):

* `residualMap_isSimple` — under a no-loops / no-parallel-edges hypothesis on the
  drawing `G`, the residual map is simple (`CombinatorialMap.IsSimple`).
* `residualMap_connected` — under a graph-connectivity hypothesis on `G`, the
  residual map is connected (`CombinatorialMap.Connected`).

The structural heart is `residualMap_vertexMk_eq_iff`: two darts have the same
vertex class iff they share an `incidentEnds` block, i.e. have the same
`dartAnchor`. This follows from the block-diagonal structure of `vertexPerm`
(`Equiv.sigmaCongrRight` keeps the sigma-fibers invariant) together with the fact
that the per-block rotation is `finRotate` conjugated by `isoFin`, hence
transitive on each block.

The map language follows Lando--Zvonkin, *Graphs on Surfaces and Their
Applications*, §1.3.3: darts carry a vertex rotation `σ`, a fixed-point-free edge
involution `α`, and a face permutation `φ` forced by the map relation
(Proposition 1.3.16 and Remark 1.3.19; Lean uses the corresponding left-action
convention `facePerm * edgePerm * vertexPerm = 1`).  The prefix-step insertion
witnesses below construct the corresponding permutation equalities directly for
leaf insertions and same-face insertions.

Everything is sorry-free and axiom-clean.

# Module layout (this file is a coordinator)

The development was split into bounded shards under `ResidualMapProperties/`, cut
at documentation seams and (inside the long prefix-step block) at top-level
declaration boundaries.  Every reference is backward — forced by Lean's
elaboration order — so each shard imports the shards before it (a linear chain).
This module re-imports them all, so downstream consumers
`import …CrossingLemma.ResidualMapProperties` unchanged:

* `…ResidualMapProperties.Helpers`                — SameCycle/finRotate helpers, dartAnchor ↔ vertex class
* `…ResidualMapProperties.PrefixStepCore`         — incident-ends bookkeeping + endpoint angular order
* `…ResidualMapProperties.PrefixStepBulk`         — the large prefix-step relabeling proofs
* `…ResidualMapProperties.SameFaceInsertion`      — same-face witnesses from endpoint splices
* `…ResidualMapProperties.CotreeBlockStep`        — reverse-cotree block-step witnesses
* `…ResidualMapProperties.SimplicityConnectivity` — (A) residualMap_isSimple, (B) residualMap_connected
-/
