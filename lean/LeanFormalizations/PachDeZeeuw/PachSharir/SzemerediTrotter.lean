/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Foundations
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.RotationRegular
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.PrefixSplice
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.CanonicalComponent
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Conclusions

/-!
# Szemerédi–Trotter from the simple crossing lemma

Classical point–line incidence bound in `ℝ²`, proved *conditionally* on the
simple crossing lemma `CrossingLemma.SimpleCrossingLemmaStatement`, which enters
as the single hypothesis `hCL`. The multigraph crossing lemma still implies this
layer by specializing to multiplicity `1`. The straight-segment construction
proves the drawing-validity condition `DrawnMultigraph.ArcsJoinEndpoints`
needed by that statement.

This is internal infrastructure toward Pach–de Zeeuw Theorem 2.3, not a
verbatim paper statement.

# Module layout (this file is a coordinator)

The development was split into five bounded shards under `SzemerediTrotter/`, cut
at documentation seams and top-level declaration boundaries.  Every reference is
backward — forced by Lean's elaboration order — so each shard imports the shards
before it (a linear chain).  This module re-imports them all, so downstream
consumers `import …PachSharir.SzemerediTrotter` unchanged:

* `…SzemerediTrotter.Foundations`        — incidence defs, `lineKey`, edge lists,
  `segmentArc`, `stMultigraph`, multiplicity bookkeeping, W1–W3 infrastructure
* `…SzemerediTrotter.RotationRegular`    — `straightLineIncidentAnglesDistinct`,
  `ArcsRotationRegular`, planar-layer defs, `stComponentDrawing` setup
* `…SzemerediTrotter.PrefixSplice`       — prefix-permute endpoint-splice angles
* `…SzemerediTrotter.CanonicalComponent` — split-pool relabeling + canonical
  component residual-map planarity (carries the single open `sorry`)
* `…SzemerediTrotter.Conclusions`        — `szemerediTrotter_of_*` deduction
  chain and the grid `A × A` rich-line interface `gridRichLine_of_*`
-/
