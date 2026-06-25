/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

Polygonal (PL) arcs and the segment side-functional — foundations for the
route-(c) discharge of the crosscut residual `exists_twoSidedPartition_of_arc`
(see `docs/ROUTE_C_PLAN.md`).

# What this file is (and the build status)

Route (c) discharges the geometric residual of `PlaneArcSeparation.lean` for
**polygonal** arcs.  The PL restriction is free downstream (the crossing-lemma
consumer uses only straight-segment drawings; see the plan, R1).  Everything in
this development is over the ambient plane `Plane = ℝ × ℝ`.

This is the bottom of the route-(c) node DAG:

* **L1** — the segment **side-functional** `sideForm` (signed area / left-of test):
  a continuous, affine-in-`z` functional whose sign splits the plane into the two
  open half-planes of the line through the directed segment `a → b`.  No inner
  product is used (recall `ℝ × ℝ` carries none — the determinant form sidesteps
  that).                                                              [PROVEN]
* **L2** — the **corner local model** at an interior vertex `a → v → b`.  The two
  open sectors `convexSector` (inside the turn) and `reflexSector` (outside) are
  proven open, disjoint, and **connected** — the convex sector as an intersection
  of two half-planes, the reflex sector as a *union* of two half-planes meeting at
  the reflected point `3v − a − b`.  Fully algebraic, no `arg`/`Complex`/disk.
  The corner-locus complement `(convexSector ∪ reflexSector)ᶜ = cornerLocus` (the
  two rays, algebraic form) is also proven.                           [PROVEN]
* **L3.1** — the **metric disk-localisation** `ball_inter_cornerLocus`: inside a
  disk around the vertex `v` of radius at most the distance to either neighbour, the
  (infinite) corner locus coincides with the two incident closed segments `[v,a]`,
  `[v,b]` — i.e. with the arc near `v`.  With `compl_sectors_eq_cornerLocus` this
  gives the local separation `disk ∖ β = (disk ∩ convexSector) ⊔ (disk ∩
  reflexSector)`.  The one piece of genuine 2-D linear algebra is
  `exists_param_of_sideForm_eq_zero` (a point on a line is an affine combination of
  its endpoints).                                                     [PROVEN]
* **Action 0** — the `PolyArc` carrier (finite vertex list + simplicity).
  The coercion `PolyArc → SimpleArc` and the collar (L3) are built on top in
  later work.                                                         [definitions]

The multi-segment P2 union proof (`union_collarPlus_collarMinus`) carries one
labelled `sorry` in its interior-vertex disk branch (now in the
`PLArc.CollarConstruction` shard); the single-segment variant is `sorry`-free.

# Module layout (this file is a coordinator)

The development was split into bounded shards under `PLArc/`, cut at the §-level
documentation seams.  Every reference is backward (a declaration only uses
earlier ones, forced by Lean's elaboration order), so each shard imports the
shards before it (a linear chain).  This module re-imports them all, so
downstream consumers `import …CrossingLemma.PLArc` unchanged:

* `PLArc.Foundations`        — §L1–§L3.2 + Action 0 + the PolyArc parametrisation
* `PLArc.CollarConstruction` — collar tube, side-function `g`, cover, P2 union
* `PLArc.Disjointness`       — P3 pairwise disjointness; `stripSupport`, `exists_pos_disk_radius`
* `PLArc.Existence`          — P4 nonempty + P3 existence primitives
* `PLArc.Preconnected`       — P5 preconnectedness + arcInterior membership
* `PLArc.NegativeCollar`     — P5⁻ negative-collar mirror
* `PLArc.ClippedCollar`      — P5 clipped-collar containment + final assembly
-/
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.CollarConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Disjointness
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Existence
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Preconnected
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.NegativeCollar
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.ClippedCollar
