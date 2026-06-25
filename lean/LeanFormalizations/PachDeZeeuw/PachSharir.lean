/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter
import LeanFormalizations.PachDeZeeuw.PachSharir.GenericProjection

/-!
# The Pach–Sharir incidence bound

Literature-facing Pach–Sharir incidence statements together with the
internal Szemerédi–Trotter reduction used downstream.

`Theorem23.lean` exports only the exact statement surfaces from the paper
(Theorem 2.3 and Corollary 2.4). `SzemerediTrotter.lean` contains the internal
reduction from the simple crossing lemma (`CrossingLemma.SimpleCrossingLemmaStatement`,
entering as hypothesis `hCL`) to the point-line incidence bound and the grid
rich-line corollary.

-/
