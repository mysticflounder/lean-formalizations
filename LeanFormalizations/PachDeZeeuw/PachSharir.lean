/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter

/-!
# The Pach–Sharir incidence bound

Literature-facing Pach–Sharir incidence statements together with the axiom-free
internal Szemerédi–Trotter reduction used downstream.

`Theorem23.lean` exports only the exact statement surfaces from the paper
(Theorem 2.3 and Corollary 2.4). `SzemerediTrotter.lean` contains the proved,
axiom-free internal reduction from the multigraph crossing lemma to the
point-line incidence bound and the grid rich-line corollary.

-/
