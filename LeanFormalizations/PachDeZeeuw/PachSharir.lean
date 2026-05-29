/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter

/-!
# The Pach–Sharir incidence bound

Formalization of the Pach–Sharir incidence bound for a set of points and a set
of bounded-degree real algebraic curves forming a *system with two degrees of
freedom and multiplicity `M`* (Pach–de Zeeuw, "Distinct distances on algebraic
curves in the plane," Theorem 2.3; and its `ℝ^D` variant).

This module supplies the load-bearing incidence input that the `pdz` module
reduces Theorem 1.1 to (`PositiveAuxiliaryIncidenceCardBoundStatement`, after the
auxiliary-curve construction, generic projection, and cell bounds). The proof
goes through a Szemerédi–Trotter-type argument that bottoms out in the multigraph
crossing inequality, consumed from the sibling `crossing-lemma` module.

-/
