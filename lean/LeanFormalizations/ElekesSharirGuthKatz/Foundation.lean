/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition

/-!
# Foundation — proof-local indexed primitives.

Defines `Point`, `Config`, `Config.toFinset`, and `hIndexed`. The energy
decomposition argument is naturally stated over function-indexed
configurations `Fin n → ℝ²`; the canonical `Esgk.h` from
`the canonical distinct-distances minimum` is stated over `Finset ℝ²`. The
image-finset operation `Config.toFinset` plus the lemma `Config.toFinset_card`
(in `Esgk.Bridge`) mediate between the two shapes.
-/

namespace Esgk

open EuclideanGeometry

/-- Alias for the ambient plane in this problem. -/
abbrev Point : Type := ℝ²

/-- An indexed configuration of `n` points in the plane. -/
abbrev Config (n : ℕ) : Type := Fin n → Point

/-- Image-finset of an indexed configuration: the set of points that appear in `p`.
Cardinality equals `n` exactly when `p` is injective (see `Config.toFinset_card`). -/
noncomputable def Config.toFinset {n : ℕ} (p : Config n) : Finset Point := Finset.image p Finset.univ

/-- Indexed-shape minimum distinct-distance count over general-position configurations.
Bridges to the canonical `Esgk.h` (Finset-shape) via `Bridge.hIndexed_eq_h`; equivalent
on both sides via `Config.toFinset` / `Finset.equivFin`. -/
noncomputable def hIndexed (n : ℕ) : ℕ := sInf {k : ℕ | ∃ p : Config n, Function.Injective p ∧
    InGeneralPosition (Config.toFinset p) ∧
    k = distinctDistances (Config.toFinset p)}

end Esgk
