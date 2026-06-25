/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition
import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.Energy
import LeanFormalizations.ElekesSharirGuthKatz.Parabola

/-!
# Finite-minimum transfer for `hIndexed`.

Connects per-configuration distance counts to `hIndexed n = sInf …` via
`Nat.sInf_le` / `Nat.le_sInf`. `gp_config_nonempty` is an internal helper
needed for the `sInf` lower-bound transfer; the two public lemmas
(`hIndexed_le_of_config`, `all_configs_lower_bound_to_hIndexed_lower_bound`)
take the FCM general-position predicate over `Config.toFinset p`.
-/

namespace Esgk

open EuclideanGeometry

/-- For every `n`, an injective general-position `n`-point configuration exists.
Internal helper for the `sInf` lower-bound transfer in
`all_configs_lower_bound_to_hIndexed_lower_bound`; not in the public validation manifest. -/
theorem gp_config_nonempty : ∀ n : ℕ, ∃ p : Config n, Function.Injective p ∧ InGeneralPosition (Config.toFinset p) := fun n ↦ ⟨parabolaConfig n, parabolaConfig_inj n, parabolaConfig_inGeneralPosition n⟩


/-- Per-configuration upper bound: `hIndexed n ≤ #distances(p)` for any injective GP
configuration. Direct from `Nat.sInf_le` applied to the defining set of `hIndexed`. -/
theorem hIndexed_le_of_config {n : ℕ} (p : Config n)
    (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) :
    hIndexed n ≤ NumDistances p := by
  apply Nat.sInf_le
  exact ⟨p, hp, hgp, rfl⟩


/-- Bulk transfer of per-configuration lower bound to `hIndexed n` via `le_csInf`,
discharging the nonemptiness side-condition with `gp_config_nonempty`. -/
theorem all_configs_lower_bound_to_hIndexed_lower_bound {n : ℕ} {B : ℕ}
    (hB : ∀ p : Config n, Function.Injective p →
      InGeneralPosition (Config.toFinset p) → B ≤ NumDistances p) :
    B ≤ hIndexed n := by
  apply le_csInf
  · obtain ⟨p, hp_inj, hp_gp⟩ := gp_config_nonempty n
    exact ⟨NumDistances p, p, hp_inj, hp_gp, rfl⟩
  · rintro k ⟨p, hp_inj, hp_gp, rfl⟩
    exact hB p hp_inj hp_gp


end Esgk
