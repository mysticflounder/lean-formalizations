/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.Parabola
import LeanFormalizations.ElekesSharirGuthKatz.Energy
import LeanFormalizations.ElekesSharirGuthKatz.CauchyEnergy
import LeanFormalizations.ElekesSharirGuthKatz.EnergyCeiling
import LeanFormalizations.ElekesSharirGuthKatz.RichnessLevels
import LeanFormalizations.ElekesSharirGuthKatz.Asymptotics
import LeanFormalizations.ElekesSharirGuthKatz.FiniteMinimum
import LeanFormalizations.ElekesSharirGuthKatz.Decomposition
import LeanFormalizations.ElekesSharirGuthKatz.BridgeIdentity

/-!
# Elekes–Sharir / Guth–Katz reduction layer (base)

The proven ES/GK reduction that turns the distinct-distances question into an
energy bound: the Elekes–Sharir energy identity, the dyadic richness-level
decomposition, ES-GK ledger existence, the Cauchy–Schwarz bridge from distance
energy to distinct distances, and the elementary `(E1)/(E2)` `O(n³)` energy
ceiling under no-four-cocircular. Sorry-free.

This is the **base reduction only**. The open research target — the exact
asymptotic order of `M(n) = max{E(P) : |P| = n, P in general position}` within
the window `n³/2^{O(√log n)} ≤ M(n) ≤ O(n³)` — and the D7.2 exact-emptiness
program aimed at beating the ceiling are research/strengthening work and are
**not** imported here. The open energy bound enters only as an explicit `Prop`
hypothesis on the top theorem, never as an axiom or `sorry`.

Imported from the sibling `esgk-on3` repository (base layer only). Declarations
live in `namespace Esgk`.
-/
