/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.Bridge
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.GapBSupport

/-!
# incidence-assembly — project wiring root

Root aggregator for the project-specific wiring that closes Pach–de Zeeuw
Theorem 1.1 from the paper-faithful sibling modules. See `IncidenceAssembly.Bridge`
for the §3 incidence assembly (Gap B) and the closed theorem, and
`IncidenceAssembly.GapBSupport` for the dimension-free combinatorial bricks feeding
Gap B (the proven point–point pigeonhole bound `incidence_pigeonhole`).
-/
