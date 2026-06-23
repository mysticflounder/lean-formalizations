/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.GapBSupport
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.SectionThreeInputs
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.SectionThreeAssembly

/-!
# incidence-assembly — project wiring root

Root aggregator for the project-specific wiring that closes Pach–de Zeeuw
Theorem 1.1 from the paper-faithful sibling modules.

* `IncidenceAssembly.GapBSupport` — the dimension-free combinatorial bricks feeding
  the assembly (the proven point–point pigeonhole bound `incidence_pigeonhole`).
* `IncidenceAssembly.SectionThreeInputs` — the three faithful §3 named literature
  inputs (Lemma 3.4 `Lemma34PartitionStatement`, Lemma 3.5 / Corollary 2.4
  `Lemma35AuxIncidenceStatement`, Lemma 3.6 `Lemma36MinorIncidenceStatement`), each a
  `def … : Prop` in `MilnorThom22FiniteStatement` house style.
* `IncidenceAssembly.SectionThreeAssembly` — the sorry-free §3 incidence assembly
  (`positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs`) and the release
  spine (`irreducibleCurve_distinctDistances_of_sectionThreeInputs`), reducing
  Pach–de Zeeuw Theorem 1.1 to the three named inputs.

The release rests on the **ℝ⁴ named-input boundary** (Option B of
`docs/gap-b-named-inputs-design.md`): the consumer of §3 is the ℝ⁴ Corollary-2.4
content (Lemma 3.5), not the planar `Theorem23Statement`, so the crossing lemma is
left off this path. See `docs/gap-b-release-assembly.md` for the dependency chain
and the top-theorem axiom closure.
-/
