/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.Theorem11
import LeanFormalizations.PachDeZeeuw.IncidenceBound
import LeanFormalizations.PachDeZeeuw.PachSharir

/-!
# The §3 incidence assembly — project wiring

This is **project-specific wiring, not a paper statement.** It connects the two
paper-faithful modules:

* `pach-sharir` supplies the verbatim Pach–de Zeeuw Corollary 2.4
  (`PachSharir.Corollary24Statement`).
* `pdz` supplies the verbatim Theorem 1.1 reduction chain, conditional on the open
  incidence-card hypothesis
  (`PachDeZeeuw.PDZ.PositiveAuxiliaryIncidenceCardBoundStatement`).

The bridge `positiveAuxiliaryIncidenceCardBound_of_corollary24` is the paper's §3
incidence assembly (Lemmas 3.2–3.7): instantiate Corollary 2.4 at `D = 4`, present
the auxiliary curves `C_ij` as algebraic curves, establish the two-degrees-of-
freedom system with multiplicity `M = 16 d⁴`, apply the corollary, and convert the
real `max{·}` bound into the `pdz`-internal cubed-integer statement. All of that —
including the real→ℕ-cubed conversion and the `D = 4` instantiation — is wiring
that deliberately lives here, never inside a paper module. It currently carries a
single `sorry` (**Gap B**).

`pachDeZeeuwTheorem11_unconditional` then closes Theorem 1.1 by feeding the bridge
the paper-faithful (but still `sorry`-backed, **Gap A**) `PachSharir.corollary24`.
The two holes are thus named and separated: Gap A in `pach-sharir`, Gap B here;
`pdz` itself is `sorry`-free.
-/

set_option linter.style.longLine false
-- The bridge consumes `h` (Corollary 2.4) once Gap B is filled; until then its
-- body is `sorry`, so `h` reads as unused.
set_option linter.unusedVariables false

namespace IncidenceAssembly

open PachDeZeeuw PachDeZeeuw.PDZ

/--
**Gap B — the §3 incidence assembly.**

Reduce `pdz`'s open positive-product incidence-card statement to the paper-exact
Pach–Sharir Corollary 2.4. The hypothesis `h` is the result the assembly consumes
once Lemmas 3.2–3.7 are formalized; the body is `sorry` pending that work.
-/
theorem positiveAuxiliaryIncidenceCardBound_of_corollary24
    (h : PachSharir.Corollary24Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  sorry

/--
Pach–de Zeeuw Theorem 1.1 as a **closed** (hypothesis-free) statement, assembled
from the paper modules. The reduction chain is fully proven in `pdz`; the only
gaps are Gap A (`PachSharir.corollary24`) and Gap B
(`positiveAuxiliaryIncidenceCardBound_of_corollary24`), so `#print axioms`
pinpoints exactly the two holes rather than blanking the theorem.
-/
theorem pachDeZeeuwTheorem11_unconditional :
    PachDeZeeuwIrreducibleCurveDistinctDistancesStatement :=
  theorem11_irreducibleCurve_distinctDistances
    (theorem12_bipartiteDistinctDistances_of_positiveCardBound
      (positiveAuxiliaryIncidenceCardBound_of_corollary24 PachSharir.corollary24))

end IncidenceAssembly
