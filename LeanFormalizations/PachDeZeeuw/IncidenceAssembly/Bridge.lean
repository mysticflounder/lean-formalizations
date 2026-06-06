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
  (`PachDeZeeuw.PositiveAuxiliaryIncidenceCardBoundStatement`).

The bridge `positiveAuxiliaryIncidenceCardBound_of_corollary24` is the paper's §3
incidence assembly (Lemmas 3.2–3.7): instantiate Corollary 2.4 at `D = 4`, present
the auxiliary curves `C_ij` as algebraic curves, establish the two-degrees-of-
freedom system with multiplicity `M = 16 d⁴`, apply the corollary, and convert the
real `max{·}` bound into the internal cubed-integer statement. All of that —
including the real→ℕ-cubed conversion and the `D = 4` instantiation — is wiring
that deliberately lives here, never inside a paper module. It currently carries a
single `sorry` (**Gap B**).

Accordingly this file is conditional on the exact paper statement
`PachSharir.Corollary24Statement`; it does not manufacture a hypothesis-free
theorem by routing through any `sorry`-backed placeholder.
-/

set_option linter.style.longLine false

namespace IncidenceAssembly

open PachDeZeeuw

/--
**Gap B — the §3 incidence assembly.**

Reduce `pdz`'s open positive-product incidence-card statement to the paper-exact
Pach–Sharir Corollary 2.4. The hypothesis `_h` is the result the assembly consumes
once Lemmas 3.2–3.7 are formalized; the body is `sorry` pending that work, so the
hypothesis is underscored to mark it intentionally-unused until Gap B is filled.
-/
theorem positiveAuxiliaryIncidenceCardBound_of_corollary24
    (_h : PachSharir.Corollary24Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  sorry

/--
Conditional assembly of Pach–de Zeeuw Theorem 1.1 from the exact paper statement
of Pach–Sharir Corollary 2.4.

This theorem is axiom-free apart from the explicit hypothesis `h24`; the only
remaining unfinished work is the bridge theorem above.
-/
theorem irreducibleCurve_distinctDistances_of_corollary24
    (h24 : PachSharir.Corollary24Statement) :
    PachDeZeeuwIrreducibleCurveDistinctDistancesStatement :=
  irreducibleCurve_distinctDistances
    (bipartiteDistinctDistances_of_positiveCardBound
      (positiveAuxiliaryIncidenceCardBound_of_corollary24 h24))

end IncidenceAssembly
