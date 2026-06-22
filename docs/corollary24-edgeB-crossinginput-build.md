# Corollary 24 — Edge-B top-level output (`EdgeBCrossingInput.lean`)

Author: Adam McKenna (orchestrator, written + validated inline on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open CrossingLemma`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBCrossingInput.lean`.

Status: **PROVEN, sorry-free, axiom-clean.** `#print axioms edgeB_crossingInput`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`, no
custom axioms). Same closure for `cConst_pos`. This confirms the theorem does not touch
the parked `SzemerediTrotter.lean:4533` line-case `sorry` (which is off the import path that
feeds this proof's closure).

## Scope (the capstone of task #43)

`edgeB_crossingInput` is the top-level Edge-B output: the curve analogue of
`szemerediTrotter_of_crossingLemma`. It composes the six already-landed `edgeBMultigraph`
discharges through the landed M-form incidence endgame
`incidence_bound_of_multigraphCrossingLemma` (`MultigraphIncidenceEndgame.lean:154`,
conditional on the parked `CrossingLemmaMultigraphStatement`), plus one elementary
rpow-absorption step. It is PURE COMPOSITION — no new analysis.

## Shipped signatures (exact)

```lean
noncomputable def edgeBCrossingConst (d M : ℕ) : ℝ :=
  PachSharir.SzemerediTrotter.multigraphIncidenceConst M * (cConst d : ℝ)   -- = 64*M*cConst d

theorem cConst_pos (d : ℕ) : 0 < cConst d

theorem edgeB_crossingInput
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞)) :
    (PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ))
```

## The composition (`n := cConst d * Γ.card`)

Instantiate `incidence_bound_of_multigraphCrossingLemma` at `G := edgeBMultigraph d M P Γ`,
`m := P.card`, `n := cConst d * Γ.card`, the same `M`/`hM`. The single non-obvious choice is
`n`, which must serve BOTH endgame slots simultaneously:

- `he : I ≤ G.numEdges + n` — discharged by `edgeB_incidence_le_numEdges_add d M P Γ` (E1),
  whose bound is exactly `I ≤ numEdges + cConst d * Γ.card`; `n` is that slack verbatim.
- `hcr : G.crossings ≤ M * n ^ 2` — `G.crossings = M * Γ.card ^ 2` (definitional, `rfl`), and
  `Γ.card ≤ cConst d * Γ.card` because `0 < cConst d` (`cConst_pos`, via `Nat.le_mul_of_pos_left`),
  so `M·Γ.card² ≤ M·(cConst d·Γ.card)²` by `gcongr`. (Picking `n := Γ.card` would discharge
  `hcr` but break `he`; picking `n := cConst d·Γ.card` discharges both.)

The other four hypotheses are the landed discharges verbatim: `hv` ← `edgeBMultigraph_card_V`
(`.V.card = P.card`, `rfl`); `hmult` ← `edgeBMultigraph_multiplicity_le_M M P Γ hpp`;
`hjoin` ← `edgeBMultigraph_arcsJoinEndpoints d M P Γ`; `hwd` ← `edgeBMultigraph_wellDrawn P Γ hcc`.

## The constant and the rpow absorption

The endgame yields `(I:ℝ) ≤ 64·M · (P.card^{2/3}·(cConst d·Γ.card)^{2/3} + P.card + cConst d·Γ.card)`.
Folding `cConst d` out to the constant `edgeBCrossingConst d M = 64·M·cConst d`:

- `(cConst d·Γ.card)^{2/3} = cConst d^{2/3}·Γ.card^{2/3}` (`Real.mul_rpow`, nonneg args).
- `cConst d^{2/3} ≤ cConst d` because `1 ≤ cConst d` and `2/3 ≤ 1`
  (`Real.rpow_le_rpow_of_exponent_le` + `Real.rpow_one`).
- Term-by-term: `P.card^{2/3}·(cConst d·Γ.card)^{2/3} ≤ cConst d·(P.card^{2/3}·Γ.card^{2/3})`;
  `P.card ≤ cConst d·P.card`; `cConst d·Γ.card = cConst d·Γ.card`. The two slack terms collected
  by `nlinarith` (after `push_cast` distributes the `ℕ→ℝ` cast of `n` and `rw [Real.mul_rpow]`
  turns the product-rpow into an atom).

`C d M := 64·M·cConst d` is a polynomial in `d, M` only — all `Corollary24Statement` requires.
`cConst d = ((d+1)^5+d+1)·(d+1) + ((d+1)^5+d)·d` (from E1, `EdgeBE1.lean`).

## The hpp/hcc scoping decision (faithful, not a workaround)

`edgeB_crossingInput` takes `hpp`/`hcc` in the `PlanePoly`/`ℝ × ℝ` representation DIRECTLY
(verbatim the clauses (iv)/(vi) consume), NOT `PachSharir.TwoDegreesOfFreedom`. Reason: the
curve–curve clause `hcc` ranges over distinct `EdgeBCurve`s `H₁ ≠ H₂`. If `Γ` contained
associate-but-distinct carriers with the same zero set (e.g. `h` and `2·h`), `hcc` would demand
a finite self-intersection `(γ ∩ γ).encard ≤ M` which is false (the whole infinite curve), and a
`.image`-deduplicated `TwoDegreesOfFreedom` clause (which never compares a curve with itself)
cannot supply it. So `h2dof ⇏ hcc` in general.

The `TwoDegreesOfFreedom → (hpp, hcc)` conversion (which additionally needs zero-set injectivity
on `Γ` — supplied downstream by reducing each carrier to its normalized irreducible factors, so
distinct carriers have distinct zero sets) is the separate downstream node
`edgeB-component-reduce`/`edgeB-chart-bridge` (design §5.3), kept out of this file so it stays
pure composition. This is a faithful decomposition of the obligation, not a restriction that
weakens the result.

## Landed leaves consumed

- The six discharges: `edgeBMultigraph_card_V`, `edgeBMultigraph_numEdges_eq_sum` (via E1),
  `edgeB_incidence_le_numEdges_add`, `edgeBMultigraph_multiplicity_le_M`,
  `edgeBMultigraph_arcsJoinEndpoints`, `edgeBMultigraph_wellDrawn`.
- The endgame `PachSharir.SzemerediTrotter.incidence_bound_of_multigraphCrossingLemma` +
  `multigraphIncidenceConst` (`MultigraphIncidenceEndgame.lean`).
- `cConst`, `edgeBMultigraph`, `EdgeBCurve`, `evalPlaneZeroSet` (`EdgeBE1.lean`, `EdgeBMultigraph.lean`,
  `LocalArc.lean`); `PachSharir.incidenceCount` (`Theorem23.lean`).
- mathlib: `Real.mul_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_one`, `Real.rpow_nonneg`,
  `Nat.le_mul_of_pos_left`, `mul_le_mul_of_nonneg_left`, `gcongr`, `nlinarith`, `positivity`.

## New local content

- `cConst_pos` — `0 < cConst d` (`unfold cConst; positivity`).
- `edgeBCrossingConst` — the `C d M := 64·M·cConst d` constant.
- The composition + rpow-absorption proof of `edgeB_crossingInput`.

No new analysis. Pure glue over landed leaves + elementary real-power arithmetic.

## Gate results

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCrossingInput` →
  `Build completed successfully (8526 jobs).` — no warnings/errors from this file (the only
  build warnings are pre-existing, in the parked `PLCollarSeparation.lean` and the line-case
  `SzemerediTrotter.lean`). Aggregator `CrossingLemma` build green (8475) with the import wired.
- `#print axioms edgeB_crossingInput` = `[propext, Classical.choice, Quot.sound]`
  (verified in a transient `/tmp` axcheck; same closure for `cConst_pos`).
- No `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `axiom` / `#print`.

## Boundary (what this does NOT do — downstream nodes)

- Conditional on the parked `CrossingLemmaMultigraphStatement` (the multigraph crossing lemma;
  unconditional proof is the separate Route-C workstream) — exactly as the line case is
  conditional on `SimpleCrossingLemmaStatement`.
- Works in the `ℝ × ℝ` chart over post-shear irreducible carriers with `hpp`/`hcc` supplied.
  Reaching `Corollary24Statement` (curves in `EuclideanSpace`, arbitrary degree, the
  `TwoDegreesOfFreedom → (hpp,hcc)` bridge with zero-set injectivity, shear application, and the
  `D>2`/`e>1` lift) is the four separate downstream nodes of design §5.3.

PROVEN. No CONJECTURED / EMPIRICALLY-VERIFIED / HEURISTIC content: the constant
`edgeBCrossingConst d M` is an exhibited closed form and the inequality is fully formalized.
With this, all six Edge-B discharges AND the top-level composition are landed; task #43 is
complete (the remaining work to `Corollary24Statement` is the named downstream bridge nodes).
