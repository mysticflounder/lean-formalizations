/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MonotoneArc

/-!
# D2: band + compact strip on each good interval (`D2-band-strip`)

The per-good-interval payload of Edge B's monotone graph decomposition
(`docs/corollary24-assembly-skeleton.md` §1.4–§1.5). On any closed `[xP, xQ]` strictly inside
a good open interval `(α, β)` (one meeting no bad x-value), this file produces **exactly** the
two structural hypotheses LEAF A (`exists_monotoneArc_single_psi`) consumes — the band
`∂_y h ≠ 0` along the curve over `[xP, xQ]`, and a compact `K` containing the curve-strip — and
composes them with LEAF A to give the single-ψ arc over `[xP, xQ]` through a prescribed start
point. There is no new analytic content here: D2a is a contrapositive against `Crit_x ⊆ Bad`,
D2b is a direct application of LEAF B (`isCompact_strip`) with `goodness → lc_y ≠ 0`.

The cut set is `Bad h = Crit_x h ∪ InfRoot_x h` (`DecompositionDefs.lean`), so the two
sub-set memberships `Crit_x ⊆ Bad` and `InfRoot_x ⊆ Bad` are `Or.inl` / `Or.inr`. The compact
`K` is the strip `strip h xP xQ` itself (`StripCompact.lean`): `isCompact_strip` proves it
compact, and `strip` membership is `⟨x ∈ [xP,xQ], on-curve⟩` by definition.

All names live in `PachDeZeeuw.Algebraic`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

/-! ### (D2a) The band: vertical tangents are bad -/

/-- **(D2a) Band.** On any good open interval `(α, β)`, every curve point over it has
`∂_y h ≠ 0`. Definitional given `Crit_x ⊆ Bad`: a band-violation at `p` puts
`p.1 ∈ Crit_x h ⊆ Bad h` (witness `y = p.2`), contradicting goodness. No analysis. -/
theorem decomp_D2a_band
    (h : PlanePoly) {α β : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) :
    ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Ioo α β → partialY h p ≠ 0 := by
  intro p hp hpα hbad0
  have hcrit : p.1 ∈ Crit_x h :=
    ⟨p.2, by simpa [mem_evalPlaneZeroSet] using hp, by simpa using hbad0⟩
  exact (hgood p.1 hpα) (Or.inl hcrit)

/-- **(D2a') Band on a closed sub-interval** `[xP, xQ] ⊆ (α, β)` — the exact form LEAF A's
`hband` wants. -/
theorem decomp_D2a_band_closed
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0 := by
  intro p hp hpIcc
  exact decomp_D2a_band h hgood p hp ⟨lt_of_lt_of_le hP hpIcc.1, lt_of_le_of_lt hpIcc.2 hQ⟩

/-! ### (D2b) The compact strip -/

/-- **(D2b) Compact strip on** `[xP, xQ] ⊆ (α, β)`. From LEAF B (`isCompact_strip`): need
`lc_y(h) ≠ 0` on `[xP, xQ]`. Goodness gives `[xP, xQ] ∩ InfRoot_x = ∅`, i.e. `lc_y(h)(x) ≠ 0`
there (`InfRoot_x ⊆ Bad` via `Or.inr`). -/
theorem decomp_D2b_compact
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    IsCompact (strip h xP xQ) := by
  apply isCompact_strip
  intro x hx hzero
  have hxIoo : x ∈ Set.Ioo α β := ⟨lt_of_lt_of_le hP hx.1, lt_of_le_of_lt hx.2 hQ⟩
  exact (hgood x hxIoo) (Or.inr hzero)

/-- **(D2b') The strip is the compact `K` LEAF A consumes.** LEAF A wants a compact `K` with
`∀ p ∈ γ, p.1 ∈ [xP,xQ] → p ∈ K`; take `K := strip h xP xQ` (D2b: compact), and the membership
is `⟨p.1 ∈ [xP,xQ], on-curve⟩` by `strip`'s definition. -/
theorem decomp_D2_strip_isK
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    IsCompact (strip h xP xQ) ∧
      (∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ strip h xP xQ) := by
  refine ⟨decomp_D2b_compact h hgood hP hQ, ?_⟩
  intro p hp hpIcc
  exact ⟨hpIcc, by simpa [mem_evalPlaneZeroSet] using hp⟩

/-! ### (D2 → LEAF A) The single-ψ arc over a good interval -/

/-- **The single-ψ existence over a closed `[xP, xQ]` strictly inside a good interval**, through
a prescribed curve start point `(xP, yP)`. Composes D2a' + D2_strip_isK + LEAF A
(`exists_monotoneArc_single_psi`). This is the immediate consumer of LEAF A and the per-arc
unit the E1 pairing applies to each consecutive incident pair. (It does not pin `ψ xQ`; that
endpoint residue is the separate `endpoint-pin` obligation, §3.2.) -/
theorem decomp_arc_on_good
    (h : PlanePoly) {α β xP yP xQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hPcurve : evalPlane h (xP, yP) = 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) := by
  obtain ⟨hK, hKsub⟩ := decomp_D2_strip_isK h hgood hP hQ
  exact exists_monotoneArc_single_psi h hxlt hPcurve hK hKsub
    (decomp_D2a_band_closed h hgood hP hQ)

end PachDeZeeuw.Algebraic
