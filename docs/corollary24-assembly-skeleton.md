# Corollary 24 decomposition assembly — Lean-targetable skeleton (D1–D3 + sheet-count + export contract)

Author: math-professor (analysis)
Date: 2026-06-20
Toolchain context: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`.

**Scope.** ONE deliverable: pin the **decomposition assembly** (`docs/corollary24-decomposition-spec.md`
§1.3 D1–D3) as concrete Lean signatures that consume the landed analytic leaves and export
exactly what `exists_monotoneArc_single_psi` needs. Four parts:

1. the D1–D3 statements as Lean signatures (real hypotheses, real conclusions);
2. the `sheet-count` sub-lemma, pinned with a proof skeleton and the exact constancy obligation;
3. the `export-1,2` interface contract and a compatibility check against the per-arc lemma's
   **actual landed signature** (no `ψ xQ`);
4. new sub-lemmas the skeleton surfaces, each as a `FLAG FOR IMPLEMENTER:` spec.

**What this does NOT do.** It does not re-derive `U_∞`, the cut-set bookkeeping, or the E1/E2
algebra — those are settled in the spec (`docs/corollary24-decomposition-spec.md` §2, §3). It does
not re-prove `lc-bound`, `B-crit`, `uinf-containment`, `chart-bridge` — it consumes them at their
spec'd / landed interfaces. It is the **glue layer** between the leaves and the per-arc lemma.

**Verification basis.** Every "landed / PROVEN in-repo" claim cites a declaration whose **exact
signature** I read this session from source: `exists_monotoneArc_single_psi` (`MonotoneArc.lean:1015`),
`isCompact_strip` + `strip` + `yLeadCoeff` (`StripCompact.lean:222,247,71`), `partialY`
(`MonotoneArc.lean:57`), `finite_singularities_of_irreducible_bound` (`Bezout.lean:1085`),
`factor_intersection_bound` (`Bezout.lean:1028`), `partial_factor_not_associated` (`Bezout.lean:999`),
`SingularPointSet` (`Bezout.lean:445`), `PlaneCurveZeroSet` (`AlgebraicPrelim.lean:118`). The
in-flight interfaces (`B-crit-lemma`, `chart-bridge`, `uinf-containment`) I consume at the
signatures the task statement and spec §3.1/§4 give; those are CONSUMED-AS-GIVEN, not verified by me.
One scratch computation (pure-Python, degree ≤ 2 root counts on three concrete curves) supports the
sheet-count constancy *mechanism*; it is EMPIRICALLY VERIFIED with scope = {`y²−(x−1)(x−3)`, `xy−1`}.
I did **not** run `lake build` or any Lean build/execution.

---

## 0. Objects this skeleton uses (all read from source this session)

| Object | Definition / signature | Location |
|---|---|---|
| `PlanePoly` | `MvPolynomial (Fin 2) ℝ` | `AlgebraicPrelim.lean:1516` |
| `evalPlane h : ℝ × ℝ → ℝ` | `xy ↦ eval (i ↦ if i=0 then xy.1 else xy.2) h` | `Bezout.lean:451` |
| `evalPlaneZeroSet h` | `{xy : ℝ × ℝ | evalPlane h xy = 0}` (closed) | `LocalArc.lean:48`, closed at `MonotoneArc.lean:284` |
| `partialY h z` | `eval (i ↦ if i=0 then z.1 else z.2) (pderiv 1 h)` = `∂_y h` on `ℝ×ℝ` | `MonotoneArc.lean:57` |
| `strip h xP xQ` | `{xy | xy.1 ∈ Icc xP xQ ∧ evalPlane h xy = 0}` | `StripCompact.lean:222` |
| `yLeadCoeff h` | `(Curry1 h).leadingCoeff : MvPolynomial (Fin 1) ℝ` = `a_D = lc_y(h)` | `StripCompact.lean:71` |
| `PlaneCurveZeroSet p` | `{x : Point2 | eval (i ↦ x i) p = 0}` (the same curve in `Point2`) | `AlgebraicPrelim.lean:118` |
| `Point2` | `EuclideanSpace ℝ (Fin 2)` (L²) | `AlgebraicPrelim.lean:22` |

The two **landed leaves** this skeleton is built around:

```lean
-- LEAF A (MonotoneArc.lean:1015) — single-ψ per closed x-interval, given band + compact strip.
theorem exists_monotoneArc_single_psi
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP yP xQ : ℝ}
    (hxlt : xP < xQ)
    (hP : evalPlane h (xP, yP) = 0)
    (hK : IsCompact K)
    (hKsub : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ K)
    (hband : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)

-- LEAF B (StripCompact.lean:247) — strip compact when lc_y(h) ≠ 0 throughout [xP,xQ].
theorem PachDeZeeuw.Algebraic.isCompact_strip (h : PlanePoly) {xP xQ : ℝ}
    (hlc : ∀ x ∈ Set.Icc xP xQ, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    IsCompact (strip h xP xQ)
```

These are sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`; see
`docs/corollary24-lcbound-build.md` §2, `docs/corollary24-perArc-clopen-build.md`).

**Naming check.** `Crit_x`, `Inf_x`, `Bad`, `sheet`, `chart-bridge` are **not yet** declared
anywhere in the source (grep this session: only `yLeadCoeff` exists). The names below are proposed,
not colliding.

**The chart gap, restated.** Every finiteness/degree bound (`finite_singularities_of_irreducible_bound`,
`factor_intersection_bound`) lives in `Point2 = EuclideanSpace ℝ (Fin 2)`; the per-arc/strip machinery
lives in `ℝ × ℝ`. The `chart-bridge` FLAG (`E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`, `x ↦ (x 0, x 1)`)
moves a `Point2`-finiteness fact to an `ℝ×ℝ`-fact. **D1 below is stated `Point2`-side for the
finiteness import, then projected to `ℝ`-valued x-sets via `E` + first coordinate.** This is the one
place the skeleton must thread `E`; I mark every such crossing explicitly with `[via chart-bridge]`.

---

## 1. The D1–D3 statements (Lean signatures)

Fix throughout: `h : PlanePoly`, `(hirr : Irreducible h)`, `(hdeg : h.totalDegree ≤ d)`,
`(hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0)` — the last is the generic-rotation output
(`∂_y h ≢ 0`, i.e. `h` is not a union of vertical lines), secured upstream by `generic-rotation`.

### 1.1 The cut-set definitions (`ℝ`-valued x-sets)

```lean
/-- Critical x-values: x-projections of curve points with a vertical tangent
(`∂_y h = 0`). Singular points (`∂_x h = ∂_y h = 0`) are a fortiori here. -/
def Crit_x (h : PlanePoly) : Set ℝ :=
  {x : ℝ | ∃ y : ℝ, evalPlane h (x, y) = 0 ∧ partialY h (x, y) = 0}

/-- Infinity-cut x-values, in the Lean-tractable polynomial-root form: zeros in `x` of
the leading-in-`y` coefficient `a_D = lc_y(h)`. (The topological-asymptote set `Inf_x`
is CONTAINED in this — that containment is the `uinf-containment` FLAG.) -/
def InfRoot_x (h : PlanePoly) : Set ℝ :=
  {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) = 0}

/-- The total bad x-set. -/
def Bad (h : PlanePoly) : Set ℝ := Crit_x h ∪ InfRoot_x h
```

Design note. The spec defines `Inf_x` topologically (an asymptote set) and proves
`Inf_x ⊆ {lc_y = 0}` (`uinf-containment`). For the **decomposition we only ever need the
right-hand side** `InfRoot_x = {lc_y = 0}`: it is what makes the strip compact (LEAF B's hypothesis
is literally `lc_y(h) ≠ 0` on `[xP,xQ]`), and it is finite by univariate degree. The topological
`Inf_x` is needed only to *justify* that cutting at `InfRoot_x` removes all asymptotes (so that the
returned `ψ` is genuinely the full-width sheet, not a truncation). So:

- **`Bad := Crit_x ∪ InfRoot_x` is the operative cut-set** (uses only `partialY`, `yLeadCoeff`);
- `uinf-containment` (`Inf_x ⊆ InfRoot_x`) is a *correctness* lemma feeding D3's "no escape," **not**
  a definitional input to D1/D2.

This is a slight reorganization of the spec's `Bad = Crit_x ∪ Inf_x`: I make the *operative* set the
polynomial-root one and demote the topological set to a downstream justification. **This shrinks the
D1 obligation**: D1 finiteness of `InfRoot_x` is `Polynomial`-trivial, with no topology.

### 1.2 D1 — finiteness of the cut-set

```lean
/-- (D1) The bad x-set is finite. -/
theorem decomp_D1_bad_finite
    (h : PlanePoly) (hirr : Irreducible h) (hdeg : h.totalDegree ≤ d)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).Finite := by
  -- Bad = Crit_x ∪ InfRoot_x; a union of two finite sets is finite.
  exact (decomp_D1_crit_finite h hirr hdeg hpy).union (decomp_D1_infroot_finite h hpy)

/-- (D1a) `InfRoot_x` finite — PROVEN-trivial: zeros of a nonzero univariate polynomial. -/
theorem decomp_D1_infroot_finite (h : PlanePoly) (hpy : MvPolynomial.pderiv (1:Fin 2) h ≠ 0) :
    (InfRoot_x h).Finite := by
  -- `x ↦ eval x (yLeadCoeff h)` = `Polynomial.eval x (XCoeffEquiv (yLeadCoeff h))` (StripCompact's
  -- continuous_evalCoeff route, def-eq), and `yLeadCoeff h ≠ 0` since `pderiv 1 h ≠ 0 ⟹ h` has
  -- positive y-degree ⟹ leadingCoeff in y is nonzero. Then `Polynomial.setOf_isRoot_finite`.
  sorry  -- FLAG: infroot-finite (§4); the nonvanishing of yLeadCoeff is the only content.

/-- (D1b) `Crit_x` finite — via B-crit + chart-bridge first-coord projection. -/
theorem decomp_D1_crit_finite
    (h : PlanePoly) (hirr : Irreducible h) (hdeg : h.totalDegree ≤ d)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Crit_x h).Finite := by
  -- B-crit (FLAG, §4) gives  Z := PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h)  Finite
  -- (Point2-side, ncard ≤ (d+1)^5). chart-bridge transports Z.Finite to ℝ×ℝ, and Crit_x is the
  -- image of (E '' Z) under Prod.fst, so Crit_x = Prod.fst '' (E '' Z) is finite (image of finite).
  sorry  -- FLAG: crit-finite-projection (§4) — pure plumbing once B-crit + chart-bridge land.
```

**Finiteness is the only thing D1 needs for the assembly.** The ncard bound `≤ c_x(d) = (d+1)^5 + d`
is needed for the *edge-loss constant* in E1, not for the decomposition's structure — I carry it as a
**separate, optional** strengthening (`decomp_D1_bad_ncard`, FLAG §4) so the structural assembly
(D2/D3) does not block on the arithmetic. (PROVEN-modulo: the bound is `B-crit`'s `(d+1)^5` +
`InfRoot`'s `deg ≤ d`, both already bounded at their leaves.)

### 1.3 The good-interval predicate, and the open-cover decomposition

```lean
/-- `(α,β)` is a good open interval for `h`: it meets no bad x-value. -/
def IsGoodInterval (h : PlanePoly) (α β : ℝ) : Prop :=
  α < β ∧ ∀ x ∈ Set.Ioo α β, x ∉ Bad h

/-- The good locus: all x off the (finite) bad set. -/
def GoodLocus (h : PlanePoly) : Set ℝ := (Bad h)ᶜ
```

**Structural fact (the partition).** Since `Bad h` is finite, `GoodLocus h = ℝ ∖ Bad h` is open and is
a **finite disjoint union of open intervals** (the connected components of the complement of a finite
set in `ℝ`). This is the "complement is a finite union of open intervals" claim of the spec's D1.

```lean
/-- (D1c) The good locus is a finite disjoint union of open intervals. The components are open,
pairwise disjoint, and finite in number (`≤ |Bad h| + 1`). -/
theorem decomp_D1_goodLocus_components
    (h : PlanePoly) (hirr : Irreducible h) (hdeg : h.totalDegree ≤ d)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → Set ℝ),
      (∀ j, ∃ a b : EReal, I j = {x : ℝ | (a : EReal) < x ∧ (x : EReal) < b}) ∧
      (Pairwise (Function.onFun Disjoint I)) ∧
      GoodLocus h = ⋃ j, I j := by
  sorry  -- FLAG: goodlocus-components (§4). This is "finite set ⟹ complement = finite ⋃ of open
         -- intervals" — a generic real-line fact, not curve-specific. EReal endpoints absorb ±∞.
```

I use `EReal` endpoints so the two unbounded components `(−∞, min Bad)` and `(max Bad, +∞)` are
expressible uniformly. **This is a generic statement about finite subsets of `ℝ`** and is the
cleanest place to keep the decomposition curve-agnostic. (The implementer may prefer to keep the
components implicit and work directly with "any `Ioo α β` disjoint from `Bad`"; D2/D3 below are
stated that way so they do not depend on the exact packaging of `decomp_D1_goodLocus_components`.)

### 1.4 D2 — band + compact strip on each good interval

This is the payload: it produces **exactly** LEAF A's two structural hypotheses (`hband`, and
`hK ∧ hKsub`) for any closed `[xP,xQ]` strictly inside a good interval.

```lean
/-- (D2a) Band. On any good open interval, every curve point over it has `∂_y h ≠ 0`.
This is DEFINITIONAL given `Crit_x ⊆ Bad`: a band-violation at `p` puts `p.1 ∈ Crit_x ⊆ Bad`,
contradicting goodness. No analysis. -/
theorem decomp_D2a_band
    (h : PlanePoly) {α β : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) :
    ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Ioo α β → partialY h p ≠ 0 := by
  intro p hp hpα hbad0
  -- p on curve, partialY h p = 0  ⟹  p.1 ∈ Crit_x h  (witness y = p.2)
  have hcrit : p.1 ∈ Crit_x h :=
    ⟨p.2, by simpa [mem_evalPlaneZeroSet] using hp, by simpa using hbad0⟩
  exact (hgood p.1 hpα) (Or.inl hcrit)   -- Crit_x ⊆ Bad := Or.inl, contradiction with goodness

/-- (D2a') Band, on a CLOSED sub-interval `[xP,xQ] ⊆ (α,β)` — the form LEAF A's `hband` wants. -/
theorem decomp_D2a_band_closed
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0 := by
  intro p hp hpIcc
  exact decomp_D2a_band h hgood p hp ⟨lt_of_lt_of_le hP hpIcc.1, lt_of_le_of_lt hpIcc.2 hQ⟩

/-- (D2b) Compact strip on `[xP,xQ] ⊆ (α,β)`. From LEAF B (`isCompact_strip`): need `lc_y(h) ≠ 0`
on `[xP,xQ]`. Goodness gives `[xP,xQ] ∩ InfRoot_x = ∅`, i.e. `lc_y(h)(x) ≠ 0` there. -/
theorem decomp_D2b_compact
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    IsCompact (PachDeZeeuw.Algebraic.strip h xP xQ) := by
  apply PachDeZeeuw.Algebraic.isCompact_strip
  intro x hx
  -- x ∈ [xP,xQ] ⊆ (α,β); if lc_y(h)(x) = 0 then x ∈ InfRoot_x ⊆ Bad, contradicting goodness.
  have hxIoo : x ∈ Set.Ioo α β := ⟨lt_of_lt_of_le hP hx.1, lt_of_le_of_lt hx.2 hQ⟩
  intro hzero
  exact (hgood x hxIoo) (Or.inr hzero)   -- InfRoot_x ⊆ Bad := Or.inr
```

**`hK ∧ hKsub` for LEAF A is now immediate from D2b.** LEAF A wants a compact `K` containing the
strip; take `K := strip h xP xQ` itself (D2b says it's compact), and `hKsub p hp hpIcc : p ∈ K` is
`⟨hpIcc, hp⟩` by `strip`'s definition. So D2b *is* the `(hK, hKsub)` package:

```lean
/-- (D2b') The strip itself is the compact `K` LEAF A consumes. -/
theorem decomp_D2_strip_isK
    (h : PlanePoly) {α β xP xQ : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) :
    IsCompact (PachDeZeeuw.Algebraic.strip h xP xQ) ∧
      (∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ PachDeZeeuw.Algebraic.strip h xP xQ) := by
  refine ⟨decomp_D2b_compact h hgood hP hQ, ?_⟩
  intro p hp hpIcc
  exact ⟨hpIcc, by simpa [mem_evalPlaneZeroSet] using hp⟩  -- strip membership = ⟨Icc, on-curve⟩
```

**D2 is PROVEN-modulo its two leaves, with the glue fully written above.** D2a is a 2-line
contrapositive (no FLAG). D2b is a direct application of LEAF B (landed) with the goodness→`lc_y≠0`
step written. The only inputs are the two landed leaves plus the `Or.inl/Or.inr` for `Crit_x,
InfRoot_x ⊆ Bad`.

### 1.5 D2 → LEAF A: the single-arc existence on a good interval

Composing D2a' + D2_strip_isK + LEAF A:

```lean
/-- The full single-ψ existence over any closed `[xP,xQ]` strictly inside a good interval,
through any prescribed start point `(xP,yP)` on the curve. This is the immediate consumer
of LEAF A and the unit the E1 pairing applies per consecutive incident pair. -/
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
```

**Status: PROVEN-modulo {LEAF A landed, LEAF B landed, `Crit_x`/`InfRoot_x` defs}.** Every Lean step
in §1.4–§1.5 is written above and uses only landed declarations. There is **no** new analytic content
in D2/the arc-on-good lemma — it is the contrapositive band + a direct LEAF-B application. This is the
load-bearing simplification this skeleton contributes: **once `Crit_x`/`InfRoot_x` are the cut-set,
D2 is glue, not a theorem.**

---

## 2. The `sheet-count` sub-lemma (D3), pinned

D3 says: over a good interval, the strip is a disjoint union of `≤ deg_y h` continuous full-width
graphs (sheets), constant in number. I split this into a **fibre-cardinality bound** (clean, mathlib)
and a **constancy** claim (the genuine obligation), and I am explicit about where the gap is.

### 2.1 Fibre cardinality (PROVEN-shaped, mathlib)

```lean
/-- The x-fibre of the curve. -/
def Fibre (h : PlanePoly) (x : ℝ) : Set ℝ := {y : ℝ | evalPlane h (x, y) = 0}

/-- (D3a) Over a good x-value the fibre is finite with `≤ deg_y h` points.
The fibre = real roots of the slice `Specialized1 x h` (`eval_specialized1`), which over a good x
has `natDegree = D = (Curry1 h).natDegree` and is nonzero (`specialized1_natDegree_and_ne_zero`,
since `lc_y(h)(x) ≠ 0` off `InfRoot_x`). A nonzero univariate poly has `≤ natDegree` roots. -/
theorem decomp_D3a_fibre_card_le
    (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    (Fibre h x).Finite ∧ (Fibre h x).ncard ≤ (PachDeZeeuw.Algebraic.Curry1 h).natDegree := by
  -- lc_y(h)(x) ≠ 0 from x ∉ InfRoot_x ⊆ Bad; slice nonzero of natDegree D; roots ≤ D.
  -- Fibre h x = {y | Polynomial.IsRoot (Specialized1 x h) y} via eval_specialized1.
  -- mathlib: Polynomial.setOf_isRoot_finite, Polynomial.card_roots_le_degree (or
  -- Polynomial.card_roots'/Finset.card_le of (Specialized1 x h).roots.toFinset).
  sorry  -- FLAG: fibre-card (§4) — routine, all bricks present + StripCompact helpers reused.
```

This uses `Specialized1` / `Curry1` / `specialized1_natDegree_and_ne_zero` **already built in
StripCompact.lean** — it is a reuse, not a new construction. The degree bound `(Curry1 h).natDegree ≤
totalDegree h ≤ d` gives `s(d) ≤ d`. **Status: PROVEN-shaped** (every brick is in-repo or mathlib).

### 2.2 Constancy of the fibre count (THE genuine D3 obligation)

This is where I am most careful. The claim "the number of sheets is constant over a good interval" is
**not** delivered by any single landed lemma. Here is the exact obligation and a proof skeleton, with
the gap flagged.

**Claim (constancy).** For `(α,β)` good and `x₁, x₂ ∈ (α,β)`,
`(Fibre h x₁).ncard = (Fibre h x₂).ncard`.

**Proof skeleton.**

1. **Local constancy via the per-arc IFT.** Fix `x₀ ∈ (α,β)`. Each `y₀ ∈ Fibre h x₀` has
   `partialY h (x₀,y₀) ≠ 0` (D2a band). The implicit-function machinery already in
   `MonotoneArc.lean` (`exists_implicitBox_of_partialY` and the `eventually_apply_eq_iff_implicitFunction`
   bridge it consumes) gives a neighborhood `U ∋ x₀` and a **continuous** `ψ_{y₀} : U → ℝ` with
   `ψ_{y₀}(x₀) = y₀`, `evalPlane h (x, ψ_{y₀}(x)) = 0`, and — crucially — **local uniqueness**: near
   `(x₀,y₀)` the only curve point over `x` is `(x, ψ_{y₀}(x))`. So each root continues to exactly one
   nearby root, giving an injection `Fibre h x₀ ↪ Fibre h x` for `x` near `x₀` (count is **lower
   semicontinuous**: `(Fibre h x).ncard ≥ (Fibre h x₀).ncard`).

2. **No new sheets appear (upper semicontinuity).** Conversely, suppose along `x_n → x₀` there were
   strictly more roots than at `x₀`. The extra roots `y_n` either (a) stay bounded, or (b) escape to
   `±∞`. Case (b) is excluded by **LEAF B / `lc-bound`**: over a closed `[x₀−ε, x₀+ε] ⊆ (α,β)` the
   strip is compact, so all roots stay in a fixed compact box — no escape. Case (a): a bounded
   sequence `(x_n, y_n)` of curve points has a convergent subsequence `→ (x₀, y*)` (compact strip),
   `y* ∈ Fibre h x₀` by closedness, and by step 1's local uniqueness `y_n = ψ_{y*}(x_n)` eventually —
   so it was **not** an extra root. Hence `(Fibre h x).ncard ≤ (Fibre h x₀).ncard` near `x₀` (**upper
   semicontinuity**).

3. **Constant on the connected `(α,β)`.** Steps 1–2 make `x ↦ (Fibre h x).ncard` **locally constant**
   on `(α,β)`; a locally constant ℕ-valued function on the connected set `(α,β)` is constant
   (`IsLocallyConstant` → constant on `IsPreconnected`).

**Where the gap is — exactly.** Step 1 (lower semicontinuity) is a direct consequence of the IFT
machinery already in `MonotoneArc.lean`, but it is **packaged inside the `ψ`-assembly**, not exposed as
a reusable "root continues to a unique nearby root" lemma. Extracting it is the main new work. Step 2's
case (b) is LEAF B (landed). Step 2's case (a) compactness-subsequence and the local-uniqueness
"it was not extra" is again the IFT uniqueness. Step 3 is mathlib (`IsLocallyConstant.iff_continuous`
/ `IsPreconnected`). **So the genuine new obligation is: expose, from the existing IFT box, a
`local injection of fibres` lemma in BOTH directions (a root continues uniquely; no extra root
appears).** I flag this precisely:

```lean
/-- (D3b-local) The hinge for constancy: near a good `x₀`, the fibre map is locally bijective.
There is `U ∈ 𝓝 x₀`, `U ⊆ (α,β)`, and for each `x ∈ U` a bijection `Fibre h x ≃ Fibre h x₀`
realized by the per-point implicit functions. (Equivalently: `(Fibre h ·).ncard` is locally
constant at every good `x₀`.) -/
theorem decomp_D3b_locally_constant
    (h : PlanePoly) {α β : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) :
    ∀ x₀ ∈ Set.Ioo α β, ∀ᶠ x in nhds x₀, (Fibre h x).ncard = (Fibre h x₀).ncard := by
  sorry  -- FLAG: fibre-local-constant (§4) — THE genuine D3 obligation. Inputs: MonotoneArc IFT
         -- box (local existence+uniqueness, both directions) + isCompact_strip (no escape).

/-- (D3b) Constancy on the good interval — `IsPreconnected.Ioo` + local constancy. -/
theorem decomp_D3b_fibre_card_const
    (h : PlanePoly) {α β : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo α β) (h₂ : x₂ ∈ Set.Ioo α β) :
    (Fibre h x₁).ncard = (Fibre h x₂).ncard := by
  -- locally-constant ℕ-valued on connected Ioo ⟹ constant.
  sorry  -- FLAG: fibre-card-const (§4) — pure topology once decomp_D3b_locally_constant lands.
```

**Constancy classification: CONJECTURED-constructible, with a complete proof skeleton.** The
mechanism is EMPIRICALLY VERIFIED (scratch, §below). The two ends of the local bijection are exactly
the two landed leaves' content (IFT uniqueness from MonotoneArc; no-escape from StripCompact); the
*extraction* of a reusable two-sided local-injection lemma is genuine new Lean work but routes
entirely through existing machinery — **no new analysis**.

**Scratch confirmation of the mechanism (EMPIRICALLY VERIFIED; scope = two curves, degree ≤ 2).**
For `h = y²−(x−1)(x−3)`: real-root count is constantly `0` on the good interval `(1,3)` and constantly
`2` on `(3,∞)`; it drops to `1` (a double root, `partialY = 2y = 0`) exactly at the critical endpoints
`x ∈ {1,3}`, which are excluded from every good interval. For `h = xy−1`: count is constantly `1` on
each of `(−∞,0)`, `(0,∞)`; the break at `x=0` is the `InfRoot_x` point (`lc_y = x = 0`). This is
consistent with constancy on good intervals and a count change only at `Bad` x-values. It does **not**
prove constancy — it confirms the claimed mechanism on two instances.

### 2.3 D3, assembled

```lean
/-- (D3) Sheet count over a good interval: the fibre is finite, `≤ deg_y h ≤ d`, and CONSTANT in x.
The sheets are the `s_{αβ} := (Fibre h x₀).ncard` continuous full-width graphs the per-arc lemma's
ψ traces; distinct sheets do not meet (D2a: `∂_y ≠ 0` ⟹ roots simple ⟹ graphs disjoint). -/
theorem decomp_D3_sheets
    (h : PlanePoly) (hirr : Irreducible h) (hdeg : h.totalDegree ≤ d)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0)
    {α β : ℝ} (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : α < β) :
    ∃ s : ℕ, s ≤ d ∧ ∀ x ∈ Set.Ioo α β, (Fibre h x).Finite ∧ (Fibre h x).ncard = s := by
  -- s := (Fibre h x_mid).ncard for any x_mid ∈ (α,β); ≤ (Curry1 h).natDegree ≤ totalDegree ≤ d
  -- (D3a); constant by D3b. Existence of x_mid from α < β (e.g. (α+β)/2 when both finite; for
  -- unbounded ends pick any interior point).
  sorry  -- assembles decomp_D3a_fibre_card_le + decomp_D3b_fibre_card_const + degree-le-totalDegree.
```

Note `(Fibre h x).ncard = s` already gives the *count*; the **sheets-as-graphs** structure (a family
`ψ_j : (α,β) → ℝ` whose graphs partition the strip) is a *re-expression* of D3 via global IFT
continuation and is **not needed by E1/E2** — E1 applies LEAF A per consecutive incident pair on a
closed sub-interval, which re-derives the relevant `ψ` locally. **I therefore do not stand up a
`Sheet` family object** (it would be a wrapper that moves the obligation without shrinking it; the
project rule forbids that). D3's deliverable is the **constant count** `s ≤ d`, which is the number
that enters the edge-loss bound. If a downstream consumer genuinely needs the explicit sheet maps, that
is a separate FLAG (`sheet-maps`, §4) marked LOW priority — but I assess it as **not** on the critical
path for E1/E2.

---

## 3. The export-1,2 interface contract, and compatibility with LEAF A's landed signature

### 3.1 What the decomposition exports (spec §3.1, made concrete against the landed leaf)

```lean
/-- export-1 (cut finiteness) = D1. -/
theorem export_1_bad_finite
    (h : PlanePoly) (hirr : Irreducible h) (hdeg : h.totalDegree ≤ d)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).Finite :=
  decomp_D1_bad_finite h hirr hdeg hpy

/-- export-2 (good-interval band + compact, in EXACTLY LEAF A's hypothesis shape).
For any closed [xP,xQ] strictly inside a good interval, this hands back the precise
`hband` and `(hK, hKsub)` that `exists_monotoneArc_single_psi` consumes. -/
theorem export_2_band_compact
    (h : PlanePoly) {α β xP xQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hP : α < xP) (hQ : xQ < β) :
    (∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0) ∧
    (∃ K : Set (ℝ × ℝ), IsCompact K ∧
        ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ K) := by
  refine ⟨decomp_D2a_band_closed h hgood hP hQ, ?_⟩
  obtain ⟨hK, hKsub⟩ := decomp_D2_strip_isK h hgood hP hQ
  exact ⟨PachDeZeeuw.Algebraic.strip h xP xQ, hK, hKsub⟩
```

`export_2_band_compact` is **fully written** above (no `sorry`): it is the conjunction of the two
written D2 glue lemmas. Both conjuncts are byte-for-byte the shapes in LEAF A's signature
(`hKsub`/`hband` are copied from `MonotoneArc.lean:1020–1021`). So:

> **export-1,2 are PROVEN-modulo {LEAF A, LEAF B landed; `B-crit`, `chart-bridge`, `infroot-finite`
> for D1's finiteness}.** export-2's band+compact half is **fully discharged** (no further FLAG)
> from the two landed leaves; export-1's finiteness is the only part still routing through in-flight
> FLAGs.

### 3.2 Compatibility check: LEAF A's missing `ψ xQ` vs what the export needs — **the gap, stated**

LEAF A delivers `ψ xP = yP` but **not** `ψ xQ = yQ` (read at `MonotoneArc.lean:1013–1014` and
confirmed in the docstring; the returned `ψ` is the sheet reachable rightward from `(xP,yP)`).

**Is this compatible with export-1,2?** Yes — **export-1,2 themselves do not need `ψ xQ`.** They
deliver the *hypotheses* (`hband`, `hK`, `hKsub`) of LEAF A; the *output* `ψ` and its endpoint
behavior is consumed by **E1**, not by export-1,2. So there is **no gap in the export-1,2 contract**
from the missing `ψ xQ`.

**Where the missing `ψ xQ` does bite: E1, and `export-3` covers it.** E1 needs, per consecutive
incident pair `(p_i, p_{i+1})` on the **same sheet** in the **same good interval**, an arc from `p_i`
to `p_{i+1}` — i.e. it needs `ψ(p_{i+1}.1) = p_{i+1}.2` (the right endpoint pinned). LEAF A gives only
the start. The spec (§3.2 E1, and §3.1 `export-3`) closes this with a **same-component hypothesis**:
both endpoints lie on one sheet over one good interval, so the rightward-continued `ψ` from `p_i`
*does* arrive at `p_{i+1}`. **The exact obligation that fills the `ψ xQ` gap is:**

```lean
/-- export-3-endpoint (the ψ xQ filler). If (xP,yP) and (xQ,yQ) lie on the SAME sheet over a good
interval (same connected component of the strip over [xP,xQ]), then the LEAF-A ψ through (xP,yP)
satisfies ψ xQ = yQ. -/
theorem export_3_endpoint_pin
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hPc : evalPlane h (xP, yP) = 0) (hQc : evalPlane h (xQ, yQ) = 0)
    (hsame : SameSheet h xP yP xQ yQ)   -- (xP,yP),(xQ,yQ) in one connected component of the strip
    {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
          ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) :
    ψ xQ = yQ := by
  sorry  -- FLAG: endpoint-pin (§4). Both ψ-graph and the (xP,yP)→(xQ,yQ) sheet are continuous
         -- single-valued selections of the curve over [xP,xQ] (D2a: ∂_y≠0 ⟹ at most one y per x in
         -- a connected piece); they agree at xP, hence everywhere (uniqueness of continuation on a
         -- band-good strip). `SameSheet` is the connectedness hypothesis export-3 supplies.
```

**This `endpoint-pin` lemma is the precise residue of the missing `ψ xQ`.** It is NOT in LEAF A; it is
a new FLAG. Its content is *uniqueness of the band-good continuation* (two continuous curve-selections
over `[xP,xQ]` agreeing at one point agree everywhere, because over a band-good strip each x has at
most one y *on a given sheet* — `partialY ≠ 0` ⟹ local single-valuedness, then connectedness). This is
the same uniqueness already used inside LEAF A's construction; like `fibre-local-constant` it must be
**exposed** as a standalone lemma. The `SameSheet` predicate is the connectedness datum `export-3`
must produce from the incident-point ordering (spec §3.1 export-3); defining `SameSheet` as "in one
connected component of `strip h xP xQ`" is the natural choice and makes `endpoint-pin` provable by
component-uniqueness.

**Verdict on §3 compatibility.**
- export-1,2 ↔ LEAF A: **fully compatible, no gap.** export-2's band+compact is the exact LEAF-A
  hypotheses and is fully written here.
- The missing `ψ xQ`: **does not affect export-1,2**; it is isolated into one new lemma
  `export_3_endpoint_pin` (FLAG `endpoint-pin`) that E1 consumes. The gap is **named and bounded**,
  and its content is the same continuation-uniqueness LEAF A already uses internally.

---

## 4. New sub-lemmas this skeleton surfaces (FLAGs)

Beyond the spec's known leaves (`lc-bound` LANDED, `B-crit-lemma`/`chart-bridge`/`uinf-containment`
in-flight, `generic-rotation`), the assembly surfaces these. Each is a Lean-targetable statement.

```
FLAG FOR IMPLEMENTER: infroot-finite        [tiny, no analysis]
  Lemma decomp_D1_infroot_finite: for `pderiv 1 h ≠ 0`, (InfRoot_x h).Finite.
  Content: (i) yLeadCoeff h ≠ 0 (h has positive y-degree since pderiv 1 h ≠ 0); (ii)
  x ↦ eval x (yLeadCoeff h) is a univariate polynomial (XCoeffEquiv, def-eq, already in
  StripCompact's continuous_evalCoeff); (iii) Polynomial.setOf_isRoot_finite. ncard ≤ deg ≤ d.
  Risk: LOW. The only real step is (i): pderiv 1 h ≠ 0 ⟹ (Curry1 h).leadingCoeff ≠ 0.

FLAG FOR IMPLEMENTER: crit-finite-projection   [plumbing; depends on B-crit + chart-bridge]
  Lemma decomp_D1_crit_finite: (Crit_x h).Finite.
  Content: B-crit gives Z := PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h) finite (Point2).
  chart-bridge E moves Z.Finite to ℝ×ℝ. Crit_x h = Prod.fst '' (E '' Z) (a point of Crit_x is the
  first coord of a Z-point: evalPlane h (x,y)=0 ∧ partialY h (x,y)=0 ⟺ (x,y) ∈ E''Z). Image of a
  finite set under Prod.fst is finite. Risk: LOW once B-crit + chart-bridge land. Must verify the
  set equality Crit_x = fst '' (E '' Z) carefully (the ⊇ uses chart-bridge's eval-intertwining,
  the ⊆ uses it backwards).

FLAG FOR IMPLEMENTER: goodlocus-components     [LANDED — GoodLocusComponents.lean, axiom-clean]
  Lemma decomp_D1_goodLocus_components: for finite S ⊆ ℝ, Sᶜ is a finite disjoint union of open
  intervals (EReal endpoints). DONE: generic `finite_compl_eq_iUnion_Ioo` (curve-agnostic) +
  specialization to S = Bad h. Component count = exactly |S|+1 (Fin (|S|+1) index). The
  specialization takes `(Bad h).Finite` as a hypothesis (NOT re-derived from hirr/hdeg/hpy),
  discharged downstream by decomp_D1_bad_finite. See docs/corollary24-goodlocus-build.md.

FLAG FOR IMPLEMENTER: fibre-card              [routine; reuses StripCompact internals]
  Lemma decomp_D3a_fibre_card_le: for x ∉ Bad h, (Fibre h x).Finite ∧ ncard ≤ (Curry1 h).natDegree.
  Content: Fibre h x = roots of Specialized1 x h (eval_specialized1); slice nonzero of natDegree D
  off InfRoot_x (specialized1_natDegree_and_ne_zero); Polynomial.card_roots_le_degree /
  setOf_isRoot_finite. Risk: LOW. All bricks present; StripCompact helpers reused verbatim.

FLAG FOR IMPLEMENTER: fibre-local-constant    [THE genuine D3 obligation]
  Lemma decomp_D3b_locally_constant: over a good interval, (Fibre h ·).ncard is locally constant.
  Content: expose, from MonotoneArc.lean's IFT box (exists_implicitBox_of_partialY + the
  eventually_apply_eq_iff_implicitFunction uniqueness), a TWO-SIDED local fibre bijection:
    (lower s.c.) each y₀ ∈ Fibre h x₀ continues to a unique nearby root  ⟹ ncard ≥;
    (upper s.c.) no extra root appears, using isCompact_strip (LANDED) to forbid escape and the
                 same IFT uniqueness to identify limits of bounded extra roots with x₀-roots ⟹ ncard ≤.
  Inputs: BOTH landed leaves' content (IFT uniqueness from MonotoneArc; no-escape from StripCompact).
  Risk: MED. No new ANALYSIS — the analysis is in the two leaves — but extracting a reusable
  local-bijection lemma from the assembly-internal IFT box is the main new work of the whole
  decomposition after lc-bound. This is the single hardest item in THIS skeleton.

FLAG FOR IMPLEMENTER: fibre-card-const        [pure topology; depends on fibre-local-constant]
  Lemma decomp_D3b_fibre_card_const: locally-constant ℕ-valued on connected Ioo ⟹ constant.
  mathlib: IsLocallyConstant + IsPreconnected.Ioo / IsPreconnected.constant. Risk: LOW.

FLAG FOR IMPLEMENTER: endpoint-pin            [the ψ xQ residue; same uniqueness as fibre-local-constant]
  Lemma export_3_endpoint_pin: on a good interval, if (xP,yP),(xQ,yQ) are SameSheet (one connected
  component of strip h xP xQ), then LEAF A's ψ through (xP,yP) has ψ xQ = yQ.
  Content: two continuous curve-selections over [xP,xQ] agreeing at xP agree at xQ, because on a
  band-good strip (∂_y≠0) a connected sheet is single-valued in x. Needs a `SameSheet` predicate
  := "(xP,yP) and (xQ,yQ) in one connected component of strip h xP xQ", and continuation-uniqueness
  (the SAME uniqueness inside LEAF A; share the extraction with fibre-local-constant). This is the
  precise filler for LEAF A's dropped ψ xQ. Risk: MED. Required for E1 (not for export-1,2).

FLAG FOR IMPLEMENTER: bad-ncard               [optional arithmetic; for E1's constant only]
  Lemma decomp_D1_bad_ncard: (Bad h).ncard ≤ (d+1)^5 + d.
  = B-crit's (d+1)^5 (via ncard ≤ for projection) + InfRoot's deg ≤ d, plus ncard_union_le.
  Risk: LOW. NOT needed for D2/D3 structure; only for the E1 edge-loss constant. Decouple.

FLAG FOR IMPLEMENTER: sheet-maps              [LOW priority; assessed OFF critical path]
  Optional: a family ψ_j : (α,β) → ℝ whose graphs partition the strip (global IFT continuation).
  NOT needed by E1/E2 (E1 re-derives ψ per consecutive pair via LEAF A). Stand up ONLY if a
  downstream consumer demands explicit sheet maps. Do not build pre-emptively (wrapper risk).
```

---

## 5. Classification table: PROVEN-modulo vs CONJECTURED vs needs-new-work

| Item | Statement | Status | Depends on |
|---|---|---|---|
| LEAF A | `exists_monotoneArc_single_psi` | **PROVEN (landed)** | — (MonotoneArc.lean:1015, axiom-clean) |
| LEAF B | `isCompact_strip` | **PROVEN (landed)** | — (StripCompact.lean:247, axiom-clean) |
| D2a band (open) | `decomp_D2a_band` | **PROVEN (landed)** | `Crit_x` def only — contrapositive (DecompositionD2.lean, axiom-clean) |
| D2a band (closed) | `decomp_D2a_band_closed` | **PROVEN (landed)** | D2a (DecompositionD2.lean) |
| D2b compact | `decomp_D2b_compact` | **PROVEN (landed)** | LEAF B + `InfRoot_x ⊆ Bad` (DecompositionD2.lean) |
| D2 strip-is-K | `decomp_D2_strip_isK` | **PROVEN (landed)** | D2b + `strip` def (DecompositionD2.lean) |
| arc-on-good | `decomp_arc_on_good` | **PROVEN (landed)** | LEAF A + LEAF B + D2 (DecompositionD2.lean, axiom-clean) |
| export-2 | `export_2_band_compact` | **PROVEN-modulo (glue written)** | D2a' + D2_strip_isK |
| D3a fibre card | `fibre_card` | **PROVEN (landed)** | mathlib roots + StripCompact internals (SheetCount.lean, axiom-clean) |
| D3b local constancy | `fibre_localConstant` | **PROVEN (landed), unconditional** | pinch of `fibre_ncard_le_eventually` (lower sc) + `fibre_ncard_ge_eventually` (upper sc), over `isCompact_strip` carrier — the genuine D3 content (SheetCount.lean, axiom-clean) |
| D3b constancy | `fibre_card_const` / `fibre_ncard_constant` | **PROVEN (landed)** | `fibre-local-constant` + `IsLocallyConstant.apply_eq_of_preconnectedSpace` (SheetCount.lean) |
| D3 sheets | `decomp_D3_sheet_count` | **PROVEN (landed)** | D3a + D3b: ∃ s ≤ `(Curry1 h).natDegree`, ∀ x ∈ Ioo, fibre finite ∧ ncard = s (SheetCount.lean, axiom-clean) |
| D1a InfRoot finite | `decomp_D1_infroot_finite` | **PROVEN (landed)** | `finite_yLeadCoeff_zeroSet` unfolded (DecompositionD1.lean, axiom-clean); takes `yLeadCoeff h ≠ 0` |
| D1b Crit finite | `decomp_D1_crit_finite` | **PROVEN (landed)** | B-crit `finite_critX_of_irreducible_bound` transported via chart-bridge `critX_eq_image_critPointSet` (DecompositionD1.lean, axiom-clean) |
| D1 Bad finite | `decomp_D1_bad_finite` | **PROVEN (landed)** | D1a ∪ D1b; `yLeadCoeff ≠ 0` derived from `∂_y h ≠ 0` via `yLeadCoeff_ne_zero_of_partialY_ne_zero` — needs only B-crit hyps |
| D1c components | `decomp_D1_goodLocus_components` | **PROVEN (landed)** | generic `finite_compl_eq_iUnion_Ioo` (GoodLocusComponents.lean, axiom-clean); takes `(Bad h).Finite` as hyp |
| export-1 | `export_1_bad_finite` | = D1 | as D1 |
| endpoint-pin (ψ xQ filler) | `endpoint_pin_of_connectingGraph` | **PARTIAL — uniqueness half landed** | connecting-graph form PROVEN via `eqOn_of_witness` (SheetCount.lean, axiom-clean): given a continuous on-curve graph χ from (xP,yP) to (xQ,yQ), ψ xQ = yQ. Closes endpoint-pin **iff** E1 supplies χ as a LEAF-A continuation arc (the planned pairing). The connected-component (`SameSheet`) form would additionally need `component_no_second_sheet` (single-valuedness of a band-good strip component) — **OPEN**, not shipped, no sorry. Decided at E1 wiring. |
| `uinf-containment` (`Inf_x ⊆ InfRoot_x`) | downstream correctness, NOT a D1/D2 input here | **CONJECTURED (spec §2.3, LEAF B discharges its core)** | LEAF B — in-flight FLAG |
| Bad ncard bound | `decomp_D1_bad_ncard` | **PROVEN-modulo (arithmetic)**, optional | B-crit ncard + InfRoot deg — FLAG `bad-ncard` |

**Headline reading.** The decomposition assembly **D2 + export-2 (band + compact) is fully written
glue over the two landed leaves** — no remaining analytic content, no FLAG on the band+compact path.
The genuine remaining work is concentrated in **two** new lemmas, both of which extract reusable
statements from machinery that **already exists** (no new analysis):

1. `fibre-local-constant` (D3 sheet-count constancy) — the harder of the two;
2. `endpoint-pin` (the `ψ xQ` residue E1 needs) — shares the same continuation-uniqueness core.

Everything else is either landed (LEAF A, LEAF B), in-flight at a known interface (`B-crit`,
`chart-bridge`, `infroot-finite` ⟸ trivial), or generic topology/arithmetic.

**One correction to the spec's framing (stated, not smuggled).** The spec carries `Bad = Crit_x ∪
Inf_x` with `Inf_x` the topological asymptote set. For the *operative* decomposition I use
`Bad = Crit_x ∪ InfRoot_x` with `InfRoot_x = {lc_y = 0}`, and demote `uinf-containment`
(`Inf_x ⊆ InfRoot_x`) to a downstream correctness lemma rather than a definitional input. This is
sound because every D1/D2 obligation needs only `InfRoot_x` (LEAF B's literal hypothesis is
`lc_y ≠ 0`), and it **shrinks** D1: `InfRoot_x` finiteness is `Polynomial`-trivial, with no topology.
`uinf-containment` is still needed to certify that the returned `ψ` is the full-width sheet (no
asymptote inside a good interval), which D3's no-escape (LEAF B) already supplies operationally; so
the topological `Inf_x` is not on the assembly's critical path. This does not move the obligation
around — it deletes the topological `Inf_x` from the cut-set definition and replaces it with the
polynomial set LEAF B already consumes.

---

## 6. What next (ranked, for the implementer)

1. **`fibre-local-constant` (FLAG, MED).** The genuine remaining D3 content. Extract from
   `MonotoneArc.lean`'s IFT box a two-sided local fibre bijection (root continues uniquely; no extra
   root, via `isCompact_strip` no-escape). This is the single hardest item *in this skeleton* (the
   hardest item *overall*, `lc-bound`, is LANDED). Do first — D3 and the sheet count gate on it.

2. **`endpoint-pin` (FLAG, MED).** The `ψ xQ` residue. Same continuation-uniqueness core as #1 —
   **do #1 and #2 together** and share the uniqueness extraction. Required to make E1 unconditional;
   not required for export-1,2. Needs a `SameSheet` predicate (connected component of the strip).

3. **`infroot-finite` + `fibre-card` (FLAGs, LOW).** Both reuse StripCompact's `Curry1`/`Specialized1`
   internals; both are short. `infroot-finite` gives D1a; `fibre-card` gives D3a. Independent of #1–2;
   can land in parallel. The only real step in `infroot-finite` is `pderiv 1 h ≠ 0 ⟹ yLeadCoeff h ≠ 0`.

4. **`crit-finite-projection` (FLAG, LOW) — gated on in-flight `B-crit` + `chart-bridge`.** Pure
   plumbing: `Crit_x = fst '' (E '' Z)`, image of a finite set. Land once those two in-flight items
   arrive. Verify the set equality `Crit_x = fst '' (E '' Z)` carefully (both inclusions use the
   eval-intertwining of `chart-bridge`).

5. **`goodlocus-components` (FLAG, LOW-MED).** Generic "finite set ⟹ complement is a finite union of
   open intervals." Curve-agnostic order topology; the `EReal` bookkeeping for unbounded ends is the
   only fiddly part. D2/D3 are stated to NOT block on this, so it can come last among the structural
   items.

6. **`bad-ncard` (FLAG, LOW), optional.** The arithmetic bound `(d+1)^5 + d`. Only for E1's constant;
   decoupled from D2/D3. Do alongside the E1 wiring (spec §3.2, §5 what-next #5), not before.

**Do NOT build** `sheet-maps` (explicit sheet family) pre-emptively — it is off the E1/E2 critical
path (E1 re-derives `ψ` per consecutive pair from LEAF A) and would be a wrapper that moves no
obligation. Stand it up only if a concrete downstream consumer demands explicit sheet maps.

**Critical-path summary.** After `lc-bound` (LANDED), the decomposition reduces to: the **glue is
already written** (D2/export-2 above), and the new theorem content is **two extraction lemmas**
(`fibre-local-constant`, `endpoint-pin`) over existing IFT/compactness machinery, plus four
low-risk plumbing FLAGs (`infroot-finite`, `fibre-card`, `crit-finite-projection`,
`goodlocus-components`) and the in-flight `B-crit`/`chart-bridge`/`uinf-containment`.
