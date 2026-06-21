# Corollary 24 — generic-rotation WLOG step: tractability scope and minimal interface

Author: math-professor (analysis)
Date: 2026-06-21
Toolchain context: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`.
Namespace `PachDeZeeuw.Algebraic` (decomposition leaves) / `PachDeZeeuw`,
`PachSharir` (Edge-B output side).

## 0. Question and one-line verdict

**Question.** Is the generic-rotation WLOG step `edgeB_crossingInput` needs (design
doc `corollary24-E1E2-assembly-design.md` §6 FLAG `generic-rotation`; spec
`corollary24-decomposition-spec.md` §1.4) tractable in mathlib v4.30, or does it hit a
mathlib-absent brick? What is the minimal honest Lean interface, and how does each piece
classify?

**Verdict.** Tractable. **No mathlib-absent brick.** The step is finite-avoidance over a
single real scalar parameter (a *shear*, not an angular rotation), and every brick it
needs is either present in mathlib v4.30 or is a routine `MvPolynomial`/degree
construction with no missing analytic ingredient. The reusable engine is **already in the
repo** (`GenericProjection.lean`'s `momentPoly` finite-root avoidance). The minimal
interface is a clean `∃ s, (good props)` existence lemma plus a substitution-coherence
lemma; it does **not** force a heavier construction. Single hardest sub-lemma:
**Obstruction GR-1** (§5) — the `MvPolynomial` total-degree bound under the linear
substitution — which is NEEDS-CONSTRUCTION, not MATHLIB-ABSENT.

**Verification basis.** Every "landed / in-repo" claim cites a declaration whose exact
signature I read this session from source (file:line given). Mathlib-availability claims
are EMPIRICALLY VERIFIED via the `nthdegree docs … --corpus mathlib` index, except
`Polynomial.finite_setOf_isRoot`, which is **VERIFIED-from-source** (used in landed repo
code, `GenericProjection.lean:104`). I did not run `lake build` or any Lean build. Three
scratch `sympy` computations were run (`/tmp/rot_lead.py`, `/tmp/shear_fix.py`,
`/tmp/coherence.py`) and are EMPIRICALLY VERIFIED on the finite case sets stated; they do
not promote any claim to PROVEN.

---

## 1. What "generic direction" must actually guarantee (read from the leaf signatures)

I traced every decomposition leaf the Edge-B output composes (design §5.2 nodes 2–5) down
to its hypotheses. **They all bottom out at the same three hypotheses on the (already
coordinate-fixed) polynomial `h`.** This is the single most important structural finding,
because it collapses "what the direction must provide" to one algebraic condition.

### 1.1 The leaf hypotheses (VERIFIED-from-source)

| Leaf | File:line | Hypotheses on the direction / on `h` |
|---|---|---|
| `decomp_D1_bad_finite` (Bad finite) | `DecompositionD1.lean:159` | `Irreducible h`, `h.totalDegree ≤ d`, `pderiv (1:Fin 2) h ≠ 0` |
| `finite_critPointSet_of_irreducible_bound` (Crit_x finite) | `CriticalPointBound.lean:90` | same three |
| `decomp_D1_crit_finite` | `DecompositionD1.lean:114` | same three |
| `decomp_D1_infroot_finite` (InfRoot_x finite) | `DecompositionD1.lean:59` | `yLeadCoeff h ≠ 0` |
| `decomp_D1_goodLocus_components` | `GoodLocusComponents.lean:253` | `(Bad h).Finite` (supplied by `decomp_D1_bad_finite`) |
| `decomp_D3_sheet_count` (sheet count) | `SheetCount.lean:412` | `hgood : ∀ x ∈ Ioo α β, x ∉ Bad h`, `α < β` |
| `decomp_arc_on_good` (LEAF-A arc) | `DecompositionD2.lean:89` | `hgood`, interval data, `evalPlane h (xP,yP)=0` |
| `endpoint_pin_of_connectingGraph` | `SheetCount.lean:128` | `hgood`, interval data (no extra direction hyp) |

The `hgood`-consuming leaves (`decomp_D3_sheet_count`, `decomp_arc_on_good`,
`endpoint_pin_of_connectingGraph`) take "good interval" as a hypothesis and internally use
`yLeadCoeff_eval_ne_zero_of_not_bad` (`SheetCount.lean:60`) to recover `yLeadCoeff(x) ≠ 0`
over good intervals. Good intervals *exist as a finite cover of the complement of a finite
set* only once `Bad h` is finite — which is `decomp_D1_bad_finite`, the same three
hypotheses.

### 1.2 The InfRoot hypothesis is **derived**, not independent (VERIFIED-from-source)

`decomp_D1_bad_finite` does **not** take `yLeadCoeff h ≠ 0` as a separate hypothesis. It
**derives** it from `pderiv (1:Fin 2) h ≠ 0` via
`yLeadCoeff_ne_zero_of_partialY_ne_zero` (`DecompositionD1.lean:128`), whose proof chain is
`pderiv 1 h ≠ 0 ⟹ h ≠ 0 ⟹ rename swap2 h ≠ 0 ⟹ Curry1 h ≠ 0 ⟹ (Curry1 h).leadingCoeff ≠ 0`
(read `DecompositionD1.lean:131–150`). Therefore:

> **Pinned requirement.** The chosen coordinate direction must provide, for each curve
> polynomial `h` of the arrangement, the single algebraic condition
> **`pderiv (1 : Fin 2) h ≠ 0`** (the curve "genuinely involves `y`", i.e. is not a union
> of lines vertical to the sweep direction). Together with the direction-independent
> `Irreducible h` and `h.totalDegree ≤ d`, this discharges the *entire* decomposition leaf
> stack. `yLeadCoeff h ≠ 0`, `(Bad h).Finite`, `(Crit_x h).Finite`, `(InfRoot_x h).Finite`,
> and the existence of good intervals are all consequences, not separate direction demands.

The cut-set objects are exactly (`DecompositionDefs.lean:31–47`): `Crit_x h = {x | ∃ y,
evalPlane h (x,y)=0 ∧ partialY h (x,y)=0}`, `InfRoot_x h = {x | eval (·↦x) (yLeadCoeff h) =
0}`, `Bad h = Crit_x h ∪ InfRoot_x h`, `IsGoodInterval h α β := α<β ∧ ∀ x∈Ioo α β, x∉Bad h`.

### 1.3 The point-separation requirement (spec §1.4 (iii))

Beyond the per-curve algebraic condition, spec §1.4 (iii) asks the direction to **separate
incident points' x-values per sheet** (no two distinct incident points share an x-value on
the same sheet, else consecutive pairing degenerates). I did **not** find this consumed by
any landed leaf signature — the landed leaves take `hgood` and incident-point data
abstractly. It is required by the **`edgesOnSheet` pairing layer** (design §4, all FLAGged,
none landed): the line-case analogue `pointsOnLine` sorts by `lineKey` and relies on a
strict order, so the curve port needs distinct x-values within a rank class. This is a
**finite** condition (avoid the finitely many directions aligning two of the finitely many
incident points) and is exactly the form the repo's `GenericProjection.lean` already
discharges (§3).

> **Scope note.** Requirement (iii) is real but is consumed *downstream of the analytic
> leaves*, by the not-yet-landed pairing bookkeeping. It does not gate the analytic
> decomposition. The generic-direction lemma should still produce it (a `Set.InjOn`-style
> clause), because the pairing needs it; but its absence does not block D1/D2/D3.

---

## 2. Does the repo already have rotation / linear-change-of-variable machinery? (VERIFIED-from-source)

**For an algebraic coordinate change on `PlanePoly = MvPolynomial (Fin 2) ℝ`
(`AlgebraicPrelim.lean:1516`): NO continuous/scalar-parametrized change of variable exists.**
What exists:

| Mechanism | Where | What it is |
|---|---|---|
| `MvPolynomial.rename swap2`, `rename (Equiv.swap 0 1)` | `StripCompact.lean:67`, `Bezout.lean:560,669`, `InfinityCut.lean:199` | **discrete coordinate *permutation*** (the x↔y swap). NOT a parametrized substitution. |
| `RotationCoherence.lean` | imported by `CrossingLemma.lean:47` | pure `Equiv.Perm` / `finRotate` / `Equiv.swap` combinatorics on the **planar drawing's cyclic vertex ordering** (`rotationOfOrder_splice`, `RotationCoherence.lean:312`). NOT a coordinate rotation. The "rotation" naming throughout `SzemerediTrotter.lean` (`ArcsRotationRegular`, `vertexRotation`, …) is this combinatorial cyclic order, *not* `R_θ` on the plane. |
| `CurveSymmetries.lean` `Lemma26Statement` | `CurveSymmetries.lean:269` | an abstract `Prop` about conic-stabilizing affine maps. No constructive substitution. |
| `MvPolynomial.aeval` / `bind₁` on `PlanePoly` | **(none)** | repo-wide grep for `bind₁`, `MvPolynomial.aeval (fun …)`, `rotationSubst`, `substLinear` returns **nothing** in `lean/` (excluding `.lake`, worktrees). |

So the genuine rotation/shear (a *linear substitution* of the variables, which is `aeval`
of degree-1 entries, not a `rename`) **must be built from scratch in the repo.** The repo's
`rename`-based coordinate handling is the wrong tool: `rename` only permutes variable
indices, it cannot express `x ↦ x + s·y`.

**However — the *finite-avoidance engine* the rotation step needs is already in the repo**,
in a different guise. `GenericProjection.lean` (read this session) proves
`exists_linearFunctional_injOn` (`:92`) and `exists_linearProjection_injOn` (`:122`) by:
- parametrizing the separating direction by a **real scalar `s`** via `momentFunctional D s
  = ∑_j s^j · projₗ j` (`:34`) and `momentPoly D v = ∑_j monomial j (v j)` (`:49`);
- forming the bad-scalar set `⋃_{(p,q)∈P.offDiag} {s | (momentPoly D (p−q)).IsRoot s}`,
  shown finite by **`Polynomial.finite_setOf_isRoot (momentPoly_ne_zero …)`**
  (`:104`, the nonzero-real-polynomial-has-finitely-many-roots brick);
- picking `s₀` off the finite bad set via `Set.Finite.exists_notMem` (`:105`).

This is **exactly** the avoidance template the generic-direction lemma needs, and it
proves `Polynomial.finite_setOf_isRoot` is present and usable in this codebase
(VERIFIED-from-source, not just index-search). It is parametrized by a *scalar*, which is
the key to §3.

---

## 3. Is each required property an open / finite-avoidance condition mathlib can express?

**Yes — and the cleanest parametrization is a *shear by a real scalar* `s`, not an angle
`θ`.** This removes all trigonometry and matches the repo's existing `momentPoly` engine.

### 3.1 The shear (replaces the angular rotation; cleaner for Lean)

Define, for a real scalar `s`, the substitution on points and polynomials:
- on points: `T_s : ℝ×ℝ → ℝ×ℝ`, `T_s (x,y) = (x − s·y, y)` (a plane bijection, inverse
  `(x,y) ↦ (x + s·y, y)`);
- on polynomials: `B_s : PlanePoly → PlanePoly`, `B_s h := aeval ![X₀ + s•X₁, X₁] h`
  (substitute variable 0 ↦ X₀ + s·X₁, variable 1 ↦ X₁; an `AlgHom`, in fact an `AlgEquiv`
  with inverse `aeval ![X₀ − s•X₁, X₁]`).

**Coherence (EMPIRICALLY VERIFIED, `/tmp/coherence.py`):** `evalPlane (B_s h) (T_s p) =
evalPlane h p` identically, and `T_s` is a bijection. Hence `p` lies on `h`'s curve iff
`T_s p` lies on `B_s h`'s curve, and the incidence count is preserved bijectively:
`I(P, Γ) = I(T_s P, {B_s h : h ∈ Γ})`. (Checked on a generic degree-2 `h`; the identity is
the standard `eval ∘ aeval` collapse, so it holds for all `h` — the scratch check is a
sanity test of the substitution convention, not a finite-range claim about a conjecture.)

### 3.2 The bad-scalar set is finite (the `pderiv 1 ≠ 0` condition)

Let `D := h.totalDegree` and let `H` be the homogeneous top-degree part of `h`. Then
(EMPIRICALLY VERIFIED on 7 cases including the degenerate vertical-line cases `x²`, `x`,
`x³+x`, `/tmp/shear_fix.py`):

> **The coefficient of `y^D` in `B_s h` equals `H(s, 1)`** (the top form evaluated at
> `x=s, y=1`), a **univariate polynomial in `s` of degree ≤ D**.

`H(s,1)` is a **nonzero** polynomial in `s` whenever `H ≠ 0`, i.e. whenever `D ≥ 1` (some
monomial `x^a y^b`, `a+b=D`, contributes the nonzero coefficient to `s^a` in `H(s,1)`).
When `H(s,1) ≠ 0` we have `deg_y(B_s h) = D ≥ 1`, so `B_s h` genuinely involves `y`, hence
**`pderiv (1:Fin 2)(B_s h) ≠ 0`**. The bad scalars (where this fails) are the **≤ D real
roots of `H(s,1)`**, a finite set by `Polynomial.finite_setOf_isRoot`.

This handles even the worst case the spec worries about: for `h = x²` (a union of vertical
lines), `B_s(x²) = (x+s y)²` has `y²`-coefficient `s²`, nonzero for `s ≠ 0`; the bad set is
`{0}`. The shear verticalizes-away the vertical components for all but one `s`.

> **Why a scalar shear, not an angle.** With `R_θ` the same coefficient is `H(−sinθ, cosθ)`,
> a nonzero *trigonometric* polynomial (EMPIRICALLY VERIFIED, `/tmp/rot_lead.py`); its
> finiteness on `[0,2π)` needs root-counting for `cos`/`sin` combinations. The shear's
> `H(s,1)` is an ordinary real polynomial in `s`, dischargeable by the very lemma the repo
> already uses (`Polynomial.finite_setOf_isRoot`). The shear is an honest WLOG for the
> Pach–Sharir/Szemerédi–Trotter incidence count, which is invariant under all invertible
> affine maps, not only orthogonal ones — so nothing is lost by using a shear instead of a
> rotation.

### 3.3 The point-separation set is finite (condition (iii))

Identical to the repo's `exists_linearFunctional_injOn`: the x-value of `T_s p` is
`p₁ − s·p₂`, so two incident points `p ≠ q` share an x-value under `T_s` iff `s` is the
single root of the degree-≤1 polynomial `(p₁−q₁) − s(p₂−q₂)` (when `p₂ ≠ q₂`; when
`p₂ = q₂` they already differ in the x-coordinate for all `s`). The bad set is a finite
union over `P.offDiag` of `≤ 1`-element root sets — exactly the `momentPoly`/`offDiag`
pattern, finite by `Polynomial.finite_setOf_isRoot`.

### 3.4 Bricks: present vs. to-build

| Brick | Status | Evidence |
|---|---|---|
| `Polynomial.finite_setOf_isRoot` (nonzero ℝ-poly ⟹ finite roots) | **PRESENT** | VERIFIED-from-source, used at `GenericProjection.lean:104` |
| `Set.Finite.exists_notMem` (avoid a finite set) | **PRESENT** | VERIFIED-from-source, `GenericProjection.lean:105` |
| `Set.Finite.biUnion` (finite union of finite sets) | **PRESENT** | VERIFIED-from-source, `GenericProjection.lean:99` |
| `MvPolynomial.aeval` (the substitution) | **PRESENT** | mathlib `Algebra.MvPolynomial.Eval` (search VDNWQG); also `eval₂Hom`, `eval₂AlgHom` |
| `eval ∘ aeval` collapse (coherence lemma) | **PRESENT** | mathlib `MvPolynomial.Eval`; the repo already does this shape in `eval_specialized1` (`StripCompact.lean:82`) |
| `Irreducible.map` (irreducibility under a `MulEquiv`/`AlgEquiv`) | **PRESENT** | mathlib `Algebra.Group.Irreducible.Lemmas` (search 7M57ZC): "Irreducibility is preserved by multiplicative equivalences." |
| `AlgEquiv.ofAlgHom` (assemble the shear `AlgEquiv` from `B_s`, `B_{−s}` + two `comp=id`) | **PRESENT** | mathlib `Algebra.Algebra.Equiv` |
| coeff of `y^D` in `B_s h` `= H(s,1)`, a poly in `s` | **TO BUILD** (routine) | §3.2; standard top-form computation |
| `(B_s h).totalDegree = h.totalDegree` (degree under the substitution) | **TO BUILD** — Obstruction GR-1 | §5; no mathlib `aeval`/`bind₁` total-degree bound found |

**Mathlib-absent check.** Searching mathlib v4.30 for an `MvPolynomial.totalDegree` bound
under `aeval`/`bind₁` substitution (degree-≤1 entries) returned nothing applicable
(surfaced `IsHomogeneous.totalDegree_le`, `totalDegree_coeff_finSuccEquiv_add_le` — neither
is the substitution bound). This is the **only** piece without a packaged lemma, and it is
NEEDS-CONSTRUCTION (a degree estimate over `Finsupp` supports), **not** a fundamental
mathlib gap: there is no missing analytic theorem (no Harnack / Thom–Milnor / semialgebraic
machinery — those are off-path per spec §5, and the shear route does not invoke them).

---

## 4. The minimal honest Lean interface

The interface splits into (A) a **coherence** lemma (substitution preserves the curve and
incidence) and (B) an **existence** lemma (a good scalar exists). (B) is a clean
`∃ s, (props)`; it does **not** force a heavier construction, because the leaf stack
consumes only `pderiv 1 (B_s h) ≠ 0` per curve (§1) plus the separation clause (§1.3),
both of which are scalar finite-avoidance.

Throughout, `B_s h` and `T_s p` are as in §3.1. (Their definitions and the coherence lemma
are themselves NEEDS-CONSTRUCTION but routine; see §5 / FLAGs.)

```lean
namespace PachDeZeeuw.Algebraic

/-- The shear substitution on polynomials: variable `0 ↦ X₀ + s·X₁`, `1 ↦ X₁`. An
`AlgEquiv` (inverse is the `(−s)`-shear). -/
noncomputable def shearPoly (s : ℝ) (h : PlanePoly) : PlanePoly :=
  MvPolynomial.aeval
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 + (MvPolynomial.C s) * MvPolynomial.X 1
                      else MvPolynomial.X 1) h

/-- The shear on points (the inverse plane map), a bijection. -/
def shearPoint (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - s * p.2, p.2)

/-- export-GR-coherence. The shear preserves the curve pointwise:
`(x,y)` is on `h` iff `T_s (x,y)` is on `B_s h`. -/
theorem evalPlane_shearPoly_shearPoint (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p := by
  sorry  -- FLAG GR-coherence: `eval ∘ aeval` collapse; the convention is VERIFIED in /tmp/coherence.py.

/-- The shear is a plane bijection (so it transports the incident point set and the
incidence count). -/
theorem shearPoint_bijective (s : ℝ) : Function.Bijective (shearPoint s) := by
  sorry  -- FLAG GR-coherence: explicit inverse `(x,y) ↦ (x + s y, y)`.

end PachDeZeeuw.Algebraic
```

```lean
open PachDeZeeuw.Algebraic in
/-- **export-GR (the minimal generic-direction existence lemma).** For a finite family of
irreducible curve polynomials `Γ`, each of total degree `≤ d` and of total degree `≥ 1`
(genuinely curves), and a finite incident point set `P`, there is a real scalar `s` such
that **every** sheared curve has `∂_y ≠ 0` (so the whole decomposition leaf stack applies
to it) AND the shear separates the x-values of distinct incident points. -/
theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P := by
  sorry
  -- FLAG generic-rotation: bad-scalar set = (finite union over Γ of real roots of the
  --   top-form poly `H_h(s,1)`) ∪ (finite union over P.offDiag of the ≤1-root separation
  --   polys). Finite by `Polynomial.finite_setOf_isRoot` + `Set.Finite.biUnion`. Pick `s`
  --   off it (`Set.Finite.exists_notMem`). For such `s`: `H_h(s,1) ≠ 0 ⟹ deg_y(B_s h)=deg h
  --   ≥ 1 ⟹ ∂_y(B_s h) ≠ 0` (the §3.2 chain); `totalDegree ≤ d` via Obstruction GR-1;
  --   `Irreducible (B_s h)` via `Irreducible.map` on the shear `AlgEquiv`.
```

**Why `∃ s` suffices and there is no heavier construction.** The leaf stack consumes
`{Irreducible (B_s h), (B_s h).totalDegree ≤ d, pderiv 1 (B_s h) ≠ 0}` per curve (§1.1–1.2)
— exactly the four output clauses (irreducibility + degree + `∂_y ≠ 0` + separation) of the
`∃ s` above. There is no need for a `Sheet` family, a global continuation object, or any
data beyond the single scalar `s` and the coherence lemma. The Edge-B output
`edgeB_crossingInput` (design §5.1) then: (1) obtains `s` from `exists_good_shear`; (2)
pushes `P` forward to `T_s P` and `Γ` to `{B_s h}`; (3) runs the landed leaf stack +
FLAGged pairing layer in sheared coordinates; (4) transfers the incidence bound back via
`evalPlane_shearPoly_shearPoint` + `shearPoint_bijective` (incidence count invariant). Steps
(1),(4) are the generic-direction interface; (3) is the existing analytic + pairing work.

---

## 5. Single hardest sub-lemma — Obstruction GR-1

> **Obstruction GR-1 (substitution total-degree bound).** For `s : ℝ` and `h : PlanePoly`,
> `(shearPoly s h).totalDegree = h.totalDegree` — or at least `≤ h.totalDegree`, which with
> the inverse shear upgrades to equality.

**Why this is the hardest.** Every other piece is either present in mathlib
(`finite_setOf_isRoot`, `aeval`, `Irreducible.map`, `AlgEquiv.ofAlgHom`) or is the §3.2
top-form coefficient computation (mechanical). GR-1 is the one estimate with **no packaged
mathlib lemma** (§3.4 search): `MvPolynomial` total degree under an `aeval` substitution by
degree-≤1 entries. The proof is standard but must be written: `aeval f` sends a monomial
`∏ X_i^{e_i}` to `∏ (f i)^{e_i}`, each factor `f i` of total degree ≤ 1, so the image has
total degree ≤ `∑ e_i = |e|`; taking the max over monomials gives `totalDegree (aeval f h)
≤ totalDegree h`. Applying the same to the inverse substitution `B_{−s}` and using
`B_{−s}(B_s h) = h` yields equality. The work is the `Finset`/`Finsupp`-support bookkeeping
for "total degree of a product is ≤ sum of total degrees" iterated over a monomial's
support, then the sup over monomials.

**Risk: LOW–MED.** It is degree bookkeeping over `Finsupp` supports with no analytic
content; the only reason it is the *hardest* item is that it is the only one not handed to
you by an existing lemma. It is **NEEDS-CONSTRUCTION, not MATHLIB-ABSENT** — nothing
fundamental is missing.

(Note: GR-1 can be sidestepped for the `∂_y ≠ 0` clause alone — that clause needs only
`deg_y(B_s h) ≥ 1`, which §3.2's `H(s,1) ≠ 0` gives directly without a *total*-degree bound.
GR-1 is needed for the `totalDegree ≤ d` clause, which the leaf stack consumes via `hdeg`.
If the assembly is restructured so the degree bound `d` is taken on `B_s h` directly rather
than inherited from `h`, GR-1 becomes unnecessary — but the natural statement, where `d`
bounds the *original* arrangement, needs it.)

---

## 6. Classification table

| Item | Statement | Class | Evidence / dependency |
|---|---|---|---|
| Pinned requirement | direction needs only `pderiv 1 h ≠ 0` (+ `Irreducible`, `deg ≤ d`) per curve | **established (this doc §1)** | VERIFIED-from-source: leaf hyps `DecompositionD1.lean:159`, `:128`; `CriticalPointBound.lean:90`; `SheetCount.lean:412`, `:128`, `:60` |
| `Polynomial.finite_setOf_isRoot` | nonzero ℝ-poly has finite roots | **ROUTINE** (present) | VERIFIED-from-source `GenericProjection.lean:104` |
| finite-avoidance engine (`momentPoly`/`offDiag`) | scalar avoiding finite bad set | **ROUTINE** (in repo, reusable) | VERIFIED-from-source `GenericProjection.lean:92–117` |
| `shearPoly` / `shearPoint` defs | the substitution + plane map | **NEEDS-CONSTRUCTION** (routine) | `aeval` present (mathlib); convention VERIFIED `/tmp/coherence.py` |
| `evalPlane_shearPoly_shearPoint` (coherence) | curve preserved pointwise | **NEEDS-CONSTRUCTION** (routine) | `eval ∘ aeval` collapse present; repo precedent `StripCompact.lean:82` |
| `shearPoint_bijective` | plane bijection | **ROUTINE** | explicit inverse |
| `y^D` coeff of `B_s h` `= H(s,1)` | top-form coefficient is a nonzero poly in `s` | **NEEDS-CONSTRUCTION** (mechanical) | EMPIRICALLY VERIFIED `/tmp/shear_fix.py` (7 cases) |
| `pderiv 1 (B_s h) ≠ 0` for good `s` | `H(s,1) ≠ 0 ⟹ deg_y ≥ 1 ⟹ ∂_y ≠ 0` | **NEEDS-CONSTRUCTION** (routine chain) | §3.2; `deg_y` from `Curry1`/`leadingCoeff` (repo `StripCompact.lean:71`) |
| `Irreducible (B_s h)` for any `s` | irreducibility under shear `AlgEquiv` | **ROUTINE** (present) | `Irreducible.map` (mathlib 7M57ZC) + `AlgEquiv.ofAlgHom` |
| **`(B_s h).totalDegree ≤ d`** | degree under substitution — **Obstruction GR-1** | **NEEDS-CONSTRUCTION** (no mathlib lemma) | §5; mathlib search found no `aeval`/`bind₁` totalDegree bound |
| `exists_good_shear` (export-GR) | `∃ s` with all good props | **NEEDS-CONSTRUCTION** (glue) | composes the above; engine in repo |
| point separation (iii) | `InjOn` of x-value under `T_s` | **ROUTINE** (present pattern) | exactly `exists_linearFunctional_injOn` |
| incidence transfer-back | `I(P,Γ) = I(T_s P, B_s Γ)` | **NEEDS-CONSTRUCTION** (routine) | bijection + coherence; depends on the Edge-B incidence-count def (not yet landed) |
| Harnack / Thom–Milnor / semialgebraic | component-count machinery | **MATHLIB-ABSENT and OFF-PATH** | EMPIRICALLY VERIFIED (spec §5); the shear route never invokes them |

**No row is MATHLIB-ABSENT-and-on-path.** The only MATHLIB-ABSENT entries (component-count
theorems) are off the route by construction; everything on the route is ROUTINE or
NEEDS-CONSTRUCTION-routine.

---

## 7. What next (ranked)

1. **`shearPoly` / `shearPoint` + coherence (`evalPlane_shearPoly_shearPoint`,
   `shearPoint_bijective`).** The substitution and its curve-preservation. Gates everything
   else; routine `aeval`/`eval` algebra with a repo precedent (`eval_specialized1`). Do
   first. Risk LOW.

2. **Obstruction GR-1 (`(B_s h).totalDegree = h.totalDegree`).** The one item with no
   mathlib lemma. Standard `Finsupp`-support degree bookkeeping; the bottleneck only in the
   sense of "not handed to you". Risk LOW–MED. (Skippable if the assembly takes `d` on the
   sheared curves directly — see §5 note.)

3. **`y^D`-coeff `= H(s,1)` + the `∂_y(B_s h) ≠ 0` chain.** The §3.2 computation: top form,
   its value at `(s,1)`, nonzero-poly-in-`s`, `deg_y ≥ 1 ⟹ Curry1` nonzero ⟹ `pderiv 1 ≠ 0`.
   Reuses the landed `yLeadCoeff_ne_zero_of_partialY_ne_zero` direction in reverse. Risk
   LOW–MED.

4. **`exists_good_shear` (export-GR).** Assemble #1–#3 with the repo's finite-avoidance
   engine (`Polynomial.finite_setOf_isRoot`, `Set.Finite.biUnion`,
   `Set.Finite.exists_notMem`) over the bad-scalar union (top-form roots per curve +
   separation roots per point-pair) + `Irreducible.map`. This is the headline lemma. Risk
   MED (glue volume, no new analysis).

5. **Incidence transfer-back** into `edgeB_crossingInput`. Gates on the Edge-B incidence
   count definition (design §5.1, not yet landed) and the pairing layer (design §4 FLAGs).
   Routine once those exist.

**Do not** introduce angular `R_θ` / `cos`/`sin` (§3.2): the scalar shear is a valid WLOG
for the affine-invariant incidence count and keeps every avoidance condition a *real
polynomial in `s`*, matching the engine already in `GenericProjection.lean`. **Do not**
reach for component-count machinery (Harnack/Thom–Milnor/semialgebraic): MATHLIB-ABSENT and
off-path; the shear route delivers `∂_y ≠ 0` from univariate top-form roots, never needing
them.
