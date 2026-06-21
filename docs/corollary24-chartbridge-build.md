# `chart-bridge` build record — coordinate-chart homeomorphism `Point2 ≃ₜ ℝ × ℝ`

Author: Adam McKenna (adam-apple@flounder.net)
Date: 2026-06-20
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`

**Status: CLOSED (PROVEN).** The coordinate-chart bridge of Edge B's generic
monotone graph decomposition (`docs/corollary24-decomposition-spec.md`, FLAG
`chart-bridge`, §0, §4) is constructed, sorry-free and axiom-clean.

File: `lean/LeanFormalizations/PachDeZeeuw/ChartBridge.lean`
Wired via: `lean/LeanFormalizations.lean` (aggregator import, alongside the other
`PachDeZeeuw` modules).

---

## 1. What this discharges

The decomposition's two coordinate representations of the same plane curve:

* `Point2 = EuclideanSpace ℝ (Fin 2)` (an L² space) hosts every Bézout /
  singularity finiteness bound — `PlaneCurveZeroSet` (`AlgebraicPrelim.lean:118`),
  `SingularPointSet`, `factor_intersection_bound`,
  `finite_singularities_of_irreducible_bound` (`Bezout.lean`).
* `ℝ × ℝ` hosts the per-arc analytic machinery — `evalPlane` (`Bezout.lean:451`),
  `evalPlaneZeroSet` (`LocalArc.lean:48`), the per-arc lemma (`MonotoneArc.lean`),
  the `lc-bound` strip-compactness `isCompact_strip` (`StripCompact.lean`).

They are the same curve under the canonical linear homeomorphism `E : Point2 ≃ₜ
ℝ × ℝ`, `x ↦ (x 0, x 1)`. This file provides `E` and the transport lemmas that
move a `Point2`-side finiteness/compactness fact to an `ℝ × ℝ`-side band/strip
fact, as the spec's §2.1 caveat (`B-crit-lemma`) and §1.3 (D2b) require.

---

## 2. Exact signatures (all PROVEN, sorry-free)

All in `namespace PachDeZeeuw.Algebraic`. `Point2` and `PlanePoly` are the
existing abbreviations; `evalPlane`, `evalPlaneZeroSet`, `PlaneCurveZeroSet` are
the existing project objects.

### The homeomorphism

```lean
/-- `E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`, `x ↦ (x 0, x 1)`. -/
noncomputable def chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow

scoped notation "E" => chartEquiv
```

Assembled exactly as the spec's §0 / §4 FLAG prescribes:
`EuclideanSpace.equiv (Fin 2) ℝ : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ)`
(a continuous *linear* equiv — its `.toHomeomorph` forgets the L² structure to
the bare function space) composed with
`Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ` (the searched-for name; its
forward map is `f ↦ (f 0, f 1)` via `finTwoArrowEquiv`).

### Coordinate formulas (all `@[simp]`, all `rfl`)

```lean
theorem chartEquiv_apply (x : Point2) : chartEquiv x = (x 0, x 1)
theorem chartEquiv_fst   (x : Point2) : (chartEquiv x).1 = x 0
theorem chartEquiv_snd   (x : Point2) : (chartEquiv x).2 = x 1
theorem chartEquiv_symm_apply_zero (z : ℝ × ℝ) : (chartEquiv.symm z) 0 = z.1
theorem chartEquiv_symm_apply_one  (z : ℝ × ℝ) : (chartEquiv.symm z) 1 = z.2
```

That all five are `rfl` confirms the orientation matches `evalPlane`'s
`if i = 0 then z.1 else z.2` convention (verified against `Bezout.lean:633`/`:654`,
where `mkPoint2 x (ψ x) i = if i = 0 then x else ψ x` under `eval`).

### Intertwining (deliverable 2)

```lean
/-- `eval (fun i => x i) p = evalPlane p (E x)`. -/
theorem eval_eq_evalPlane_chart (p : PlanePoly) (x : Point2) :
    MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x)
```

Proof: `unfold evalPlane`, reduce to the equality of evaluation functions
`(fun i => x i) = (fun i => if i = 0 then (E x).1 else (E x).2)`, discharged by
`fin_cases i <;> simp` (the `chartEquiv_fst`/`chartEquiv_snd` simp lemmas fire).
The orientation here is the one the spec asked to verify: it is
`evalPlane p (E x)`, **not** the swap, because `(E x).1 = x 0` and `(E x).2 = x 1`.

### Curve-set transport (deliverable 3)

```lean
/-- `E '' PlaneCurveZeroSet p = evalPlaneZeroSet p`. -/
theorem chartEquiv_image_planeCurveZeroSet (p : PlanePoly) :
    chartEquiv '' PlaneCurveZeroSet p = evalPlaneZeroSet p

/-- `E ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p`. -/
theorem chartEquiv_preimage_evalPlaneZeroSet (p : PlanePoly) :
    chartEquiv ⁻¹' evalPlaneZeroSet p = PlaneCurveZeroSet p
```

The image lemma is the spec's deliverable 3; the preimage form is the companion
(curve pulls back), proved directly from the intertwining.

### Preservation lemmas (deliverable 4)

```lean
theorem chartEquiv_image_finite_iff {s : Set Point2} :
    (chartEquiv '' s).Finite ↔ s.Finite
theorem chartEquiv_image_finite {s : Set Point2} (hs : s.Finite) :
    (chartEquiv '' s).Finite
theorem chartEquiv_image_isCompact_iff {s : Set Point2} :
    IsCompact (chartEquiv '' s) ↔ IsCompact s
theorem chartEquiv_image_isCompact {s : Set Point2} (hs : IsCompact s) :
    IsCompact (chartEquiv '' s)
```

- Finite: `Set.finite_image_iff (chartEquiv.injective.injOn)` (forward: `.image`).
- Compact: forward is `IsCompact.image chartEquiv.continuous`; the `iff`'s reverse
  pushes through `chartEquiv.symm.continuous` and `chartEquiv.symm_comp_self`.

### First-coordinate intertwining (deliverable 4, x-projection)

```lean
/-- `(E x).1 = x 0` (named form for use through `E`). -/
theorem chartEquiv_intertwines_fst (x : Point2) : (chartEquiv x).1 = x 0

/-- x-values agree in both charts:
    `(fun x => (E x).1) '' PlaneCurveZeroSet p = Prod.fst '' evalPlaneZeroSet p`. -/
theorem chartEquiv_xproj_image (p : PlanePoly) :
    (fun x : Point2 => (chartEquiv x).1) '' PlaneCurveZeroSet p
      = Prod.fst '' evalPlaneZeroSet p
```

`chartEquiv_xproj_image` is the form the decomposition's x-axis cut (§1.1) will
consume to move "the set of bad x-values" between charts: combining
`chartEquiv_image_planeCurveZeroSet` with `chartEquiv_fst`, the `Point2`-side
x-projection of the curve equals the `ℝ × ℝ`-side x-projection. With
`chartEquiv_image_finite_iff`, a `Point2`-side finite critical set (from
`factor_intersection_bound`) transports to a finite set of critical x-values on
the `ℝ × ℝ` side.

---

## 3. Axiom report (PROVEN)

`#print axioms` on every one of the 15 declarations returns exactly:

```
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`/`Lean.ofReduceNat`, no custom axioms, no
`native_decide`. Verified via a scratch `#print axioms` harness (built, then
removed). `grep` over `ChartBridge.lean` confirms no `sorry`/`admit`/
`native_decide`/`axiom` tokens.

---

## 4. Build

```
./lake-build.sh LeanFormalizations.PachDeZeeuw.ChartBridge
→ Build completed successfully (8479 jobs).
```

ChartBridge itself elaborates in ~4 s; the job count is the full mathlib +
project dependency closure (Bezout, LocalArc, and their transitive deps). No new
warnings attributable to `ChartBridge.lean` (the `info:` lines in the log are
pre-existing `#check`s in `CrossingLemma.lean`, a transitive dependency).

---

## 5. Relationship to downstream FLAGs

This bridge is the §2.1 / §1.3 (D2b) caveat's discharge: it is what lets the
`Point2`-stated `factor_intersection_bound` and
`finite_singularities_of_irreducible_bound` (and, via `B-crit-lemma`, the
critical set `Z = γ ∩ {∂_y h = 0}`) be moved to `ℝ × ℝ`-side finite-bad-x-value
facts, and lets a `Point2`-side compact set become an `ℝ × ℝ`-side compact `K`
for the per-arc lemma's `hK`. It does not by itself prove `B-crit-lemma`,
`uinf-containment`, `sheet-count`, or `generic-rotation`; it removes the
coordinate-mismatch obstruction between the two halves of the decomposition.

The two preservation directions provided (`_iff` and forward) cover both uses:
the forward `chartEquiv_image_finite` / `chartEquiv_image_isCompact` for moving a
`Point2`-fact to `ℝ × ℝ`, and the `_iff` forms when the `ℝ × ℝ`-side statement is
the hypothesis.
