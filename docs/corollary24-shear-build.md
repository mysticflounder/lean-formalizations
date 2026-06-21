# Corollary 24 — shear substitution + coherence build record (Edge B, `Shear.lean`)

Author: math-prover
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic`. File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/Shear.lean`.

## Scope

This realizes step 1 of the `generic-rotation` WLOG construction
(`docs/corollary24-generic-rotation-scope.md` §3.1, §4, §7 item 1): the foundational
brick on which the rest of the generic-direction argument is built. The "generic
direction" is a **shear by a real scalar** `s` (substitution `x ↦ x + s·y`, `y ↦ y` on
polynomials; inverse plane map `(x,y) ↦ (x − s·y, y)` on points), NOT an angular rotation.
This is the WLOG-valid affine change of variable for the affine-invariant incidence count,
and it removes all trigonometry.

Delivered (scope doc §4):

* `shearPoly s h` — polynomial substitution `var 0 ↦ X₀ + s·X₁`, `var 1 ↦ X₁`.
* `shearPoint s p` — inverse plane map `(x,y) ↦ (x − s·y, y)`.
* `evalPlane_shearPoly_shearPoint` — curve-preservation coherence (the `eval ∘ aeval`
  collapse).
* `shearPoint_bijective` — plane bijection with explicit two-sided inverse.
* `shearPoint_curve_iff` — the curve-set transfer corollary the downstream incidence
  transfer consumes.

**Explicitly NOT in scope (separate downstream steps, scope doc §5, §7 items 2–4):**
Obstruction GR-1 (the `totalDegree` bound under the substitution), the `∂_y ≠ 0` chain
(`H(s,1) ≠ 0 ⇒ deg_y ≥ 1`), `exists_good_shear` (the headline `∃ s` existence lemma), and
the `Irreducible (shearPoly s h)` transfer. None of those are touched here.

## Status: COMPLETE. No `sorry`, no `native_decide`, no `unsafe`, no `@[implemented_by]`, no `@[extern]`, no named `axiom`.

Build target: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear` (from
repo root) — `Build completed successfully (8482 jobs)`, no warnings, no errors.

Forbidden-token scan over the shipped file: clean (no `sorry` / `native_decide` /
`@[implemented_by]` / `@[extern]` / `unsafe` / `axiom`).

### `#print axioms` (verbatim) — every shipped declaration

```
'PachDeZeeuw.Algebraic.evalPlane_shearPoly_shearPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoint_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoint_curve_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPointInv_shearPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoint_shearPointInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPointInv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPointEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearVars' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.shearPointInv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exactly `[propext, Classical.choice, Quot.sound]` for all twelve. No `sorryAx`, no
`Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom axioms.
(Verified by compiling a throwaway `#print axioms` harness with `lake env lean` against the
already-built dependency oleans; the harness file was deleted and is not committed.)

## Definitions

```lean
noncomputable def shearVars (s : ℝ) : Fin 2 → PlanePoly :=
  fun i => if i = 0 then MvPolynomial.X 0 + (MvPolynomial.C s) * MvPolynomial.X 1
           else MvPolynomial.X 1

noncomputable def shearPoly (s : ℝ) (h : PlanePoly) : PlanePoly :=
  MvPolynomial.aeval (shearVars s) h

def shearPoint (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - s * p.2, p.2)

def shearPointInv (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + s * p.2, p.2)
```

`shearVars` is factored out of `shearPoly` (one definition of the substitution vector). The
substitution form `shearPoly s h := aeval (shearVars s) h` is exactly the scope-doc §3.1
`B_s`. `shearPointInv` is the explicit two-sided inverse used for bijectivity and the
point-level `Equiv`.

## THE COHERENCE CONVENTION (settled)

`evalPlane` (`Bezout.lean:451`) is
`evalPlane p (x,y) = MvPolynomial.eval (fun i => if i = 0 then x else y) p`, i.e.
**variable index `0` is `x`, index `1` is `y`**.

With the scope-doc signs unchanged:

* `shearPoly` substitutes `var 0 ↦ X₀ + s·X₁`, `var 1 ↦ X₁`;
* `shearPoint s (x,y) = (x − s·y, y)`;

the coherence identity `evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p` holds
**on the nose** — no inverse-sign adjustment was needed. Symbolic derivation (the check the
task required): writing `(x',y') := shearPoint s (x,y) = (x − s·y, y)`,

```
evalPlane (shearPoly s h) (x',y')
  = eval (i ↦ if i=0 then x' else y') (aeval (shearVars s) h)         -- defs
  = aeval (i ↦ aeval (i ↦ if i=0 then x' else y') (shearVars s i)) h  -- eval∘aeval collapse
```

and evaluating the substituted variables at the sheared point:

* `var 0 ↦ x' + s·y' = (x − s·y) + s·y = x`,
* `var 1 ↦ y' = y`,

so the inner point function is `i ↦ if i=0 then x else y`, giving
`eval (i ↦ if i=0 then x else y) h = evalPlane h (x,y)`. The `s·y` introduced by the
polynomial shear (`X₀ ↦ X₀ + s·X₁`) cancels the `− s·y` of the point shear (`x ↦ x − s·y`):
the two signs are conjugate by design, which is why the convention closes exactly.

This matches the scope doc's intended statement `evalPlane (B_s h)(T_s p) = evalPlane h p`;
the convention shipped is the scope-doc convention.

## The deliverables and their exact shipped signatures

| # | Name | Signature (conclusion) | Class |
|---|---|---|---|
| def | `shearPoly` | `ℝ → PlanePoly → PlanePoly` | PROVEN (definition) |
| def | `shearPoint` | `ℝ → ℝ × ℝ → ℝ × ℝ` | PROVEN (definition) |
| (1) | `evalPlane_shearPoly_shearPoint` | `evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p` | **PROVEN** |
| (2) | `shearPoint_bijective` | `Function.Bijective (shearPoint s)` | **PROVEN** |
| (3) | `shearPoint_curve_iff` | `p ∈ evalPlaneZeroSet h ↔ shearPoint s p ∈ evalPlaneZeroSet (shearPoly s h)` | **PROVEN** |
| aux | `shearPointInv_shearPoint` / `shearPoint_shearPointInv` | two-sided inverse identities | **PROVEN** |
| aux | `shearPointEquiv` | `(ℝ × ℝ) ≃ (ℝ × ℝ)` packaging the point shear | **PROVEN** |

### Proof strategies

**(1) `evalPlane_shearPoly_shearPoint`** — the `eval ∘ aeval` collapse.
1. Set `pt : Fin 2 → ℝ := fun i => if i = 0 then (shearPoint s p).1 else (shearPoint s p).2`,
   the point at which the substituted polynomial is evaluated.
2. Rewrite `evalPlane (shearPoly s h) (shearPoint s p)` as
   `(MvPolynomial.aeval pt) (MvPolynomial.aeval (shearVars s) h)` using `evalPlane`,
   `shearPoly`, and `MvPolynomial.aeval_eq_eval` (over the base ring `ℝ`, `eval = aeval`).
3. Push the outer `aeval pt` (an `ℝ`-algebra hom `MvPolynomial (Fin 2) ℝ →ₐ[ℝ] ℝ`) through
   the inner `aeval` with **`MvPolynomial.comp_aeval_apply`**, reducing to
   `aeval (fun i => aeval pt (shearVars s i)) h`.
4. Prove the inner variable map equals the unsheared point function
   `fun i => if i = 0 then p.1 else p.2` (`funext i; fin_cases i`):
   * index 0: `aeval pt (X 0 + C s * X 1) = pt 0 + s · pt 1 = (p.1 − s·p.2) + s·p.2 = p.1`
     via `map_add`, `map_mul`, `aeval_X`, `aeval_C`, `Algebra.algebraMap_self_apply`
     (`algebraMap ℝ ℝ s = s`), then `ring`. (`pt 0 = p.1 − s·p.2`, `pt 1 = p.2` hold by
     `rfl`.)
   * index 1: `aeval pt (X 1) = pt 1 = p.2`.
5. Rewrite by that equality, unfold `evalPlane`, and collapse `eval = aeval` again
   (`MvPolynomial.aeval_eq_eval`).

The codebase precedent for this shape is `eval_specialized1` (`StripCompact.lean:82`),
which performs the analogous `eval`-through-substitution collapse via
`eval_eq_eval_mv_eval'` + `eval_rename`. This file uses the `aeval`-native lemma
`comp_aeval_apply` instead of `rename`/`finSuccEquiv`, because the shear is a genuine
linear substitution (`X₀ ↦ X₀ + s·X₁`), not a variable permutation.

**(2) `shearPoint_bijective`** — explicit two-sided inverse. Two `@[simp]` lemmas
`shearPointInv_shearPoint`, `shearPoint_shearPointInv` discharge the inverse identities by
`cases` on the pair + `Prod.mk.injEq` + `ring` on the first coordinate (second is reflexive
after `Prod.mk.injEq`). Then `Function.bijective_iff_has_inverse.2 ⟨shearPointInv s, …⟩`.
Also packaged as `shearPointEquiv : (ℝ × ℝ) ≃ (ℝ × ℝ)`.

**(3) `shearPoint_curve_iff`** — immediate from (1): rewrite both `evalPlaneZeroSet`
memberships to `evalPlane = 0` (`mem_evalPlaneZeroSet`) and apply
`evalPlane_shearPoly_shearPoint`. The statement is in the direction the downstream incidence
transfer consumes: `p` on `h` ⟺ `T_s p` on `B_s h`. No sign/direction subtlety arose; this
is the exact §4-preferred form.

## Landed API consumed (read from source this session)

| Symbol | Where | Use |
|---|---|---|
| `PlanePoly` (`= MvPolynomial (Fin 2) ℝ`) | `AlgebraicPrelim.lean:1516` | the polynomial type |
| `evalPlane` (`= eval (i ↦ if i=0 then x else y)`) | `Bezout.lean:451` | plane evaluation; fixes the `0↦x, 1↦y` convention |
| `evalPlaneZeroSet` / `mem_evalPlaneZeroSet` | `LocalArc.lean:48,51` | the curve `{h=0}` and its membership simp lemma |
| `MvPolynomial.aeval` | mathlib `Algebra.MvPolynomial.Eval:585` | the substitution |
| `MvPolynomial.comp_aeval_apply` | mathlib `Eval.lean:628` | the `eval ∘ aeval` collapse (pushes an `AlgHom` through `aeval`) |
| `MvPolynomial.aeval_eq_eval` | mathlib `Eval.lean:600` | `eval g = aeval g` over the base ring |
| `MvPolynomial.aeval_X`, `aeval_C` | mathlib `Eval.lean:603,606` | variable / constant images |
| `Algebra.algebraMap_self_apply` | mathlib `Algebra/Defs.lean:396` | `algebraMap ℝ ℝ s = s` |
| `Function.bijective_iff_has_inverse` | mathlib | bijectivity from a two-sided inverse |

## PROVEN / CONJECTURED / EMPIRICALLY VERIFIED / HEURISTIC classification

| Claim | Class | Basis |
|---|---|---|
| `shearPoly`, `shearPoint`, `shearVars`, `shearPointInv` are well-typed defs | **PROVEN** | compiles; defs |
| `evalPlane_shearPoly_shearPoint` (coherence) | **PROVEN** | Lean kernel, axioms `[propext, Classical.choice, Quot.sound]` |
| Coherence holds on the nose with the scope-doc signs (no inverse-sign flip) | **PROVEN** | the proof closes with those exact signs; symbolic derivation above |
| `shearPoint_bijective` (explicit inverse `(x,y) ↦ (x+s·y,y)`) | **PROVEN** | Lean kernel, same axioms |
| `shearPoint_curve_iff` (curve-set transfer) | **PROVEN** | Lean kernel, same axioms |
| `shearPointEquiv` (point-level `Equiv`) | **PROVEN** | Lean kernel, same axioms |
| Whole file is axiom-clean (no `sorryAx`/`ofReduceBool`/custom) | **PROVEN** | `#print axioms` verbatim above |
| Polynomial `shearPoly` is an `AlgEquiv` (inverse the `(−s)`-shear) | **NOT ATTEMPTED (deferred)** | out of scope; see note below |
| `(shearPoly s h).totalDegree ≤ d` (Obstruction GR-1) | **NOT ATTEMPTED** | out of scope (scope doc §5) |
| `pderiv 1 (shearPoly s h) ≠ 0` for good `s` | **NOT ATTEMPTED** | out of scope (scope doc §3.2, §7 item 3) |
| `exists_good_shear` (headline existence) | **NOT ATTEMPTED** | out of scope (scope doc §7 item 4) |

## AlgEquiv packaging decision (deferred)

The task permitted additionally packaging `shearPoly` as an `AlgEquiv` (inverse the
`(−s)`-shear) IF it lands cleanly, since `Irreducible.map` downstream wants it. **Deferred.**
Reasoning: it requires the `aeval`-composition law
`aeval (shearVars (−s)) (aeval (shearVars s) h) = h` (i.e.
`aeval (fun i => aeval (shearVars (−s)) (shearVars s i)) = AlgHom.id` via
`comp_aeval` + showing `aeval (shearVars (−s)) (shearVars s i) = X i` for each `i`), which
is a self-contained ~30–40 line addition and belongs with the `Irreducible (shearPoly s h)`
transfer — explicitly a separate downstream step (scope doc §3.4, §6, consumed only by
`exists_good_shear`, §7 item 4, which is out of scope here). To keep this deliverable scoped
to §7 item 1 (defs + coherence + bijectivity), the polynomial `AlgEquiv` is left for the
step that needs it. The **point-level** `Equiv` (`shearPointEquiv`) IS shipped — it is a
clean byproduct of the bijectivity proof and is what the incidence-count transfer (push the
incident-point `Finset` forward) consumes.

## Convention note for the orchestrator

The aggregator `CrossingLemma.lean` was deliberately NOT edited (per task constraint). To
wire this file in, add
`import LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear` to the aggregator during
validation. Build the module standalone with
`./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.Shear`.
