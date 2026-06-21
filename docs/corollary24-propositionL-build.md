# Proposition L (local arc) — build record

**Scope.** Records the formalization of Proposition L from
`docs/corollary24-B2-viability.md` §3: the local IFT arc as a
`CrossingLemma.SimpleCurveArc`. This is the Edge-B "GO" brick — the local arc at a
nonsingular point of a real plane algebraic curve. It makes no claim about joining two
prescribed points (the open global obligations G-B2-arc / G-B2-sing of the viability
doc are untouched).

Date: 2026-06-20. Lean toolchain `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`.

Deliverable file: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/LocalArc.lean`
(wired via `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean`, which the root
`LeanFormalizations` library transitively imports).

---

## 1. What was proved (PROVEN)

All statements below are **PROVEN** (sorry-free, kernel-checked, core axioms only).

### Headline — `exists_simpleCurveArc_of_nonsingular`

```
theorem exists_simpleCurveArc_of_nonsingular
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
          (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0 ∨
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
          (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    ∃ a : CrossingLemma.SimpleCurveArc,
      a.carrier = Set.range a.param ∧
        a.carrier ⊆ evalPlaneZeroSet h ∧
          a.param ⟨(1 : ℝ) / 2, by norm_num⟩ = z
```

* `PlanePoly = MvPolynomial (Fin 2) ℝ` (in-repo alias).
* `evalPlane h : ℝ × ℝ → ℝ` is the in-repo (`Bezout.lean`) evaluation of `h` on
  `ℝ × ℝ`; `evalPlaneZeroSet h := {xy : ℝ × ℝ | evalPlane h xy = 0}` (new, this file)
  is the curve `γ` in `ℝ × ℝ` coordinates — the natural host of a `SimpleCurveArc`
  (whose codomain is `ℝ × ℝ`, not `Point2 = EuclideanSpace ℝ (Fin 2)`).
* **Nonsingular** is expressed directly: `evalPlane h z = 0` and at least one partial is
  nonzero at `z`. This is exactly `z ∈ γ \ SingularPointSet h` written in `ℝ × ℝ`
  coordinates (`SingularPointSet` = both partials vanish), avoiding the
  `Point2 ↔ ℝ × ℝ` identification.
* **Passes through `z`:** at parameter `½` (the midpoint of the closed subinterval the
  graph is reparametrized from). The headline is the genuine combined statement; it
  dispatches to the two charts below.

### Per-chart theorems

* `exists_simpleCurveArc_of_nonsingular_partial1` — chart over `x`, hypothesis
  `∂₁h(z) ≠ 0` (graph of the implicit function `ψ`, `t ↦ (t, ψ t)`).
* `exists_simpleCurveArc_of_nonsingular_partial0` — chart over `y`, hypothesis
  `∂₀h(z) ≠ 0`. Derived from the `∂₁` chart on the coordinate-swapped curve
  `rename (Equiv.swap 0 1) h`, composed with the swap homeomorphism `(x,y) ↦ (y,x)`
  of `ℝ × ℝ`. Both have the identical conclusion shape.

### Supporting lemmas

* `exists_implicitGraph_of_partial1` — the IFT graph data at a nonsingular point:
  produces `ψ : ℝ → ℝ`, `ε > 0` with `ψ z.1 = z.2`, **`ContinuousOn ψ (Metric.ball z.1 ε)`**,
  and `evalPlane h (x, ψ x) = 0` for all `x` in the ball. This reconstructs the
  implicit-function setup of the in-repo seed
  `nonsingular_point_has_infinite_zeroSet_of_partial1` (`Bezout.lean:544`) — which keeps
  its `ψ`/`ε`/equation/injectivity internal — and additionally extracts the
  `ContinuousOn` the seed never needed.
* `evalPlane_rename_swap` — `evalPlane (rename (swap 0 1) h) (x,y) = evalPlane h (y,x)`
  (the coordinate-swap evaluation identity used by the `∂₀` chart).

---

## 2. How the three `SimpleCurveArc` fields were discharged

`SimpleCurveArc` (`CrossingLemma/CrossingLemma.lean:43`) has fields
`param : Set.Icc (0:ℝ) 1 → ℝ × ℝ`, `cont : Continuous param`,
`inj : Function.Injective param`, and `carrier : Set (ℝ × ℝ) := Set.range param`
(default). The `param`/`cont`/`inj` fields are mandatory; `carrier` is left at its
default. **No field is left as `sorry`.**

For the chart-over-`x` arc, `param := fun t => (reparam t, ψ (reparam t))`, where
`reparam : Set.Icc (0:ℝ) 1 → ℝ`, `reparam t = z.1 + (ε/2)·(2t − 1)`, affinely sends
`[0,1]` onto `[z.1 − ε/2, z.1 + ε/2] ⊆ ball z.1 ε`, with `reparam ½ = z.1`.

| Field | Discharged by |
|---|---|
| `param` | `fun t => (reparam t, ψ (reparam t))` (graph of the IFT function on the reparametrized subinterval). |
| `cont` (`Continuous param`) | `Continuous.prodMk` of: `reparam` continuous (`fun_prop`, affine in the subtype coercion) and `ψ ∘ reparam` continuous via **`ContinuousOn.comp_continuous`** (`hψ_cont : ContinuousOn ψ (ball z.1 ε)`, `reparam` continuous, image-in-ball `hreparam_mem`). This is the FLAGGED step. |
| `inj` (`Function.Injective param`) | first coordinate: `param s = param t ⇒ reparam s = reparam t` (`congrArg Prod.fst`) `⇒ s = t` (`reparam` injective — affine with nonzero slope, `mul_left_cancel₀` + `Subtype.ext`). The doc's `isEmbedding_graph` route is not needed; the first-projection argument the in-repo seed already uses is simpler and was reused. |
| `carrier` (default `Set.range param`) | left default; the theorem additionally proves `a.carrier = Set.range a.param` (by `rfl`) so the carrier is concrete and reusable, and `a.carrier ⊆ evalPlaneZeroSet h` from the local equation `evalPlane h (x, ψ x) = 0` on the ball. |

For the chart-over-`y` arc, `param := fun t => ((a'.param t).2, (a'.param t).1)` (swap
of the `∂₁`-chart arc `a'`). Continuity from `continuous_fst`/`continuous_snd` composed
with `a'.cont`; injectivity from `a'.inj` after un-swapping; carrier-in-`γ` via
`evalPlane_rename_swap`. `carrier = range` again by `rfl`.

### The FLAGGED continuity step (resolved)

`ContDiffAt.contDiffAt_implicitFunction` (mathlib `ImplicitContDiff.lean:90`) gives only
`ContDiffAt ℝ ⊤ ψ z.1` — smoothness at the **single** base point, hence only
`ContinuousAt ψ z.1`. `SimpleCurveArc.cont` is `Continuous` on the whole subtype, which
needs `ContinuousOn ψ` on a neighbourhood. The viability doc flagged this.

Resolution (in `exists_implicitGraph_of_partial1`): `ContDiffAt.contDiffOn`
(`Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1004`),
`ContDiffAt 𝕜 n f x → m ≤ n → (m = ∞ → n = ω) → ∃ u ∈ 𝓝 x, ContDiffOn 𝕜 m f u`, applied
with `m = 0` (continuity), turns the point-local `ContDiffAt ℝ ⊤ ψ z.1` into
`∃ U ∈ 𝓝 z.1, ContDiffOn ℝ 0 ψ U`, then `contDiffOn_zero` (`Defs.lean:609`) gives
`ContinuousOn ψ U`. Intersecting `U` with the local-equation neighbourhood and shrinking
to an `ε`-ball yields a single ball carrying both continuity and the curve equation. No
"IFT hypotheses hold on an open set / same `ψ` at nearby points" argument is needed —
`ContDiffAt.contDiffOn` does it directly from the point-local `ContDiffAt`.

---

## 3. Inputs used (all PRESENT in mathlib v4.30 / in-repo)

In-repo (`Bezout.lean` / `AlgebraicPrelim.lean`, namespace `PachDeZeeuw.Algebraic`):
`evalPlane`, `evalPlane_contDiff`, `cdImplicitFunction`, `cdApplyImplicitFunction`,
`hasFDerivAt_isInvertible_partial`, `toSpanSingleton_bijective_of_ne_zero`,
`curry0_pderiv0`, `Specialized0`, `eval_eq_specialized_eval`, `mkPoint2`. The seed's
invertibility derivation (`∂₁h(z) ≠ 0 ⇒ partial derivative invertible`) is reconstructed
inline in `exists_implicitGraph_of_partial1` (the seed does not expose it as a lemma).
The existing seed `nonsingular_point_has_infinite_zeroSet_of_partial1` is **left
untouched**.

mathlib: `ContDiffAt.implicitFunction_apply_self`,
`ContDiffAt.eventually_apply_implicitFunction`,
`ContDiffAt.contDiffAt_implicitFunction`, `ContDiffAt.contDiffOn`, `contDiffOn_zero`,
`ContinuousOn.comp_continuous`, `MvPolynomial.eval_rename`, `MvPolynomial.pderiv_rename`,
`Metric.mem_nhds_iff`, `Filter.inter_mem`, standard `Prod`/`Continuous` lemmas.

`isEmbedding_graph` (`SumProd.lean:602`) was **not** needed: the first-projection
injectivity argument is shorter and is what the in-repo seed already uses.

**Structural assumptions / finiteness:** none. The result is purely local-analytic — it
uses only smoothness of `evalPlane h` (true for every polynomial) and the single nonzero
partial at `z`. No finiteness, no irreducibility, no degree bound is required for
Proposition L (those enter only the global B2 obligations, which are out of scope here).

---

## 4. `#print axioms` (PROVEN — core axioms only)

Verified by building a scratch module with `#print axioms` on each headline (then
removed). All five declarations report exactly:

```
'…exists_simpleCurveArc_of_nonsingular'          depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_simpleCurveArc_of_nonsingular_partial0' depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_simpleCurveArc_of_nonsingular_partial1' depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_implicitGraph_of_partial1'              depends on axioms: [propext, Classical.choice, Quot.sound]
'…evalPlane_rename_swap'                          depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom
axiom. This is the required `[propext, Classical.choice, Quot.sound]`.

---

## 5. Build command + result

```
./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc   # module
./lake-build.sh LeanFormalizations                                      # full root library
```

Both **succeed** (`Build completed successfully`). The root build is green with
`LocalArc` wired through `CrossingLemma.lean`. The single pre-existing `⚠` on
`PachDeZeeuw.IncidenceAssembly.Bridge` is unrelated to this file (present before the
change; `LocalArc` itself emits no warnings). The build wrapper `./lake-build.sh` was
used throughout — no direct `lean`/`lake env lean`, no stderr suppression.

(Build-environment note: the worktree had no `.lake`; mathlib `packages`/`config` were
symlinked from the parent and `build/` was APFS-cloned (copy-on-write) so project-olean
writes stay isolated to the worktree. This is build infrastructure only — no source
outside the worktree was modified.)

---

## 6. Fields/obligations NOT discharged (honest scope statement)

* **None within Proposition L itself.** All three mandatory `SimpleCurveArc` fields are
  discharged sorry-free; the headline is the full combined nonsingular-point statement,
  not a weakened fragment.
* **Out of scope (named, untouched).** The global B2 object — an arc between two
  *prescribed* same-branch points — is NOT addressed. Per the viability doc this needs
  G-B2-arc (path → injective arc / Moore–Menger, absent from mathlib v4.30) and
  G-B2-sing (real branch decomposition at a singular endpoint, absent). Proposition L is
  the local atom those would consume; it does not reduce or move that obligation.
* **`Point2` bridge.** The statement is in `ℝ × ℝ` (the `SimpleCurveArc` codomain), with
  the curve as `evalPlaneZeroSet h ⊆ ℝ × ℝ`. A bridge to `PlaneCurveZeroSet h ⊆ Point2`
  (via `mkPoint2`) was not added — it is not needed for a `SimpleCurveArc` (which lives in
  `ℝ × ℝ`) and would be a separate plumbing lemma. Flag only, not a gap in the arc.
