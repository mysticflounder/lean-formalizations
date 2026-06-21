# Strengthened-A1, conditions (1)∧(2) — build record

**Scope.** Records the formalization of the rank-2 + `InjOn` half of the
strengthened-A1 node specified in `docs/corollary24-A4a-adjudication.md` §6.1
(`exists_generic_projection`). The §6.1 obligation has three conditions:
(1) `π` surjective (rank 2); (2) `Set.InjOn π ↑P`; (3) secant-cone / BAD-avoidance.
**This build establishes conditions (1)∧(2) only.** Condition (3) is entangled
with the canonical eliminant `F_γ` (the separate `A2_canonical` node, §6.2) and is
**not** addressed here; it remains open for a future task.

The new declarations are added to
`lean/LeanFormalizations/PachDeZeeuw/PachSharir/GenericProjection.lean`, sibling to
the existing `exists_linearProjection_injOn`. The existing engine declarations
(`momentFunctional`, `momentPoly`, `exists_linearFunctional_injOn`,
`exists_linearProjection_injOn`) are unchanged.

## Final statement

```lean
/-- **Strengthened-A1, conditions (1)∧(2).** For `D ≥ 2` and a finite point set
`P` there is a linear map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ
(Fin 2)` that is surjective (rank 2) and injective on `P`. -/
theorem exists_rank2_projection_injOn (hD : 2 ≤ D)
    (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Function.Surjective π ∧ Set.InjOn π ↑P
```

Two supporting theorems (grounded reusable sublemmas, same file/namespace):

```lean
/-- An independent pair of functionals assembles, via `LinearMap.pi`, to a
surjective map `ℝ^D → (Fin 2 → ℝ)`. -/
theorem surjective_pi_of_linearIndependent
    (f g : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) (hfg : LinearIndependent ℝ ![f, g]) :
    Function.Surjective
      (LinearMap.pi ![f, g] : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] (Fin 2 → ℝ))

/-- For `D ≥ 2`, any nonzero functional `f` extends to an independent pair
`![g, f]` in the dual space. -/
theorem exists_linearIndependent_pair_of_ne_zero (hD : 2 ≤ D)
    (f : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ g : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ, LinearIndependent ℝ ![g, f]
```

## Status: PROVEN (Lean-verified, sorry-free, axiom-clean)

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.PachSharir.GenericProjection`
  succeeds with no errors, no warnings, no `sorry`.
- Axiom report (`#print axioms PachSharir.exists_rank2_projection_injOn`):
  `[propext, Classical.choice, Quot.sound]` — only the three permitted Lean core
  axioms. No `sorryAx`, no `Lean.ofReduceBool`, no custom axioms. (`native_decide`
  is not used anywhere in the proof.)
- Toolchain: `leanprover/lean4:v4.30.0`, mathlib pinned by the repo
  `lake-manifest.json`.

## Construction (PROVEN mathematics)

`exists_linearFunctional_injOn D P` (the existing moment-curve engine) yields a
single functional `λ` separating all pairs of `P`. The rank-2 map is `π = (μ, λ)`
assembled as `(EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ LinearMap.pi
![μ, λ]`, with `μ` chosen so the pair `![μ, λ]` is linearly independent in the
dual.

- **Condition (2), `InjOn`.** Inherited from the `λ`-coordinate (the *second*
  coordinate of the assembled map): `π p = π q ⟹ λ p = λ q ⟹ p = q` by the
  separating property of `λ`. Independent of the choice of `μ`.
- **Condition (1), surjective.** From independence of `![μ, λ]`: the composite is
  `LinearEquiv.surjective` (the `EuclideanSpace.equiv` factor) composed with
  surjectivity of `LinearMap.pi ![μ, λ]`, the latter proven from independence via
  the transpose criterion (`surjective_pi_of_linearIndependent`).
- **Existence of `μ`.** When `λ ≠ 0`, `exists_linearIndependent_pair_of_ne_zero`
  completes `λ` to `![μ, λ]` (using `dim (dual ℝ^D) = D ≥ 2 > 1`). When `λ = 0`
  (which forces `P` to be a subsingleton, so `InjOn` is automatic for any `π`),
  the construction seeds surjectivity with the nonzero coordinate functional
  `proj 0` instead.

The `λ = 0` branch is a genuine case split, not vacuous: it is reached exactly
when `|P| ≤ 1`, and there `InjOn` holds for the constructed rank-2 `π` because the
domain set is a subsingleton.

## mathlib bricks used

- `LinearMap.dualMap_injective_iff` — `f.dualMap` injective ↔ `f` surjective (the
  transpose criterion driving `surjective_pi_of_linearIndependent`).
- `LinearMap.ker_eq_bot`, `Submodule.eq_bot_iff` — injectivity via trivial kernel.
- `LinearMap.dualMap_apply`, `LinearMap.pi_apply`, `map_sum`, `map_smul` — to
  expand the dual map of `LinearMap.pi` into the covector combination.
- `Fintype.linearIndependent_iff` — independence ⟹ all coefficients zero.
- `linearIndependent_unique_iff` — singleton `![f]` independent ↔ `f ≠ 0`.
- `exists_linearIndependent_cons_of_lt_rank` — extend an independent family by one
  vector below the rank.
- `Module.finrank_linearMap`, `finrank_euclideanSpace`, `Module.finrank_eq_rank` —
  to certify `1 < rank (dual ℝ^D) = D` for `D ≥ 2`.
- `LinearEquiv.surjective`, `Function.Surjective.comp`, `LinearMap.coe_comp` —
  surjectivity of the assembled composite.
- `EuclideanSpace.projₗ`, `EuclideanSpace.single`, `PiLp.single_apply`,
  `EuclideanSpace.equiv` — the `EuclideanSpace`/`PiLp` packaging and the `proj 0`
  seed for the degenerate branch.

## Open obligation (out of scope here)

Condition (3) of §6.1 — for every `p ∈ P` and `γ ∈ Γ` with `p ∉ γ`,
`π p ∉ Z(F_γ)` (the BAD-avoidance / secant-cone condition) — is **not** proven by
this theorem. Per the adjudication doc it is the load-bearing mathlib-absent
content (Proposition 3: `BAD(p,γ)` is a proper real subvariety), and it is
entangled with the canonical eliminant `F_γ` of the `A2_canonical` node (§6.2). It
requires the secant-cone dimension argument (including directions at infinity) and
the canonical-eliminant development, neither of which is in mathlib. That is the
next node in dependency order after this one.
