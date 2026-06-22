# Corollary 24 — Edge-B shear application (`EdgeBShearApply.lean`)

Author: Adam McKenna
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open CrossingLemma`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBShearApply.lean`.

Status: **PROVEN, sorry-free, axiom-clean.**
`#print axioms edgeB_crossingInput_unsheared` = `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`, no `Lean.ofReduceBool`, no custom axioms). Same closure for the three
supporting lemmas `incidenceCount_map_image_equiv`, `image_shearPoint_evalPlaneZeroSet`,
`shearPoly_injective`. The theorem does not touch the parked `sorry`s in
`SzemerediTrotter.lean:4533`, `PLArc.lean`, `PlaneArcSeparation.lean`,
`CrossingLemmaAmplification.lean` (all off this proof's import-closure spine).

## Scope (item 5 of the generic-rotation scope, `corollary24-generic-rotation-scope.md` §7)

`edgeB_crossingInput` (`EdgeBCrossingInput.lean`) requires its curve family as a
`Finset (EdgeBCurve d)`, and `EdgeBCurve d` bakes in the non-vertical condition
`pderiv (1 : Fin 2) h ≠ 0` (`EdgeBMultigraph.lean:63`). This node removes that precondition
by shearing: it proves the same incidence bound, with the same constant
`edgeBCrossingConst d M`, for an arbitrary `Γ₀ : Finset PlanePoly` of irreducible plane
curve polynomials of total degree `≤ d` and `≥ 1` (no `∂_y ≠ 0` assumption). It is
composition over two landed layers (`edgeB_crossingInput` and the shear stack) plus three
small new lemmas; no new analysis.

## Shipped signature (exact)

```lean
theorem edgeB_crossingInput_unsheared
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ₀ : Finset PlanePoly)
    (hirr : ∀ h ∈ Γ₀, Irreducible h)
    (hdeg : ∀ h ∈ Γ₀, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ₀, 1 ≤ h.totalDegree)
    (hpp₀ : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ₀.filter (fun h => p ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
        q ∈ {z | evalPlane h z = 0})).card ≤ M)
    (hcc₀ : ∀ h₁ ∈ Γ₀, ∀ h₂ ∈ Γ₀, h₁ ≠ h₂ →
      ({z : ℝ × ℝ | evalPlane h₁ z = 0} ∩ {z | evalPlane h₂ z = 0}).encard ≤ (M : ℕ∞)) :
    (PachSharir.incidenceCount P (Γ₀.image (fun h => evalPlaneZeroSet h)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ₀.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ₀.card : ℝ))
```

`hpp₀`/`hcc₀` are stated in the `PlanePoly`/`ℝ × ℝ` representation (the same shape as
`edgeB_crossingInput`'s `hpp`/`hcc`, but quantified over the original `Γ₀` rather than over
`EdgeBCurve d`). `hCL` is the same parked multigraph crossing-lemma hypothesis as
`edgeB_crossingInput`; it is carried through, never discharged.

## The proof chain

Let `s` be the good shear scalar from `exists_good_shear Γ₀ P d hirr hdeg hpos`
(`ShearExists.lean:110`), which supplies, for every `h ∈ Γ₀`:
`pderiv 1 (shearPoly s h) ≠ 0` (`hpd`), `(shearPoly s h).totalDegree ≤ d` (`hdg`),
`Irreducible (shearPoly s h)` (`hir`); the fourth clause (x-separation `InjOn`) is not
needed here (already consumed by the leaves inside `edgeB_crossingInput`).

1. **Packaging.** `pkg : {h // h ∈ Γ₀} → EdgeBCurve d`,
   `pkg ⟨h, _⟩ := ⟨shearPoly s h, hir h _, hdg h _, hpd h _⟩`. Injective (`hpkg_inj`):
   two `pkg` outputs are equal iff their first components agree (`congrArg PSigma.fst`,
   the `Σ'` proof fields are propositional), and `shearPoly s` is injective
   (`shearPoly_injective`, below). `Γ_s := Γ₀.attach.image pkg : Finset (EdgeBCurve d)`.
2. **Sheared point set.** `P_s := P.map (shearPointEquiv s).toEmbedding`
   (`shearPointEquiv`, `Shear.lean:127`). `|P_s| = |P|` by `Finset.card_map`.
   `|Γ_s| = |Γ₀|` by `Finset.card_image_of_injective hpkg_inj` + `Finset.card_attach`.
3. **Point–point transport (`hpp₀ → hpp_s`).** For `p = shearPoint s p₀`, `q = shearPoint s q₀`
   (`p₀ q₀ ∈ P`), reindex the filter over `Γ_s`: `Finset.filter_image` pushes the predicate
   inside the `pkg`-image, `Finset.card_image_of_injective` drops the (injective) image, then
   `Finset.filter_congr` rewrites the per-curve membership
   `shearPoint s p₀ ∈ Z(shearPoly s h) ↔ p₀ ∈ Z(h)` (the `.symm` of `shearPoint_curve_iff`,
   `Shear.lean:137`), and `Finset.filter_attach` + `Finset.card_map`/`card_attach` collapse
   the attach filter to `(Γ₀.filter …).card`. Bounded by `hpp₀ p₀ … q₀ … (p₀ ≠ q₀)`.
4. **Curve–curve transport (`hcc₀ → hcc_s`).** For `Hᵢ = pkg ⟨hᵢ, _⟩`, the zero set
   `{z | evalPlane (shearPoly s hᵢ) z = 0}` equals `shearPoint s '' {z | evalPlane hᵢ z = 0}`
   (`image_shearPoint_evalPlaneZeroSet`, below). The intersection therefore equals
   `shearPoint s '' (Z(h₁) ∩ Z(h₂))` (`Set.image_inter` with `shearPoint` injective), and its
   `encard` equals `(Z(h₁) ∩ Z(h₂)).encard` (`Function.Injective.encard_image`). Bounded by
   `hcc₀ h₁ … h₂ … (h₁ ≠ h₂)`.
5. **Apply.** `edgeB_crossingInput hCL d M hM P_s Γ_s hpp_s hcc_s` gives the bound for the
   sheared arrangement with the curve family `Γ_s.image (fun H => evalPlaneZeroSet H.1)`.
6. **Transfer back.** `hLHS`: `Γ_s.image (Z ∘ ·.1) = Γ₀.image (fun h => Z (shearPoly s h))`
   (`Finset.image_image` + `Finset.attach_image_val`). `hsets`: this equals
   `(Γ₀.image Z).image (fun γ => shearPointEquiv s '' γ)` (each `Z (shearPoly s h) = e '' Z h`,
   `image_shearPoint_evalPlaneZeroSet`, by `Finset.ext`). Then
   `incidenceCount_map_image_equiv (shearPointEquiv s) P (Γ₀.image Z)` (the general bijection
   invariance, below) rewrites `incidenceCount P_s (Γ_s.image (Z∘·.1))` back to
   `incidenceCount P (Γ₀.image Z)`. Finally `rw [hinc, hcardP, hcardΓ] at hmain` recovers the
   original `|P|`, `|Γ₀|` in the bound. Same constant `edgeBCrossingConst d M`.

## New local content (three lemmas + the theorem)

- **`incidenceCount_map_image_equiv (e : α ≃ β) (P) (S)`** — general bijection-invariance:
  `incidenceCount (P.map e.toEmbedding) (S.image (fun γ => e '' γ)) = incidenceCount P S`.
  Proof via `incidenceCount_eq_sum` (`EdgeBE1.lean:416`): reindex the sum over `S.image (e''·)`
  by `Finset.sum_image` (the map `γ ↦ e '' γ` is injective, `Set.image_injective` + `e.injective`),
  then per-term `Finset.filter_map` + `Finset.card_map` reduce
  `|{q ∈ P.map e : q ∈ e '' γ}|` to `|{p ∈ P : p ∈ γ}|` via `Function.Injective.mem_set_image`.
  This is the one genuinely-new small bookkeeping lemma (step 6).
- **`image_shearPoint_evalPlaneZeroSet (s) (h)`** —
  `shearPoint s '' evalPlaneZeroSet h = evalPlaneZeroSet (shearPoly s h)`. From the curve
  coherence `shearPoint_curve_iff` (both directions; surjectivity of `shearPoint s` via the
  explicit inverse `shearPointInv`, `Shear.lean:110–118`).
- **`shearPoly_injective (s)`** — `Function.Injective (shearPoly s)`. `shearPoly s` is the
  underlying map of the algebra equivalence `shearAlgEquiv s` (`ShearIrreducible.lean:82`):
  `(shearAlgEquiv s).injective` + `shearAlgEquiv_apply` (`ShearIrreducible.lean:88`).
- **`edgeB_crossingInput_unsheared`** — the headline theorem (proof chain above).

## Landed leaves consumed (by exact name)

- **Top-level Edge-B output:** `PachDeZeeuw.Algebraic.edgeB_crossingInput`
  (`EdgeBCrossingInput.lean:78`), `edgeBCrossingConst` (`:65`).
- **Shear existence:** `exists_good_shear` (`ShearExists.lean:110`).
- **Shear coherence / bijection (`Shear.lean`):** `shearPoly`, `shearPoint`, `shearPointInv`,
  `shearPointEquiv` (`:127`), `shearPoint_curve_iff` (`:137`), `shearPoint_bijective` (`:122`),
  `shearPointInv_shearPoint` / `shearPoint_shearPointInv` (`:110`/`:115`).
- **Shear irreducibility / injectivity (`ShearIrreducible.lean`):** `shearAlgEquiv` (`:82`),
  `shearAlgEquiv_apply` (`:88`).
- **Incidence double-counting:** `incidenceCount_eq_sum` (`EdgeBE1.lean:416`);
  `PachSharir.incidenceCount` (`Theorem23.lean:38`); `evalPlaneZeroSet` (`LocalArc.lean:48`),
  `evalPlane` (`Bezout.lean:451`); `EdgeBCurve` (`EdgeBMultigraph.lean:63`).
- **mathlib:** `Finset.card_map`, `Finset.card_attach`, `Finset.card_image_of_injective`,
  `Finset.filter_map`, `Finset.filter_image`, `Finset.filter_congr`, `Finset.filter_attach`,
  `Finset.image_image`, `Finset.attach_image_val`, `Finset.sum_image`, `Finset.sum_congr`,
  `Set.image_injective`, `Set.image_inter`, `Function.Injective.mem_set_image`,
  `Function.Injective.encard_image`, `AlgEquiv.injective`.

## Gate results

- Build green: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBShearApply`
  → `Build completed successfully (8532 jobs).` No warnings/errors from this file. (The only
  build warnings are pre-existing parked `sorry`s and `unusedSimpArgs` lints in
  `PLCollarSeparation.lean`, `SzemerediTrotter.lean`, `PLArc.lean`, `PlaneArcSeparation.lean`,
  `CrossingLemmaAmplification.lean` — all off this file's closure.)
- `#print axioms edgeB_crossingInput_unsheared` = `[propext, Classical.choice, Quot.sound]`
  (verified in a transient `/tmp`-style axcheck module; same closure for
  `incidenceCount_map_image_equiv`, `image_shearPoint_evalPlaneZeroSet`, `shearPoly_injective`).
- No `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `axiom` in
  shipped code. Self-audit grep checklist clean (no heartbeat overrides; only the
  `linter.style.longLine` suppression, matching the sibling `EdgeBCrossingInput.lean`;
  no `nolint`; no `change`; namespace depth 2; 228-line file).
- Aggregator `CrossingLemma.lean` and all landed files left untouched (this file is a new
  leaf, not imported by anything yet).

## Boundary (what this does NOT do)

- Conditional on the parked `CrossingLemmaMultigraphStatement` (`hCL`), exactly as
  `edgeB_crossingInput`.
- Works in the `ℝ × ℝ` chart with `hpp₀`/`hcc₀` supplied over `Γ₀ : Finset PlanePoly`. It
  does NOT convert `PachSharir.TwoDegreesOfFreedom → (hpp₀, hcc₀)` (the separate downstream
  `edgeB-component-reduce`/`edgeB-chart-bridge` node, which additionally needs zero-set
  injectivity on `Γ₀`), nor lift to `EuclideanSpace` / arbitrary degree / the `D>2`, `e>1`
  ambient (design §5.3 downstream nodes). It removes precisely the `∂_y ≠ 0` precondition of
  `edgeB_crossingInput`, replacing the `EdgeBCurve d` family with an arbitrary irreducible
  degree-(`≤ d`, `≥ 1`) `PlanePoly` family.

PROVEN. No CONJECTURED / EMPIRICALLY-VERIFIED / HEURISTIC content: the constant is the
exhibited `edgeBCrossingConst d M`, and every transport step is fully formalized.
