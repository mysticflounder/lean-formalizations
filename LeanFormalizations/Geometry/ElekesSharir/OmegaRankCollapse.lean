/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# ω-rank collapse (generic linear-algebra lemma L4)

A ruling of a nondegenerate regulus is a conic inside a projective plane
`H ⊂ ℙ⁵` in the Klein quadric, and `H` is cut out by a `3`-dimensional space `W`
of linear forms. Pulling a form `ℓ ∈ W` back through the Plücker map produces an
expression `ω(ℓ)·(|q|² − |p|²) + affine(p,q)`, where `ω : W → ℝ` is the linear
functional reading the `M₃`-coefficient. The combinatorial pay-off is that there
are always **at least two** independent norm-free pullbacks: forms in `ker ω`.

The single mathematical fact this needs is the rank–nullity bound

  `dim W = 3` and `ω : W → ℝ` linear  ⟹  `dim (ker ω) ≥ 2`,

because `range ω ≤ ℝ` has dimension at most `1`. This is the content of
**L4 (ω-rank collapse)** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma B, verified chain step 1).

This file states and proves that bound generically: for any finite-dimensional
`K`-vector space `W` and any linear functional `ω : W →ₗ[K] K`,

  `Module.finrank K W − 1 ≤ Module.finrank K (LinearMap.ker ω)`,

and specialises it to `dim W = 3 ⟹ dim ker ω ≥ 2`.

The accompanying *pullback non-degeneracy* statement of the doc (Lemma B step 1:
the only form pulling back to the zero affine function is `0`) is recorded as the
abstract injectivity hypothesis it really is — see `pullback_nondegenerate`.

References:
* Rank–nullity: `LinearMap.finrank_range_add_finrank_ker`
  (`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`).
* `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma B, step 1.
-/

namespace ElekesSharir

open Module

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Rank-nullity collapse for a functional.** For a linear functional
`ω : W →ₗ[K] K` on a finite-dimensional space `W`, the kernel has dimension at
least `dim W − 1`, because the range sits inside the one-dimensional space `K`.

This is the generic engine behind L4 (ω-rank collapse): pulling forms back
through Plücker turns "norm-free" into "lies in `ker ω`". -/
theorem finrank_ker_functional_ge (ω : W →ₗ[K] K) :
    finrank K W - 1 ≤ finrank K (LinearMap.ker ω) := by
  have hrn : finrank K (LinearMap.range ω) + finrank K (LinearMap.ker ω)
      = finrank K W := LinearMap.finrank_range_add_finrank_ker ω
  have hrange : finrank K (LinearMap.range ω) ≤ 1 := by
    calc finrank K (LinearMap.range ω)
        ≤ finrank K K := Submodule.finrank_le _
      _ = 1 := finrank_self K
  omega

/-- **L4 (ω-rank collapse), main case.** If `dim W = 3` and `ω : W →ₗ[K] K` is a
linear functional, then `dim (ker ω) ≥ 2`: there are always at least two
independent norm-free pullbacks.

This is `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
Lemma B, verified chain step 1 ("Rank–nullity: dim ker ω ≥ 2"). -/
theorem finrank_ker_ge_two_of_finrank_eq_three (ω : W →ₗ[K] K)
    (hW : finrank K W = 3) :
    2 ≤ finrank K (LinearMap.ker ω) := by
  have := finrank_ker_functional_ge ω
  omega

omit [FiniteDimensional K W] in
/-- **Pullback non-degeneracy (L4, abstract form).** The doc's side-condition
("the only form pulling back to the zero affine function is `0`") is, abstractly,
the statement that the pullback map `pull : W →ₗ[K] A` from forms to affine
functions is *injective*. Under that hypothesis the norm-free packet `ker ω`
embeds (as `pull` restricted to it) into the affine functions with no kernel, so
distinct norm-free forms give distinct affine constraints.

We state it as the literal consequence: an injective pullback sends a nonzero
form to a nonzero affine function. The geometric content (a nonzero constant
pullback is a pure `D₃`-form, excluded because no ES line satisfies `D₃ = 0`)
is the *justification* that `pull` is injective on the relevant subspace; it is
supplied at the assembly site, not here. -/
theorem pullback_nondegenerate {A : Type*} [AddCommGroup A] [Module K A]
    (pull : W →ₗ[K] A) (hpull : Function.Injective pull) {ℓ : W} (hℓ : ℓ ≠ 0) :
    pull ℓ ≠ 0 := by
  intro h
  exact hℓ (hpull (by simpa using h))

end ElekesSharir
