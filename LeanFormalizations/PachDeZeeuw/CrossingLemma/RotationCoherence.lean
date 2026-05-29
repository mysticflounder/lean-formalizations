/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma

/-!
# PDZ BR-3b — the atomic rotation-splice coherence lemma (Front 2)

**This file is OFF the aggregator.** It is a standalone combinatorial lemma for
card BR-3b of the Pach–de Zeeuw route-(B) bridge. No geometry, no Jordan curve
theorem: it is pure `Equiv.Perm` / `finRotate` / `Equiv.swap` combinatorics on
`Fin (n+1)` vs `Fin n`, transported along the order isomorphisms supplied by
`CrossingLemma.PDZ.isoFin`.

## What it proves and why it is the right bridge

Recall the two combinatorial objects this connects:

* **Monolithic angular rotation** (`CrossingLemma.lean`): for a finite
  linearly-ordered type `β`, `rotationOfOrder L : Equiv.Perm β` is the
  cyclic-successor permutation — list `β` in `L`-increasing order and send each
  element to the next, the last wrapping to the first
  (`rotationOfOrder_apply_isoFin`). The vertex rotation
  `vertexRotation G hARR hp` is a `rotationOfOrder` of the angular order on a
  vertex's incident ends.

* **Incremental corner splice** (`CombinatorialMapEdgeInsertion.lean`): the
  single-edge insertion `insVertexPerm M c₁ c₂` acts on the vertex rotation by
  `swap (Sum.inl (M.vertexPerm c₁)) a · swap (Sum.inl (M.vertexPerm c₂)) b ·
  (σ ⊕ 1)` on `D ⊕ Fin 2`. Its **single-corner step** is
  `swap (Sum.inl (σ c)) a · (σ ⊕ 1)`: in cycle terms this threads the new dart
  `a` into `σ`'s cycle right after `c` (one checks `c ↦ a ↦ σ c`).

The **atomic rotation-splice coherence fact** says these two descriptions agree
for a single new element: if you augment the linear order `L` on `β` by
inserting a new element `x` (here `Sum.inr () : β ⊕ Unit`) at some rank, getting
`L'` on `β ⊕ Unit`, and if `c` is the immediate `L'`-predecessor of `x`, then

  `rotationOfOrder L' = Equiv.swap (Sum.inl (σ c)) (Sum.inr ()) * σ.sumCongr 1`,

with `σ := rotationOfOrder L`. This is exactly the single-corner-splice shape of
`insVertexPerm` (with `a := Sum.inr ()`, `Sum.inl (σ c) = Sum.inl (M.vertexPerm
c)`). It is the lemma that lets an `insertedEdgeMap`-tower built in angular order
reproduce the angular `vertexRotation` — the crux of BR-3b's OBSTRUCTION B(ii).

The hypotheses are minimal and exactly pin `L'`:
* `hmono` — `Sum.inl` is `L'`-strictly-monotone (i.e. `L'` restricts to `L` on
  `β`); the only remaining freedom in `L'` is the rank of `x`;
* `hpred` — `rotationOfOrder L' (Sum.inl c) = Sum.inr ()`, i.e. `x` is the
  immediate `L'`-successor of `c` (equivalently `c = pred_{L'}(x)`); this pins
  the rank of `x`.

## Proof architecture

* `succAbove_val`, `val_add_one_val` — value (`Fin.val`) normal forms.
* `crux`, `crux_fire` — the two `Fin (n+1)` index identities relating the
  `Fin (n+1)`-successor `(·+1)` to the `Fin n`-successor through `Fin.succAbove`,
  off and at the wrap/insertion point. (Verified for `n ≤ 8` before formalizing.)
* `finRotate_finCongr`, `permOfEquiv_finCongr` — `finRotate` is natural under the
  size-cast `finCongr`, so `rotationOfOrder L'` (indexed by `Fin (card (β⊕Unit))`)
  may be computed through any `Fin (card β + 1)`-indexed increasing enumeration.
* `enumInl` — the enumeration bridge: removing `x`'s slot from the `L'`-increasing
  enumeration of `β ⊕ Unit` recovers the `L`-increasing enumeration of `β`
  (both are *the* increasing map into the finset `{x}ᶜ`, so they coincide by
  `Finset.orderEmbOfFin_unique`).
* `rotationOfOrder_splice` — the main theorem, assembled by `Equiv.ext` and a
  three-way case split (the new element `x`; the predecessor slot, where the swap
  fires; the generic slot, handled by `crux`).
-/

set_option linter.style.longLine false

namespace CrossingLemma.PDZ

open Fin

/-! ### Value normal forms for `Fin` -/

/-- Value of `Fin.succAbove`: it is `i` below the gap `k`, and `i+1` at or above. -/
theorem succAbove_val {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    (k.succAbove i).val = if (i.val < k.val) then i.val else i.val + 1 := by
  rw [Fin.succAbove]
  split_ifs with h1 h2 h3
  · rfl
  · simp only [Fin.lt_def, Fin.val_castSucc] at h1; omega
  · simp only [Fin.lt_def, Fin.val_castSucc] at h1; omega
  · rfl

/-- Value of `(a + 1 : Fin (n+1))`: `0` at the top, else `a.val + 1`. -/
theorem val_add_one_val {n : ℕ} (a : Fin (n + 1)) :
    (a + 1).val = if a.val = n then 0 else a.val + 1 := by
  rw [Fin.val_add_one]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (by rw [h1]; rfl) h2
  · exact absurd (Fin.ext h3) h1
  · rfl

/-! ### The two `Fin (n+1)` index identities -/

/-- **Generic slot.** Away from the insertion point (`k.succAbove i + 1 ≠ k`),
the `Fin (n+1)`-successor of `k.succAbove i` is `k.succAbove` of the
`Fin n`-successor of `i`. -/
theorem succAbove_add_one {m : ℕ} (k : Fin (m + 1 + 1)) (i : Fin (m + 1))
    (h : (k.succAbove i) + 1 ≠ k) :
    (k.succAbove i) + 1 = k.succAbove (i + 1) := by
  apply Fin.ext
  have hk : k.val < m + 2 := k.isLt
  have hi : i.val < m + 1 := i.isLt
  have hv : ((k.succAbove i) + 1).val ≠ k.val := fun hc => h (Fin.ext hc)
  rw [val_add_one_val, succAbove_val] at hv ⊢
  have hi1 : ((i + 1 : Fin (m + 1))).val = if i.val = m then 0 else i.val + 1 :=
    val_add_one_val i
  rw [succAbove_val, hi1]
  split_ifs at hv ⊢ <;> omega

/-- **Insertion point.** At the slot whose `Fin (n+1)`-successor is `k` (i.e.
`x`'s predecessor slot), `k.succAbove` of the `Fin n`-successor of `i` is `k + 1`
(the slot just after the new element). -/
theorem succAbove_add_one_fire {m : ℕ} (k : Fin (m + 1 + 1)) (i : Fin (m + 1))
    (h : (k.succAbove i) + 1 = k) :
    k.succAbove (i + 1) = k + 1 := by
  apply Fin.ext
  have hk : k.val < m + 2 := k.isLt
  have hi : i.val < m + 1 := i.isLt
  have hv : ((k.succAbove i) + 1).val = k.val := by rw [h]
  rw [val_add_one_val, succAbove_val] at hv
  have hi1 : ((i + 1 : Fin (m + 1))).val = if i.val = m then 0 else i.val + 1 :=
    val_add_one_val i
  rw [succAbove_val, hi1, val_add_one_val (n := m + 1) k]
  split_ifs at hv ⊢ <;> omega

/-! ### Generic-`N` repackaging of the index identities

`succAbove_add_one` / `succAbove_add_one_fire` are stated for `Fin (m+1+1)` and
`Fin (m+1)`, and use the `Fin`-successor `(· + 1)` on the *small* fin `Fin (m+1)`, which
requires the carrier to be syntactically a successor (the `OfNat (Fin _) 1` instance).
Downstream (`rotationOfOrder_splice`) the small carrier is `Fin (Fintype.card β)`, not in
`m+1` form, so we repackage using the **rotation successor `finRotate N`** in place of
`(· + 1)` (these coincide on `Fin (m+1)` by `finRotate_succ_apply`, but `finRotate N` is
well-typed for every `N`, needing no `OfNat`). The empty case `N = 0` is dispatched by
`Fin.elim0`. This lets the identities apply at `Fin (card β + 1)` / `Fin (card β)` with no
manual size casts — and `finRotate N i` is exactly the index that `rotationOfOrder`
produces. -/

/-- Generic-`N` form of `succAbove_add_one`, with the small-fin successor written as
`finRotate N` (so no `OfNat (Fin N) 1` instance is needed). -/
theorem succAbove_finRotate {N : ℕ} (k : Fin (N + 1)) (i : Fin N)
    (h : (k.succAbove i) + 1 ≠ k) :
    (k.succAbove i) + 1 = k.succAbove (finRotate N i) := by
  cases N with
  | zero => exact i.elim0
  | succ m => rw [finRotate_succ_apply]; exact succAbove_add_one k i h

/-- Generic-`N` form of `succAbove_add_one_fire`, with the small-fin successor written as
`finRotate N`. -/
theorem succAbove_finRotate_fire {N : ℕ} (k : Fin (N + 1)) (i : Fin N)
    (h : (k.succAbove i) + 1 = k) :
    k.succAbove (finRotate N i) = k + 1 := by
  cases N with
  | zero => exact i.elim0
  | succ m => rw [finRotate_succ_apply]; exact succAbove_add_one_fire k i h

/-! ### `finRotate` is natural under the size cast `finCongr` -/

/-- `finRotate` commutes with the size-cast equivalence `finCongr`. -/
theorem finRotate_finCongr {a b : ℕ} (h : a = b) (i : Fin a) :
    finRotate b (finCongr h i) = finCongr h (finRotate a i) := by
  subst h; simp [finCongr]

/-- `permOfEquiv` is invariant under precomposing the index equivalence with a
size-cast `finCongr`. Hence the rotation may be computed through any
`Fin (card + 1)`-indexed increasing enumeration. -/
theorem permOfEquiv_finCongr {a b : ℕ} (h : a = b) {β : Type*} (e : Fin a ≃ β) :
    permOfEquiv ((finCongr h).symm.trans e) = permOfEquiv e := by
  subst h; congr 1

/-! ### The augmented setup and the enumeration bridge

Throughout: `β` a finite linear order with `L : LinearOrder β`, `n := card β`,
and `L'` a linear order on `β ⊕ Unit` extending `L` on the `Sum.inl` copy. The
new element is `x := Sum.inr ()`. We write `cardSucc` for
`card (β ⊕ Unit) = n + 1`. -/

section Augmented

variable {β : Type*} [Fintype β] (L : LinearOrder β) (L' : LinearOrder (β ⊕ Unit))

/-- `card (β ⊕ Unit) = card β + 1`. -/
theorem card_sum_unit : Fintype.card (β ⊕ Unit) = Fintype.card β + 1 := by
  rw [Fintype.card_sum, Fintype.card_unit]

/-- The `L'`-increasing enumeration of `β ⊕ Unit`, re-indexed by `Fin (card β + 1)`
through the size cast. Kept as a bare `Equiv` (the `Sum` order instance on the
codomain is *not* `L'`, so we carry `L'`-monotonicity separately in `enumSucc_strictMono`). -/
noncomputable def enumSucc : Fin (Fintype.card β + 1) ≃ (β ⊕ Unit) :=
  (finCongr (card_sum_unit (β := β))).symm.trans (isoFin L').toEquiv

/-- `enumSucc` is `L'`-strictly-monotone. -/
theorem enumSucc_strictMono :
    @StrictMono (Fin (Fintype.card β + 1)) (β ⊕ Unit) _ L'.toPreorder (enumSucc L') := by
  letI := L'
  intro a b hab
  simp only [enumSucc, Equiv.trans_apply, OrderIso.coe_toEquiv]
  apply (isoFin L').strictMono
  simpa [finCongr] using hab

/-- `rotationOfOrder L'` is computed by `enumSucc`, i.e. `permOfEquiv` of the
re-indexed enumeration. -/
theorem rotationOfOrder_eq_permOfEquiv_enumSucc :
    rotationOfOrder L' = permOfEquiv (enumSucc L') := by
  rw [enumSucc, permOfEquiv_finCongr]
  rfl

/-- The position (rank) of the new element `Sum.inr ()` in the `L'`-order. -/
noncomputable def newRank : Fin (Fintype.card β + 1) := (enumSucc L').symm (Sum.inr ())

/-- **Enumeration bridge.** Deleting the new element's slot from the `L'`-increasing
enumeration of `β ⊕ Unit` recovers the `L`-increasing enumeration of `β`: for every
`i`, `enumSucc L'` at `(newRank).succAbove i` is `Sum.inl (isoFin L i)`. Proven by
`Finset.orderEmbOfFin_unique` — both sides are *the* `L'`-increasing map of
`Fin (card β)` into the finset `{Sum.inr ()}ᶜ`. -/
theorem enumInl
    (hext : ∀ a b : β, L'.lt (Sum.inl a) (Sum.inl b) ↔ L.lt a b) (i : Fin (Fintype.card β)) :
    enumSucc L' ((newRank L').succAbove i) = Sum.inl (isoFin L i) := by
  classical
  -- It suffices to prove the position identity on the `Fin` side:
  --   g i := (enumSucc L').symm (inl (isoFin L i)) equals (newRank).succAbove.
  -- Then apply `enumSucc L'` to both sides.
  set g : Fin (Fintype.card β) → Fin (Fintype.card β + 1) :=
    fun i => (enumSucc L').symm (Sum.inl (isoFin L i)) with hg
  suffices hgeq : g = (newRank L').succAbove by
    have hgi := congrFun hgeq i
    rw [hg] at hgi
    -- hgi : (enumSucc L').symm (inl (isoFin L i)) = (newRank).succAbove i
    rw [← hgi, Equiv.apply_symm_apply]
  -- Prove g = succAbove via uniqueness of the increasing enum of `{newRank}ᶜ` in `Fin _`
  -- (canonical `Fin` order — no `Sum` order instance is involved here).
  set s : Finset (Fin (Fintype.card β + 1)) := {newRank L'}ᶜ with hs
  have hcard : s.card = Fintype.card β := by
    rw [hs, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]; omega
  -- g maps into s
  have hgs : ∀ j, g j ∈ s := by
    intro j
    rw [hs, Finset.mem_compl, Finset.mem_singleton, hg]
    intro hc
    have hcc : Sum.inl (isoFin L j) = enumSucc L' (newRank L') := by
      rw [← hc, Equiv.apply_symm_apply]
    rw [newRank, Equiv.apply_symm_apply] at hcc
    exact Sum.inl_ne_inr hcc
  -- g strict-mono on `Fin`. We never let instance synthesis pick a `<` on `β ⊕ Unit`:
  -- the ambient `Sum.instPreorderSum` (built from `L` on `β`, which is available to
  -- synthesis because the hypothesis `L : LinearOrder β` sits in the local context) is
  -- a trap — it is *not* `L'`. We therefore pin the codomain preorder to `L'.toPreorder`
  -- explicitly via `@StrictMono.lt_iff_lt` on the already-proven `enumSucc_strictMono`,
  -- whose codomain order is intrinsically `L'`. The `L'`-comparison of the two
  -- `enumSucc`-images reduces (by `Equiv.apply_symm_apply`) to
  -- `L'.lt (inl (isoFin L a)) (inl (isoFin L b))`, which `hext` + `isoFin_lt` discharge;
  -- reflecting back through the `enumSucc` strict-mono bijection yields the `Fin`-`<` goal.
  have hgmono : StrictMono g := by
    intro a b hab
    rw [hg]
    simp only
    have key : @LT.lt (β ⊕ Unit) L'.toPreorder.toLT
        (enumSucc L' ((enumSucc L').symm (Sum.inl (isoFin L a))))
        (enumSucc L' ((enumSucc L').symm (Sum.inl (isoFin L b)))) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact (hext _ _).mpr (isoFin_lt L hab)
    exact (@StrictMono.lt_iff_lt _ _ _ L'.toPreorder _ (enumSucc_strictMono L') _ _).mp key
  -- succAbove maps into s and is strict-mono
  have hsas : ∀ j, (newRank L').succAbove j ∈ s := by
    intro j; rw [hs, Finset.mem_compl, Finset.mem_singleton]
    exact Fin.succAbove_ne (newRank L') j
  -- both equal s.orderEmbOfFin
  have e₁ := Finset.orderEmbOfFin_unique hcard hgs hgmono
  have e₂ := Finset.orderEmbOfFin_unique hcard hsas (Fin.strictMono_succAbove (newRank L'))
  rw [e₁, e₂]

/-- `enumSucc L'` at the new element's rank is the new element. -/
theorem enumSucc_newRank : enumSucc L' (newRank L') = Sum.inr () := by
  rw [newRank, Equiv.apply_symm_apply]

/-- The cyclic-successor permutation `rotationOfOrder L'`, evaluated through the
re-indexed enumeration `enumSucc L'`: it is `enumSucc` of the `Fin (card β + 1)`-rotation
of the inverse-image index. -/
theorem rotationOfOrder_apply_enumSucc (y : β ⊕ Unit) :
    rotationOfOrder L' y =
      enumSucc L' (finRotate (Fintype.card β + 1) ((enumSucc L').symm y)) := by
  rw [rotationOfOrder_eq_permOfEquiv_enumSucc, permOfEquiv, Equiv.trans_apply,
    Equiv.trans_apply]

/-- **The atomic rotation-splice coherence lemma.** Let `L` be a linear order on the
fintype `β` with cyclic-successor permutation `σ := rotationOfOrder L`, and let `L'` be a
linear order on `β ⊕ Unit` that:

* (`hmono`) restricts to `L` on the `Sum.inl` copy of `β` — i.e. `Sum.inl` is
  `L'`-strictly-monotone; the only freedom left in `L'` is the rank of the new element
  `x := Sum.inr ()`;
* (`hpred`) places `x` immediately after `Sum.inl c` in the `L'`-order — i.e.
  `rotationOfOrder L' (Sum.inl c) = Sum.inr ()`, pinning the rank of `x`.

Then the cyclic-successor permutation of `L'` is the single-corner splice of `σ`:

  `rotationOfOrder L' = Equiv.swap (Sum.inl (σ c)) (Sum.inr ()) * σ.sumCongr 1`,

which threads the new dart `x` into `σ`'s cycle right after `c` (`c ↦ x ↦ σ c`). This is
exactly the single-corner shape of `insVertexPerm`. The proof is `Equiv.ext` and a
three-way split on the slot of the argument `y`: the new element `x`; the predecessor
slot of `x` (where the swap fires); and every generic slot. The `Fin`-index bookkeeping
is supplied by `succAbove_finRotate` / `succAbove_finRotate_fire`, and the translation
between the `Fin (card β + 1)`-rotation and the `β ⊕ Unit` statement by `enumInl`.

No nonemptiness hypothesis on `β` is needed: the hypothesis `c : β` already forces `β`
nonempty, and the `card β = 0` corner is impossible (`Fin (card β)` would be empty). -/
theorem rotationOfOrder_splice (c : β)
    (hmono : ∀ a b : β, L'.lt (Sum.inl a) (Sum.inl b) ↔ L.lt a b)
    (hpred : rotationOfOrder L' (Sum.inl c) = Sum.inr ()) :
    rotationOfOrder L' =
      Equiv.swap (Sum.inl ((rotationOfOrder L) c)) (Sum.inr ())
        * (rotationOfOrder L).sumCongr 1 := by
  classical
  set σ := rotationOfOrder L with hσ
  -- `c`'s rank index in the `L`-enumeration of `β`.
  set ic : Fin (Fintype.card β) := (isoFin L).symm c with hic
  have hceq : isoFin L ic = c := by rw [hic, OrderIso.apply_symm_apply]
  -- `Sum.inl c` sits at slot `(newRank).succAbove ic` of `enumSucc L'`.
  have hsymm_c : (enumSucc L').symm (Sum.inl c) = (newRank L').succAbove ic := by
    apply (enumSucc L').injective
    rw [Equiv.apply_symm_apply, ← hceq, enumInl L L' hmono ic]
  -- `σ c = isoFin L (finRotate (card β) ic)` (the `L`-cyclic successor of `c`).
  have hσc : σ c = isoFin L (finRotate (Fintype.card β) ic) := by
    rw [hσ, ← hceq, rotationOfOrder_apply_isoFin]
  -- **Fire fact**: `x`'s predecessor slot is exactly `ic`'s slot, one below `newRank`.
  have hfire : (newRank L').succAbove ic + 1 = newRank L' := by
    have h := hpred
    rw [rotationOfOrder_apply_enumSucc, hsymm_c,
      finRotate_succ_apply, ← enumSucc_newRank L'] at h
    exact (enumSucc L').injective h
  -- Assemble by `Equiv.ext`, casing on the argument.
  ext y
  rw [rotationOfOrder_apply_enumSucc, Equiv.Perm.mul_apply, Equiv.sumCongr_apply]
  cases y with
  | inr u =>
    -- The new element `x = Sum.inr u`. LHS rotates `newRank` forward; RHS is `Sum.inl (σ c)`.
    obtain rfl : u = () := rfl
    rw [show (enumSucc L').symm (Sum.inr ()) = newRank L' from rfl, finRotate_succ_apply,
      ← succAbove_finRotate_fire (newRank L') ic hfire, enumInl L L' hmono,
      Sum.map_inr, Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_right, hσc]
  | inl a =>
    -- A slot `Sum.inl a`. Write `a = isoFin L i` with `i := (isoFin L).symm a`.
    set i : Fin (Fintype.card β) := (isoFin L).symm a with hi
    have haeq : isoFin L i = a := by rw [hi, OrderIso.apply_symm_apply]
    have hsymm_a : (enumSucc L').symm (Sum.inl a) = (newRank L').succAbove i := by
      apply (enumSucc L').injective
      rw [Equiv.apply_symm_apply, ← haeq, enumInl L L' hmono i]
    -- `σ a = isoFin L (finRotate (card β) i)`.
    have hσa : σ a = isoFin L (finRotate (Fintype.card β) i) := by
      rw [hσ, ← haeq, rotationOfOrder_apply_isoFin]
    rw [hsymm_a, finRotate_succ_apply, Sum.map_inl, hσa]
    by_cases hfi : (newRank L').succAbove i + 1 = newRank L'
    · -- Fire slot: forced `i = ic`, hence `a = c`; the swap sends `Sum.inl (σ c)` to `x`.
      have hii : i = ic := by
        have : (newRank L').succAbove i = (newRank L').succAbove ic := by
          have := hfi.trans hfire.symm
          exact add_right_cancel this
        exact (Fin.succAbove_right_inj).mp this
      rw [hfi, enumSucc_newRank, hii, ← hσc]
      exact (Equiv.swap_apply_left _ _).symm
    · -- Generic slot: the swap does not fire (target ≠ `Sum.inl (σ c)`, ≠ `x`).
      rw [succAbove_finRotate (newRank L') i hfi, enumInl L L' hmono]
      have hne_ic : i ≠ ic := by
        intro hcon; exact hfi (by rw [hcon]; exact hfire)
      have hne1 : (Sum.inl (isoFin L (finRotate (Fintype.card β) i)) : β ⊕ Unit)
          ≠ Sum.inl (σ c) := by
        rw [hσc, ne_eq, Sum.inl.injEq]
        intro hcon
        exact hne_ic ((finRotate _).injective ((isoFin L).injective hcon))
      have hne2 : (Sum.inl (isoFin L (finRotate (Fintype.card β) i)) : β ⊕ Unit)
          ≠ Sum.inr () :=
        Sum.inl_ne_inr
      exact (Equiv.swap_apply_of_ne_of_ne hne1 hne2).symm

end Augmented

end CrossingLemma.PDZ
