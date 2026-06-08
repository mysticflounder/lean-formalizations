/-
Combinatorial orbit-delta engine for the drawing→combinatorial-map bridge.

A reusable orbit-count engine for the drawing→combinatorial-map bridge,
independent of the vertex rotation. Pure permutation combinatorics — NO geometry, NO Jordan curve
theorem. Built on the vendored `CombinatorialMap` carrier (mathlib PR #16074).

## Status (this session)

**D1-B — COMPLETE, sorry-free, axiom-clean** (`[propext, Classical.choice,
Quot.sound]`, verified by `#print axioms`). The transposition–cycle dichotomy for
the `SameCycle` orbit count `orbitCount f := Fintype.card (Quotient
(SameCycle.setoid f))`:

  `orbitCount_swap_mul` : for `p ≠ q`,
    * `f.SameCycle p q  → orbitCount (swap p q * f) = orbitCount f + 1`  (split)
    * `¬ f.SameCycle p q → orbitCount f = orbitCount (swap p q * f) + 1`  (merge)

Proven via two independent routes that meet:
  * the **bridge** `orbitCount_eq`:
      `orbitCount f = (card α − #support) + #cycleFactorsFinset`
    (explicit `Equiv` of the quotient with `{fixed points} ⊕ cycleFactorsFinset`),
    giving the SIGN/parity engine `sign_eq_orbitCount_parity` and the parity flip;
  * the **setoid-join** magnitude bound (`joinSetoid` = `f`'s partition with the
    `p ~ q` classes identified): monotonicity + a one-link card bound pin
    `|Δ orbitCount| ≤ 1` with NO cycle combinatorics; the parity flip then forces
    exactly `±1`. Direction: the link is redundant when `f.SameCycle p q`
    (`join_eq_of_sameCycle`) ⇒ `+1`; the joining lemma
    `sameCycle_swap_mul_of_not_sameCycle` (the swap fires at the cycle
    wrap-around) reduces the merge case to the split case on `swap p q * f`.

Carrier interface (sorry-free): `card_{vertex,edge,face}_eq_orbitCount` identify
the carrier `Vertex`/`Edge`/`Face` counts with `orbitCount` of the structure
permutations — the handle through which D1-A feeds `orbitCount_swap_mul` into
Euler bookkeeping.

**D1-A — COMPLETE, sorry-free, axiom-clean** (`[propext, Classical.choice,
Quot.sound]`, verified by `#print axioms`). D1-A enlarges the darts to `D ⊕ Fin 2`
(two new darts `a := Sum.inr 0`, `b := Sum.inr 1`), sets `α' = α ⊕ (a b)`, splices
`σ → σ'` at corners `c₁` (tail), `c₂` (head) with `c₁ ≠ c₂`, and forces
`φ' = σ'⁻¹ * α'`. Concretely:
  * `insEdgePerm  = α.sumCongr (swap 0 1)`  — a fixed-point-free involution;
  * `insVertexPerm = swap (inl σc₁) a · swap (inl σc₂) b · (σ ⊕ 1)` — threads `a`
    after `c₁` and `b` after `c₂` in the rotation;
  * `insFacePerm  = insVertexPerm⁻¹ · insEdgePerm` (forced).
The bundle is packaged as `insertedEdgeMap : CombinatorialMap (D ⊕ Fin 2)`.

Deltas (all reduced to the D1-B `orbitCount_swap_mul` engine):
  1. **Structure axioms** — `insertedEdgeMap` (`face·edge·vertex = 1` automatic via
     `α'α' = 1`; involutivity + fpf of `α'` from the two `sumCongr` summands).
  2. **`card_edge_insertedEdgeMap`**: `|E'| = |E| + 1` (via `orbitCount_sumCongr`,
     one new `α'`-orbit `{a,b}`).
  3. **`card_vertex_insertedEdgeMap`**: `|V'| = |V|` — this splice threads `a,b`
     into existing rotations (each new dart joins one vertex orbit; vertices never
     fuse), proved by two *merge* applications of `orbitCount_swap_mul`.
  4. **`card_face_insertedEdgeMap`** (the heart): `|F'| = |F| + 1` iff `c₁,c₂` share
     a `facePerm`-orbit (a face *splits*), else `|F| = |F'| + 1` (faces *merge*).
     Proven by the product form `φ' = swap (inl c₁) a · swap (inl c₂) b · (φ ⊕ (a b))`
     (`insFacePerm_eq_product`): the inner swap always merges `{a,b}` into `c₂`'s
     face (→ `F`); the outer swap then splits iff `c₁` and `c₂` shared a face
     (`insFacePermStep1_sameCycle_iff`, via the merge characterization
     `sameCycle_swap_mul_iff_of_not_sameCycle`).
  5. **`eulerCharacteristic_insertedEdgeMap_le`**: `χ' ≤ χ` always, with
     `χ' = χ` exactly in the facial (same-face) case and `χ' = χ − 2` otherwise.

Reusable orbit-engine additions: `orbitCount_sumCongr` (additivity over `sumCongr`)
and `sameCycle_swap_mul_iff_of_not_sameCycle` (the merge same-cycle dichotomy).
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Sign
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic

open Equiv Equiv.Perm

namespace CombinatorialMap.EdgeInsertion

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The `SameCycle` quotient of a permutation on a `Fintype` is finite. (Matches
the carrier's `Fintype M.Vertex` instance, also via `Fintype.ofFinite`.) -/
noncomputable instance instFintypeQuotientSameCycle (f : Perm α) :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid f)) :=
  Fintype.ofFinite _

/-- The number of orbits of a permutation `f` acting on `α`, i.e. the number of
`SameCycle` equivalence classes (fixed points count as singleton orbits). This is
the abstract cardinality the carrier uses for `Vertex`/`Edge`/`Face`. -/
noncomputable def orbitCount (f : Perm α) : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f))

/-! ### The bridge: `orbitCount` in terms of support and cycle factors

`orbitCount f = (card α − #support) + #cycleFactorsFinset`. The `SameCycle`
quotient splits as fixed-point singleton classes (one per non-support point) plus
support classes (one per cycle factor of `f`). We exhibit an explicit
`Equiv` to `{x // f x = x} ⊕ f.cycleFactorsFinset` and count. -/

/-- Forward map of the bridge equivalence, on representatives: a fixed point goes
to itself in the left summand; a moved point goes to its cycle factor on the
right. -/
private noncomputable def bridgeToFun (f : Perm α) (x : α) :
    {x : α // f x = x} ⊕ (f.cycleFactorsFinset : Finset (Perm α)) :=
  if hx : f x = x then Sum.inl ⟨x, hx⟩
  else Sum.inr ⟨f.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
    (Equiv.Perm.mem_support.mpr hx)⟩

/-- `bridgeToFun` is constant on `SameCycle` classes, hence descends to the
quotient. -/
private lemma bridgeToFun_sameCycle (f : Perm α) {x y : α}
    (h : f.SameCycle x y) : bridgeToFun f x = bridgeToFun f y := by
  unfold bridgeToFun
  by_cases hx : f x = x
  · -- x fixed ⟹ x = y, so y fixed too
    have hxy : x = y := h.eq_of_left hx
    subst hxy
    rw [dif_pos hx]
  · -- x moved ⟹ y moved, same cycle factor
    have hy : f y ≠ y := by
      intro hyfix
      exact hx (h.eq_of_right hyfix ▸ hyfix)
    rw [dif_neg hx, dif_neg hy]
    congr 1
    exact Subtype.ext h.cycleOf_eq

/-- The bridge equivalence: the `SameCycle` quotient is fixed points plus cycle
factors. -/
private noncomputable def bridgeEquiv (f : Perm α) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ≃
      ({x : α // f x = x} ⊕ (f.cycleFactorsFinset : Finset (Perm α))) where
  toFun := Quotient.lift (bridgeToFun f) (fun _ _ h => bridgeToFun_sameCycle f h)
  invFun := fun s => s.elim
    (fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid f) x.1)
    (fun σ => Quotient.mk (Equiv.Perm.SameCycle.setoid f)
      (((Equiv.Perm.mem_cycleFactorsFinset_iff.mp σ.2).1.nonempty_support).choose))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x =>
      change Sum.elim _ _ (bridgeToFun f x) = _
      unfold bridgeToFun
      by_cases hx : f x = x
      · rw [dif_pos hx]; rfl
      · rw [dif_neg hx]
        change Quotient.mk _ _ = Quotient.mk _ x
        -- the chosen point of (cycleOf x).support is SameCycle with x
        have hmem := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp
          (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
            (Equiv.Perm.mem_support.mpr hx))).1.nonempty_support.choose_spec
        rw [Quotient.eq]
        change f.SameCycle _ x
        exact ((Equiv.Perm.mem_support_cycleOf_iff' hx).mp hmem).symm
  right_inv := by
    intro s
    cases s with
    | inl x =>
      change Quotient.lift _ _ (Quotient.mk _ x.1) = _
      change bridgeToFun f x.1 = _
      unfold bridgeToFun
      rw [dif_pos x.2]
    | inr σ =>
      change Quotient.lift _ _ (Quotient.mk _ _) = _
      change bridgeToFun f _ = _
      set a := (((Equiv.Perm.mem_cycleFactorsFinset_iff.mp σ.2).1.nonempty_support).choose)
        with ha
      have haσ : a ∈ (σ.1).support :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp σ.2).1.nonempty_support.choose_spec
      have hfa : f a ≠ a := by
        have h2 := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp σ.2).2 a haσ
        rw [Equiv.Perm.mem_support] at haσ
        rw [← h2]; exact haσ
      unfold bridgeToFun
      rw [dif_neg hfa]
      congr 1
      apply Subtype.ext
      change f.cycleOf a = σ.1
      exact (Equiv.Perm.cycle_is_cycleOf haσ σ.2).symm

/-- The number of fixed points of `f` is `card α − #support`. -/
private lemma card_fixed_eq (f : Perm α) :
    Fintype.card {x : α // f x = x} = Fintype.card α - f.support.card := by
  classical
  -- partition `univ` by membership in `support`
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (p := fun x => x ∈ f.support)
  rw [Finset.card_univ] at hpart
  -- the support-filter is `support` itself
  have hpos : ((Finset.univ : Finset α).filter (fun x => x ∈ f.support)) = f.support := by
    ext x; simp
  -- the complement-filter is the fixed-point subtype's finset
  have hneg : ((Finset.univ : Finset α).filter (fun x => x ∉ f.support)).card
      = Fintype.card {x : α // f x = x} := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mem_support]
    tauto
  rw [hpos, hneg] at hpart
  omega

/-- **The bridge.** `orbitCount f = (card α − #support) + #cycleFactorsFinset`. -/
theorem orbitCount_eq (f : Perm α) :
    orbitCount f = (Fintype.card α - f.support.card) + f.cycleFactorsFinset.card := by
  unfold orbitCount
  rw [Fintype.card_congr (bridgeEquiv f), Fintype.card_sum, Fintype.card_coe, card_fixed_eq]

/-- `Multiset.card f.cycleType = #f.cycleFactorsFinset`. -/
lemma card_cycleType_eq_card_cycleFactorsFinset (f : Perm α) :
    Multiset.card f.cycleType = f.cycleFactorsFinset.card := by
  rw [Equiv.Perm.cycleType, Multiset.card_map]; rfl

/-- The bridge in `cycleType` form: `orbitCount f = card α − #support + #cycleType`. -/
theorem orbitCount_eq_cycleType (f : Perm α) :
    orbitCount f = (Fintype.card α - f.support.card) + Multiset.card f.cycleType := by
  rw [orbitCount_eq, card_cycleType_eq_card_cycleFactorsFinset]

/-! ### Parity of `orbitCount` flips under a transposition

From `sign (swap p q * π) = − sign π` and `sign f = (−1)^(#support + #cycleType)`,
the parity of `#support + #cycleType` flips, hence (via the bridge) the parity of
`orbitCount` flips. This pins the ±1 to be ODD; combined with a magnitude bound it
gives exactly ±1. -/

/-- `support.card ≤ card α` for any permutation. -/
private lemma support_card_le (f : Perm α) : f.support.card ≤ Fintype.card α := by
  rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)

/-- `(-1 : ℤˣ)` to powers differing by an even amount agree. -/
private lemma neg_one_zpow_add_two_mul (a k : ℕ) :
    (-1 : ℤˣ) ^ (a + 2 * k) = (-1 : ℤˣ) ^ a := by
  rw [pow_add, pow_mul]
  simp [pow_succ]

/-- The sign of `f` as a parity of `orbitCount f` and `card α`:
`sign f = (-1) ^ (orbitCount f + card α)`. -/
lemma sign_eq_orbitCount_parity (f : Perm α) :
    Equiv.Perm.sign f = (-1 : ℤˣ) ^ (orbitCount f + Fintype.card α) := by
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType]
  -- exponents: LHS `s + C`, RHS `orbitCount + N = (N - s + C) + N`.
  have hle := support_card_le f
  set s := f.support.card
  set C := Multiset.card f.cycleType
  set N := Fintype.card α
  -- the RHS exponent equals `(s + C) + 2 * (N - s)`
  have hexp : orbitCount f + N = (s + C) + 2 * (N - s) := by
    rw [orbitCount_eq_cycleType]; omega
  rw [hexp, neg_one_zpow_add_two_mul]

/-- `(-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ (a % 2)`. -/
private lemma neg_one_pow_eq_pow_mod_two (a : ℕ) :
    (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ (a % 2) := by
  conv_lhs => rw [show a = a % 2 + 2 * (a / 2) from by omega]
  rw [neg_one_zpow_add_two_mul]

/-- Two `(-1 : ℤˣ)` powers agree iff the exponents have equal parity. -/
private lemma neg_one_zpow_eq_iff_parity (a b : ℕ) :
    ((-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b) ↔ (a % 2 = b % 2) := by
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b]
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      rw [ha, hb] at h ⊢ <;> first | rfl | (exfalso; revert h; decide)
  · intro h; rw [h]

/-- **Parity flip.** `orbitCount (swap p q * f)` and `orbitCount f` have opposite
parity when `p ≠ q`. -/
lemma orbitCount_swap_mul_parity (f : Perm α) {p q : α} (hpq : p ≠ q) :
    orbitCount (Equiv.swap p q * f) % 2 ≠ orbitCount f % 2 := by
  intro hpar
  -- sign(swap p q * f) = - sign f, but the parity of the orbit-count-based exponents agree
  have hsg : Equiv.Perm.sign (Equiv.swap p q * f) = - Equiv.Perm.sign f := by
    rw [map_mul, Equiv.Perm.sign_swap hpq]; simp
  rw [sign_eq_orbitCount_parity, sign_eq_orbitCount_parity] at hsg
  -- both sides as ±1 powers; the parities of exponents agree by hpar, contradicting the sign
  have hexp_par : (orbitCount (Equiv.swap p q * f) + Fintype.card α) % 2
      = (orbitCount f + Fintype.card α) % 2 := by omega
  rw [← neg_one_zpow_eq_iff_parity] at hexp_par
  rw [hexp_par] at hsg
  -- hsg : (-1)^e = - (-1)^e, impossible for a unit (apply the injection `ℤˣ → ℤ`)
  have hval := congrArg (Units.val) hsg
  simp only [Units.val_neg] at hval
  -- hval : (↑((-1)^e) : ℤ) = - ↑((-1)^e); but a unit value is ≠ 0 — contradiction
  have hu : ((-1 : ℤˣ) ^ (orbitCount f + Fintype.card α) : ℤˣ).val ≠ 0 :=
    Units.ne_zero ((-1 : ℤˣ) ^ (orbitCount f + Fintype.card α))
  set c : ℤ := ((-1 : ℤˣ) ^ (orbitCount f + Fintype.card α) : ℤˣ).val with hc
  exact hu (by omega)

/-- **Parity flip (≠ form).** When `p ≠ q`, `orbitCount (swap p q * f) ≠ orbitCount f`. -/
lemma orbitCount_swap_mul_ne (f : Perm α) {p q : α} (hpq : p ≠ q) :
    orbitCount (Equiv.swap p q * f) ≠ orbitCount f := by
  intro h
  exact orbitCount_swap_mul_parity f hpq (by rw [h])

/-! ### Magnitude bound via the setoid join (route for the exact ±1)

The clean, cycle-combinatorics-free route to `|orbitCount (swap p q * f) −
orbitCount f| ≤ 1`. Let `J := SameCycle.setoid f ⊔ ⟨pair p q⟩`, the partition of
`f` with the classes of `p` and `q` identified.

* **Monotonicity** (`orbitCount_mono_of_le`, PROVEN below): a finer setoid has at
  least as many classes — `Quot.factor` gives a surjection of quotients.
* `SameCycle (swap p q * f) ≤ J`: each `g`-step `g x = (p q)(f x)` is an `f`-step
  (hence `≤ J`) possibly composed with the `p~q` link (in `J`); induct on the
  `SameCycle` witness. Hence `orbitCount J ≤ orbitCount (swap p q * f)` and
  (taking `f` for `g`, as `SameCycle f ≤ J` trivially) `orbitCount J ≤ orbitCount f`.
* **One-link bound**: `orbitCount f ≤ orbitCount J + 1` and
  `orbitCount (swap p q * f) ≤ orbitCount J + 1` — adjoining a single pair to a
  setoid drops the class count by at most one. {{NEEDS_PROOF}} (see gap report).

Together: both counts lie in `{orbitCount J, orbitCount J + 1}`, so they differ by
at most 1. With the parity flip (they are unequal) this pins `|Δ| = 1`. -/

omit [DecidableEq α] in
/-- **Monotonicity of class count.** If `s` refines `t` (`s.r x y → t.r x y`),
then `t` has at most as many classes as `s`. Stated with `Nat.card` to avoid
`Fintype (Quotient _)` instance plumbing in the statement. -/
lemma card_quotient_mono_of_le {s t : Setoid α} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) := by
  haveI : Fintype (Quotient s) := Fintype.ofFinite _
  haveI : Fintype (Quotient t) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  -- the canonical surjection `Quotient s ↠ Quotient t` (well-defined since s ≤ t)
  refine Fintype.card_le_of_surjective
    (fun a => Quotient.liftOn a (Quotient.mk t) (fun x y hxy => Quotient.sound (h hxy))) ?_
  intro q
  induction q using Quotient.ind with
  | _ x => exact ⟨Quotient.mk s x, rfl⟩

omit [DecidableEq α] in
/-- `orbitCount` as a `Nat.card`. -/
lemma orbitCount_eq_natCard (f : Perm α) :
    orbitCount f = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid f)) := by
  rw [orbitCount, Nat.card_eq_fintype_card]

open Relation in
omit [DecidableEq α] [Fintype α] in
/-- If an equivalence relation `E` links every point to its `g`-image, it links any
two points in the same `g`-cycle. -/
private lemma sameCycle_le_of_step {g : Perm α} {E : Setoid α}
    (hstep : ∀ x, E x (g x)) {x y : α} (h : g.SameCycle x y) : E x y := by
  obtain ⟨i, rfl⟩ := h
  -- `E x ((g ^ i) x)` for every integer `i`, by induction
  suffices hall : ∀ j : ℤ, E x ((g ^ j) x) by exact hall i
  intro j
  induction j using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hstepn : (g ^ (n + 1 : ℤ)) x = g ((g ^ (n : ℤ)) x) := by
        rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      rw [hstepn]
      exact E.trans' ih (hstep _)
  | pred n ih =>
      -- step down: `(g^(-n-1)) x = g⁻¹ ((g^(-n)) x)`, and `E a (g⁻¹ a)` from `E (g⁻¹ a) a`
      have hgi : ∀ a, E a (g⁻¹ a) := by
        intro a
        have hstepa := hstep (g⁻¹ a)
        simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at hstepa
        exact E.symm' hstepa
      have hstepn : (g ^ (-n - 1 : ℤ)) x = g⁻¹ ((g ^ (-n : ℤ)) x) := by
        rw [show (-(n : ℤ) - 1 : ℤ) = (-1) + (-n) by ring, zpow_add, zpow_neg_one,
          Equiv.Perm.mul_apply]
      rw [hstepn]
      exact E.trans' ih (hgi _)

open Relation in
/-- The "joined" setoid: `f`'s cycle partition with the classes of `p` and `q`
identified. Built as the equivalence closure of `SameCycle f` together with the
single link `p ~ q`. -/
private def joinSetoid (f : Perm α) (p q : α) : Setoid α :=
  EqvGen.setoid (fun x y => f.SameCycle x y ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p))

open Relation in
omit [DecidableEq α] [Fintype α] in
/-- The link generator sits in `joinSetoid`. -/
private lemma link_le_join (f : Perm α) (p q : α) :
    (joinSetoid f p q).r p q :=
  EqvGen.rel _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))

open Relation in
omit [DecidableEq α] [Fintype α] in
/-- `SameCycle f` refines `joinSetoid`. -/
private lemma sameCycle_le_join (f : Perm α) (p q : α) :
    Equiv.Perm.SameCycle.setoid f ≤ joinSetoid f p q := by
  intro x y h
  exact EqvGen.rel _ _ (Or.inl h)

open Relation in
omit [Fintype α] in
/-- `SameCycle (swap p q * f)` refines `joinSetoid f p q`: a `g`-step is an
`f`-step possibly composed with the `p ~ q` link. -/
private lemma sameCycle_swap_mul_le_join (f : Perm α) (p q : α) :
    Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f) ≤ joinSetoid f p q := by
  intro x y h
  -- it suffices that `joinSetoid` links every `x` to `(swap p q * f) x`
  refine sameCycle_le_of_step (g := Equiv.swap p q * f) (E := joinSetoid f p q) ?_ h
  intro z
  have hfz : (Equiv.swap p q * f) z = Equiv.swap p q (f z) := rfl
  -- `joinSetoid` links `z` to `f z`
  have hzf : (joinSetoid f p q).r z (f z) :=
    EqvGen.rel _ _ (Or.inl (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)))
  rw [hfz]
  by_cases h1 : f z = p
  · -- swap p q (f z) = q, and z ~ f z = p ~ q
    rw [h1, Equiv.swap_apply_left]
    rw [h1] at hzf
    exact (joinSetoid f p q).trans' hzf (link_le_join f p q)
  · by_cases h2 : f z = q
    · rw [h2, Equiv.swap_apply_right]
      rw [h2] at hzf
      exact (joinSetoid f p q).trans' hzf ((joinSetoid f p q).symm' (link_le_join f p q))
    · -- swap fixes f z
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hzf

open Relation in
omit [DecidableEq α] [Fintype α] in
/-- **Characterization of `joinSetoid`.** Two points are joined iff they are
`f`-same-cycle, or one is `f`-same-cycle with `p` and the other with `q`. The only
new identification beyond `SameCycle f` is the merge of the `p`- and `q`-classes. -/
private lemma join_characterization (f : Perm α) (p q : α) {x y : α}
    (h : (joinSetoid f p q).r x y) :
    f.SameCycle x y ∨ (f.SameCycle x p ∧ f.SameCycle y q) ∨ (f.SameCycle x q ∧ f.SameCycle y p) := by
  -- the RHS predicate `P x y`
  induction h with
  | rel x y hxy =>
      rcases hxy with hsc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hsc
      · exact Or.inr (Or.inl ⟨SameCycle.refl _ _, SameCycle.refl _ _⟩)
      · exact Or.inr (Or.inr ⟨SameCycle.refl _ _, SameCycle.refl _ _⟩)
  | refl x => exact Or.inl (SameCycle.refl _ _)
  | symm x y _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
      · exact Or.inr (Or.inl ⟨h2, h1⟩)
  | trans x y z _ _ ihxy ihyz =>
      rcases ihxy with hxy | ⟨hxp, hyq⟩ | ⟨hxq, hyp⟩
      · -- x ~ y
        rcases ihyz with hyz | ⟨hyp, hzq⟩ | ⟨hyq, hzp⟩
        · exact Or.inl (hxy.trans hyz)
        · exact Or.inr (Or.inl ⟨hxy.trans hyp, hzq⟩)
        · exact Or.inr (Or.inr ⟨hxy.trans hyq, hzp⟩)
      · -- x ~ p, y ~ q
        rcases ihyz with hyz | ⟨hyp, hzq⟩ | ⟨hyq, hzp⟩
        · exact Or.inr (Or.inl ⟨hxp, hyz.symm.trans hyq⟩)
        · -- y ~ p and y ~ q ⟹ p ~ z via y; so x ~ p ~ z ⟹ x ~ z
          exact Or.inl (hxp.trans (hyp.symm.trans (hyq.trans hzq.symm)))
        · -- z ~ p and x ~ p ⟹ x ~ z
          exact Or.inl (hxp.trans hzp.symm)
      · -- x ~ q, y ~ p
        rcases ihyz with hyz | ⟨hyp, hzq⟩ | ⟨hyq, hzp⟩
        · exact Or.inr (Or.inr ⟨hxq, hyz.symm.trans hyp⟩)
        · -- z ~ q and x ~ q ⟹ x ~ z
          exact Or.inl (hxq.trans hzq.symm)
        · -- y ~ q and y ~ p ⟹ q ~ z via y; x ~ q ~ z ⟹ x ~ z
          exact Or.inl (hxq.trans (hyq.symm.trans (hyp.trans hzp.symm)))

/-- The raw function on representatives for `joinInj`: send a `q`-class point to
`none`, any other to `some` of its `joinSetoid` class. -/
private noncomputable def joinInjFun (f : Perm α) (p q : α) (x : α) :
    Option (Quotient (joinSetoid f p q)) := by
  classical
  exact if f.SameCycle x q then none else some (Quotient.mk (joinSetoid f p q) x)

private lemma joinInjFun_sameCycle (f : Perm α) (p q : α) {x y : α}
    (h : f.SameCycle x y) : joinInjFun f p q x = joinInjFun f p q y := by
  classical
  unfold joinInjFun
  by_cases hxq : f.SameCycle x q
  · rw [if_pos hxq, if_pos (h.symm.trans hxq)]
  · rw [if_neg hxq, if_neg (fun hyq => hxq (h.trans hyq))]
    congr 1
    exact Quotient.sound (sameCycle_le_join f p q h)

/-- The injection `Quotient (SameCycle f) ↪ Option (Quotient (joinSetoid f p q))`
witnessing the one-link bound. Injective because the only `joinSetoid` merge of
distinct `f`-classes is the `{p-class, q-class}` pair (`join_characterization`). -/
private noncomputable def joinInj (f : Perm α) (p q : α) :
    Quotient (Equiv.Perm.SameCycle.setoid f) → Option (Quotient (joinSetoid f p q)) :=
  Quotient.lift (joinInjFun f p q) (fun _ _ h => joinInjFun_sameCycle f p q h)

@[simp] private lemma joinInj_mk (f : Perm α) (p q : α) (x : α) :
    joinInj f p q (Quotient.mk _ x) = joinInjFun f p q x := rfl

private lemma joinInj_injective (f : Perm α) (p q : α) :
    Function.Injective (joinInj f p q) := by
  classical
  intro a b hab
  induction a using Quotient.ind with
  | _ x =>
  induction b using Quotient.ind with
  | _ y =>
    rw [joinInj_mk, joinInj_mk] at hab
    unfold joinInjFun at hab
    by_cases hxq : f.SameCycle x q <;> by_cases hyq : f.SameCycle y q
    · -- both q-class
      exact Quotient.sound (hxq.trans hyq.symm)
    · rw [if_pos hxq, if_neg hyq] at hab; exact absurd hab (by simp)
    · rw [if_neg hxq, if_pos hyq] at hab; exact absurd hab (by simp)
    · -- both `some`; `J x y` and neither is `q`-class ⟹ `f.SameCycle x y`
      rw [if_neg hxq, if_neg hyq, Option.some.injEq] at hab
      have hJ : (joinSetoid f p q).r x y := Quotient.exact hab
      rcases join_characterization f p q hJ with h | ⟨_, hyq'⟩ | ⟨hxq', _⟩
      · exact Quotient.sound h
      · exact absurd hyq' hyq
      · exact absurd hxq' hxq

/-- **One-link bound.** Adjoining the single pair `p ~ q` to `f`'s cycle partition
drops the class count by at most one: `orbitCount f ≤ Nat.card (Quotient J) + 1`. -/
private lemma orbitCount_le_join_succ (f : Perm α) (p q : α) :
    orbitCount f ≤ Nat.card (Quotient (joinSetoid f p q)) + 1 := by
  haveI : Fintype (Quotient (joinSetoid f p q)) := Fintype.ofFinite _
  have hcard : Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f))
      ≤ Fintype.card (Option (Quotient (joinSetoid f p q))) :=
    Fintype.card_le_of_injective _ (joinInj_injective f p q)
  rw [Fintype.card_option] at hcard
  rw [orbitCount, show Nat.card (Quotient (joinSetoid f p q))
    = Fintype.card (Quotient (joinSetoid f p q)) from Nat.card_eq_fintype_card]
  exact hcard

omit [DecidableEq α] in
/-- `Nat.card (Quotient (joinSetoid f p q)) ≤ orbitCount f` (the join is coarser
than `f`'s cycle partition). -/
private lemma natCard_join_le_orbitCount (f : Perm α) (p q : α) :
    Nat.card (Quotient (joinSetoid f p q)) ≤ orbitCount f := by
  rw [orbitCount_eq_natCard]
  exact card_quotient_mono_of_le (sameCycle_le_join f p q)

/-- **Lipschitz bound (upper).** A transposition raises the orbit count by at most
one: `orbitCount (swap p q * f) ≤ orbitCount f + 1`. -/
lemma orbitCount_swap_mul_le_succ (f : Perm α) (p q : α) :
    orbitCount (Equiv.swap p q * f) ≤ orbitCount f + 1 := by
  -- one-link bound on `g := swap p q * f`, then lower-bound its join by `orbitCount f`
  set g := Equiv.swap p q * f with hg
  -- `f = swap p q * g`, so `SameCycle f ≤ joinSetoid g p q`
  have hfg : f = Equiv.swap p q * g := by
    rw [hg, ← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hle : Equiv.Perm.SameCycle.setoid f ≤ joinSetoid g p q := by
    rw [hfg]; exact sameCycle_swap_mul_le_join g p q
  calc orbitCount g ≤ Nat.card (Quotient (joinSetoid g p q)) + 1 := orbitCount_le_join_succ g p q
    _ ≤ orbitCount f + 1 := by
        have := card_quotient_mono_of_le hle
        rw [orbitCount_eq_natCard]; omega

/-- **Lipschitz bound (lower).** `orbitCount f ≤ orbitCount (swap p q * f) + 1`,
the reverse bound, by applying the upper bound to `g` (`f = swap p q * g`). -/
lemma orbitCount_le_swap_mul_succ (f : Perm α) (p q : α) :
    orbitCount f ≤ orbitCount (Equiv.swap p q * f) + 1 := by
  have h := orbitCount_swap_mul_le_succ (Equiv.swap p q * f) p q
  rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at h

/-- **Exact magnitude (±1).** When `p ≠ q`, the orbit count changes by exactly one
under multiplication by the transposition `swap p q`. -/
theorem orbitCount_swap_mul_eq_or (f : Perm α) {p q : α} (hpq : p ≠ q) :
    orbitCount (Equiv.swap p q * f) = orbitCount f + 1 ∨
      orbitCount f = orbitCount (Equiv.swap p q * f) + 1 := by
  have hup := orbitCount_swap_mul_le_succ f p q
  have hlo := orbitCount_le_swap_mul_succ f p q
  have hne := orbitCount_swap_mul_ne f hpq
  omega

/-! ### Direction: which sign of ±1 occurs (keyed on `f.SameCycle p q`)

When `p, q` already lie in the same `f`-cycle, the link `p ~ q` is redundant, so
`joinSetoid f p q = SameCycle.setoid f` and `orbitCount (swap p q * f)` is pinned
to `orbitCount f + 1` (split). -/

open Relation in
omit [DecidableEq α] [Fintype α] in
/-- If `p, q` are in the same `f`-cycle, adjoining the link `p ~ q` changes
nothing: `joinSetoid f p q = SameCycle.setoid f`. -/
private lemma join_eq_of_sameCycle {f : Perm α} {p q : α} (h : f.SameCycle p q) :
    joinSetoid f p q = Equiv.Perm.SameCycle.setoid f := by
  refine le_antisymm ?_ (sameCycle_le_join f p q)
  -- the generators of `joinSetoid` are all already `SameCycle f`-related
  refine Setoid.eqvGen_le (fun x y hxy => ?_)
  rcases hxy with hsc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsc
  · exact h
  · exact h.symm

omit [Fintype α] in
/-- In the split case, multiplying by `swap p q` only subdivides an existing
cycle: every `(swap p q * f)`-cycle is contained in an `f`-cycle. -/
theorem sameCycle_swap_mul_le_of_sameCycle {f : Perm α} {p q : α}
    (h : f.SameCycle p q) :
    Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f) ≤
      Equiv.Perm.SameCycle.setoid f := by
  rw [← join_eq_of_sameCycle h]
  exact sameCycle_swap_mul_le_join f p q

/-- **Split direction.** If `p, q` share an `f`-cycle then the orbit count goes up
by one: `orbitCount (swap p q * f) = orbitCount f + 1`. -/
theorem orbitCount_swap_mul_of_sameCycle (f : Perm α) {p q : α} (hpq : p ≠ q)
    (h : f.SameCycle p q) : orbitCount (Equiv.swap p q * f) = orbitCount f + 1 := by
  -- lower bound on `orbitCount g` via the join (which equals `SameCycle f` here)
  have hge : orbitCount f ≤ orbitCount (Equiv.swap p q * f) := by
    have hmono := card_quotient_mono_of_le (sameCycle_swap_mul_le_join f p q)
    rw [join_eq_of_sameCycle h] at hmono
    rw [orbitCount_eq_natCard, orbitCount_eq_natCard (Equiv.swap p q * f)]
    exact hmono
  have hup := orbitCount_swap_mul_le_succ f p q
  have hne := orbitCount_swap_mul_ne f hpq
  omega

/-- In the split case, the two cut points land in different cycles after the
transposition. -/
theorem not_sameCycle_swap_mul_of_sameCycle (f : Perm α) {p q : α} (hpq : p ≠ q)
    (h : f.SameCycle p q) : ¬ (Equiv.swap p q * f).SameCycle p q := by
  intro hg
  have hsplit := orbitCount_swap_mul_of_sameCycle f hpq h
  have hsplit_again := orbitCount_swap_mul_of_sameCycle (Equiv.swap p q * f) hpq hg
  have hcancel : Equiv.swap p q * (Equiv.swap p q * f) = f := by
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  rw [hcancel] at hsplit_again
  omega

/-- Target pool for a split cycle: every old `f`-orbit except the orbit of `p`,
plus the two new cycles created by the split. -/
abbrev SplitCyclePool (f : Perm α) (p : α) :=
  {r : Quotient (Equiv.Perm.SameCycle.setoid f) //
    r ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid f) p} ⊕ Fin 2

noncomputable instance instFintypeSplitCyclePool (f : Perm α) (p : α) :
    Fintype (SplitCyclePool f p) := by
  classical
  infer_instance

/-- Representative-level classifier for the quotient after a split transposition.
It sends points outside the split `f`-cycle to their old `f`-orbit, and points in
the split cycle to the new side containing `p` or to the other side. -/
private noncomputable def splitCycleQuotToFun (f : Perm α) {p q : α}
    (_hpq : p ≠ q) (_h : f.SameCycle p q) (x : α) :
    SplitCyclePool f p :=
  if hx : f.SameCycle x p then
    if (Equiv.swap p q * f).SameCycle x p then Sum.inr 0 else Sum.inr 1
  else
    Sum.inl ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid f) x, by
      intro hq
      exact hx (Quotient.eq''.mp hq)⟩

/-- The split-cycle classifier is constant on `(swap p q * f)`-orbits. -/
private lemma splitCycleQuotToFun_respects (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) {x y : α}
    (hxy : (Equiv.swap p q * f).SameCycle x y) :
    splitCycleQuotToFun f hpq h x = splitCycleQuotToFun f hpq h y := by
  classical
  have hxyf : f.SameCycle x y := sameCycle_swap_mul_le_of_sameCycle h hxy
  unfold splitCycleQuotToFun
  by_cases hx : f.SameCycle x p
  · have hy : f.SameCycle y p := hxyf.symm.trans hx
    by_cases hxp : (Equiv.swap p q * f).SameCycle x p
    · have hyp : (Equiv.swap p q * f).SameCycle y p := hxy.symm.trans hxp
      simp [hx, hy, hxp, hyp]
    · have hyp : ¬ (Equiv.swap p q * f).SameCycle y p := by
        intro hyp
        exact hxp (hxy.trans hyp)
      simp [hx, hy, hxp, hyp]
  · have hy : ¬ f.SameCycle y p := by
      intro hyp
      exact hx (hxyf.trans hyp)
    simp [hx, hy]
    exact Quotient.sound hxyf

/-- Quotient-level classifier for the orbit split caused by `swap p q`. -/
noncomputable def splitCycleQuotMap (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) →
      SplitCyclePool f p :=
  Quotient.lift (splitCycleQuotToFun f hpq h)
    (fun _ _ hxy => splitCycleQuotToFun_respects f hpq h hxy)

/-- A dart outside the split `f`-cycle is carried to its old orbit in the
split-cycle target pool. -/
@[simp] theorem splitCycleQuotMap_mk_of_not_sameCycle (f : Perm α) {p q x : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) (hx : ¬ f.SameCycle x p) :
    splitCycleQuotMap f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) x) =
      Sum.inl ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid f) x, by
        intro hq
        exact hx (Quotient.eq''.mp hq)⟩ := by
  simp [splitCycleQuotMap, splitCycleQuotToFun, hx]

/-- The split-cycle side containing the cut point `p`. -/
@[simp] theorem splitCycleQuotMap_mk_left (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    splitCycleQuotMap f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) p) =
      Sum.inr (0 : Fin 2) := by
  have hpp : f.SameCycle p p := Equiv.Perm.SameCycle.refl _ _
  have hgpp : (Equiv.swap p q * f).SameCycle p p := Equiv.Perm.SameCycle.refl _ _
  simp [splitCycleQuotMap, splitCycleQuotToFun, hpp, hgpp]

/-- The split-cycle side containing the other cut point `q`. -/
@[simp] theorem splitCycleQuotMap_mk_right (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    splitCycleQuotMap f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) q) =
      Sum.inr (1 : Fin 2) := by
  have hqp : f.SameCycle q p := h.symm
  have hnot : ¬ (Equiv.swap p q * f).SameCycle q p := by
    intro hg
    exact (not_sameCycle_swap_mul_of_sameCycle f hpq h) hg.symm
  simp [splitCycleQuotMap, splitCycleQuotToFun, hqp, hnot]

/-- The split-cycle classifier is onto. -/
theorem splitCycleQuotMap_surjective (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    Function.Surjective (splitCycleQuotMap f hpq h) := by
  classical
  intro y
  cases y with
  | inl r =>
      rcases r with ⟨r, hr⟩
      induction r using Quotient.ind with
      | _ x =>
          have hx : ¬ f.SameCycle x p := by
            intro hxp
            exact hr (Quotient.sound hxp)
          refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) x, ?_⟩
          simp [splitCycleQuotMap, splitCycleQuotToFun, hx]
  | inr i =>
      cases i using Fin.cases with
      | zero =>
          refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) p, ?_⟩
          have hpp : f.SameCycle p p := Equiv.Perm.SameCycle.refl _ _
          have hgpp : (Equiv.swap p q * f).SameCycle p p := Equiv.Perm.SameCycle.refl _ _
          simp [splitCycleQuotMap, splitCycleQuotToFun, hpp, hgpp]
      | succ i =>
          cases i using Fin.cases with
          | zero =>
              refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) q, ?_⟩
              have hqp : f.SameCycle q p := h.symm
              have hnot : ¬ (Equiv.swap p q * f).SameCycle q p := by
                intro hg
                exact (not_sameCycle_swap_mul_of_sameCycle f hpq h) hg.symm
              simp [splitCycleQuotMap, splitCycleQuotToFun, hqp, hnot]
          | succ j => exact Fin.elim0 j

omit [DecidableEq α] in
/-- The split-cycle target pool has one more element than the old orbit quotient. -/
theorem card_splitCyclePool (f : Perm α) (p : α) :
    Fintype.card (SplitCyclePool f p) = orbitCount f + 1 := by
  classical
  unfold SplitCyclePool orbitCount
  rw [Fintype.card_sum, Fintype.card_fin]
  have hcompl := Fintype.card_subtype_compl
    (p := fun r : Quotient (Equiv.Perm.SameCycle.setoid f) =>
      r = Quotient.mk (Equiv.Perm.SameCycle.setoid f) p)
  have hsingle :
      Fintype.card {r : Quotient (Equiv.Perm.SameCycle.setoid f) //
          r = Quotient.mk (Equiv.Perm.SameCycle.setoid f) p} = 1 :=
    Fintype.card_subtype_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid f) p)
  rw [hsingle] at hcompl
  rw [hcompl]
  have hnonempty : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid f)) :=
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid f) p⟩
  have hpos : 0 < Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f)) :=
    Fintype.card_pos_iff.mpr hnonempty
  omega

/-- The domain of the split-cycle classifier and its target pool have equal
cardinality. -/
theorem card_splitCycleQuotMap_domain (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f))) =
      Fintype.card (SplitCyclePool f p) := by
  change orbitCount (Equiv.swap p q * f) = Fintype.card (SplitCyclePool f p)
  rw [orbitCount_swap_mul_of_sameCycle f hpq h, card_splitCyclePool]

/-- Explicit equivalence of orbit quotients after a split transposition with
`old orbits except the split orbit, plus two new sides`. -/
noncomputable def splitCycleQuotEquiv (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    Quotient (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) ≃
      SplitCyclePool f p :=
  Equiv.ofBijective (splitCycleQuotMap f hpq h)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨splitCycleQuotMap_surjective f hpq h,
        card_splitCycleQuotMap_domain f hpq h⟩)

/-- A dart outside the split `f`-cycle is carried unchanged by the split-cycle
quotient equivalence. -/
@[simp] theorem splitCycleQuotEquiv_mk_of_not_sameCycle (f : Perm α) {p q x : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) (hx : ¬ f.SameCycle x p) :
    splitCycleQuotEquiv f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) x) =
      Sum.inl ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid f) x, by
        intro hq
        exact hx (Quotient.eq''.mp hq)⟩ := by
  simp [splitCycleQuotEquiv, hx]

/-- The split-cycle quotient equivalence sends the side containing `p` to
`0 : Fin 2`. -/
@[simp] theorem splitCycleQuotEquiv_mk_left (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    splitCycleQuotEquiv f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) p) =
      Sum.inr (0 : Fin 2) := by
  simp [splitCycleQuotEquiv]

/-- The split-cycle quotient equivalence sends the side containing `q` to
`1 : Fin 2`. -/
@[simp] theorem splitCycleQuotEquiv_mk_right (f : Perm α) {p q : α}
    (hpq : p ≠ q) (h : f.SameCycle p q) :
    splitCycleQuotEquiv f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) q) =
      Sum.inr (1 : Fin 2) := by
  simp [splitCycleQuotEquiv]

/-- An arbitrary representative in the split `f`-cycle lands on side `0` when
it remains in the post-split component containing `p`. -/
@[simp] theorem splitCycleQuotEquiv_mk_of_sameCycle_left
    (f : Perm α) {p q x : α} (hpq : p ≠ q) (h : f.SameCycle p q)
    (hx : f.SameCycle x p) (hleft : (Equiv.swap p q * f).SameCycle x p) :
    splitCycleQuotEquiv f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) x) =
      Sum.inr (0 : Fin 2) := by
  simp [splitCycleQuotEquiv, splitCycleQuotMap, splitCycleQuotToFun, hx, hleft]

/-- An arbitrary representative in the split `f`-cycle lands on side `1` when
it is not in the post-split component containing `p`. -/
@[simp] theorem splitCycleQuotEquiv_mk_of_sameCycle_right
    (f : Perm α) {p q x : α} (hpq : p ≠ q) (h : f.SameCycle p q)
    (hx : f.SameCycle x p) (hright : ¬ (Equiv.swap p q * f).SameCycle x p) :
    splitCycleQuotEquiv f hpq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)) x) =
      Sum.inr (1 : Fin 2) := by
  simp [splitCycleQuotEquiv, splitCycleQuotMap, splitCycleQuotToFun, hx, hright]

omit [DecidableEq α] in
/-- The minimal `f`-period of `p` is positive (every point of a `Fintype` perm is
periodic). -/
private lemma minimalPeriod_pos (f : Perm α) (x : α) : 0 < Function.minimalPeriod f x := by
  rw [Function.minimalPeriod_pos_iff_mem_periodicPts]
  exact ⟨orderOf f, orderOf_pos f, by show (f ^ orderOf f) x = x; rw [pow_orderOf_eq_one]; rfl⟩

omit [DecidableEq α] [Fintype α] in
/-- `(f ^ j) p = p` only at `j = 0` below the minimal period. -/
private lemma pow_ne_self_of_lt_minimalPeriod (f : Perm α) (p : α) {j : ℕ}
    (hj0 : j ≠ 0) (hjk : j < Function.minimalPeriod f p) : (f ^ j) p ≠ p := by
  have := Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hj0 hjk
  rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow] at this
  exact this

open Relation in
/-- **Joining lemma.** If `p, q` are in *different* `f`-cycles (`p ≠ q`), then they
are in the *same* `(swap p q * f)`-cycle: following `p` along `g = swap p q * f`
traces the `f`-cycle of `p` and lands on `q` after one full period (the swap fires
exactly at the wrap-around). -/
theorem sameCycle_swap_mul_of_not_sameCycle (f : Perm α) {p q : α}
    (h : ¬ f.SameCycle p q) : (Equiv.swap p q * f).SameCycle p q := by
  set g := Equiv.swap p q * f with hgdef
  set k := Function.minimalPeriod f p with hk
  have hkpos : 0 < k := minimalPeriod_pos f p
  -- `(f ^ j) p ≠ q` for all `j` (different cycle)
  have hfjq : ∀ j : ℕ, (f ^ j) p ≠ q := by
    intro j hj; exact h ⟨j, hj⟩
  -- `(f ^ (j+1)) p = f ((f ^ j) p)`
  have hfstep : ∀ j : ℕ, (f ^ (j + 1)) p = f ((f ^ j) p) := by
    intro j; rw [pow_succ', Equiv.Perm.mul_apply]
  -- `(g ^ (j+1)) p = g ((g ^ j) p)`
  have hgstep : ∀ j : ℕ, (g ^ (j + 1)) p = g ((g ^ j) p) := by
    intro j; rw [pow_succ', Equiv.Perm.mul_apply]
  -- trace: `(g ^ j) p = (f ^ j) p` for `j < k`
  have htrace : ∀ j : ℕ, j < k → (g ^ j) p = (f ^ j) p := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ n ih =>
        intro hlt
        have hn : n < k := Nat.lt_of_succ_lt hlt
        rw [hgstep n, ih hn, hgdef, Equiv.Perm.mul_apply, ← hfstep n]
        -- swap fixes `(f^(n+1)) p` (it is ≠ p, ≠ q since 0 < n+1 < k)
        have hne_p : (f ^ (n + 1)) p ≠ p :=
          pow_ne_self_of_lt_minimalPeriod f p (Nat.succ_ne_zero n) hlt
        have hne_q : (f ^ (n + 1)) p ≠ q := hfjq (n + 1)
        rw [Equiv.swap_apply_of_ne_of_ne hne_p hne_q]
  -- final wrap-around step: `(g ^ k) p = q`
  have hfinal : (g ^ k) p = q := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    rw [hm, hgstep m, htrace m (hm ▸ Nat.lt_succ_self m), hgdef, Equiv.Perm.mul_apply,
      ← hfstep m]
    -- `(f^(m+1)) p = (f^k) p = p`, then `swap p q p = q`
    have hwrap : (f ^ (m + 1)) p = p := by
      have hip := Function.iterate_minimalPeriod (f := (f : α → α)) (x := p)
      rw [Equiv.Perm.iterate_eq_pow, ← hk, hm] at hip
      exact hip
    rw [hwrap, Equiv.swap_apply_left]
  exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hfinal⟩

/-- **Merge direction.** If `p, q` lie in *different* `f`-cycles then the orbit
count goes *down* by one: `orbitCount f = orbitCount (swap p q * f) + 1`. -/
theorem orbitCount_swap_mul_of_not_sameCycle (f : Perm α) {p q : α} (hpq : p ≠ q)
    (h : ¬ f.SameCycle p q) : orbitCount f = orbitCount (Equiv.swap p q * f) + 1 := by
  -- `g.SameCycle p q`, so the split direction applies to `g` (and `swap p q * g = f`)
  have hg : (Equiv.swap p q * f).SameCycle p q := sameCycle_swap_mul_of_not_sameCycle f h
  have := orbitCount_swap_mul_of_sameCycle (Equiv.swap p q * f) hpq hg
  rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at this

/-- **D1-B (exact, with direction).** For `p ≠ q`, multiplication by the
transposition `swap p q` changes the orbit count by exactly one: `+1` when `p, q`
share an `f`-cycle (a cycle *splits*), `−1` otherwise (two cycles *merge*). -/
theorem orbitCount_swap_mul (f : Perm α) {p q : α} (hpq : p ≠ q) :
    (f.SameCycle p q → orbitCount (Equiv.swap p q * f) = orbitCount f + 1) ∧
      (¬ f.SameCycle p q → orbitCount f = orbitCount (Equiv.swap p q * f) + 1) :=
  ⟨orbitCount_swap_mul_of_sameCycle f hpq, orbitCount_swap_mul_of_not_sameCycle f hpq⟩

/-! ### Which pairs are same-cycle after a *merge* transposition

In the merge case (`¬ f.SameCycle p q`), the cycle partition of `swap p q * f` is
exactly the `joinSetoid` — `f`'s partition with the `p`- and `q`-classes fused.
This is the converse refinement to `sameCycle_swap_mul_le_join`, and it lets the
D1-A splice read off the same-cycle relation in the spliced face/vertex
permutation. -/

open Relation in
/-- In the merge case, an `f`-cycle stays inside a `(swap p q * f)`-cycle: every
`f`-step is realized by `swap p q * f` up to the (now redundant) `p ~ q` link. -/
private lemma sameCycle_le_swap_mul_of_not_sameCycle (f : Perm α) {p q : α}
    (h : ¬ f.SameCycle p q) :
    Equiv.Perm.SameCycle.setoid f ≤ Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f) := by
  set g := Equiv.swap p q * f with hg
  -- `g.SameCycle p q` (the merge fires)
  have hgpq : g.SameCycle p q := sameCycle_swap_mul_of_not_sameCycle f h
  intro x y hxy
  -- it suffices that `g` links every `z` to `f z`
  refine sameCycle_le_of_step (g := f) (E := Equiv.Perm.SameCycle.setoid g) ?_ hxy
  intro z
  -- `g.SameCycle z (g z)` always; and `g z = swap p q (f z)`
  have hstep : g.SameCycle z (g z) := Equiv.Perm.sameCycle_apply_right.mpr (SameCycle.refl _ _)
  have hgz : g z = Equiv.swap p q (f z) := rfl
  by_cases h1 : f z = p
  · -- g z = q ; want g.SameCycle z (f z) = g.SameCycle z p
    rw [h1]
    rw [hgz, h1, Equiv.swap_apply_left] at hstep
    -- z ~ q ~ p
    exact hstep.trans hgpq.symm
  · by_cases h2 : f z = q
    · rw [h2]
      rw [hgz, h2, Equiv.swap_apply_right] at hstep
      exact hstep.trans hgpq
    · -- swap fixes f z, so g z = f z
      rw [hgz, Equiv.swap_apply_of_ne_of_ne h1 h2] at hstep
      exact hstep

open Relation in
/-- **Merge same-cycle characterization.** When `p, q` are in different `f`-cycles,
the `(swap p q * f)`-partition is exactly `joinSetoid f p q`. -/
private lemma sameCycle_swap_mul_setoid_eq_join (f : Perm α) {p q : α}
    (h : ¬ f.SameCycle p q) :
    Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f) = joinSetoid f p q := by
  refine le_antisymm (sameCycle_swap_mul_le_join f p q) ?_
  -- `joinSetoid` is generated by `SameCycle f` and the link `p ~ q`; both hold in
  -- `SameCycle (swap p q * f)`.
  refine Setoid.eqvGen_le (fun x y hxy => ?_)
  rcases hxy with hsc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact sameCycle_le_swap_mul_of_not_sameCycle f h hsc
  · exact sameCycle_swap_mul_of_not_sameCycle f h
  · exact (sameCycle_swap_mul_of_not_sameCycle f h).symm

open Relation in
/-- **Merge same-cycle dichotomy (usable form).** When `p ≠ q` lie in different
`f`-cycles, two darts are `(swap p q * f)`-same-cycle iff they were `f`-same-cycle,
or one lies in the `p`-cycle and the other in the `q`-cycle. -/
theorem sameCycle_swap_mul_iff_of_not_sameCycle (f : Perm α) {p q : α}
    (h : ¬ f.SameCycle p q) {x y : α} :
    (Equiv.swap p q * f).SameCycle x y ↔
      (f.SameCycle x y ∨ (f.SameCycle x p ∧ f.SameCycle y q) ∨
        (f.SameCycle x q ∧ f.SameCycle y p)) := by
  -- `(swap p q * f).SameCycle x y` is defeq to `(SameCycle.setoid (swap p q * f)).r x y`.
  have hsetoid : (Equiv.swap p q * f).SameCycle x y ↔ (joinSetoid f p q).r x y := by
    rw [show (Equiv.swap p q * f).SameCycle x y
          ↔ (Equiv.Perm.SameCycle.setoid (Equiv.swap p q * f)).r x y from Iff.rfl,
        sameCycle_swap_mul_setoid_eq_join f h]
  rw [hsetoid]
  constructor
  · intro hxy; exact join_characterization f p q hxy
  · intro hxy
    rcases hxy with hsc | ⟨hxp, hyq⟩ | ⟨hxq, hyp⟩
    · exact EqvGen.rel _ _ (Or.inl hsc)
    · exact (joinSetoid f p q).trans' (EqvGen.rel _ _ (Or.inl hxp))
        ((joinSetoid f p q).trans' (link_le_join f p q)
          ((joinSetoid f p q).symm' (EqvGen.rel _ _ (Or.inl hyq))))
    · exact (joinSetoid f p q).trans' (EqvGen.rel _ _ (Or.inl hxq))
        ((joinSetoid f p q).trans' ((joinSetoid f p q).symm' (link_le_join f p q))
          ((joinSetoid f p q).symm' (EqvGen.rel _ _ (Or.inl hyp))))

/-! ### Bridge to the `CombinatorialMap` carrier

`orbitCount` of the three structure permutations is exactly the carrier's
`Vertex`/`Edge`/`Face` count. This is the interface through which **D1-A** feeds
`orbitCount_swap_mul` into Euler-characteristic bookkeeping: the corner splice
multiplies the relevant orbit permutation by a transposition, so the cell count
changes by exactly `±1` per `orbitCount_swap_mul`. -/

/-- The carrier's face count is the `orbitCount` of `facePerm`. (Same for
`Vertex`/`Edge` by the identical argument — `orbitCount` is, by definition, the
`SameCycle`-quotient cardinality the carrier uses.) -/
theorem card_face_eq_orbitCount {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) :
    Fintype.card M.Face = orbitCount M.facePerm :=
  -- both are `Fintype.card (Quotient (SameCycle.setoid M.facePerm))`, up to the
  -- (proof-irrelevant) `Fintype` instance.
  Fintype.card_congr (Equiv.refl _)

/-- Carrier vertex count as an `orbitCount`. -/
theorem card_vertex_eq_orbitCount {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) :
    Fintype.card M.Vertex = orbitCount M.vertexPerm :=
  Fintype.card_congr (Equiv.refl _)

/-- Carrier edge count as an `orbitCount`. -/
theorem card_edge_eq_orbitCount {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) :
    Fintype.card M.Edge = orbitCount M.edgePerm :=
  Fintype.card_congr (Equiv.refl _)

/-- Equality of permutations transports their `SameCycle` quotient. -/
noncomputable def quotientSameCycleEquivOfPermEq {D : Type*} {σ τ : Perm D}
    (h : σ = τ) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid τ) := by
  subst h
  exact Equiv.refl _

/-- Transport by an equality of permutations carries each quotient class to the
same representative class for the transported permutation. -/
@[simp] theorem quotientSameCycleEquivOfPermEq_mk {D : Type*} {σ τ : Perm D}
    (h : σ = τ) (x : D) :
    quotientSameCycleEquivOfPermEq h
        (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid τ) x := by
  subst h
  rfl

/-! ## D1-A — edge insertion on `D ⊕ Fin 2`

We enlarge the dart set by two new darts `a := Sum.inr 0`, `b := Sum.inr 1`
forming a single new edge, and splice them into the vertex rotation at two corner
darts `c₁` (tail) and `c₂` (head), `c₁ ≠ c₂`. The construction is purely algebraic
(a product of transpositions and a `sumCongr`); no geometry. The V/E/F deltas all
reduce to the `orbitCount` engine above.

### Step 0 — `orbitCount` of a `sumCongr`

`orbitCount (g.sumCongr h) = orbitCount g + orbitCount h`: the orbits of a direct
sum of permutations split as the `inl`-orbits of `g` and the `inr`-orbits of `h`
(the permutation never mixes the two summands). Proven by an explicit `Equiv` of
the `SameCycle` quotients — the same technique as `bridgeEquiv`. -/

section SumCongr

variable {β : Type*} [DecidableEq β] [Fintype β]

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- `(g.sumCongr h) ^ n` distributes over the sum for `n : ℤ`. -/
private lemma sumCongr_zpow (g : Perm α) (h : Perm β) (n : ℤ) :
    (g.sumCongr h) ^ n = (g ^ n).sumCongr (h ^ n) := by
  have := map_zpow (Equiv.Perm.sumCongrHom α β) (g, h) n
  simpa [Equiv.Perm.sumCongrHom] using this.symm

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- `(g.sumCongr h)^n` on a left dart is `g^n` on that dart. -/
private lemma sumCongr_zpow_inl (g : Perm α) (h : Perm β) (x : α) (n : ℤ) :
    ((g.sumCongr h) ^ n) (Sum.inl x) = Sum.inl ((g ^ n) x) := by
  rw [sumCongr_zpow]; simp

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- `(g.sumCongr h)^n` on a right dart is `h^n` on that dart. -/
private lemma sumCongr_zpow_inr (g : Perm α) (h : Perm β) (y : β) (n : ℤ) :
    ((g.sumCongr h) ^ n) (Sum.inr y) = Sum.inr ((h ^ n) y) := by
  rw [sumCongr_zpow]; simp

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- Left darts are `sumCongr`-same-cycle iff their `g`-images are `g`-same-cycle. -/
private lemma sumCongr_sameCycle_inl (g : Perm α) (h : Perm β) {x y : α} :
    (g.sumCongr h).SameCycle (Sum.inl x) (Sum.inl y) ↔ g.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    rw [sumCongr_zpow_inl] at hn
    exact ⟨n, Sum.inl.inj hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [sumCongr_zpow_inl, hn]⟩

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- Right darts are `sumCongr`-same-cycle iff their `h`-images are `h`-same-cycle. -/
private lemma sumCongr_sameCycle_inr (g : Perm α) (h : Perm β) {x y : β} :
    (g.sumCongr h).SameCycle (Sum.inr x) (Sum.inr y) ↔ h.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    rw [sumCongr_zpow_inr] at hn
    exact ⟨n, Sum.inr.inj hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [sumCongr_zpow_inr, hn]⟩

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
/-- A left dart and a right dart are never `sumCongr`-same-cycle. -/
private lemma sumCongr_not_sameCycle_inl_inr (g : Perm α) (h : Perm β) (x : α) (y : β) :
    ¬ (g.sumCongr h).SameCycle (Sum.inl x) (Sum.inr y) := by
  rintro ⟨n, hn⟩
  rw [sumCongr_zpow_inl] at hn
  exact Sum.inl_ne_inr hn

/-- Forward map of the `sumCongr`-quotient equivalence, on representatives:
`inl x ↦ inl [x]_g`, `inr y ↦ inr [y]_h`. -/
private def sumCongrQuotToFun (g : Perm α) (h : Perm β) (s : α ⊕ β) :
    Quotient (Equiv.Perm.SameCycle.setoid g) ⊕ Quotient (Equiv.Perm.SameCycle.setoid h) :=
  s.elim (fun x => Sum.inl (Quotient.mk _ x)) (fun y => Sum.inr (Quotient.mk _ y))

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
private lemma sumCongrQuotToFun_respects (g : Perm α) (h : Perm β) {s t : α ⊕ β}
    (hst : (g.sumCongr h).SameCycle s t) :
    sumCongrQuotToFun g h s = sumCongrQuotToFun g h t := by
  cases s with
  | inl x =>
    cases t with
    | inl y =>
      exact congrArg Sum.inl (Quotient.sound ((sumCongr_sameCycle_inl g h).mp hst))
    | inr y => exact absurd hst (sumCongr_not_sameCycle_inl_inr g h x y)
  | inr x =>
    cases t with
    | inl y => exact absurd hst.symm (sumCongr_not_sameCycle_inl_inr g h y x)
    | inr y =>
      exact congrArg Sum.inr (Quotient.sound ((sumCongr_sameCycle_inr g h).mp hst))

/-- The orbits of `g.sumCongr h` are the orbits of `g` (on the left) plus the
orbits of `h` (on the right). -/
private def sumCongrQuotEquiv (g : Perm α) (h : Perm β) :
    Quotient (Equiv.Perm.SameCycle.setoid (g.sumCongr h)) ≃
      (Quotient (Equiv.Perm.SameCycle.setoid g) ⊕ Quotient (Equiv.Perm.SameCycle.setoid h)) where
  toFun := Quotient.lift (sumCongrQuotToFun g h)
    (fun _ _ hst => sumCongrQuotToFun_respects g h hst)
  invFun := fun s => s.elim
    (Quotient.lift (fun x => Quotient.mk _ (Sum.inl x))
      (fun x y hxy => Quotient.sound ((sumCongr_sameCycle_inl g h).mpr hxy)))
    (Quotient.lift (fun y => Quotient.mk _ (Sum.inr y))
      (fun x y hxy => Quotient.sound ((sumCongr_sameCycle_inr g h).mpr hxy)))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ s =>
      cases s with
      | inl x => rfl
      | inr y => rfl
  right_inv := by
    intro s
    cases s with
    | inl q => induction q using Quotient.ind with | _ x => rfl
    | inr q => induction q using Quotient.ind with | _ y => rfl

omit [DecidableEq α] [DecidableEq β] in
/-- **`orbitCount` is additive over `sumCongr`.** -/
theorem orbitCount_sumCongr (g : Perm α) (h : Perm β) :
    orbitCount (g.sumCongr h) = orbitCount g + orbitCount h := by
  unfold orbitCount
  rw [Fintype.card_congr (sumCongrQuotEquiv g h), Fintype.card_sum]

/-- The identity on `Fin 2` has two orbits (two fixed points). -/
private lemma orbitCount_one_fin2 : orbitCount (1 : Perm (Fin 2)) = 2 := by
  rw [orbitCount_eq]; simp

/-- The transposition `(0 1)` on `Fin 2` has a single orbit. -/
private lemma orbitCount_swap_fin2 : orbitCount (Equiv.swap (0 : Fin 2) 1) = 1 := by
  rw [orbitCount_eq, Equiv.Perm.support_swap (by decide),
    Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton (Equiv.Perm.isCycle_swap (by decide))]
  decide

end SumCongr

/-! ### Step 1 — the inserted-edge construction

`D ⊕ Fin 2`; the two new darts `a := Sum.inr 0`, `b := Sum.inr 1` form one new edge.
We splice them into the vertex rotation at the corners `c₁` (tail), `c₂` (head):
in cycle notation `c₁ → a → σ c₁` and `c₂ → b → σ c₂`, which as a closed form is a
pair of transpositions left-multiplying the trivial extension `σ ⊕ 1`. The face
permutation `φ'` is forced by `φ' := σ'⁻¹ · α'`. -/

section Construction

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D) (c₁ c₂ : D)

/-- The first new dart. -/
abbrev dartA : D ⊕ Fin 2 := Sum.inr 0

/-- The second new dart. -/
abbrev dartB : D ⊕ Fin 2 := Sum.inr 1

/-- The enlarged edge permutation: `α` on the old darts, the swap `(a b)` on the
two new darts. A fixed-point-free involution because each summand is. -/
def insEdgePerm : Equiv.Perm (D ⊕ Fin 2) :=
  M.edgePerm.sumCongr (Equiv.swap 0 1)

/-- The enlarged vertex permutation: the corner splice
`swap (inl (σ c₁)) a · swap (inl (σ c₂)) b · (σ ⊕ 1)`. In cycles this threads `a`
into `σ`'s cycle right after `c₁` and `b` right after `c₂`. -/
def insVertexPerm : Equiv.Perm (D ⊕ Fin 2) :=
  Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA) *
    Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB) *
    M.vertexPerm.sumCongr 1

/-- The enlarged face permutation, forced by the structure relation. -/
def insFacePerm : Equiv.Perm (D ⊕ Fin 2) :=
  (insVertexPerm M c₁ c₂)⁻¹ * insEdgePerm M

omit [Fintype D] [DecidableEq D] in
/-- `insEdgePerm` is an involution. -/
lemma insEdgePerm_involutive : Function.Involutive (insEdgePerm M) := by
  intro x
  show (insEdgePerm M) ((insEdgePerm M) x) = x
  rw [← Equiv.Perm.mul_apply]
  unfold insEdgePerm
  rw [Equiv.Perm.sumCongr_mul]
  have he : M.edgePerm * M.edgePerm = 1 := by
    ext z; rw [Equiv.Perm.mul_apply, M.edgePerm_involutive z]; rfl
  rw [he, show Equiv.swap (0 : Fin 2) 1 * Equiv.swap 0 1 = 1 from Equiv.swap_mul_self _ _,
    Equiv.Perm.sumCongr_one, Equiv.Perm.one_apply]

omit [Fintype D] [DecidableEq D] in
/-- `insEdgePerm` is fixed-point-free. -/
lemma insEdgePerm_fixedPointFree (x : D ⊕ Fin 2) : (insEdgePerm M) x ≠ x := by
  unfold insEdgePerm
  cases x with
  | inl d =>
    rw [Equiv.Perm.sumCongr_apply]
    simp only [Sum.map_inl, ne_eq, Sum.inl.injEq]
    -- `M.edgePerm d ≠ d` from fixed-point-freeness of the carrier's edge perm
    intro hd
    exact (M.isEmpty_fixedPoints_edgePerm.false ⟨d, by
      show M.edgePerm d = d; exact hd⟩)
  | inr i =>
    rw [Equiv.Perm.sumCongr_apply]
    simp only [Sum.map_inr, ne_eq, Sum.inr.injEq]
    -- `swap 0 1 i ≠ i` on `Fin 2`
    revert i
    decide

/-- **Step 1 — the inserted-edge `CombinatorialMap`.** -/
def insertedEdgeMap : CombinatorialMap (D ⊕ Fin 2) where
  vertexPerm := insVertexPerm M c₁ c₂
  edgePerm := insEdgePerm M
  facePerm := insFacePerm M c₁ c₂
  face_mul_edge_mul_vertex_eq_one := by
    unfold insFacePerm
    -- (σ'⁻¹ α') α' σ' = σ'⁻¹ (α' α') σ' = σ'⁻¹ σ' = 1
    rw [mul_assoc, mul_assoc, ← mul_assoc (insEdgePerm M)]
    have he : insEdgePerm M * insEdgePerm M = 1 := by
      ext z; rw [Equiv.Perm.mul_apply, insEdgePerm_involutive M z]; rfl
    rw [he, one_mul, inv_mul_cancel]
  edgePerm_involutive := insEdgePerm_involutive M
  isEmpty_fixedPoints_edgePerm :=
    ⟨fun x => insEdgePerm_fixedPointFree M x.1 x.2⟩

omit [Fintype D] in
@[simp] lemma insertedEdgeMap_vertexPerm :
    (insertedEdgeMap M c₁ c₂).vertexPerm = insVertexPerm M c₁ c₂ := rfl

omit [Fintype D] in
@[simp] lemma insertedEdgeMap_edgePerm :
    (insertedEdgeMap M c₁ c₂).edgePerm = insEdgePerm M := rfl

omit [Fintype D] in
@[simp] lemma insertedEdgeMap_facePerm :
    (insertedEdgeMap M c₁ c₂).facePerm = insFacePerm M c₁ c₂ := rfl

/-! ### Step 2 — the edge delta `|E'| = |E| + 1` -/

/-- **Edge delta.** The inserted-edge map has exactly one more edge. -/
theorem card_edge_insertedEdgeMap :
    Fintype.card (insertedEdgeMap M c₁ c₂).Edge = Fintype.card M.Edge + 1 := by
  rw [card_edge_eq_orbitCount, card_edge_eq_orbitCount, insertedEdgeMap_edgePerm]
  unfold insEdgePerm
  rw [orbitCount_sumCongr, orbitCount_swap_fin2]

/-! ### Step 3 — the vertex delta `|V'| = |V|`

This construction threads `a` and `b` into existing vertex rotations, so the
vertex count is unchanged. We read this off `orbitCount`: `σ' = swap (inl σc₁) a ·
swap (inl σc₂) b · (σ ⊕ 1)`. The base `σ ⊕ 1` has `orbitCount = V + 2` (two new
singleton orbits `a`, `b`). Each of the two transpositions joins a singleton orbit
(`b`, then `a`) to an `inl`-orbit — both *merges* — dropping the count back to `V`. -/

omit [Fintype D] [DecidableEq D] in
/-- `dartA ≠ dartB`. -/
private lemma dartA_ne_dartB : (dartA : D ⊕ Fin 2) ≠ dartB := by
  show (Sum.inr 0 : D ⊕ Fin 2) ≠ Sum.inr 1
  simp only [ne_eq, Sum.inr.injEq]; decide

omit [Fintype D] [DecidableEq D] in
/-- An `inl` dart is never `dartA`. -/
private lemma inl_ne_dartA (d : D) : (Sum.inl d : D ⊕ Fin 2) ≠ dartA := by
  simp [dartA]

omit [Fintype D] [DecidableEq D] in
/-- An `inl` dart is never `dartB`. -/
private lemma inl_ne_dartB (d : D) : (Sum.inl d : D ⊕ Fin 2) ≠ dartB := by
  simp [dartB]

omit [Fintype D] [DecidableEq D] in
/-- `σ ⊕ 1` fixes the new dart `dartA`. -/
private lemma sumCongr_one_fix_dartA (σ : Perm D) :
    σ.sumCongr 1 (dartA) = dartA := by
  show σ.sumCongr 1 (Sum.inr 0) = Sum.inr 0
  rw [Equiv.Perm.sumCongr_apply]; rfl

/-- The intermediate vertex permutation after the first (rightmost) splice swap. -/
private def insVertexPermStep1 (σ : Perm D) (c₂ : D) : Perm (D ⊕ Fin 2) :=
  Equiv.swap (Sum.inl (σ c₂)) (dartB) * σ.sumCongr 1

omit [Fintype D] in
/-- `dartA` is fixed by the first-step vertex permutation. -/
private lemma insVertexPermStep1_fix_dartA (σ : Perm D) (c₂ : D) :
    insVertexPermStep1 σ c₂ (dartA) = dartA := by
  unfold insVertexPermStep1
  rw [Equiv.Perm.mul_apply, sumCongr_one_fix_dartA,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (inl_ne_dartA _)) dartA_ne_dartB]

/-- **Vertex delta.** The inserted-edge map has the same number of vertices. -/
theorem card_vertex_insertedEdgeMap :
    Fintype.card (insertedEdgeMap M c₁ c₂).Vertex = Fintype.card M.Vertex := by
  rw [card_vertex_eq_orbitCount, card_vertex_eq_orbitCount, insertedEdgeMap_vertexPerm]
  -- σ' = swap (inl σc₁) a · (step1),  step1 = swap (inl σc₂) b · (σ ⊕ 1)
  have hbase : orbitCount (M.vertexPerm.sumCongr (1 : Perm (Fin 2)))
      = orbitCount M.vertexPerm + 2 := by
    rw [orbitCount_sumCongr, orbitCount_one_fin2]
  -- first merge: orbitCount (step1) = orbitCount (σ ⊕ 1) - 1 = V + 1
  have hstep1 : orbitCount (insVertexPermStep1 M.vertexPerm c₂)
      = orbitCount M.vertexPerm + 1 := by
    have hne : ¬ (M.vertexPerm.sumCongr (1 : Perm (Fin 2))).SameCycle
        (Sum.inl (M.vertexPerm c₂)) (dartB) :=
      sumCongr_not_sameCycle_inl_inr M.vertexPerm 1 (M.vertexPerm c₂) 1
    have := orbitCount_swap_mul_of_not_sameCycle (M.vertexPerm.sumCongr 1)
      (inl_ne_dartB _) hne
    rw [hbase] at this
    -- `this : V + 2 = orbitCount step1 + 1`
    unfold insVertexPermStep1
    omega
  -- second merge: orbitCount σ' = orbitCount step1 - 1 = V
  have hne2 : ¬ (insVertexPermStep1 M.vertexPerm c₂).SameCycle
      (Sum.inl (M.vertexPerm c₁)) (dartA) := by
    intro hsc
    -- `dartA` is fixed by step1, so SameCycle forces `inl σc₁ = dartA`, impossible
    have : (Sum.inl (M.vertexPerm c₁) : D ⊕ Fin 2) = dartA :=
      hsc.eq_of_right (insVertexPermStep1_fix_dartA M.vertexPerm c₂)
    exact inl_ne_dartA _ this
  have hfinal := orbitCount_swap_mul_of_not_sameCycle (insVertexPermStep1 M.vertexPerm c₂)
    (inl_ne_dartA _) hne2
  -- assemble: σ' = swap (inl σc₁) a · step1
  have hσ' : insVertexPerm M c₁ c₂
      = Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA) * insVertexPermStep1 M.vertexPerm c₂ := by
    unfold insVertexPerm insVertexPermStep1; rw [mul_assoc]
  rw [hσ']
  omega

/-! ### Step 4 — the face delta `|F'| = |F| ± 1`

The face count delta is the heart of D1-A. We exhibit the forced face permutation
as a product of two transpositions on top of the trivial extension `φ ⊕ (a b)`:
`φ' = swap (inl c₁) a · swap (inl c₂) b · (φ ⊕ (a b))`. The base `φ ⊕ (a b)` has
`orbitCount = F + 1` (one new 2-cycle orbit `{a,b}`). The first transposition
`swap (inl c₂) b` *merges* `{a,b}` into `c₂`'s face (always a merge: `b` is `inr`,
`inl c₂` is `inl`), giving `F`. The second `swap (inl c₁) a` then *splits* iff
`a` (now in `c₂`'s face) is same-cycle with `inl c₁` — which happens iff `c₁, c₂`
shared a face originally — and *merges* otherwise. Hence `F' = F + 1` (same face)
or `F' = F − 1` (different faces). -/

/-- The trivial sum extension of the face permutation, with the new darts a 2-cycle. -/
private def baseFacePerm (φ : Perm D) : Perm (D ⊕ Fin 2) :=
  φ.sumCongr (Equiv.swap 0 1)

omit [Fintype D] [DecidableEq D] in
/-- `baseFacePerm` sends `dartA ↦ dartB` and `dartB ↦ dartA`. -/
private lemma baseFacePerm_dartA (φ : Perm D) : baseFacePerm φ (dartA) = dartB := by
  show φ.sumCongr (Equiv.swap 0 1) (Sum.inr 0) = Sum.inr 1
  rw [Equiv.Perm.sumCongr_apply]; simp [Equiv.swap_apply_left]

omit [Fintype D] [DecidableEq D] in
private lemma baseFacePerm_dartB (φ : Perm D) : baseFacePerm φ (dartB) = dartA := by
  show φ.sumCongr (Equiv.swap 0 1) (Sum.inr 1) = Sum.inr 0
  rw [Equiv.Perm.sumCongr_apply]; simp [Equiv.swap_apply_right]

omit [Fintype D] [DecidableEq D] in
/-- On `inl` darts, `baseFacePerm φ` is `φ`. -/
private lemma baseFacePerm_inl (φ : Perm D) (d : D) :
    baseFacePerm φ (Sum.inl d) = Sum.inl (φ d) := by
  show φ.sumCongr (Equiv.swap 0 1) (Sum.inl d) = Sum.inl (φ d)
  rw [Equiv.Perm.sumCongr_apply]; rfl

omit [Fintype D] in
/-- The two corner transpositions `swap (inl c₁) a` and `swap (inl c₂) b` are
disjoint (given `c₁ ≠ c₂`), hence commute. -/
private lemma swap_disjoint_commute (hc : c₁ ≠ c₂) :
    Equiv.swap (Sum.inl c₁) (dartA) * Equiv.swap (Sum.inl c₂) (dartB)
      = Equiv.swap (Sum.inl c₂) (dartB) * Equiv.swap (Sum.inl c₁) (dartA) := by
  apply Equiv.ext; intro x
  have h1 : (Sum.inl c₁ : D ⊕ Fin 2) ≠ Sum.inl c₂ := by simp [hc]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all [inl_ne_dartA, inl_ne_dartB]

omit [Fintype D] in
/-- **The forced face permutation in product form.** Requires `c₁ ≠ c₂` (tail and
head are distinct darts), used to commute the two disjoint corner transpositions.
Proven by group algebra: invert the vertex splice, conjugate the two corner
transpositions past the diagonal `σ⁻¹ ⊕ 1`, recombine `σ⁻¹α = φ` on the inl block,
then commute the now-disjoint corner swaps. -/
private lemma insFacePerm_eq_product (hc : c₁ ≠ c₂) :
    insFacePerm M c₁ c₂ =
      Equiv.swap (Sum.inl c₁) (dartA) * Equiv.swap (Sum.inl c₂) (dartB) *
        baseFacePerm M.facePerm := by
  set Sg : Perm (D ⊕ Fin 2) := M.vertexPerm⁻¹.sumCongr 1 with hSg
  set s2 : Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB) with hs2
  set s1 : Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA) with hs1
  set t2 : Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl c₂) (dartB) with ht2
  set t1 : Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl c₁) (dartA) with ht1
  -- σ'⁻¹ = Sg * s2 * s1
  have hinv : (insVertexPerm M c₁ c₂)⁻¹ = Sg * s2 * s1 := by
    unfold insVertexPerm
    rw [mul_inv_rev, mul_inv_rev, hs1, hs2, Equiv.swap_inv, Equiv.swap_inv, hSg,
      Equiv.Perm.sumCongr_inv, inv_one, mul_assoc]
  -- conjugation facts
  have hSginl : ∀ c : D, Sg (Sum.inl (M.vertexPerm c)) = Sum.inl c := by
    intro c; rw [hSg, Equiv.Perm.sumCongr_apply]; simp
  have hSga : Sg (dartA) = dartA := by
    rw [hSg]; show M.vertexPerm⁻¹.sumCongr 1 (Sum.inr 0) = Sum.inr 0
    rw [Equiv.Perm.sumCongr_apply]; rfl
  have hSgb : Sg (dartB) = dartB := by
    rw [hSg]; show M.vertexPerm⁻¹.sumCongr 1 (Sum.inr 1) = Sum.inr 1
    rw [Equiv.Perm.sumCongr_apply]; rfl
  have hconj2 : Sg * s2 = t2 * Sg := by
    have h := (Equiv.swap_apply_apply Sg (Sum.inl (M.vertexPerm c₂)) (dartB)).symm
    rw [hSginl, hSgb] at h
    rw [hs2, ht2, ← h, mul_assoc, inv_mul_cancel, mul_one]
  have hconj1 : Sg * s1 = t1 * Sg := by
    have h := (Equiv.swap_apply_apply Sg (Sum.inl (M.vertexPerm c₁)) (dartA)).symm
    rw [hSginl, hSga] at h
    rw [hs1, ht1, ← h, mul_assoc, inv_mul_cancel, mul_one]
  have hSgedge : Sg * insEdgePerm M = baseFacePerm M.facePerm := by
    rw [hSg]; unfold insEdgePerm baseFacePerm
    rw [Equiv.Perm.sumCongr_mul, one_mul, M.facePerm_eq]
  -- assemble by group algebra
  unfold insFacePerm
  rw [hinv]
  -- Sg * s2 * s1 * edge = t2 * Sg * s1 * edge = t2 * t1 * Sg * edge = t2 * t1 * base
  calc Sg * s2 * s1 * insEdgePerm M
      = t2 * Sg * s1 * insEdgePerm M := by rw [hconj2]
    _ = t2 * (Sg * s1) * insEdgePerm M := by rw [mul_assoc t2 Sg s1]
    _ = t2 * (t1 * Sg) * insEdgePerm M := by rw [hconj1]
    _ = t2 * t1 * (Sg * insEdgePerm M) := by simp only [mul_assoc]
    _ = t2 * t1 * baseFacePerm M.facePerm := by rw [hSgedge]
    _ = t1 * t2 * baseFacePerm M.facePerm := by
          rw [ht1, ht2, swap_disjoint_commute c₁ c₂ hc]

omit [Fintype D] [DecidableEq D] in
/-- The new darts are same-cycle in `baseFacePerm` (they form the new 2-cycle). -/
private lemma baseFacePerm_sameCycle_darts (φ : Perm D) :
    (baseFacePerm φ).SameCycle (dartA) (dartB) := by
  refine (sumCongr_sameCycle_inr φ (Equiv.swap 0 1)).mpr ?_
  exact ⟨1, by rw [zpow_one, Equiv.swap_apply_left]⟩

omit [DecidableEq D] in
/-- `orbitCount (baseFacePerm φ) = orbitCount φ + 1`. -/
private lemma orbitCount_baseFacePerm (φ : Perm D) :
    orbitCount (baseFacePerm φ) = orbitCount φ + 1 := by
  unfold baseFacePerm; rw [orbitCount_sumCongr, orbitCount_swap_fin2]

/-- The intermediate face permutation after the first (inner) corner swap. -/
private def insFacePermStep1 (φ : Perm D) (c₂ : D) : Perm (D ⊕ Fin 2) :=
  Equiv.swap (Sum.inl c₂) (dartB) * baseFacePerm φ

/-- The first inner swap is always a *merge* (it joins the new edge `{a,b}` to
`c₂`'s face), so the intermediate has `orbitCount = F`. -/
private lemma orbitCount_insFacePermStep1 (φ : Perm D) (c₂ : D) :
    orbitCount (insFacePermStep1 φ c₂) = orbitCount φ := by
  have hne : ¬ (baseFacePerm φ).SameCycle (Sum.inl c₂) (dartB) := by
    unfold baseFacePerm; exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap 0 1) c₂ 1
  have := orbitCount_swap_mul_of_not_sameCycle (baseFacePerm φ) (inl_ne_dartB _) hne
  rw [orbitCount_baseFacePerm] at this
  unfold insFacePermStep1
  omega

/-- **Same-face bridge.** In the intermediate `insFacePermStep1`, `inl c₁` and the
new dart `dartA` are same-cycle iff `c₁` and `c₂` shared a `φ`-face. -/
private lemma insFacePermStep1_sameCycle_iff (φ : Perm D) (c₁ c₂ : D) :
    (insFacePermStep1 φ c₂).SameCycle (Sum.inl c₁) (dartA) ↔ φ.SameCycle c₁ c₂ := by
  unfold insFacePermStep1
  have hne : ¬ (baseFacePerm φ).SameCycle (Sum.inl c₂) (dartB) := by
    unfold baseFacePerm; exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap 0 1) c₂ 1
  rw [sameCycle_swap_mul_iff_of_not_sameCycle (baseFacePerm φ) hne]
  -- evaluate the three disjuncts in `baseFacePerm`
  have hbase_inl_inr : ∀ (d : D) (j : Fin 2),
      ¬ (baseFacePerm φ).SameCycle (Sum.inl d) (Sum.inr j) := by
    intro d j; unfold baseFacePerm
    exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap 0 1) d j
  have hbase_inl : (baseFacePerm φ).SameCycle (Sum.inl c₁) (Sum.inl c₂) ↔ φ.SameCycle c₁ c₂ := by
    unfold baseFacePerm; exact sumCongr_sameCycle_inl φ (Equiv.swap 0 1)
  constructor
  · rintro (h | ⟨h12, _⟩ | ⟨h1b, _⟩)
    · exact absurd h (hbase_inl_inr c₁ 0)
    · exact hbase_inl.mp h12
    · exact absurd h1b (hbase_inl_inr c₁ 1)
  · intro h
    -- the middle disjunct holds: inl c₁ ~ inl c₂ (= φ.SameCycle) and dartA ~ dartB
    exact Or.inr (Or.inl ⟨hbase_inl.mpr h, baseFacePerm_sameCycle_darts φ⟩)

/-- Old darts have exactly their old face-cycle relation after the intermediate
merge that attaches the new edge's two-dart face to `c₂`'s old face. -/
private lemma insFacePermStep1_sameCycle_inl_inl_iff (φ : Perm D) (c₂ x y : D) :
    (insFacePermStep1 φ c₂).SameCycle (Sum.inl x) (Sum.inl y) ↔
      φ.SameCycle x y := by
  unfold insFacePermStep1
  have hne : ¬ (baseFacePerm φ).SameCycle (Sum.inl c₂) (dartB) := by
    unfold baseFacePerm
    exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap 0 1) c₂ 1
  rw [sameCycle_swap_mul_iff_of_not_sameCycle (baseFacePerm φ) hne]
  have hbase_inl_inl :
      (baseFacePerm φ).SameCycle (Sum.inl x) (Sum.inl y) ↔ φ.SameCycle x y := by
    unfold baseFacePerm
    exact sumCongr_sameCycle_inl φ (Equiv.swap 0 1)
  have hbase_inl_inr : ∀ (d : D) (j : Fin 2),
      ¬ (baseFacePerm φ).SameCycle (Sum.inl d) (Sum.inr j) := by
    intro d j
    unfold baseFacePerm
    exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap 0 1) d j
  constructor
  · rintro (h | ⟨_hx, hy⟩ | ⟨hx, _hy⟩)
    · exact hbase_inl_inl.mp h
    · exact absurd hy (hbase_inl_inr y 1)
    · exact absurd hx (hbase_inl_inr x 1)
  · intro h
    exact Or.inl (hbase_inl_inl.mpr h)

/-- Representative-level map collapsing the intermediate face permutation
`insFacePermStep1 φ c₂` back to the old `φ`-face quotient.  Old darts keep their
old face; the two new darts belong to the old face of `c₂`. -/
private noncomputable def insFacePermStep1QuotToFun (φ : Perm D) (c₂ : D) :
    D ⊕ Fin 2 → Quotient (Equiv.Perm.SameCycle.setoid φ)
  | Sum.inl d => Quotient.mk (Equiv.Perm.SameCycle.setoid φ) d
  | Sum.inr _ => Quotient.mk (Equiv.Perm.SameCycle.setoid φ) c₂

omit [Fintype D] [DecidableEq D] in
private lemma insFacePermStep1QuotToFun_eq_of_base_same_c2
    (φ : Perm D) (c₂ : D) {s : D ⊕ Fin 2}
    (h : (baseFacePerm φ).SameCycle s (Sum.inl c₂)) :
    insFacePermStep1QuotToFun φ c₂ s =
      Quotient.mk (Equiv.Perm.SameCycle.setoid φ) c₂ := by
  cases s with
  | inl d =>
      change Quotient.mk (Equiv.Perm.SameCycle.setoid φ) d =
        Quotient.mk (Equiv.Perm.SameCycle.setoid φ) c₂
      apply Quotient.sound
      have h' : (φ.sumCongr (Equiv.swap (0 : Fin 2) 1)).SameCycle
          (Sum.inl d) (Sum.inl c₂) := by
        simpa [baseFacePerm] using h
      exact (sumCongr_sameCycle_inl φ (Equiv.swap (0 : Fin 2) 1)).mp h'
  | inr _ => rfl

omit [Fintype D] [DecidableEq D] in
private lemma insFacePermStep1QuotToFun_eq_of_base_same_dartB
    (φ : Perm D) (c₂ : D) {s : D ⊕ Fin 2}
    (h : (baseFacePerm φ).SameCycle s (dartB)) :
    insFacePermStep1QuotToFun φ c₂ s =
      Quotient.mk (Equiv.Perm.SameCycle.setoid φ) c₂ := by
  cases s with
  | inl d =>
      exfalso
      have h' : (φ.sumCongr (Equiv.swap (0 : Fin 2) 1)).SameCycle
          (Sum.inl d) (Sum.inr (1 : Fin 2)) := by
        simpa [baseFacePerm, dartB] using h
      exact (sumCongr_not_sameCycle_inl_inr φ (Equiv.swap (0 : Fin 2) 1) d
        (1 : Fin 2)) h'
  | inr _ => rfl

/-- The intermediate quotient map is constant on `insFacePermStep1`-orbits. -/
private lemma insFacePermStep1QuotToFun_respects (φ : Perm D) (c₂ : D)
    {s t : D ⊕ Fin 2} (hst : (insFacePermStep1 φ c₂).SameCycle s t) :
    insFacePermStep1QuotToFun φ c₂ s = insFacePermStep1QuotToFun φ c₂ t := by
  classical
  unfold insFacePermStep1 at hst
  have hne : ¬ (baseFacePerm φ).SameCycle (Sum.inl c₂) (dartB) := by
    unfold baseFacePerm
    exact sumCongr_not_sameCycle_inl_inr φ (Equiv.swap (0 : Fin 2) 1) c₂ (1 : Fin 2)
  rcases (sameCycle_swap_mul_iff_of_not_sameCycle (baseFacePerm φ) hne).mp hst with
    hbase | ⟨hs, ht⟩ | ⟨hs, ht⟩
  · cases s with
    | inl d =>
        cases t with
        | inl e =>
            change Quotient.mk (Equiv.Perm.SameCycle.setoid φ) d =
              Quotient.mk (Equiv.Perm.SameCycle.setoid φ) e
            apply Quotient.sound
            have h' :
                (φ.sumCongr (Equiv.swap (0 : Fin 2) 1)).SameCycle
                  (Sum.inl d) (Sum.inl e) := by
              simpa [baseFacePerm] using hbase
            exact (sumCongr_sameCycle_inl φ (Equiv.swap (0 : Fin 2) 1)).mp h'
        | inr i =>
            exfalso
            have h' :
                (φ.sumCongr (Equiv.swap (0 : Fin 2) 1)).SameCycle
                  (Sum.inl d) (Sum.inr i) := by
              simpa [baseFacePerm] using hbase
            exact (sumCongr_not_sameCycle_inl_inr φ (Equiv.swap (0 : Fin 2) 1) d i) h'
    | inr i =>
        cases t with
        | inl e =>
            exfalso
            have h' :
                (φ.sumCongr (Equiv.swap (0 : Fin 2) 1)).SameCycle
                  (Sum.inl e) (Sum.inr i) := by
              simpa [baseFacePerm] using hbase.symm
            exact (sumCongr_not_sameCycle_inl_inr φ (Equiv.swap (0 : Fin 2) 1) e i) h'
        | inr _ => rfl
  · rw [insFacePermStep1QuotToFun_eq_of_base_same_c2 φ c₂ hs,
      insFacePermStep1QuotToFun_eq_of_base_same_dartB φ c₂ ht]
  · rw [insFacePermStep1QuotToFun_eq_of_base_same_dartB φ c₂ hs,
      insFacePermStep1QuotToFun_eq_of_base_same_c2 φ c₂ ht]

/-- Quotient map from the intermediate face permutation back to old faces. -/
noncomputable def insFacePermStep1QuotMap (φ : Perm D) (c₂ : D) :
    Quotient (Equiv.Perm.SameCycle.setoid (insFacePermStep1 φ c₂)) →
      Quotient (Equiv.Perm.SameCycle.setoid φ) :=
  Quotient.lift (insFacePermStep1QuotToFun φ c₂)
    (fun _ _ hst => insFacePermStep1QuotToFun_respects φ c₂ hst)

theorem insFacePermStep1QuotMap_surjective (φ : Perm D) (c₂ : D) :
    Function.Surjective (insFacePermStep1QuotMap φ c₂) := by
  intro r
  induction r using Quotient.ind with
  | _ d =>
      refine ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid (insFacePermStep1 φ c₂))
        (Sum.inl d), rfl⟩

theorem card_insFacePermStep1_quotient (φ : Perm D) (c₂ : D) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (insFacePermStep1 φ c₂))) =
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid φ)) := by
  change orbitCount (insFacePermStep1 φ c₂) = orbitCount φ
  exact orbitCount_insFacePermStep1 φ c₂

/-- The intermediate face quotient is equivalent to the original old-face quotient. -/
noncomputable def insFacePermStep1QuotEquiv (φ : Perm D) (c₂ : D) :
    Quotient (Equiv.Perm.SameCycle.setoid (insFacePermStep1 φ c₂)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid φ) :=
  Equiv.ofBijective (insFacePermStep1QuotMap φ c₂)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨insFacePermStep1QuotMap_surjective φ c₂,
        card_insFacePermStep1_quotient φ c₂⟩)

@[simp] theorem insFacePermStep1QuotEquiv_mk_inl (φ : Perm D) (c₁ c₂ : D) :
    insFacePermStep1QuotEquiv φ c₂
        (Quotient.mk (Equiv.Perm.SameCycle.setoid (insFacePermStep1 φ c₂))
          (Sum.inl c₁)) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid φ) c₁ :=
  rfl

/-- Transport the split-cycle pool of the intermediate face permutation to the
old-face split pool. -/
noncomputable def insFacePermStep1SplitPoolEquiv (φ : Perm D) (c₁ c₂ : D) :
    SplitCyclePool (insFacePermStep1 φ c₂) (Sum.inl c₁) ≃
      SplitCyclePool φ c₁ :=
  Equiv.sumCongr
    ((insFacePermStep1QuotEquiv φ c₂).subtypeEquiv (by
      intro r
      constructor
      · intro hr hnew
        apply hr
        apply (insFacePermStep1QuotEquiv φ c₂).injective
        simpa using hnew
      · intro hr hold
        apply hr
        simpa using congrArg (insFacePermStep1QuotEquiv φ c₂) hold))
    (Equiv.refl (Fin 2))

omit [Fintype D] in
/-- Face-permutation product decomposition for a same-face edge insertion:
first merge the new two-dart face into `c₂`'s face, then split the resulting
cycle at `c₁` and the new dart `dartA`. -/
theorem insertedEdgeMap_facePerm_eq_splitStep
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂) :
    (insertedEdgeMap M c₁ c₂).facePerm =
      Equiv.swap (Sum.inl c₁) (dartA) * insFacePermStep1 M.facePerm c₂ := by
  rw [insertedEdgeMap_facePerm, insFacePerm_eq_product M c₁ c₂ hc]
  change Equiv.swap (Sum.inl c₁) (dartA) *
      Equiv.swap (Sum.inl c₂) (dartB) * baseFacePerm M.facePerm =
    Equiv.swap (Sum.inl c₁) (dartA) *
      (Equiv.swap (Sum.inl c₂) (dartB) * baseFacePerm M.facePerm)
  rw [mul_assoc]

/-- If `c₁` and `c₂` lie in one old face, then after the intermediate merge
`Sum.inl c₁` and `dartA` lie in one face-cycle. -/
private theorem insFacePermStep1_sameCycle_inl_dartA_of_sameCycle
    (φ : Perm D) (c₁ c₂ : D) (hsame : φ.SameCycle c₁ c₂) :
    (insFacePermStep1 φ c₂).SameCycle (Sum.inl c₁) (dartA) :=
  (insFacePermStep1_sameCycle_iff φ c₁ c₂).mpr hsame

/-- The inserted face quotient in the same-face case is exactly old faces except
the split face, plus the two new split sides. -/
noncomputable def insertedFaceSplitPoolEquiv
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    (insertedEdgeMap M c₁ c₂).Face ≃
      ({f : M.Face // f ≠ M.Face_mk c₁} ⊕ Fin 2) :=
  (quotientSameCycleEquivOfPermEq (insertedEdgeMap_facePerm_eq_splitStep M c₁ c₂ hc)).trans
    ((splitCycleQuotEquiv (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
      (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame)).trans
      (insFacePermStep1SplitPoolEquiv M.facePerm c₁ c₂))

/-- An old dart outside the split face is carried to its old face by the
inserted-face split equivalence. -/
@[simp] theorem insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle
    (M : CombinatorialMap D) (c₁ c₂ x : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) (hx : ¬ M.facePerm.SameCycle x c₁) :
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl x)) =
      Sum.inl ⟨M.Face_mk x, by
        intro hq
        exact hx (Quotient.eq''.mp hq)⟩ := by
  change insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
          (Sum.inl x)) =
      Sum.inl ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid M.facePerm) x, by
        intro hq
        exact hx (Quotient.eq''.mp hq)⟩
  have hxstep :
      ¬ (insFacePermStep1 M.facePerm c₂).SameCycle (Sum.inl x) (Sum.inl c₁) := by
    intro h
    exact hx ((insFacePermStep1_sameCycle_inl_inl_iff M.facePerm c₂ x c₁).mp h)
  change (insFacePermStep1SplitPoolEquiv M.facePerm c₁ c₂)
      ((splitCycleQuotEquiv (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
        (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame))
          ((quotientSameCycleEquivOfPermEq
            (insertedEdgeMap_facePerm_eq_splitStep M c₁ c₂ hc))
            (Quotient.mk
              (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
              (Sum.inl x)))) =
    Sum.inl ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid M.facePerm) x, by
      intro hq
      exact hx (Quotient.eq''.mp hq)⟩
  rw [quotientSameCycleEquivOfPermEq_mk]
  simp [insFacePermStep1SplitPoolEquiv, hxstep]

/-- The inserted-face split equivalence names the side containing the old cut
corner `c₁` as `0 : Fin 2`. -/
@[simp] theorem insertedFaceSplitPoolEquiv_mk_inl_left
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl c₁)) =
      Sum.inr (0 : Fin 2) := by
  change insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
          (Sum.inl c₁)) =
      Sum.inr (0 : Fin 2)
  change (insFacePermStep1SplitPoolEquiv M.facePerm c₁ c₂)
      ((splitCycleQuotEquiv (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
        (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame))
          ((quotientSameCycleEquivOfPermEq
            (insertedEdgeMap_facePerm_eq_splitStep M c₁ c₂ hc))
            (Quotient.mk
              (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
              (Sum.inl c₁)))) =
    Sum.inr (0 : Fin 2)
  rw [quotientSameCycleEquivOfPermEq_mk]
  simp [insFacePermStep1SplitPoolEquiv]

/-- The inserted-face split equivalence names the side containing the new dart
`dartA` as `1 : Fin 2`. -/
@[simp] theorem insertedFaceSplitPoolEquiv_mk_dartA_right
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (dartA : D ⊕ Fin 2)) =
      Sum.inr (1 : Fin 2) := by
  change insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
          (dartA : D ⊕ Fin 2)) =
      Sum.inr (1 : Fin 2)
  change (insFacePermStep1SplitPoolEquiv M.facePerm c₁ c₂)
      ((splitCycleQuotEquiv (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
        (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame))
          ((quotientSameCycleEquivOfPermEq
            (insertedEdgeMap_facePerm_eq_splitStep M c₁ c₂ hc))
            (Quotient.mk
              (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
              (dartA : D ⊕ Fin 2)))) =
    Sum.inr (1 : Fin 2)
  rw [quotientSameCycleEquivOfPermEq_mk]
  simp [insFacePermStep1SplitPoolEquiv]

/-- The inserted-face split equivalence names the side containing the new dart
`dartB` as `0 : Fin 2`, the same side as the old cut corner `c₁`. -/
@[simp] theorem insertedFaceSplitPoolEquiv_mk_dartB_left
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (dartB : D ⊕ Fin 2)) =
      Sum.inr (0 : Fin 2) := by
  change insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        (Quotient.mk
          (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
          (dartB : D ⊕ Fin 2)) =
      Sum.inr (0 : Fin 2)
  change (insFacePermStep1SplitPoolEquiv M.facePerm c₁ c₂)
      ((splitCycleQuotEquiv (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
        (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame))
          ((quotientSameCycleEquivOfPermEq
            (insertedEdgeMap_facePerm_eq_splitStep M c₁ c₂ hc))
            (Quotient.mk
              (Equiv.Perm.SameCycle.setoid (insertedEdgeMap M c₁ c₂).facePerm)
              (dartB : D ⊕ Fin 2)))) =
    Sum.inr (0 : Fin 2)
  rw [quotientSameCycleEquivOfPermEq_mk]
  have hstep_apply :
      (insFacePermStep1 M.facePerm c₂) (dartB : D ⊕ Fin 2) = dartA := by
    change (Equiv.swap (Sum.inl c₂) (dartB : D ⊕ Fin 2) *
        baseFacePerm M.facePerm) (dartB : D ⊕ Fin 2) = dartA
    rw [Equiv.Perm.mul_apply]
    have hbase : (baseFacePerm M.facePerm) (dartB : D ⊕ Fin 2) = dartA := by
      simp [baseFacePerm, dartA, dartB]
    rw [hbase]
    exact Equiv.swap_apply_of_ne_of_ne (by simp [dartA]) (by simp [dartA, dartB])
  have hstepDartB :
      (insFacePermStep1 M.facePerm c₂).SameCycle (dartB : D ⊕ Fin 2) (Sum.inl c₁) := by
    have hstepDartA :
        (insFacePermStep1 M.facePerm c₂).SameCycle (dartA : D ⊕ Fin 2) (Sum.inl c₁) :=
      (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame).symm
    have hBA :
        (insFacePermStep1 M.facePerm c₂).SameCycle (dartB : D ⊕ Fin 2) dartA :=
      ⟨1, by simpa [zpow_one] using hstep_apply⟩
    exact hBA.trans hstepDartA
  have hleft :
      (Equiv.swap (Sum.inl c₁) (dartA : D ⊕ Fin 2) *
        insFacePermStep1 M.facePerm c₂).SameCycle (dartB : D ⊕ Fin 2) (Sum.inl c₁) := by
    exact ⟨1, by
      rw [zpow_one, Equiv.Perm.mul_apply, hstep_apply]
      exact Equiv.swap_apply_right (Sum.inl c₁) (dartA : D ⊕ Fin 2)⟩
  rw [splitCycleQuotEquiv_mk_of_sameCycle_left
    (insFacePermStep1 M.facePerm c₂) (inl_ne_dartA c₁)
    (insFacePermStep1_sameCycle_inl_dartA_of_sameCycle M.facePerm c₁ c₂ hsame)
    hstepDartB hleft]
  simp [insFacePermStep1SplitPoolEquiv]

/-- A same-face insertion does not change the face-cycle relation between old
darts outside the split face. -/
theorem insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_of_not_sameCycle
    (M : CombinatorialMap D) (c₁ c₂ x y : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂)
    (hx : ¬ M.facePerm.SameCycle x c₁) (hy : ¬ M.facePerm.SameCycle y c₁) :
    (insertedEdgeMap M c₁ c₂).facePerm.SameCycle (Sum.inl x) (Sum.inl y) ↔
      M.facePerm.SameCycle x y := by
  constructor
  · intro hxy
    have himg := congrArg (insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame)
      (Quotient.sound hxy)
    rw [insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle M c₁ c₂ x hc hsame hx,
      insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle M c₁ c₂ y hc hsame hy] at himg
    have hface : M.Face_mk x = M.Face_mk y := by
      exact congrArg Subtype.val (Sum.inl.inj himg)
    exact Quotient.eq''.mp hface
  · intro hxy
    have hface : M.Face_mk x = M.Face_mk y := Quotient.sound hxy
    have himg :
        insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl x)) =
          insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
            ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl y)) := by
      rw [insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle M c₁ c₂ x hc hsame hx,
        insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle M c₁ c₂ y hc hsame hy]
      apply congrArg Sum.inl
      exact Subtype.ext hface
    have hface' :
        (insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl x) =
          (insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl y) :=
      (insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame).injective himg
    exact Quotient.eq''.mp hface'

/-- **Face delta (split / merge dichotomy).** Inserting the edge spliced at corners
`c₁ ≠ c₂`:
* if `c₁, c₂` lie on a common face (`facePerm`-orbit) the face *splits*:
  `|F'| = |F| + 1`;
* otherwise the two faces *merge*: `|F| = |F'| + 1`. -/
theorem card_face_insertedEdgeMap (hc : c₁ ≠ c₂) :
    (M.facePerm.SameCycle c₁ c₂ →
        Fintype.card (insertedEdgeMap M c₁ c₂).Face = Fintype.card M.Face + 1) ∧
      (¬ M.facePerm.SameCycle c₁ c₂ →
        Fintype.card M.Face = Fintype.card (insertedEdgeMap M c₁ c₂).Face + 1) := by
  -- rewrite both face counts as orbit counts; φ' = t1 * (step1)
  have hF' : Fintype.card (insertedEdgeMap M c₁ c₂).Face
      = orbitCount (Equiv.swap (Sum.inl c₁) (dartA) * insFacePermStep1 M.facePerm c₂) := by
    rw [card_face_eq_orbitCount, insertedEdgeMap_facePerm, insFacePerm_eq_product M c₁ c₂ hc,
      insFacePermStep1, mul_assoc]
  have hF : Fintype.card M.Face = orbitCount M.facePerm := card_face_eq_orbitCount M
  -- the inner orbit count is F
  have hstep1 : orbitCount (insFacePermStep1 M.facePerm c₂) = orbitCount M.facePerm :=
    orbitCount_insFacePermStep1 M.facePerm c₂
  -- the same-face bridge for the outer swap
  have hbridge := insFacePermStep1_sameCycle_iff M.facePerm c₁ c₂
  -- the outer swap dichotomy
  have hdich := orbitCount_swap_mul (insFacePermStep1 M.facePerm c₂)
    (p := Sum.inl c₁) (q := dartA) (inl_ne_dartA _)
  refine ⟨fun hsc => ?_, fun hsc => ?_⟩
  · -- same face → split
    rw [hF', hF]
    have h := hdich.1 (hbridge.mpr hsc)
    omega
  · -- different face → merge
    rw [hF', hF]
    have h := hdich.2 (fun hc' => hsc (hbridge.mp hc'))
    omega

/-! ### Step 5 — Euler-characteristic monotonicity

Combining the three deltas (`V' = V`, `E' = E + 1`, `F' = F ± 1`):
* facial insertion (`c₁, c₂` share a face): `χ' = χ` (a face splits, edge count and
  face count both rise by one);
* non-facial insertion: `χ' = χ − 2` (faces merge), so `χ` strictly drops.
In all cases `χ' ≤ χ`. -/

/-- **Euler characteristic in the facial (same-face) case is unchanged.** -/
theorem eulerCharacteristic_insertedEdgeMap_of_sameCycle (hc : c₁ ≠ c₂)
    (h : M.facePerm.SameCycle c₁ c₂) :
    (insertedEdgeMap M c₁ c₂).eulerCharacteristic = M.eulerCharacteristic := by
  unfold CombinatorialMap.eulerCharacteristic
  rw [card_edge_insertedEdgeMap, card_vertex_insertedEdgeMap,
    (card_face_insertedEdgeMap M c₁ c₂ hc).1 h]
  push_cast
  ring

/-- **Euler characteristic strictly drops by 2 in the non-facial case.** -/
theorem eulerCharacteristic_insertedEdgeMap_of_not_sameCycle (hc : c₁ ≠ c₂)
    (h : ¬ M.facePerm.SameCycle c₁ c₂) :
    (insertedEdgeMap M c₁ c₂).eulerCharacteristic = M.eulerCharacteristic - 2 := by
  unfold CombinatorialMap.eulerCharacteristic
  have hface := (card_face_insertedEdgeMap M c₁ c₂ hc).2 h
  rw [card_edge_insertedEdgeMap, card_vertex_insertedEdgeMap]
  -- `card M.Face = card Face' + 1`, so `card Face' = card M.Face - 1` in ℤ
  have : (Fintype.card (insertedEdgeMap M c₁ c₂).Face : ℤ) = (Fintype.card M.Face : ℤ) - 1 := by
    have := hface; push_cast [this]; omega
  rw [this]; push_cast; ring

/-- **χ-monotonicity (D1-A).** Inserting an edge never increases the Euler
characteristic; it is unchanged exactly in the facial (same-face) case. -/
theorem eulerCharacteristic_insertedEdgeMap_le (hc : c₁ ≠ c₂) :
    (insertedEdgeMap M c₁ c₂).eulerCharacteristic ≤ M.eulerCharacteristic := by
  by_cases h : M.facePerm.SameCycle c₁ c₂
  · rw [eulerCharacteristic_insertedEdgeMap_of_sameCycle M c₁ c₂ hc h]
  · rw [eulerCharacteristic_insertedEdgeMap_of_not_sameCycle M c₁ c₂ hc h]; omega

/-- **Planarity is preserved by facial edge insertion.** If the two splice
corners lie on a common face, then inserting the new edge keeps Euler
characteristic `2`. -/
theorem isPlanar_insertedEdgeMap_of_sameCycle (hc : c₁ ≠ c₂)
    (hplanar : M.IsPlanar) (h : M.facePerm.SameCycle c₁ c₂) :
    (insertedEdgeMap M c₁ c₂).IsPlanar := by
  unfold CombinatorialMap.IsPlanar
  rw [eulerCharacteristic_insertedEdgeMap_of_sameCycle M c₁ c₂ hc h]
  exact hplanar

/-- **Converse of facial edge insertion.** If both the original map and the
edge-inserted map are planar, then the two splice corners must already lie on a
common face. -/
theorem sameCycle_of_isPlanar_insertedEdgeMap (hc : c₁ ≠ c₂)
    (hplanar : (insertedEdgeMap M c₁ c₂).IsPlanar) (hMplanar : M.IsPlanar) :
    M.facePerm.SameCycle c₁ c₂ := by
  by_cases h : M.facePerm.SameCycle c₁ c₂
  · exact h
  · exfalso
    have hchi := eulerCharacteristic_insertedEdgeMap_of_not_sameCycle
      (M := M) (c₁ := c₁) (c₂ := c₂) hc h
    unfold CombinatorialMap.IsPlanar at hplanar hMplanar
    rw [hplanar, hMplanar] at hchi
    norm_num at hchi

end Construction

/-
## Leaf-edge insertion

`insertedEdgeMap` handles the cycle-edge case: both new darts are threaded into
existing vertex cycles, so the vertex count is unchanged.  For the tree-first
residual-map induction one also needs the complementary operation that inserts a
new edge whose second endpoint is a **fresh leaf vertex**.  Combinatorially,
only one new dart is spliced into an existing vertex cycle; the other remains a
singleton vertex orbit.

The Euler deltas are then the expected planar-tree ones:
* one new edge orbit,
* one new vertex orbit, and
* the unique old face is preserved (the new edge does not split a face).

Hence the Euler characteristic is unchanged.
-/
section LeafConstruction

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D) (c : D)

/-- The dart threaded into the existing vertex cycle. -/
abbrev leafDartA : D ⊕ Fin 2 := Sum.inr 0

/-- The dart anchored at the new leaf vertex. -/
abbrev leafDartB : D ⊕ Fin 2 := Sum.inr 1

/-- The edge permutation for leaf-edge insertion: the old edge involution on the
existing darts, and the transposition of the two new darts. -/
def insertedLeafEdgePerm : Equiv.Perm (D ⊕ Fin 2) :=
  M.edgePerm.sumCongr (Equiv.swap 0 1)

/-- The vertex permutation for leaf-edge insertion.  The new dart `leafDartA`
is spliced into the old vertex cycle immediately after `c`; `leafDartB` stays a
singleton orbit, representing the new leaf vertex. -/
def insertedLeafVertexPerm : Equiv.Perm (D ⊕ Fin 2) :=
  Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA) * M.vertexPerm.sumCongr 1

/-- The new dart threaded into the old vertex cycle when the old endpoint is
indexed by the Boolean `b`. -/
abbrev leafThreadDart (b : Bool) : D ⊕ Fin 2 :=
  Sum.inr (if b then (1 : Fin 2) else (0 : Fin 2))

/-- The new dart left as the singleton leaf vertex when the old endpoint is
indexed by the Boolean `b`. -/
abbrev leafSingletonDart (b : Bool) : D ⊕ Fin 2 :=
  Sum.inr (if b then (0 : Fin 2) else (1 : Fin 2))

/-- The vertex permutation for leaf-edge insertion when either new dart may be
the dart threaded into the old vertex cycle. -/
def insertedLeafVertexPermAt (b : Bool) : Equiv.Perm (D ⊕ Fin 2) :=
  Equiv.swap (Sum.inl (M.vertexPerm c)) (leafThreadDart (D := D) b) *
    M.vertexPerm.sumCongr 1

/-- The base face permutation before splicing the new dart into an old face: the
old face permutation on the existing darts and the transposition of the two new
darts. -/
private def leafBaseFacePerm : Equiv.Perm (D ⊕ Fin 2) :=
  M.facePerm.sumCongr (Equiv.swap 0 1)

/-- The forced face permutation for leaf-edge insertion. -/
def insertedLeafFacePerm : Equiv.Perm (D ⊕ Fin 2) :=
  (insertedLeafVertexPerm M c)⁻¹ * insertedLeafEdgePerm M

/-- The forced face permutation for the Boolean-indexed leaf-edge insertion. -/
def insertedLeafFacePermAt (b : Bool) : Equiv.Perm (D ⊕ Fin 2) :=
  (insertedLeafVertexPermAt M c b)⁻¹ * insertedLeafEdgePerm M

omit [Fintype D] [DecidableEq D] in
/-- `insertedLeafEdgePerm` is an involution. -/
lemma insertedLeafEdgePerm_involutive : Function.Involutive (insertedLeafEdgePerm M) := by
  intro x
  show insertedLeafEdgePerm M (insertedLeafEdgePerm M x) = x
  rw [← Equiv.Perm.mul_apply]
  unfold insertedLeafEdgePerm
  rw [Equiv.Perm.sumCongr_mul]
  have he : M.edgePerm * M.edgePerm = 1 := by
    ext z
    rw [Equiv.Perm.mul_apply, M.edgePerm_involutive z]
    rfl
  rw [he, show Equiv.swap (0 : Fin 2) 1 * Equiv.swap 0 1 = 1 from Equiv.swap_mul_self _ _,
    Equiv.Perm.sumCongr_one, Equiv.Perm.one_apply]

omit [Fintype D] [DecidableEq D] in
/-- `insertedLeafEdgePerm` is fixed-point-free. -/
lemma insertedLeafEdgePerm_fixedPointFree (x : D ⊕ Fin 2) :
    insertedLeafEdgePerm M x ≠ x := by
  unfold insertedLeafEdgePerm
  cases x with
  | inl d =>
      rw [Equiv.Perm.sumCongr_apply]
      simp only [Sum.map_inl, ne_eq, Sum.inl.injEq]
      intro hd
      exact (M.isEmpty_fixedPoints_edgePerm.false ⟨d, hd⟩)
  | inr i =>
      rw [Equiv.Perm.sumCongr_apply]
      simp only [Sum.map_inr, ne_eq, Sum.inr.injEq]
      revert i
      decide

/-- **Leaf-edge insertion on `D ⊕ Fin 2`.** One new dart is threaded into the
old vertex cycle at `c`; the other becomes a new singleton vertex orbit. -/
def insertedLeafEdgeMap : CombinatorialMap (D ⊕ Fin 2) where
  vertexPerm := insertedLeafVertexPerm M c
  edgePerm := insertedLeafEdgePerm M
  facePerm := insertedLeafFacePerm M c
  face_mul_edge_mul_vertex_eq_one := by
    unfold insertedLeafFacePerm
    rw [mul_assoc, mul_assoc, ← mul_assoc (insertedLeafEdgePerm M)]
    have he : insertedLeafEdgePerm M * insertedLeafEdgePerm M = 1 := by
      ext z
      rw [Equiv.Perm.mul_apply, insertedLeafEdgePerm_involutive M z]
      rfl
    rw [he, one_mul, inv_mul_cancel]
  edgePerm_involutive := insertedLeafEdgePerm_involutive M
  isEmpty_fixedPoints_edgePerm := ⟨fun x => insertedLeafEdgePerm_fixedPointFree M x.1 x.2⟩

/-- **Boolean-indexed leaf-edge insertion on `D ⊕ Fin 2`.** The new dart
`leafThreadDart b` is threaded into the old vertex cycle at `c`; the other new
dart is a singleton vertex orbit. -/
def insertedLeafEdgeMapAt (b : Bool) : CombinatorialMap (D ⊕ Fin 2) where
  vertexPerm := insertedLeafVertexPermAt M c b
  edgePerm := insertedLeafEdgePerm M
  facePerm := insertedLeafFacePermAt M c b
  face_mul_edge_mul_vertex_eq_one := by
    unfold insertedLeafFacePermAt
    rw [mul_assoc, mul_assoc, ← mul_assoc (insertedLeafEdgePerm M)]
    have he : insertedLeafEdgePerm M * insertedLeafEdgePerm M = 1 := by
      ext z
      rw [Equiv.Perm.mul_apply, insertedLeafEdgePerm_involutive M z]
      rfl
    rw [he, one_mul, inv_mul_cancel]
  edgePerm_involutive := insertedLeafEdgePerm_involutive M
  isEmpty_fixedPoints_edgePerm := ⟨fun x => insertedLeafEdgePerm_fixedPointFree M x.1 x.2⟩

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMap_vertexPerm :
    (insertedLeafEdgeMap M c).vertexPerm = insertedLeafVertexPerm M c := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMapAt_vertexPerm (b : Bool) :
    (insertedLeafEdgeMapAt M c b).vertexPerm = insertedLeafVertexPermAt M c b := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMap_edgePerm :
    (insertedLeafEdgeMap M c).edgePerm = insertedLeafEdgePerm M := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMapAt_edgePerm (b : Bool) :
    (insertedLeafEdgeMapAt M c b).edgePerm = insertedLeafEdgePerm M := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMap_facePerm :
    (insertedLeafEdgeMap M c).facePerm = insertedLeafFacePerm M c := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMapAt_facePerm (b : Bool) :
    (insertedLeafEdgeMapAt M c b).facePerm = insertedLeafFacePermAt M c b := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafVertexPermAt_false :
    insertedLeafVertexPermAt M c false = insertedLeafVertexPerm M c := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafFacePermAt_false :
    insertedLeafFacePermAt M c false = insertedLeafFacePerm M c := rfl

omit [Fintype D] in
@[simp] lemma insertedLeafEdgeMapAt_false :
    insertedLeafEdgeMapAt M c false = insertedLeafEdgeMap M c := rfl

/-- A leaf-edge insertion adds one edge orbit. -/
theorem card_edge_insertedLeafEdgeMap :
    Fintype.card (insertedLeafEdgeMap M c).Edge = Fintype.card M.Edge + 1 := by
  rw [card_edge_eq_orbitCount, card_edge_eq_orbitCount, insertedLeafEdgeMap_edgePerm]
  unfold insertedLeafEdgePerm
  rw [orbitCount_sumCongr, orbitCount_swap_fin2]

omit [Fintype D] [DecidableEq D] in
private lemma leafDartA_ne_leafDartB : (leafDartA : D ⊕ Fin 2) ≠ leafDartB := by
  show (Sum.inr 0 : D ⊕ Fin 2) ≠ Sum.inr 1
  simp only [ne_eq, Sum.inr.injEq]
  decide

omit [Fintype D] [DecidableEq D] in
private lemma inl_ne_leafDartA (d : D) : (Sum.inl d : D ⊕ Fin 2) ≠ leafDartA := by
  simp [leafDartA]

omit [Fintype D] [DecidableEq D] in
private lemma leafVertexBase_fix_dartA (σ : Equiv.Perm D) :
    σ.sumCongr 1 (leafDartA : D ⊕ Fin 2) = leafDartA := by
  show σ.sumCongr 1 (Sum.inr 0) = Sum.inr 0
  rw [Equiv.Perm.sumCongr_apply]
  rfl

/-- A leaf-edge insertion adds one residual-map vertex orbit: one new singleton
vertex survives after threading `leafDartA` into the old vertex cycle. -/
theorem card_vertex_insertedLeafEdgeMap :
    Fintype.card (insertedLeafEdgeMap M c).Vertex = Fintype.card M.Vertex + 1 := by
  rw [card_vertex_eq_orbitCount, card_vertex_eq_orbitCount, insertedLeafEdgeMap_vertexPerm]
  have hbase : orbitCount (M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2)))
      = orbitCount M.vertexPerm + 2 := by
    rw [orbitCount_sumCongr, orbitCount_one_fin2]
  have hne : ¬ (M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2))).SameCycle
      (Sum.inl (M.vertexPerm c)) leafDartA := by
    exact sumCongr_not_sameCycle_inl_inr M.vertexPerm 1 (M.vertexPerm c) 0
  have hmerge := orbitCount_swap_mul_of_not_sameCycle (M.vertexPerm.sumCongr 1)
    (inl_ne_leafDartA _) hne
  unfold insertedLeafVertexPerm
  rw [hbase] at hmerge
  omega

omit [Fintype D] in
private lemma leafFacePerm_eq_product :
    insertedLeafFacePerm M c =
      Equiv.swap (Sum.inl c) leafDartA * leafBaseFacePerm M := by
  set Sg : Equiv.Perm (D ⊕ Fin 2) := M.vertexPerm⁻¹.sumCongr 1 with hSg
  set s : Equiv.Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl (M.vertexPerm c)) leafDartA with hs
  set t : Equiv.Perm (D ⊕ Fin 2) := Equiv.swap (Sum.inl c) leafDartA with ht
  have hinv : (insertedLeafVertexPerm M c)⁻¹ = Sg * s := by
    unfold insertedLeafVertexPerm
    rw [mul_inv_rev, hs, Equiv.swap_inv, hSg, Equiv.Perm.sumCongr_inv, inv_one]
  have hSginl : Sg (Sum.inl (M.vertexPerm c)) = Sum.inl c := by
    rw [hSg, Equiv.Perm.sumCongr_apply]
    simp
  have hSga : Sg (leafDartA : D ⊕ Fin 2) = leafDartA := by
    rw [hSg]
    show M.vertexPerm⁻¹.sumCongr 1 (Sum.inr 0) = Sum.inr 0
    rw [Equiv.Perm.sumCongr_apply]
    rfl
  have hconj : Sg * s = t * Sg := by
    have h := (Equiv.swap_apply_apply Sg (Sum.inl (M.vertexPerm c)) leafDartA).symm
    rw [hSginl, hSga] at h
    rw [hs, ht, ← h, mul_assoc, inv_mul_cancel, mul_one]
  have hSgedge : Sg * insertedLeafEdgePerm M = leafBaseFacePerm M := by
    rw [hSg]
    unfold insertedLeafEdgePerm leafBaseFacePerm
    rw [Equiv.Perm.sumCongr_mul, one_mul, M.facePerm_eq]
  unfold insertedLeafFacePerm
  rw [hinv]
  calc
    Sg * s * insertedLeafEdgePerm M
        = t * Sg * insertedLeafEdgePerm M := by rw [hconj]
    _ = t * (Sg * insertedLeafEdgePerm M) := by rw [mul_assoc]
    _ = t * leafBaseFacePerm M := by rw [hSgedge]

/-- A leaf-edge insertion preserves the face count: the new edge remains inside a
single old face, so no old face is split or merged. -/
theorem card_face_insertedLeafEdgeMap :
    Fintype.card (insertedLeafEdgeMap M c).Face = Fintype.card M.Face := by
  have hbase : orbitCount (leafBaseFacePerm M)
      = orbitCount M.facePerm + 1 := by
    unfold leafBaseFacePerm
    rw [orbitCount_sumCongr, orbitCount_swap_fin2]
  have hne : ¬ (leafBaseFacePerm M).SameCycle (Sum.inl c) leafDartA := by
    unfold leafBaseFacePerm
    exact sumCongr_not_sameCycle_inl_inr M.facePerm (Equiv.swap 0 1) c 0
  have hmerge := orbitCount_swap_mul_of_not_sameCycle (leafBaseFacePerm M)
    (inl_ne_leafDartA _) hne
  rw [card_face_eq_orbitCount, card_face_eq_orbitCount, insertedLeafEdgeMap_facePerm,
    leafFacePerm_eq_product]
  rw [hbase] at hmerge
  omega

/-- **Euler characteristic is unchanged under leaf-edge insertion.** -/
theorem eulerCharacteristic_insertedLeafEdgeMap :
    (insertedLeafEdgeMap M c).eulerCharacteristic = M.eulerCharacteristic := by
  unfold CombinatorialMap.eulerCharacteristic
  rw [card_edge_insertedLeafEdgeMap, card_vertex_insertedLeafEdgeMap,
    card_face_insertedLeafEdgeMap]
  push_cast
  ring

/-- **Planarity is preserved by leaf-edge insertion.** Adjoining a new leaf edge
keeps Euler characteristic `2`. -/
theorem isPlanar_insertedLeafEdgeMap (hplanar : M.IsPlanar) :
    (insertedLeafEdgeMap M c).IsPlanar := by
  unfold CombinatorialMap.IsPlanar
  rw [eulerCharacteristic_insertedLeafEdgeMap M c]
  exact hplanar

end LeafConstruction

/-! ### Conjugacy under dart relabeling

The insertion constructions are natural under reindexing of the old dart set.
This is the exact bookkeeping needed when an insertion step is identified only
up to a permutation of darts, as happens in the residual-map bridge after
changing edge order. -/

section Congr

private theorem sumCongr_permCongr_sumCongr
    {D D' β : Type*} (e : D ≃ D') (σ : Equiv.Perm D) (τ : Equiv.Perm β) :
    (e.sumCongr (Equiv.refl β)).permCongr (σ.sumCongr τ) =
      (e.permCongr σ).sumCongr τ := by
  ext z
  cases z <;> rfl

private theorem sumCongr_permCongr_swap_inl_inr
    {D D' β : Type*} [DecidableEq D] [DecidableEq D'] [DecidableEq β]
    (e : D ≃ D') (a : D) (b : β) :
    (e.sumCongr (Equiv.refl β)).permCongr (Equiv.swap (Sum.inl a) (Sum.inr b)) =
      Equiv.swap (Sum.inl (e a)) (Sum.inr b) := by
  ext z
  cases z with
  | inl x =>
      by_cases hx : x = e a
      · subst hx
        simp [Equiv.permCongr_apply, Equiv.swap_apply_left]
      · simp [Equiv.permCongr_apply]
        have hne1 : (Sum.inl (e.symm x) : D ⊕ β) ≠ Sum.inl a := by
          intro h
          apply hx
          apply Sum.inl.inj at h
          simpa using congrArg e h
        have hne2 : (Sum.inl (e.symm x) : D ⊕ β) ≠ Sum.inr b := Sum.inl_ne_inr
        have hne3 : (Sum.inl x : D' ⊕ β) ≠ Sum.inl (e a) := by
          intro h
          apply hx
          exact Sum.inl.inj h
        have hne4 : (Sum.inl x : D' ⊕ β) ≠ Sum.inr b := Sum.inl_ne_inr
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne hne3 hne4]
        simp
  | inr y =>
      by_cases hy : y = b
      · subst hy
        simp [Equiv.permCongr_apply, Equiv.swap_apply_right]
      · simp [Equiv.permCongr_apply]
        have hne1 : (Sum.inr y : D ⊕ β) ≠ Sum.inl a := Sum.inr_ne_inl
        have hne2 : (Sum.inr y : D ⊕ β) ≠ Sum.inr b := by
          intro h
          apply hy
          exact Sum.inr.inj h
        have hne3 : (Sum.inr y : D' ⊕ β) ≠ Sum.inl (e a) := Sum.inr_ne_inl
        have hne4 : (Sum.inr y : D' ⊕ β) ≠ Sum.inr b := by
          intro h
          apply hy
          exact Sum.inr.inj h
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne hne3 hne4]
        rfl

private theorem sumCongrRight_permCongr_sumCongr
    {D β β' : Type*} (e : β ≃ β') (σ : Equiv.Perm D) (τ : Equiv.Perm β) :
    ((Equiv.refl D).sumCongr e).permCongr (σ.sumCongr τ) =
      σ.sumCongr (e.permCongr τ) := by
  ext z
  cases z <;> rfl

private theorem sumCongrRight_permCongr_swap_inl_inr
    {D β β' : Type*} [DecidableEq D] [DecidableEq β] [DecidableEq β']
    (e : β ≃ β') (a : D) (b : β) :
    ((Equiv.refl D).sumCongr e).permCongr (Equiv.swap (Sum.inl a) (Sum.inr b)) =
      Equiv.swap (Sum.inl a) (Sum.inr (e b)) := by
  ext z
  cases z with
  | inl x =>
      by_cases hx : x = a
      · subst hx
        simp [Equiv.permCongr_apply, Equiv.swap_apply_left]
      · simp [Equiv.permCongr_apply]
        have hne1 : (Sum.inl x : D ⊕ β) ≠ Sum.inl a := by
          intro h
          exact hx (Sum.inl.inj h)
        have hne2 : (Sum.inl x : D ⊕ β) ≠ Sum.inr b := Sum.inl_ne_inr
        have hne3 : (Sum.inl x : D ⊕ β') ≠ Sum.inl a := by
          intro h
          exact hx (Sum.inl.inj h)
        have hne4 : (Sum.inl x : D ⊕ β') ≠ Sum.inr (e b) := Sum.inl_ne_inr
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2,
          Equiv.swap_apply_of_ne_of_ne hne3 hne4]
        rfl
  | inr y =>
      by_cases hy : y = e b
      · subst hy
        simp [Equiv.permCongr_apply, Equiv.swap_apply_right]
      · simp [Equiv.permCongr_apply]
        have hne1 : (Sum.inr (e.symm y) : D ⊕ β) ≠ Sum.inl a := Sum.inr_ne_inl
        have hne2 : (Sum.inr (e.symm y) : D ⊕ β) ≠ Sum.inr b := by
          intro h
          apply hy
          apply Sum.inr.inj at h
          simpa using congrArg e h
        have hne3 : (Sum.inr y : D ⊕ β') ≠ Sum.inl a := Sum.inr_ne_inl
        have hne4 : (Sum.inr y : D ⊕ β') ≠ Sum.inr (e b) := by
          intro h
          exact hy (Sum.inr.inj h)
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2,
          Equiv.swap_apply_of_ne_of_ne hne3 hne4]
        simp

variable {D D' : Type*} [Fintype D] [Fintype D'] [DecidableEq D] [DecidableEq D']
  {M : CombinatorialMap D} {M' : CombinatorialMap D'}

omit [Fintype D] [Fintype D'] [DecidableEq D] [DecidableEq D'] in
/-- Reindexing the old darts conjugates the enlarged edge involution of
facial-edge insertion. -/
theorem insEdgePerm_permCongr
    (e : D ≃ D') (hedge : e.permCongr M.edgePerm = M'.edgePerm) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insEdgePerm M) =
      insEdgePerm M' := by
  rw [insEdgePerm, insEdgePerm, sumCongr_permCongr_sumCongr, hedge]

omit [Fintype D] [Fintype D'] in
/-- Reindexing the old darts conjugates the enlarged vertex permutation of
facial-edge insertion. -/
theorem insVertexPerm_permCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (c₁ c₂ : D) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insVertexPerm M c₁ c₂) =
      insVertexPerm M' (e c₁) (e c₂) := by
  let f := Equiv.permCongrHom (e.sumCongr (Equiv.refl (Fin 2)))
  have hvc1 : e (M.vertexPerm c₁) = M'.vertexPerm (e c₁) := by
    simpa [Equiv.permCongr_apply] using congrArg (fun σ => σ (e c₁)) hvertex
  have hvc2 : e (M.vertexPerm c₂) = M'.vertexPerm (e c₂) := by
    simpa [Equiv.permCongr_apply] using congrArg (fun σ => σ (e c₂)) hvertex
  have hmul :
      (e.sumCongr (Equiv.refl (Fin 2))).permCongr
        (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2) *
          Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2) *
          M.vertexPerm.sumCongr 1)
        = ((e.sumCongr (Equiv.refl (Fin 2))).permCongr
            (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2))) *
          ((e.sumCongr (Equiv.refl (Fin 2))).permCongr
            (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2))) *
          ((e.sumCongr (Equiv.refl (Fin 2))).permCongr (M.vertexPerm.sumCongr 1)) := by
    have h1 := map_mul f
      (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2))
      (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2) * M.vertexPerm.sumCongr 1)
    have h2 := map_mul f
      (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2))
      (M.vertexPerm.sumCongr 1)
    calc
      f
          (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2) *
            (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2) *
              M.vertexPerm.sumCongr 1))
          = f (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2)) *
              f (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2) *
                M.vertexPerm.sumCongr 1) := h1
      _ = f (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2)) *
            (f (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2)) *
              f (M.vertexPerm.sumCongr 1)) := by rw [h2]
      _ = f (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2)) *
            f (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2)) *
            f (M.vertexPerm.sumCongr 1) := by simp [mul_assoc]
  calc
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insVertexPerm M c₁ c₂)
      = (e.sumCongr (Equiv.refl (Fin 2))).permCongr
          (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2) *
            Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2) *
            M.vertexPerm.sumCongr 1) := by rfl
    _ = ((e.sumCongr (Equiv.refl (Fin 2))).permCongr
            (Equiv.swap (Sum.inl (M.vertexPerm c₁)) (dartA : D ⊕ Fin 2))) *
          ((e.sumCongr (Equiv.refl (Fin 2))).permCongr
            (Equiv.swap (Sum.inl (M.vertexPerm c₂)) (dartB : D ⊕ Fin 2))) *
          ((e.sumCongr (Equiv.refl (Fin 2))).permCongr (M.vertexPerm.sumCongr 1)) := hmul
    _ = Equiv.swap (Sum.inl (e (M.vertexPerm c₁))) (dartA : D' ⊕ Fin 2) *
          Equiv.swap (Sum.inl (e (M.vertexPerm c₂))) (dartB : D' ⊕ Fin 2) *
          ((e.permCongr M.vertexPerm).sumCongr 1) := by
            rw [sumCongr_permCongr_swap_inl_inr, sumCongr_permCongr_swap_inl_inr,
              sumCongr_permCongr_sumCongr]
    _ = insVertexPerm M' (e c₁) (e c₂) := by
          simp [insVertexPerm, hvertex, hvc1, hvc2]

omit [Fintype D] [Fintype D'] in
/-- Reindexing the old darts conjugates the forced face permutation of
facial-edge insertion. -/
theorem insFacePerm_permCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) (c₁ c₂ : D) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insFacePerm M c₁ c₂) =
      insFacePerm M' (e c₁) (e c₂) := by
  let f := Equiv.permCongrHom (e.sumCongr (Equiv.refl (Fin 2)))
  have hv' : f (insVertexPerm M c₁ c₂) = insVertexPerm M' (e c₁) (e c₂) := by
    simpa [f] using insVertexPerm_permCongr (M := M) (M' := M') e hvertex c₁ c₂
  have he' : f (insEdgePerm M) = insEdgePerm M' := by
    simpa [f] using insEdgePerm_permCongr (M := M) (M' := M') e hedge
  calc
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insFacePerm M c₁ c₂)
      = f ((insVertexPerm M c₁ c₂)⁻¹ * insEdgePerm M) := by rfl
    _ = f (insVertexPerm M c₁ c₂)⁻¹ * f (insEdgePerm M) := by
      exact map_mul f _ _
    _ = (insVertexPerm M' (e c₁) (e c₂))⁻¹ * insEdgePerm M' := by
      rw [map_inv, hv', he']
    _ = insFacePerm M' (e c₁) (e c₂) := by rfl

omit [Fintype D] [Fintype D'] [DecidableEq D] [DecidableEq D'] in
/-- Reindexing the old darts conjugates the enlarged edge involution of leaf-edge
insertion. -/
theorem insertedLeafEdgePerm_permCongr
    (e : D ≃ D') (hedge : e.permCongr M.edgePerm = M'.edgePerm) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insertedLeafEdgePerm M) =
      insertedLeafEdgePerm M' := by
  rw [insertedLeafEdgePerm, insertedLeafEdgePerm, sumCongr_permCongr_sumCongr, hedge]

omit [Fintype D] [Fintype D'] in
/-- Reindexing the old darts conjugates the enlarged vertex permutation of
leaf-edge insertion. -/
theorem insertedLeafVertexPerm_permCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (c : D) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insertedLeafVertexPerm M c) =
      insertedLeafVertexPerm M' (e c) := by
  have hvc : e (M.vertexPerm c) = M'.vertexPerm (e c) := by
    simpa [Equiv.permCongr_apply] using congrArg (fun σ => σ (e c)) hvertex
  calc
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insertedLeafVertexPerm M c)
      = (e.sumCongr (Equiv.refl (Fin 2))).permCongr
          (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2) *
            M.vertexPerm.sumCongr 1) := by rfl
    _ = ((e.sumCongr (Equiv.refl (Fin 2))).permCongr
            (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2))) *
          ((e.sumCongr (Equiv.refl (Fin 2))).permCongr (M.vertexPerm.sumCongr 1)) := by
            exact map_mul (Equiv.permCongrHom (e.sumCongr (Equiv.refl (Fin 2))))
              (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2))
              (M.vertexPerm.sumCongr 1)
    _ = Equiv.swap (Sum.inl (e (M.vertexPerm c))) (leafDartA : D' ⊕ Fin 2) *
          ((e.permCongr M.vertexPerm).sumCongr 1) := by
            rw [sumCongr_permCongr_swap_inl_inr, sumCongr_permCongr_sumCongr]
    _ = insertedLeafVertexPerm M' (e c) := by
          simp [insertedLeafVertexPerm, hvertex, hvc]

omit [Fintype D] in
/-- Swapping the two new darts turns the standard leaf insertion into the
Boolean-indexed insertion in which `leafDartB` is threaded into the old vertex
cycle. -/
theorem leafDartSwap_permCongr_insertedLeafVertexPerm
    (M : CombinatorialMap D) (c : D) :
    ((Equiv.refl D).sumCongr (Equiv.swap (0 : Fin 2) 1)).permCongr
        (insertedLeafVertexPerm M c) =
      insertedLeafVertexPermAt M c true := by
  let e : D ⊕ Fin 2 ≃ D ⊕ Fin 2 :=
    (Equiv.refl D).sumCongr (Equiv.swap (0 : Fin 2) 1)
  let f := Equiv.permCongrHom e
  calc
    e.permCongr (insertedLeafVertexPerm M c)
        = f (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2) *
            M.vertexPerm.sumCongr 1) := by rfl
    _ = f (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2)) *
          f (M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2))) := by
            exact map_mul f _ _
    _ = Equiv.swap (Sum.inl (M.vertexPerm c)) (Sum.inr (1 : Fin 2)) *
          M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2)) := by
            rw [show f (Equiv.swap (Sum.inl (M.vertexPerm c)) (leafDartA : D ⊕ Fin 2)) =
                Equiv.swap (Sum.inl (M.vertexPerm c)) (Sum.inr (1 : Fin 2)) by
                  simpa [f, e, leafDartA] using
                    sumCongrRight_permCongr_swap_inl_inr
                      (D := D) (β := Fin 2) (β' := Fin 2)
                      (Equiv.swap (0 : Fin 2) 1) (M.vertexPerm c) (0 : Fin 2),
              show f (M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2))) =
                M.vertexPerm.sumCongr (1 : Equiv.Perm (Fin 2)) by
                  simpa [f, e] using
                    sumCongrRight_permCongr_sumCongr
                      (D := D) (β := Fin 2) (β' := Fin 2)
                      (Equiv.swap (0 : Fin 2) 1) M.vertexPerm
                      (1 : Equiv.Perm (Fin 2))]
    _ = insertedLeafVertexPermAt M c true := by
          simp [insertedLeafVertexPermAt, leafThreadDart]

omit [Fintype D] in
/-- Swapping the two new darts preserves the enlarged leaf-edge involution. -/
theorem leafDartSwap_permCongr_insertedLeafEdgePerm
    (M : CombinatorialMap D) :
    ((Equiv.refl D).sumCongr (Equiv.swap (0 : Fin 2) 1)).permCongr
        (insertedLeafEdgePerm M) =
      insertedLeafEdgePerm M := by
  let e : D ⊕ Fin 2 ≃ D ⊕ Fin 2 :=
    (Equiv.refl D).sumCongr (Equiv.swap (0 : Fin 2) 1)
  let f := Equiv.permCongrHom e
  calc
    e.permCongr (insertedLeafEdgePerm M)
        = f (M.edgePerm.sumCongr (Equiv.swap (0 : Fin 2) 1)) := by rfl
    _ = M.edgePerm.sumCongr
          ((Equiv.swap (0 : Fin 2) 1).permCongr (Equiv.swap (0 : Fin 2) 1)) := by
            simpa [f, e, insertedLeafEdgePerm] using
              sumCongrRight_permCongr_sumCongr
                (D := D) (β := Fin 2) (β' := Fin 2)
                (Equiv.swap (0 : Fin 2) 1) M.edgePerm (Equiv.swap (0 : Fin 2) 1)
    _ = insertedLeafEdgePerm M := by
          ext z
          cases z with
          | inl d => rfl
          | inr j => fin_cases j <;> rfl

omit [Fintype D] [Fintype D'] in
/-- Reindexing the old darts conjugates the forced face permutation of leaf-edge
insertion. -/
theorem insertedLeafFacePerm_permCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) (c : D) :
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insertedLeafFacePerm M c) =
      insertedLeafFacePerm M' (e c) := by
  let f := Equiv.permCongrHom (e.sumCongr (Equiv.refl (Fin 2)))
  have hv' : f (insertedLeafVertexPerm M c) = insertedLeafVertexPerm M' (e c) := by
    simpa [f] using insertedLeafVertexPerm_permCongr (M := M) (M' := M') e hvertex c
  have he' : f (insertedLeafEdgePerm M) = insertedLeafEdgePerm M' := by
    simpa [f] using insertedLeafEdgePerm_permCongr (M := M) (M' := M') e hedge
  calc
    (e.sumCongr (Equiv.refl (Fin 2))).permCongr (insertedLeafFacePerm M c)
      = f ((insertedLeafVertexPerm M c)⁻¹ * insertedLeafEdgePerm M) := by rfl
    _ = f (insertedLeafVertexPerm M c)⁻¹ * f (insertedLeafEdgePerm M) := by
      exact map_mul f _ _
    _ = (insertedLeafVertexPerm M' (e c))⁻¹ * insertedLeafEdgePerm M' := by
      rw [map_inv, hv', he']
    _ = insertedLeafFacePerm M' (e c) := by rfl

/-- Reindexing the old darts extends to an isomorphism between the two
facial-edge insertion maps. -/
def insertedEdgeMapIsoOfPermCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) (c₁ c₂ : D) :
    CombinatorialMap.Iso (insertedEdgeMap M c₁ c₂) (insertedEdgeMap M' (e c₁) (e c₂)) where
  toEquiv := e.sumCongr (Equiv.refl (Fin 2))
  vertex_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insVertexPerm_permCongr (M := M) (M' := M') e hvertex c₁ c₂)
    simpa [insertedEdgeMap_vertexPerm, Equiv.permCongr_apply]
      using h
  edge_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insEdgePerm_permCongr (M := M) (M' := M') e hedge)
    simpa [insertedEdgeMap_edgePerm, Equiv.permCongr_apply]
      using h
  face_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insFacePerm_permCongr (M := M) (M' := M') e hvertex hedge c₁ c₂)
    simpa [insertedEdgeMap_facePerm, Equiv.permCongr_apply]
      using h

/-- Reindexing the old darts extends to an isomorphism between the two
leaf-edge insertion maps. -/
def insertedLeafEdgeMapIsoOfPermCongr
    (e : D ≃ D') (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) (c : D) :
    CombinatorialMap.Iso (insertedLeafEdgeMap M c) (insertedLeafEdgeMap M' (e c)) where
  toEquiv := e.sumCongr (Equiv.refl (Fin 2))
  vertex_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insertedLeafVertexPerm_permCongr (M := M) (M' := M') e hvertex c)
    simpa [insertedLeafEdgeMap_vertexPerm, Equiv.permCongr_apply]
      using h
  edge_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insertedLeafEdgePerm_permCongr (M := M) (M' := M') e hedge)
    simpa [insertedLeafEdgeMap_edgePerm, Equiv.permCongr_apply]
      using h
  face_comm := by
    funext x
    have h := congrArg (fun σ => σ ((e.sumCongr (Equiv.refl (Fin 2))) x))
      (insertedLeafFacePerm_permCongr (M := M) (M' := M') e hvertex hedge c)
    simpa [insertedLeafEdgeMap_facePerm, Equiv.permCongr_apply]
      using h

end Congr

end CombinatorialMap.EdgeInsertion
