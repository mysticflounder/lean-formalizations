/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

Euler characteristic bound for a connected combinatorial map.

Goal: a *connected* combinatorial map has Euler characteristic ≤ 2.

Mathematically this is the genus inequality `χ = 2 − 2g ≤ 2` (`g ≥ 0`). We prove it
via the **F₂ (co)homology rank route** (route (ii) of the card), on top of the
vendored `CombinatorialMap` carrier (mathlib PR #16074) and the reusable
connectivity / orbit-counting helpers in `PlanarEdgeBound.lean`.

## Route (chosen): F₂ cobordism / coboundary rank

Work over `R := ZMod 2`. Put
  `C⁰ := M.Vertex → R`,  `C¹ := M.Edge → R`,  `C² := M.Face → R`.
These are finite-dimensional `R`-vector spaces with `finrank = card`.

Two coboundary maps:
  `δ₀ : C⁰ →ₗ C¹`,  `(δ₀ g) e = g u + g w`   (`{u,w}` the endpoints of `e`)
  `δ₁ : C¹ →ₗ C²`,  `(δ₁ h) f = ∑_{d ∈ f} h (edge of d)`  (sum over the face orbit)
and a third map `η : C² →ₗ C¹`, the transpose of `δ₁`:
  `(η ξ) e = ξ (face of d) + ξ (face of αd)`  for `e = {d, αd}`.

Key facts:
  (A) `δ₁ ∘ δ₀ = 0`              — the cochain-complex condition (telescoping over F₂).
  (R1) connected ⟹ `finrank (ker δ₀) ≤ 1`   — vertex connectivity.
  (R2) connected ⟹ `finrank (ker η) ≤ 1`    — face connectivity (same argument, dual).
  (T)  `rank η = rank δ₁`        — `η = δ₁ᵀ` w.r.t. the standard pairings.

Assembly (pure linear algebra):
  `rank δ₀ = V − finrank(ker δ₀) ≥ V − 1`,
  `rank δ₀ + rank δ₁ ≤ E`        (from (A): `im δ₀ ⊆ ker δ₁`, rank-nullity),
  `rank δ₁ = rank η = F − finrank(ker η) ≥ F − 1`,
  hence `(V−1) + (F−1) ≤ E`, i.e. `V − E + F ≤ 2`. ∎
-/
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Basis

open scoped BigOperators

namespace CombinatorialMap

variable {D : Type*} {M : CombinatorialMap D}

/-- Coefficient field for the chain complex. -/
local notation "R" => ZMod 2

/-! ### Standing facts about the carrier used throughout -/

/-- A `vertexPerm` step does not change the vertex class. -/
lemma vertexMk_vertexPerm (d : D) : M.Vertex_mk (M.vertexPerm d) = M.Vertex_mk d :=
  (Quotient.eq'').2 (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)).symm

/-- A `vertexPerm⁻¹` step does not change the vertex class. -/
lemma vertexMk_vertexPerm_inv (d : D) : M.Vertex_mk (M.vertexPerm⁻¹ d) = M.Vertex_mk d := by
  have h := vertexMk_vertexPerm (M := M) (M.vertexPerm⁻¹ d)
  simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
  exact h.symm

/-- A `facePerm` step does not change the face class. -/
lemma faceMk_facePerm (d : D) : M.Face_mk (M.facePerm d) = M.Face_mk d :=
  (Quotient.eq'').2 (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)).symm

/-- A `facePerm⁻¹` step does not change the face class. -/
lemma faceMk_facePerm_inv (d : D) : M.Face_mk (M.facePerm⁻¹ d) = M.Face_mk d := by
  have := faceMk_facePerm (M := M) (M.facePerm⁻¹ d)
  simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
  exact this.symm

/-- `σ d = α (φ⁻¹ d)`:  from `σ φ α = 1` we get `σ = α φ⁻¹` (`α` an involution). -/
lemma vertexPerm_eq_edgePerm_facePerm_inv (d : D) :
    M.vertexPerm d = M.edgePerm (M.facePerm⁻¹ d) := by
  have h : M.vertexPerm * M.facePerm * M.edgePerm = 1 := vertex_mul_face_mul_edge_eq_one
  -- σ = (φ α)⁻¹ = α⁻¹ φ⁻¹ = α φ⁻¹
  have hσ : M.vertexPerm = M.edgePerm * M.facePerm⁻¹ := by
    have h2 : M.vertexPerm * M.facePerm = M.edgePerm⁻¹ := by
      have := congr($h * M.edgePerm⁻¹)
      rwa [mul_assoc, mul_inv_cancel, mul_one, one_mul] at this
    have h3 : M.vertexPerm = M.edgePerm⁻¹ * M.facePerm⁻¹ := by
      have := congr($h2 * M.facePerm⁻¹)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
    rwa [show M.edgePerm⁻¹ = M.edgePerm from
      M.edgePerm_involutive.symm_eq_self_of_involutive] at h3
  rw [hσ, Equiv.Perm.mul_apply]

/-- `σ⁻¹ d = φ (α d)`:  inverse of `σ = α φ⁻¹`. -/
lemma vertexPerm_inv_eq_facePerm_edgePerm (d : D) :
    M.vertexPerm⁻¹ d = M.facePerm (M.edgePerm d) := by
  have hσ : M.vertexPerm = M.edgePerm * M.facePerm⁻¹ := by
    have h : M.vertexPerm * M.facePerm * M.edgePerm = 1 := vertex_mul_face_mul_edge_eq_one
    have h2 : M.vertexPerm * M.facePerm = M.edgePerm⁻¹ := by
      have := congr($h * M.edgePerm⁻¹)
      rwa [mul_assoc, mul_inv_cancel, mul_one, one_mul] at this
    have h3 : M.vertexPerm = M.edgePerm⁻¹ * M.facePerm⁻¹ := by
      have := congr($h2 * M.facePerm⁻¹)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
    rwa [show M.edgePerm⁻¹ = M.edgePerm from
      M.edgePerm_involutive.symm_eq_self_of_involutive] at h3
  have : M.vertexPerm⁻¹ = M.facePerm * M.edgePerm⁻¹ := by
    rw [hσ, mul_inv_rev, inv_inv]
  rw [this, Equiv.Perm.mul_apply,
    show M.edgePerm⁻¹ = M.edgePerm from M.edgePerm_involutive.symm_eq_self_of_involutive]

/-- `α d` and `φ d` lie in the same vertex orbit (`α = σ ∘ φ`). -/
lemma vertexMk_edgePerm_eq_vertexMk_facePerm (d : D) :
    M.Vertex_mk (M.edgePerm d) = M.Vertex_mk (M.facePerm d) := by
  -- α d = σ (φ d):  from `σ (φ x) = α x` (`vertex_face_eq_edge`).
  have h : M.edgePerm d = M.vertexPerm (M.facePerm d) := (vertex_face_eq_edge (M := M) d).symm
  rw [h, vertexMk_vertexPerm]

/-! ### The coboundary `δ₀ : (Vertex → R) → (Edge → R)` -/

/-- Value of `δ₀ g` on an edge, lifted from a dart representative `d`:
`g(class d) + g(class (αd))`. Well-defined because the two darts of an edge are
exactly `d` and `αd` (Lemma A), and the sum is symmetric over `R`. -/
noncomputable def cobound0Fun (g : M.Vertex → R) : M.Edge → R :=
  Quotient.lift
    (fun d : D => g (M.Vertex_mk d) + g (M.Vertex_mk (M.edgePerm d)))
    (by
      intro d d' (h : (Equiv.Perm.SameCycle.setoid M.edgePerm).r d d')
      have h' : M.edgePerm.SameCycle d d' := h
      rcases (M.sameCycle_edgePerm_iff d d').1 h' with rfl | rfl
      · rfl
      · -- d' = α d : swap the two summands
        simp only [M.edgePerm_involutive d]
        rw [add_comm])

@[simp] lemma cobound0Fun_mk (g : M.Vertex → R) (d : D) :
    cobound0Fun g (M.Edge_mk d) = g (M.Vertex_mk d) + g (M.Vertex_mk (M.edgePerm d)) := rfl

/-- The coboundary `δ₀` as an `R`-linear map. -/
noncomputable def cobound0 : (M.Vertex → R) →ₗ[R] (M.Edge → R) where
  toFun := cobound0Fun
  map_add' g₁ g₂ := by
    funext e
    induction e using Quotient.ind with
    | _ d =>
        simp only [cobound0Fun_mk, Pi.add_apply]
        ring
  map_smul' c g := by
    funext e
    induction e using Quotient.ind with
    | _ d =>
        simp only [cobound0Fun_mk, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring

@[simp] lemma cobound0_apply_mk (g : M.Vertex → R) (d : D) :
    (cobound0 (M := M)) g (M.Edge_mk d)
      = g (M.Vertex_mk d) + g (M.Vertex_mk (M.edgePerm d)) := rfl

/-! ### The map `η : (Face → R) → (Edge → R)` (transpose of `δ₁`) -/

/-- Value of `η ξ` on an edge `e = {d, αd}`: `ξ(face d) + ξ(face (αd))`.
Well-defined and symmetric, exactly as for `δ₀`. -/
noncomputable def faceEdge (ξ : M.Face → R) : M.Edge → R :=
  Quotient.lift
    (fun d : D => ξ (M.Face_mk d) + ξ (M.Face_mk (M.edgePerm d)))
    (by
      intro d d' (h : (Equiv.Perm.SameCycle.setoid M.edgePerm).r d d')
      have h' : M.edgePerm.SameCycle d d' := h
      rcases (M.sameCycle_edgePerm_iff d d').1 h' with rfl | rfl
      · rfl
      · simp only [M.edgePerm_involutive d]
        rw [add_comm])

@[simp] lemma faceEdge_mk (ξ : M.Face → R) (d : D) :
    faceEdge ξ (M.Edge_mk d) = ξ (M.Face_mk d) + ξ (M.Face_mk (M.edgePerm d)) := rfl

/-- `η` as an `R`-linear map. -/
noncomputable def faceCobound : (M.Face → R) →ₗ[R] (M.Edge → R) where
  toFun := faceEdge
  map_add' ξ₁ ξ₂ := by
    funext e
    induction e using Quotient.ind with
    | _ d => simp only [faceEdge_mk, Pi.add_apply]; ring
  map_smul' c ξ := by
    funext e
    induction e using Quotient.ind with
    | _ d => simp only [faceEdge_mk, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

@[simp] lemma faceCobound_apply_mk (ξ : M.Face → R) (d : D) :
    (faceCobound (M := M)) ξ (M.Edge_mk d)
      = ξ (M.Face_mk d) + ξ (M.Face_mk (M.edgePerm d)) := rfl

/-! ### R1: connectivity bounds `finrank (ker δ₀) ≤ 1`

A `g` in `ker δ₀` is equal across each edge (its only non-automatic constraint),
hence — by connectivity — constant on all vertex classes. So `ker δ₀` is spanned
by the all-ones function and has dimension ≤ 1. -/

/-- In `ZMod 2`, `a + b = 0 ↔ a = b`. -/
private lemma zmod2_add_eq_zero_iff {a b : R} : a + b = 0 ↔ a = b := by
  revert a b; decide

/-- A kernel element of `δ₀` is constant across edges. -/
lemma cobound0_mem_ker_edge_eq {g : M.Vertex → R} (hg : g ∈ LinearMap.ker (cobound0 (M := M)))
    (d : D) : g (M.Vertex_mk (M.edgePerm d)) = g (M.Vertex_mk d) := by
  have h0 : (cobound0 (M := M)) g = 0 := hg
  have := congrFun h0 (M.Edge_mk d)
  simp only [cobound0_apply_mk, Pi.zero_apply] at this
  -- this : g (Vertex_mk d) + g (Vertex_mk (αd)) = 0
  rw [add_comm] at this
  exact (zmod2_add_eq_zero_iff).1 this

/-- A kernel element of `δ₀` is globally constant (uses connectivity). -/
lemma cobound0_mem_ker_const (hc : M.Connected) {g : M.Vertex → R}
    (hg : g ∈ LinearMap.ker (cobound0 (M := M))) (d₀ d : D) :
    g (M.Vertex_mk d) = g (M.Vertex_mk d₀) := by
  set S : Set D := {a | g (M.Vertex_mk a) = g (M.Vertex_mk d₀)} with hS
  have hd₀ : d₀ ∈ S := by simp [hS]
  have hσ : ∀ a ∈ S, M.vertexPerm a ∈ S := by
    intro a ha; simp only [hS, Set.mem_setOf_eq, vertexMk_vertexPerm] at ha ⊢; exact ha
  have hσ' : ∀ a ∈ S, M.vertexPerm⁻¹ a ∈ S := by
    intro a ha; simp only [hS, Set.mem_setOf_eq, vertexMk_vertexPerm_inv] at ha ⊢; exact ha
  have hα : ∀ a ∈ S, M.edgePerm a ∈ S := by
    intro a ha
    simp only [hS, Set.mem_setOf_eq] at ha ⊢
    rw [cobound0_mem_ker_edge_eq hg a]; exact ha
  exact reachable_mem_of_invariant d₀ hd₀ hσ hσ' hα d (hc d₀ d)

/-- **R1.** For a connected map, `finrank (ker δ₀) ≤ 1`. -/
lemma finrank_ker_cobound0_le_one (hc : M.Connected) :
    Module.finrank R (LinearMap.ker (cobound0 (M := M))) ≤ 1 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · -- no darts: `Vertex → R` is subsingleton, finrank 0
    have hVempty : IsEmpty M.Vertex := by
      constructor; rintro v; obtain ⟨d, rfl⟩ := Quotient.exists_rep v; exact hD.elim d
    have : Subsingleton (M.Vertex → R) := ⟨fun a b => funext fun v => hVempty.elim v⟩
    have hsub : Subsingleton (LinearMap.ker (cobound0 (M := M))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton]; omega
  · obtain ⟨d₀⟩ := hD
    -- witness: all-ones is in the kernel; every kernel element is a scalar multiple of it.
    have hone : (fun _ : M.Vertex => (1 : R)) ∈ LinearMap.ker (cobound0 (M := M)) := by
      rw [LinearMap.mem_ker]; funext e
      obtain ⟨d, rfl⟩ := Quotient.exists_rep e
      show (cobound0 (M := M)) (fun _ => (1 : R)) (M.Edge_mk d) = (0 : M.Edge → R) (M.Edge_mk d)
      simp only [cobound0_apply_mk, Pi.zero_apply]; decide
    refine finrank_le_one
      (M := LinearMap.ker (cobound0 (M := M))) ⟨fun _ => (1 : R), hone⟩ ?_
    rintro ⟨g, hg⟩
    refine ⟨g (M.Vertex_mk d₀), ?_⟩
    apply Subtype.ext
    funext v
    obtain ⟨d, rfl⟩ := Quotient.exists_rep v
    show g (M.Vertex_mk d₀) • (1 : R) = g (M.Vertex_mk d)
    rw [smul_eq_mul, mul_one]
    exact (cobound0_mem_ker_const hc hg d₀ d).symm

/-! ### R2: connectivity bounds `finrank (ker η) ≤ 1`

A `ξ` in `ker η` is constant across each edge's two faces. Via `σ = α φ⁻¹` a
`vertexPerm` step lands in an edge-adjacent face, so by connectivity `ξ` is
constant on all face classes. Same shape as R1. -/

/-- A kernel element of `η` is constant across the two faces of each edge. -/
lemma faceCobound_mem_ker_face_eq {ξ : M.Face → R}
    (hξ : ξ ∈ LinearMap.ker (faceCobound (M := M))) (d : D) :
    ξ (M.Face_mk (M.edgePerm d)) = ξ (M.Face_mk d) := by
  have h0 : (faceCobound (M := M)) ξ = 0 := hξ
  have := congrFun h0 (M.Edge_mk d)
  simp only [faceCobound_apply_mk, Pi.zero_apply] at this
  rw [add_comm] at this
  exact (zmod2_add_eq_zero_iff).1 this

/-- A kernel element of `η` is globally constant (uses connectivity). -/
lemma faceCobound_mem_ker_const (hc : M.Connected) {ξ : M.Face → R}
    (hξ : ξ ∈ LinearMap.ker (faceCobound (M := M))) (d₀ d : D) :
    ξ (M.Face_mk d) = ξ (M.Face_mk d₀) := by
  set S : Set D := {a | ξ (M.Face_mk a) = ξ (M.Face_mk d₀)} with hS
  have hd₀ : d₀ ∈ S := by simp [hS]
  -- σ a = α (φ⁻¹ a): face of σa equals face of α(φ⁻¹a), which by the ker constraint
  -- on dart `φ⁻¹ a` equals face of φ⁻¹ a = face of a.
  have hσ : ∀ a ∈ S, M.vertexPerm a ∈ S := by
    intro a ha
    simp only [hS, Set.mem_setOf_eq] at ha ⊢
    rw [vertexPerm_eq_edgePerm_facePerm_inv,
      faceCobound_mem_ker_face_eq hξ (M.facePerm⁻¹ a), faceMk_facePerm_inv]
    exact ha
  -- σ⁻¹ a = φ (α a): face of σ⁻¹a equals face of φ(αa) = face of αa, = face of a by constraint.
  have hσ' : ∀ a ∈ S, M.vertexPerm⁻¹ a ∈ S := by
    intro a ha
    simp only [hS, Set.mem_setOf_eq] at ha ⊢
    rw [vertexPerm_inv_eq_facePerm_edgePerm, faceMk_facePerm,
      faceCobound_mem_ker_face_eq hξ a]
    exact ha
  have hα : ∀ a ∈ S, M.edgePerm a ∈ S := by
    intro a ha
    simp only [hS, Set.mem_setOf_eq] at ha ⊢
    rw [faceCobound_mem_ker_face_eq hξ a]; exact ha
  exact reachable_mem_of_invariant d₀ hd₀ hσ hσ' hα d (hc d₀ d)

/-- **R2.** For a connected map, `finrank (ker η) ≤ 1`. -/
lemma finrank_ker_faceCobound_le_one (hc : M.Connected) :
    Module.finrank R (LinearMap.ker (faceCobound (M := M))) ≤ 1 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have hFempty : IsEmpty M.Face := by
      constructor; rintro f; obtain ⟨d, rfl⟩ := Quotient.exists_rep f; exact hD.elim d
    have : Subsingleton (M.Face → R) := ⟨fun a b => funext fun f => hFempty.elim f⟩
    have hsub : Subsingleton (LinearMap.ker (faceCobound (M := M))) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton]; omega
  · obtain ⟨d₀⟩ := hD
    have hone : (fun _ : M.Face => (1 : R)) ∈ LinearMap.ker (faceCobound (M := M)) := by
      rw [LinearMap.mem_ker]; funext e
      obtain ⟨d, rfl⟩ := Quotient.exists_rep e
      show (faceCobound (M := M)) (fun _ => (1 : R)) (M.Edge_mk d)
        = (0 : M.Edge → R) (M.Edge_mk d)
      simp only [faceCobound_apply_mk, Pi.zero_apply]; decide
    refine finrank_le_one
      (M := LinearMap.ker (faceCobound (M := M))) ⟨fun _ => (1 : R), hone⟩ ?_
    rintro ⟨ξ, hξ⟩
    refine ⟨ξ (M.Face_mk d₀), ?_⟩
    apply Subtype.ext
    funext f
    obtain ⟨d, rfl⟩ := Quotient.exists_rep f
    show ξ (M.Face_mk d₀) • (1 : R) = ξ (M.Face_mk d)
    rw [smul_eq_mul, mul_one]
    exact (faceCobound_mem_ker_const hc hξ d₀ d).symm

/-! ### The coboundary `δ₁ : (Edge → R) → (Face → R)` and the complex condition -/

/-- The dart orbit of a face `f`, as a `Finset D`. -/
noncomputable def faceFiber [Fintype D] (f : M.Face) : Finset D :=
  letI : DecidableEq M.Face := Classical.decEq _
  Finset.univ.filter (fun d => M.Face_mk d = f)

lemma mem_faceFiber [Fintype D] {f : M.Face} {d : D} :
    d ∈ faceFiber f ↔ M.Face_mk d = f := by
  classical
  rw [faceFiber]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- `δ₁ h` evaluated on a face is the sum of `h` over the edges of that face's
dart orbit. -/
noncomputable def cobound1Fun [Fintype D] (h : M.Edge → R) : M.Face → R :=
  fun f => ∑ d ∈ faceFiber f, h (M.Edge_mk d)

/-- `δ₁` as an `R`-linear map. -/
noncomputable def cobound1 [Fintype D] : (M.Edge → R) →ₗ[R] (M.Face → R) where
  toFun := cobound1Fun
  map_add' h₁ h₂ := by
    funext f
    simp only [cobound1Fun, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c h := by
    funext f
    simp only [cobound1Fun, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

/-- The cochain-complex condition `δ₁ ∘ δ₀ = 0`.

Pointwise on a face `f`: the summand for dart `d` is `g(class d) + g(class αd)`,
and `class αd = class (φd)` (since `α = σ∘φ`). So the summand telescopes to
`g(class d) + g(class (φd))`; summing over the `φ`-orbit `f` and reindexing the
second half by `φ` gives `2·∑ = 0` over `R = ZMod 2`. -/
lemma cobound1_comp_cobound0 [Fintype D] :
    (cobound1 (M := M)).comp (cobound0 (M := M)) = 0 := by
  ext g f
  show cobound1Fun ((cobound0 (M := M)) g) f = (0 : M.Face → R) f
  simp only [cobound1Fun, Pi.zero_apply]
  -- rewrite each summand `(δ₀ g)(Edge_mk d) = g(Vertex_mk d) + g(Vertex_mk (φ d))`
  have hsummand : ∀ d ∈ faceFiber f, (cobound0 (M := M)) g (M.Edge_mk d)
      = g (M.Vertex_mk d) + g (M.Vertex_mk (M.facePerm d)) := by
    intro d _
    rw [cobound0_apply_mk, vertexMk_edgePerm_eq_vertexMk_facePerm]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_add_distrib]
  -- reindex the second sum by `φ`
  have hreindex : ∑ d ∈ faceFiber f, g (M.Vertex_mk (M.facePerm d))
      = ∑ d ∈ faceFiber f, g (M.Vertex_mk d) := by
    apply Finset.sum_nbij' (fun d => M.facePerm d) (fun d => M.facePerm⁻¹ d)
    · intro d hd
      rw [mem_faceFiber] at hd ⊢; rw [faceMk_facePerm]; exact hd
    · intro d hd
      rw [mem_faceFiber] at hd ⊢; rw [faceMk_facePerm_inv]; exact hd
    · intro d _; simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    · intro d _; simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    · intro d _; rfl
  rw [hreindex]
  -- now ∑ + ∑ = 0 over ZMod 2 (characteristic two)
  exact CharTwo.add_self_eq_zero _

/-! ### Pure linear-algebra assembly

Given a two-step cochain complex `C⁰ →[δ₀] C¹ →[δ₁] C²` and a map `η : C² → C¹`
that is the transpose of `δ₁` (so `rank δ₁ = rank η`), with both `ker δ₀` and
`ker η` of dimension `≤ 1`, the alternating dimension count is `≤ 2`. -/

private lemma euler_assembly
    {C0 C1 C2 : Type*}
    [AddCommGroup C0] [Module R C0] [FiniteDimensional R C0]
    [AddCommGroup C1] [Module R C1] [FiniteDimensional R C1]
    [AddCommGroup C2] [Module R C2] [FiniteDimensional R C2]
    (δ₀ : C0 →ₗ[R] C1) (δ₁ : C1 →ₗ[R] C2) (η : C2 →ₗ[R] C1)
    (hker0 : Module.finrank R (LinearMap.ker δ₀) ≤ 1)
    (hkerη : Module.finrank R (LinearMap.ker η) ≤ 1)
    (hcomp : LinearMap.range δ₀ ≤ LinearMap.ker δ₁)
    (htrans : Module.finrank R (LinearMap.range δ₁) = Module.finrank R (LinearMap.range η)) :
    (Module.finrank R C0 : ℤ) - Module.finrank R C1 + Module.finrank R C2 ≤ 2 := by
  -- abbreviations
  set V := Module.finrank R C0
  set E := Module.finrank R C1
  set F := Module.finrank R C2
  set r0 := Module.finrank R (LinearMap.range δ₀) with hr0
  set r1 := Module.finrank R (LinearMap.range δ₁) with hr1
  set rη := Module.finrank R (LinearMap.range η) with hrη
  -- rank-nullity for the three maps
  have rn0 : r0 + Module.finrank R (LinearMap.ker δ₀) = V := δ₀.finrank_range_add_finrank_ker
  have rn1 : r1 + Module.finrank R (LinearMap.ker δ₁) = E := δ₁.finrank_range_add_finrank_ker
  have rnη : rη + Module.finrank R (LinearMap.ker η) = F := η.finrank_range_add_finrank_ker
  -- range δ₀ ≤ ker δ₁  ⟹  r0 ≤ dim ker δ₁
  have hle : r0 ≤ Module.finrank R (LinearMap.ker δ₁) := Submodule.finrank_mono hcomp
  -- assemble over ℕ then cast
  have key : V + F ≤ E + 2 := by
    have h1 : V ≤ r0 + 1 := by omega
    have h2 : F ≤ rη + 1 := by omega
    have h3 : r0 + r1 ≤ E := by omega
    have h4 : r1 = rη := htrans
    omega
  have : (V : ℤ) + F ≤ E + 2 := by exact_mod_cast key
  omega

/-! ### (T) Transpose: `rank δ₁ = rank η`

`η` is the transpose of `δ₁` with respect to the standard (dot-product) pairings
on the coordinate spaces `C¹ = Edge → R` and `C² = Face → R`:
`⟨δ₁ h, ξ⟩_{C²} = ⟨h, η ξ⟩_{C¹}` for all `h, ξ` — both sides equal
`∑_{d ∈ D} h(edge d)·ξ(face d)`. A map and its transpose have equal rank, so
`finrank (range δ₁) = finrank (range η)`. -/

open Classical in
/-- The faces hit by the two darts of the edge `Edge_mk d₀`, recorded as an
F₂-indicator pair. This is the shared value of the `(f, e)` matrix entry of `δ₁`
and the `(e, f)` matrix entry of `η`. -/
lemma cobound1_single_eq_faceCobound_single [Fintype D] (d₀ : D) (f : M.Face) :
    (cobound1 (M := M)) (Pi.single (M.Edge_mk d₀) (1 : R)) f
      = (faceCobound (M := M)) (Pi.single f (1 : R)) (M.Edge_mk d₀) := by
  -- RHS: ξ(face d₀) + ξ(face αd₀), ξ = single f 1
  rw [faceCobound_apply_mk]
  -- LHS: ∑_{d ∈ faceFiber f} single (Edge_mk d₀) 1 (Edge_mk d)
  show (cobound1Fun (M := M) (Pi.single (M.Edge_mk d₀) (1 : R))) f = _
  simp only [cobound1Fun]
  -- the summand is the indicator [Edge_mk d = Edge_mk d₀]
  have hsummand : ∀ d ∈ faceFiber f,
      (Pi.single (M.Edge_mk d₀) (1 : R) : M.Edge → R) (M.Edge_mk d)
        = if M.Edge_mk d = M.Edge_mk d₀ then (1 : R) else 0 := by
    intro d _
    by_cases h : M.Edge_mk d = M.Edge_mk d₀
    · rw [h, Pi.single_eq_same, if_pos rfl]
    · rw [Pi.single_eq_of_ne h, if_neg h]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_boole]
  -- the filtered fiber is the part of the 2-dart edge orbit lying in face `f`
  have hcond : ∀ d : D, (M.Edge_mk d = M.Edge_mk d₀) ↔ (d = d₀ ∨ d = M.edgePerm d₀) := by
    intro d; rw [edge_mk_eq_iff]; exact M.sameCycle_edgePerm_iff d₀ d
  have hfilter : (faceFiber f).filter (fun d => M.Edge_mk d = M.Edge_mk d₀)
      = ({d₀, M.edgePerm d₀} : Finset D).filter (fun d => M.Face_mk d = f) := by
    ext d
    simp only [Finset.mem_filter, mem_faceFiber, Finset.mem_insert, Finset.mem_singleton]
    rw [hcond d]; tauto
  rw [hfilter]
  -- {d₀, αd₀} has two distinct darts; the filtered card is the sum of two indicators
  have hne : d₀ ≠ M.edgePerm d₀ := (M.edgePerm_apply_ne d₀).symm
  rw [Finset.filter_insert, Finset.filter_singleton, Pi.single_apply, Pi.single_apply]
  by_cases h0 : M.Face_mk d₀ = f <;> by_cases h1 : M.Face_mk (M.edgePerm d₀) = f
  · rw [if_pos h0, if_pos h1, if_pos h0, if_pos h1,
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    push_cast; ring
  · rw [if_pos h0, if_neg h1, if_pos h0, if_neg h1,
      Finset.card_insert_of_notMem (Finset.notMem_empty _), Finset.card_empty]
    push_cast; ring
  · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1, Finset.card_singleton]
    push_cast; ring
  · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1, Finset.card_empty]
    push_cast; ring

open Classical in
/-- **(T).** `δ₁` and `η` have equal rank, because `η = δ₁ᵀ` under the standard
coordinate bases. We realise both as matrices in the `Pi.basisFun` bases; the
matrix of `η` is the transpose of the matrix of `δ₁` (entrywise, this is
`cobound1_single_eq_faceCobound_single`), and a matrix and its transpose share a
rank. -/
lemma finrank_range_cobound1_eq_finrank_range_faceCobound [Fintype D] :
    Module.finrank R (LinearMap.range (cobound1 (M := M)))
      = Module.finrank R (LinearMap.range (faceCobound (M := M))) := by
  -- coordinate bases on the function spaces
  set bE := Pi.basisFun R M.Edge with hbE
  set bF := Pi.basisFun R M.Face with hbF
  -- the two matrices
  set Aδ : Matrix M.Face M.Edge R := LinearMap.toMatrix bE bF (cobound1 (M := M)) with hAδ
  set Aη : Matrix M.Edge M.Face R := LinearMap.toMatrix bF bE (faceCobound (M := M)) with hAη
  -- entrywise transpose relation `Aη = Aδ.transpose`
  have htrans : Aη = Aδ.transpose := by
    ext e f
    rw [Matrix.transpose_apply, hAη, hAδ, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      hbE, hbF, Pi.basisFun_repr, Pi.basisFun_repr, Pi.basisFun_apply, Pi.basisFun_apply]
    -- goal: (faceCobound (single f 1)) e = (cobound1 (single e 1)) f
    obtain ⟨d, rfl⟩ := Quotient.exists_rep e
    exact (cobound1_single_eq_faceCobound_single d f).symm
  -- ranks of the maps equal ranks of their matrices
  have hδ : Module.finrank R (LinearMap.range (cobound1 (M := M))) = Matrix.rank Aδ := by
    rw [Matrix.rank_eq_finrank_range_toLin Aδ bF bE, hAδ, Matrix.toLin_toMatrix]
  have hη : Module.finrank R (LinearMap.range (faceCobound (M := M))) = Matrix.rank Aη := by
    rw [Matrix.rank_eq_finrank_range_toLin Aη bE bF, hAη, Matrix.toLin_toMatrix]
  rw [hδ, hη, htrans, Matrix.rank_transpose]

/-! ### Top theorem: connected ⟹ `χ ≤ 2` -/

/-- A connected combinatorial map has Euler characteristic `≤ 2`.

Equivalently `χ = 2 − 2g ≤ 2` with genus `g ≥ 0`. Proved via the F₂ cochain
complex `(Vertex → R) →[δ₀] (Edge → R) →[δ₁] (Face → R)`: connectivity makes
`ker δ₀` (R1) and `ker η` (R2) at most one-dimensional, `δ₁ ∘ δ₀ = 0` is the
complex condition, and `η = δ₁ᵀ` gives `rank δ₁ = rank η`; the alternating
dimension count is then `≤ 2`. -/
theorem eulerCharacteristic_le_two [Fintype D]
    (M : CombinatorialMap D) (hconn : M.Connected) :
    M.eulerCharacteristic ≤ 2 := by
  -- identify finite ranks of the coordinate spaces with the cell counts
  have hV : Module.finrank R (M.Vertex → R) = Fintype.card M.Vertex :=
    Module.finrank_fintype_fun_eq_card R
  have hE : Module.finrank R (M.Edge → R) = Fintype.card M.Edge :=
    Module.finrank_fintype_fun_eq_card R
  have hF : Module.finrank R (M.Face → R) = Fintype.card M.Face :=
    Module.finrank_fintype_fun_eq_card R
  have hassembly :
      (Module.finrank R (M.Vertex → R) : ℤ) - Module.finrank R (M.Edge → R)
        + Module.finrank R (M.Face → R) ≤ 2 :=
    euler_assembly (cobound0 (M := M)) (cobound1 (M := M)) (faceCobound (M := M))
      (finrank_ker_cobound0_le_one hconn)
      (finrank_ker_faceCobound_le_one hconn)
      (LinearMap.range_le_ker_iff.mpr (cobound1_comp_cobound0))
      (finrank_range_cobound1_eq_finrank_range_faceCobound)
  rw [hV, hE, hF] at hassembly
  -- `eulerCharacteristic` is exactly that alternating count
  show (Fintype.card M.Vertex : ℤ) - Fintype.card M.Edge + Fintype.card M.Face ≤ 2
  exact hassembly

end CombinatorialMap





