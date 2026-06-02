/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMap
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

/-!
# Euler witness properties of the residual combinatorial map

This file proves the two EU-witness hypotheses about the residual combinatorial
map `residualMap G hARR` (built in `ResidualMap.lean`):

* `residualMap_isSimple` — under a no-loops / no-parallel-edges hypothesis on the
  drawing `G`, the residual map is simple (`CombinatorialMap.IsSimple`).
* `residualMap_connected` — under a graph-connectivity hypothesis on `G`, the
  residual map is connected (`CombinatorialMap.Connected`).

The structural heart is `residualMap_vertexMk_eq_iff`: two darts have the same
vertex class iff they share an `incidentEnds` block, i.e. have the same
`dartAnchor`. This follows from the block-diagonal structure of `vertexPerm`
(`Equiv.sigmaCongrRight` keeps the sigma-fibers invariant) together with the fact
that the per-block rotation is `finRotate` conjugated by `isoFin`, hence
transitive on each block.

Everything is sorry-free and axiom-clean.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap

variable (G : DrawnMultigraph)

/-! ## Generic helpers: SameCycle under `permCongr` and `sigmaCongrRight`. -/

/-- `SameCycle` for a conjugated permutation `e.permCongr σ` reduces to `SameCycle`
for `σ` on the pre-images under `e`. -/
theorem permCongr_sameCycle {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (x y : β) :
    (e.permCongr σ).SameCycle x y ↔ σ.SameCycle (e.symm x) (e.symm y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hzp : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) :=
      (map_zpow e.permCongrHom σ i).symm
    rw [hzp] at hi
    rw [Equiv.permCongr_apply] at hi
    have := congrArg e.symm hi
    rwa [Equiv.symm_apply_apply] at this
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hzp : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) :=
      (map_zpow e.permCongrHom σ i).symm
    rw [hzp, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

/-- The `i`-th power of `Equiv.sigmaCongrRight F` acts fiberwise. -/
theorem sigmaCongrRight_zpow {α : Type*} {β : α → Type*} (F : ∀ a, Equiv.Perm (β a))
    (i : ℤ) (s : Σ a, β a) :
    ((Equiv.sigmaCongrRight F) ^ i) s = ⟨s.1, (F s.1 ^ i) s.2⟩ := by
  have hzp : (Equiv.Perm.sigmaCongrRight F) ^ i
      = Equiv.Perm.sigmaCongrRight (fun a => F a ^ i) := by
    have h := (map_zpow (Equiv.Perm.sigmaCongrRightHom β) F i).symm
    rw [Equiv.Perm.sigmaCongrRightHom_apply, Equiv.Perm.sigmaCongrRightHom_apply] at h
    rw [h]
    rfl
  change ((Equiv.Perm.sigmaCongrRight F) ^ i) s = _
  rw [hzp]
  rfl

/-- `SameCycle` for `Equiv.sigmaCongrRight F` holds iff the base points agree and
the fiber points are `SameCycle` under the corresponding fiber permutation. -/
theorem sigmaCongrRight_sameCycle {α : Type*} {β : α → Type*}
    (F : ∀ a, Equiv.Perm (β a)) (s t : Σ a, β a) :
    (Equiv.Perm.sigmaCongrRight F).SameCycle s t ↔
      ∃ h : s.1 = t.1, (F s.1).SameCycle s.2 (h ▸ t.2) := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  constructor
  · rintro ⟨i, hi⟩
    rw [sigmaCongrRight_zpow F i ⟨s1, s2⟩] at hi
    have hbase : s1 = t1 := (Sigma.mk.injEq _ _ _ _).mp hi |>.1
    subst hbase
    refine ⟨rfl, i, ?_⟩
    have := (Sigma.mk.injEq _ _ _ _).mp hi |>.2
    simpa using this
  · rintro ⟨hbase, i, hi⟩
    simp only at hbase
    subst hbase
    refine ⟨i, ?_⟩
    rw [sigmaCongrRight_zpow F i ⟨s1, s2⟩]
    simp only at hi
    rw [hi]

/-! ## `finRotate` is transitive: any two indices share its cycle. -/

/-- `finRotate (n+2)` has no fixed points. -/
theorem finRotate_apply_ne {n : ℕ} (x : Fin (n + 2)) : finRotate (n + 2) x ≠ x := by
  have hx : x ∈ Equiv.Perm.support (finRotate (n + 2)) := by
    rw [support_finRotate]; exact Finset.mem_univ x
  exact (Equiv.Perm.mem_support.mp hx)

/-- `finRotate n` is transitive on `Fin n`: any two indices are in the same cycle. -/
theorem finRotate_sameCycle (n : ℕ) (x y : Fin n) :
    (finRotate n).SameCycle x y := by
  match n, x, y with
  | 0, x, _ => exact absurd x.2 (by omega)
  | 1, x, y => exact (Subsingleton.elim x y).sameCycle _
  | (m + 2), x, y =>
      exact isCycle_finRotate.sameCycle (finRotate_apply_ne x) (finRotate_apply_ne y)

/-! ## `dartAnchor` ↔ vertex-class characterisation for the residual map. -/

/-- The vertex permutation of the residual map, unfolded. -/
theorem residualMap_vertexPerm (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).vertexPerm
      = (dartSigmaEquiv G).symm.permCongr (sigmaVertexPerm G hARR) := rfl

/-- The edge permutation of the residual map is the end-swap. -/
theorem residualMap_edgePerm_apply (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    (residualMap G hARR).edgePerm d = (d.1, !d.2) := by
  rcases d with ⟨e, b⟩
  rfl

/-- Every power of the residual edge permutation preserves the edge index. -/
theorem residualMap_edgePerm_zpow_fst (hARR : ArcsRotationRegular G)
    (k : ℤ) (d : Fin G.numEdges × Bool) :
    (((residualMap G hARR).edgePerm ^ k) d).1 = d.1 := by
  have hinv : ∀ x : Fin G.numEdges × Bool,
      (((residualMap G hARR).edgePerm)⁻¹ x).1 = x.1 := by
    intro x
    have h :=
      residualMap_edgePerm_apply G hARR (((residualMap G hARR).edgePerm)⁻¹ x)
    have hx :
        (residualMap G hARR).edgePerm (((residualMap G hARR).edgePerm)⁻¹ x) = x :=
      Equiv.apply_symm_apply (residualMap G hARR).edgePerm x
    rw [hx] at h
    have hfirst :=
      congrArg (fun y : Fin G.numEdges × Bool => y.1) h
    exact hfirst.symm
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hpow :
          ((residualMap G hARR).edgePerm ^ (n + 1 : ℤ)) d =
            (residualMap G hARR).edgePerm
              (((residualMap G hARR).edgePerm ^ (n : ℤ)) d) := by
        rw [show (n + 1 : ℤ) = 1 + n by ring, zpow_add, zpow_one,
          Equiv.Perm.mul_apply]
      rw [hpow, residualMap_edgePerm_apply, ih]
  | pred n ih =>
      have hpow :
          ((residualMap G hARR).edgePerm ^ (-(n : ℤ) - 1 : ℤ)) d =
            ((residualMap G hARR).edgePerm)⁻¹
              (((residualMap G hARR).edgePerm ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1 : ℤ) = (-1) + (-n) by ring, zpow_add,
          zpow_neg_one, Equiv.Perm.mul_apply]
      rw [hpow, hinv, ih]

/-- Two darts have the same residual edge class iff they have the same edge
index. -/
theorem residualMap_edgeMk_eq_iff (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) :
    (residualMap G hARR).Edge_mk d = (residualMap G hARR).Edge_mk d' ↔
      d.1 = d'.1 := by
  rw [CombinatorialMap.Edge_mk, CombinatorialMap.Edge_mk, Quotient.eq'']
  change (residualMap G hARR).edgePerm.SameCycle d d' ↔ d.1 = d'.1
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact (residualMap_edgePerm_zpow_fst G hARR k d).symm
  · intro hidx
    rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    simp only at hidx
    subst e'
    cases b <;> cases b'
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    · exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    · exact Equiv.Perm.SameCycle.refl _ _

/-- The residual map's edge classes are canonically indexed by drawing edges. -/
noncomputable def residualMapEdgeEquiv (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).Edge ≃ Fin G.numEdges where
  toFun :=
    Quotient.lift Prod.fst (by
      intro d d' h
      exact (residualMap_edgeMk_eq_iff G hARR d d').mp (Quotient.sound h))
  invFun := fun e => (residualMap G hARR).Edge_mk (e, false)
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ d =>
        change (residualMap G hARR).Edge_mk (d.1, false) =
          (residualMap G hARR).Edge_mk d
        rw [residualMap_edgeMk_eq_iff]
  right_inv := by
    intro e
    rfl

/-- The residual map has one edge class for each drawn edge. -/
theorem residualMap_edge_card (hARR : ArcsRotationRegular G) :
    Fintype.card (residualMap G hARR).Edge = G.numEdges := by
  rw [Fintype.card_congr (residualMapEdgeEquiv G hARR), Fintype.card_fin]

/-- **Crux for simplicity & connectivity.** Two darts have the same residual
vertex class iff they have the same anchor vertex (equivalently, lie in the same
`incidentEnds` block). -/
theorem residualMap_vertexMk_eq_iff (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) :
    (residualMap G hARR).Vertex_mk d = (residualMap G hARR).Vertex_mk d' ↔
      dartAnchor G d = dartAnchor G d' := by
  rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq'']
  change (residualMap G hARR).vertexPerm.SameCycle d d' ↔ _
  rw [residualMap_vertexPerm, permCongr_sameCycle]
  -- Now `σ`-SameCycle on the sigma type, where `σ = sigmaVertexPerm`.
  rw [sigmaVertexPerm, sigmaCongrRight_sameCycle]
  constructor
  · rintro ⟨hbase, -⟩
    -- The base of `(dartSigmaEquiv G) d` is `⟨dartAnchor G d, _⟩`.
    have : (dartSigmaEquiv G d).1 = (dartSigmaEquiv G d').1 := by
      simpa using hbase
    have hval := congrArg (Subtype.val) this
    simpa [dartSigmaEquiv] using hval
  · intro hanchor
    have hbase : (dartSigmaEquiv G d).1 = (dartSigmaEquiv G d').1 := by
      apply Subtype.ext
      simpa [dartSigmaEquiv] using hanchor
    refine ⟨hbase, ?_⟩
    -- Within a single block, the rotation is transitive (conjugated `finRotate`).
    set p := (dartSigmaEquiv G d).1 with hp
    -- `vertexRotation G hARR p.2 = (isoFin L).toEquiv.permCongr (finRotate ..)`.
    have htrans : ∀ x y : ↥(incidentEnds G (p : ℝ × ℝ)),
        (vertexRotation G hARR p.2).SameCycle x y := by
      intro x y
      unfold vertexRotation vertexRotationAtRadius rotationOfOrder permOfEquiv
      -- `permOfEquiv eq = eq.permCongr (finRotate n)`.
      have heq : ∀ (n : ℕ) (eq : Fin n ≃ ↥(incidentEnds G (p : ℝ × ℝ))),
          ((eq.symm.trans (finRotate n)).trans eq) = eq.permCongr (finRotate n) := by
        intro n eq; rfl
      rw [heq]
      rw [permCongr_sameCycle]
      exact finRotate_sameCycle _ _ _
    -- transport `htrans` along `hbase`.
    have := htrans (dartSigmaEquiv G d).2 (hbase ▸ (dartSigmaEquiv G d').2)
    convert this using 2

/-- If every listed drawing vertex has an incident dart, residual vertex classes
are canonically equivalent to the listed drawing vertices. -/
noncomputable def residualMapVertexEquivOfIncident
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    (residualMap G hARR).Vertex ≃ ↥G.V where
  toFun :=
    Quotient.lift
      (fun d : Fin G.numEdges × Bool => ⟨dartAnchor G d, dartAnchor_mem G d⟩)
      (by
        intro d d' h
        apply Subtype.ext
        exact (residualMap_vertexMk_eq_iff G hARR d d').mp (Quotient.sound h))
  invFun := fun p =>
    (residualMap G hARR).Vertex_mk (Classical.choose (hincident p))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ d =>
        change
          (residualMap G hARR).Vertex_mk
              (Classical.choose
                (hincident ⟨dartAnchor G d, dartAnchor_mem G d⟩)) =
            (residualMap G hARR).Vertex_mk d
        rw [residualMap_vertexMk_eq_iff]
        exact dartAnchor_eq_of_mem G
          (Classical.choose_spec
            (hincident ⟨dartAnchor G d, dartAnchor_mem G d⟩))
  right_inv := by
    intro p
    apply Subtype.ext
    change dartAnchor G (Classical.choose (hincident p)) = (p : ℝ × ℝ)
    exact dartAnchor_eq_of_mem G (Classical.choose_spec (hincident p))

/-- Under incident coverage of the listed vertices, the residual map has the
same number of vertex classes as the drawing's vertex set. -/
theorem residualMap_vertex_card_of_incident
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    Fintype.card (residualMap G hARR).Vertex = Fintype.card ↥G.V := by
  exact Fintype.card_congr (residualMapVertexEquivOfIncident G hARR hincident)

/-! ## (A) Simplicity. -/

/-- The residual edge `e` has endpoint vertex-classes the residual vertices of
its two anchors `(G.endpoints e).1` and `(G.endpoints e).2`. -/
theorem residualMap_edge_ends (hARR : ArcsRotationRegular G)
    (e : Fin G.numEdges) :
    Edge.ends ((residualMap G hARR).Edge_mk (e, false))
      = s((residualMap G hARR).Vertex_mk (e, false),
          (residualMap G hARR).Vertex_mk (e, true)) := by
  rw [Edge.ends_mk,
    show (residualMap G hARR).edgePerm (e, false) = (e, true) by
      simp [residualMap_edgePerm_apply]]

/-- **(A) `residualMap_isSimple`.** Under no-loops and no-parallel-edges
hypotheses on the drawing `G`, the residual combinatorial map is simple. -/
theorem residualMap_isSimple (hARR : ArcsRotationRegular G)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e') :
    (residualMap G hARR).IsSimple := by
  classical
  -- Anchors of the two ends of edge `e`.
  have hanchor0 : ∀ e : Fin G.numEdges, dartAnchor G (e, false) = (G.endpoints e).1 := by
    intro e; rfl
  have hanchor1 : ∀ e : Fin G.numEdges, dartAnchor G (e, true) = (G.endpoints e).2 := by
    intro e; rfl
  constructor
  · -- No loops: no residual edge is a diagonal.
    intro edge
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    rcases d with ⟨e, b⟩
    -- The ends of edge `e` have anchors `(G.endpoints e).1 ≠ (G.endpoints e).2`,
    -- so their residual vertex classes differ.
    have hne : (residualMap G hARR).Vertex_mk (e, false)
        ≠ (residualMap G hARR).Vertex_mk (e, true) := by
      rw [Ne, residualMap_vertexMk_eq_iff, hanchor0, hanchor1]
      exact hloop e
    -- `Edge_mk (e,b) = Edge_mk (e,false)`.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]
          exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    change ¬ (Edge.ends ((residualMap G hARR).Edge_mk (e, b))).IsDiag
    rw [hedge, residualMap_edge_ends]
    rw [Sym2.isDiag_iff_proj_eq]
    exact hne
  · -- No parallel edges: `Edge.ends` injective.
    intro edge edge' hends
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    obtain ⟨d', rfl⟩ := Quotient.exists_rep edge'
    rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    -- Reduce both to the `false`-end representative.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    have hedge' : (residualMap G hARR).Edge_mk (e', b')
        = (residualMap G hARR).Edge_mk (e', false) := by
      cases b' with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    -- It suffices to show `(e,false)` and `(e',false)` are the same edge.
    suffices hgoal : (residualMap G hARR).Edge_mk (e, false)
        = (residualMap G hARR).Edge_mk (e', false) by
      change (residualMap G hARR).Edge_mk (e, b) = (residualMap G hARR).Edge_mk (e', b')
      rw [hedge, hedge', hgoal]
    -- From the endpoint-pair injectivity.
    have hends : Edge.ends ((residualMap G hARR).Edge_mk (e, b))
        = Edge.ends ((residualMap G hARR).Edge_mk (e', b')) := hends
    rw [hedge, hedge', residualMap_edge_ends, residualMap_edge_ends] at hends
    -- `hends` : `s(V e.1, V e.2) = s(V e'.1, V e'.2)` as residual vertex classes.
    -- We split on the two ways the unordered pair can match.
    rw [Sym2.eq_iff] at hends
    -- In either case, anchors of edge `e` are a permutation of anchors of `e'`.
    have key : s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- false↦false, true↦true
        rw [Sym2.eq_iff]; left
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor0] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor1] at h2
        exact ⟨h1, h2⟩
      · -- false↦true, true↦false
        rw [Sym2.eq_iff]; right
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor1] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor0] at h2
        exact ⟨h1, h2⟩
    have : e = e' := hpar e e' key
    subst this
    rfl

/-! ## (B) Connectivity. -/

/-- Graph-connectivity of the underlying drawing: any two vertices of `G.V` are
joined by an edge-walk, where an edge `e` connects its two endpoints. Mirrors the
combinatorial map's `Connected`. -/
def DrawnMultigraph.GraphConnected (G : DrawnMultigraph) : Prop :=
  ∀ p q : ↥G.V, Relation.ReflTransGen
    (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q

/-- A connected drawing with at least two listed vertices has no isolated listed
vertex: every `p : G.V` has an incident dart. -/
theorem incidentCoverage_of_graphConnected_of_two_le
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ) := by
  classical
  intro p
  have hcard' : 1 < Fintype.card ↥G.V := by omega
  rcases Finset.exists_mem_ne
      (s := (Finset.univ : Finset ↥G.V)) hcard' p with
    ⟨q, _hqmem, hqne⟩
  have hpath := hconn p q
  rw [Relation.ReflTransGen.cases_head_iff] at hpath
  rcases hpath with hpq | ⟨r, hstep, _hrq⟩
  · exact False.elim (hqne hpq.symm)
  rcases hstep with ⟨e, hforward | hbackward⟩
  · refine ⟨(e, false), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hforward.1⟩
  · refine ⟨(e, true), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hbackward.2⟩

/-- The residual one-step reachability relation. -/
private def resStep (hARR : ArcsRotationRegular G) :
    Fin G.numEdges × Bool → Fin G.numEdges × Bool → Prop :=
  fun a b => b = (residualMap G hARR).vertexPerm a
    ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
    ∨ b = (residualMap G hARR).edgePerm a

/-- A `vertexPerm`-power step is reachable by `ReflTransGen` of the residual step
relation (both natural- and inverse-power directions). -/
theorem reflTransGen_of_vertexPerm_zpow (hARR : ArcsRotationRegular G)
    (k : ℤ) (a : Fin G.numEdges × Bool) :
    Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ k) a) := by
  -- Reduce to natural powers in both directions.
  have hnat : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (n + 1)) a
            = (residualMap G hARR).vertexPerm (((residualMap G hARR).vertexPerm ^ n) a) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inl rfl)
  have hneg : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ (-(m : ℤ))) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (-(↑(n + 1) : ℤ))) a
            = (residualMap G hARR).vertexPerm⁻¹ (((residualMap G hARR).vertexPerm ^ (-(n : ℤ))) a) := by
          rw [show (-(↑(n + 1) : ℤ)) = (-1) + (-(n : ℤ)) by push_cast; ring,
            zpow_add, Equiv.Perm.mul_apply, zpow_neg_one]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inr (Or.inl rfl))
  rcases le_total 0 k with hk | hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast]; exact hnat m a
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hneg m a

/-- **Within-vertex reachability.** Any two darts with the same anchor are joined
by `ReflTransGen` of the residual step relation. -/
theorem reflTransGen_of_same_anchor (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) (h : dartAnchor G d = dartAnchor G d') :
    Relation.ReflTransGen (resStep G hARR) d d' := by
  have hsc : (residualMap G hARR).vertexPerm.SameCycle d d' := by
    have : (residualMap G hARR).Vertex_mk d = (residualMap G hARR).Vertex_mk d' :=
      (residualMap_vertexMk_eq_iff G hARR d d').mpr h
    rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq''] at this
    exact this
  obtain ⟨k, hk⟩ := hsc
  have := reflTransGen_of_vertexPerm_zpow G hARR k d
  rwa [hk] at this

/-- **Edge bridge.** The two ends of edge `e` are joined by a single residual
`edgePerm` step. -/
theorem reflTransGen_edge_bridge (hARR : ArcsRotationRegular G) (e : Fin G.numEdges) :
    Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) := by
  refine Relation.ReflTransGen.single (Or.inr (Or.inr ?_))
  simp [residualMap_edgePerm_apply]

/-- The residual step relation matches the `Connected` definition's step. -/
theorem resStep_eq_connectedStep (hARR : ArcsRotationRegular G)
    (a b : Fin G.numEdges × Bool) :
    resStep G hARR a b ↔
      (b = (residualMap G hARR).vertexPerm a
        ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
        ∨ b = (residualMap G hARR).edgePerm a) := Iff.rfl

/-- **(B) `residualMap_connected`.** Under graph-connectivity of `G`, the residual
combinatorial map is connected. -/
theorem residualMap_connected (hARR : ArcsRotationRegular G)
    (hconn : G.GraphConnected) :
    (residualMap G hARR).Connected := by
  classical
  -- We prove `ReflTransGen (resStep)` between any two darts, then convert.
  suffices hmain : ∀ d d' : Fin G.numEdges × Bool,
      Relation.ReflTransGen (resStep G hARR) d d' by
    intro d d'
    exact hmain d d'
  intro d d'
  -- Step 1: connect `d` to the `false`-end of its own edge `(d.1, false)`,
  -- and `d'` to `(d'.1, false)`; then connect anchors via graph walk.
  -- Anchors of d and d' lie in G.V.
  set pa : ↥G.V := ⟨dartAnchor G d, dartAnchor_mem G d⟩ with hpa
  set pb : ↥G.V := ⟨dartAnchor G d', dartAnchor_mem G d'⟩ with hpb
  -- Reachability between two darts whose anchors are joined by a graph walk:
  -- prove a general lemma by induction on the walk.
  have lift : ∀ (p q : ↥G.V),
      Relation.ReflTransGen
        (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
          ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
          ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q →
      ∀ (x : Fin G.numEdges × Bool), dartAnchor G x = (p : ℝ × ℝ) →
        ∀ (y : Fin G.numEdges × Bool), dartAnchor G y = (q : ℝ × ℝ) →
          Relation.ReflTransGen (resStep G hARR) x y := by
    intro p q hwalk
    induction hwalk with
    | refl =>
        intro x hx y hy
        exact reflTransGen_of_same_anchor G hARR x y (by rw [hx, hy])
    | @tail b c _hpb hbc ih =>
        intro x hx y hy
        obtain ⟨e, hcase⟩ := hbc
        rcases hcase with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · -- endpoints e = (b, c): use end `false` at anchor b, `true` at anchor c.
          have hf : dartAnchor G (e, false) = (b : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (c : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, false) :=
            ih x hx (e, false) hf
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) :=
            reflTransGen_edge_bridge G hARR e
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, true) y :=
            reflTransGen_of_same_anchor G hARR (e, true) y (by rw [ht, hy])
          exact (step1.trans step2).trans step3
        · -- endpoints e = (c, b): use end `false` at anchor c, `true` at anchor b.
          have hf : dartAnchor G (e, false) = (c : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (b : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, true) :=
            ih x hx (e, true) ht
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, true) (e, false) :=
            Relation.ReflTransGen.single (Or.inr (Or.inr (by simp [residualMap_edgePerm_apply])))
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, false) y :=
            reflTransGen_of_same_anchor G hARR (e, false) y (by rw [hf, hy])
          exact (step1.trans step2).trans step3
  exact lift pa pb (hconn pa pb) d rfl d' rfl

end CrossingLemma
