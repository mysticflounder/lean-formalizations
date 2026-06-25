/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 2/6 — **PrefixStepCore**: the core of the prefix-step
dart-relabeling development — the incident-ends bookkeeping and endpoint angular
order for a single new last edge. Split out of `ResidualMapProperties.lean`; see
that coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

/-! ## Prefix-step dart relabeling -/

def prefixStepDartToFun (m : ℕ) :
    (Fin m × Bool ⊕ Fin 2) → (Fin (m + 1) × Bool)
  | Sum.inl ⟨i, b⟩ => (Fin.castSucc i, b)
  | Sum.inr j => (Fin.last m, j = 1)

def prefixStepDartInvFun (m : ℕ) :
    (Fin (m + 1) × Bool) → (Fin m × Bool ⊕ Fin 2)
  | (i, b) =>
      if h : i.val < m then
        Sum.inl (⟨⟨i.val, h⟩, b⟩)
      else
        Sum.inr (if b then 1 else 0)

/-- The successor-prefix dart carrier `Fin (m+1) × Bool` is the old prefix dart
carrier `Fin m × Bool` plus the two darts of the new last edge. -/
def prefixStepDartEquiv (m : ℕ) :
    (Fin m × Bool ⊕ Fin 2) ≃ (Fin (m + 1) × Bool) where
  toFun := prefixStepDartToFun m
  invFun := prefixStepDartInvFun m
  left_inv := by
    intro x
    rcases x with x | j
    · rcases x with ⟨i, b⟩
      simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_castSucc, i.isLt]
    · fin_cases j <;> simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_last]
  right_inv := by
    intro d
    rcases d with ⟨i, b⟩
    by_cases h : i.val < m
    · simp [prefixStepDartToFun, prefixStepDartInvFun, h]
    · have hm : i.val = m := by omega
      have hi : i = Fin.last m := by
        apply Fin.ext
        simp [Fin.val_last, hm]
      subst hi
      cases b <;> simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_last]

@[simp] theorem prefixStepDartEquiv_apply_inl (m : ℕ) (i : Fin m) (b : Bool) :
    prefixStepDartEquiv m (Sum.inl (i, b)) = (Fin.castSucc i, b) := rfl

@[simp] theorem prefixStepDartEquiv_apply_inr_zero (m : ℕ) :
    prefixStepDartEquiv m (Sum.inr (0 : Fin 2)) = (Fin.last m, false) := by
  rfl

@[simp] theorem prefixStepDartEquiv_apply_inr_one (m : ℕ) :
    prefixStepDartEquiv m (Sum.inr (1 : Fin 2)) = (Fin.last m, true) := by
  rfl

@[simp] theorem prefixStepDartEquiv_symm_apply_castSucc (m : ℕ) (i : Fin m) (b : Bool) :
    (prefixStepDartEquiv m).symm (Fin.castSucc i, b) = Sum.inl (i, b) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_castSucc, i.isLt]

@[simp] theorem prefixStepDartEquiv_symm_apply_last_false (m : ℕ) :
    (prefixStepDartEquiv m).symm (Fin.last m, false) = Sum.inr (0 : Fin 2) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_last]

@[simp] theorem prefixStepDartEquiv_symm_apply_last_true (m : ℕ) :
    (prefixStepDartEquiv m).symm (Fin.last m, true) = Sum.inr (1 : Fin 2) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_last]

/-- The residual-map edge permutation is the product of the identity on the edge
index with the Boolean swap. -/
theorem residualMap_edgePerm_eq_boolSwap (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).edgePerm =
      Equiv.prodCongr (Equiv.refl (Fin G.numEdges)) (Equiv.swap false true) := by
  apply Equiv.ext
  rintro ⟨e, b⟩
  cases b <;> rfl

/-- After relabeling the enlarged dart carrier by `prefixStepDartEquiv`, the
inserted-edge involution becomes the standard residual end-swap on
`Fin (m+1) × Bool`, provided the old edge involution already had that form. -/
theorem prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply
    {m : ℕ} {M : CombinatorialMap (Fin m × Bool)}
    (hedge : ∀ d : Fin m × Bool, M.edgePerm d = (d.1, !d.2)) :
    (prefixStepDartEquiv m).permCongr (insEdgePerm M) =
      Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true) := by
  apply Equiv.ext
  intro x
  rcases (prefixStepDartEquiv m).surjective x with ⟨z, rfl⟩
  rw [Equiv.permCongr_apply]
  cases z with
  | inl old =>
      rcases old with ⟨i, b⟩
      cases b <;> simp [prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun,
        insEdgePerm, hedge]
  | inr j =>
      fin_cases j <;> simp [prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun,
        insEdgePerm, Fin.val_last]

/-- The same relabeling statement for leaf-edge insertion. The leaf and
same-face insertion maps share the same enlarged edge involution. -/
theorem prefixStepDartEquiv_permCongr_insertedLeafEdgePerm_of_edgePerm_apply
    {m : ℕ} {M : CombinatorialMap (Fin m × Bool)}
    (hedge : ∀ d : Fin m × Bool, M.edgePerm d = (d.1, !d.2)) :
    (prefixStepDartEquiv m).permCongr (insertedLeafEdgePerm M) =
      Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true) := by
  simpa [insertedLeafEdgePerm, insEdgePerm] using
    (prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply (m := m) (M := M) hedge)

/-- For residual maps of ordered prefixes, the leaf-insertion edge involution on
the `m`-prefix matches the residual end-swap on the `(m+1)`-prefix after
transport along `prefixStepDartEquiv`. -/
theorem prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    (prefixStepDartEquiv m).permCongr
      (insertedLeafEdgePerm (residualMap (G.prefixEdges m hm) hARR)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm := by
  trans Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true)
  · exact prefixStepDartEquiv_permCongr_insertedLeafEdgePerm_of_edgePerm_apply
      (M := residualMap (G.prefixEdges m hm) hARR)
      (hedge := residualMap_edgePerm_apply (G := G.prefixEdges m hm) hARR)
  · symm
    exact residualMap_edgePerm_eq_boolSwap (G := G.prefixEdges (m + 1) hm') hARR'

/-- For residual maps of ordered prefixes, the same-face insertion edge
involution on the `m`-prefix matches the residual end-swap on the `(m+1)`-prefix
after transport along `prefixStepDartEquiv`. -/
theorem prefixStepDartEquiv_permCongr_residualMap_insEdgePerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    (prefixStepDartEquiv m).permCongr
      (insEdgePerm (residualMap (G.prefixEdges m hm) hARR)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm := by
  trans Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true)
  · exact prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply
      (M := residualMap (G.prefixEdges m hm) hARR)
      (hedge := residualMap_edgePerm_apply (G := G.prefixEdges m hm) hARR)
  · symm
    exact residualMap_edgePerm_eq_boolSwap (G := G.prefixEdges (m + 1) hm') hARR'

private theorem castLE_castSucc_eq_castLE {m n : ℕ}
    (hm : m ≤ n) (hm' : m + 1 ≤ n) (i : Fin m) :
    Fin.castLE hm' i.castSucc = Fin.castLE hm i := by
  apply Fin.ext
  rfl

/-- On an old dart, the ARR angle is unchanged when passing from a prefix to
its successor prefix. The underlying arc is the same, and the first-crossing
parameter is unique, so the two witness families read off the same angle. -/
theorem arrAngle_prefixStep_inl_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (e : Fin m × Bool) (he : e ∈ incidentEnds (G.prefixEdges m hm) p)
    {r : ℝ} (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp)
    (hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp) :
    arrAngle (G.prefixEdges m hm) hARR hp e r =
      arrAngle (G.prefixEdges (m + 1) hm') hARR' hp (prefixStepDartEquiv m (Sum.inl e)) r := by
  obtain ⟨t, ht, hα⟩ := arrAngle_firstCrossing (G := G.prefixEdges m hm) hARR hp he hr0 hr
  have hsuccmem :
      prefixStepDartEquiv m (Sum.inl e) ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := by
    simpa [prefixStepDartEquiv_apply_inl] using
      (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm) (hm' := hm')).2 he
  obtain ⟨t', ht', hα'⟩ :=
    arrAngle_firstCrossing (G := G.prefixEdges (m + 1) hm') hARR' hp hsuccmem hr0 hr'
  have heG : (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p :=
    (mem_incidentEnds_prefixEdges_iff (G := G) (m := m) (hm := hm)).mp he
  have htG : IsFirstCrossing G p (Fin.castLE hm e.1, e.2) r t := by
    exact (prefixEdges_isFirstCrossing_iff (G := G) (m := m) (hm := hm)).mp ht
  have htG' : IsFirstCrossing G p (Fin.castLE hm e.1, e.2) r t' := by
    have htemp :
        IsFirstCrossing (G.prefixEdges (m + 1) hm') p
          (prefixStepDartEquiv m (Sum.inl e)) r t' := ht'
    have htmp := (prefixEdges_isFirstCrossing_iff (G := G) (m := m + 1) (hm := hm')).mp htemp
    simpa [prefixStepDartEquiv_apply_inl, castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using
      htmp
  have ht_eq : t = t' :=
    isFirstCrossing_unique_of_arcsJoinEndpoints G hjoin heG hr0 htG htG'
  calc
    arrAngle (G.prefixEdges m hm) hARR hp e r = angleAt p ((G.arc (Fin.castLE hm e.1)).param t) := by
      simpa [DrawnMultigraph.prefixEdges] using hα
    _ = angleAt p ((G.arc (Fin.castLE hm e.1)).param t') := by rw [ht_eq]
    _ = arrAngle (G.prefixEdges (m + 1) hm') hARR' hp (prefixStepDartEquiv m (Sum.inl e)) r := by
      symm
      simpa [prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges,
        castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using hα'

/-- To identify a successor-prefix residual map with a leaf insertion on the
previous prefix, it is enough to prove the vertex-permutation splice statement.
The edge permutation is already handled by
`prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm`, and the face
permutation then follows formally from the combinatorial-map axioms. -/
noncomputable def insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (b : Bool) (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    CombinatorialMap.Iso
      (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b)
      (residualMap (G.prefixEdges (m + 1) hm') hARR') :=
  isoOfPermCongrOfVertexEdge (prefixStepDartEquiv m) hvertex
    (by
      simpa using
        (prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm
          (G := G) m hm hm' hARR hARR'))

/-- To identify a successor-prefix residual map with a same-face insertion on
the previous prefix, it is enough to prove the vertex-permutation splice
statement. The edge permutation is already handled by
`prefixStepDartEquiv_permCongr_residualMap_insEdgePerm`, and the face
permutation then follows formally from the combinatorial-map axioms. -/
noncomputable def insertedEdgeMapIsoOfPrefixStepVertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    CombinatorialMap.Iso
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂)
      (residualMap (G.prefixEdges (m + 1) hm') hARR') :=
  isoOfPermCongrOfVertexEdge (prefixStepDartEquiv m) hvertex
    (prefixStepDartEquiv_permCongr_residualMap_insEdgePerm
      (G := G) m hm hm' hARR hARR')

/-- **Leaf insertion, residual-map form.** If the successor prefix is identified
with the leaf-edge insertion of the previous residual map by the vertex-rotation
splice equation, then planarity of the previous residual map implies planarity
of the successor residual map.

This is the combinatorial-map layer corresponding to the usual planar-embedding
operation of adding a leaf edge: the new edge is inserted at one old corner and
the other new dart is a singleton vertex. -/
theorem residualMap_isPlanar_prefixStep_leaf_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (b : Bool) (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  let iso := insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' b c hvertex
  exact (isPlanar_iff_of_iso iso).mpr
    (isPlanar_insertedLeafEdgeMapAt (M := residualMap (G.prefixEdges m hm) hARR)
      (c := c) b hplanar)

/-- **Same-face insertion, residual-map form.** If the successor prefix is
identified with the facial insertion of a new edge into the previous residual map
by the vertex-rotation splice equation, then planarity is preserved provided the
two insertion corners lie on the same face of the previous residual map.

This is the residual-map version of the standard planar-embedding operation of
drawing an edge inside a face between two existing corners. -/
theorem residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  exact (isPlanar_iff_of_iso iso).mpr
    (isPlanar_insertedEdgeMap_of_sameCycle
      (M := residualMap (G.prefixEdges m hm) hARR) (c₁ := c₁) (c₂ := c₂)
      hc hplanar hsame)

/-- If both the predecessor residual map and the successor residual map are
planar, then the successor edge really was a same-face insertion at the
predecessor. This is the converse of
`residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm`, and packages the
inserted-edge converse theorem at the residual-map level. -/
theorem sameFace_of_planar_prefixStep_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar)
    (hplanar' : (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂ := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  have hplanarInserted :
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).IsPlanar := by
    exact (isPlanar_iff_of_iso iso).mp hplanar'
  exact CombinatorialMap.EdgeInsertion.sameCycle_of_isPlanar_insertedEdgeMap
    (M := residualMap (G.prefixEdges m hm) hARR) (c₁ := c₁) (c₂ := c₂) hc
    hplanarInserted hplanar

/-- Same-face prefix insertion preserves the face-cycle relation between old
darts outside the split residual face.

This is the residual-map transport of the standard face-splitting fact for
combinatorial maps: after inserting an edge through one face, every old face
other than the split face is carried unchanged through the successor prefix
isomorphism. -/
theorem residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_of_not_sameCycle
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hx : ¬ (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x c₁)
    (hy : ¬ (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle y c₁) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl x)) (prefixStepDartEquiv m (Sum.inl y)) ↔
      (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x y := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl x)) (iso.toEquiv (Sum.inl y)) ↔
    (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x y
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_of_not_sameCycle
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ x y hc hsame hx hy

/-- Same-face prefix insertion identifies successor same-face relations for old
darts with equality in the split-face quotient of the inserted predecessor map.

This is the residual-prefix form of the Lando--Zvonkin face split: after the
new edge is inserted through one predecessor face, later cotree bookkeeping can
test whether two old darts still lie in the same successor face by comparing
their images in `insertedFaceSplitPoolEquiv`. -/
theorem residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl x)) (prefixStepDartEquiv m (Sum.inl y)) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl y)) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl x)) (iso.toEquiv (Sum.inl y)) ↔
    insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
          (Sum.inl x)) =
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
          (Sum.inl y))
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ x y hc hsame

/-- Same-face prefix insertion identifies all successor face equalities with
equality in the inserted split-face quotient.

This is the unrestricted split-face criterion.  The earlier old-dart version is
the common cotree-label case, but later splice corners in an induction may also
be one of the two darts of the most recently inserted edge; this form keeps the
new-dart cases available without another ad hoc case split. -/
theorem residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (x y : (Fin m × Bool) ⊕ Fin 2) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m x) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m y) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk x) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk y) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  constructor
  · intro hface
    have hcycle :
        (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
          (prefixStepDartEquiv m x) (prefixStepDartEquiv m y) :=
      Quotient.eq''.mp hface
    have hcycle_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).facePerm.SameCycle
          x y := by
      simpa [iso] using (CombinatorialMap.Iso.facePerm_sameCycle_iff iso x y).mp hcycle
    exact congrArg
      (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame)
      (Quotient.sound hcycle_inserted)
  · intro hsplit
    have hface_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk x =
          (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk y :=
      (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame).injective
        hsplit
    have hcycle_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).facePerm.SameCycle
          x y :=
      Quotient.eq''.mp hface_inserted
    have hcycle :
        (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
          (prefixStepDartEquiv m x) (prefixStepDartEquiv m y) := by
      simpa [iso] using (CombinatorialMap.Iso.facePerm_sameCycle_iff iso x y).mpr
        hcycle_inserted
    exact Quotient.sound hcycle

/-- Current-prefix form of
`residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq`.

This is the form used by the next cotree insertion: its predecessor splice
corners are darts of the current prefix.  Pulling them back through
`prefixStepDartEquiv.symm` records whether each corner is carried from the
previous prefix or is one of the two newly inserted darts. -/
theorem residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (x y : Fin (m + 1) × Bool) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk x =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk y ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            ((prefixStepDartEquiv m).symm x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            ((prefixStepDartEquiv m).symm y)) := by
  simpa using
    (residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
      ((prefixStepDartEquiv m).symm x) ((prefixStepDartEquiv m).symm y))

/-- Face equality for carried old darts after a same-face prefix insertion is
equivalent to equality in the inserted split-face quotient.

This is the quotient-valued form of
`residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq`.  It
is the form consumed by the later cotree constructor: the cotree label invariant
produces equality in `insertedFaceSplitPoolEquiv`, while
`ResidualMapPrefixStepInsertion.sameFace` asks for equality of predecessor
`Face_mk` classes. -/
theorem residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl x)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl y)) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl y)) := by
  constructor
  · intro hface
    exact
      (residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
        (G := G) m hm hm' hARR hARR' c₁ c₂ x y hc hsame hvertex).mp
        (Quotient.eq''.mp hface)
  · intro hsplit
    exact Quotient.sound
      ((residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
        (G := G) m hm hm' hARR hARR' c₁ c₂ x y hc hsame hvertex).mpr hsplit)

/-- Reverse cotree label transport gives split-pool equality after one
same-face residual-prefix insertion.

This is the residual-map form of the Lando--Zvonkin face-splitting quotient:
if the inserted split-pool label is constant along the still-unpeeled dual
prefix, then the reverse cotree edge selected at the current leaf-peeling step
has equal split-pool labels on its two old incident faces. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent i =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  exact
    CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
      T hTsub parent hparent i label hlabel hadj

/-- Reverse cotree split-pool label transport gives successor face equality
after one same-face residual-prefix insertion.

This combines the reverse cotree label invariant with the Lando--Zvonkin
split-face quotient for a same-face insertion.  If the inserted split-pool
label is constant along the still-unpeeled dual prefix, then the concrete
reverse cotree edge selected at the current leaf-peeling step has its two old
incident faces identified in the successor residual map. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v →
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
          label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent i =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  classical
  obtain ⟨d, hedge, hsplit⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub parent hparent i label hlabel hadj
  refine ⟨d, hedge, ?_⟩
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Reverse cotree split-pool label transport for the next unpeeled prefix.

This is the residual-map form of the reverse leaf-peeling invariant: after the
current reverse cotree leaf-parent edge is peeled, it is enough to verify the
split-pool label invariant on every edge internal to the next unpeeled dual
prefix except that peeled edge.  Connectedness of the next prefix then gives
split-pool equality for the next selected reverse cotree edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  exact
    CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj_ne_current_parent
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj

/-- Reverse cotree face-label transport on a residual map prefix.

This is the residual-map packaging of the generic reverse leaf-peeling label
transport lemma from `VertexGraph.lean`: once a label is constant across the
adjacent pairs inside the next unpeeled reverse prefix, it is constant on that
whole prefix. -/
theorem residualMap_prefixStep_faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_face_label_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    {β : Type*} (label : (residualMap (G.prefixEdges m hm) hARR).Face → β)
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    {u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hu : u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset)
    (hv : v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset) :
    label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v) := by
  simpa using
    (CombinatorialMap.faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_face_label_eq_of_forall_adj_ne_current_parent
      (M := residualMap (G.prefixEdges m hm) hARR) T hl_nodup parent hparent i
      label hadj hu hv)

/-- Representative-invariant reverse cotree split-pool label transport.

The selector `faceEdgeOfLeafOrderReverse` names an unoriented edge class.  This
version of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent`
works for any dart representative of that edge class, reversing the two
incident faces if necessary.  This is the shape consumed by constructor-facing
same-face insertion witnesses, whose endpoint adapter may choose either
orientation of the selected residual edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      (residualMap (G.prefixEdges m hm) hARR).Edge_mk d =
        (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) :
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  let M := residualMap (G.prefixEdges m hm) hARR
  obtain ⟨d₀, hedge, hsplit₀⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj
  have hE : M.Edge_mk d = M.Edge_mk d₀ := by
    exact hd.trans hedge
  have hlabel₀ : label (M.Face_mk d₀) = label (M.Face_mk (M.edgePerm d₀)) := by
    calc
      label (M.Face_mk d₀)
          = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
              ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d₀)) := hlabel d₀
      _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
              ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d₀))) := hsplit₀
      _ = label (M.Face_mk (M.edgePerm d₀)) := (hlabel (M.edgePerm d₀)).symm
  have hlabel_d : label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) :=
    M.edge_face_label_eq_of_edge_mk_eq label hE hlabel₀
  calc
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_d
    _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

/-- Reverse cotree split-pool label transport from dual face-pair equality.

This is the face-pair form of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`:
the quotient transport depends only on the unordered dual face pair of the
current reverse leaf-parent edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      s((residualMap (G.prefixEdges m hm) hARR).Face_mk d,
        (residualMap (G.prefixEdges m hm) hARR).Face_mk
          ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)) =
        s(dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega)))) :
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  let M := residualMap (G.prefixEdges m hm) hARR
  have hlabel_d : label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
      T hTsub hl_nodup parent hparent i j hprefix label hadj d hd
  calc
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_d
    _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

/-- Reverse cotree successor face equality for the next unpeeled prefix.

This composes the non-peeled-edge split-pool transport with the residual
same-face quotient criterion, producing successor `Face_mk` equality for the
next selected reverse cotree edge after one same-face insertion. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  classical
  obtain ⟨d, hedge, hsplit⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj
  refine ⟨d, hedge, ?_⟩
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Representative-invariant reverse cotree successor face equality.

This converts the non-peeled-edge split-pool invariant into successor
`Face_mk` equality for any dart representative of the selected reverse cotree
edge, rather than only the representative produced by the cotree selector proof.
It is the face-equality form needed before matching the selected edge to the
actual endpoint splice corners of the ordered drawing prefix. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      (residualMap (G.prefixEdges m hm) hARR).Edge_mk d =
        (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  have hsplit :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj d hd
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Reverse cotree successor face equality from dual face-pair equality.

This is the face-pair form of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`.
It records only the unordered pair of predecessor faces of the current reverse
leaf-parent edge, matching the literature's tree-cotree statements. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      s((residualMap (G.prefixEdges m hm) hARR).Face_mk d,
        (residualMap (G.prefixEdges m hm) hARR).Face_mk
          ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)) =
        s(dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega)))) :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  have hsplit :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj d hd
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Same-face prefix insertion separates the two old cut corners into the two
successor residual faces. -/
theorem residualMap_prefixStep_sameFace_old_corners_not_sameCycle
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    ¬ (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁)) (prefixStepDartEquiv m (Sum.inl c₂)) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change ¬ (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl c₁)) (iso.toEquiv (Sum.inl c₂))
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_not_sameCycle_inl_corners
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame

/-- Same-face prefix insertion puts the old left cut corner in the successor
face of the new dart `(Fin.last m, true)`. -/
theorem residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁)) (Fin.last m, true) := by
  have hcycle :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁))
        (prefixStepDartEquiv m (dartB : Fin m × Bool ⊕ Fin 2)) := by
    let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
      (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
    change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (iso.toEquiv (Sum.inl c₁)) (iso.toEquiv (dartB : Fin m × Bool ⊕ Fin 2))
    rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
    exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_left_dartB
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
  rw [prefixStepDartEquiv_apply_inr_one] at hcycle
  exact hcycle

/-- Same-face prefix insertion puts the old right cut corner in the successor
face of the new dart `(Fin.last m, false)`. -/
theorem residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₂)) (Fin.last m, false) := by
  have hcycle :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₂))
        (prefixStepDartEquiv m (dartA : Fin m × Bool ⊕ Fin 2)) := by
    let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
      (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
    change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (iso.toEquiv (Sum.inl c₂)) (iso.toEquiv (dartA : Fin m × Bool ⊕ Fin 2))
    rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
    exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_right_dartA
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
  rw [prefixStepDartEquiv_apply_inr_zero] at hcycle
  exact hcycle

/-- Face-class form of
`residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true`. -/
theorem residualMap_prefixStep_sameFace_old_left_corner_face_eq_last_true
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₁)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true) := by
  exact Quotient.sound
    (residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex)

/-- Face-class form of
`residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false`. -/
theorem residualMap_prefixStep_sameFace_old_right_corner_face_eq_last_false
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₂)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) := by
  exact Quotient.sound
    (residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex)

/-- Same-face prefix insertion separates the two old cut-corner face classes in
the successor residual map. -/
theorem residualMap_prefixStep_sameFace_old_corners_face_ne
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₁)) ≠
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₂)) := by
  intro hface
  exact residualMap_prefixStep_sameFace_old_corners_not_sameCycle
    (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
    (Quotient.eq''.mp hface)

/-- Same-face prefix insertion creates two distinct successor faces on the two
sides of the new last edge. -/
theorem residualMap_prefixStep_sameFace_new_edge_faces_ne
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) ≠
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true) := by
  intro hlast
  have hleft :=
    residualMap_prefixStep_sameFace_old_left_corner_face_eq_last_true
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
  have hright :=
    residualMap_prefixStep_sameFace_old_right_corner_face_eq_last_false
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
  exact
    residualMap_prefixStep_sameFace_old_corners_face_ne
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
      (hleft.trans (hlast.symm.trans hright.symm))

/-- Same-face prefix insertion makes the new residual edge a dual adjacency
between the two split successor faces.

This is the residual-map version of
`CombinatorialMap.insertedEdgeMap_faceGraph_adj_new_edge`: under the prefix-step
isomorphism, `dartA` and `dartB` become the two darts of the new last edge,
`(Fin.last m, false)` and `(Fin.last m, true)`.  Thus the new edge is the dual
edge between the two faces created by the split. -/
theorem residualMap_prefixStep_sameFace_new_edge_faceGraph_adj_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    ((residualMap (G.prefixEdges (m + 1) hm') hARR').faceGraph).Adj
      ((residualMap (G.prefixEdges (m + 1) hm') hARR').dual.Vertex_mk
        (Fin.last m, false))
      ((residualMap (G.prefixEdges (m + 1) hm') hARR').dual.Vertex_mk
        (Fin.last m, true)) := by
  classical
  let M₀ := residualMap (G.prefixEdges m hm) hARR
  let M₁ := residualMap (G.prefixEdges (m + 1) hm') hARR'
  let I := insertedEdgeMap M₀ c₁ c₂
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  refine ⟨?hne, ⟨M₁.dual.Edge_mk (Fin.last m, false), ?hends⟩⟩
  · intro h
    have hface : M₁.Face_mk (Fin.last m, false) = M₁.Face_mk (Fin.last m, true) := by
      change (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true)
      have h' := congrArg
        (dualVertexEquivFace (residualMap (G.prefixEdges (m + 1) hm') hARR')) h
      simpa only [dualVertexEquivFace_vertexMk] using h'
    have htarget : M₁.facePerm.SameCycle (Fin.last m, false) (Fin.last m, true) :=
      Quotient.eq''.mp hface
    have hinsert : I.facePerm.SameCycle (dartA : Fin m × Bool ⊕ Fin 2) dartB := by
      have hiff := CombinatorialMap.Iso.facePerm_sameCycle_iff iso
        (dartA : Fin m × Bool ⊕ Fin 2) dartB
      exact hiff.mp (by simpa [iso, I, M₁] using htarget)
    have hfaceI : I.Face_mk (dartA : Fin m × Bool ⊕ Fin 2) = I.Face_mk dartB :=
      Quotient.sound hinsert
    have himg := congrArg (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame) hfaceI
    change (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame)
        ((insertedEdgeMap M₀ c₁ c₂).Face_mk dartA) =
      (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame)
        ((insertedEdgeMap M₀ c₁ c₂).Face_mk dartB) at himg
    rw [insertedFaceSplitPoolEquiv_mk_dartA_right M₀ c₁ c₂ hc hsame,
      insertedFaceSplitPoolEquiv_mk_dartB_left M₀ c₁ c₂ hc hsame] at himg
    exact (by decide : (1 : Fin 2) ≠ 0) (Sum.inr.inj himg)
  · simpa [M₁, faceGraph, CombinatorialMap.dual, residualMap_edgePerm_apply]
      using (Edge.ends_mk (M := M₁.dual) (Fin.last m, false))

/-- The two residual-map insertion alternatives for one ordered prefix step.

The `leaf` case is the tree-growth operation: one endpoint of the new edge is a
new leaf vertex and the old endpoint rotation is a single-corner splice.  The
`sameFace` case is the cotree-growth operation: both endpoints are already in
the previous prefix, the two splice corners lie on the same face, and the
successor rotation is the two-corner splice. -/
inductive ResidualMapPrefixStepInsertion
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) : Prop
  | leaf (b : Bool) (c : Fin m × Bool)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
  | sameFace (c₁ c₂ : Fin m × Bool)
      (hc : c₁ ≠ c₂)
      (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)

/-- Explicit same-face data for one ordered prefix step.

This is the witness package carried by the cotree phase: two predecessor darts
in one residual face, together with the transported vertex-permutation splice
statement identifying the successor residual map with the corresponding
`insertedEdgeMap`. -/
structure ResidualMapPrefixStepSameFaceData
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) where
  c₁ : Fin m × Bool
  c₂ : Fin m × Bool
  hc : c₁ ≠ c₂
  hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂
  hvertex :
    (prefixStepDartEquiv m).permCongr
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm

/-- Forget explicit same-face data down to the corresponding ordered-prefix
insertion witness. -/
def ResidualMapPrefixStepSameFaceData.toInsertion
    {m : ℕ} {hm : m ≤ G.numEdges} {hm' : m + 1 ≤ G.numEdges}
    {hARR : ArcsRotationRegular (G.prefixEdges m hm)}
    {hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')}
    (hdata : ResidualMapPrefixStepSameFaceData (G := G) m hm hm' hARR hARR') :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' :=
  .sameFace hdata.c₁ hdata.c₂ hdata.hc hdata.hsame hdata.hvertex

/-- A `ResidualMapPrefixStepInsertion` witness turns planarity of the previous
prefix residual map into planarity of the successor prefix residual map. -/
theorem residualMap_isPlanar_prefixStep_of_insertion
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hstep : ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR')
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  cases hstep with
  | leaf b c hvertex =>
      exact residualMap_isPlanar_prefixStep_leaf_of_vertexPerm
        (G := G) m hm hm' hARR hARR' b c hvertex hplanar
  | sameFace c₁ c₂ hc hsame hvertex =>
      exact residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm
        (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex hplanar

/-- Ordered-prefix planarity induction for residual maps.

Starting from a planar base prefix, if every later prefix step is either a
leaf insertion or a same-face insertion in the sense of
`ResidualMapPrefixStepInsertion`, then every later prefix residual map is
planar. This is the formal insertion-order skeleton used by tree-cotree proofs:
the geometric content is exactly the construction of the step witnesses. -/
theorem residualMap_isPlanar_prefix_of_insertions_from
    (start : ℕ)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hbase : ∀ hstart : start ≤ G.numEdges,
      (residualMap (G.prefixEdges start hstart) (hARR start hstart)).IsPlanar)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (n : ℕ) (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).IsPlanar := by
  revert hn
  refine Nat.le_induction ?base ?step n hstartn
  · intro hstartG
    exact hbase hstartG
  · intro m hstartm ih hm'
    exact residualMap_isPlanar_prefixStep_of_insertion
      (G := G) m (Nat.le_of_succ_le hm') hm'
      (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
      (hstep m hm' hstartm)
      (ih (Nat.le_of_succ_le hm'))

/-- Bounded ordered-prefix planarity induction for residual maps.

This is the interval form of `residualMap_isPlanar_prefix_of_insertions_from`:
to prove planarity only up to a target prefix `n`, it is enough to construct
insertion witnesses only for the steps with `m + 1 ≤ n`. -/
theorem residualMap_isPlanar_prefix_of_insertions_to
    (start n : ℕ)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hbase : ∀ hstart : start ≤ G.numEdges,
      (residualMap (G.prefixEdges start hstart) (hARR start hstart)).IsPlanar)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m → m + 1 ≤ n →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).IsPlanar := by
  have hmain : ∀ k : ℕ, start ≤ k → k ≤ n →
      ∀ hk : k ≤ G.numEdges,
        (residualMap (G.prefixEdges k hk) (hARR k hk)).IsPlanar := by
    intro k hstartk
    refine Nat.le_induction ?base ?step k hstartk
    · intro _ hstartG
      exact hbase hstartG
    · intro m hstartm ih hm_succ_le_n hm_succ
      exact residualMap_isPlanar_prefixStep_of_insertion
        (G := G) m (Nat.le_of_succ_le hm_succ) hm_succ
        (hARR m (Nat.le_of_succ_le hm_succ)) (hARR (m + 1) hm_succ)
        (hstep m hm_succ hstartm hm_succ_le_n)
        (ih (Nat.le_of_succ_le hm_succ_le_n) (Nat.le_of_succ_le hm_succ))
  exact hmain n hstartn (Nat.le_refl n) hn

/-- At an endpoint of the new last edge, the incident-end type of the
successor prefix is the old incident-end type plus one new dart. -/
noncomputable def incident_ends_prefix_step_endpoint_equiv
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit ≃
      ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
  adjoin_point_equiv
    (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)
    (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother)

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inl
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother (Sum.inl a) =
      (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother a).1 := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inr
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother (Sum.inr ()) =
      incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_old_equiv_apply_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    ((incident_ends_prefix_step_endpoint_old_equiv
        (G := G) m hm hm' b hpnew hpother a).1).1 =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  rfl

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inl_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    (incident_ends_prefix_step_endpoint_equiv
        (G := G) m hm hm' b hpnew hpother (Sum.inl a)).1 =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inr_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    (incident_ends_prefix_step_endpoint_equiv
        (G := G) m hm hm' b hpnew hpother (Sum.inr ())).1 =
      (Fin.last m, b) := by
  rw [incident_ends_prefix_step_endpoint_equiv_apply_inr]
  rfl

/-- If the carried old endpoint dart is the angular predecessor of the new
endpoint dart, then it is also the predecessor under the successor residual-map
vertex permutation.

This is the combinatorial-map form of the straight-line predecessor witness:
an equality proved using `vertexRotationAtRadius` on the drawing side converts
directly into a `vertexPerm` predecessor relation in the successor residual
map. -/
theorem residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ (G.prefixEdges (m + 1) hm').V)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother c).1) =
      incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
  let x :=
    incident_ends_prefix_step_endpoint_old_equiv
      (G := G) m hm hm' b hpnew hpother c
  have hrot :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr)) =
        vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp :=
    rotation_wellDefined (G := G.prefixEdges (m + 1) hm') hARR' hp hr0 hr
  have hrotx :
      ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp) x).1 =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    have hx :
        vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
            (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
              (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr)) x =
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
      simpa [x] using hpred
    exact congrArg Subtype.val (hrot.symm ▸ hx)
  calc
    (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm x.1
        = ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp) x).1 := by
            exact residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp x
    _ = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := hrotx

/-- Face-class form of
`residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius`.

The predecessor old endpoint dart represents the same successor face as the
opposite side of the newly inserted edge. -/
theorem residualMap_face_prefix_step_endpoint_old_eq_edgePerm_new_of_vertexRotationAtRadius
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ (G.prefixEdges (m + 1) hm').V)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother c).1) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        ((residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm
          (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)) := by
  let M := residualMap (G.prefixEdges (m + 1) hm') hARR'
  let x :=
    (incident_ends_prefix_step_endpoint_old_equiv
      (G := G) m hm hm' b hpnew hpother c).1
  let y := incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew
  have hperm : M.vertexPerm x = y :=
    residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius
      (G := G) m hm hm' b hpnew hpother hARR' hp hr0 hr c hpred
  have hx : x = M.vertexPerm⁻¹ y := by
    apply M.vertexPerm.injective
    simpa using hperm
  calc
    M.Face_mk x = M.Face_mk (M.vertexPerm⁻¹ y) := by rw [hx]
    _ = M.Face_mk (M.facePerm (M.edgePerm y)) := by
          rw [M.vertexPerm_inv_eq_facePerm_edgePerm]
    _ = M.Face_mk (M.edgePerm y) := by rw [M.faceMk_facePerm]

/-- At a vertex not touched by the new last edge, the carried-over incident ends
of the predecessor and successor prefixes are canonically equivalent.

This is the transport equivalence needed for the unchanged-vertex part of the
ordered-prefix insertion witnesses. -/
noncomputable def incident_ends_prefix_step_unchanged_equiv
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    ↥(incidentEnds (G.prefixEdges m hm) p) ≃
      ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) := by
  refine Equiv.ofBijective
    (fun a =>
      ⟨prefixStepDartEquiv m (Sum.inl a.1),
        by
          simpa [prefixStepDartEquiv_apply_inl] using
            (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
              (hm' := hm')).2 a.2⟩)
    ?_
  constructor
  · intro a1 a2 h
    rcases a1 with ⟨⟨i1, b1⟩, ha1⟩
    rcases a2 with ⟨⟨i2, b2⟩, ha2⟩
    apply Subtype.ext
    apply Prod.ext
    · have hpair := congrArg Subtype.val h
      have hfst : Fin.castSucc i1 = Fin.castSucc i2 := by
        simpa only [prefixStepDartEquiv_apply_inl] using congrArg Prod.fst hpair
      exact Fin.castSucc_injective _ hfst
    · have hpair := congrArg Subtype.val h
      simpa only [prefixStepDartEquiv_apply_inl] using congrArg Prod.snd hpair
  · intro e
    rcases e with ⟨⟨i, b⟩, he⟩
    by_cases hlast : i = Fin.last m
    · subst hlast
      cases b <;> exfalso
      · have hnot : (Fin.last m, false) ∉ incidentEnds (G.prefixEdges (m + 1) hm') p := by
          intro hmem
          unfold incidentEnds at hmem
          change (Fin.last m, false) ∈
            Finset.univ.filter
              (fun e : Fin (m + 1) × Bool =>
                if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
                else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p) at hmem
          rw [Finset.mem_filter] at hmem
          exact hp1 hmem.2
        exact hnot he
      · have hnot : (Fin.last m, true) ∉ incidentEnds (G.prefixEdges (m + 1) hm') p := by
          intro hmem
          unfold incidentEnds at hmem
          change (Fin.last m, true) ∈
            Finset.univ.filter
              (fun e : Fin (m + 1) × Bool =>
                if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
                else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p) at hmem
          rw [Finset.mem_filter] at hmem
          exact hp2 hmem.2
        exact hnot he
    · have hpair : (Fin.castSucc (i.castPred hlast), b) = (i, b) := by
        ext <;> simp [Fin.castSucc_castPred]
      have hsucc : (Fin.castSucc (i.castPred hlast), b) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
        simpa [hpair] using he
      have hsrc : (i.castPred hlast, b) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨i.castPred hlast, b⟩)).mp hsucc
      refine ⟨⟨(i.castPred hlast, b), hsrc⟩, ?_⟩
      apply Subtype.ext
      simpa only [prefixStepDartEquiv_apply_inl, Fin.castSucc_castPred]

@[simp] theorem incident_ends_prefix_step_unchanged_equiv_apply_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    ((incident_ends_prefix_step_unchanged_equiv
        (G := G) m hm hm' hp1 hp2 a).1) =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  rfl

/-- At a vertex untouched by the new last edge, the carried-over angular order
is preserved by the canonical transport equivalence. This is the unchanged-vertex
transport theorem needed for the tree-first prefix witness construction. -/
theorem vertexRotationAtRadius_prefix_step_unchanged
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp)
    (hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp) :
    (incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2).permCongr
      (vertexRotationAtRadius (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r
        (endAngleKey_injective (G.prefixEdges m hm) p _ _
          (arrAngle_injOn (G.prefixEdges m hm) hARR hp hr0 hr))) =
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
          (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr')) := by
  unfold vertexRotationAtRadius
  refine rotationOfOrder_permCongr _ _ _ ?_
  intro a b
  have ha :
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) a) =
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r a := by
    rcases a with ⟨⟨i, bi⟩, hai⟩
    simpa [endAngleKey, incident_ends_prefix_step_unchanged_equiv,
      prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges] using
      (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
        (e := ⟨i, bi⟩) hai hr0 hr hr').symm
  have hb :
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) b) =
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r b := by
    rcases b with ⟨⟨i, bi⟩, hbi⟩
    simpa [endAngleKey, incident_ends_prefix_step_unchanged_equiv,
      prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges] using
      (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
        (e := ⟨i, bi⟩) hbi hr0 hr hr').symm
  change
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) a) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) b) ↔
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r a <
        endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r b
  rw [ha, hb]

/-- At a vertex untouched by the new last edge, the canonical vertex rotation is
also transported unchanged. -/
theorem vertexRotation_prefix_step_unchanged
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    :
    (incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2).permCongr
      (vertexRotation (G.prefixEdges m hm) hARR hp) =
      vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp := by
  let r : ℝ :=
    min (arrRadius (G.prefixEdges m hm) hARR hp)
      (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
  have hr0 : 0 < r :=
    lt_min (arrRadius_pos (G := G.prefixEdges m hm) hARR hp)
      (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp)
  have hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp := min_le_left _ _
  have hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp := min_le_right _ _
  have htmp := vertexRotationAtRadius_prefix_step_unchanged
    (G := G) m hm hm' hjoin hARR hARR' hp hp1 hp2
    (r := r) hr0 hr hr'
  have hold :
      vertexRotationAtRadius (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r
        (endAngleKey_injective (G.prefixEdges m hm) p _ _
          (arrAngle_injOn (G.prefixEdges m hm) hARR hp hr0 hr)) =
      vertexRotation (G.prefixEdges m hm) hARR hp :=
    rotation_wellDefined (G := G.prefixEdges m hm) hARR hp hr0 hr
  have hnew :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
          (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr')) =
      vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp :=
    rotation_wellDefined (G := G.prefixEdges (m + 1) hm') hARR' hp hr0 hr'
  simpa [hold, hnew] using htmp

/-- If the new last edge introduces a fresh leaf endpoint `p`, then that
successor prefix endpoint has at most one incident end. This is the local
cardinality fact needed to make the leaf vertex rotation trivial. -/
theorem incidentEnds_prefix_step_endpoint_card_le_one_of_new_leaf
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
  (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hprev : ∀ e : Fin m × Bool, e ∉ incidentEnds (G.prefixEdges m hm) p) :
    Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) ≤ 1 := by
  classical
  refine Fintype.card_le_one_iff_subsingleton.mpr ⟨?_⟩
  intro a c
  have ha : a = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    rcases a with ⟨⟨i, bi⟩, hai⟩
    by_cases hlast : i = Fin.last m
    · subst hlast
      cases b
      · cases bi
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p := by
            simpa [incidentEnds] using hai
          exact hne hEq
      · cases bi
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p := by
            simpa [incidentEnds] using hai
          exact hne hEq
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
    · have hsucc : (Fin.castSucc (i.castPred hlast), bi) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
          simpa [Fin.castSucc_castPred] using hai
      have hsrc : (i.castPred hlast, bi) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨i.castPred hlast, bi⟩)).mp hsucc
      exact False.elim ((hprev ⟨i.castPred hlast, bi⟩) hsrc)
  have hc' : c = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    rcases c with ⟨⟨j, bj⟩, hc⟩
    by_cases hlast : j = Fin.last m
    · subst hlast
      cases b
      · cases bj
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p := by
            simpa [incidentEnds] using hc
          exact hne hEq
      · cases bj
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p := by
            simpa [incidentEnds] using hc
          exact hne hEq
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
    · have hsucc : (Fin.castSucc (j.castPred hlast), bj) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
          simpa [Fin.castSucc_castPred] using hc
      have hsrc : (j.castPred hlast, bj) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨j.castPred hlast, bj⟩)).mp hsucc
      exact False.elim ((hprev ⟨j.castPred hlast, bj⟩) hsrc)
  rw [ha, hc']

/-- If an endpoint of the new last edge already has an incident dart in the
predecessor prefix, then the successor prefix has at least two incident ends at
that endpoint: the carried-over old dart and the new last-edge dart. -/
theorem two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hold : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p) :
    2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) := by
  rcases hold with ⟨eold, heold⟩
  let oldEnd : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    ⟨(eold.1.castSucc, eold.2),
      (mem_incidentEnds_prefixEdges_castSucc_iff
        (G := G) (m := m) (hm := hm) (hm' := hm') (p := p) (e := eold)).mpr heold⟩
  let newEnd : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew
  have hne : oldEnd ≠ newEnd := by
    intro h
    have hval : (eold.1.castSucc, eold.2) = (Fin.last m, b) :=
      congrArg Subtype.val h
    exact Fin.castSucc_ne_last eold.1 (congrArg Prod.fst hval)
  have hlt : 1 < Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    (Fintype.one_lt_card_iff).mpr ⟨oldEnd, newEnd, hne⟩
  omega


end CrossingLemma
