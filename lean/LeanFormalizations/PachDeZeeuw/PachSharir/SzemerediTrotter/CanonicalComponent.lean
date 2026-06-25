/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Foundations
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.RotationRegular
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.PrefixSplice

/-!
# Szemerédi–Trotter — Canonical component planarity (shard 4 of 5)

The split-pool relabeling proof for the prefix-permuted component drawing and
the canonical-component residual-map planarity statements derived from it.  This
shard carries the single open `sorry`
(`straightLineCanonicalComponentResidualMapPlanarityOfARR`).  Imports
`Foundations`, `RotationRegular`, and `PrefixSplice` (linear chain).
-/

set_option linter.style.longLine false

namespace PachSharir.SzemerediTrotter

open scoped Classical
open CrossingLemma


private lemma stComponentDrawing_prefixPermute_current_splitPool_eq_of_choose
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)))
    (hARR' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')))
    (hARR'' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).facePerm.SameCycle
        s₁ s₂)
    (_hvertex :
      (prefixStepDartEquiv m).permCongr
        (CombinatorialMap.EdgeInsertion.insertedEdgeMap
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂).vertexPerm =
        (residualMap
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) hARR').vertexPerm)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 = p₁)
    (hpnew₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 = p₂)
    (hpother₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 ≠ p₁)
    (hpother₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 ≠ p₂)
    (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V)
    (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V)
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁)
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)
    (hchoose :
      let c₁ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
            (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
      let c₂ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
            (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    ∀ (c₁ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁))
      (c₂ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)),
      c₁.1 ≠ c₂.1 →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₁
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₁ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₁
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' false hpnew₁ →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₂
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₂ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₂
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' true hpnew₂ →
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)) := by
  intro c₁ c₂ _hc hpred₁ hpred₂
  let c₁₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
        (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
  let c₂₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
        (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
  have hc₁ :
      c₁ = c₁₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ ?_ hold₁
      (stMultigraph_localRadius_pos P L p₁) le_rfl hpred₁
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₁
  have hc₂ :
      c₂ = c₂₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ ?_ hold₂
      (stMultigraph_localRadius_pos P L p₂) le_rfl hpred₂
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₂
  simpa [c₁₀, c₂₀, hc₁, hc₂] using hchoose

private theorem
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_choose_sideLabels
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {a : ℕ}
    (T :
      SimpleGraph
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex)
    [DecidableEq
      (residualMap (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex]
    (hTsub :
      T ≤
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).faceGraph)
    {l :
      List
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ (stComponentDrawing P L S E hE C).numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)
          (CombinatorialMap.faceEdgeOfLeafOrderReverse
            (residualMap (stComponentDrawing P L S E hE C)
              (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm'' :
      (a + i.1 + 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
        hARR).facePerm.SameCycle s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (CombinatorialMap.EdgeInsertion.insertedEdgeMap
          (residualMap
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
            hARR)
          s₁ s₂).vertexPerm =
        (residualMap
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm')
          hARR').vertexPerm)
    (hcoverage :
      ∀ p : ↥(stComponentDrawing P L S E hE C).V,
        ∃ e : Fin (a + i.1 + 1) × Bool,
          e ∈ incidentEnds
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm')
            (p : ℝ × ℝ))
    (sideLabel :
      Fin (stComponentDrawing P L S E hE C).numEdges × Bool →
        ({f :
          (residualMap
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
            hARR).Face //
          f ≠
            (residualMap
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
              hARR).Face_mk s₁} ⊕
          Fin 2))
    (label :
      (residualMap (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Face →
        ({f :
          (residualMap
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
            hARR).Face //
          f ≠
            (residualMap
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
              hARR).Face_mk s₁} ⊕
          Fin 2))
    (hsideLabel :
      ∀ d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool,
        sideLabel d =
          label
            ((residualMap (stComponentDrawing P L S E hE C)
              (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Face_mk d))
    (hl_nodup : l.Nodup)
    (hadj :
      ∀ ⦃u v :
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex⦄,
        u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
        v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
        T.Adj u v →
        s(u, v) ≠
          s(l[(Fin.rev i).1 + 1]'(by omega),
            parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
        label
            (CombinatorialMap.dualVertexEquivFace
              (residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
              u) =
          label
            (CombinatorialMap.dualVertexEquivFace
              (residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
              v))
    (hchoose_direct :
      ∀ d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool,
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Edge_mk d =
            (CombinatorialMap.faceEdgeOfLeafOrderReverse
              (residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
              T hTsub parent hparent j) →
        ∀ {p₁ p₂ : ℝ × ℝ}
          (hpnew₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 = p₁)
          (hpnew₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 = p₂)
          (hpother₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 ≠ p₁)
          (hpother₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 ≠ p₂),
          p₁ = dartAnchor (stComponentDrawing P L S E hE C) d ∧
            p₂ =
              dartAnchor (stComponentDrawing P L S E hE C)
                ((residualMap (stComponentDrawing P L S E hE C)
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) →
          (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V) →
          (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V) →
          (hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₁) →
          (hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₂) →
          let c₁ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
                (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
          let c₂ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
                (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
          CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
            sideLabel d ∧
            CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
            sideLabel
              ((residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d))
    (hchoose_swapped :
      ∀ d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool,
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Edge_mk d =
            (CombinatorialMap.faceEdgeOfLeafOrderReverse
              (residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
              T hTsub parent hparent j) →
        ∀ {p₁ p₂ : ℝ × ℝ}
          (hpnew₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 = p₁)
          (hpnew₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 = p₂)
          (hpother₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 ≠ p₁)
          (hpother₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 ≠ p₂),
          p₁ =
              dartAnchor (stComponentDrawing P L S E hE C)
                ((residualMap (stComponentDrawing P L S E hE C)
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) ∧
            p₂ = dartAnchor (stComponentDrawing P L S E hE C) d →
          (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V) →
          (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V) →
          (hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₁) →
          (hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₂) →
          let c₁ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
                (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
          let c₂ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
                (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
          CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
            sideLabel
              ((residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) ∧
            CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
            sideLabel d) :
    ResidualMapPrefixStepInsertion
      (G := (stComponentDrawing P L S E hE C).permuteEdges π)
      (a + i.1 + 1) hm' hm'' hARR' hARR'' := by
  let G := stComponentDrawing P L S E hE C
  let G₀ := stMultigraph P L
  let hEc :=
    edgeSetComponentEdgeSet_subset_edgeSetOn G₀ hE (stMultigraph_arcsJoinEndpoints P L) C
  let hARRG := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  have hjoin : G.ArcsJoinEndpoints := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_arcsJoinEndpoints (G := G₀) (hE := hEc)
        (stMultigraph_arcsJoinEndpoints P L)
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_sector_sideLabels
      π hjoin hARRG T hTsub parent hparent hblock hπcotree i j hprefix
      hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex hcoverage
      sideLabel label hsideLabel hl_nodup hadj
      (by
        intro d hd p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        have hp₁G : p₁ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₁
        have hp₂G : p₂ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₂
        have hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁ := by
          simpa [G] using hcoverage ⟨p₁, hp₁G⟩
        have hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂ := by
          simpa [G] using hcoverage ⟨p₂, hp₂G⟩
        exact
          stComponentDrawing_prefixPermute_sector_sideLabels_direct_of_choose
            P L hL hS (hE := hE) C π (a + i.1) hm hm' hm'' hARR hARR' hARR''
            s₁ s₂ hs hsame hvertex d hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁G hp₂G
            sideLabel hold₁ hold₂
            (hchoose_direct d hd hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect
              hp₁G hp₂G hold₁ hold₂)
            c₁ c₂ hc hpred₁ hpred₂)
      (by
        intro d hd p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        have hp₁G : p₁ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₁
        have hp₂G : p₂ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₂
        have hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁ := by
          simpa [G] using hcoverage ⟨p₁, hp₁G⟩
        have hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂ := by
          simpa [G] using hcoverage ⟨p₂, hp₂G⟩
        exact
          stComponentDrawing_prefixPermute_sector_sideLabels_swapped_of_choose
            P L hL hS (hE := hE) C π (a + i.1) hm hm' hm'' hARR hARR' hARR''
            s₁ s₂ hs hsame hvertex d hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁G hp₂G
            sideLabel hold₁ hold₂
            (hchoose_swapped d hd hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped
              hp₁G hp₂G hold₁ hold₂)
            c₁ c₂ hc hpred₁ hpred₂)

private theorem
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_choose_splitPool_eq
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    {a : ℕ}
    (Sₑ :
      Set
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Edge)
    (T :
      SimpleGraph
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex)
    [DecidableEq
      (residualMap (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex]
    (hTsub :
      T ≤
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).faceGraphOnEdgeSet Sₑ)
    {l :
      List
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (stComponentDrawing P L S E hE C)
        (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ (stComponentDrawing P L S E hE C).numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)
          (CombinatorialMap.faceEdgeOfLeafOrderOnEdgeSetReverse
            (residualMap (stComponentDrawing P L S E hE C)
              (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
            Sₑ T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm'' :
      (a + i.1 + 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
        hARR).facePerm.SameCycle s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (CombinatorialMap.EdgeInsertion.insertedEdgeMap
          (residualMap
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
            hARR)
          s₁ s₂).vertexPerm =
        (residualMap
          (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm')
          hARR').vertexPerm)
    (hcoverage :
      ∀ p : ↥(stComponentDrawing P L S E hE C).V,
        ∃ e : Fin (a + i.1 + 1) × Bool,
          e ∈ incidentEnds
            (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1 + 1) hm')
            (p : ℝ × ℝ))
    (hchoose :
      ∀ d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool,
        (residualMap (stComponentDrawing P L S E hE C)
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).Edge_mk d =
            (CombinatorialMap.faceEdgeOfLeafOrderOnEdgeSetReverse
              (residualMap (stComponentDrawing P L S E hE C)
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
              Sₑ T hTsub parent hparent j) →
        ∀ {p₁ p₂ : ℝ × ℝ}
          (hpnew₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 = p₁)
          (hpnew₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 = p₂)
          (hpother₁ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).2 ≠ p₁)
          (hpother₂ :
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((a + i.1 + 1) + 1) hm'').endpoints
                (Fin.last (a + i.1 + 1))).1 ≠ p₂),
          ((p₁ = dartAnchor (stComponentDrawing P L S E hE C) d ∧
              p₂ =
                dartAnchor (stComponentDrawing P L S E hE C)
                  ((residualMap (stComponentDrawing P L S E hE C)
                    (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d)) ∨
            (p₁ =
                dartAnchor (stComponentDrawing P L S E hE C)
                  ((residualMap (stComponentDrawing P L S E hE C)
                    (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) ∧
              p₂ = dartAnchor (stComponentDrawing P L S E hE C) d)) →
          (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V) →
          (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V) →
          (hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₁) →
          (hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds
              (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                (a + i.1 + 1) hm')
              p₂) →
          let c₁ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
                (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
          let c₂ :=
            Classical.choose
              (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
                P L hL (hE := hE) C π (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
                (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
          CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
            CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
              (residualMap
                (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                hARR)
              s₁ s₂ hs hsame
              ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
                (residualMap
                  (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (a + i.1) hm)
                  hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData
        (G := (stComponentDrawing P L S E hE C).permuteEdges π)
        (a + i.1 + 1) hm' hm'' hARR' hARR'') := by
  let G := stComponentDrawing P L S E hE C
  let G₀ := stMultigraph P L
  let hEc :=
    edgeSetComponentEdgeSet_subset_edgeSetOn G₀ hE (stMultigraph_arcsJoinEndpoints P L) C
  let hARRG := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  have hjoin : G.ArcsJoinEndpoints := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_arcsJoinEndpoints (G := G₀) (hE := hEc)
        (stMultigraph_arcsJoinEndpoints P L)
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG Sₑ T hTsub parent hparent hblock hπcotree i j hprefix
      hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex hcoverage
      (by
        intro d hd p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        have hp₁G : p₁ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₁
        have hp₂G : p₂ ∈ G.V := by
          simpa [G, DrawnMultigraph.permuteEdges] using hp₂
        have hold₁ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁ := by
          simpa [G] using hcoverage ⟨p₁, hp₁G⟩
        have hold₂ : ∃ e : Fin (a + i.1 + 1) × Bool,
            e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂ := by
          simpa [G] using hcoverage ⟨p₂, hp₂G⟩
        exact
          stComponentDrawing_prefixPermute_current_splitPool_eq_of_choose
            P L hL hS (hE := hE) C π (a + i.1) hm hm' hm'' hARR hARR' hARR''
            s₁ s₂ hs hsame hvertex hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁G hp₂G
            hold₁ hold₂
            (hchoose d hd hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁G hp₂G hold₁ hold₂)
            c₁ c₂ hc hpred₁ hpred₂)

private theorem
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepInsertion_leaf_of_treeEdgeOfLeafOrder
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (_hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (T : SimpleGraph ↥(stComponentDrawing P L S E hE C).V)
    (hTsub :
      T ≤
        (stComponentDrawing P L S E hE C).vertexGraph
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L)))
    {l : List ↥(stComponentDrawing P L S E hE C).V}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      ↥(stComponentDrawing P L S E hE C).V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ (stComponentDrawing P L S E hE C).numEdges}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        (stComponentDrawing P L S E hE C).treeEdgeOfLeafOrder
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L))
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_multiplicity_le (G := G) (hE := hEc)
                (stMultigraph_multiplicity_le_one P L hL))
          T hTsub parent hparent j)
    (i : Fin (l.length - 1)) (hi : 1 ≤ i.1)
    (hm : i.1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : i.1 + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges i.1 hm))
    (hARR' : ArcsRotationRegular
      (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (i.1 + 1) hm')) :
    ResidualMapPrefixStepInsertion
      (G := (stComponentDrawing P L S E hE C).permuteEdges π)
      i.1 hm hm' hARR hARR' := by
  let G := stComponentDrawing P L S E hE C
  let G₀ := stMultigraph P L
  let hEc :=
    edgeSetComponentEdgeSet_subset_edgeSetOn G₀ hE (stMultigraph_arcsJoinEndpoints P L) C
  have hjoin : G.ArcsJoinEndpoints := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_arcsJoinEndpoints (G := G₀) (hE := hEc)
        (stMultigraph_arcsJoinEndpoints P L)
  have hmult : ∀ p q, G.multiplicity p q ≤ 1 := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_multiplicity_le (G := G₀) (hE := hEc)
        (stMultigraph_multiplicity_le_one P L hL)
  exact
    G.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
      hjoin hmult T hTsub hl_nodup parent hparent hπ i hi hm hm' hARR hARR'

private theorem
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_treePrefix_next
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (T : SimpleGraph ↥(stComponentDrawing P L S E hE C).V)
    (hTsub :
      T ≤
        (stComponentDrawing P L S E hE C).vertexGraph
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L)))
    {l : List ↥(stComponentDrawing P L S E hE C).V}
    (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥(stComponentDrawing P L S E hE C).V)
    (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      ↥(stComponentDrawing P L S E hE C).V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ (stComponentDrawing P L S E hE C).numEdges}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        (stComponentDrawing P L S E hE C).treeEdgeOfLeafOrder
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L))
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_multiplicity_le (G := G) (hE := hEc)
                (stMultigraph_multiplicity_le_one P L hL))
          T hTsub parent hparent j)
    (hm : l.length - 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData
        (G := (stComponentDrawing P L S E hE C).permuteEdges π)
        (l.length - 1) hm hm'
        (prefixEdges_arcsRotationRegular
          ((stComponentDrawing P L S E hE C).permuteEdges π) (l.length - 1) hm
          (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)))
        (prefixEdges_arcsRotationRegular
          ((stComponentDrawing P L S E hE C).permuteEdges π) ((l.length - 1) + 1) hm'
          (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)))) := by
  let G := stComponentDrawing P L S E hE C
  let G₀ := stMultigraph P L
  let hEc :=
    edgeSetComponentEdgeSet_subset_edgeSetOn G₀ hE (stMultigraph_arcsJoinEndpoints P L) C
  have hjoin : G.ArcsJoinEndpoints := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_arcsJoinEndpoints (G := G₀) (hE := hEc)
        (stMultigraph_arcsJoinEndpoints P L)
  have hmult : ∀ p q, G.multiplicity p q ≤ 1 := by
    simpa [G, stComponentDrawing, G₀, hEc] using
      edgeSetDrawing_multiplicity_le (G := G₀) (hE := hEc)
        (stMultigraph_multiplicity_le_one P L hL)
  let hARRprefix : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm) :=
    fun m hm =>
      prefixEdges_arcsRotationRegular (G.permuteEdges π) m hm
        (permuteEdges_arrRotationRegular G π
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_permuted_treePrefix_next
      hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hm' hARRprefix

private theorem
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepInsertion_sameFace_of_treePrefix_next
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (T : SimpleGraph ↥(stComponentDrawing P L S E hE C).V)
    (hTsub :
      T ≤
        (stComponentDrawing P L S E hE C).vertexGraph
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L)))
    {l : List ↥(stComponentDrawing P L S E hE C).V}
    (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥(stComponentDrawing P L S E hE C).V)
    (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      ↥(stComponentDrawing P L S E hE C).V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ (stComponentDrawing P L S E hE C).numEdges}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        (stComponentDrawing P L S E hE C).treeEdgeOfLeafOrder
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_arcsJoinEndpoints (G := G) (hE := hEc)
                (stMultigraph_arcsJoinEndpoints P L))
          (by
            let G := stMultigraph P L
            let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
              (stMultigraph_arcsJoinEndpoints P L) C
            simpa [stComponentDrawing, G, hEc] using
              edgeSetDrawing_multiplicity_le (G := G) (hE := hEc)
                (stMultigraph_multiplicity_le_one P L hL))
          T hTsub parent hparent j)
    (hm : l.length - 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges) :
    ResidualMapPrefixStepInsertion
      (G := (stComponentDrawing P L S E hE C).permuteEdges π)
      (l.length - 1) hm hm'
      (prefixEdges_arcsRotationRegular
        ((stComponentDrawing P L S E hE C).permuteEdges π) (l.length - 1) hm
        (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)))
      (prefixEdges_arcsRotationRegular
        ((stComponentDrawing P L S E hE C).permuteEdges π) ((l.length - 1) + 1) hm'
        (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
          (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) := by
  obtain ⟨hdata⟩ :=
    stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_treePrefix_next
      P L hL hS (hE := hE) C π T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hm'
  exact hdata.toInsertion

/-- **Straight-line canonical-component residual-map planarity, with ARR already
inherited from the straight-line drawing.**

This is the exact remaining genus-zero part of Pach--Tóth,
*A crossing lemma for multigraphs*, Lemma 2.1, specialized to the
Szemerédi--Trotter incidence graph: after the one-edge-per-crossing deletion,
each canonical connected component of the surviving straight-line drawing has
planar residual map for its inherited local rotation system. -/
def StraightLineCanonicalComponentResidualMapPlanarityOfARR : Prop :=
  ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) →
    ∀ (S : Finset (ℝ × ℝ)), (hS : S ⊆ (stMultigraph P L).V) →
      ∀ (E : Finset (Fin (stMultigraph P L).numEdges)),
        ∀ hE : E ⊆ edgeSetOn (stMultigraph P L) S,
          NoCrossingPairsInEdgeSet (stMultigraph P L) E →
            ∀ C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent,
              3 ≤ (edgeSetComponentVertexSet (stMultigraph P L) C).card →
                (residualMap (stComponentDrawing P L S E hE C)
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).IsPlanar

/-- The straight-line canonical-component residual-map endpoint gives the
componentwise genus-zero planarization required by the ACNS/Leighton deletion
step. This is the ST-specific form of Pach--Tóth Lemma 2.1: the component is
already connected by construction, ARR is inherited from straight segments, and
the only hypothesis is residual-map genus zero. -/
theorem straightLineCrossingFreeComponentwisePlanarization_of_canonical_component_residualMapPlanarityOfARR
    (hres : StraightLineCanonicalComponentResidualMapPlanarityOfARR) :
    StraightLineCrossingFreeComponentwisePlanarization := by
  intro P L hL S hS E hE hfree
  let G := stMultigraph P L
  refine ⟨(edgeSetSimpleGraph G S E).ConnectedComponent,
    (show Fintype (edgeSetSimpleGraph G S E).ConnectedComponent from
      SetLike.instFintype),
    edgeSetComponentVertexSet G, edgeSetComponentEdgeSet G hE, ?_, ?_, ?_, ?_⟩
  · exact edgeSetComponentEdgeSet_card_sum G hE
  · exact (edgeSetComponentVertexSet_card_sum (G := G) (S := S) (E := E)).le
  · intro C
    exact edgeSetComponentVertexSet_subset G C
  · intro C
    let hEc := edgeSetComponentEdgeSet_subset_edgeSetOn G hE
      (stMultigraph_arcsJoinEndpoints P L) C
    refine ⟨hEc, ?_⟩
    intro hv
    let D := stComponentDrawing P L S E hE C
    let hDarr := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
    have hDmult : ∀ p q, D.multiplicity p q ≤ 1 := by
      simpa [D, stComponentDrawing, G, hEc] using edgeSetDrawing_multiplicity_le
        (G := G) (hE := hEc) (stMultigraph_multiplicity_le_one P L hL)
    have hDjoin : D.ArcsJoinEndpoints := by
      simpa [D, stComponentDrawing, G, hEc] using edgeSetDrawing_arcsJoinEndpoints
        (G := G) (hE := hEc) (stMultigraph_arcsJoinEndpoints P L)
    have hDconn : D.GraphConnected := by
      simpa [D, stComponentDrawing, G, hEc] using edgeSetComponentDrawing_graphConnected
        (G := G) hE (stMultigraph_arcsJoinEndpoints P L) C
    have hDverts : 3 ≤ D.V.card := by
      simpa [D, stComponentDrawing, edgeSetDrawing, G] using hv
    have hDplanar : (residualMap D hDarr).IsPlanar := by
      simpa [D, hDarr] using hres P L hL S hS E hE hfree C hv
    have hplD : HasGenusZeroSimplePlanarization (abstractize D) := by
      exact has_genus_zero_simple_planarization_of_residual_map D hDarr hDjoin
        hDmult hDconn hDverts hDplanar
    simpa [D, stComponentDrawing, G, hEc] using
      abstractizeEdgeSet_has_genus_zero_simple_planarization_of_edgeSetDrawing
        (G := G) hplD

/-- **Straight-line canonical-component residual-map planarity statement.**

This is the genus-zero bridge for the Szemerédi--Trotter incidence
construction: the component-level straight-line residual map is organized to
follow the literature's ordered insertion proof, and the later corollary
reuses it to obtain planar residual maps for the canonical connected
components of crossing-free survivors. -/
theorem straightLineCanonicalComponentResidualMapPlanarityOfARR :
    StraightLineCanonicalComponentResidualMapPlanarityOfARR := by
  intro P L hL S hS E hE hfree C hv
  let G := stComponentDrawing P L S E hE C
  let hARRG := stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C
  have hjoin : G.ArcsJoinEndpoints := by
    simpa [G, stComponentDrawing] using
      edgeSetDrawing_arcsJoinEndpoints
        (G := stMultigraph P L)
        (hE := edgeSetComponentEdgeSet_subset_edgeSetOn (stMultigraph P L) hE
          (stMultigraph_arcsJoinEndpoints P L) C)
        (stMultigraph_arcsJoinEndpoints P L)
  have hmult : ∀ p q, G.multiplicity p q ≤ 1 := by
    simpa [G, stComponentDrawing] using
      edgeSetDrawing_multiplicity_le
        (G := stMultigraph P L)
        (hE := edgeSetComponentEdgeSet_subset_edgeSetOn (stMultigraph P L) hE
          (stMultigraph_arcsJoinEndpoints P L) C)
        (stMultigraph_multiplicity_le_one P L hL)
  have hconn : G.GraphConnected := by
    simpa [G, stComponentDrawing] using
      edgeSetComponentDrawing_graphConnected
        (G := stMultigraph P L) hE (stMultigraph_arcsJoinEndpoints P L) C
  have hV : 3 ≤ G.V.card := by
    simpa [G, stComponentDrawing, edgeSetDrawing] using hv
  obtain ⟨Tvertex, hTvertex_sub, hTvertex_tree, lvertex, hlvertex_nodup,
    hlvertex_len, parentVertex, hparentVertex, Tface, hTface_sub, hTface_tree,
    lface, hlface_nodup, hlface_len, parentFace, hparentFace, hblock, π, hπtree,
    hπrest⟩ :=
    G.exists_treeCotreePositionPermutation_of_graphConnected
      hjoin hmult hARRG hconn hV
  have hlvertex_two : 2 ≤ lvertex.length := by
    rw [hlvertex_len]
    have hV' : 3 ≤ Fintype.card ↥G.V := by
      simpa using hV
    omega
  have hmtree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges := by
    have hblock' : lvertex.length - 1 ≤ G.numEdges := by
      exact le_trans (Nat.le_add_right _ _) hblock
    simpa [G, DrawnMultigraph.permuteEdges] using hblock'
  have hktree0 : lvertex.length - 1 ≤ G.numEdges := by omega
  have hπtree_simple : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree0 i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub parentVertex hparentVertex i := by
    intro i
    have hcast : (Fin.castLE hktree0 i : Fin G.numEdges)
        = Fin.castLE hblock (Fin.castAdd (lface.length - 1) i) := by
      apply Fin.ext; simp
    rw [hcast]; exact hπtree i
  let hARRprefix : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm) :=
    fun m hm =>
      prefixEdges_arcsRotationRegular (G.permuteEdges π) m hm
        (permuteEdges_arrRotationRegular G π hARRG)
  let R₀ : Set (ℝ × ℝ) := Set.univ
  have hR₀ : IsOpen R₀ := by
    simp [R₀]
  let start : ℕ := lvertex.length - 1
  have hstartG : start ≤ (G.permuteEdges π).numEdges := by
    simpa [start, G, DrawnMultigraph.permuteEdges] using hmtree
  -- Target 1: build dr and hstepCrosscut inductively via poolRegion/splitClass.
  -- The induction uses the bridge (regionSeparates_prefix_of_crosscut) at each
  -- level to obtain hsame from hregion.  The two hard obligations are:
  --   (A) hregion — cotree co-faciality: Face_mk c₁ = Face_mk c₂ at level m
  --   (B) exists_twoSidedPartition_of_straightArc instantiation for the straight
  --       graph edge
  -- Both are isolated as sorries inside this block.
  have h_exists_target1 : ∃ (dr : ∀ (m : ℕ), m ≤ (G.permuteEdges π).numEdges →
        (Fin m × Bool) → Set (ℝ × ℝ))
      (hstepCrosscut : ∀ (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges), start ≤ m →
        PrefixStepCrosscutData (G.permuteEdges π) m (Nat.le_of_succ_le hm') hm'
          (hARRprefix m (Nat.le_of_succ_le hm')) (hARRprefix (m + 1) hm')
          (dr m (Nat.le_of_succ_le hm')) (dr (m + 1) hm')),
      True := by
    let G' := G.permuteEdges π
    -- Target 1 (collar item #14 / Obligation B gluing): construct the region
    -- family `dr` over every prefix level together with one
    -- `PrefixStepCrosscutData` per step `start ≤ m < N`.
    --
    -- The mutually-recursive bundle (sub-obligation B0) is now DISCHARGED by the
    -- sorry-free harness `CrossingLemma.exists_dr_hstepCrosscut`
    -- (EdmondsSameRegion.lean): it builds `dr` by a simultaneous recursion that
    -- maintains region-separation and face-constancy at every level, consuming a
    -- single per-step producer `PerStepCrosscutInput`.  All of the assembly between
    -- that producer and the recursion is sorry-free and axiom-clean
    -- (`mkPrefixStepCrosscutData`, `prefixStepSameRegion_poolRegion_injective`,
    -- `stepRegionFamily_hconst`, `nonempty_prefixStepCrosscut_of_data`), and the B2
    -- region equality is the sorry-free transport `CrossingLemma.prefixStepSameRegion`.
    --
    -- What remains is exactly the per-step producer `hgeo` — *one* cotree-step
    -- bundle from `dr m` + its two invariants.  Its genuine open content (true with
    -- the new-edge endpoint data in scope here):
    --   (B1) the extractor's `hsplit` identity — the entered angular sectors at the
    --        two endpoints land on the same split side (the *rotation-chosen*
    --        endpoint corners, NOT the bundle's predecessor corners, which lie on
    --        opposite sides);
    --        feeds `exists_residualMapPrefixStepSameFaceData_…`
    --        (ResidualMapProperties.lean:5785, lines 5813-5867); and
    --   (B2) the existence of the preconnected complement witness `S` and sector
    --        points realising the two corner regions, feeding `prefixStepSameRegion`,
    --        plus the global-side distinctness `hWne`/`hWold` from
    --        `exists_twoSidedPartition_prefixStep`.
    --
    -- `hgeo` is strictly smaller than the former monolithic `sorry`: the recursion
    -- (B0) is gone, the region transport (B2 equality) and injectivity are
    -- discharged, and only the extractor/partition geometry remains.  See
    -- docs/crossing-lemma-A1-edmonds-sameregion.md.
    have hcard1' : ∀ h : start ≤ G'.numEdges,
        Fintype.card (residualMap (G'.prefixEdges start h)
          (hARRprefix start h)).Face = 1 := by
      intro h
      apply G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree_simple h hARRprefix
    have hgeo : CrossingLemma.PerStepCrosscutInput G' start hARRprefix := by
      sorry
    exact CrossingLemma.exists_dr_hstepCrosscut G' start hARRprefix hstartG hcard1' hgeo
  obtain ⟨dr, hstepCrosscut, _⟩ := h_exists_target1
  let G' := G.permuteEdges π
  have hcard1 : ∀ h : start ≤ (G.permuteEdges π).numEdges,
      Fintype.card (residualMap ((G.permuteEdges π).prefixEdges start h)
        (hARRprefix start h)).Face = 1 := by
    intro h
    apply G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
      hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
      parentVertex hparentVertex hπtree_simple h hARRprefix
  have hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges), 1 ≤ m →
      ResidualMapPrefixStepInsertion (G := G.permuteEdges π) m
        (Nat.le_of_succ_le hm') hm' (hARRprefix m (Nat.le_of_succ_le hm'))
        (hARRprefix (m + 1) hm') := by
    intro m hm' hmpos
    have hm : m ≤ (G.permuteEdges π).numEdges := Nat.le_of_succ_le hm'
    have hARRm : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm) :=
      hARRprefix m hm
    have hARRm' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm') :=
      hARRprefix (m + 1) hm'
    by_cases htree : m + 1 ≤ lvertex.length - 1
    · have hmle : m < lvertex.length - 1 := Nat.lt_of_succ_le htree
      have hi : 1 ≤ m := hmpos
      let i : Fin (lvertex.length - 1) := ⟨m, by
        have : m < lvertex.length - 1 := hmle
        omega⟩
      have hstep' :=
        G.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
          (hjoin := hjoin) (hmult := hmult) (T := Tvertex) (hTsub := hTvertex_sub)
          (hl_nodup := hlvertex_nodup) (parent := parentVertex) (hparent := hparentVertex)
          (hk := by
            have hktree' : lvertex.length - 1 ≤ G.numEdges := by
              omega
            simpa [G, DrawnMultigraph.permuteEdges] using hktree')
          (hπ := hπtree) i hi hm hm' hARRm hARRm'
      simpa [G, hARRprefix, hARRm, hARRm'] using hstep'
    · have htree_or_later : m = lvertex.length - 1 ∨ lvertex.length - 1 < m := by
        omega
      rcases htree_or_later with rfl | hgt
      · exact
          stComponentDrawing_prefixPermute_exists_residualMapPrefixStepInsertion_sameFace_of_treePrefix_next
            P L hL hS (hE := hE) C π Tvertex hTvertex_sub hlvertex_nodup hlvertex_len
            hlvertex_two parentVertex hparentVertex (hk := hmtree) (hπ := hπtree)
            hm hm'
      · -- Cotree step `lvertex.length - 1 < m`.
        classical
        -- The combinatorial face-count induction (proved in ResidualMapProperties)
        -- gives `hcount` without planarity, provided we have per-step co-faciality
        -- witnesses for all cotree steps.  Those witnesses are the ST:4713 residual.
        -- Pending ST:4713, we use a constructive case split: if `m` falls within the
        -- cotree block (positions `lvertex.length-1` to `(lvertex.length-1)+(lface.length-1)-1`),
        -- use the OnEdgeSet cotree step lemma; otherwise `m` is beyond the block and
        -- the generic endpoint-incident lemma supplies the step.
        have hNE : (G.permuteEdges π).numEdges = G.numEdges := by
          simp [DrawnMultigraph.permuteEdges]
        have hmlt : m < G.numEdges := by
          have hm'2 := hm'; rw [hNE] at hm'2; omega
        have hktree0 : lvertex.length - 1 ≤ G.numEdges := by omega
        have hπtree' : ∀ i : Fin (lvertex.length - 1),
            π (Fin.castLE hktree0 i) =
              G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub parentVertex hparentVertex i := by
          intro i
          have hcast : (Fin.castLE hktree0 i : Fin G.numEdges)
              = Fin.castLE hblock (Fin.castAdd (lface.length - 1) i) := by
            apply Fin.ext; simp
          rw [hcast]; exact hπtree i
        by_cases hink : m - (lvertex.length - 1) < lface.length - 1
        · -- m is within the cotree block: use the bridge to get SameCycle from hstepCrosscut.
          have hstart_m : start ≤ m := by
            dsimp [start]
            omega
          have hs_data := hstepCrosscut m hm' hstart_m
          have hsame_cotree :
              (residualMap (G'.prefixEdges m hm) (hARRprefix m hm)).facePerm.SameCycle
                hs_data.c₁ hs_data.c₂ :=
            regionSeparates_prefix_of_crosscut G' start hARRprefix dr hcard1 hstepCrosscut
              m hstart_m hm hs_data.c₁ hs_data.c₂ hs_data.hregion
          exact ResidualMapPrefixStepInsertion.sameFace hs_data.c₁ hs_data.c₂
            hs_data.hc hsame_cotree hs_data.hvertex
        · -- m beyond the cotree block: same bridge approach.
          have hstart_m : start ≤ m := by
            dsimp [start]
            omega
          have hs_data := hstepCrosscut m hm' hstart_m
          have hsame_beyond :
              (residualMap (G'.prefixEdges m hm) (hARRprefix m hm)).facePerm.SameCycle
                hs_data.c₁ hs_data.c₂ :=
            regionSeparates_prefix_of_crosscut G' start hARRprefix dr hcard1 hstepCrosscut
              m hstart_m hm hs_data.c₁ hs_data.c₂ hs_data.hregion
          exact ResidualMapPrefixStepInsertion.sameFace hs_data.c₁ hs_data.c₂
            hs_data.hc hsame_beyond hs_data.hvertex
  have hplanarπ : ∃ hARRπ : ArcsRotationRegular (G.permuteEdges π),
      (residualMap (G.permuteEdges π) hARRπ).IsPlanar := by
    exact exists_residualMap_isPlanar_of_prefix_insertions_connected
      (G := G.permuteEdges π) (permuteEdges_arcsJoinEndpoints G π hjoin)
      ((DrawnMultigraph.permuteEdges_graphConnected_iff G π).2 hconn) hV
      hARRprefix hstep
  rcases hplanarπ with ⟨hARRπ, hplanarπ⟩
  have hARRπ_eq : hARRπ = permuteEdges_arrRotationRegular G π hARRG := Subsingleton.elim _ _
  have hplanar : (residualMap G hARRG).IsPlanar := by
    exact (isPlanar_iff_of_iso (residualMapIsoPermuteEdges (G := G) π hjoin hARRG)).2
      (by simpa [hARRπ_eq] using hplanarπ)
  simpa [G, hARRG] using hplanar


end PachSharir.SzemerediTrotter
