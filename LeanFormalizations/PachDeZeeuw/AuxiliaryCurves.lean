/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Pach--de Zeeuw auxiliary curves

This file freezes the auxiliary-curve definitions and the incidence bridge
used by the later Pach--de Zeeuw incidence packet.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.PDZ

open EuclideanGeometry

/-- The bivariate polynomial defining the second curve in a prepared input. -/
private noncomputable def curveWitnessPoly₂ {d : ℕ}
    (X : PreparedBipartiteInput d) : MvPolynomial (Fin 2) ℝ :=
  Classical.choose X.hC₂

private lemma curveWitnessPoly₂_spec {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.C₂ = {x : Point2 | MvPolynomial.eval (fun i => x i) (curveWitnessPoly₂ X) = 0} := by
  dsimp [curveWitnessPoly₂]
  rcases Classical.choose_spec X.hC₂ with ⟨_, _, _, hEq⟩
  simpa using hEq

/-- Encode a pair of planar points as a point of `Point4`. -/
private noncomputable def auxPointOfPair (pq : Point2 × Point2) : Point4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm fun
    | 0 => pq.1 0
    | 1 => pq.1 1
    | 2 => pq.2 0
    | _ => pq.2 1

private lemma auxPointOfPair_fst (pq : Point2 × Point2) :
    auxPointOfPair pq 0 = pq.1 0 := by
  simp [auxPointOfPair]

private lemma auxPointOfPair_snd (pq : Point2 × Point2) :
    auxPointOfPair pq 1 = pq.1 1 := by
  simp [auxPointOfPair]

private lemma auxPointOfPair_third (pq : Point2 × Point2) :
    auxPointOfPair pq 2 = pq.2 0 := by
  simp [auxPointOfPair]

private lemma auxPointOfPair_fourth (pq : Point2 × Point2) :
    auxPointOfPair pq 3 = pq.2 1 := by
  simp [auxPointOfPair]

private lemma auxPointOfPair_injective : Function.Injective auxPointOfPair := by
  intro p q h
  cases p with
  | mk p1 p2 =>
    cases q with
    | mk q1 q2 =>
      have h0 := congrArg (fun z : Point4 => z 0) h
      have h1 := congrArg (fun z : Point4 => z 1) h
      have h2 := congrArg (fun z : Point4 => z 2) h
      have h3 := congrArg (fun z : Point4 => z 3) h
      simp [auxPointOfPair] at h0 h1 h2 h3
      ext i <;> fin_cases i <;> simp [h0, h1, h2, h3]

private noncomputable def auxFirstPair (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 0
    | _ => z 1

private noncomputable def auxSecondPair (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 2
    | _ => z 3

private lemma auxFirstPair_of_auxPointOfPair (pq : Point2 × Point2) :
    auxFirstPair (auxPointOfPair pq) = pq.1 := by
  ext i <;> fin_cases i <;> simp [auxFirstPair, auxPointOfPair]

private lemma auxSecondPair_of_auxPointOfPair (pq : Point2 × Point2) :
    auxSecondPair (auxPointOfPair pq) = pq.2 := by
  ext i <;> fin_cases i <;> simp [auxSecondPair, auxPointOfPair]

/-- The point set for the auxiliary curves, obtained from the `P₂ × P₂` image. -/
noncomputable def auxPointSet {d : ℕ} (X : PreparedBipartiteInput d) :
    Finset Point4 :=
  (X.P₂.product X.P₂).image auxPointOfPair

/--
The auxiliary curve `C_ij` from the paper, written as a subset of `Point4`.

The three defining equations are the two copies of the `C₂` equation and the
equal-distance relation between the target pair and the source pair `i, j`.
-/
noncomputable def auxCurve {d : ℕ} (X : PreparedBipartiteInput d)
    (i j : X.P₁) : Set Point4 :=
  {z : Point4 |
    MvPolynomial.eval (fun k => auxFirstPair z k) (curveWitnessPoly₂ X) = 0 ∧
    MvPolynomial.eval (fun k => auxSecondPair z k) (curveWitnessPoly₂ X) = 0 ∧
    dist (i : Point2) (auxFirstPair z) ^ 2 = dist (j : Point2) (auxSecondPair z) ^ 2}

/-- Incidence set between the auxiliary point set and auxiliary curves. -/
noncomputable def auxIncidences {d : ℕ} (X : PreparedBipartiteInput d) :
    Finset (Point4 × (X.P₁ × X.P₁)) :=
  by
    classical
    exact
      ((auxPointSet X).product (Finset.univ : Finset (X.P₁ × X.P₁))).filter
        (fun p => p.1 ∈ auxCurve X p.2.1 p.2.2)

private lemma auxPointOfPair_mem_auxPointSet {d : ℕ}
    (X : PreparedBipartiteInput d) {p q : Point2}
    (hp : p ∈ X.P₂) (hq : q ∈ X.P₂) :
    auxPointOfPair (p, q) ∈ auxPointSet X := by
  dsimp [auxPointSet]
  refine Finset.mem_image.mpr ?_
  refine ⟨(p, q), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨hp, hq⟩

private lemma auxPointOfPair_mem_auxCurve {d : ℕ}
    (X : PreparedBipartiteInput d) (i j : X.P₁) {p q : Point2}
    (hp : p ∈ X.P₂) (hq : q ∈ X.P₂)
    (hdist : dist (i : Point2) p = dist (j : Point2) q) :
    auxPointOfPair (p, q) ∈ auxCurve X i j := by
  dsimp [auxCurve]
  constructor
  · have hpC₂ : p ∈ X.C₂ := X.hP₂ hp
    rw [curveWitnessPoly₂_spec] at hpC₂
    simpa [auxFirstPair_of_auxPointOfPair] using hpC₂
  · constructor
    · have hqC₂ : q ∈ X.C₂ := X.hP₂ hq
      rw [curveWitnessPoly₂_spec] at hqC₂
      simpa [auxSecondPair_of_auxPointOfPair] using hqC₂
    · have hsq : dist (i : Point2) p ^ 2 = dist (j : Point2) q ^ 2 := by
        exact congrArg (fun t : ℝ => t ^ 2) hdist
      simpa [auxFirstPair_of_auxPointOfPair, auxSecondPair_of_auxPointOfPair] using hsq

private noncomputable def quadrupleToIncidence {d : ℕ}
    (X : PreparedBipartiteInput d)
    (q : {x // x ∈ (X.P₁.product X.P₂).product (X.P₁.product X.P₂)}) :
    Point4 × (X.P₁ × X.P₁) := by
  rcases Finset.mem_product.mp q.2 with ⟨hleft, hright⟩
  rcases Finset.mem_product.mp hleft with ⟨hi, hp⟩
  rcases Finset.mem_product.mp hright with ⟨hj, hq⟩
  exact (auxPointOfPair (q.1.1.2, q.1.2.2), (⟨q.1.1.1, hi⟩, ⟨q.1.2.1, hj⟩))

/-- The incidence/equal-distance bridge between auxiliary incidences and quadruples. -/
def AuxIncidenceBridgeStatement : Prop :=
  ∀ d : ℕ, ∀ X : PreparedBipartiteInput d,
    (equalDistanceQuadruples X).card ≤ (auxIncidences X).card

/-- The auxiliary incidence bridge sends each equal-distance quadruple to an incidence. -/
theorem auxIncidenceBridge : AuxIncidenceBridgeStatement := by
  intro d X
  classical
  let S : Finset ((Point2 × Point2) × (Point2 × Point2)) := equalDistanceQuadruples X
  let f : {x // x ∈ S} → Point4 × (X.P₁ × X.P₁) := fun q =>
    let hquad : q.1 ∈ (X.P₁.product X.P₂).product (X.P₁.product X.P₂) := (Finset.mem_filter.mp q.2).1
    let hleft : q.1.1 ∈ X.P₁.product X.P₂ := (Finset.mem_product.mp hquad).1
    let hright : q.1.2 ∈ X.P₁.product X.P₂ := (Finset.mem_product.mp hquad).2
    let hi : q.1.1.1 ∈ X.P₁ := (Finset.mem_product.mp hleft).1
    let hj : q.1.2.1 ∈ X.P₁ := (Finset.mem_product.mp hright).1
    ⟨auxPointOfPair (q.1.1.2, q.1.2.2), (⟨q.1.1.1, hi⟩, ⟨q.1.2.1, hj⟩)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h
    cases q1 with
    | mk q1 hq1 =>
      cases q2 with
      | mk q2 hq2 =>
        have hpt : auxPointOfPair (q1.1.2, q1.2.2) = auxPointOfPair (q2.1.2, q2.2.2) := by
          have h' := congrArg Prod.fst h
          simpa [f] using h'
        have hidx : (q1.1.1, q1.2.1) = (q2.1.1, q2.2.1) := by
          have h' := congrArg Prod.snd h
          simpa [f] using h'
        have htarget : (q1.1.2, q1.2.2) = (q2.1.2, q2.2.2) := by
          exact auxPointOfPair_injective hpt
        have hleft : q1.1 = q2.1 := by
          have h11 : q1.1.1 = q2.1.1 := by
            simpa using (show q1.1.1 = q2.1.1 ∧ q1.2.1 = q2.2.1 from by simpa using hidx).1
          have h12 : q1.1.2 = q2.1.2 := by
            simpa using (show q1.1.2 = q2.1.2 ∧ q1.2.2 = q2.2.2 from by simpa using htarget).1
          ext i <;> fin_cases i <;> simpa [h11, h12]
        have hright : q1.2 = q2.2 := by
          have h21 : q1.2.1 = q2.2.1 := by
            simpa using (show q1.1.1 = q2.1.1 ∧ q1.2.1 = q2.2.1 from by simpa using hidx).2
          have h22 : q1.2.2 = q2.2.2 := by
            simpa using (show q1.1.2 = q2.1.2 ∧ q1.2.2 = q2.2.2 from by simpa using htarget).2
          ext i <;> fin_cases i <;> simpa [h21, h22]
        apply Subtype.ext
        apply Prod.ext <;> assumption
  have hsubset : Finset.image f S.attach ⊆ auxIncidences X := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    have hquad : q.1 ∈ (X.P₁.product X.P₂).product (X.P₁.product X.P₂) := by
      exact (Finset.mem_filter.mp q.2).1
    have hdist : dist q.1.1.1 q.1.1.2 = dist q.1.2.1 q.1.2.2 := by
      exact (Finset.mem_filter.mp q.2).2
    rcases Finset.mem_product.mp hquad with ⟨hleft, hright⟩
    rcases Finset.mem_product.mp hleft with ⟨hi, hp⟩
    rcases Finset.mem_product.mp hright with ⟨hj, hq⟩
    have hpoint : (f q).1 ∈ auxPointSet X := by
      simpa [f] using auxPointOfPair_mem_auxPointSet X hp hq
    have hcurve : (f q).1 ∈ auxCurve X ⟨q.1.1.1, hi⟩ ⟨q.1.2.1, hj⟩ := by
      simpa [f] using
        auxPointOfPair_mem_auxCurve X ⟨q.1.1.1, hi⟩ ⟨q.1.2.1, hj⟩ hp hq hdist
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ?_
      constructor
      · exact hpoint
      · simp
    · simpa [f] using hcurve
  calc
    (equalDistanceQuadruples X).card = S.attach.card := by
      simpa [S] using (Finset.card_attach (s := S))
    _ = (Finset.image f S.attach).card := by
      rw [Finset.card_image_of_injective _ hf]
    _ ≤ (auxIncidences X).card := Finset.card_le_card hsubset

end PachDeZeeuw.PDZ
