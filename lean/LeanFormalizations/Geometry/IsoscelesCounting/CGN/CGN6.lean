/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.Lc1Strict
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L1
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexIndepHelpers
import LeanFormalizations.Geometry.IsoscelesCounting.SignedAreaOangle
import LeanFormalizations.Geometry.IsoscelesCounting.OangleBridge
import Mathlib

/-!
# CGN6: normalized minor-cap chain model

This file develops the full CGN6 layer named in the counterexample-card-ge-nine
prose. It defines the normalized minor-cap chain data structures and proves the
main geometric lemmas:

* `MinorCapChainCoords` / `MinorCapChainModel`: the normalized coordinate data interface
  (ordered coordinates, endpoint normalization, unit-disk bound, adjacent-slope bookkeeping).
* `CGN6norm`: normalization of a MEC cap packet to a minor-cap chain model.
* `CGN6b0` / `CGN6b`: endpoint secant bounds and the non-acute inner-product lemma.
* `CGN6c`: one-sided distance injectivity and strict endpoint monotonicity.
* `CGN6d0`: midpoint betweenness for positive-side apices.
* `CGN6e0`-`CGN6e7`: apex-side dichotomy and indexed-witness existence and uniqueness.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators

namespace IsoscelesCounting
namespace CGN

/-- Convert a natural index into a `Fin m` index. -/
def finIndex (m : ℕ) (n : ℕ) (hn : n < m) : Fin m :=
  ⟨n, hn⟩

/-- The slope of the secant line through two indexed points in a normalized
minor-cap chain. The intended use always supplies `i < j`, so the denominator
is positive. -/
noncomputable def slopeAt {m : ℕ} (X Y : Fin m → ℝ)
    (i j : ℕ) (hi : i < m) (hj : j < m) : ℝ :=
  (Y (finIndex m j hj) - Y (finIndex m i hi))
    / (X (finIndex m j hj) - X (finIndex m i hi))

/-- Reconstruct the `ℝ²`-point from its coordinates. -/
noncomputable def point {m : ℕ} (X Y : Fin m → ℝ) (t : Fin m) : ℝ² :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => if i = 0 then X t else Y t)

/-- Construct a vector in `ℝ²` from its two coordinates. -/
noncomputable def vec2 (x y : ℝ) : ℝ² :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

/-- The left adjacent secant slope `slope(t, t+1)` in natural indexing. -/
noncomputable def adjacentSlope {m : ℕ} (X Y : Fin m → ℝ)
    (t : ℕ) (h : t + 1 < m) : ℝ :=
  slopeAt X Y t (t + 1) (by omega) h

/-- The right adjacent secant slope `slope(t+1, t+2)` in natural indexing. -/
noncomputable def nextAdjacentSlope {m : ℕ} (X Y : Fin m → ℝ)
    (t : ℕ) (h : t + 2 < m) : ℝ :=
  slopeAt X Y (t + 1) (t + 2) (by omega) (by omega)

/-- Totalized `X` coordinate on natural indices. Outside the valid range, this
returns `0` so that interval sums can be written on `ℕ`. -/
noncomputable def xCoord {m : ℕ} (X : Fin m → ℝ) (n : ℕ) : ℝ :=
  if h : n < m then X (finIndex m n h) else 0

/-- Totalized `Y` coordinate on natural indices. Outside the valid range, this
returns `0` so that interval sums can be written on `ℕ`. -/
noncomputable def yCoord {m : ℕ} (Y : Fin m → ℝ) (n : ℕ) : ℝ :=
  if h : n < m then Y (finIndex m n h) else 0

/-- Totalized adjacent slope on natural indices. Outside the valid range, this
returns `0` so that interval sums can be written on `ℕ`. -/
noncomputable def adjSlopeNat {m : ℕ} (X Y : Fin m → ℝ) (t : ℕ) : ℝ :=
  if h : t + 1 < m then slopeAt X Y t (t + 1) (by omega) h else 0

/-- Internal normalized minor-cap chain coordinates. The cap points are indexed
in order and carry separate `X` / `Y` coordinates. The fields match the prose
package:

* `X_0 = -1`, `X_(m-1) = 1`
* `Y_0 = Y_(m-1) = 0`
* strict `X`-monotonicity
* all points lie in the unit disk
* adjacent secant slopes are weakly decreasing

The coordinate core is the boundary object for CGN6b; it is stronger than
`OrderedCap` because it remembers the geometric normalization data. -/
structure MinorCapChainCoords (m : ℕ) where
  /-- The cap has at least two points, so the two endpoints exist. -/
  hm : 2 ≤ m
  /-- `X`-coordinates of the normalized cap chain. -/
  X : Fin m → ℝ
  /-- `Y`-coordinates of the normalized cap chain. -/
  Y : Fin m → ℝ
  /-- Strict increase of the `X` coordinates. -/
  x_strict : ∀ {i j : Fin m}, i < j → X i < X j
  /-- Left endpoint normalization. -/
  X_first : X (finIndex m 0 (by omega)) = -1
  /-- Right endpoint normalization. -/
  X_last : X (finIndex m (m - 1) (by omega)) = 1
  /-- Left endpoint lies on the diameter. -/
  Y_first : Y (finIndex m 0 (by omega)) = 0
  /-- Right endpoint lies on the diameter. -/
  Y_last : Y (finIndex m (m - 1) (by omega)) = 0
  /-- Every point lies in the closed upper half-plane. -/
  y_nonneg : ∀ t : Fin m, 0 ≤ Y t
  /-- Every point lies in the closed unit disk. -/
  unit_disk : ∀ t : Fin m, X t ^ 2 + Y t ^ 2 ≤ 1
  /-- Adjacent secant slopes `d_t = slope(t, t+1)` are weakly decreasing. -/
  adjacent_slopes_decreasing :
    ∀ t : ℕ, ∀ h : t + 2 < m,
      adjacentSlope X Y t (by omega) ≥ nextAdjacentSlope X Y t h

/-- The public normalized model attached to an ordered cap `L`.  It stores the
coordinate core plus the point-coordinate coherence field used by the CGN6c /
CGN6e transport steps. -/
structure MinorCapChainModel {m : ℕ} (L : OrderedCap m) where
  /-- Normalized coordinates of the cap chain. -/
  coords : MinorCapChainCoords m
  /-- The cap points are exactly the normalized coordinates. -/
  points_eq : ∀ t : Fin m, L.points t = point coords.X coords.Y t

/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/

/-- Explicit chord-frame coordinate map used by the CGN6 normalization.

The intended instantiation is the midpoint/rotation/reflection/scaling
map from the prose proof: the `scale` parameter is `2 / ‖q_m - q_1‖`
and the two direction vectors are the normalized chord and inward normal
vectors. -/
noncomputable def chordFrame (M e n : ℝ²) (scale : ℝ) : ℝ² → ℝ² :=
  fun z =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 =>
      if i = 0 then scale * ⟪z - M, e⟫_ℝ else scale * ⟪z - M, n⟫_ℝ)

@[simp] theorem chordFrame_center (M e n : ℝ²) (scale : ℝ) :
    chordFrame M e n scale M = 0 := by
  ext i
  fin_cases i <;> simp [chordFrame]

/-- A two-vector family is orthonormal if both vectors have norm `1`,
and they are orthogonal. -/
private theorem orthonormal_pair_ite {e n : ℝ²}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    Orthonormal ℝ (fun i : Fin 2 => if i = 0 then e else n) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [he, hn, hen, real_inner_comm]

/-- A vector in `ℝ²` is the sum of its coordinates in an orthonormal pair. -/
private theorem orthonormal_pair_decomp {e n x : ℝ²}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    x = inner ℝ e x • e + inner ℝ n x • n := by
  classical
  have hpair : Orthonormal ℝ (fun i : Fin 2 => if i = 0 then e else n) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, hn, hen, real_inner_comm]
  let b : Module.Basis (Fin 2) ℝ ℝ² :=
    basisOfOrthonormalOfCardEqFinrank
      hpair
      (by simp)
  have hb : Orthonormal ℝ ⇑b := by
    simpa [b] using hpair
  let ob : OrthonormalBasis (Fin 2) ℝ ℝ² := b.toOrthonormalBasis hb
  calc
    x = ∑ i : Fin 2, inner ℝ (ob i) x • ob i := by
      have h := ob.sum_repr' x
      simpa [ob, b] using h.symm
    _ = inner ℝ e x • e + inner ℝ n x • n := by
      simp [ob, b, Fin.sum_univ_two]

/-- Squared norm in an orthonormal pair is the sum of squared coordinates. -/
private theorem orthonormal_pair_normsq {e n x : ℝ²}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    ‖x‖ ^ 2 = (inner ℝ e x)^2 + (inner ℝ n x)^2 := by
  have hdecomp := orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := x)
  rw [hdecomp]
  have horth : inner ℝ (inner ℝ e x • e) (inner ℝ n x • n) = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, hen]
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (inner ℝ e x • e) (inner ℝ n x • n) horth
  have hinner_e : inner ℝ e (inner ℝ e x • e + inner ℝ n x • n) = inner ℝ e x := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp [he, hen]
  have hinner_n : inner ℝ n (inner ℝ e x • e + inner ℝ n x • n) = inner ℝ n x := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp [hn, hen, real_inner_comm]
  simpa [hinner_e, hinner_n, norm_smul, he, hn, pow_two] using hsq

/-- The `e`-coordinate of a vector in an orthonormal pair is recovered by
pairing with `e`. -/
private theorem orthonormal_pair_inner_left {e n u : ℝ²}
    (he : ‖e‖ = 1) (_hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    ⟪⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n, e⟫_ℝ = ⟪e, u⟫_ℝ := by
  rw [inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
  have he2 : ‖e‖ ^ 2 = 1 := by nlinarith [he]
  have hen' : ⟪n, e⟫_ℝ = 0 := by simpa [real_inner_comm] using hen
  rw [he2, hen']
  simp

/-- The `n`-coordinate of a vector in an orthonormal pair is recovered by
pairing with `n`. -/
private theorem orthonormal_pair_inner_right {e n u : ℝ²}
    (_he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    ⟪⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n, n⟫_ℝ = ⟪n, u⟫_ℝ := by
  rw [inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
  have hn2 : ‖n‖ ^ 2 = 1 := by nlinarith [hn]
  have hen' : ⟪e, n⟫_ℝ = 0 := hen
  rw [hn2, hen']
  simp

/-- The right-angle rotation squares to negation. -/
private theorem rightAngleRotation_sq_neg (x : ℝ²) :
    EuclideanGeometry.o.rightAngleRotation (EuclideanGeometry.o.rightAngleRotation x) = -x := by
  have h := congrArg (fun f : ℝ² ≃ₗᵢ[ℝ] ℝ² => f (EuclideanGeometry.o.rightAngleRotation x))
    EuclideanGeometry.o.rightAngleRotation_symm
  simp

/-- The `chordFrame` map is linear when the midpoint is `0`. -/
private noncomputable def chordLinear (e n : ℝ²) (scale : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun := fun v => chordFrame (0 : ℝ²) e n scale v
  map_add' := by
    intro x y
    ext i <;> fin_cases i <;> simp [chordFrame, inner_add_left]
    all_goals ring
  map_smul' := by
    intro m x
    ext i <;> fin_cases i <;> simp [chordFrame, inner_smul_left]
    all_goals ring

/-- Area-form identity for the standard orientation and the right-angle
rotation of a unit vector. -/
private theorem orthonormal_areaForm (e : ℝ²) (he : ‖e‖ = 1) :
    ∀ u v : ℝ²,
      IsoscelesCounting.stdOrientation.areaForm u v =
        ⟪u, e⟫_ℝ * ⟪v, IsoscelesCounting.stdOrientation.rightAngleRotation e⟫_ℝ -
        ⟪u, IsoscelesCounting.stdOrientation.rightAngleRotation e⟫_ℝ * ⟪v, e⟫_ℝ := by
  let n : ℝ² := IsoscelesCounting.stdOrientation.rightAngleRotation e
  have hn : ‖n‖ = 1 := by
    simp [n, he]
  have hen : inner ℝ e n = 0 := by
    simp [n]
  have hEn : IsoscelesCounting.stdOrientation.areaForm e n = 1 := by
    simp [n, he]
  have harea_e : ∀ v : ℝ², IsoscelesCounting.stdOrientation.areaForm e v = ⟪v, n⟫_ℝ := by
    intro v
    have h' : IsoscelesCounting.stdOrientation.areaForm e v =
        ⟪v, IsoscelesCounting.stdOrientation.rightAngleRotation e⟫_ℝ := by
      have h := IsoscelesCounting.stdOrientation.inner_rightAngleRotation_right (x := v) (y := e)
      rw [IsoscelesCounting.stdOrientation.areaForm_swap] at h
      simpa using h.symm
    simpa [n] using h' 
  have harea_n : ∀ v : ℝ², IsoscelesCounting.stdOrientation.areaForm n v = -⟪v, e⟫_ℝ := by
    intro v
    have h' : IsoscelesCounting.stdOrientation.areaForm
        (IsoscelesCounting.stdOrientation.rightAngleRotation e) v = -⟪v, e⟫_ℝ := by
      have h := IsoscelesCounting.stdOrientation.inner_rightAngleRotation_left
        (x := IsoscelesCounting.stdOrientation.rightAngleRotation e) (y := v)
      simp [real_inner_comm]
    simpa [n] using h'
  intro u v
  have hu := orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := u)
  have htmp1 : IsoscelesCounting.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) =
      ⟪e, u⟫_ℝ • IsoscelesCounting.stdOrientation.areaForm e := by
    exact LinearMap.map_smul (IsoscelesCounting.stdOrientation.areaForm) (⟪e, u⟫_ℝ) e
  have htmp2 : IsoscelesCounting.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) =
      ⟪n, u⟫_ℝ • IsoscelesCounting.stdOrientation.areaForm n := by
    exact LinearMap.map_smul (IsoscelesCounting.stdOrientation.areaForm) (⟪n, u⟫_ℝ) n
  have h1 : IsoscelesCounting.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) v =
      ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ := by
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp1
    simp [harea_e v]
  have h2 : IsoscelesCounting.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) v =
      -⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := by
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp2
    simp [harea_n v]
  have hsum :
      IsoscelesCounting.stdOrientation.areaForm
          (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v =
        ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ - ⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := by
    have htmp :
        IsoscelesCounting.stdOrientation.areaForm
          (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) =
        IsoscelesCounting.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) +
          IsoscelesCounting.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) := by
      exact LinearMap.map_add (IsoscelesCounting.stdOrientation.areaForm)
        (⟪e, u⟫_ℝ • e) (⟪n, u⟫_ℝ • n)
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp
    change (IsoscelesCounting.stdOrientation.areaForm
      (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n)) v =
      (IsoscelesCounting.stdOrientation.areaForm (⟪e, u⟫_ℝ • e)) v +
        (IsoscelesCounting.stdOrientation.areaForm (⟪n, u⟫_ℝ • n)) v at this
    rw [h1, h2] at this
    simpa [sub_eq_add_neg] using this
  have hrew : IsoscelesCounting.stdOrientation.areaForm u v =
      IsoscelesCounting.stdOrientation.areaForm
        (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v := by
    simpa using congrArg (fun z : ℝ² => IsoscelesCounting.stdOrientation.areaForm z v) hu
  have hfinal : IsoscelesCounting.stdOrientation.areaForm u v =
      ⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ := by
    calc
      IsoscelesCounting.stdOrientation.areaForm u v =
          IsoscelesCounting.stdOrientation.areaForm
            (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v := hrew
      _ = ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ - ⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := hsum
      _ = ⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ := by
        rw [real_inner_comm (x := e) (y := u), real_inner_comm (x := n) (y := u)]
  simpa [n] using hfinal

/-- Area-form formula for `vec2`. -/
private theorem vec2_areaForm (a b c d : ℝ) :
    IsoscelesCounting.stdOrientation.areaForm (vec2 a b) (vec2 c d) = a * d - b * c := by
  have h := IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm (v := (0 : ℝ²))
    (vj := vec2 a b) (vk := vec2 c d)
  have h' : IsoscelesCounting.stdOrientation.areaForm (vec2 a b) (vec2 c d) =
      IsoscelesCounting.signedArea2 (0 : ℝ²) (vec2 a b) (vec2 c d) := by
    simpa [vec2, sub_eq_add_neg] using h.symm
  rw [h']
  simp [IsoscelesCounting.signedArea2, vec2]
  ring_nf

/-- Distance-squared formula for `vec2`. -/
private theorem vec2_dist_sq (x1 y1 x2 y2 : ℝ) :
    dist (vec2 x1 y1) (vec2 x2 y2) ^ 2 = (x1 - x2) ^ 2 + (y1 - y2) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_sq_eq]
  simp [vec2, sub_eq_add_neg, pow_two]

private theorem point_eq_vec2 {m : ℕ} (X Y : Fin m → ℝ) (t : Fin m) :
    point X Y t = vec2 (X t) (Y t) := by
  ext i <;> fin_cases i <;>
    simp [point, vec2]

private theorem point_signedArea2_eq {m : ℕ} (X Y : Fin m → ℝ) (t0 t1 t2 : Fin m) :
    signedArea2 (point X Y t0) (point X Y t1) (point X Y t2) =
      (X t1 - X t0) * (Y t2 - Y t1) - (Y t1 - Y t0) * (X t2 - X t1) := by
  rw [point_eq_vec2 X Y t0, point_eq_vec2 X Y t1, point_eq_vec2 X Y t2]
  simp [IsoscelesCounting.signedArea2, vec2]
  ring

/-- Scaled area-form formula for `vec2`. -/
private theorem vec2_areaForm_scaled (a b c d scale : ℝ) :
    IsoscelesCounting.stdOrientation.areaForm
        (vec2 (scale * a) (scale * b))
        (vec2 (scale * c) (scale * d)) =
      scale ^ 2 * (a * d - b * c) := by
  have h := vec2_areaForm (a := scale * a) (b := scale * b) (c := scale * c) (d := scale * d)
  have h' : (scale * a) * (scale * d) - (scale * b) * (scale * c) =
      scale ^ 2 * (a * d - b * c) := by
    ring
  exact h.trans h'

-- The normalization proof is large enough to need a higher elaboration budget.
set_option maxHeartbeats 600000 in
/-- CGN6norm: a MEC cap packet can be normalized to a cap-attached minor-cap
chain model.  The proof follows the documented midpoint / chord-frame / scale
construction and packages the result as `MinorCapChainModel (L.map T hT)` with
the associated similarity transport data. -/
theorem CGN6norm_minorCapChainModel_of_mecCapPacket
    {A : Finset ℝ²} {m : ℕ} {L : OrderedCap m}
    (Packet : MecCapPacket A L)
    (Hside : MinorCapSideHypotheses Packet)
    (Hord : StrictCapOrder A L) :
    ∃ T, ∃ hT : Function.Injective T, ∃ _tau : SimilarityTransportData T,
      Nonempty (MinorCapChainModel (L.map T hT)) := by
  classical
  let q1 : ℝ² := L.points (firstIndex (m := m) Packet.hm)
  let qm : ℝ² := L.points (lastIndex (m := m) Packet.hm)
  have hfirst_last : firstIndex (m := m) Packet.hm ≠ lastIndex (m := m) Packet.hm := by
    intro h
    have hm1 : 1 < m := by
      simpa using Packet.hm
    have hval0 : (firstIndex (m := m) Packet.hm).val = 0 := by simp [firstIndex]
    have hval1 : (lastIndex (m := m) Packet.hm).val = m - 1 := by simp [lastIndex]
    have hne : m - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hm1
    have hval : (0 : ℕ) = m - 1 := by
      simpa [hval0, hval1] using congrArg Fin.val h
    exact hne hval.symm
  have hqne : q1 ≠ qm := by
    intro hq
    exact hfirst_last (L.injective hq)
  let u : ℝ² := qm - q1
  have hu : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr hqne.symm
  have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let e : ℝ² := ‖u‖⁻¹ • u
  let n : ℝ² := IsoscelesCounting.stdOrientation.rightAngleRotation e
  have he : ‖e‖ = 1 := by
    dsimp [e]
    have hnonneg : 0 ≤ ‖u‖⁻¹ := by positivity
    calc
      ‖e‖ = ‖‖u‖⁻¹ • u‖ := rfl
      _ = ‖u‖⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ = 1 := by field_simp [hu_norm.ne']
  have hn : ‖n‖ = 1 := by
    simp [n, he]
  have hen : inner ℝ e n = 0 := by
    simp [n]
  let scale : ℝ := 2 / ‖u‖
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  let F : ℝ² →ₗ[ℝ] ℝ² := chordLinear e n scale
  have hF_inj : Function.Injective F := by
    intro v w hfw
    have h0 : F (v - w) = 0 := by
      simp [map_sub, hfw]
    have hcoord0 : scale * ⟪v - w, e⟫_ℝ = 0 := by
      have := congrArg (fun z : ℝ² => z 0) h0
      simpa [F, chordLinear, chordFrame] using this
    have hcoord1 : scale * ⟪v - w, n⟫_ℝ = 0 := by
      have := congrArg (fun z : ℝ² => z 1) h0
      simpa [F, chordLinear, chordFrame] using this
    have hv0 : ⟪e, v - w⟫_ℝ = 0 := by
      simpa [real_inner_comm] using
        (mul_eq_zero.mp hcoord0).resolve_left (by positivity)
    have hv1 : ⟪n, v - w⟫_ℝ = 0 := by
      simpa [real_inner_comm] using
        (mul_eq_zero.mp hcoord1).resolve_left (by positivity)
    have hdecomp := orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := v - w)
    have hzero : v - w = 0 := by
      simpa [hv0, hv1] using hdecomp
    exact sub_eq_zero.mp hzero
  have hF_equiv : ℝ² ≃ₗ[ℝ] ℝ² :=
    LinearEquiv.ofInjectiveOfFinrankEq F hF_inj (by simp)
  let M : ℝ² := midpoint ℝ q1 qm
  let T : ℝ² → ℝ² := fun z => F (z - M)
  have hTaff : ℝ² ≃ᵃ[ℝ] ℝ² := by
    simpa [T, F, chordLinear, chordFrame, M] using
      (AffineEquiv.ofLinearEquiv hF_equiv M (0 : ℝ²))
  have hT : Function.Injective T := by
    intro x y hxy
    have hxy' : F (x - M) = F (y - M) := by
      simpa [T] using hxy
    have hxy'' : x - M = y - M := hF_inj hxy'
    simpa using hxy''
  have hnormF : ∀ v : ℝ², ‖F v‖ = scale * ‖v‖ := by
    intro v
    have hsq : ‖F v‖ ^ 2 = scale ^ 2 * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [F, chordLinear, chordFrame, orthonormal_pair_normsq (e := e) (n := n) he hn hen,
        pow_two, mul_comm, mul_left_comm, mul_assoc, real_inner_comm]
      ring_nf
    have hnonneg : 0 ≤ scale * ‖v‖ := by positivity
    have hnormnonneg : 0 ≤ ‖F v‖ := norm_nonneg _
    nlinarith [hsq, hnonneg, hnormnonneg]
  have hareaF : ∀ u v : ℝ², stdOrientation.areaForm (F u) (F v) = scale ^ 2 * stdOrientation.areaForm u v := by
    intro u v
    have hFu : F u = vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ) := by
      ext i <;> fin_cases i <;>
        simp [F, chordLinear, chordFrame, vec2]
    have hFv : F v = vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ) := by
      ext i <;> fin_cases i <;>
        simp [F, chordLinear, chordFrame, vec2]
    have hvec_area :
        stdOrientation.areaForm
            (vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ))
            (vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ)) =
          scale ^ 2 * (⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ) := by
      simpa using vec2_areaForm_scaled (a := ⟪u, e⟫_ℝ) (b := ⟪u, n⟫_ℝ)
        (c := ⟪v, e⟫_ℝ) (d := ⟪v, n⟫_ℝ) scale
    calc
      stdOrientation.areaForm (F u) (F v)
          = stdOrientation.areaForm
              (vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ))
              (vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ)) := by
                  rw [hFu, hFv]
      _ = scale ^ 2 * (⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ) := hvec_area
      _ = scale ^ 2 * stdOrientation.areaForm u v := by
          rw [orthonormal_areaForm (e := e) he u v]
  have hdist_image : ∀ a b : ℝ², dist (T a) (T b) = scale * dist a b := by
    intro a b
    calc
      dist (T a) (T b) = ‖F (a - M) - F (b - M)‖ := by
        simp [T, dist_eq_norm]
      _ = ‖F ((a - M) - (b - M))‖ := by
        simp
      _ = ‖F (a - b)‖ := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = scale * dist a b := by
        rw [hnormF, dist_eq_norm]
  have hdist_eq_iff : ∀ a b c : ℝ²,
      dist (T a) (T b) = dist (T a) (T c) ↔ dist a b = dist a c := by
    intro a b c
    constructor
    · intro h
      have hs : scale ≠ 0 := ne_of_gt hscale_pos
      rw [hdist_image a b, hdist_image a c] at h
      exact (mul_left_cancel₀ hs) h
    · intro h
      have hs : scale ≠ 0 := ne_of_gt hscale_pos
      rw [hdist_image a b, hdist_image a c]
      exact congrArg (fun x => scale * x) h
  have hconvexHull_mem_iff : ∀ {S : Set ℝ²} {a : ℝ²},
      T a ∈ convexHull ℝ (T '' S) ↔ a ∈ convexHull ℝ S := by
    intro S a
    let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' T F M (by
      intro p'
      simp [T, sub_eq_add_neg, map_add, add_comm])
    have hmap : T '' (convexHull ℝ S) = convexHull ℝ (T '' S) := by
      simpa using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      have himage : T a ∈ T '' convexHull ℝ S := by
        rw [← hmap] at ha
        exact ha
      rcases himage with ⟨b, hb, hTb⟩
      have hba : b = a := hT hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show T a ∈ T '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  have hhalfplane_sign : ∀ a b c : ℝ²,
      signedArea2 (T a) (T b) (T c) =
        (1 : ℝ) * (scale ^ 2) * signedArea2 a b c := by
    intro a b c
    have hsub1 : T b - T a = F (b - a) := by
      change F (b - M) - F (a - M) = F (b - a)
      rw [← map_sub]
      congr 1
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hsub2 : T c - T a = F (c - a) := by
      change F (c - M) - F (a - M) = F (c - a)
      rw [← map_sub]
      congr 1
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      signedArea2 (T a) (T b) (T c)
          = stdOrientation.areaForm (T b - T a) (T c - T a) := by
              rw [signedArea2_eq_stdOrientation_areaForm]
      _ = stdOrientation.areaForm (F (b - a)) (F (c - a)) := by rw [hsub1, hsub2]
      _ = scale ^ 2 * stdOrientation.areaForm (b - a) (c - a) := hareaF _ _
      _ = (1 : ℝ) * (scale ^ 2) * signedArea2 a b c := by
            rw [signedArea2_eq_stdOrientation_areaForm]
            ring
  let hX : Fin m → ℝ := fun t => scale * ⟪L.points t - M, e⟫_ℝ
  let hY : Fin m → ℝ := fun t => scale * ⟪L.points t - M, n⟫_ℝ
  have hXdef : hX = fun t : Fin m => scale * ⟪L.points t - M, e⟫_ℝ := rfl
  have hYdef : hY = fun t : Fin m => scale * ⟪L.points t - M, n⟫_ℝ := rfl
  have hq1mid : q1 - M = -(1 / 2 : ℝ) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - qm) := by
        simp [M]
      _ = -(1 / 2 : ℝ) • u := by
        rw [show q1 - qm = -u by simp [u]]
        simp [smul_neg]
  have hqm_mid : qm - M = (1 / 2 : ℝ) • u := by
    simp [M, u]
  have hue : ⟪u, e⟫_ℝ = ‖u‖ := by
    dsimp [e]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hnorm : ‖u‖⁻¹ * ‖u‖ ^ 2 = ‖u‖ := by
      rw [pow_two]
      calc
        ‖u‖⁻¹ * (‖u‖ * ‖u‖) = (‖u‖⁻¹ * ‖u‖) * ‖u‖ := by ring
        _ = ‖u‖ := by
          rw [inv_mul_cancel₀ hu_norm.ne', one_mul]
    simpa [pow_two] using hnorm
  have hun : ⟪u, n⟫_ℝ = 0 := by
    have h0 : ‖u‖⁻¹ * ⟪u, n⟫_ℝ = 0 := by
      simpa [e, real_inner_smul_left] using hen
    have hne : ‖u‖⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_left hne
  have hcenter_x : scale * ⟪Packet.center - M, e⟫_ℝ = 0 := by
    have hdist_eq : dist Packet.center q1 = dist Packet.center qm := by
      simpa [q1, qm, dist_comm] using Packet.first_on_circle.trans Packet.last_on_circle.symm
    have hperp :
        Packet.center ∈ AffineSubspace.perpBisector q1 qm := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      simpa [q1, qm] using hdist_eq
    have hperp' :
        ⟪Packet.center - midpoint ℝ q1 qm, qm - q1⟫_ℝ = 0 := by
      have h :=
        (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
          (c := Packet.center) (p₁ := q1) (p₂ := qm)).mp hperp
      simpa [M] using h
    have heq : ⟪Packet.center - M, e⟫_ℝ = 0 := by
      have hs : ‖u‖ ≠ 0 := ne_of_gt hu_norm
      have hperp'' : ⟪Packet.center - M, u⟫_ℝ = 0 := by
        simpa [u, M] using hperp'
      have hmul : ‖u‖ * ⟪Packet.center - M, e⟫_ℝ = 0 := by
        rw [show e = ‖u‖⁻¹ • u by rfl, inner_smul_right]
        simp [hperp'']
      exact (mul_eq_zero.mp hmul).resolve_left hs
    nlinarith [heq, hscale_pos]
  have hTcoord : ∀ z : ℝ²,
      T z = vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ) := by
    intro z
    ext i <;> fin_cases i <;>
      simp [T, F, chordLinear, chordFrame, vec2]
  have hChordArea : ∀ z : ℝ²,
      signedArea2 (T q1) (T qm) (T z) = 2 * (scale * ⟪z - M, n⟫_ℝ) := by
    intro z
    have hTq1 : T q1 = vec2 (-1 : ℝ) 0 := by
      rw [hTcoord]
      have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
        rw [hq1mid]
        simp [u, real_inner_smul_left, hue]
      have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
        calc
          scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
          _ = -1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
        rw [hq1mid]
        simp [u, real_inner_smul_left, hun]
      simp [vec2, hq1e, hq1n]
    have hTqm : T qm = vec2 (1 : ℝ) 0 := by
      rw [hTcoord]
      have hqme' : ⟪qm - M, e⟫_ℝ = (1 / 2 : ℝ) * ‖u‖ := by
        rw [hqm_mid]
        simp [u, real_inner_smul_left, hue]
      have hqme : scale * ⟪qm - M, e⟫_ℝ = 1 := by
        calc
          scale * ⟪qm - M, e⟫_ℝ = scale * ((1 / 2 : ℝ) * ‖u‖) := by rw [hqme']
          _ = 1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      have hqmn : scale * ⟪qm - M, n⟫_ℝ = 0 := by
        rw [hqm_mid]
        simp [u, real_inner_smul_left, hun]
      simp [vec2, hqme, hqmn]
    have hTz : T z = vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ) := hTcoord z
    have hvec :
        signedArea2 (vec2 (-1 : ℝ) 0) (vec2 (1 : ℝ) 0)
            (vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ)) =
          2 * (scale * ⟪z - M, n⟫_ℝ) := by
      norm_num [IsoscelesCounting.signedArea2, vec2]
    rw [hTq1, hTqm, hTz]
    exact hvec
  have hcenter_y_nonpos : scale * ⟪Packet.center - M, n⟫_ℝ ≤ 0 := by
    have harea := hhalfplane_sign (a := q1) (b := qm) (c := Packet.center)
    have hchord := hChordArea Packet.center
    have hside : signedArea2 q1 qm Packet.center ≤ 0 := Hside.center_side_nonpos
    nlinarith [harea, hchord, hside, hscale_pos]
  have hXstrict : ∀ {i j : Fin m}, i < j → hX i < hX j := by
    intro i j hij
    have hproj := Hord.chord_projection_strict (i := i) (j := j) hij
    have hx : 0 < ⟪L.points j - L.points i, e⟫_ℝ := by
      have hu' : ⟪L.points j - L.points i, u⟫_ℝ > 0 := by
        simpa [u, q1, qm] using hproj
      have hmul : ‖u‖ * ⟪L.points j - L.points i, e⟫_ℝ = ⟪L.points j - L.points i, u⟫_ℝ := by
        simp [e, u, real_inner_smul_right, hu_norm.ne']
      nlinarith [hu', hmul, hu_norm]
    have hdiff : hX j - hX i = scale * ⟪L.points j - L.points i, e⟫_ℝ := by
      have hinner : ⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ =
          ⟪L.points j + -L.points i, e⟫_ℝ := by
        have hj : ⟪L.points j + -M, e⟫_ℝ = ⟪L.points j, e⟫_ℝ - ⟪M, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points j) M e)
        have hi : ⟪L.points i + -M, e⟫_ℝ = ⟪L.points i, e⟫_ℝ - ⟪M, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points i) M e)
        have hji : ⟪L.points j + -L.points i, e⟫_ℝ = ⟪L.points j, e⟫_ℝ - ⟪L.points i, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points j) (L.points i) e)
        rw [hj, hi, hji]
        ring
      have htmp1 : hX j - hX i = scale * (⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ) := by
        simp [hX, sub_eq_add_neg]
        ring
      have htmp2 : scale * (⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ) =
          scale * ⟪L.points j - L.points i, e⟫_ℝ := by
        rw [hinner]
        simp [sub_eq_add_neg]
      exact htmp1.trans htmp2
    nlinarith [hdiff, hx, hscale_pos]
  have hYnonneg : ∀ t : Fin m, 0 ≤ hY t := by
    intro t
    have hsa : 0 ≤ signedArea2 q1 qm (L.points t) := Hside.cap_side_nonneg t
    have hlink := hChordArea (L.points t)
    nlinarith [hsa, hlink, hhalfplane_sign (a := q1) (b := qm) (c := L.points t), hscale_pos]
  let tau : SimilarityTransportData T :=
    { scale := scale
      scale_pos := hscale_pos
      dist_image := hdist_image
      dist_eq_iff := hdist_eq_iff
      convexHull_mem_iff := hconvexHull_mem_iff
      orientation := (1 : ℝ)
      orientation_sq := by norm_num
      halfplane_sign := hhalfplane_sign }
  let coords : MinorCapChainCoords m :=
    { hm := Packet.hm
      X := hX
      Y := hY
      x_strict := by
        intro i j hij
        exact hXstrict hij
      X_first := by
        have hq1 : L.points (finIndex m 0 (by omega)) = q1 := by
          simp [q1, finIndex, firstIndex]
        calc
          hX (finIndex m 0 (by omega)) = scale * ⟪q1 - M, e⟫_ℝ := by
            simp [hX, hq1]
          _ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by
            rw [hq1mid]
            simp [u, real_inner_smul_left, hue]
          _ = -1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      X_last := by
        have hqm' : L.points (finIndex m (m - 1) (by omega)) = qm := by
          simp [qm, finIndex, lastIndex]
        calc
          hX (finIndex m (m - 1) (by omega)) = scale * ⟪qm - M, e⟫_ℝ := by
            simp [hX, hqm']
          _ = scale * ((1 / 2 : ℝ) * ‖u‖) := by
            rw [hqm_mid]
            simp [u, real_inner_smul_left, hue]
          _ = 1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      Y_first := by
        have hq1 : L.points (finIndex m 0 (by omega)) = q1 := by
          simp [q1, finIndex, firstIndex]
        calc
          hY (finIndex m 0 (by omega)) = scale * ⟪q1 - M, n⟫_ℝ := by
            simp [hY, hq1]
          _ = 0 := by
            rw [hq1mid]
            simp [u, real_inner_smul_left, hun]
      Y_last := by
        have hqm' : L.points (finIndex m (m - 1) (by omega)) = qm := by
          simp [qm, finIndex, lastIndex]
        calc
          hY (finIndex m (m - 1) (by omega)) = scale * ⟪qm - M, n⟫_ℝ := by
            simp [hY, hqm']
          _ = 0 := by
            rw [hqm_mid]
            simp [u, real_inner_smul_left, hun]
      y_nonneg := by
        intro t
        simpa [hY] using hYnonneg t
      unit_disk := by
        intro t
        let lam : ℝ := -(scale * ⟪Packet.center - M, n⟫_ℝ)
        have hlam : 0 ≤ lam := by
          simpa [lam] using neg_nonneg.mpr hcenter_y_nonpos
        have hYt : 0 ≤ hY t := hYnonneg t
        have hTpt : T (L.points t) = vec2 (hX t) (hY t) := by
          rw [hXdef, hYdef]
          exact hTcoord (L.points t)
        have hTcenter : T Packet.center = vec2 0 (-lam) := by
          rw [hTcoord]
          ext i <;> fin_cases i <;> simp [lam, hcenter_x]
        have hTq1 : T q1 = vec2 (-1) 0 := by
          rw [hTcoord]
          have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
            have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
              rw [hq1mid, real_inner_smul_left, hue]
            calc
              scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
              _ = -1 := by
                dsimp [scale]
                field_simp [hu_norm.ne']
          have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
            rw [hq1mid, real_inner_smul_left, hun]
            ring
          simp [vec2, hq1e, hq1n]
        have hdist0 : dist (L.points t) Packet.center ≤ dist q1 Packet.center := by
          have h := Packet.disk_mem t
          rw [← Packet.first_on_circle] at h
          exact h
        have hdist_le : dist (T (L.points t)) (T Packet.center) ≤ dist (T q1) (T Packet.center) := by
          rw [hdist_image, hdist_image]
          exact mul_le_mul_of_nonneg_left hdist0 (le_of_lt hscale_pos)
        have hdist_sq : dist (T (L.points t)) (T Packet.center) ^ 2 ≤
            dist (T q1) (T Packet.center) ^ 2 := by
          have hdn1 : 0 ≤ dist (T (L.points t)) (T Packet.center) := dist_nonneg
          have hdn2 : 0 ≤ dist (T q1) (T Packet.center) := dist_nonneg
          have hle : |dist (T (L.points t)) (T Packet.center)| ≤
              |dist (T q1) (T Packet.center)| := by
            simpa [abs_of_nonneg hdn1, abs_of_nonneg hdn2] using hdist_le
          exact sq_le_sq.mpr hle
        have hleft : dist (T (L.points t)) (T Packet.center) ^ 2 =
            hX t ^ 2 + (hY t + lam) ^ 2 := by
          rw [hTpt, hTcenter]
          have h := vec2_dist_sq (x1 := hX t) (y1 := hY t) (x2 := 0) (y2 := -lam)
          norm_num [sub_eq_add_neg] at h
          exact h
        have hright : dist (T q1) (T Packet.center) ^ 2 = 1 + lam ^ 2 := by
          have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
            have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
              rw [hq1mid, real_inner_smul_left, hue]
            calc
              scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
              _ = -1 := by
                dsimp [scale]
                field_simp [hu_norm.ne']
          have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
            rw [hq1mid, real_inner_smul_left, hun]
            ring
          have hq1coord : T q1 = vec2 (-1) 0 := by
            rw [hTcoord]
            simp [hq1e, hq1n]
          rw [hq1coord, hTcenter]
          have h := vec2_dist_sq (x1 := -1) (y1 := (0 : ℝ)) (x2 := 0) (y2 := -lam)
          norm_num [sub_eq_add_neg] at h
          exact h
        have hsum : hX t ^ 2 + (hY t + lam) ^ 2 ≤ 1 + lam ^ 2 := by
          rw [hleft, hright] at hdist_sq
          exact hdist_sq
        have hcross : 0 ≤ 2 * hY t * lam := by
          have hprod : 0 ≤ hY t * lam := mul_nonneg hYt hlam
          have htwo : 0 ≤ (2 : ℝ) := by norm_num
          simpa [mul_assoc] using mul_nonneg htwo hprod
        have hsq : (hY t + lam) ^ 2 = hY t ^ 2 + 2 * hY t * lam + lam ^ 2 := by
          ring
        have hsum'' : hX t ^ 2 + hY t ^ 2 + 2 * hY t * lam + lam ^ 2 ≤ 1 + lam ^ 2 := by
          calc
            hX t ^ 2 + hY t ^ 2 + 2 * hY t * lam + lam ^ 2
                = hX t ^ 2 + (hY t + lam) ^ 2 := by ring
            _ ≤ 1 + lam ^ 2 := by
              exact hsum
        have hstep : hX t ^ 2 + hY t ^ 2 ≤ 1 := by
          linarith [hsum'', hcross]
        exact hstep
      adjacent_slopes_decreasing := by
        intro t ht
        have ht0 : t < m := by omega
        have ht1 : t + 1 < m := by omega
        have ht2 : t + 2 < m := ht
        have hx1 : 0 < hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0) := by
          have hltFin : finIndex m t ht0 < finIndex m (t + 1) ht1 := by
            simp [finIndex, Fin.lt_def]
          have hlt : hX (finIndex m t ht0) < hX (finIndex m (t + 1) ht1) := by
            exact hXstrict hltFin
          exact sub_pos.mpr hlt
        have hx2 : 0 < hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1) := by
          have hltFin : finIndex m (t + 1) ht1 < finIndex m (t + 2) ht2 := by
            simp [finIndex, Fin.lt_def]
          have hlt : hX (finIndex m (t + 1) ht1) < hX (finIndex m (t + 2) ht2) := by
            exact hXstrict hltFin
          exact sub_pos.mpr hlt
        have hturn : signedArea2 (T (L.points (finIndex m t ht0)))
            (T (L.points (finIndex m (t + 1) ht1))) (T (L.points (finIndex m (t + 2) ht2))) ≤ 0 := by
          have horig : signedArea2 (L.points (finIndex m t ht0))
              (L.points (finIndex m (t + 1) ht1)) (L.points (finIndex m (t + 2) ht2)) ≤ 0 :=
            Hord.consecutive_turn_nonpos t ht
          have htrans := hhalfplane_sign (a := L.points (finIndex m t ht0))
            (b := L.points (finIndex m (t + 1) ht1))
            (c := L.points (finIndex m (t + 2) ht2))
          have hscale_sq_nonneg : 0 ≤ scale ^ 2 := sq_nonneg _
          rw [htrans]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_nonpos_of_nonneg_of_nonpos hscale_sq_nonneg horig
        have hturn' : signedArea2 (point hX hY (finIndex m t ht0))
            (point hX hY (finIndex m (t + 1) ht1)) (point hX hY (finIndex m (t + 2) ht2)) ≤ 0 := by
          have hturnvec :
              signedArea2 (vec2 (hX (finIndex m t ht0)) (hY (finIndex m t ht0)))
                (vec2 (hX (finIndex m (t + 1) ht1)) (hY (finIndex m (t + 1) ht1)))
                (vec2 (hX (finIndex m (t + 2) ht2)) (hY (finIndex m (t + 2) ht2))) ≤ 0 := by
            rw [hTcoord (L.points (finIndex m t ht0)),
              hTcoord (L.points (finIndex m (t + 1) ht1)),
              hTcoord (L.points (finIndex m (t + 2) ht2))] at hturn
            exact hturn
          rw [point_eq_vec2 hX hY (finIndex m t ht0),
            point_eq_vec2 hX hY (finIndex m (t + 1) ht1),
            point_eq_vec2 hX hY (finIndex m (t + 2) ht2)]
          exact hturnvec
        have harea :
            signedArea2 (point hX hY (finIndex m t ht0))
              (point hX hY (finIndex m (t + 1) ht1))
              (point hX hY (finIndex m (t + 2) ht2)) =
              (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) *
                (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) -
                (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                  (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
          exact point_signedArea2_eq (X := hX) (Y := hY) (finIndex m t ht0)
            (finIndex m (t + 1) ht1) (finIndex m (t + 2) ht2)
        have hcross :
            (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) *
                (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) ≤
              (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
          have hturn'' := hturn'
          rw [harea] at hturn''
          have htemp :
              (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) *
                  (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) ≤
                (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                  (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
            exact sub_nonpos.mp hturn''
          rw [mul_comm]
          exact htemp
        have hratio :
            nextAdjacentSlope (X := hX) (Y := hY) t ht ≤
              adjacentSlope (X := hX) (Y := hY) t (by omega) := by
          rw [adjacentSlope, nextAdjacentSlope, slopeAt, slopeAt]
          exact (div_le_div_iff₀ hx2 hx1).2 hcross
        simpa [ge_iff_le] using hratio }
  refine ⟨T, hT, tau, ?_⟩
  exact ⟨⟨coords, by
    intro t
    have hpt : T (L.points t) = vec2 (hX t) (hY t) := by
      rw [hXdef, hYdef]
      exact hTcoord (L.points t)
    calc
      (L.map T hT).points t = T (L.points t) := rfl
      _ = vec2 (hX t) (hY t) := hpt
      _ = point hX hY t := by symm; exact point_eq_vec2 hX hY t
  ⟩⟩

/-- Tail interval weighted-average bound for a weakly decreasing sequence with
strictly positive weights. The interval `[a, b)` is split at `i`, and the
weighted average over the tail `[i, b)` is at most the weighted average over
the whole `[a, b)`. -/
theorem weighted_average_tail_bound
    {w d : ℕ → ℝ} {a i b : ℕ}
    (hai : a < i) (hib : i < b)
    (hmono : ∀ {t u : ℕ}, a ≤ t → t < u → u < b → d t ≥ d u)
    (hwpos : ∀ t ∈ Finset.Ico a b, 0 < w t) :
    (∑ t ∈ Finset.Ico i b, w t * d t) / (∑ t ∈ Finset.Ico i b, w t) ≤
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t) := by
  let Psum : ℝ := ∑ t ∈ Finset.Ico a i, w t
  let Qsum : ℝ := ∑ t ∈ Finset.Ico i b, w t
  let Pval : ℝ := ∑ t ∈ Finset.Ico a i, w t * d t
  let Qval : ℝ := ∑ t ∈ Finset.Ico i b, w t * d t
  have hPnonempty : (Finset.Ico a i).Nonempty := Finset.nonempty_Ico.mpr hai
  have hQnonempty : (Finset.Ico i b).Nonempty := Finset.nonempty_Ico.mpr hib
  have hwP : ∀ t ∈ Finset.Ico a i, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : a ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < i := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨hti, lt_trans htt hib⟩
    exact hwpos t ht'
  have hwQ : ∀ t ∈ Finset.Ico i b, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : i ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < b := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨le_trans (le_of_lt hai) hti, htt⟩
    exact hwpos t ht'
  have hPsum : 0 < Psum := by
    dsimp [Psum]
    exact Finset.sum_pos hwP hPnonempty
  have hQsum : 0 < Qsum := by
    dsimp [Qsum]
    exact Finset.sum_pos hwQ hQnonempty
  have hcross_nonneg :
      0 ≤ ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u) := by
    refine Finset.sum_nonneg ?_
    intro t ht
    refine Finset.sum_nonneg ?_
    intro u hu
    have htI : a ≤ t := (Finset.mem_Ico.mp ht).1
    have htlt : t < i := (Finset.mem_Ico.mp ht).2
    have hui : i ≤ u := (Finset.mem_Ico.mp hu).1
    have hult : u < b := (Finset.mem_Ico.mp hu).2
    have htu : t < u := lt_of_lt_of_le htlt hui
    have hdt : 0 ≤ d t - d u := by
      have hmono' : d t ≥ d u := hmono htI htu hult
      exact sub_nonneg.mpr hmono'
    have hwu : 0 ≤ w t * w u := by
      exact mul_nonneg (le_of_lt (hwP t ht)) (le_of_lt (hwQ u hu))
    exact mul_nonneg hwu hdt
  have hcross_eq :
      ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u)
        = Pval * Qsum - Psum * Qval := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp [mul_sub, mul_left_comm, mul_comm]
  have hcross_prod : Psum * Qval ≤ Pval * Qsum := by
    nlinarith [hcross_nonneg, hcross_eq]
  have hfull_sum_w :
      ∑ t ∈ Finset.Ico a b, w t = Psum + Qsum := by
    symm
    simpa [Psum, Qsum, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := w) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have hfull_sum_wd :
      ∑ t ∈ Finset.Ico a b, w t * d t = Pval + Qval := by
    symm
    simpa [Pval, Qval, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := fun t => w t * d t) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have htarget : Qval / Qsum ≤ (Pval + Qval) / (Psum + Qsum) := by
    have hsumpos : 0 < Psum + Qsum := by nlinarith [hPsum, hQsum]
    have hsumne : Psum + Qsum ≠ 0 := ne_of_gt hsumpos
    have hQne : Qsum ≠ 0 := ne_of_gt hQsum
    field_simp [hQne, hsumne]
    nlinarith [hcross_prod]
  simpa [Psum, Qsum, Pval, Qval, hfull_sum_w, hfull_sum_wd] using htarget

/-- Initial interval weighted-average bound for a weakly decreasing sequence
with strictly positive weights. The interval `[a, b)` is split at `i`, and the
weighted average over the prefix `[a, i)` is at least the weighted average over
the whole `[a, b)`. -/
theorem weighted_average_initial_bound
    {w d : ℕ → ℝ} {a i b : ℕ}
    (hai : a < i) (hib : i < b)
    (hmono : ∀ {t u : ℕ}, a ≤ t → t < u → u < b → d t ≥ d u)
    (hwpos : ∀ t ∈ Finset.Ico a b, 0 < w t) :
    (∑ t ∈ Finset.Ico a i, w t * d t) / (∑ t ∈ Finset.Ico a i, w t) ≥
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t) := by
  let Psum : ℝ := ∑ t ∈ Finset.Ico a i, w t
  let Qsum : ℝ := ∑ t ∈ Finset.Ico i b, w t
  let Pval : ℝ := ∑ t ∈ Finset.Ico a i, w t * d t
  let Qval : ℝ := ∑ t ∈ Finset.Ico i b, w t * d t
  have hPnonempty : (Finset.Ico a i).Nonempty := Finset.nonempty_Ico.mpr hai
  have hQnonempty : (Finset.Ico i b).Nonempty := Finset.nonempty_Ico.mpr hib
  have hwP : ∀ t ∈ Finset.Ico a i, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : a ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < i := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨hti, lt_trans htt hib⟩
    exact hwpos t ht'
  have hwQ : ∀ t ∈ Finset.Ico i b, 0 < w t := by
    intro t ht
    have ht' : t ∈ Finset.Ico a b := by
      have hti : i ≤ t := (Finset.mem_Ico.mp ht).1
      have htt : t < b := (Finset.mem_Ico.mp ht).2
      exact Finset.mem_Ico.mpr ⟨le_trans (le_of_lt hai) hti, htt⟩
    exact hwpos t ht'
  have hPsum : 0 < Psum := by
    dsimp [Psum]
    exact Finset.sum_pos hwP hPnonempty
  have hQsum : 0 < Qsum := by
    dsimp [Qsum]
    exact Finset.sum_pos hwQ hQnonempty
  have hcross_nonneg :
      0 ≤ ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u) := by
    refine Finset.sum_nonneg ?_
    intro t ht
    refine Finset.sum_nonneg ?_
    intro u hu
    have htI : a ≤ t := (Finset.mem_Ico.mp ht).1
    have htlt : t < i := (Finset.mem_Ico.mp ht).2
    have hui : i ≤ u := (Finset.mem_Ico.mp hu).1
    have hult : u < b := (Finset.mem_Ico.mp hu).2
    have htu : t < u := lt_of_lt_of_le htlt hui
    have hdt : 0 ≤ d t - d u := by
      have hmono' : d t ≥ d u := hmono htI htu hult
      exact sub_nonneg.mpr hmono'
    have hwu : 0 ≤ w t * w u := by
      exact mul_nonneg (le_of_lt (hwP t ht)) (le_of_lt (hwQ u hu))
    exact mul_nonneg hwu hdt
  have hcross_eq :
      ∑ t ∈ Finset.Ico a i, ∑ u ∈ Finset.Ico i b, w t * w u * (d t - d u)
        = Pval * Qsum - Psum * Qval := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp [mul_sub, mul_left_comm, mul_comm]
  have hcross_prod : Psum * Qval ≤ Pval * Qsum := by
    nlinarith [hcross_nonneg, hcross_eq]
  have hfull_sum_w :
      ∑ t ∈ Finset.Ico a b, w t = Psum + Qsum := by
    symm
    simpa [Psum, Qsum, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := w) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have hfull_sum_wd :
      ∑ t ∈ Finset.Ico a b, w t * d t = Pval + Qval := by
    symm
    simpa [Pval, Qval, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_consecutive (f := fun t => w t * d t) (m := a) (n := i) (k := b)
        (le_of_lt hai) (le_of_lt hib))
  have htarget : Pval / Psum ≥ (Pval + Qval) / (Psum + Qsum) := by
    have hsumpos : 0 < Psum + Qsum := by nlinarith [hPsum, hQsum]
    have hsumne : Psum + Qsum ≠ 0 := ne_of_gt hsumpos
    have hPne : Psum ≠ 0 := ne_of_gt hPsum
    field_simp [hPne, hsumne]
    nlinarith [hcross_prod]
  simpa [Psum, Qsum, Pval, Qval, hfull_sum_w, hfull_sum_wd] using htarget

/-- CGN6b0: the endpoint secant bounds for a normalized minor-cap chain. -/
theorem CGN6b0_secantEndpointBounds_coords {m : ℕ} (L : MinorCapChainCoords m) :
    (∀ {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < m),
      slopeAt L.X L.Y i j (by omega) hj ≤ slopeAt L.X L.Y 0 j (by omega) hj) ∧
    (∀ {j k : ℕ} (hjk : j < k) (hk : k < m),
      slopeAt L.X L.Y j k (by omega) (by omega) ≥
        slopeAt L.X L.Y j (m - 1) (by omega) (by omega)) := by
  let x : ℕ → ℝ := xCoord L.X
  let y : ℕ → ℝ := yCoord L.Y
  let w : ℕ → ℝ := fun t => x (t + 1) - x t
  let d : ℕ → ℝ := adjSlopeNat L.X L.Y
  have hdstep : ∀ n : ℕ, n + 2 < m → d n ≥ d (n + 1) := by
    intro n hn
    have hn1 : n + 1 < m := by omega
    simpa [d, adjSlopeNat, adjacentSlope, nextAdjacentSlope, hn1, hn] using
      L.adjacent_slopes_decreasing n hn
  have hmono_aux : ∀ t n : ℕ, t + n + 1 < m → d t ≥ d (t + n) := by
    intro t n
    induction n generalizing t with
    | zero =>
        intro _
        exact le_rfl
    | succ n ih =>
        intro htn
        have htn' : t + n + 1 < m := by omega
        have hstep : d (t + n) ≥ d (t + n + 1) := by
          have htn2 : t + n + 2 < m := by omega
          exact hdstep (t + n) htn2
        exact hstep.trans (ih t htn')
  have hmono_b : ∀ {b : ℕ}, b < m → ∀ {t u : ℕ}, t < u → u < b → d t ≥ d u := by
    intro b hb t u htu hu
    have hsum : t + (u - t) = u := by omega
    have hlt : t + (u - t) + 1 < m := by
      have hu1 : u + 1 < m := by omega
      simpa [hsum, Nat.add_assoc] using hu1
    simpa [hsum, Nat.add_assoc] using hmono_aux t (u - t) hlt
  have hwpos_upper : ∀ {a b : ℕ}, b < m → ∀ t ∈ Finset.Ico a b, 0 < w t := by
    intro a b hb t ht
    have htb : t < b := (Finset.mem_Ico.mp ht).2
    have ht0 : t < m := lt_trans htb hb
    have ht1 : t + 1 < m := by omega
    have hxlt : x t < x (t + 1) := by
      dsimp [x]
      simp [xCoord, ht0, ht1]
      exact L.x_strict (by simp [finIndex])
    simpa [w] using sub_pos.mpr hxlt
  have hsecant_eq : ∀ {a b : ℕ} (hab : a < b) (hb : b < m),
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
        = slopeAt L.X L.Y a b (by omega) (by omega) := by
    intro a b hab hb
    have ha : a < m := by omega
    have hden : ∑ t ∈ Finset.Ico a b, w t = x b - x a := by
      simpa [w] using (Finset.sum_Ico_sub (f := x) (le_of_lt hab))
    have hstep : ∀ t ∈ Finset.Ico a b, w t * d t = y (t + 1) - y t := by
      intro t ht
      have htb : t < b := (Finset.mem_Ico.mp ht).2
      have ht0 : t < m := lt_trans htb hb
      have ht1 : t + 1 < m := by omega
      have hne : x (t + 1) - x t ≠ 0 := by
        have hxlt : x t < x (t + 1) := by
          dsimp [x]
          simp [xCoord, ht0, ht1]
          have hlt_fin : finIndex m t ht0 < finIndex m (t + 1) ht1 := by
            simp [finIndex, Fin.lt_def]
          exact L.x_strict hlt_fin
        exact sub_ne_zero.mpr (ne_of_gt hxlt)
      have hmul :
          (x (t + 1) - x t) * ((y (t + 1) - y t) / (x (t + 1) - x t))
            = y (t + 1) - y t := by
        simpa [mul_div_assoc] using
          (mul_div_cancel_left₀ (b := y (t + 1) - y t) hne)
      simpa [w, d, x, y, adjSlopeNat, xCoord, yCoord, ht0, ht1] using hmul
    have hnum : ∑ t ∈ Finset.Ico a b, w t * d t = y b - y a := by
      calc
        ∑ t ∈ Finset.Ico a b, w t * d t = ∑ t ∈ Finset.Ico a b, (y (t + 1) - y t) := by
          exact Finset.sum_congr rfl hstep
        _ = y b - y a := by
          simpa [y] using (Finset.sum_Ico_sub (f := y) (le_of_lt hab))
    calc
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
          = (y b - y a) / (x b - x a) := by rw [hnum, hden]
      _ = slopeAt L.X L.Y a b (by omega) (by omega) := by
          simp [slopeAt, x, y, xCoord, yCoord, ha, hb]
  constructor
  · intro i j hi hij hj
    have havg :=
      weighted_average_tail_bound (w := w) (d := d) (a := 0) (i := i) (b := j)
        hi hij (by
          intro t u _ htu hu
          exact hmono_b (by omega : j < m) htu hu) (hwpos_upper (a := 0) (b := j) hj)
    have htail_sec :
        (∑ t ∈ Finset.Ico i j, w t * d t) / (∑ t ∈ Finset.Ico i j, w t)
          = slopeAt L.X L.Y i j (by omega) (by omega) := hsecant_eq hij hj
    have hfull_sec :
        (∑ t ∈ Finset.range j, w t * d t) / (∑ t ∈ Finset.range j, w t)
          = slopeAt L.X L.Y 0 j (by omega) (by omega) := by
      have h0j : 0 < j := by omega
      have hsec := hsecant_eq h0j hj
      have hrange : Finset.range j = Finset.Ico 0 j := Finset.range_eq_Ico j
      rw [hrange]
      exact hsec
    simpa [htail_sec, hfull_sec] using havg
  · intro j k hjk hk
    by_cases hk' : k = m - 1
    · subst hk'
      simp
    · have hkm1 : k < m - 1 := by omega
      have havg :=
        weighted_average_initial_bound (w := w) (d := d) (a := j) (i := k) (b := m - 1)
          (by omega) hkm1 (by
            intro t u _ htu hu
            exact hmono_b (by omega : m - 1 < m) htu hu)
          (hwpos_upper (a := j) (b := m - 1) (by omega : m - 1 < m))
      have hprefix_sec :
          (∑ t ∈ Finset.Ico j k, w t * d t) / (∑ t ∈ Finset.Ico j k, w t)
            = slopeAt L.X L.Y j k (by omega) (by omega) := hsecant_eq hjk hk
      have hfull_sec :
          (∑ t ∈ Finset.Ico j (m - 1), w t * d t) / (∑ t ∈ Finset.Ico j (m - 1), w t)
            = slopeAt L.X L.Y j (m - 1) (by omega) (by omega) := by
        have hjm1 : j < m - 1 := by omega
        exact hsecant_eq hjm1 (by omega)
      simpa [hprefix_sec, hfull_sec] using havg

/-- Public wrapper for `CGN6b0_secantEndpointBounds_coords`. -/
theorem CGN6b0_secantEndpointBounds {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    (∀ {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < m),
      slopeAt M.coords.X M.coords.Y i j (by omega) hj
        ≤ slopeAt M.coords.X M.coords.Y 0 j (by omega) hj) ∧
    (∀ {j k : ℕ} (hjk : j < k) (hk : k < m),
      slopeAt M.coords.X M.coords.Y j k (by omega) (by omega) ≥
        slopeAt M.coords.X M.coords.Y j (m - 1) (by omega) (by omega)) := by
  simpa using (CGN6b0_secantEndpointBounds_coords M.coords)

/-- A normalized minor-cap chain sees every interior subchord at a nonacute
angle. -/
theorem CGN6b_nonacute_of_minorCapChainCoords {m : ℕ} (L : MinorCapChainCoords m) :
    ∀ {i j k : Fin m}, i < j → j < k →
      ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ ≤ 0 := by
  intro i j k hij hjk
  let x : ℕ → ℝ := xCoord L.X
  let y : ℕ → ℝ := yCoord L.Y
  let w : ℕ → ℝ := fun t => x (t + 1) - x t
  let d : ℕ → ℝ := adjSlopeNat L.X L.Y
  let σL : ℝ := slopeAt L.X L.Y i.val j.val i.isLt j.isLt
  let σR : ℝ := slopeAt L.X L.Y j.val k.val j.isLt k.isLt
  have hij_nat : i.val < j.val := Fin.lt_def.mp hij
  have hjk_nat : j.val < k.val := Fin.lt_def.mp hjk
  have hi_nat : i.val < m := i.isLt
  have hj_nat : j.val < m := j.isLt
  have hk_nat : k.val < m := k.isLt
  have ha_pos : 0 < L.X j - L.X i := sub_pos.mpr (L.x_strict hij)
  have hb_pos : 0 < L.X k - L.X j := sub_pos.mpr (L.x_strict hjk)
  have hdstep : ∀ n : ℕ, n + 2 < m → d n ≥ d (n + 1) := by
    intro n hn
    have hn1 : n + 1 < m := by omega
    simpa [d, adjSlopeNat, adjacentSlope, nextAdjacentSlope, hn1, hn] using
      L.adjacent_slopes_decreasing n hn
  have hmono_aux : ∀ t n : ℕ, t + n + 1 < m → d t ≥ d (t + n) := by
    intro t n
    induction n generalizing t with
    | zero =>
        intro _
        exact le_rfl
    | succ n ih =>
        intro htn
        have htn' : t + n + 1 < m := by omega
        have hstep : d (t + n) ≥ d (t + n + 1) := by
          have htn2 : t + n + 2 < m := by omega
          exact hdstep (t + n) htn2
        exact hstep.trans (ih t htn')
  have hmono_b : ∀ {b : ℕ}, b < m → ∀ {t u : ℕ}, t < u → u < b → d t ≥ d u := by
    intro b hb t u htu hu
    have hsum : t + (u - t) = u := by omega
    have hlt : t + (u - t) + 1 < m := by
      have hu1 : u + 1 < m := by omega
      simpa [hsum, Nat.add_assoc] using hu1
    simpa [hsum, Nat.add_assoc] using hmono_aux t (u - t) hlt
  have hwpos_upper : ∀ {a b : ℕ}, b < m → ∀ t ∈ Finset.Ico a b, 0 < w t := by
    intro a b hb t ht
    have htb : t < b := (Finset.mem_Ico.mp ht).2
    have ht0 : t < m := lt_trans htb hb
    have ht1 : t + 1 < m := by omega
    have hxlt : x t < x (t + 1) := by
      dsimp [x]
      simp [xCoord, ht0, ht1]
      exact L.x_strict (by simp [finIndex])
    simpa [w] using sub_pos.mpr hxlt
  have hinner_eq :
      ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ
        = -(L.X j - L.X i) * (L.X k - L.X j) * (1 + σL * σR) := by
    have hcoord :
        ⟪point L.X L.Y i - point L.X L.Y j, point L.X L.Y k - point L.X L.Y j⟫_ℝ
          = (L.X i - L.X j) * (L.X k - L.X j) + (L.Y i - L.Y j) * (L.Y k - L.Y j) := by
      rw [PiLp.inner_apply]
      simp [point, Fin.sum_univ_two]
      ring
    have hσL_eq : σL * (L.X j - L.X i) = L.Y j - L.Y i := by
      have hne : L.X j - L.X i ≠ 0 := sub_ne_zero.mpr (ne_of_gt (L.x_strict hij))
      dsimp [σL, slopeAt, finIndex]
      field_simp [hne]
    have hσR_eq : σR * (L.X k - L.X j) = L.Y k - L.Y j := by
      have hne : L.X k - L.X j ≠ 0 := sub_ne_zero.mpr (ne_of_gt (L.x_strict hjk))
      dsimp [σR, slopeAt, finIndex]
      field_simp [hne]
    have hYleft : L.Y i - L.Y j = -σL * (L.X j - L.X i) := by linarith [hσL_eq]
    have hYright : L.Y k - L.Y j = σR * (L.X k - L.X j) := by linarith [hσR_eq]
    rw [hcoord, hYleft, hYright]
    ring
  have hsecant_avg : ∀ {a b : ℕ} (hab : a < b) (hb : b < m),
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
        = slopeAt L.X L.Y a b (by omega) (by omega) := by
    intro a b hab hb
    have ha : a < m := by omega
    have hstep_ab : ∀ t ∈ Finset.Ico a b, w t * d t = y (t + 1) - y t := by
      intro t ht
      have htb : t < b := (Finset.mem_Ico.mp ht).2
      have ht0 : t < m := lt_trans htb hb
      have ht1 : t + 1 < m := by omega
      have hne : x (t + 1) - x t ≠ 0 := by
        have hxlt : x t < x (t + 1) := by
          dsimp [x]
          simp [xCoord, ht0, ht1]
          have hlt_fin : finIndex m t ht0 < finIndex m (t + 1) ht1 := by
            simp [finIndex, Fin.lt_def]
          exact L.x_strict hlt_fin
        exact sub_ne_zero.mpr (ne_of_gt hxlt)
      have hmul :
          (x (t + 1) - x t) * ((y (t + 1) - y t) / (x (t + 1) - x t))
            = y (t + 1) - y t := by
        simpa [mul_div_assoc] using
          (mul_div_cancel_left₀ (b := y (t + 1) - y t) hne)
      simpa [w, d, x, y, adjSlopeNat, xCoord, yCoord, ht0, ht1] using hmul
    have hnum : ∑ t ∈ Finset.Ico a b, w t * d t = y b - y a := by
      calc
        ∑ t ∈ Finset.Ico a b, w t * d t = ∑ t ∈ Finset.Ico a b, (y (t + 1) - y t) := by
          exact Finset.sum_congr rfl (by intro t ht; exact hstep_ab t ht)
        _ = y b - y a := by
          simpa [y] using (Finset.sum_Ico_sub (f := y) (m := a) (n := b)
            (le_of_lt hab))
    have hden : ∑ t ∈ Finset.Ico a b, w t = x b - x a := by
      dsimp [w]
      exact Finset.sum_Ico_sub (f := x) (m := a) (n := b) (le_of_lt hab)
    calc
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t)
          = (y b - y a) / (x b - x a) := by rw [hnum, hden]
      _ = slopeAt L.X L.Y a b (by omega) (by omega) := by
          have hxb : x b = L.X (finIndex m b hb) := by
            dsimp [x]
            simp [xCoord, hb]
          have hxa : x a = L.X (finIndex m a ha) := by
            dsimp [x]
            simp [xCoord, ha]
          have hyb : y b = L.Y (finIndex m b hb) := by
            dsimp [y]
            simp [yCoord, hb]
          have hya : y a = L.Y (finIndex m a ha) := by
            dsimp [y]
            simp [yCoord, ha]
          rw [hxb, hxa, hyb, hya]
          dsimp [slopeAt, finIndex]
  have hwhole :
      (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t)
        = slopeAt L.X L.Y i.val k.val hi_nat hk_nat := hsecant_avg (a := i.val) (b := k.val)
          (by omega) hk_nat
  have hprefix :
      (∑ t ∈ Finset.Ico i.val j.val, w t * d t) / (∑ t ∈ Finset.Ico i.val j.val, w t)
        ≥ (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t) := by
    exact weighted_average_initial_bound
      (w := w) (d := d) (a := i.val) (i := j.val) (b := k.val)
      hij_nat hjk_nat
      (by
        intro t u ht htu hu
        exact hmono_b (by omega : k.val < m) htu hu)
      (fun t ht => hwpos_upper (a := i.val) (b := k.val) (by omega : k.val < m) t ht)
  have htail :
      (∑ t ∈ Finset.Ico j.val k.val, w t * d t) / (∑ t ∈ Finset.Ico j.val k.val, w t)
        ≤ (∑ t ∈ Finset.Ico i.val k.val, w t * d t) / (∑ t ∈ Finset.Ico i.val k.val, w t) := by
    exact weighted_average_tail_bound
      (w := w) (d := d) (a := i.val) (i := j.val) (b := k.val)
      hij_nat hjk_nat
      (by
        intro t u ht htu hu
        exact hmono_b (by omega : k.val < m) htu hu)
      (fun t ht => hwpos_upper (a := i.val) (b := k.val) (by omega : k.val < m) t ht)
  have hσge : σL ≥ σR := by
    have hLavg : (∑ t ∈ Finset.Ico i.val j.val, w t * d t) / (∑ t ∈ Finset.Ico i.val j.val, w t)
        = σL := hsecant_avg hij_nat hj_nat
    have hRavg : (∑ t ∈ Finset.Ico j.val k.val, w t * d t) / (∑ t ∈ Finset.Ico j.val k.val, w t)
        = σR := hsecant_avg hjk_nat hk_nat
    linarith [hprefix, htail, hwhole, hLavg, hRavg]
  have hLbound : σL ≤ L.Y j / (L.X j + 1) := by
    by_cases hi0 : i.val = 0
    · have hi0' : i.val = 0 := hi0
      have h0simp : slopeAt L.X L.Y 0 j.val (by omega) hj_nat = L.Y j / (L.X j + 1) := by
        dsimp [slopeAt, finIndex]
        have hX0 : L.X ⟨0, by omega⟩ = -1 := L.X_first
        have hY0 : L.Y ⟨0, by omega⟩ = 0 := L.Y_first
        rw [hX0, hY0]
        ring_nf
      dsimp [σL]
      have hrefl :
          slopeAt L.X L.Y 0 j.val (by omega) hj_nat ≤
            slopeAt L.X L.Y 0 j.val (by omega) hj_nat := le_rfl
      simp [hi0', h0simp]
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have h0 :
          slopeAt L.X L.Y i.val j.val hi_nat hj_nat ≤
            slopeAt L.X L.Y 0 j.val (by omega) hj_nat := by
        exact (CGN6b0_secantEndpointBounds_coords L).1 hi_pos hij_nat hj_nat
      have h0simp : slopeAt L.X L.Y 0 j.val (by omega) hj_nat = L.Y j / (L.X j + 1) := by
        dsimp [slopeAt, finIndex]
        have hX0 : L.X ⟨0, by omega⟩ = -1 := L.X_first
        have hY0 : L.Y ⟨0, by omega⟩ = 0 := L.Y_first
        rw [hX0, hY0]
        ring_nf
      simpa [σL, h0simp] using h0
  have hRbound : -σR ≤ L.Y j / (1 - L.X j) := by
    by_cases hklast : k.val = m - 1
    · have hklast' : k.val = m - 1 := hklast
      have hlsimp : slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega)
          = -L.Y j / (1 - L.X j) := by
        dsimp [slopeAt, finIndex]
        have hXlast : L.X ⟨m - 1, by omega⟩ = 1 := L.X_last
        have hYlast : L.Y ⟨m - 1, by omega⟩ = 0 := L.Y_last
        rw [hXlast, hYlast]
        ring_nf
      have h0' : σR ≥ -L.Y j / (1 - L.X j) := by
        have hrefl :
            slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) ≤
              slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) := le_rfl
        simp [σR, hklast', hlsimp]
      have h0'' : -σR ≤ L.Y j / (1 - L.X j) := by
        have h0le : -L.Y j / (1 - L.X j) ≤ σR := by
          simpa [ge_iff_le] using h0'
        have htmp : -σR ≤ -(-L.Y j / (1 - L.X j)) := by
          exact neg_le_neg h0le
        convert htmp using 1 <;> ring_nf
      exact h0''
    · have h0 : slopeAt L.X L.Y j.val k.val hj_nat hk_nat
          ≥ slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega) := by
        exact (CGN6b0_secantEndpointBounds_coords L).2 hjk_nat hk_nat
      have hlsimp : slopeAt L.X L.Y j.val (m - 1) (by omega) (by omega)
          = -L.Y j / (1 - L.X j) := by
        dsimp [slopeAt, finIndex]
        have hXlast : L.X ⟨m - 1, by omega⟩ = 1 := L.X_last
        have hYlast : L.Y ⟨m - 1, by omega⟩ = 0 := L.Y_last
        rw [hXlast, hYlast]
        ring_nf
      have h0' : σR ≥ -L.Y j / (1 - L.X j) := by
        unfold σR
        simpa [hlsimp] using h0
      have h0'' : -σR ≤ L.Y j / (1 - L.X j) := by
        have h0le : -L.Y j / (1 - L.X j) ≤ σR := by
          simpa [ge_iff_le] using h0'
        have htmp : -σR ≤ -(-L.Y j / (1 - L.X j)) := by
          exact neg_le_neg h0le
        convert htmp using 1 <;> ring_nf
      exact h0''
  have hprod_ge_neg1 : -1 ≤ σL * σR := by
    by_cases hσRnonneg : 0 ≤ σR
    · have hσLnonneg : 0 ≤ σL := by
        linarith [hσge, hσRnonneg]
      have hprod_nonneg : 0 ≤ σL * σR := mul_nonneg hσLnonneg hσRnonneg
      linarith
    · have hσRneg : σR < 0 := lt_of_not_ge hσRnonneg
      by_cases hσLnonneg : 0 ≤ σL
      · have hx1 : 0 < L.X j + 1 := by
          have hfirst_lt_j_nat : 0 < j.val := by omega
          have hfirst_lt_j : finIndex m 0 (by omega) < j := by
            simp [finIndex, Fin.lt_def, hfirst_lt_j_nat]
          have hxlt : L.X (finIndex m 0 (by omega)) < L.X j := L.x_strict hfirst_lt_j
          linarith [hxlt, L.X_first]
        have h1x : 0 < 1 - L.X j := by
          have hj_lt_last_nat : j.val < m - 1 := by omega
          have hj_lt_last : j < finIndex m (m - 1) (by omega) := by
            simp [finIndex, Fin.lt_def, hj_lt_last_nat]
          have hxlt : L.X j < L.X (finIndex m (m - 1) (by omega)) := L.x_strict hj_lt_last
          linarith [hxlt, L.X_last]
        have hy : 0 ≤ L.Y j := L.y_nonneg j
        have hunit : L.Y j ^ 2 ≤ (1 - L.X j) * (1 + L.X j) := by
          nlinarith [L.unit_disk j]
        have hLmul : σL * (L.X j + 1) ≤ L.Y j := (le_div_iff₀ hx1).mp hLbound
        have hRmul : (-σR) * (1 - L.X j) ≤ L.Y j := (le_div_iff₀ h1x).mp hRbound
        have hprod : (-σL * σR) * ((L.X j + 1) * (1 - L.X j)) ≤ L.Y j ^ 2 := by
          have hmul := mul_le_mul hLmul hRmul (by nlinarith [hσRneg, h1x]) hy
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
        have hden : 0 < (L.X j + 1) * (1 - L.X j) := by
          nlinarith [hx1, h1x]
        have hDle : (-σL * σR) * ((L.X j + 1) * (1 - L.X j))
            ≤ (L.X j + 1) * (1 - L.X j) := by
          calc
            (-σL * σR) * ((L.X j + 1) * (1 - L.X j)) ≤ L.Y j ^ 2 := hprod
            _ ≤ (1 - L.X j) * (1 + L.X j) := hunit
            _ = (L.X j + 1) * (1 - L.X j) := by ring
        have htemp : -σL * σR ≤
            ((L.X j + 1) * (1 - L.X j)) / ((L.X j + 1) * (1 - L.X j)) := by
          exact (le_div_iff₀ hden).mpr hDle
        have hdiv : ((L.X j + 1) * (1 - L.X j)) / ((L.X j + 1) * (1 - L.X j)) = 1 := by
          field_simp [ne_of_gt hden]
        linarith
      · have hσLneg : σL < 0 := lt_of_not_ge hσLnonneg
        have hσLle0 : σL ≤ 0 := le_of_lt hσLneg
        have hσRle0 : σR ≤ 0 := le_of_lt hσRneg
        have hprod_nonneg : 0 ≤ σL * σR := mul_nonneg_of_nonpos_of_nonpos hσLle0 hσRle0
        linarith
  have hnonneg : 0 ≤ 1 + σL * σR := by linarith [hprod_ge_neg1]
  have hposprod : 0 ≤ (L.X j - L.X i) * (L.X k - L.X j) := by
    exact mul_nonneg (le_of_lt ha_pos) (le_of_lt hb_pos)
  have hprod_total :
      0 ≤ (L.X j - L.X i) * (L.X k - L.X j) * (1 + σL * σR) := by
    exact mul_nonneg hposprod hnonneg
  rw [hinner_eq]
  convert (neg_nonpos.mpr hprod_total) using 1 <;> ring_nf

/-- Public wrapper for `CGN6b_nonacute_of_minorCapChainCoords`. -/
theorem CGN6b_nonacute_of_minorCapChainModel {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    ∀ {i j k : Fin m}, i < j → j < k →
      ⟪L.points i - L.points j, L.points k - L.points j⟫_ℝ ≤ 0 := by
  intro i j k hij hjk
  rw [M.points_eq i, M.points_eq j, M.points_eq k]
  exact CGN6b_nonacute_of_minorCapChainCoords M.coords hij hjk

/-- `CGN6c`: a fixed cap vertex sees distinct distances on each side of the
chain.  The later-side and earlier-side statements are proved by the same
inner-product calculation with the order reversed. -/
theorem CGN6c_oneSidedDistanceInjective {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L) :
    (∀ {j r s : Fin m}, j < r → r < s →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) ∧
    (∀ {j r s : Fin m}, r < s → s < j →
      dist (L.points j) (L.points r) ≠ dist (L.points j) (L.points s)) := by
  constructor
  · intro j r s hjr hrs hdist
    have hnonacute := CGN6b_nonacute_of_minorCapChainModel M hjr hrs
    have hsq : dist (L.points j) (L.points r) ^ 2 = dist (L.points j) (L.points s) ^ 2 := by
      rw [hdist]
    have hmid0 :
        inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (L.points s - L.points r) = 0 := by
      nlinarith [IsoscelesCounting.inner_chord_eq_dist_sq_diff (L.points r) (L.points s)
        (L.points j), hsq]
    have hmid_r :
        midpoint ℝ (L.points r) (L.points s) - L.points r =
          (1 / 2 : ℝ) • (L.points s - L.points r) := by
      simp
    have hinner_mid :
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points r)
          (L.points s - L.points r) = dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_rs : ‖L.points s - L.points r‖ = dist (L.points r) (L.points s) := by
        simpa [dist_eq_norm] using (dist_comm (L.points s) (L.points r))
      calc
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points r)
            (L.points s - L.points r)
            = ‖L.points s - L.points r‖ ^ 2 * (1 / 2 : ℝ) := by
                rw [hmid_r, real_inner_smul_left, real_inner_self_eq_norm_sq]
                ring_nf
        _ = dist (L.points r) (L.points s) ^ 2 / 2 := by
                rw [hdist_rs]
                ring_nf
    have hinner :
        inner ℝ (L.points j - L.points r) (L.points s - L.points r) =
          dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdecomp : L.points j - L.points r =
          (L.points j - midpoint ℝ (L.points r) (L.points s)) +
            (midpoint ℝ (L.points r) (L.points s) - L.points r) := by
        abel
      rw [hdecomp, inner_add_left, hmid0, zero_add, hinner_mid]
    have hs_ne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    have hpos : 0 < dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hs_ne
      nlinarith [sq_pos_of_pos hdist_pos]
    nlinarith [hnonacute, hinner, hpos]
  · intro j r s hrs hsj hdist
    have hnonacute := CGN6b_nonacute_of_minorCapChainModel M hrs hsj
    have hsq : dist (L.points j) (L.points r) ^ 2 = dist (L.points j) (L.points s) ^ 2 := by
      rw [hdist]
    have hmid0 :
        inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (L.points r - L.points s) = 0 := by
      have hswap :
          inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
            (L.points s - L.points r) = 0 := by
        nlinarith [IsoscelesCounting.inner_chord_eq_dist_sq_diff (L.points r) (L.points s)
          (L.points j), hsq]
      have hswapneg : inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
          (-(L.points s - L.points r)) = 0 := by
        have h' :
            inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
              (-(L.points s - L.points r)) =
            -inner ℝ (L.points j - midpoint ℝ (L.points r) (L.points s))
              (L.points s - L.points r) := by
          simpa using
            (inner_neg_right (L.points j - midpoint ℝ (L.points r) (L.points s))
              (L.points s - L.points r))
        simpa [hswap] using h'
      simpa [sub_eq_add_neg, neg_sub] using hswapneg
    have hmid_r :
        midpoint ℝ (L.points r) (L.points s) - L.points s =
          (1 / 2 : ℝ) • (L.points r - L.points s) := by
      simp
    have hinner_mid :
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points s)
          (L.points r - L.points s) = dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_rs : ‖L.points r - L.points s‖ = dist (L.points r) (L.points s) := by
        simp [dist_eq_norm]
      calc
        inner ℝ (midpoint ℝ (L.points r) (L.points s) - L.points s)
            (L.points r - L.points s)
            = ‖L.points r - L.points s‖ ^ 2 * (1 / 2 : ℝ) := by
                rw [hmid_r, real_inner_smul_left, real_inner_self_eq_norm_sq]
                ring_nf
        _ = dist (L.points r) (L.points s) ^ 2 / 2 := by
                rw [hdist_rs]
                ring_nf
    have hinner :
        inner ℝ (L.points j - L.points s) (L.points r - L.points s) =
          dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdecomp : L.points j - L.points s =
          (L.points j - midpoint ℝ (L.points r) (L.points s)) +
            (midpoint ℝ (L.points r) (L.points s) - L.points s) := by
        abel
      rw [hdecomp, inner_add_left, hmid0, zero_add, hinner_mid]
    have hnonacute' :
        inner ℝ (L.points j - L.points s) (L.points r - L.points s) ≤ 0 := by
      simpa [real_inner_comm] using hnonacute
    have hs_ne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    have hpos : 0 < dist (L.points r) (L.points s) ^ 2 / 2 := by
      have hdist_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hs_ne
      nlinarith [sq_pos_of_pos hdist_pos]
    nlinarith [hinner, hnonacute', hpos]

/-- Distances from the first endpoint of a normalized minor-cap chain increase
strictly along the chain. This is the theorem-level endpoint monotonicity
consumer of `CGN6b` used later in the finite-endpoint N4a lane. -/
theorem CGN6c_dist_strict_from_first {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L)
    {i0 : Fin m}
    (hi0 : i0 = finIndex m 0 (by
      have hm : 2 ≤ m := M.coords.hm
      omega)) :
    ∀ {r s : Fin m}, i0 < r → r < s →
      dist (L.points i0) (L.points r) <
        dist (L.points i0) (L.points s) := by
  subst i0
  intro r s h0r hrs
  let i0 : Fin m := finIndex m 0 (by
    have hm : 2 ≤ m := M.coords.hm
    omega)
  have hnonacute :
      ⟪L.points i0 - L.points r, L.points s - L.points r⟫_ℝ ≤ 0 :=
    CGN6b_nonacute_of_minorCapChainModel M h0r hrs
  have hinner_nonneg :
      0 ≤ ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ := by
    have hneg :
        ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ =
          -⟪L.points i0 - L.points r, L.points s - L.points r⟫_ℝ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (inner_neg_right (L.points i0 - L.points r) (L.points s - L.points r))
    rw [hneg]
    linarith
  have hrs_ne : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  have hrs_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hrs_ne
  have hsq_gap :
      dist (L.points i0) (L.points s) ^ 2 =
        dist (L.points i0) (L.points r) ^ 2 + dist (L.points r) (L.points s) ^ 2
          + 2 * ⟪L.points i0 - L.points r, L.points r - L.points s⟫_ℝ := by
    have hvec :
        L.points i0 - L.points s =
          (L.points i0 - L.points r) + (L.points r - L.points s) := by
      abel
    rw [dist_eq_norm, hvec, norm_add_pow_two_real, dist_eq_norm, dist_eq_norm]
    ring
  have hsq_lt :
      dist (L.points i0) (L.points r) ^ 2 <
        dist (L.points i0) (L.points s) ^ 2 := by
    have hrs_sq_pos : 0 < dist (L.points r) (L.points s) ^ 2 := by
      nlinarith [sq_pos_of_pos hrs_pos]
    nlinarith [hsq_gap, hinner_nonneg, hrs_sq_pos]
  have hr_nonneg : 0 ≤ dist (L.points i0) (L.points r) := dist_nonneg
  have hs_nonneg : 0 ≤ dist (L.points i0) (L.points s) := dist_nonneg
  nlinarith [hsq_lt, sq_nonneg (dist (L.points i0) (L.points r) - dist (L.points i0) (L.points s)),
    sq_nonneg (dist (L.points i0) (L.points r) + dist (L.points i0) (L.points s))]

/-- Distances from the last endpoint of a normalized minor-cap chain decrease
strictly as one moves toward that endpoint. This is the CGN6-local mirror
wrapper used by the finite-endpoint `E3-L20b` lane. -/
theorem CGN6c_dist_strict_from_last {m : ℕ} {L : OrderedCap m}
    (M : MinorCapChainModel L)
    {jm : Fin m}
    (hjm : jm = finIndex m (m - 1) (by
      have hm : 2 ≤ m := M.coords.hm
      omega)) :
    ∀ {r s : Fin m}, r < s → s < jm →
      dist (L.points jm) (L.points s) <
        dist (L.points jm) (L.points r) := by
  subst jm
  intro r s hrs hsj
  let jm : Fin m := finIndex m (m - 1) (by
    have hm : 2 ≤ m := M.coords.hm
    omega)
  have hnonacute :
      ⟪L.points r - L.points s, L.points jm - L.points s⟫_ℝ ≤ 0 :=
    CGN6b_nonacute_of_minorCapChainModel M hrs hsj
  have hinner_nonneg :
      0 ≤ ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ := by
    have hnonacute' :
        ⟪L.points jm - L.points s, L.points r - L.points s⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using hnonacute
    have hneg :
        ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ =
          -⟪L.points jm - L.points s, L.points r - L.points s⟫_ℝ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (inner_neg_right (L.points jm - L.points s) (L.points r - L.points s))
    rw [hneg]
    linarith
  have hrs_ne : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  have hrs_pos : 0 < dist (L.points r) (L.points s) := dist_pos.mpr hrs_ne
  have hsq_gap :
      dist (L.points jm) (L.points r) ^ 2 =
        dist (L.points jm) (L.points s) ^ 2 + dist (L.points r) (L.points s) ^ 2
          + 2 * ⟪L.points jm - L.points s, L.points s - L.points r⟫_ℝ := by
    have hvec :
        L.points jm - L.points r =
          (L.points jm - L.points s) + (L.points s - L.points r) := by
      abel
    rw [dist_eq_norm, hvec, norm_add_pow_two_real, dist_eq_norm, dist_eq_norm]
    have hnorm_rev : ‖L.points s - L.points r‖ ^ 2 = ‖L.points r - L.points s‖ ^ 2 := by
      rw [norm_sub_rev]
    nlinarith
  have hsq_lt :
      dist (L.points jm) (L.points s) ^ 2 <
        dist (L.points jm) (L.points r) ^ 2 := by
    have hrs_sq_pos : 0 < dist (L.points r) (L.points s) ^ 2 := by
      nlinarith [sq_pos_of_pos hrs_pos]
    nlinarith [hsq_gap, hinner_nonneg, hrs_sq_pos]
  have hs_nonneg : 0 ≤ dist (L.points jm) (L.points s) := dist_nonneg
  have hr_nonneg : 0 ≤ dist (L.points jm) (L.points r) := dist_nonneg
  nlinarith [hsq_lt, sq_nonneg (dist (L.points jm) (L.points s) - dist (L.points jm) (L.points r)),
    sq_nonneg (dist (L.points jm) (L.points s) + dist (L.points jm) (L.points r))]

/-- CGN6d0 positive-side helper: if two apexes are both on the same open side
of the perpendicular bisector of `x y`, then the midpoint of `x y` is weakly
between the two apexes in one of the two endpoint orders. This is the local
midpoint/`Wbtw` bridge used by the CGN6d wrapper and the later CGN6e
same-side contradiction. -/
theorem CGN6d0_positiveSideBisector_to_wbtw
    {x y a b : ℝ²}
    (hx : x ≠ y)
    (haeq : dist a x = dist a y)
    (hbeq : dist b x = dist b y)
    (ha_pos : 0 < signedArea2 x y a)
    (hb_pos : 0 < signedArea2 x y b) :
    Wbtw ℝ (midpoint ℝ x y) a b ∨ Wbtw ℝ (midpoint ℝ x y) b a := by
  have hm : midpoint ℝ x y ∈ affineSpan ℝ ({x, y} : Set ℝ²) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(1 / 2 : ℝ), ?_⟩
    rw [midpoint_eq_smul_add]
    simp [AffineMap.lineMap]
    module
  have hcol_xy_mid : Collinear ℝ ({x, y, midpoint ℝ x y} : Set ℝ²) := by
    have hcol' : Collinear ℝ ({midpoint ℝ x y, x, y} : Set ℝ²) := by
      exact collinear_insert_of_mem_affineSpan_pair
        (p₁ := midpoint ℝ x y) (p₂ := x) (p₃ := y) hm
    have hset : ({midpoint ℝ x y, x, y} : Set ℝ²) = ({x, y, midpoint ℝ x y} : Set ℝ²) := by
      ext p
      simp [or_comm, or_assoc]
    simpa [hset] using hcol'
  have hmid_area : signedArea2 x y (midpoint ℝ x y) = 0 := by
    exact (IsoscelesCounting.signedArea2_eq_zero_iff_collinear x y (midpoint ℝ x y)).2 hcol_xy_mid
  have haP : a ∈ AffineSubspace.perpBisector x y := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    exact haeq
  have hbP : b ∈ AffineSubspace.perpBisector x y := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    exact hbeq
  have hmP : midpoint ℝ x y ∈ AffineSubspace.perpBisector x y := by
    exact AffineSubspace.midpoint_mem_perpBisector x y
  have hane : a -ᵥ midpoint ℝ x y ≠ 0 := by
    intro h
    have ha_mid : a = midpoint ℝ x y := (vsub_eq_zero_iff_eq).mp h
    subst ha_mid
    linarith
  haveI : Fact (Module.finrank ℝ ℝ² = 1 + 1) := ⟨by
    simp⟩
  have hdir_finrank : Module.finrank ℝ (AffineSubspace.perpBisector x y).direction = 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have hxyvec : y -ᵥ x ≠ 0 := by
      intro h
      exact hx ((vsub_eq_zero_iff_eq).mp h).symm
    exact Submodule.finrank_orthogonal_span_singleton (v := y -ᵥ x) hxyvec
  have hdir_le : ℝ ∙ (a -ᵥ midpoint ℝ x y) ≤ (AffineSubspace.perpBisector x y).direction := by
    rw [AffineSubspace.direction_perpBisector]
    exact (Submodule.span_singleton_le_iff_mem _ _).2
      (by simpa [AffineSubspace.direction_perpBisector] using
        (AffineSubspace.vsub_mem_direction haP hmP))
  have hdir_eq : ℝ ∙ (a -ᵥ midpoint ℝ x y) = (AffineSubspace.perpBisector x y).direction := by
    apply Submodule.eq_of_le_of_finrank_eq hdir_le
    rw [finrank_span_singleton hane, hdir_finrank]
  have hbspan : b -ᵥ midpoint ℝ x y ∈ ℝ ∙ (a -ᵥ midpoint ℝ x y) := by
    rw [hdir_eq]
    simpa [AffineSubspace.direction_perpBisector] using
      (AffineSubspace.vsub_mem_direction hbP hmP)
  rcases Submodule.mem_span_singleton.mp hbspan with ⟨r, hr⟩
  have hcol : Collinear ℝ ({a, midpoint ℝ x y, b} : Set ℝ²) := by
    rw [collinear_iff_of_mem (by
      simp : midpoint ℝ x y ∈ ({a, midpoint ℝ x y, b} : Set ℝ²))]
    refine ⟨a -ᵥ midpoint ℝ x y, ?_⟩
    intro p hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨1, ?_⟩
      simp
    · refine ⟨0, ?_⟩
      simp
    · refine ⟨r, ?_⟩
      exact (eq_vadd_iff_vsub_eq p (r • (a -ᵥ midpoint ℝ x y))
        (midpoint ℝ x y)).2 hr.symm
  rcases IsoscelesCounting.collinear_three_wbtw hcol with h1 | h2 | h3
  · exfalso
    let l : ℝ² →ₗ[ℝ] ℝ :=
      { toFun := fun v => signedArea2 x y v - signedArea2 x y 0
        map_add' := by
          intro u v
          simp [signedArea2]
          ring
        map_smul' := by
          intro c v
          simp [signedArea2]
          ring }
    let f : ℝ² →ᵃ[ℝ] ℝ :=
      AffineMap.mk' (fun p => signedArea2 x y p) l 0 (by
        intro p
        simp [l])
    have hmap : Wbtw ℝ (f a) (f (midpoint ℝ x y)) (f b) := Wbtw.map h1 f
    change Wbtw ℝ (signedArea2 x y a) (signedArea2 x y (midpoint ℝ x y))
      (signedArea2 x y b) at hmap
    rw [hmid_area] at hmap
    have hseg : 0 ∈ segment ℝ (signedArea2 x y a) (signedArea2 x y b) := hmap.mem_segment
    rw [segment_eq_image] at hseg
    rcases hseg with ⟨θ, hθ, heq⟩
    have hpos : 0 < (1 - θ) * signedArea2 x y a + θ * signedArea2 x y b := by
      have hθ0 : 0 ≤ θ := hθ.1
      have hθ1 : θ ≤ 1 := hθ.2
      by_cases hθz : θ = 0
      · subst hθz
        simpa using ha_pos
      · by_cases hθ1' : θ = 1
        · subst hθ1'
          simpa using hb_pos
        · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθz)
          have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθ1'
          have h1' : 0 < (1 - θ) * signedArea2 x y a := by
            have h : 0 < 1 - θ := by nlinarith [hθlt]
            exact mul_pos h ha_pos
          have h2' : 0 < θ * signedArea2 x y b := mul_pos hθpos hb_pos
          exact add_pos h1' h2'
    have heq' : (1 - θ) * signedArea2 x y a + θ * signedArea2 x y b = 0 := by
      simpa [smul_eq_mul] using heq
    exact (ne_of_gt hpos) heq'
  · exact Or.inr h2
  · exact Or.inl (Wbtw.symm h3)

/-- CGN6e0: a non-base apex does not lie on the subchord line. -/
theorem CGN6e0_apex_not_on_subchordLine
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A) (har : a ≠ L.points r) (has : a ≠ L.points s) :
    signedArea2 (L.points r) (L.points s) a ≠ 0 := by
  intro hzero
  have hcol : Collinear ℝ ({L.points r, L.points s, a} : Set ℝ²) := by
    exact (IsoscelesCounting.signedArea2_eq_zero_iff_collinear
      (L.points r) (L.points s) a).mp hzero
  have hrA : L.points r ∈ A := hmem r
  have hsA : L.points s ∈ A := hmem s
  have hrs' : L.points r ≠ L.points s := by
    intro h
    exact (ne_of_lt hrs) (L.injective h)
  exact hconv.not_three_collinear hrA hsA haA hrs' har.symm has.symm hcol

/-- CGN6e1: each non-base apex lies strictly on one open side of the
subchord line. -/
theorem CGN6e1_apex_side_dichotomy
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A) (har : a ≠ L.points r) (has : a ≠ L.points s) :
    0 < signedArea2 (L.points r) (L.points s) a ∨
      signedArea2 (L.points r) (L.points s) a < 0 := by
  rcases lt_trichotomy (signedArea2 (L.points r) (L.points s) a) 0 with
    hneg | hzero | hpos
  · exact Or.inr hneg
  · exfalso
    exact CGN6e0_apex_not_on_subchordLine hconv hmem hrs haA har has hzero
  · exact Or.inl hpos

private theorem signedArea2_swap (x y z : ℝ²) :
    signedArea2 x y z = - signedArea2 y x z := by
  unfold signedArea2
  ring

/-- CGN6e2: two apices cannot both lie on the complementary side of the
subchord line. -/
theorem CGN6e2_not_two_apices_on_complementary_side
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s))
    (ha_neg : signedArea2 (L.points r) (L.points s) a < 0)
    (hb_neg : signedArea2 (L.points r) (L.points s) b < 0) :
    False := by
  have hxy : L.points s ≠ L.points r := by
    intro h
    exact (ne_of_lt hrs) (Eq.symm (L.injective h))
  have ha_pos : 0 < signedArea2 (L.points s) (L.points r) a := by
    rw [signedArea2_swap]
    linarith
  have hb_pos : 0 < signedArea2 (L.points s) (L.points r) b := by
    rw [signedArea2_swap]
    linarith
  have hwt :
      Wbtw ℝ (midpoint ℝ (L.points s) (L.points r)) a b ∨
        Wbtw ℝ (midpoint ℝ (L.points s) (L.points r)) b a :=
    CGN6d0_positiveSideBisector_to_wbtw
      (x := L.points s) (y := L.points r)
      hxy haeq.symm hbeq.symm ha_pos hb_pos
  have hsA : L.points s ∈ A := hmem s
  have hrA : L.points r ∈ A := hmem r
  rcases hwt with hwt | hwt
  · have hxne : L.points s ≠ a := by
      exact has.symm
    have hyne : L.points r ≠ a := by
      exact har.symm
    have hbne : b ≠ a := hab.symm
    exact hconv.not_same_ray_perpBisector_of_wbtw hsA hrA haA hbA hxne hyne hbne hwt
  · have hxne : L.points s ≠ b := by
      exact hbs.symm
    have hyne : L.points r ≠ b := by
      exact hbr.symm
    have hbne : a ≠ b := hab
    exact hconv.not_same_ray_perpBisector_of_wbtw hsA hrA hbA haA hxne hyne hbne hwt

/-- CGN6e3: two distinct apices force at least one positive subchain side. -/
theorem CGN6e3_exists_subchain_side_apex
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s)) :
    0 < signedArea2 (L.points r) (L.points s) a ∨
      0 < signedArea2 (L.points r) (L.points s) b := by
  rcases CGN6e1_apex_side_dichotomy hconv hmem hrs haA har has with hapos | haneg
  · exact Or.inl hapos
  · rcases CGN6e1_apex_side_dichotomy hconv hmem hrs hbA hbr hbs with hbpos | hbneg
    · exact Or.inr hbpos
    · exfalso
      exact CGN6e2_not_two_apices_on_complementary_side
        hconv hmem hrs haA hbA hab har has hbr hbs haeq hbeq haneg hbneg

/-- CGN6e4: a positive-side apex determines an indexed witness. -/
theorem CGN6e4_positive_side_apex_to_indexed_witness
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Hord : StrictCapOrder A L)
    {r s : Fin m} (hrs : r < s) {a : ℝ²}
    (haA : a ∈ A)
    (hapos : 0 < signedArea2 (L.points r) (L.points s) a)
    (haeq : dist a (L.points r) = dist a (L.points s)) :
    ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = a ∧
      WitnessesCapEdgeAt L j r s := by
  have hiff :=
    Hord.subchord_open_side_iff_A (r := r) (s := s) hrs (x := a) haA
  rcases hiff.mp hapos with
    ⟨j, hjr, hjs, hjx⟩
  refine ⟨j, hjr, hjs, hjx, ?_⟩
  exact ⟨hjr, hjs, by simpa [hjx] using haeq⟩

/-- CGN6e5: two apices give existence of an indexed witness. -/
theorem CGN6e5_exists_indexedWitness_of_twoApices
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s)) :
    ∃ j : Fin m, WitnessesCapEdgeAt L j r s := by
  rcases CGN6e3_exists_subchain_side_apex hconv hmem hrs haA hbA hab
      har has hbr hbs haeq hbeq with hapos | hbpos
  · rcases CGN6e4_positive_side_apex_to_indexed_witness Hord hrs haA hapos haeq with
      ⟨j, hjr, hjs, hjx, hjw⟩
    exact ⟨j, hjw⟩
  · rcases CGN6e4_positive_side_apex_to_indexed_witness Hord hrs hbA hbpos hbeq with
      ⟨j, hjr, hjs, hjx, hjw⟩
    exact ⟨j, hjw⟩

/-- CGN6e6: an indexed witness is unique. -/
theorem CGN6e6_unique_indexedWitness
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {j k : Fin m}
    (hj : WitnessesCapEdgeAt L j r s)
    (hk : WitnessesCapEdgeAt L k r s) :
    j = k := by
  by_cases hjk : j = k
  · exact hjk
  · exfalso
    have hjA : L.points j ∈ A := hmem j
    have hkA : L.points k ∈ A := hmem k
    have hrA : L.points r ∈ A := hmem r
    have hsA : L.points s ∈ A := hmem s
    have hposj : 0 < signedArea2 (L.points r) (L.points s) (L.points j) := by
      have hiff :=
        Hord.subchord_open_side_iff_A (r := r) (s := s) hrs (x := L.points j) hjA
      exact hiff.mpr ⟨j, hj.1, hj.2.1, rfl⟩
    have hposk : 0 < signedArea2 (L.points r) (L.points s) (L.points k) := by
      have hiff :=
        Hord.subchord_open_side_iff_A (r := r) (s := s) hrs (x := L.points k) hkA
      exact hiff.mpr ⟨k, hk.1, hk.2.1, rfl⟩
    have hxy : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    have hwt :
        Wbtw ℝ (midpoint ℝ (L.points r) (L.points s)) (L.points j) (L.points k) ∨
          Wbtw ℝ (midpoint ℝ (L.points r) (L.points s)) (L.points k) (L.points j) :=
      CGN6d0_positiveSideBisector_to_wbtw
        (x := L.points r) (y := L.points s)
        hxy hj.2.2 hk.2.2 hposj hposk
    have hjne : j ≠ k := hjk
    rcases hwt with hwt | hwt
    · have hxne : L.points r ≠ L.points j := by
        intro h
        exact (ne_of_lt hj.1) (L.injective h)
      have hyne : L.points s ≠ L.points j := by
        intro h
        exact (ne_of_lt hj.2.1) (Eq.symm (L.injective h))
      have hbne : L.points k ≠ L.points j := by
        intro h
        exact hjne (Eq.symm (L.injective h))
      exact hconv.not_same_ray_perpBisector_of_wbtw hrA hsA hjA hkA hxne hyne hbne hwt
    · have hxne : L.points r ≠ L.points k := by
        intro h
        exact (ne_of_lt hk.1) (L.injective h)
      have hyne : L.points s ≠ L.points k := by
        intro h
        exact (ne_of_lt hk.2.1) (Eq.symm (L.injective h))
      have hbne : L.points j ≠ L.points k := by
        intro h
        exact hjne (L.injective h)
      exact hconv.not_same_ray_perpBisector_of_wbtw hrA hsA hkA hjA hxne hyne hbne hwt

/-- CGN6e7: the public ordered-endpoint theorem. -/
theorem CGN6e_indexedWitness_of_twoApices
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Model : MinorCapChainModel L)
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s)) :
    ∃! j : Fin m, WitnessesCapEdgeAt L j r s := by
  rcases CGN6e5_exists_indexedWitness_of_twoApices Hord hconv hmem hrs
      haA hbA hab har has hbr hbs haeq hbeq with ⟨j, hj⟩
  refine ⟨j, hj, ?_⟩
  intro k hk
  exact (CGN6e6_unique_indexedWitness Hord hconv hmem hrs hj hk).symm

end CGN
end IsoscelesCounting
