/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN
import LeanFormalizations.Geometry.IsoscelesCounting.CircumcenterSide
import LeanFormalizations.Geometry.IsoscelesCounting.CircumscribedMECPacket
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexIndepHelpers
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexCyclicOrderConstruct
import LeanFormalizations.Geometry.IsoscelesCounting.OangleBridge
import Mathlib

/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) are
defined in this file. The declarations here are the sanctioned interfaces
consumed by the existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace

namespace IsoscelesCounting
namespace CGN

/-- `CGN4g0`: re-export the global convex-boundary order wrapper under the
CGN-local name consumed by the cap-block extractor. -/
theorem CGN4g0_globalBoundaryOrder_of_convexIndep
    {A : Finset ℝ²} (hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  simpa using IsoscelesCounting.exists_isCcwConvexPolygon_of_convexIndep hA hnoncoll

/-- A support cap `C` presented as a contiguous ordered block inside a global
boundary enumeration `phi`. -/
structure BoundaryCapBlock (A C : Finset ℝ²) {n m : ℕ}
    (phi : Fin n → ℝ²) (L : OrderedCap m) where
  /-- The block has at least two points, so both endpoints exist. -/
  hm : 2 ≤ m
  /-- Left endpoint of the block in the global enumeration. -/
  lo : Fin n
  /-- Right endpoint of the block in the global enumeration. -/
  hi : Fin n
  /-- The global boundary indices are ordered from `lo` to `hi`. -/
  hlohi : lo < hi
  /-- Reindex the local cap order into the global boundary order. -/
  idx : Fin m → Fin n
  /-- The local-to-global reindexing is strictly increasing. -/
  idx_strict : StrictMono idx
  /-- The first local point is the left global endpoint. -/
  idx_first : idx (firstIndex hm) = lo
  /-- The last local point is the right global endpoint. -/
  idx_last : idx (lastIndex hm) = hi
  /-- The reindexing hits exactly the closed global interval `[lo, hi]`. -/
  idx_range_exact : ∀ q : Fin n, (lo ≤ q ∧ q ≤ hi) ↔ ∃ t : Fin m, idx t = q
  /-- Local cap points are the corresponding points of the global enumeration. -/
  points_eq : ∀ t : Fin m, L.points t = phi (idx t)
  /-- The local cap image is exactly the support cap `C`. -/
  cap_image : Finset.univ.image L.points = C
  /-- The support cap lies in the ambient finite set. -/
  cap_subset_A : C ⊆ A
  /-- The global enumeration realizes the ambient finite set. -/
  phi_image : Finset.univ.image phi = A

/-- Local CGN4g helper: once the omitted support vertex is the cut point of
the global boundary order, the opposite support cap is exactly the closed
interval between the two support endpoints. This is not a new public CGN
interface; it packages the `OnArcOpposite` predicate as a finite
interval statement so it can feed `CGN4g1_capBlock_of_supportCap`. -/
private theorem supportCap_interval_of_oppositeFirst
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    {u v w : ℝ²}
    (_hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ IsoscelesCounting.OnArcOpposite u v w x)
    (hv_mem : v ∈ C)
    (hw_mem : w ∈ C)
    {u_idx v_idx w_idx : Fin n}
    (hu : phi u_idx = u)
    (hv : phi v_idx = v)
    (hw : phi w_idx = w)
    (huv : u_idx < v_idx)
    (hvw : v_idx < w_idx) :
    ∀ x : ℝ², x ∈ C ↔ ∃ q : Fin n, v_idx ≤ q ∧ q ≤ w_idx ∧ phi q = x := by
  have huw : u_idx < w_idx := lt_trans huv hvw
  have hu_neg : IsoscelesCounting.signedArea2 u v w < 0 := by
    simpa [hu, hv, hw] using hneg huv hvw
  intro x
  constructor
  · intro hxC
    have hxA : x ∈ A := hC_subset hxC
    rw [← hphi_image] at hxA
    rcases Finset.mem_image.mp hxA with ⟨q, _, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    have hq_arc : IsoscelesCounting.OnArcOpposite u v w (phi q) :=
      (hC_arc (phi q) hqA).1 hxC
    have hnot_lt_left : ¬ q < v_idx := by
      intro hqv
      have hq_neg : IsoscelesCounting.signedArea2 (phi q) v w < 0 := by
        simpa [hv, hw] using hneg hqv hvw
      have hprod_pos : 0 <
          IsoscelesCounting.signedArea2 (phi q) v w * IsoscelesCounting.signedArea2 u v w := by
        have h1 : 0 < -IsoscelesCounting.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -IsoscelesCounting.signedArea2 u v w := by linarith
        have hpos : 0 < (-IsoscelesCounting.signedArea2 (phi q) v w) *
            (-IsoscelesCounting.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold IsoscelesCounting.OnArcOpposite at hq_arc
      linarith
    have hnot_lt_right : ¬ w_idx < q := by
      intro hwq
      have hq_neg_vwx : IsoscelesCounting.signedArea2 v w (phi q) < 0 := by
        simpa [hv, hw] using hneg hvw hwq
      have hcyc : IsoscelesCounting.signedArea2 (phi q) v w =
          IsoscelesCounting.signedArea2 v w (phi q) := by
        simp [IsoscelesCounting.signedArea2]
        ring
      have hq_neg : IsoscelesCounting.signedArea2 (phi q) v w < 0 := by
        rw [hcyc]
        exact hq_neg_vwx
      have hprod_pos : 0 <
          IsoscelesCounting.signedArea2 (phi q) v w * IsoscelesCounting.signedArea2 u v w := by
        have h1 : 0 < -IsoscelesCounting.signedArea2 (phi q) v w := by linarith
        have h2 : 0 < -IsoscelesCounting.signedArea2 u v w := by linarith
        have hpos : 0 < (-IsoscelesCounting.signedArea2 (phi q) v w) *
            (-IsoscelesCounting.signedArea2 u v w) := by positivity
        simpa [neg_mul_neg] using hpos
      unfold IsoscelesCounting.OnArcOpposite at hq_arc
      linarith
    exact ⟨q, le_of_not_gt hnot_lt_left, le_of_not_gt hnot_lt_right, rfl⟩
  · rintro ⟨q, hvle, hqle, rfl⟩
    have hqA : phi q ∈ A := by
      rw [← hphi_image]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
    rcases eq_or_lt_of_le hvle with rfl | hvq
    · simpa [hv] using hv_mem
    rcases eq_or_lt_of_le hqle with rfl | hqw
    · simpa [hw] using hw_mem
    · have hmid_neg : IsoscelesCounting.signedArea2 v (phi q) w < 0 := by
        simpa [hv, hw] using hneg hvq hqw
      have hcyc : IsoscelesCounting.signedArea2 (phi q) v w =
          IsoscelesCounting.signedArea2 v w (phi q) := by
        simp [IsoscelesCounting.signedArea2]
        ring
      have hswap : IsoscelesCounting.signedArea2 v w (phi q) =
          -IsoscelesCounting.signedArea2 v (phi q) w := by
        simp [IsoscelesCounting.signedArea2]
      have hq_pos : 0 < IsoscelesCounting.signedArea2 (phi q) v w := by
        rw [hcyc, hswap]
        linarith
      have hq_arc : IsoscelesCounting.OnArcOpposite u v w (phi q) := by
        unfold IsoscelesCounting.OnArcOpposite
        have hprod_nonpos :
            IsoscelesCounting.signedArea2 (phi q) v w * IsoscelesCounting.signedArea2 u v w ≤ 0 := by
          nlinarith
        exact hprod_nonpos
      exact (hC_arc (phi q) hqA).2 hq_arc

/-- Local CGN4g helper: strict negative signed-area order on increasing
triples is preserved under cyclic shifts of the boundary enumeration.  This is
the finite-order bookkeeping behind "cut the global order at the omitted
support vertex" before applying
`supportCap_interval_of_oppositeFirst`. -/
private theorem hneg_of_cyclicShift
    {n : ℕ} {phi : Fin n → ℝ²}
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (cut : Fin n) :
    ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi (i + cut)) (phi (j + cut)) (phi (k + cut)) < 0 := by
  have hcyc {a b c : ℝ²} :
      IsoscelesCounting.signedArea2 a b c = IsoscelesCounting.signedArea2 c a b := by
    simp [IsoscelesCounting.signedArea2]
    ring
  let bound : ℕ := n - cut.val
  have hval_nowrap {t : Fin n} (ht : (t : ℕ) < bound) :
      ((t + cut : Fin n) : ℕ) = t.val + cut.val := by
    rw [Fin.val_add_eq_ite]
    have hlt : ¬ n ≤ t.val + cut.val := by
      omega
    simp [hlt]
  have hval_wrap {t : Fin n} (ht : bound ≤ (t : ℕ)) :
      ((t + cut : Fin n) : ℕ) = t.val - bound := by
    rw [Fin.val_add_eq_ite]
    have hge : n ≤ t.val + cut.val := by
      omega
    simp [hge]
    omega
  intro i j k hij hjk
  have hik : i < k := lt_trans hij hjk
  by_cases hk : (k : ℕ) < bound
  · have hi : (i : ℕ) < bound := by omega
    have hj : (j : ℕ) < bound := by omega
    have hij' : i + cut < j + cut := by
      change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
      rw [hval_nowrap hi, hval_nowrap hj]
      omega
    have hjk' : j + cut < k + cut := by
      change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
      rw [hval_nowrap hj, hval_nowrap hk]
      omega
    exact hneg hij' hjk'
  · by_cases hj : (j : ℕ) < bound
    · have hi : (i : ℕ) < bound := by omega
      have hk' : bound ≤ (k : ℕ) := by omega
      have hki : k + cut < i + cut := by
        change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
        rw [hval_wrap hk', hval_nowrap hi]
        omega
      have hij' : i + cut < j + cut := by
        change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
        rw [hval_nowrap hi, hval_nowrap hj]
        omega
      have hneg' :
          IsoscelesCounting.signedArea2 (phi (k + cut)) (phi (i + cut)) (phi (j + cut)) < 0 :=
        hneg hki hij'
      simpa [hcyc] using hneg'
    · by_cases hi : (i : ℕ) < bound
      · have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hjk'' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        have hki : k + cut < i + cut := by
          change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
          rw [hval_wrap hk', hval_nowrap hi]
          omega
        have hneg' :
            IsoscelesCounting.signedArea2 (phi (j + cut)) (phi (k + cut)) (phi (i + cut)) < 0 :=
          hneg hjk'' hki
        simpa [hcyc] using hneg'
      · have hi' : bound ≤ (i : ℕ) := by omega
        have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hij' : i + cut < j + cut := by
          change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
          rw [hval_wrap hi', hval_wrap hj']
          omega
        have hjk' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        exact hneg hij' hjk'

/-- `CGN4g1`: package a support cap described as a closed global interval into
the ordered-cap block interface plus the MEC-side packet fields. -/
theorem CGN4g1_capBlock_of_supportCap
    {A C : Finset ℝ²} {n : ℕ} {phi : Fin n → ℝ²}
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    {lo hi : Fin n} (hlohi : lo < hi)
    (hC_interval : ∀ x : ℝ²,
      x ∈ C ↔ ∃ q : Fin n, lo ≤ q ∧ q ≤ hi ∧ phi q = x)
    (center : ℝ²) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hdisk_C : ∀ x, x ∈ C → dist x center ≤ radius)
    (hlo_circle : dist (phi lo) center = radius)
    (hhi_circle : dist (phi hi) center = radius)
    (hcap_side : ∀ x, x ∈ C ->
      0 ≤ IsoscelesCounting.signedArea2 (phi lo) (phi hi) x)
    (hcenter_side :
      IsoscelesCounting.signedArea2 (phi lo) (phi hi) center ≤ 0) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ _Hside : MinorCapSideHypotheses Packet,
      ∃ _Block : BoundaryCapBlock A C phi L,
        _Block.lo = lo ∧ _Block.hi = hi := by
  let I : Finset (Fin n) := Finset.Icc lo hi
  have hlo_mem : lo ∈ I := by
    simp [I, Finset.mem_Icc, hlohi.le]
  have hhi_mem : hi ∈ I := by
    simp [I, Finset.mem_Icc, hlohi.le]
  have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨lo, hlo_mem⟩
  have hm : 2 ≤ I.card := by
    simp [I, Fin.card_Icc]
    omega
  let idx : Fin I.card ↪o Fin n := I.orderEmbOfFin rfl
  let L : OrderedCap I.card := {
    points := fun t => phi (idx t)
    injective := by
      intro i j hij
      apply idx.injective
      exact hphi_inj hij
  }
  have hidx_first : idx (firstIndex hm) = lo := by
    calc
      idx (firstIndex hm) = I.orderEmbOfFin rfl ⟨0, hIpos⟩ := by
        rfl
      _ = I.min' ⟨lo, hlo_mem⟩ := Finset.orderEmbOfFin_zero rfl hIpos
      _ = lo := by
        refine (Finset.min'_eq_iff (s := I) (H := ⟨lo, hlo_mem⟩) (a := lo)).2 ?_
        constructor
        · exact hlo_mem
        · intro q hq
          exact (Finset.mem_Icc.mp hq).1
  have hidx_last : idx (lastIndex hm) = hi := by
    calc
      idx (lastIndex hm) = I.orderEmbOfFin rfl
          ⟨I.card - 1, Nat.sub_lt hIpos (by decide : 0 < (1 : ℕ))⟩ := by
        rfl
      _ = I.max' ⟨hi, hhi_mem⟩ := Finset.orderEmbOfFin_last rfl hIpos
      _ = hi := by
        refine (Finset.max'_eq_iff (s := I) (H := ⟨hi, hhi_mem⟩) (a := hi)).2 ?_
        constructor
        · exact hhi_mem
        · intro q hq
          exact (Finset.mem_Icc.mp hq).2
  have hidx_range_exact : ∀ q : Fin n, (lo ≤ q ∧ q ≤ hi) ↔ ∃ t : Fin I.card, idx t = q := by
    intro q
    constructor
    · intro hq
      have hqI : q ∈ I := by simpa [I, Finset.mem_Icc] using hq
      rw [← Finset.image_orderEmbOfFin_univ (s := I) (h := rfl)] at hqI
      rcases Finset.mem_image.mp hqI with ⟨t, _, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      have htI : idx t ∈ I := Finset.orderEmbOfFin_mem I rfl t
      simpa [ht, I, Finset.mem_Icc] using htI
  have hpoints_eq : ∀ t : Fin I.card, L.points t = phi (idx t) := by
    intro t
    rfl
  have hcap_image : Finset.univ.image L.points = C := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      have hidx_bounds : lo ≤ idx t ∧ idx t ≤ hi :=
        (hidx_range_exact (idx t)).2 ⟨t, rfl⟩
      refine (hC_interval _).2 ?_
      exact ⟨idx t, hidx_bounds.1, hidx_bounds.2, rfl⟩
    · intro hx
      rcases (hC_interval _).1 hx with ⟨q, hloq, hqhi, hqeq⟩
      have hqI : q ∈ I := by simpa [I, Finset.mem_Icc] using And.intro hloq hqhi
      rw [← Finset.image_orderEmbOfFin_univ (s := I) (h := rfl)] at hqI
      rcases Finset.mem_image.mp hqI with ⟨t, _, ht⟩
      have ht' : q = idx t := ht.symm
      have hphi_tx : phi (idx t) = x := by
        simpa [ht'] using hqeq
      refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
      simpa [hpoints_eq t] using hphi_tx
  have hcap_subset_A : C ⊆ A := by
    intro x hxC
    rcases (hC_interval _).1 hxC with ⟨q, _, _, rfl⟩
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  let Block : BoundaryCapBlock A C phi L := {
    hm := hm
    lo := lo
    hi := hi
    hlohi := hlohi
    idx := idx
    idx_strict := (I.orderEmbOfFin rfl).strictMono
    idx_first := hidx_first
    idx_last := hidx_last
    idx_range_exact := hidx_range_exact
    points_eq := hpoints_eq
    cap_image := hcap_image
    cap_subset_A := hcap_subset_A
    phi_image := hphi_image
  }
  let Packet : MecCapPacket A L := {
    hm := hm
    center := center
    radius := radius
    radius_nonneg := hradius_nonneg
    mem_A := by
      intro t
      have htC : L.points t ∈ C := by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      exact Block.cap_subset_A htC
    disk_mem := by
      intro t
      exact hdisk_C (L.points t) <| by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
    first_on_circle := by
      simpa [Block.points_eq, Block.idx_first] using hlo_circle
    last_on_circle := by
      simpa [Block.points_eq, Block.idx_last] using hhi_circle
  }
  let Hside : MinorCapSideHypotheses Packet := {
    cap_side_nonneg := by
      intro t
      have htC : L.points t ∈ C := by
        rw [← Block.cap_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      simpa [Block.points_eq, Block.idx_first, Block.idx_last] using
        hcap_side (L.points t) htC
    center_side_nonpos := by
      simpa [Block.idx_first, Block.idx_last, Block.points_eq] using hcenter_side
  }
  exact ⟨I.card, L, Packet, Hside, Block, rfl, rfl⟩

/-- `CGN4g2`: consecutive local turns are nonpositive once the global boundary
enumeration carries strict negative signed area on increasing triples. -/
theorem CGN4g2_consecutiveTurn_nonpos_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0) :
    ∀ t : ℕ, ∀ ht : t + 2 < m,
      IsoscelesCounting.signedArea2
        (L.points ⟨t, by
          exact lt_trans
            (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0 := by
  intro t ht
  let i0 : Fin m := ⟨t, by
    exact lt_trans
      (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩
  let i1 : Fin m := ⟨t + 1, by
    exact lt_trans
      (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
      ht⟩
  let i2 : Fin m := ⟨t + 2, ht⟩
  have hi01 : i0 < i1 := by
    change t < t + 1
    omega
  have hi12 : i1 < i2 := by
    change t + 1 < t + 2
    omega
  have hidx01 : Block.idx i0 < Block.idx i1 := Block.idx_strict hi01
  have hidx12 : Block.idx i1 < Block.idx i2 := Block.idx_strict hi12
  exact le_of_lt <| by
    simpa [i0, i1, i2, Block.points_eq] using hneg hidx01 hidx12

end CGN

set_option maxHeartbeats 2000000 in
-- The boundary-cap projection normalization expands several basis-coordinate
-- identities and signed-area formulas in one theorem.
/-- Strict endpoint-chord projection order for a boundary cap block.  The proof
follows the closure-plan normalization route in unscaled chord coordinates:
represent every cap point in the basis `u, rightAngleRotation u` around the
chord midpoint, use the MEC disk inequality to bound the first coordinate in
`[-1/2, 1/2]`, use the global signed-area order to force positive second
coordinates on interior vertices, and then compare the two signed-area
inequalities against the endpoint chord to deduce strict first-coordinate
increase. -/
theorem boundaryCap_chordProjection_strict
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : IsoscelesCounting.CGN.OrderedCap m}
    (_hA : IsoscelesCounting.ConvexIndep A)
    (Block : IsoscelesCounting.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (Packet : IsoscelesCounting.CGN.MecCapPacket A L)
    (Hside : IsoscelesCounting.CGN.MinorCapSideHypotheses Packet) :
    ∀ {r s : Fin m}, r < s ->
      0 < inner ℝ (L.points s - L.points r)
        (L.points (IsoscelesCounting.CGN.lastIndex Packet.hm) -
          L.points (IsoscelesCounting.CGN.firstIndex Packet.hm)) := by
  have hhm : Packet.hm = Block.hm := Subsingleton.elim _ _
  let q1 : ℝ² := L.points (IsoscelesCounting.CGN.firstIndex Block.hm)
  let qm : ℝ² := L.points (IsoscelesCounting.CGN.lastIndex Block.hm)
  let u : ℝ² := qm - q1
  have hu : u ≠ 0 := by
    dsimp [u, q1, qm]
    exact sub_ne_zero.mpr <| by
      intro h
      have hidx : IsoscelesCounting.CGN.firstIndex Block.hm = IsoscelesCounting.CGN.lastIndex Block.hm :=
        L.injective h.symm
      have hval : (IsoscelesCounting.CGN.firstIndex Block.hm).val =
          (IsoscelesCounting.CGN.lastIndex Block.hm).val := congrArg Fin.val hidx
      have hval0 : (IsoscelesCounting.CGN.firstIndex Block.hm).val = 0 := by
        simp [IsoscelesCounting.CGN.firstIndex]
      have hval1 : (IsoscelesCounting.CGN.lastIndex Block.hm).val = m - 1 := by
        simp [IsoscelesCounting.CGN.lastIndex]
      rw [hval0, hval1] at hval
      have hm : 2 ≤ m := Block.hm
      omega
  let nvec : ℝ² := IsoscelesCounting.stdOrientation.rightAngleRotation u
  let β := IsoscelesCounting.stdOrientation.basisRightAngleRotation u hu
  let M : ℝ² := midpoint ℝ q1 qm
  let X : Fin m → ℝ := fun t => β.repr (L.points t - M) 0
  let Y : Fin m → ℝ := fun t => β.repr (L.points t - M) 1
  let xc : ℝ := β.repr (Packet.center - M) 0
  let yc : ℝ := β.repr (Packet.center - M) 1
  have hsum_pt : ∀ t : Fin m, L.points t - M = X t • u + Y t • nvec := by
    intro t
    simpa [β, X, Y, nvec] using (β.sum_repr (L.points t - M)).symm
  have hsum_center : Packet.center - M = xc • u + yc • nvec := by
    simpa [β, xc, yc, nvec] using (β.sum_repr (Packet.center - M)).symm
  have hnorm_nvec : ‖nvec‖ = ‖u‖ := by
    simp [nvec]
  have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
    simpa [β, nvec] using (β.repr_self 0)
  have hβu0 : β.repr u 0 = 1 := by
    simp [hβu]
  have hβu1 : β.repr u 1 = 0 := by
    simp [hβu]
  have horth : inner ℝ u nvec = 0 := by
    simp [nvec]
  have horth_rev : inner ℝ nvec u = 0 := by
    simpa [real_inner_comm] using horth
  have harea_u_left : ∀ r : ℝ, IsoscelesCounting.stdOrientation.areaForm u (r • u) = 0 := by
    intro r
    rw [map_smul]
    simp
  have harea_u_right : ∀ r : ℝ,
      IsoscelesCounting.stdOrientation.areaForm u (r • nvec) = r * ‖u‖ ^ 2 := by
    intro r
    rw [map_smul]
    simp [nvec, Orientation.areaForm_rightAngleRotation_right]
  have harea_swap : IsoscelesCounting.stdOrientation.areaForm nvec u = -‖u‖ ^ 2 := by
    have h :=
      IsoscelesCounting.stdOrientation.areaForm_rightAngleRotation_right (x := u) (y := u)
    rw [IsoscelesCounting.stdOrientation.areaForm_swap] at h
    simp [nvec]
  have hsqpos : 0 < ‖u‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - qm) := by
        simp [M]
      _ = (-(1 / 2 : ℝ)) • u := by
        rw [show q1 - qm = -u by
          dsimp [u]
          abel_nf]
        simp [smul_neg]
  have hqm_mid : qm - M = (1 / 2 : ℝ) • u := by
    simp [M, u]
  have hX_first : X (IsoscelesCounting.CGN.firstIndex Block.hm) = -(1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hq1mid
    change X (IsoscelesCounting.CGN.firstIndex Block.hm) =
      (β.repr ((-(1 / 2 : ℝ)) • u)) 0 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hY_first : Y (IsoscelesCounting.CGN.firstIndex Block.hm) = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hq1mid
    change Y (IsoscelesCounting.CGN.firstIndex Block.hm) =
      (β.repr ((-(1 / 2 : ℝ)) • u)) 1 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hX_last : X (IsoscelesCounting.CGN.lastIndex Block.hm) = (1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hqm_mid
    change X (IsoscelesCounting.CGN.lastIndex Block.hm) =
      (β.repr ((1 / 2 : ℝ) • u)) 0 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hY_last : Y (IsoscelesCounting.CGN.lastIndex Block.hm) = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hqm_mid
    change Y (IsoscelesCounting.CGN.lastIndex Block.hm) =
      (β.repr ((1 / 2 : ℝ) • u)) 1 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hcenter_perp : inner ℝ (Packet.center - M) u = 0 := by
    have hdist_eq : dist Packet.center q1 = dist Packet.center qm := by
      simpa [q1, qm, dist_comm] using
        Packet.first_on_circle.trans Packet.last_on_circle.symm
    have hperp : Packet.center ∈ AffineSubspace.perpBisector q1 qm := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      simpa using hdist_eq
    have h :=
      (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
        (c := Packet.center) (p₁ := q1) (p₂ := qm)).mp hperp
    simpa [M] using h
  have hxc_zero : xc = 0 := by
    have hinner : inner ℝ (Packet.center - M) u = xc * ‖u‖ ^ 2 := by
      have horth' : inner ℝ nvec u = 0 := by
        simpa [real_inner_comm] using horth
      calc
        inner ℝ (Packet.center - M) u = inner ℝ (xc • u + yc • nvec) u := by
          rw [hsum_center]
        _ = inner ℝ (xc • u) u + inner ℝ (yc • nvec) u := by
          rw [inner_add_left]
        _ = xc * ‖u‖ ^ 2 + yc * 0 := by
          rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, horth']
          simp
        _ = xc * ‖u‖ ^ 2 := by ring
    nlinarith [hcenter_perp, hinner, hsqpos]
  have hcenter_decomp : Packet.center - M = yc • nvec := by
    rw [hsum_center, hxc_zero, zero_smul, zero_add]
  have hdist_sq_coeff :
      ∀ a b : ℝ, ‖a • u + b • nvec‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u‖ ^ 2 := by
    intro a b
    have horth' : inner ℝ (a • u) (b • nvec) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]
      ring
    have hnorm :
        ‖a • u + b • nvec‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • nvec‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • nvec) horth'
    have hu_part : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
        _ = |a| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    have hn_part : ‖b • nvec‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖b • nvec‖ ^ 2 = (|b| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
        _ = |b| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = b ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    rw [hnorm, hu_part, hn_part]
    ring
  have hpt_minus_q1 : ∀ t : Fin m,
      L.points t - q1 = (X t + 1 / 2) • u + Y t • nvec := by
    intro t
    calc
      L.points t - q1 = (L.points t - M) - (q1 - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X t • u + Y t • nvec) - ((-(1 / 2 : ℝ)) • u) := by
        rw [hsum_pt t, hq1mid]
      _ = (X t • u + (1 / 2 : ℝ) • u) + Y t • nvec := by
        rw [sub_eq_add_neg, neg_smul]
        abel_nf
      _ = (X t + 1 / 2) • u + Y t • nvec := by
        rw [← add_smul]
  have hqm_minus_pt : ∀ t : Fin m,
      qm - L.points t = (1 / 2 - X t) • u + (-Y t) • nvec := by
    intro t
    calc
      qm - L.points t = (qm - M) - (L.points t - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = ((1 / 2 : ℝ) • u) - (X t • u + Y t • nvec) := by
        rw [hqm_mid, hsum_pt t]
      _ = ((1 / 2 : ℝ) • u + (-X t) • u) + (-Y t) • nvec := by
        rw [sub_eq_add_neg, neg_smul, neg_smul]
        abel_nf
      _ = (1 / 2 - X t) • u + (-Y t) • nvec := by
        rw [← add_smul]
        simp [sub_eq_add_neg]
  have hpt_minus_center : ∀ t : Fin m,
      L.points t - Packet.center = X t • u + (Y t - yc) • nvec := by
    intro t
    calc
      L.points t - Packet.center = (L.points t - M) - (Packet.center - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X t • u + Y t • nvec) - (yc • nvec) := by
        rw [hsum_pt t, hcenter_decomp]
      _ = X t • u + (Y t • nvec + -(yc • nvec)) := by
        rw [sub_eq_add_neg]
        abel_nf
      _ = X t • u + (Y t • nvec + (-yc) • nvec) := by
        rw [neg_smul]
      _ = X t • u + (Y t - yc) • nvec := by
        rw [← add_smul]
        simp [sub_eq_add_neg]
  have hq1_minus_center :
      q1 - Packet.center = (-(1 / 2 : ℝ)) • u + (-yc) • nvec := by
    calc
      q1 - Packet.center = (q1 - M) - (Packet.center - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = ((-(1 / 2 : ℝ)) • u) - (yc • nvec) := by
        rw [hq1mid, hcenter_decomp]
      _ = (-(1 / 2 : ℝ)) • u + (-yc) • nvec := by
        simp [sub_eq_add_neg, neg_smul]
  have hdiff_coords : ∀ r s : Fin m,
      L.points s - L.points r = (X s - X r) • u + (Y s - Y r) • nvec := by
    intro r s
    calc
      L.points s - L.points r = (L.points s - M) - (L.points r - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X s • u + Y s • nvec) - (X r • u + Y r • nvec) := by
        rw [hsum_pt s, hsum_pt r]
      _ = (X s • u + (-X r) • u) + (Y s • nvec + (-Y r) • nvec) := by
        rw [sub_eq_add_neg, neg_smul, neg_smul]
        abel_nf
      _ = (X s - X r) • u + (Y s - Y r) • nvec := by
        rw [← add_smul, ← add_smul]
        simp [sub_eq_add_neg]
  have harea_first_last : ∀ t : Fin m,
      IsoscelesCounting.signedArea2 q1 qm (L.points t) = Y t * ‖u‖ ^ 2 := by
    intro t
    calc
      IsoscelesCounting.signedArea2 q1 qm (L.points t) =
          IsoscelesCounting.stdOrientation.areaForm u (L.points t - q1) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u
          ((X t + 1 / 2) • u + Y t • nvec) := by
        rw [hpt_minus_q1 t]
      _ = Y t * ‖u‖ ^ 2 := by
        rw [map_add, harea_u_left (X t + 1 / 2), harea_u_right (Y t)]
        simp
  have harea_first_t_last : ∀ t : Fin m,
      IsoscelesCounting.signedArea2 q1 (L.points t) qm = -Y t * ‖u‖ ^ 2 := by
    intro t
    calc
      IsoscelesCounting.signedArea2 q1 (L.points t) qm =
          IsoscelesCounting.stdOrientation.areaForm (L.points t - q1) (qm - q1) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm
          ((X t + 1 / 2) • u + Y t • nvec) u := by
        rw [hpt_minus_q1 t]
      _ = -Y t * ‖u‖ ^ 2 := by
        simp [map_add, map_smul, harea_swap]
  have harea_first_rs : ∀ r s : Fin m,
      IsoscelesCounting.signedArea2 q1 (L.points r) (L.points s) =
        ((X r + 1 / 2) * Y s - Y r * (X s + 1 / 2)) * ‖u‖ ^ 2 := by
    intro r s
    calc
      IsoscelesCounting.signedArea2 q1 (L.points r) (L.points s) =
          IsoscelesCounting.stdOrientation.areaForm (L.points r - q1) (L.points s - q1) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm
          ((X r + 1 / 2) • u + Y r • nvec)
          ((X s + 1 / 2) • u + Y s • nvec) := by
        rw [hpt_minus_q1 r, hpt_minus_q1 s]
      _ = ((X r + 1 / 2) * Y s - Y r * (X s + 1 / 2)) * ‖u‖ ^ 2 := by
        have hun : IsoscelesCounting.stdOrientation.areaForm u nvec = ‖u‖ ^ 2 := by
          simpa using harea_u_right (1 : ℝ)
        simp [map_add, map_smul, hun, harea_swap]
        ring_nf
  have harea_rs_last : ∀ r s : Fin m,
      IsoscelesCounting.signedArea2 (L.points r) (L.points s) qm =
        ((X r - 1 / 2) * Y s - (X s - 1 / 2) * Y r) * ‖u‖ ^ 2 := by
    intro r s
    calc
      IsoscelesCounting.signedArea2 (L.points r) (L.points s) qm =
          IsoscelesCounting.stdOrientation.areaForm
            (L.points s - L.points r) (qm - L.points r) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm
          ((X s - X r) • u + (Y s - Y r) • nvec)
          ((1 / 2 - X r) • u + (-Y r) • nvec) := by
        rw [hdiff_coords r s, hqm_minus_pt r]
      _ = ((X r - 1 / 2) * Y s - (X s - 1 / 2) * Y r) * ‖u‖ ^ 2 := by
        have hun : IsoscelesCounting.stdOrientation.areaForm u nvec = ‖u‖ ^ 2 := by
          simpa using harea_u_right (1 : ℝ)
        simp [map_add, map_smul, hun, harea_swap]
        ring_nf
  have hcenter_side_coeff : yc ≤ 0 := by
    have hside : IsoscelesCounting.signedArea2 q1 qm Packet.center ≤ 0 := by
      simpa [q1, qm] using Hside.center_side_nonpos
    have harea_center :
        IsoscelesCounting.signedArea2 q1 qm Packet.center = yc * ‖u‖ ^ 2 := by
      calc
        IsoscelesCounting.signedArea2 q1 qm Packet.center =
            IsoscelesCounting.stdOrientation.areaForm u (Packet.center - q1) := by
          rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
        _ = IsoscelesCounting.stdOrientation.areaForm u
            (((1 / 2 : ℝ)) • u + yc • nvec) := by
          have h : Packet.center - q1 = ((1 / 2 : ℝ)) • u + yc • nvec := by
            calc
              Packet.center - q1 = (Packet.center - M) - (q1 - M) := by
                rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
                abel_nf
              _ = (yc • nvec) - ((-(1 / 2 : ℝ)) • u) := by
                rw [hcenter_decomp, hq1mid]
              _ = ((1 / 2 : ℝ)) • u + yc • nvec := by
                rw [sub_eq_add_neg, neg_smul]
                abel_nf
          rw [h]
        _ = yc * ‖u‖ ^ 2 := by
          rw [map_add, harea_u_left (1 / 2), harea_u_right yc]
          simp
    nlinarith [hside, harea_center, hsqpos]
  have hY_nonneg : ∀ t : Fin m, 0 ≤ Y t := by
    intro t
    have hside : 0 ≤ IsoscelesCounting.signedArea2 q1 qm (L.points t) := by
      simpa [q1, qm] using Hside.cap_side_nonneg t
    rw [harea_first_last t] at hside
    nlinarith [hside, hsqpos]
  have hdisk_bound : ∀ t : Fin m,
      X t ^ 2 + (Y t - yc) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 + yc ^ 2 := by
    intro t
    have hdist : dist (L.points t) Packet.center ≤ dist q1 Packet.center := by
      have hdisk : dist (L.points t) Packet.center ≤ Packet.radius := Packet.disk_mem t
      have hq1rad : dist q1 Packet.center = Packet.radius := by
        simpa [q1, hhm] using Packet.first_on_circle
      rw [hq1rad]
      exact hdisk
    have hdist_sq : dist (L.points t) Packet.center ^ 2 ≤ dist q1 Packet.center ^ 2 := by
      have hdist_left_nonneg : 0 ≤ dist (L.points t) Packet.center := dist_nonneg
      have hdist_right_nonneg : 0 ≤ dist q1 Packet.center := dist_nonneg
      nlinarith [hdist, hdist_left_nonneg, hdist_right_nonneg]
    have hleft :
        dist (L.points t) Packet.center ^ 2 =
          (X t ^ 2 + (Y t - yc) ^ 2) * ‖u‖ ^ 2 := by
      rw [dist_eq_norm]
      rw [hpt_minus_center t, hdist_sq_coeff]
    have hright :
        dist q1 Packet.center ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
      rw [dist_eq_norm]
      rw [hq1_minus_center, hdist_sq_coeff]
      ring_nf
    rw [hleft, hright] at hdist_sq
    nlinarith [hdist_sq, hsqpos]
  have hX_sq_bound : ∀ t : Fin m, X t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    intro t
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    nlinarith [hbound, hy, hcenter_side_coeff]
  have hX_lo : ∀ t : Fin m, -(1 / 2 : ℝ) ≤ X t := by
    intro t
    have hsq := hX_sq_bound t
    nlinarith
  have hX_hi : ∀ t : Fin m, X t ≤ (1 / 2 : ℝ) := by
    intro t
    have hsq := hX_sq_bound t
    nlinarith
  have hX_eq_first : ∀ {t : Fin m}, X t = -(1 / 2 : ℝ) → t = IsoscelesCounting.CGN.firstIndex Block.hm := by
    intro t hxt
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    have hyc0 : 2 * yc ≤ 0 := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonpos_of_nonneg_of_nonpos htwo hcenter_side_coeff
    have hyc : 0 ≤ Y t - 2 * yc := by
      exact sub_nonneg.mpr (le_trans hyc0 hy)
    rw [hxt] at hbound
    norm_num at hbound
    have hyzero : Y t = 0 := by
      have hsq_le : (Y t - yc) ^ 2 ≤ yc ^ 2 := hbound
      have hprod_le : Y t * (Y t - 2 * yc) ≤ 0 := by
        rw [show Y t * (Y t - 2 * yc) = (Y t - yc) ^ 2 - yc ^ 2 by ring]
        exact sub_nonpos.mpr hsq_le
      have hprod_nonneg : 0 ≤ Y t * (Y t - 2 * yc) := by
        exact mul_nonneg hy hyc
      have hprod_zero : Y t * (Y t - 2 * yc) = 0 := le_antisymm hprod_le hprod_nonneg
      rcases mul_eq_zero.mp hprod_zero with hY | hyc0
      · exact hY
      · linarith [hy, hcenter_side_coeff, hyc0]
    have hvec : L.points t - M = q1 - M := by
      rw [hsum_pt t, hq1mid, hxt, hyzero]
      simp
    have hpt : L.points t = q1 := by
      exact sub_left_injective hvec
    exact L.injective hpt
  have hX_eq_last : ∀ {t : Fin m}, X t = (1 / 2 : ℝ) → t = IsoscelesCounting.CGN.lastIndex Block.hm := by
    intro t hxt
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    have hyc0 : 2 * yc ≤ 0 := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonpos_of_nonneg_of_nonpos htwo hcenter_side_coeff
    have hyc : 0 ≤ Y t - 2 * yc := by
      exact sub_nonneg.mpr (le_trans hyc0 hy)
    rw [hxt] at hbound
    norm_num at hbound
    have hyzero : Y t = 0 := by
      have hsq_le : (Y t - yc) ^ 2 ≤ yc ^ 2 := hbound
      have hprod_le : Y t * (Y t - 2 * yc) ≤ 0 := by
        rw [show Y t * (Y t - 2 * yc) = (Y t - yc) ^ 2 - yc ^ 2 by ring]
        exact sub_nonpos.mpr hsq_le
      have hprod_nonneg : 0 ≤ Y t * (Y t - 2 * yc) := by
        exact mul_nonneg hy hyc
      have hprod_zero : Y t * (Y t - 2 * yc) = 0 := le_antisymm hprod_le hprod_nonneg
      rcases mul_eq_zero.mp hprod_zero with hY | hyc0
      · exact hY
      · linarith [hy, hcenter_side_coeff, hyc0]
    have hvec : L.points t - M = qm - M := by
      rw [hsum_pt t, hqm_mid, hxt, hyzero]
      simp
    have hpt : L.points t = qm := by
      exact sub_left_injective hvec
    exact L.injective hpt
  have hfirst_lt_of_ne : ∀ {t : Fin m}, t ≠ IsoscelesCounting.CGN.firstIndex Block.hm →
      IsoscelesCounting.CGN.firstIndex Block.hm < t := by
    intro t ht
    change 0 < t.val
    have hne0 : t.val ≠ 0 := by
      intro hzero
      apply ht
      apply Fin.ext
      simpa [IsoscelesCounting.CGN.firstIndex] using hzero
    exact Nat.pos_iff_ne_zero.mpr hne0
  have hlt_last_of_ne : ∀ {t : Fin m}, t ≠ IsoscelesCounting.CGN.lastIndex Block.hm →
      t < IsoscelesCounting.CGN.lastIndex Block.hm := by
    intro t ht
    change t.val < m - 1
    have hne_last : t.val ≠ m - 1 := by
      intro hz
      apply ht
      apply Fin.ext
      simpa [IsoscelesCounting.CGN.lastIndex] using hz
    omega
  have hX_gt_first : ∀ {t : Fin m}, t ≠ IsoscelesCounting.CGN.firstIndex Block.hm →
      -(1 / 2 : ℝ) < X t := by
    intro t ht
    have hlo := hX_lo t
    have hneq : X t ≠ -(1 / 2 : ℝ) := by
      intro h
      exact ht (hX_eq_first h)
    exact lt_of_le_of_ne hlo hneq.symm
  have hX_lt_last : ∀ {t : Fin m}, t ≠ IsoscelesCounting.CGN.lastIndex Block.hm →
      X t < (1 / 2 : ℝ) := by
    intro t ht
    have hhi := hX_hi t
    have hneq : X t ≠ (1 / 2 : ℝ) := by
      intro h
      exact ht (hX_eq_last h)
    exact lt_of_le_of_ne hhi hneq
  have hY_pos_interior : ∀ {t : Fin m},
      IsoscelesCounting.CGN.firstIndex Block.hm < t →
      t < IsoscelesCounting.CGN.lastIndex Block.hm →
      0 < Y t := by
    intro t hfirst hlast
    have hidx_first : Block.idx (IsoscelesCounting.CGN.firstIndex Block.hm) < Block.idx t := by
      simpa [Block.idx_first] using Block.idx_strict hfirst
    have hidx_last : Block.idx t < Block.idx (IsoscelesCounting.CGN.lastIndex Block.hm) := by
      simpa [Block.idx_last] using Block.idx_strict hlast
    have hq1_phi : q1 = phi (Block.idx (IsoscelesCounting.CGN.firstIndex Block.hm)) := by
      simp [q1, Block.points_eq]
    have hqm_phi : qm = phi (Block.idx (IsoscelesCounting.CGN.lastIndex Block.hm)) := by
      simp [qm, Block.points_eq]
    have ht_phi : L.points t = phi (Block.idx t) := by
      simpa using Block.points_eq t
    have hneg_t : IsoscelesCounting.signedArea2 q1 (L.points t) qm < 0 := by
      rw [hq1_phi, ht_phi, hqm_phi]
      exact hneg hidx_first hidx_last
    rw [harea_first_t_last t] at hneg_t
    by_contra hy_not
    have hy_nonpos : Y t ≤ 0 := le_of_not_gt hy_not
    have hnegY_nonneg : 0 ≤ -Y t := by
      exact neg_nonneg.mpr hy_nonpos
    have hprod_nonneg : 0 ≤ (-Y t) * ‖u‖ ^ 2 := by
      exact mul_nonneg hnegY_nonneg (le_of_lt hsqpos)
    exact not_lt_of_ge hprod_nonneg hneg_t
  have hproj_formula : ∀ r s : Fin m,
      inner ℝ (L.points s - L.points r) (qm - q1) =
        (X s - X r) * ‖u‖ ^ 2 := by
    intro r s
    calc
      inner ℝ (L.points s - L.points r) (qm - q1) = inner ℝ (L.points s - L.points r) u := by
        simp [u, qm, q1]
      _ = inner ℝ ((X s - X r) • u + (Y s - Y r) • nvec) u := by rw [hdiff_coords r s]
      _ = (X s - X r) * ‖u‖ ^ 2 := by
        have horth2 : inner ℝ ((Y s - Y r) • nvec) u = 0 := by
          rw [inner_smul_left, horth_rev]
          simp
        calc
          inner ℝ ((X s - X r) • u + (Y s - Y r) • nvec) u =
              (starRingEnd ℝ (X s - X r)) * ‖u‖ ^ 2 + 0 := by
            rw [inner_add_left, horth2, inner_smul_left, real_inner_self_eq_norm_sq]
          _ = (X s - X r) * ‖u‖ ^ 2 := by
            simp
  have hproj_formula' : ∀ r s : Fin m,
      inner ℝ (L.points s - L.points r)
        (L.points (IsoscelesCounting.CGN.lastIndex Packet.hm) -
          L.points (IsoscelesCounting.CGN.firstIndex Packet.hm)) =
        (X s - X r) * ‖u‖ ^ 2 := by
    intro r s
    simpa [q1, qm, hhm] using hproj_formula r s
  intro r s hrs
  by_cases hr_first : r = IsoscelesCounting.CGN.firstIndex Block.hm
  · subst hr_first
    have hs_ne : s ≠ IsoscelesCounting.CGN.firstIndex Block.hm := ne_of_gt hrs
    have hXs : -(1 / 2 : ℝ) < X s := hX_gt_first hs_ne
    have hproj := hproj_formula' (IsoscelesCounting.CGN.firstIndex Block.hm) s
    rw [hX_first] at hproj
    nlinarith [hproj, hsqpos, hXs]
  · by_cases hs_last : s = IsoscelesCounting.CGN.lastIndex Block.hm
    · subst hs_last
      have hr_ne : r ≠ IsoscelesCounting.CGN.lastIndex Block.hm := ne_of_lt hrs
      have hXr : X r < (1 / 2 : ℝ) := hX_lt_last hr_ne
      have hproj := hproj_formula' r (IsoscelesCounting.CGN.lastIndex Block.hm)
      rw [hX_last] at hproj
      nlinarith [hproj, hsqpos, hXr]
    · have hr_int : IsoscelesCounting.CGN.firstIndex Block.hm < r := hfirst_lt_of_ne hr_first
      have hs_int : s < IsoscelesCounting.CGN.lastIndex Block.hm := hlt_last_of_ne hs_last
      have hs_from_first : IsoscelesCounting.CGN.firstIndex Block.hm < s := lt_trans hr_int hrs
      have hr_to_last : r < IsoscelesCounting.CGN.lastIndex Block.hm := lt_trans hrs hs_int
      have hYr : 0 < Y r := hY_pos_interior hr_int hr_to_last
      have hYs : 0 < Y s := hY_pos_interior hs_from_first hs_int
      have hXr_lo : 0 < X r + 1 / 2 := by
        have h := hX_gt_first hr_first
        linarith
      have hXs_lo : 0 < X s + 1 / 2 := by
        have h := hX_gt_first (by
          intro hs0
          exact hs_from_first.ne hs0.symm)
        linarith
      have hXr_hi : 0 < 1 / 2 - X r := by
        have h := hX_lt_last (by
          intro hr0
          exact hr_to_last.ne hr0)
        linarith
      have hXs_hi : 0 < 1 / 2 - X s := by
        have h := hX_lt_last hs_last
        linarith
      have hidx_first_r : Block.idx (IsoscelesCounting.CGN.firstIndex Block.hm) < Block.idx r := by
        simpa [Block.idx_first] using Block.idx_strict hr_int
      have hidx_r_s : Block.idx r < Block.idx s := Block.idx_strict hrs
      have hidx_s_last : Block.idx s < Block.idx (IsoscelesCounting.CGN.lastIndex Block.hm) := by
        simpa [Block.idx_last] using Block.idx_strict hs_int
      have hneg_left : IsoscelesCounting.signedArea2 q1 (L.points r) (L.points s) < 0 := by
        simpa [q1, qm, Block.points_eq, Block.idx_first, Block.idx_last] using
          hneg hidx_first_r hidx_r_s
      have hneg_right : IsoscelesCounting.signedArea2 (L.points r) (L.points s) qm < 0 := by
        simpa [q1, qm, Block.points_eq, Block.idx_first, Block.idx_last] using
          hneg hidx_r_s hidx_s_last
      have hineq_left :
          (X r + 1 / 2) * Y s < Y r * (X s + 1 / 2) := by
        rw [harea_first_rs r s] at hneg_left
        nlinarith [hneg_left, hsqpos]
      have hineq_right :
          Y r / Y s < (1 / 2 - X r) / (1 / 2 - X s) := by
        have htmp :
            (1 / 2 - X s) * Y r < (1 / 2 - X r) * Y s := by
          rw [harea_rs_last r s] at hneg_right
          nlinarith [hneg_right, hsqpos]
        exact (div_lt_div_iff₀ hYs hXs_hi).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
      have hineq_left' :
          (X r + 1 / 2) / (X s + 1 / 2) < Y r / Y s := by
        exact (div_lt_div_iff₀ hXs_lo hYs).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hineq_left
      have hratio :
          (X r + 1 / 2) / (X s + 1 / 2) < (1 / 2 - X r) / (1 / 2 - X s) :=
        lt_trans hineq_left' hineq_right
      have hcross :
          (X r + 1 / 2) * (1 / 2 - X s) < (1 / 2 - X r) * (X s + 1 / 2) := by
        exact (div_lt_div_iff₀ hXs_lo hXs_hi).1 hratio
      have hXrs : X r < X s := by
        nlinarith [hcross]
      have hproj := hproj_formula' r s
      nlinarith [hproj, hsqpos, hXrs]

/-- The positive open side of a local subchord in a boundary block consists
exactly of the globally indexed block vertices strictly between the two local
indices. This is the signed-area order packaging consumed by `CGN4g4`. -/
theorem boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : IsoscelesCounting.CGN.OrderedCap m}
    (Block : IsoscelesCounting.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (_hno3 : ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
      x ≠ y → y ≠ z → x ≠ z →
      IsoscelesCounting.signedArea2 x y z ≠ 0) :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < IsoscelesCounting.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
  have hcyc {a b c : ℝ²} :
      IsoscelesCounting.signedArea2 a b c = IsoscelesCounting.signedArea2 c a b := by
    simp [IsoscelesCounting.signedArea2]
    ring
  have hswap {a b c : ℝ²} :
      IsoscelesCounting.signedArea2 a b c = -IsoscelesCounting.signedArea2 a c b := by
    simp [IsoscelesCounting.signedArea2]
  intro r s hrs x hxA
  constructor
  · intro hpos
    have hidxrs : Block.idx r < Block.idx s := Block.idx_strict hrs
    have hxphi : x ∈ Finset.univ.image phi := by
      rw [Block.phi_image]
      exact hxA
    rcases Finset.mem_image.mp hxphi with ⟨q, -, hqeq⟩
    have hpos' : 0 < IsoscelesCounting.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi q) := by
      simpa [Block.points_eq, hqeq] using hpos
    rcases lt_trichotomy q (Block.idx r) with hq_lt_r | hq_eq_r | hq_gt_r
    · have hneg' : IsoscelesCounting.signedArea2 (phi q) (phi (Block.idx r)) (phi (Block.idx s)) < 0 :=
        hneg hq_lt_r hidxrs
      rw [← hcyc] at hneg'
      linarith
    · subst hq_eq_r
      simp [IsoscelesCounting.signedArea2] at hpos'
    · rcases lt_trichotomy q (Block.idx s) with hq_lt_s | hq_eq_s | hq_gt_s
      · have hq_bounds : Block.lo ≤ q ∧ q ≤ Block.hi := by
          constructor
          · have hlo : Block.lo ≤ Block.idx r := by
              exact ((Block.idx_range_exact (Block.idx r)).2 ⟨r, rfl⟩).1
            exact le_trans hlo hq_gt_r.le
          · have hhi : Block.idx s ≤ Block.hi := by
              exact ((Block.idx_range_exact (Block.idx s)).2 ⟨s, rfl⟩).2
            exact le_trans hq_lt_s.le hhi
        rcases (Block.idx_range_exact q).1 hq_bounds with ⟨j, hjq⟩
        refine ⟨j, ?_, ?_, ?_⟩
        · by_contra hnot
          have hle : j ≤ r := le_of_not_gt hnot
          have : Block.idx j ≤ Block.idx r := Block.idx_strict.monotone hle
          rw [hjq] at this
          exact not_le_of_gt hq_gt_r this
        · by_contra hnot
          have hle : s ≤ j := le_of_not_gt hnot
          have : Block.idx s ≤ Block.idx j := Block.idx_strict.monotone hle
          rw [hjq] at this
          exact not_le_of_gt hq_lt_s this
        · rw [Block.points_eq, hjq, hqeq]
      · subst hq_eq_s
        simp [IsoscelesCounting.signedArea2] at hpos'
      · have hneg' : IsoscelesCounting.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi q) < 0 :=
          hneg hidxrs hq_gt_s
        linarith
  · rintro ⟨j, hrj, hjs, rfl⟩
    have hidxrj : Block.idx r < Block.idx j := Block.idx_strict hrj
    have hidxjs : Block.idx j < Block.idx s := Block.idx_strict hjs
    have hneg' :
        IsoscelesCounting.signedArea2 (phi (Block.idx r)) (phi (Block.idx j)) (phi (Block.idx s)) < 0 :=
      hneg hidxrj hidxjs
    have hpos' :
        0 < IsoscelesCounting.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi (Block.idx j)) := by
      rw [hswap]
      linarith
    simpa [Block.points_eq] using hpos'

namespace CGN

/-- `CGN4g3`: package strict endpoint-chord projection order from the global
signed-area boundary order and the MEC-side packet fields. -/
theorem CGN4g3_chordProjection_strict_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (hA : IsoscelesCounting.ConvexIndep A)
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (Packet : MecCapPacket A L)
    (Hside : MinorCapSideHypotheses Packet) :
    ∀ {r s : Fin m}, r < s ->
      0 < inner ℝ (L.points s - L.points r)
        (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
  intro r s hrs
  simpa using IsoscelesCounting.boundaryCap_chordProjection_strict
    (A := A) (C := C) (phi := phi) (L := L) hA Block hneg Packet Hside hrs

/-- `CGN4g4`: package the local subchord open-side characterization from the
global signed-area order helper. -/
theorem CGN4g4_subchord_open_side_iff_A_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0)
    (hno3 : ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
      x ≠ y → y ≠ z → x ≠ z →
      IsoscelesCounting.signedArea2 x y z ≠ 0) :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < IsoscelesCounting.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
  intro r s hrs x hxA
  simpa using IsoscelesCounting.boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
    (Block := Block) (hneg := hneg) (_hno3 := hno3) (r := r) (s := s) hrs (x := x) hxA

/-- `CGN4g5`: assemble the pure packaging fields into the public strict cap
order interface consumed by CGN6 / CGN7. -/
theorem CGN4g5_strictCapOrder_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hturn : ∀ t : ℕ, ∀ ht : t + 2 < m,
      IsoscelesCounting.signedArea2
        (L.points ⟨t, by
          exact lt_trans
            (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0)
    (hproj : ∀ {r s : Fin m}, r < s →
      0 < inner ℝ (L.points s - L.points r)
        (L.points (lastIndex Block.hm) - L.points (firstIndex Block.hm)))
    (hsideiff : ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < IsoscelesCounting.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x)) :
    StrictCapOrder A L where
  hm := Block.hm
  consecutive_turn_nonpos := hturn
  chord_projection_strict := by
    intro i j hij
    simpa using hproj hij
  subchord_open_side_iff_A := hsideiff

/-- CGN8 step-2 packaging wrapper: turn one support-cap description into the
ordered-cap packet consumed by CGN6 / CGN7.  This theorem is packaging only:
the proof routes through `CGN4g0`-`CGN4g5` and the local cyclic-cut helpers
above. -/
theorem CGN4g_capData_of_supportCap_oriented
    {A C : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ IsoscelesCounting.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : IsoscelesCounting.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ _Hside : MinorCapSideHypotheses Packet,
      ∃ _Hord : StrictCapOrder A L,
        Finset.univ.image L.points = C ∧
          ((L.points (firstIndex Packet.hm) = M.v2 ∧
              L.points (lastIndex Packet.hm) = M.v3) ∨
            (L.points (firstIndex Packet.hm) = M.v3 ∧
              L.points (lastIndex Packet.hm) = M.v2)) := by
  classical
  obtain ⟨n, hn, phi, hphi_inj, hphi_image, hccw⟩ :=
    CGN4g0_globalBoundaryOrder_of_convexIndep hA hnoncoll
  haveI : NeZero n := ⟨by omega⟩
  have hneg : ∀ {i j k : Fin n}, i < j → j < k →
      IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
    intro i j k hij hjk
    have hij_ne : phi i ≠ phi j := by
      intro h
      exact (ne_of_lt hij) (hphi_inj h)
    have hkj_ne : phi k ≠ phi j := by
      intro h
      exact (ne_of_gt hjk) (hphi_inj h)
    have hswap : IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) =
        -IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) := by
      simp [IsoscelesCounting.signedArea2]
      ring
    have hsign : SignType.sign (IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
      rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k) hij_ne hkj_ne]
      exact hccw.sign_oangle hij hjk
    have hpos : 0 < IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) := (sign_eq_one_iff).mp hsign
    linarith
  have hv1A : M.v1 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v1_mem
  have hv2A : M.v2 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v2_mem
  have hv3A : M.v3 ∈ Finset.univ.image phi := by
    rw [hphi_image]
    exact M.v3_mem
  rcases Finset.mem_image.mp hv1A with ⟨i1, _, hi1⟩
  rcases Finset.mem_image.mp hv2A with ⟨i2, _, hi2⟩
  rcases Finset.mem_image.mp hv3A with ⟨i3, _, hi3⟩
  let psi : Fin n → ℝ² := fun t => phi (t + i1)
  have hpsi_inj : Function.Injective psi := by
    intro a b hab
    apply (finCycle i1).injective
    exact hphi_inj hab
  have hpsi_image : Finset.univ.image psi = A := by
    calc
      Finset.univ.image psi = Finset.univ.image (fun t : Fin n => phi (t + i1)) := rfl
      _ = Finset.univ.image phi := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
          exact Finset.mem_image_of_mem phi (Finset.mem_univ _)
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨q, _, rfl⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨q - i1, Finset.mem_univ _, ?_⟩
          rw [show (q - i1) + i1 = q by
            simp]
      _ = A := hphi_image
  have hneg_shift :
      ∀ {i j k : Fin n}, i < j → j < k →
        IsoscelesCounting.signedArea2 (psi i) (psi j) (psi k) < 0 := by
    intro i j k hij hjk
    simpa [psi] using
      (hneg_of_cyclicShift (phi := phi) hneg i1 hij hjk :
        IsoscelesCounting.signedArea2 (phi (i + i1)) (phi (j + i1)) (phi (k + i1)) < 0)
  have hpsi0 : psi 0 = M.v1 := by
    change phi (0 + i1) = M.v1
    simp [hi1]
  have hi2_ne_i1 : i2 ≠ i1 := by
    intro h
    exact M.v12_ne (by simpa [hi1, hi2] using (congrArg phi h).symm)
  have hi3_ne_i1 : i3 ≠ i1 := by
    intro h
    exact M.v13_ne (by simpa [hi1, hi3] using (congrArg phi h).symm)
  have hi2_ne_i3 : i2 ≠ i3 := by
    intro h
    exact M.v23_ne (by simpa [hi2, hi3] using congrArg phi h)
  have hi2_pos : 0 < i2 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi2_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [finCycle] using h)
  have hi3_pos : 0 < i3 - i1 := by
    exact Fin.pos_iff_ne_zero.mpr (by
      intro h0
      apply hi3_ne_i1
      have h := congrArg (fun t : Fin n => t + i1) h0
      simpa [finCycle] using h)
  by_cases h23 : i2 - i1 < i3 - i1
  · have hC_interval :
        ∀ x : ℝ², x ∈ C ↔
          ∃ q : Fin n, i2 - i1 ≤ q ∧ q ≤ i3 - i1 ∧ psi q = x := by
      simpa [psi, hi1, hi2, hi3] using
        supportCap_interval_of_oppositeFirst
          (A := A) (C := C) (phi := psi)
          hpsi_inj hpsi_image hneg_shift hC_subset hC_arc hv_mem hw_mem
          (u_idx := 0) (v_idx := i2 - i1) (w_idx := i3 - i1)
          hpsi0 (by simp [psi, hi2]) (by simp [psi, hi3])
          hi2_pos h23
    have hcap_side :
        ∀ x, x ∈ C →
          0 ≤ IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) x := by
      intro x hxC
      rcases (hC_interval x).1 hxC with ⟨q, hqlo, hqhi, rfl⟩
      rcases eq_or_lt_of_le hqlo with rfl | hqlo'
      · simp [IsoscelesCounting.signedArea2]
      rcases eq_or_lt_of_le hqhi with rfl | hqhi'
      · simp [IsoscelesCounting.signedArea2]
      · have hneg_mid :
          IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi q) (psi (i3 - i1)) < 0 := by
          exact hneg_shift hqlo' hqhi'
        have hswap :
            IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) (psi q) =
              -IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi q) (psi (i3 - i1)) := by
          simp [IsoscelesCounting.signedArea2]
        rw [hswap]
        linarith
    have hcenter_prod :
        0 ≤ IsoscelesCounting.signedArea2 P.center (psi (i2 - i1)) (psi (i3 - i1)) *
          IsoscelesCounting.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) := by
      have hacuteψ :
          0 ≤ ⟪psi (i2 - i1) - psi 0, psi (i3 - i1) - psi 0⟫_ℝ := by
        simpa [psi, hpsi0, hi2, hi3] using hacute
      have h := IsoscelesCounting.center_same_side_as_apex_of_nonobtuse
        (O := P.center) (a := psi (i2 - i1)) (b := psi (i3 - i1)) (c := psi 0)
        (r := P.radius)
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        (by simpa [hpsi0] using P.moser_on_boundary_1)
        hacuteψ
      simpa [mul_comm] using h
    have hcenter_neg :
        IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center ≤ 0 := by
      have hbase_neg :
          IsoscelesCounting.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 :=
        hneg_shift hi2_pos h23
      have hcyc :
          IsoscelesCounting.signedArea2 P.center (psi (i2 - i1)) (psi (i3 - i1)) =
            IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center := by
        simp [IsoscelesCounting.signedArea2]
        ring
      rw [hcyc] at hcenter_prod
      by_contra hpos
      push Not at hpos
      have : IsoscelesCounting.signedArea2 (psi (i2 - i1)) (psi (i3 - i1)) P.center *
          IsoscelesCounting.signedArea2 (psi 0) (psi (i2 - i1)) (psi (i3 - i1)) < 0 :=
        mul_neg_of_pos_of_neg hpos hbase_neg
      linarith
    obtain ⟨m, L, Packet, Hside, Block, hlo, hhi⟩ :=
      CGN4g1_capBlock_of_supportCap
        (A := A) (C := C) (phi := psi)
        hpsi_inj hpsi_image h23 hC_interval
        P.center P.radius (le_of_lt P.radius_pos)
        (fun x hx => P.disk_contains_A x (hC_subset hx))
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        hcap_side hcenter_neg
    have hturn := CGN4g2_consecutiveTurn_nonpos_of_capBlock Block hneg_shift
    have hproj :
        ∀ {r s : Fin m}, r < s →
          0 < inner ℝ (L.points s - L.points r)
            (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
      intro r s hrs
      exact CGN4g3_chordProjection_strict_of_capBlock
        (A := A) (C := C) (phi := psi) (L := L) hA Block hneg_shift Packet Hside hrs
    have hno3 :
        ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
          x ≠ y → y ≠ z → x ≠ z →
          IsoscelesCounting.signedArea2 x y z ≠ 0 := by
      intro x y z hx hy hz hxy hyz hxz hzero
      have hcol : Collinear ℝ ({x, y, z} : Set ℝ²) :=
        (IsoscelesCounting.signedArea2_eq_zero_iff_collinear x y z).1 hzero
      exact False.elim (IsoscelesCounting.ConvexIndep.not_three_collinear hA hx hy hz hxy hxz hyz hcol)
    have hsideiff :
        ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
          (0 < IsoscelesCounting.signedArea2 (L.points r) (L.points s) x ↔
            ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
      intro r s hrs
      exact fun {x} hx => by
        simpa using
          (CGN4g4_subchord_open_side_iff_A_of_capBlock
            (A := A) (C := C) (phi := psi) (L := L)
            Block hneg_shift hno3 (r := r) (s := s) hrs (x := x) hx)
    let Hord : StrictCapOrder A L :=
      CGN4g5_strictCapOrder_of_capBlock Block hturn hproj hsideiff
    have hfirst_v2 : L.points (firstIndex Packet.hm) = M.v2 := by
      calc
        L.points (firstIndex Packet.hm)
            = psi (Block.idx (firstIndex Packet.hm)) := by
                exact Block.points_eq (firstIndex Packet.hm)
        _ = psi Block.lo := by rw [Block.idx_first]
        _ = psi (i2 - i1) := by rw [hlo]
        _ = M.v2 := by simp [psi, hi2]
    have hlast_v3 : L.points (lastIndex Packet.hm) = M.v3 := by
      calc
        L.points (lastIndex Packet.hm)
            = psi (Block.idx (lastIndex Packet.hm)) := by
                exact Block.points_eq (lastIndex Packet.hm)
        _ = psi Block.hi := by rw [Block.idx_last]
        _ = psi (i3 - i1) := by rw [hhi]
        _ = M.v3 := by simp [psi, hi3]
    exact ⟨m, L, Packet, Hside, Hord, Block.cap_image, Or.inl ⟨hfirst_v2, hlast_v3⟩⟩
  · have h32 : i3 - i1 < i2 - i1 := lt_of_le_of_ne (le_of_not_gt h23) (by
        intro hEq
        exact hi2_ne_i3 (by
          have h := congrArg (fun t : Fin n => t + i1) hEq
          simpa [finCycle] using h.symm))
    have hswap_arc :
        ∀ x ∈ A, x ∈ C ↔ IsoscelesCounting.OnArcOpposite M.v1 M.v3 M.v2 x := by
      intro x hxA
      rw [hC_arc x hxA]
      unfold IsoscelesCounting.OnArcOpposite
      have hx :
          IsoscelesCounting.signedArea2 x M.v3 M.v2 = -IsoscelesCounting.signedArea2 x M.v2 M.v3 := by
        simp [IsoscelesCounting.signedArea2]
      have hu :
          IsoscelesCounting.signedArea2 M.v1 M.v3 M.v2 = -IsoscelesCounting.signedArea2 M.v1 M.v2 M.v3 := by
        simp [IsoscelesCounting.signedArea2]
      rw [hx, hu, neg_mul_neg]
    have hacute' : 0 ≤ ⟪M.v3 - M.v1, M.v2 - M.v1⟫_ℝ := by
      simpa [real_inner_comm] using hacute
    have hC_interval :
        ∀ x : ℝ², x ∈ C ↔
          ∃ q : Fin n, i3 - i1 ≤ q ∧ q ≤ i2 - i1 ∧ psi q = x := by
      simpa [psi, hi1, hi2, hi3] using
        supportCap_interval_of_oppositeFirst
          (A := A) (C := C) (phi := psi)
          hpsi_inj hpsi_image hneg_shift hC_subset hswap_arc hw_mem hv_mem
          (u_idx := 0) (v_idx := i3 - i1) (w_idx := i2 - i1)
          hpsi0 (by simp [psi, hi3]) (by simp [psi, hi2])
          hi3_pos h32
    have hcap_side :
        ∀ x, x ∈ C →
          0 ≤ IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) x := by
      intro x hxC
      rcases (hC_interval x).1 hxC with ⟨q, hqlo, hqhi, rfl⟩
      rcases eq_or_lt_of_le hqlo with rfl | hqlo'
      · simp [IsoscelesCounting.signedArea2]
      rcases eq_or_lt_of_le hqhi with rfl | hqhi'
      · simp [IsoscelesCounting.signedArea2]
      · have hneg_mid :
          IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi q) (psi (i2 - i1)) < 0 := by
          exact hneg_shift hqlo' hqhi'
        have hswap :
            IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) (psi q) =
              -IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi q) (psi (i2 - i1)) := by
          simp [IsoscelesCounting.signedArea2]
        rw [hswap]
        linarith
    have hcenter_prod :
        0 ≤ IsoscelesCounting.signedArea2 P.center (psi (i3 - i1)) (psi (i2 - i1)) *
          IsoscelesCounting.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) := by
      have hacuteψ :
          0 ≤ ⟪psi (i3 - i1) - psi 0, psi (i2 - i1) - psi 0⟫_ℝ := by
        simpa [psi, hpsi0, hi2, hi3, real_inner_comm] using hacute'
      have h := IsoscelesCounting.center_same_side_as_apex_of_nonobtuse
        (O := P.center) (a := psi (i3 - i1)) (b := psi (i2 - i1)) (c := psi 0)
        (r := P.radius)
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        (by simpa [hpsi0] using P.moser_on_boundary_1)
        hacuteψ
      simpa [mul_comm] using h
    have hcenter_neg :
        IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center ≤ 0 := by
      have hbase_neg :
          IsoscelesCounting.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
        hneg_shift hi3_pos h32
      have hcyc :
          IsoscelesCounting.signedArea2 P.center (psi (i3 - i1)) (psi (i2 - i1)) =
            IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center := by
        simp [IsoscelesCounting.signedArea2]
        ring
      rw [hcyc] at hcenter_prod
      by_contra hpos
      push Not at hpos
      have : IsoscelesCounting.signedArea2 (psi (i3 - i1)) (psi (i2 - i1)) P.center *
          IsoscelesCounting.signedArea2 (psi 0) (psi (i3 - i1)) (psi (i2 - i1)) < 0 :=
        mul_neg_of_pos_of_neg hpos hbase_neg
      linarith
    obtain ⟨m, L, Packet, Hside, Block, hlo, hhi⟩ :=
      CGN4g1_capBlock_of_supportCap
        (A := A) (C := C) (phi := psi)
        hpsi_inj hpsi_image h32 hC_interval
        P.center P.radius (le_of_lt P.radius_pos)
        (fun x hx => P.disk_contains_A x (hC_subset hx))
        (by simpa [psi, hi3] using P.moser_on_boundary_3)
        (by simpa [psi, hi2] using P.moser_on_boundary_2)
        hcap_side hcenter_neg
    have hturn := CGN4g2_consecutiveTurn_nonpos_of_capBlock Block hneg_shift
    have hproj :
        ∀ {r s : Fin m}, r < s →
          0 < inner ℝ (L.points s - L.points r)
            (L.points (lastIndex Packet.hm) - L.points (firstIndex Packet.hm)) := by
      intro r s hrs
      exact CGN4g3_chordProjection_strict_of_capBlock
        (A := A) (C := C) (phi := psi) (L := L) hA Block hneg_shift Packet Hside hrs
    have hno3 :
        ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
          x ≠ y → y ≠ z → x ≠ z →
          IsoscelesCounting.signedArea2 x y z ≠ 0 := by
      intro x y z hx hy hz hxy hyz hxz hzero
      have hcol : Collinear ℝ ({x, y, z} : Set ℝ²) :=
        (IsoscelesCounting.signedArea2_eq_zero_iff_collinear x y z).1 hzero
      exact False.elim (IsoscelesCounting.ConvexIndep.not_three_collinear hA hx hy hz hxy hxz hyz hcol)
    have hsideiff :
        ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
          (0 < IsoscelesCounting.signedArea2 (L.points r) (L.points s) x ↔
            ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
      intro r s hrs
      exact fun {x} hx => by
        simpa using
          (CGN4g4_subchord_open_side_iff_A_of_capBlock
            (A := A) (C := C) (phi := psi) (L := L)
            Block hneg_shift hno3 (r := r) (s := s) hrs (x := x) hx)
    let Hord : StrictCapOrder A L :=
      CGN4g5_strictCapOrder_of_capBlock Block hturn hproj hsideiff
    have hfirst_v3 : L.points (firstIndex Packet.hm) = M.v3 := by
      calc
        L.points (firstIndex Packet.hm)
            = psi (Block.idx (firstIndex Packet.hm)) := by
                exact Block.points_eq (firstIndex Packet.hm)
        _ = psi Block.lo := by rw [Block.idx_first]
        _ = psi (i3 - i1) := by rw [hlo]
        _ = M.v3 := by simp [psi, hi3]
    have hlast_v2 : L.points (lastIndex Packet.hm) = M.v2 := by
      calc
        L.points (lastIndex Packet.hm)
            = psi (Block.idx (lastIndex Packet.hm)) := by
                exact Block.points_eq (lastIndex Packet.hm)
        _ = psi Block.hi := by rw [Block.idx_last]
        _ = psi (i2 - i1) := by rw [hhi]
        _ = M.v2 := by simp [psi, hi2]
    exact ⟨m, L, Packet, Hside, Hord, Block.cap_image, Or.inr ⟨hfirst_v3, hlast_v2⟩⟩

/-- Drop the endpoint-orientation packet when only the bare cap data is
needed. -/
theorem CGN4g_capData_of_supportCap
    {A C : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²))
    (hC_subset : C ⊆ A)
    (hC_arc : ∀ x ∈ A, x ∈ C ↔ IsoscelesCounting.OnArcOpposite M.v1 M.v2 M.v3 x)
    (hv_mem : M.v2 ∈ C)
    (hw_mem : M.v3 ∈ C)
    (P : IsoscelesCounting.CircumscribedMECPacket A M)
    (hacute : 0 ≤ ⟪M.v2 - M.v1, M.v3 - M.v1⟫_ℝ) :
    ∃ m, ∃ L : OrderedCap m,
      ∃ Packet : MecCapPacket A L,
      ∃ _Hside : MinorCapSideHypotheses Packet,
      ∃ _Hord : StrictCapOrder A L,
        Finset.univ.image L.points = C := by
  rcases CGN4g_capData_of_supportCap_oriented
      (A := A) (C := C) (M := M) hA hnoncoll hC_subset hC_arc hv_mem hw_mem P hacute with
    ⟨m, L, Packet, Hside, Hord, hLC, _⟩
  exact ⟨m, L, Packet, Hside, Hord, hLC⟩

end CGN
end IsoscelesCounting
