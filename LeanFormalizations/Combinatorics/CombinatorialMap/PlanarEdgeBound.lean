/-
Euler's formula and the planar (multi)graph edge bound.

On the vendored `CombinatorialMap` carrier, this proves the simple-graph edge
bound `e ≤ 3v − 6` from Euler's formula `v − e + f = 2` (genus zero), via the
standard counting argument:
  * each edge of the fixed-point-free involution `edgePerm` is two darts, so the
    dart count is `2e` (`two_card_edge_eq_card_darts`);
  * the faces partition the darts, so their lengths sum to the dart count
    (`sum_faceLength_eq_card_darts`), giving `2e = Σ face lengths`;
  * in a simple, connected map with at least three vertices every face has length
    at least three (`three_le_faceLength`), so `2e ≥ 3f`.
It then lifts that to the multigraph bound `e ≤ M·(3v − 6)` for a multigraph
whose edges carry multiplicity at most `M` over their endpoint pairs
(`planar_multigraph_edge_bound`).

The connectivity and simplicity predicates (`Connected`, `IsSimple`) enter the
counting theorems only as hypotheses, so the development is robust to a different
encoding of them.
-/
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import Mathlib.Data.Sym.Sym2

open scoped BigOperators

namespace CombinatorialMap

variable {D : Type*} {M : CombinatorialMap D}

noncomputable instance instFintypeFaceSameCycle [Fintype D] {w : D} :
    Fintype {u | M.facePerm.SameCycle w u} :=
  Fintype.ofFinite _

/-- The length of a face is the number of darts in its `facePerm` orbit. -/
noncomputable def Face.length [Fintype D] [DecidableEq D] (f : M.Face) : ℕ :=
  Quotient.lift (fun w ↦ Fintype.card {u | M.facePerm.SameCycle w u}) (fun w u h ↦ by
    simp [Set.coe_setOf]
    suffices M.facePerm.SameCycle w = M.facePerm.SameCycle u by
      classical
      simp_all only
      convert rfl
    ext
    exact ⟨h.symm.trans, h.trans⟩) f

/-- The map is connected: any two darts are mutually reachable by single
`vertexPerm`/`vertexPerm⁻¹`/`edgePerm` steps. Encoded as `ReflTransGen` over the
one-step relation, which avoids `MulAction.orbit` plumbing and yields a free
invariant-set closure lemma. (`edgePerm⁻¹ = edgePerm` since it is an involution,
so no separate `edgePerm⁻¹` step is needed.) -/
def Connected (M : CombinatorialMap D) : Prop :=
  ∀ d d' : D, Relation.ReflTransGen
    (fun a b ↦ b = M.vertexPerm a ∨ b = M.vertexPerm⁻¹ a ∨ b = M.edgePerm a) d d'

/-- A `SameCycle` class of the fixed-point-free involution `edgePerm` is
`{d, edgePerm d}`. (Duplicates `sameCycle_edgePerm_iff` below.) -/
lemma edge_sameCycle_iff (d d' : D) :
    M.edgePerm.SameCycle d d' ↔ d' = d ∨ d' = M.edgePerm d := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    have hsq : M.edgePerm ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact M.edge_mul_edge_eq_one
    rcases Int.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · left
      have : M.edgePerm ^ i = 1 := by rw [hk, ← two_mul, zpow_mul, hsq, one_zpow]
      rw [this] at hi; simpa using hi.symm
    · right
      have : M.edgePerm ^ i = M.edgePerm := by
        rw [hk, zpow_add, zpow_one, zpow_mul, hsq, one_zpow, one_mul]
      rw [this] at hi; exact hi.symm
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)

/-- The unordered pair of endpoint vertices of an edge. -/
noncomputable def Edge.ends (e : M.Edge) : Sym2 M.Vertex :=
  Quotient.lift
    (fun d : D => s(M.Vertex_mk d, M.Vertex_mk (M.edgePerm d)))
    (by
      intro d d' (h : (Equiv.Perm.SameCycle.setoid M.edgePerm).r d d')
      have h' : M.edgePerm.SameCycle d d' := h
      rcases (edge_sameCycle_iff d d').1 h' with rfl | rfl
      · rfl
      · simp only []
        have : M.edgePerm (M.edgePerm d) = d := M.edgePerm_involutive d
        rw [this]; exact Sym2.eq_swap)
    e

lemma Edge.ends_mk (d : D) :
    Edge.ends (M.Edge_mk d) = s(M.Vertex_mk d, M.Vertex_mk (M.edgePerm d)) := rfl

/-- The map is simple: no loops (no edge's endpoint pair is a diagonal) and no
parallel edges (`Edge.ends` is injective). -/
def IsSimple (M : CombinatorialMap D) : Prop :=
  (∀ e : M.Edge, ¬ (Edge.ends e).IsDiag) ∧
  Function.Injective (Edge.ends (M := M))

noncomputable instance instFintypeEdgeSameCycle [Fintype D] {w : D} :
    Fintype {u | M.edgePerm.SameCycle w u} :=
  Fintype.ofFinite _

lemma edgePerm_sq : M.edgePerm ^ (2 : ℤ) = 1 := by
  rw [show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast, sq]
  exact M.edge_mul_edge_eq_one

/-- The only zpowers of the involution `edgePerm` are `1` and `edgePerm`. -/
lemma edgePerm_zpow_dichotomy (i : ℤ) :
    M.edgePerm ^ i = 1 ∨ M.edgePerm ^ i = M.edgePerm := by
  rcases Int.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    subst hk
    rw [show k + k = 2 * k from (two_mul k).symm, zpow_mul, edgePerm_sq, one_zpow]
  · right
    subst hk
    rw [zpow_add, zpow_mul, edgePerm_sq, one_zpow, one_mul, zpow_one]

/-- `edgePerm` has no fixed point. -/
lemma edgePerm_apply_ne (d : D) : M.edgePerm d ≠ d := by
  intro h
  exact M.isEmpty_fixedPoints_edgePerm.elim ⟨d, h⟩

/-- Lemma A (membership form). -/
lemma sameCycle_edgePerm_iff (d u : D) :
    M.edgePerm.SameCycle d u ↔ u = d ∨ u = M.edgePerm d := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases M.edgePerm_zpow_dichotomy i with h | h
    · left; rw [h]; rfl
    · right; rw [h]
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)

/-- Lemma A (set form). -/
lemma setOf_sameCycle_edgePerm (d : D) :
    {u | M.edgePerm.SameCycle d u} = {d, M.edgePerm d} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact M.sameCycle_edgePerm_iff d u

/-- Lemma A (ncard). Each `edgePerm`-orbit has exactly two darts. -/
lemma ncard_setOf_sameCycle_edgePerm (d : D) :
    ({u | M.edgePerm.SameCycle d u}).ncard = 2 := by
  rw [M.setOf_sameCycle_edgePerm d]
  exact Set.ncard_pair (M.edgePerm_apply_ne d).symm

/-- Lemma A (Fintype.card form). -/
lemma card_setOf_sameCycle_edgePerm [Fintype D] (d : D) :
    Fintype.card {u | M.edgePerm.SameCycle d u} = 2 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    M.ncard_setOf_sameCycle_edgePerm d]

/-- `Edge_mk` agrees on `a` and `d₀` iff they share an `edgePerm` cycle. -/
lemma edge_mk_eq_iff (a d₀ : D) :
    M.Edge_mk a = M.Edge_mk d₀ ↔ M.edgePerm.SameCycle d₀ a := by
  rw [Edge_mk, Edge_mk, Quotient.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Equality of a two-sided face label is independent of the chosen dart
representative of an edge class.

For a fixed-point-free involution, an edge class has exactly the two dart
representatives `d₀` and `edgePerm d₀`. Thus a label equality between the two
faces incident to `d₀` transports to any representative of the same edge class,
possibly reversing the equality. -/
theorem edge_face_label_eq_of_edge_mk_eq {β : Type*} (label : M.Face → β)
    {d d₀ : D}
    (hE : M.Edge_mk d = M.Edge_mk d₀)
    (hlabel : label (M.Face_mk d₀) = label (M.Face_mk (M.edgePerm d₀))) :
    label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) := by
  have hsc : M.edgePerm.SameCycle d₀ d := (M.edge_mk_eq_iff d d₀).mp hE
  rcases (M.sameCycle_edgePerm_iff d₀ d).mp hsc with hd | hd
  · rw [hd]
    exact hlabel
  · rw [hd, M.edgePerm_involutive d₀]
    exact hlabel.symm

/-- Each fiber of `Edge_mk` has exactly two elements. -/
lemma card_edge_fiber [Fintype D] (e : M.Edge)
    [DecidablePred fun a : D => M.Edge_mk a = e] :
    ({a ∈ (Finset.univ : Finset D) | M.Edge_mk a = e}).card = 2 := by
  obtain ⟨d₀, rfl⟩ := Quotient.exists_rep e
  have hset : {a ∈ (Finset.univ : Finset D) | M.Edge_mk a = M.Edge_mk d₀}
      = {u | M.edgePerm.SameCycle d₀ u}.toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      Set.mem_setOf_eq]
    exact M.edge_mk_eq_iff a d₀
  rw [hset, Set.toFinset_card, M.card_setOf_sameCycle_edgePerm d₀]

/-- Every edge orbit of the fixed-point-free involution `edgePerm` has two
darts, so the dart count is twice the edge count. -/
theorem two_card_edge_eq_card_darts [Fintype D] :
    2 * Fintype.card M.Edge = Fintype.card D := by
  classical
  have hmaps : Set.MapsTo (M.Edge_mk) (↑(Finset.univ : Finset D))
      (↑(Finset.univ : Finset M.Edge)) := fun _ _ => Finset.mem_univ _
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun e _ => M.card_edge_fiber e),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- `Face_mk` agrees on `a` and `d₀` iff they share a `facePerm` cycle. -/
lemma face_mk_eq_iff (a d₀ : D) :
    M.Face_mk a = M.Face_mk d₀ ↔ M.facePerm.SameCycle d₀ a := by
  rw [Face_mk, Face_mk, Quotient.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Each fiber of `Face_mk` has cardinality equal to that face's length. -/
lemma card_face_fiber [Fintype D] [DecidableEq D] (f : M.Face)
    [DecidablePred fun a : D => M.Face_mk a = f] :
    ({a ∈ (Finset.univ : Finset D) | M.Face_mk a = f}).card = Face.length f := by
  obtain ⟨d₀, rfl⟩ := Quotient.exists_rep f
  have hset : {a ∈ (Finset.univ : Finset D) | M.Face_mk a = M.Face_mk d₀}
      = {u | M.facePerm.SameCycle d₀ u}.toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      Set.mem_setOf_eq]
    exact M.face_mk_eq_iff a d₀
  rw [hset, Set.toFinset_card]
  rfl

/-- Face orbits partition the darts, so their lengths sum to the dart count. -/
theorem sum_faceLength_eq_card_darts [Fintype D] [DecidableEq D] :
    ∑ f : M.Face, f.length = Fintype.card D := by
  classical
  have hmaps : Set.MapsTo (M.Face_mk) (↑(Finset.univ : Finset D))
      (↑(Finset.univ : Finset M.Face)) := fun _ _ => Finset.mem_univ _
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at h
  rw [h]
  exact Finset.sum_congr rfl (fun f _ => (M.card_face_fiber f).symm)

/-- Combining the per-edge and per-face dart counts: twice the edge count is
the total face length. -/
theorem two_card_edge_eq_sum_faceLength [Fintype D] [DecidableEq D] :
    2 * Fintype.card M.Edge = ∑ f : M.Face, f.length := by
  rw [two_card_edge_eq_card_darts, ← sum_faceLength_eq_card_darts]

/-- `σ(φ x) = α x`, from `facePerm = vertexPerm⁻¹ * edgePerm`. -/
lemma vertex_face_eq_edge (x : D) : M.vertexPerm (M.facePerm x) = M.edgePerm x := by
  rw [M.facePerm_eq, Equiv.Perm.mul_apply]; simp

/-- A set closed under `vertexPerm`/`vertexPerm⁻¹`/`edgePerm`
contains everything reachable from one of its members. -/
lemma reachable_mem_of_invariant {S : Set D} (d₀ : D) (hd₀ : d₀ ∈ S)
    (hσ : ∀ a ∈ S, M.vertexPerm a ∈ S) (hσ' : ∀ a ∈ S, M.vertexPerm⁻¹ a ∈ S)
    (hα : ∀ a ∈ S, M.edgePerm a ∈ S) :
    ∀ d', Relation.ReflTransGen
      (fun a b ↦ b = M.vertexPerm a ∨ b = M.vertexPerm⁻¹ a ∨ b = M.edgePerm a) d₀ d' →
      d' ∈ S := by
  intro d' h
  induction h with
  | refl => exact hd₀
  | tail _ step ih =>
      rcases step with h | h | h <;> subst h
      · exact hσ _ ih
      · exact hσ' _ ih
      · exact hα _ ih

/-- In a simple, connected map with at least three vertices, every face has
length at least three. -/
theorem three_le_faceLength [Fintype D] [DecidableEq D]
    (hs : M.IsSimple) (hc : M.Connected) (hv : 3 ≤ Fintype.card M.Vertex)
    (f : M.Face) : 3 ≤ f.length := by
  obtain ⟨w, rfl⟩ := Quotient.exists_rep f
  change 3 ≤ Face.length (M.Face_mk w)
  by_contra hlt
  push Not at hlt
  have hL1 : 1 ≤ Face.length (M.Face_mk w) := by
    change 1 ≤ Fintype.card {u | M.facePerm.SameCycle w u}
    have : Nonempty {u | M.facePerm.SameCycle w u} := ⟨⟨w, Equiv.Perm.SameCycle.refl _ _⟩⟩
    exact Fintype.card_pos
  have hcases : Face.length (M.Face_mk w) = 1 ∨ Face.length (M.Face_mk w) = 2 := by omega
  rcases hcases with h | h
  · have hfix : M.facePerm w = w := by
      have hL' : Fintype.card {u | M.facePerm.SameCycle w u} = 1 := h
      have hsub : Subsingleton {u | M.facePerm.SameCycle w u} :=
        Fintype.card_le_one_iff_subsingleton.mp hL'.le
      have e1 : ({u | M.facePerm.SameCycle w u} : Set D) w := Equiv.Perm.SameCycle.refl _ _
      have e2 : ({u | M.facePerm.SameCycle w u} : Set D) (M.facePerm w) :=
        Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
      have : (⟨w, e1⟩ : {u | M.facePerm.SameCycle w u}) = ⟨M.facePerm w, e2⟩ :=
        Subsingleton.elim _ _
      exact (Subtype.mk_eq_mk.mp this).symm
    have hloop : M.edgePerm w = M.vertexPerm w := by
      have h0 : M.vertexPerm⁻¹ (M.edgePerm w) = w := by
        rw [M.facePerm_eq, Equiv.Perm.mul_apply] at hfix; exact hfix
      have := congrArg M.vertexPerm h0
      simpa using this
    have hsc : M.vertexPerm.SameCycle w (M.edgePerm w) := by
      rw [hloop]; exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
    have hvv : M.Vertex_mk w = M.Vertex_mk (M.edgePerm w) := Quotient.eq''.mpr hsc
    refine hs.1 (M.Edge_mk w) ?_
    rw [Edge.ends_mk, hvv]
    exact Sym2.mk_isDiag_iff.mpr rfl
  · have hL' : Fintype.card {u | M.facePerm.SameCycle w u} = 2 := h
    have hne : M.facePerm w ≠ w := by
      intro hfix
      have hall : ∀ u ∈ {u | M.facePerm.SameCycle w u}, u = w := fun u hu =>
        (Equiv.Perm.SameCycle.eq_of_left hu hfix).symm
      have hsub : Subsingleton {u | M.facePerm.SameCycle w u} :=
        ⟨fun a b => Subtype.ext (by rw [hall a.1 a.2, hall b.1 b.2])⟩
      have hle : Fintype.card {u | M.facePerm.SameCycle w u} ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    have h2 : M.facePerm (M.facePerm w) = w := by
      have hncard : {u | M.facePerm.SameCycle w u}.ncard = 2 := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]; exact hL'
      have hsubset : ({w, M.facePerm w} : Set D) ⊆ {u | M.facePerm.SameCycle w u} := by
        intro x hx
        rcases hx with rfl | rfl
        · exact Equiv.Perm.SameCycle.refl _ _
        · exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
      have hpair : ({w, M.facePerm w} : Set D).ncard = 2 := Set.ncard_pair (Ne.symm hne)
      have heq : ({w, M.facePerm w} : Set D) = {u | M.facePerm.SameCycle w u} :=
        Set.eq_of_subset_of_ncard_le hsubset (by rw [hncard, hpair]) (Set.toFinite _)
      have hmem : M.facePerm (M.facePerm w) ∈ ({w, M.facePerm w} : Set D) := by
        rw [heq]
        exact Equiv.Perm.sameCycle_apply_right.mpr
          (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
      rcases hmem with hh | hh
      · exact hh
      · exact absurd (M.facePerm.injective hh) hne
    rcases eq_or_ne (M.Edge_mk w) (M.Edge_mk (M.facePerm w)) with hsame | hdiff
    · have hI : M.facePerm w = M.edgePerm w := by
        have : M.edgePerm.SameCycle w (M.facePerm w) := Quotient.eq''.mp hsame
        rcases (edge_sameCycle_iff w (M.facePerm w)).1 this with hh | hh
        · exact absurd hh hne
        · exact hh
      have hσw : M.vertexPerm w = w := by
        have step : M.vertexPerm w = M.edgePerm (M.facePerm w) := by
          have := vertex_face_eq_edge (M := M) (M.facePerm w)
          rw [h2] at this; exact this
        rw [step, hI]; exact M.edgePerm_involutive w
      have hσαw : M.vertexPerm (M.edgePerm w) = M.edgePerm w := by
        have := vertex_face_eq_edge (M := M) w; rwa [hI] at this
      have hσiw : M.vertexPerm⁻¹ w = w := by
        rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hσw]
      have hσiαw : M.vertexPerm⁻¹ (M.edgePerm w) = M.edgePerm w := by
        rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hσαw]
      set S : Set D := {w, M.edgePerm w} with hSdef
      have hwS : w ∈ S := Set.mem_insert _ _
      have hαwS : M.edgePerm w ∈ S := Set.mem_insert_of_mem _ rfl
      have hσinv : ∀ a ∈ S, M.vertexPerm a ∈ S := by
        intro a ha; rcases ha with rfl | rfl
        · rw [hσw]; exact hwS
        · rw [hσαw]; exact hαwS
      have hσ'inv : ∀ a ∈ S, M.vertexPerm⁻¹ a ∈ S := by
        intro a ha; rcases ha with rfl | rfl
        · rw [hσiw]; exact hwS
        · rw [hσiαw]; exact hαwS
      have hαinv : ∀ a ∈ S, M.edgePerm a ∈ S := by
        intro a ha; rcases ha with rfl | rfl
        · exact hαwS
        · rw [M.edgePerm_involutive w]; exact hwS
      have huniv : ∀ d : D, d ∈ S := fun d =>
        reachable_mem_of_invariant w hwS hσinv hσ'inv hαinv d (hc w d)
      have hcard2 : Fintype.card M.Vertex ≤ 2 := by
        have hsurj : Function.Surjective (M.Vertex_mk) := Quotient.mk_surjective
        have hsub : (Set.univ : Set M.Vertex) ⊆ {M.Vertex_mk w, M.Vertex_mk (M.edgePerm w)} := by
          intro v _
          obtain ⟨d, rfl⟩ := hsurj v
          rcases huniv d with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
        have hcardeq : Fintype.card M.Vertex = (Set.univ : Set M.Vertex).ncard := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card]
        rw [hcardeq]
        calc (Set.univ : Set M.Vertex).ncard
            ≤ ({M.Vertex_mk w, M.Vertex_mk (M.edgePerm w)} : Set M.Vertex).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ 2 := by
              rcases eq_or_ne (M.Vertex_mk w) (M.Vertex_mk (M.edgePerm w)) with hh | hh
              · rw [hh]; simp [Set.ncard_singleton]
              · rw [Set.ncard_pair hh]
      omega
    · have hep1 : M.vertexPerm.SameCycle (M.facePerm w) (M.edgePerm w) := by
        rw [← vertex_face_eq_edge (M := M) w]
        exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
      have hep2 : M.vertexPerm.SameCycle w (M.edgePerm (M.facePerm w)) := by
        have key : M.edgePerm (M.facePerm w) = M.vertexPerm w := by
          have := vertex_face_eq_edge (M := M) (M.facePerm w)
          rw [h2] at this; exact this.symm
        rw [key]; exact Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)
      have hends : Edge.ends (M.Edge_mk w) = Edge.ends (M.Edge_mk (M.facePerm w)) := by
        rw [Edge.ends_mk, Edge.ends_mk]
        have e1 : M.Vertex_mk (M.facePerm w) = M.Vertex_mk (M.edgePerm w) := Quotient.eq''.mpr hep1
        have e2 : M.Vertex_mk w = M.Vertex_mk (M.edgePerm (M.facePerm w)) := Quotient.eq''.mpr hep2
        rw [e1, ← e2]; exact Sym2.eq_swap
      exact hdiff (hs.2 hends)

/-- The simple-planar edge bound `e ≤ 3v − 6`, over `ℤ`, from Euler's formula
(`IsPlanar`), the face-length bound (`three_le_faceLength`), and
`2e = Σ face lengths` (`two_card_edge_eq_sum_faceLength`). -/
theorem card_edge_le_three_card_vertex_sub_six [Fintype D]
    (hp : M.IsPlanar) (hc : M.Connected) (hs : M.IsSimple)
    (hv : 3 ≤ Fintype.card M.Vertex) :
    (Fintype.card M.Edge : ℤ) ≤ 3 * Fintype.card M.Vertex - 6 := by
  classical
  have hEuler : (Fintype.card M.Vertex : ℤ) - Fintype.card M.Edge + Fintype.card M.Face = 2 := hp
  have h3 : 2 * Fintype.card M.Edge = ∑ f : M.Face, f.length :=
    two_card_edge_eq_sum_faceLength
  have hsum : Fintype.card M.Face * 3 ≤ ∑ f : M.Face, f.length := by
    rw [← Finset.card_univ]
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset M.Face)
      (fun f => f.length) 3 (fun f _ => three_le_faceLength hs hc hv f)
    simpa [smul_eq_mul, Nat.mul_comm] using this
  have h3' : (2 * Fintype.card M.Edge : ℤ) = ((∑ f : M.Face, f.length : ℕ) : ℤ) := by
    exact_mod_cast h3
  have hsum' : (Fintype.card M.Face * 3 : ℤ) ≤ ((∑ f : M.Face, f.length : ℕ) : ℤ) := by
    exact_mod_cast hsum
  omega

end CombinatorialMap

/-- Abstract carrier produced after one edge per crossing is deleted and the
drawing is forgotten, retaining only the finite multigraph data needed by the
planar edge bound. -/
structure AbstractPlanarizedMultigraph where
  Vertex : Type
  Edge : Type
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  edgeVerts : Edge → Sym2 Vertex

attribute [instance] AbstractPlanarizedMultigraph.vertexFintype
attribute [instance] AbstractPlanarizedMultigraph.edgeFintype

open Classical in
/-- Multiplicity cap on unordered vertex pairs. -/
def PairMultiplicityBound (G : AbstractPlanarizedMultigraph) (M : ℕ) : Prop :=
  ∀ uv : Sym2 G.Vertex,
    ((Finset.univ.filter fun e : G.Edge ↦ G.edgeVerts e = uv).card) ≤ M

open Classical in
/-- Internal planarity witness: the present-pair simple collapse of `G` embeds
into some simple, connected, genus-zero (Euler = 2) `CombinatorialMap` on the
same vertex set, whose edge count dominates the number of distinct vertex pairs
that occur as endpoints in `G`. Existential — the actual map is constructed by
the drawing→map bridge, so the multigraph bound stays a pure counting
consequence of the simple-graph bound. -/
def HasGenusZeroSimplePlanarization (G : AbstractPlanarizedMultigraph) : Prop :=
  ∃ (D : Type) (_ : Fintype D) (Mp : CombinatorialMap D),
    Mp.IsSimple ∧ Mp.Connected ∧ Mp.IsPlanar ∧
    Fintype.card Mp.Vertex = Fintype.card G.Vertex ∧
    (Finset.univ.image G.edgeVerts).card ≤ Fintype.card Mp.Edge

/-- The planar multigraph edge bound `e ≤ M·(3v−6)`: a mechanical
multiplicity-collapse consequence of the simple-graph bound `e ≤ 3v−6` for the
witness map. The fibers of `edgeVerts` over the present pairs are each bounded by
`M`; there are at most `3v−6` present pairs
(`card_edge_le_three_card_vertex_sub_six` on the witness map); multiply. -/
theorem planar_multigraph_edge_bound (G : AbstractPlanarizedMultigraph) (M : ℕ)
    (hpl : HasGenusZeroSimplePlanarization G)
    (hmult : PairMultiplicityBound G M)
    (hv : 3 ≤ Fintype.card G.Vertex) :
    Fintype.card G.Edge ≤ M * (3 * Fintype.card G.Vertex - 6) := by
  classical
  set v := Fintype.card G.Vertex with hvdef
  set s := (Finset.univ.image G.edgeVerts).card with hsdef
  -- Step 1: fiberwise count of edges over their endpoint pairs.
  have hmaps : Set.MapsTo G.edgeVerts (↑(Finset.univ : Finset G.Edge))
      (↑(Finset.univ.image G.edgeVerts)) := by
    intro e _
    exact Finset.mem_image_of_mem _ (Finset.mem_univ e)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at hfib
  -- Step 2: each fiber is bounded by `M`.
  have hbound : Fintype.card G.Edge ≤ M * s := by
    rw [hfib]
    calc ∑ p ∈ Finset.univ.image G.edgeVerts,
              (Finset.univ.filter fun e : G.Edge ↦ G.edgeVerts e = p).card
        ≤ ∑ _p ∈ Finset.univ.image G.edgeVerts, M :=
          Finset.sum_le_sum (fun p _ => hmult p)
      _ = M * s := by
          rw [Finset.sum_const, smul_eq_mul, hsdef, Nat.mul_comm]
  -- Step 3: the simple-graph edge bound on the planar witness gives `s ≤ 3v − 6`.
  obtain ⟨D, _hD, Mp, hSimple, hConn, hPlanar, hVcard, hEcard⟩ := hpl
  have hEU4 : (Fintype.card Mp.Edge : ℤ) ≤ 3 * Fintype.card Mp.Vertex - 6 :=
    CombinatorialMap.card_edge_le_three_card_vertex_sub_six (M := Mp) hPlanar hConn hSimple
      (by rw [hVcard]; omega)
  have hsle : s ≤ 3 * v - 6 := by
    have hVZ : (Fintype.card Mp.Vertex : ℤ) = v := by rw [hVcard]
    have hEZ : (s : ℤ) ≤ Fintype.card Mp.Edge := by exact_mod_cast hEcard
    have : (s : ℤ) ≤ 3 * v - 6 := by
      calc (s : ℤ) ≤ Fintype.card Mp.Edge := hEZ
        _ ≤ 3 * Fintype.card Mp.Vertex - 6 := hEU4
        _ = 3 * v - 6 := by rw [hVZ]
    omega
  -- Step 4: combine.
  calc Fintype.card G.Edge ≤ M * s := hbound
    _ ≤ M * (3 * v - 6) := Nat.mul_le_mul_left M hsle
