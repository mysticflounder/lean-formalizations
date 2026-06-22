/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultigraph
import LeanFormalizations.PachDeZeeuw.CrossingLemma.BadPointBounds
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23

/-!
# The Edge-B E1 incidence bound (`edgeB_incidence_le_numEdges_add`)

The curve analogue of the line-case incidence-edge bound
`incidences_le_numEdges_add` (`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:1024`),
which provides the endgame hypothesis `he : I ≤ G.numEdges + n` consumed by the
M-form incidence endgame `incidence_bound_of_multigraphCrossingLemma`
(`MultigraphIncidenceEndgame.lean:154`).

For a finite family `Γ` of post-shear irreducible curve carriers (`EdgeBCurve d`)
and a finite point set `P`, the total point–curve incidence count over the curve
images `Γ.image (fun H => evalPlaneZeroSet H.1)` is bounded by the multigraph's
edge count plus a slack `c d * Γ.card`, with `c d` a polynomial in `d` only.

## Incidence-count definition (the `I` consumed by the endgame)

`I := PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))`, the
Pach–Sharir point–curve incidence count over the `ℝ × ℝ`-chart zero sets. This is
exactly the `I` that `edgeB_crossingInput` feeds the endgame (design
`docs/corollary24-edgeB-assembly-construction-design.md` §5.2, §3.3).

## The explicit `c d` (good-x / bad-x split)

Per curve `H ∈ Γ`, `|{p ∈ P : p ∈ γ_H}|` splits by `p.1 ∈ Bad H.1`:

* **bad-x** (`p.1 ∈ Bad H.1`): `≤ (Bad H.1).ncard · d ≤ ((d+1)^5+d)·d`. Each bad
  x-value has fibre `≤ d` (`fibre_card_le_at_bad`); there are `≤ (d+1)^5+d` bad
  x-values (`decomp_D1_bad_ncard`). The product bound is
  `card_le_mul_card_image_of_maps_to` over the first coordinate.
* **good-x** (`p.1 ∉ Bad H.1`): by `goodIntervalsBundle_covers` every good-x
  P-point lies in some (bracket, rank) class; per class the points are
  `pointsOnSheet` and `|pointsOnSheet| ≤ |edgesOnSheet| + 1` (`length_edgesOnSheet`).
  Summing over the `#classKeys` classes (`= |goodIntervalsBundle| · (d+1)`) gives
  `≤ numEdges_H + #classKeys` with `#classKeys ≤ ((d+1)^5+d+1)·(d+1)` (number of
  good-locus components `= (Bad H.1).ncard + 1 ≤ (d+1)^5+d+1`, times `d+1` ranks).

Folding both per-curve terms over `Γ`:

  `c d := ((d+1)^5 + d + 1) * (d+1) + ((d+1)^5 + d) * d`.

This is the honest constant from the actual proof: the good-x slack carries the
`(d+1)` rank factor (each good-locus component splits into `≤ d+1` sheets, each
contributing one `+1`), so the first summand is `#components · (d+1)`, not
`#components`. (The coverage-fix doc's `((d+1)^5+d+1)` omits the rank factor; the
assembly-design §3.2 `(|Bad h|+1)·(d+1)` is the correct count and the one used
here.) `c d` is a polynomial in `d` only, as `Corollary24Statement` permits.

See `docs/corollary24-edgeB-e1-build.md` for the build record.

GLUE over already-landed, axiom-clean leaves; the only genuinely new content is the
list-cover counting lemma `card_le_sum_map_filter_of_cover` and the two `≤ d`
fibre-rank helpers, all elementary.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma
open scoped Classical

/-! ### List-arithmetic helpers -/

/-- `(L.map (fun x => f x + 1)).sum = (L.map f).sum + L.length`: the per-element `+1`s
sum to the list length. Elementary induction; used to split the per-class `+1` slack
off the edge-count sum. -/
theorem sum_map_add_one {β : Type*} (L : List β) (f : β → ℕ) :
    (L.map (fun x => f x + 1)).sum = (L.map f).sum + L.length := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

/-! ### A list-cover counting lemma -/

/-- **List-cover card bound.** If every element of a finset `S` satisfies `pred b`
for *some* bucket `b` in a list `L`, then `|S|` is at most the sum over `L` of the
per-bucket counts `|S.filter (pred b)|`. Buckets may overlap; the bound is one-sided
(`≤`). Proof by induction on `L`: an element not in the head bucket has its covering
witness in the tail, so the induction hypothesis applies to the tail-restricted
finset. This is the curve analogue of "sort all incident points into chains", but
with the chains keyed by a *list* of (bracket, rank) classes that may overlap, so no
disjointness or decidable-on-`Σ'` bucket index is needed. -/
theorem card_le_sum_map_filter_of_cover {α β : Type*} (S : Finset α)
    (L : List β) (pred : β → α → Prop) [∀ b, DecidablePred (pred b)]
    (hcover : ∀ p ∈ S, ∃ b ∈ L, pred b p) :
    S.card ≤ (L.map (fun b => (S.filter (pred b)).card)).sum := by
  induction L generalizing S with
  | nil =>
    -- No buckets ⟹ no element is covered ⟹ `S = ∅`.
    have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨b, hb, _⟩ := hcover p hp
      exact (List.not_mem_nil) hb
    simp [hS]
  | cons b L ih =>
    -- Split `S` by membership in the head bucket `pred b`.
    have hsplit : (S.filter (pred b)).card + (S.filter (fun a => ¬ pred b a)).card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (pred b)
    -- Every element NOT in the head bucket is covered by the tail `L`.
    have hcover' : ∀ p ∈ S.filter (fun a => ¬ pred b a), ∃ b' ∈ L, pred b' p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨b', hb', hpb'⟩ := hcover p hp.1
      rcases List.mem_cons.mp hb' with hbeq | hmem
      · exact absurd (hbeq ▸ hpb') hp.2
      · exact ⟨b', hmem, hpb'⟩
    have hih := ih (S.filter (fun a => ¬ pred b a)) hcover'
    -- Tail-restricted per-bucket counts are `≤` the unrestricted per-bucket counts.
    have htail :
        (L.map (fun b' => ((S.filter (fun a => ¬ pred b a)).filter (pred b')).card)).sum
          ≤ (L.map (fun b' => (S.filter (pred b')).card)).sum := by
      apply List.sum_le_sum
      intro b' _
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      exact Finset.filter_subset _ _
    rw [List.map_cons, List.sum_cons]
    calc S.card = (S.filter (pred b)).card + (S.filter (fun a => ¬ pred b a)).card := hsplit.symm
      _ ≤ (S.filter (pred b)).card
            + (L.map (fun b' => ((S.filter (fun a => ¬ pred b a)).filter (pred b')).card)).sum :=
          Nat.add_le_add_left hih _
      _ ≤ (S.filter (pred b)).card + (L.map (fun b' => (S.filter (pred b')).card)).sum :=
          Nat.add_le_add_left htail _

/-! ### Fibre-rank `≤ d` helpers (good and bad x) -/

/-- The fibre over **any** `x` of a post-shear irreducible curve is finite. The slice
`Specialized1 x h` is nonzero for every `x` (`specialized1_ne_zero_of_isPrimitive`
applied to `curry1_isPrimitive_of_irreducible`), so its real root set — which equals
the fibre (`fibre_eq_setOf_isRoot`) — is finite. This is the finiteness companion to
the landed `fibre_card_le_at_bad` (which exports only the `≤ d` count). -/
theorem fibre_finite_at_bad (h : PlanePoly) (hirr : Irreducible h)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) (x : ℝ) : (Fibre h x).Finite := by
  have hprim := curry1_isPrimitive_of_irreducible h hirr hpy
  have hne : Specialized1 x h ≠ 0 := specialized1_ne_zero_of_isPrimitive h x hprim
  have hset : Fibre h x = ↑(Specialized1 x h).roots.toFinset := by
    rw [fibre_eq_setOf_isRoot]
    ext y
    simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, Finset.mem_coe,
      Polynomial.mem_roots hne, Polynomial.IsRoot.def]
  rw [hset]
  exact (Specialized1 x h).roots.toFinset.finite_toSet

/-- The sheet rank `sheetRank h x y = (Fibre h x ∩ Iio y).ncard` is at most `d` for a
post-shear irreducible curve of total degree `≤ d`, over **any** `x`. The points-below
set is a subset of the fibre, which is finite (`fibre_finite_at_bad`) with `≤ d` points
(`fibre_card_le_at_bad`). Hence every rank that occurs lands in `range (d+1)`. -/
theorem sheetRank_le_at_bad (h : PlanePoly) (hirr : Irreducible h)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) {d : ℕ} (hdeg : h.totalDegree ≤ d)
    (x y : ℝ) : sheetRank h x y ≤ d := by
  rw [sheetRank]
  calc (Fibre h x ∩ Set.Iio y).ncard
      ≤ (Fibre h x).ncard :=
        Set.ncard_le_ncard Set.inter_subset_left (fibre_finite_at_bad h hirr hpy x)
    _ ≤ d := fibre_card_le_at_bad h hirr hpy hdeg x

/-! ### The bad-x incident set and its per-curve bound -/

/-- The bad-`x` incident points of `P` on curve `H`: in `P`, on the curve, with
`x`-coordinate in `Bad H.1`. -/
noncomputable def badIncident {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    Finset (ℝ × ℝ) :=
  P.filter (fun p => p ∈ evalPlaneZeroSet H.1 ∧ p.1 ∈ Bad H.1)

/-- Over a fixed bad `x = b`, the bad-`x` incident points with first coordinate `b`
number at most `d`: they inject (via the second coordinate) into the fibre
`Fibre H.1 b`, which is finite (`fibre_finite_at_bad`) with `≤ d` points
(`fibre_card_le_at_bad`). -/
theorem badIncident_fibre_card_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) (b : ℝ) :
    ((badIncident P H).filter (fun p => p.1 = b)).card ≤ d := by
  set Qb := (badIncident P H).filter (fun p => p.1 = b) with hQb
  have hfin : (Fibre H.1 b).Finite := fibre_finite_at_bad H.1 H.2.1 H.2.2.2 b
  -- `Prod.snd` is injective on `Qb` (all points share first coordinate `b`).
  have hinj : Set.InjOn Prod.snd (Qb : Set (ℝ × ℝ)) := by
    intro p hp q hq hpq
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    have : p.1 = q.1 := by rw [hp.2, hq.2]
    exact Prod.ext this hpq
  -- The second-coordinate image lands in the (finite) fibre.
  have himg : Qb.image Prod.snd ⊆ hfin.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hpQb, hpy⟩ := hy
    rw [hQb, Finset.mem_filter, badIncident, Finset.mem_filter] at hpQb
    obtain ⟨⟨_, hpZ, _⟩, hpb⟩ := hpQb
    rw [Set.Finite.mem_toFinset]
    -- `p = (b, y)` is on the curve, so `y ∈ Fibre H.1 b`.
    rw [Fibre, Set.mem_setOf_eq]
    rw [mem_evalPlaneZeroSet] at hpZ
    rw [← hpb, ← hpy]
    exact hpZ
  calc Qb.card = (Qb.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ hfin.toFinset.card := Finset.card_le_card himg
    _ = (Fibre H.1 b).ncard := (Set.ncard_eq_toFinset_card (Fibre H.1 b) hfin).symm
    _ ≤ d := fibre_card_le_at_bad H.1 H.2.1 H.2.2.2 H.2.2.1 b

/-- **Per-curve bad-`x` bound.** The bad-`x` incident points on `H` number at most
`((d+1)^5 + d) · d`: the first-coordinate map sends `badIncident P H` into the finite
bad set (card `≤ (d+1)^5+d` by `decomp_D1_bad_ncard`), each fibre having `≤ d` points
(`badIncident_fibre_card_le`), via `card_le_mul_card_image_of_maps_to`. -/
theorem badIncident_card_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (badIncident P H).card ≤ ((d + 1) ^ 5 + d) * d := by
  set badFin := (edgeBCurve_bad_finite H).toFinset with hbadFin
  -- Every bad-`x` incident point's first coordinate is a bad x-value.
  have hmaps : ∀ p ∈ badIncident P H, p.1 ∈ badFin := by
    intro p hp
    rw [badIncident, Finset.mem_filter] at hp
    rw [hbadFin, Set.Finite.mem_toFinset]
    exact hp.2.2
  have hcard :=
    Finset.card_le_mul_card_image_of_maps_to (s := badIncident P H) (t := badFin)
      (f := Prod.fst) hmaps d
      (fun b _ => badIncident_fibre_card_le P H b)
  -- `|badFin| = (Bad H.1).ncard ≤ (d+1)^5 + d`.
  have hbadcard : badFin.card ≤ (d + 1) ^ 5 + d := by
    rw [hbadFin, ← Set.ncard_eq_toFinset_card (Bad H.1) (edgeBCurve_bad_finite H)]
    exact decomp_D1_bad_ncard H.1 H.2.1 H.2.2.1 H.2.2.2
  calc (badIncident P H).card ≤ d * badFin.card := hcard
    _ ≤ d * ((d + 1) ^ 5 + d) := Nat.mul_le_mul_left _ hbadcard
    _ = ((d + 1) ^ 5 + d) * d := Nat.mul_comm _ _

/-! ### The good-x incident set and its per-curve edge bound -/

/-- The good-`x` incident points of `P` on curve `H`: in `P`, on the curve
`evalPlaneZeroSet H.1`, with `x`-coordinate off `Bad H.1`. -/
noncomputable def goodIncident {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    Finset (ℝ × ℝ) :=
  P.filter (fun p => p ∈ evalPlaneZeroSet H.1 ∧ p.1 ∉ Bad H.1)

/-- The (bracket, rank) class predicate: on the curve, `x` in the bracket interval,
sheet rank equal to the class rank. The `goodIncident`-filter by this predicate is a
subset of the class's `pointsOnSheet`, so its card is bounded by `|edgesOnSheet| + 1`. -/
def predBracket {d : ℕ} (H : EdgeBCurve d)
    (key : Σ' ab : ℝ × ℝ, PProd (∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) ℕ)
    (p : ℝ × ℝ) : Prop :=
  p ∈ evalPlaneZeroSet H.1 ∧ p.1 ∈ Set.Ioo key.1.1 key.1.2 ∧ sheetRank H.1 p.1 p.2 = key.2.2

/-- Per class, the good-`x` incident points in that (bracket, rank) class are a subset
of `pointsOnSheet`, so their count is at most `|edgesOnSheet| + 1` (`length_edgesOnSheet`,
the curve analogue of `filter_card_le_edges`). -/
theorem goodIncident_filter_card_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d)
    (key : Σ' ab : ℝ × ℝ, PProd (∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) ℕ) :
    ((goodIncident P H).filter (predBracket H key)).card
      ≤ (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length + 1 := by
  -- The filtered finset is a subset of the `pointsOnSheet` underlying finset.
  have hsub : (goodIncident P H).filter (predBracket H key)
      ⊆ P.filter (fun p => p ∈ evalPlaneZeroSet H.1 ∧ p.1 ∈ Set.Ioo key.1.1 key.1.2
          ∧ sheetRank H.1 p.1 p.2 = key.2.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpgi, hpZ, hpIoo, hprank⟩ := hp
    rw [goodIncident, Finset.mem_filter] at hpgi
    exact ⟨hpgi.1, hpZ, hpIoo, hprank⟩
  calc ((goodIncident P H).filter (predBracket H key)).card
      ≤ (P.filter (fun p => p ∈ evalPlaneZeroSet H.1 ∧ p.1 ∈ Set.Ioo key.1.1 key.1.2
            ∧ sheetRank H.1 p.1 p.2 = key.2.2)).card := Finset.card_le_card hsub
    _ = (pointsOnSheet P H.1 key.1.1 key.1.2 key.2.2).length :=
        (length_pointsOnSheet P H.1 key.1.1 key.1.2 key.2.2).symm
    _ ≤ (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length + 1 := by
        rcases length_edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2 with hlen | hnil
        · omega
        · rw [hnil, List.length_nil, Nat.zero_add]
          -- when there are no edges, `|pointsOnSheet| ≤ 1`.
          by_contra hc
          push Not at hc
          unfold edgesOnSheet at hnil
          rw [List.eq_nil_iff_length_eq_zero, List.length_zip, List.length_tail] at hnil
          omega

/-- **Coverage of the good-`x` incident points by the class keys.** Every good-`x`
incident point on `H` lies in some (bracket, rank) class of `classKeys d P H`: its
covering bracket comes from `goodIntervalsBundle_covers`, and its rank
`sheetRank H.1 p.1 p.2 ≤ d` (`sheetRank_le_at_bad`) lands in `range (d+1)`. This is the
hypothesis the list-cover bound `card_le_sum_map_filter_of_cover` consumes. -/
theorem goodIncident_cover {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    ∀ p ∈ goodIncident P H, ∃ key ∈ classKeys d P H, predBracket H key p := by
  intro p hp
  rw [goodIncident, Finset.mem_filter] at hp
  obtain ⟨hpP, hpZ, hpbad⟩ := hp
  -- A covering bracket `gi ∈ goodIntervalsBundle P H` for `p.1`.
  obtain ⟨gi, hgi, hpIoo⟩ := goodIntervalsBundle_covers P H p hpP hpbad
  -- The rank `j := sheetRank H.1 p.1 p.2 ≤ d`, so `j ∈ range (d+1)`.
  set j := sheetRank H.1 p.1 p.2 with hj
  have hjle : j ≤ d := sheetRank_le_at_bad H.1 H.2.1 H.2.2.2 H.2.2.1 p.1 p.2
  have hjmem : j ∈ List.range (d + 1) := List.mem_range.mpr (by omega)
  -- The class key for `(gi, j)` is in `classKeys` (the flatMap image).
  refine ⟨⟨gi.1, ⟨gi.2, j⟩⟩, ?_, ?_⟩
  · rw [classKeys, List.mem_flatMap]
    exact ⟨gi, hgi, List.mem_map.mpr ⟨j, hjmem, rfl⟩⟩
  · exact ⟨hpZ, hpIoo, rfl⟩

/-! ### Per-curve total: good-`x` ⊔ bad-`x` -/

/-- The points of `P` on curve `H` split into good-`x` and bad-`x` incident points
(by `p.1 ∈ Bad H.1`). -/
theorem incident_card_eq {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).card
      = (goodIncident P H).card + (badIncident P H).card := by
  -- `goodIncident` / `badIncident` are the `¬bad` / `bad` halves of the on-curve filter.
  have hg : goodIncident P H
      = (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).filter (fun p => ¬ p.1 ∈ Bad H.1) := by
    rw [goodIncident, Finset.filter_filter]
  have hb : badIncident P H
      = (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).filter (fun p => p.1 ∈ Bad H.1) := by
    rw [badIncident, Finset.filter_filter]
  rw [hg, hb, add_comm]
  exact (Finset.card_filter_add_card_filter_not
    (s := P.filter (fun p => p ∈ evalPlaneZeroSet H.1)) (fun p => p.1 ∈ Bad H.1)).symm

/-! ### Class-count bound -/

/-- The number of good-locus components on `H` equals `(Bad H.1).ncard + 1`:
`goodIntervalsBundle P H` is the `univ`-list of the component index type `ι`, whose
cardinality is `(Bad H.1).ncard + 1` (`decomp_D1_goodLocus_components`'s 4th clause,
with the finite bad set's `toFinset.card = (Bad H.1).ncard`). -/
theorem goodIntervalsBundle_length {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (goodIntervalsBundle P H).length = (Bad H.1).ncard + 1 := by
  -- Reconstruct the `Classical.choose` chain `goodIntervalsBundle` uses.
  set h0 := decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H) with hh0
  set ι := Classical.choose h0 with hι
  set instι : Fintype ι := Classical.choose (Classical.choose_spec h0) with hinstι
  set I : ι → Set ℝ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec h0)) with hIdef
  set hI := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h0)) with hhI
  -- `goodIntervalsBundle` is the `univ`-list mapped, so its length is `Fintype.card ι`.
  have hlen : (goodIntervalsBundle P H).length = Fintype.card ι := by
    rw [goodIntervalsBundle]
    rw [List.length_map, Finset.length_toList, Finset.card_univ]
  rw [hlen, hI.2.2.2, Set.ncard_eq_toFinset_card (Bad H.1) (edgeBCurve_bad_finite H)]

/-- `(classKeys d P H).length = (goodIntervalsBundle P H).length * (d+1)`: each bracket
contributes the `d+1` ranks of `List.range (d+1)`. -/
theorem classKeys_length {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (classKeys d P H).length = (goodIntervalsBundle P H).length * (d + 1) := by
  rw [classKeys, List.length_flatMap]
  rw [List.map_congr_left (g := fun _ => d + 1)
    (fun gi _ => by rw [List.length_map, List.length_range])]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

/-- **Class-count bound.** `(classKeys d P H).length ≤ ((d+1)^5 + d + 1) * (d+1)`: the
number of good-locus components is `(Bad H.1).ncard + 1 ≤ (d+1)^5 + d + 1`
(`decomp_D1_bad_ncard`), each split into `d+1` ranks. -/
theorem classKeys_length_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (classKeys d P H).length ≤ ((d + 1) ^ 5 + d + 1) * (d + 1) := by
  rw [classKeys_length, goodIntervalsBundle_length]
  have hbad : (Bad H.1).ncard ≤ (d + 1) ^ 5 + d :=
    decomp_D1_bad_ncard H.1 H.2.1 H.2.2.1 H.2.2.2
  exact Nat.mul_le_mul_right _ (by omega)

/-- **Per-curve good-`x` bound.** The good-`x` incident points on `H` number at most the
per-curve edge count plus the number of class keys: combine the list-cover bound
(`card_le_sum_map_filter_of_cover` with `goodIncident_cover`) with the per-class
`≤ |edgesOnSheet| + 1` (`goodIncident_filter_card_le`), then split the `+1`s into a
`(classKeys d P H).length` term. -/
theorem goodIncident_card_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (goodIncident P H).card
      ≤ ((classKeys d P H).map
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum
        + (classKeys d P H).length := by
  calc (goodIncident P H).card
      ≤ ((classKeys d P H).map
            (fun key => ((goodIncident P H).filter (predBracket H key)).card)).sum :=
        card_le_sum_map_filter_of_cover (goodIncident P H) (classKeys d P H)
          (predBracket H) (goodIncident_cover P H)
    _ ≤ ((classKeys d P H).map
            (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length + 1)).sum := by
        apply List.sum_le_sum
        intro key _
        exact goodIncident_filter_card_le P H key
    _ = ((classKeys d P H).map
            (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum
          + (classKeys d P H).length :=
        sum_map_add_one (classKeys d P H)
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)

/-! ### The E1 constant and the per-curve total bound -/

/-- **The E1 slack constant `c d`** (polynomial in `d` only). The good-`x` slack is
`#classKeys ≤ ((d+1)^5+d+1)·(d+1)` (`classKeys_length_le`); the bad-`x` term is
`((d+1)^5+d)·d` (`badIncident_card_le`). Their sum is the per-curve slack folded into
`c d · Γ.card`. -/
def cConst (d : ℕ) : ℕ := ((d + 1) ^ 5 + d + 1) * (d + 1) + ((d + 1) ^ 5 + d) * d

/-- **Per-curve total bound.** The points of `P` on curve `H` number at most the
per-curve edge sum plus `cConst d`: split into good-`x` (`goodIncident_card_le`,
`classKeys_length_le`) and bad-`x` (`badIncident_card_le`). -/
theorem incident_card_le {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).card
      ≤ ((classKeys d P H).map
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum
        + cConst d := by
  rw [incident_card_eq, cConst]
  have hgood := goodIncident_card_le P H
  have hkeys := classKeys_length_le P H
  have hbad := badIncident_card_le P H
  -- good ≤ edgeSum + classKeys_len ≤ edgeSum + ((d+1)^5+d+1)*(d+1); bad ≤ ((d+1)^5+d)*d.
  omega

/-! ### Global incidence-count assembly -/

/-- **Incidence double-counting** (generic, the `incidences_eq_sum` analogue for
`incidenceCount`). `incidenceCount P S = Σ_{γ∈S} |{p∈P : p∈γ}|`. -/
theorem incidenceCount_eq_sum {α : Type*} (P : Finset α) (S : Finset (Set α)) :
    PachSharir.incidenceCount P S = ∑ γ ∈ S, (P.filter (fun p => p ∈ γ)).card := by
  rw [PachSharir.incidenceCount, Finset.card_filter, Finset.sum_product_right]
  exact Finset.sum_congr rfl (fun γ _ => (Finset.card_filter _ _).symm)

/-- **E1 (Edge-B incidence-edge bound).** The Pach–Sharir incidence count of `(P, Γ)`
over the `ℝ × ℝ`-chart curve zero sets is at most the Edge-B multigraph's edge count
plus the slack `cConst d · Γ.card`. This is the `he : I ≤ G.numEdges + n` ingredient
(with `n := cConst d * Γ.card`) of the M-form incidence endgame
`incidence_bound_of_multigraphCrossingLemma`.

The proof collapses the curve image to a sum over `Γ` (`incidenceCount_eq_sum` +
`Finset.sum_image_le_of_nonneg`), bounds each per-curve term by the per-curve edge sum
plus `cConst d` (`incident_card_le`), recognizes the summed edge term as `numEdges`
(`edgeBMultigraph_numEdges_eq_sum`), and folds the `cConst d` per curve into
`cConst d · Γ.card`. `M` enters only via the multigraph's crossing field; the edge
count and this bound are `M`-independent. -/
theorem edgeB_incidence_le_numEdges_add
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))
      ≤ (edgeBMultigraph d M P Γ).numEdges + cConst d * Γ.card := by
  -- Step 1: collapse the curve image to a sum over `Γ`.
  have hstep1 :
      PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))
        ≤ ∑ H ∈ Γ, (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).card := by
    rw [incidenceCount_eq_sum]
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  -- Step 2: per-curve total bound.
  have hstep2 :
      ∑ H ∈ Γ, (P.filter (fun p => p ∈ evalPlaneZeroSet H.1)).card
        ≤ ∑ H ∈ Γ, (((classKeys d P H).map
            (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum + cConst d) :=
    Finset.sum_le_sum (fun H _ => incident_card_le P H)
  -- Step 3: distribute the sum; the edge term is `numEdges`, the constant is `cConst d * |Γ|`.
  have hstep3 :
      ∑ H ∈ Γ, (((classKeys d P H).map
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum + cConst d)
        = (edgeBMultigraph d M P Γ).numEdges + cConst d * Γ.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm Γ.card (cConst d),
      ← edgeBMultigraph_numEdges_eq_sum d M P Γ]
  exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))

end PachDeZeeuw.Algebraic
