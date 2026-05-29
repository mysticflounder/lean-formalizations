/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Finite multigraph crossing lemma — standalone combinatorial surface

This file freezes the carrier types and the frozen `Prop` statement of the
finite multigraph crossing inequality (Székely / Ajtai–Chvátal–Newborn–
Szemerédi, multigraph form) used by the Pach--de Zeeuw incidence lane.

It is **mathlib-only**: it imports no `CrossingLemma.*` module. The crossing
lemma is purely combinatorial — it mentions no algebraic curves,
`auxCurve`, or `PreparedBipartiteInput` — so it is developed and elaborated in
isolation, and downstream PDZ files import *this* surface rather than the
reverse.

No proofs live here: the file lays down carriers (`SimpleCurveArc`,
`DrawnMultigraph`), the edge-multiplicity counter, and the frozen statement
`CrossingLemmaMultigraphStatement`. The statement is kept entirely in `ℕ` and
entirely cubed (`e³ ≤ 64·M·v²·cr`), avoiding `Real.rpow` on the critical path.

These definitions are transcribed from the verified spec
`docs/formalization/problem-98-pdz-ps-crossing-lemma-spec-2026-05-25.md`
(§3.4 / §4.1 / §4.2); the field structure, the `Fin numEdges` edge indexing,
the `0 < M` and `4·M·v ≤ e` threshold, and the `e³ ≤ 64·M·v²·cr` conclusion are
load-bearing and verified against arXiv 1308.0177.
-/

set_option linter.style.longLine false

namespace CrossingLemma.PDZ

/-- A simple continuous plane arc: the image of an injective continuous map from
the unit interval `[0,1]` into `ℝ²`. "Simple" means no self-intersection
(`inj`). Stored as a function field; there is no `DecidableEq` on such arcs, so
they are indexed by `Fin _` rather than collected into a `Finset` (see
`DrawnMultigraph.arc`). -/
structure SimpleCurveArc where
  param : Set.Icc (0 : ℝ) 1 → ℝ × ℝ
  cont : Continuous param
  inj : Function.Injective param
  carrier : Set (ℝ × ℝ) := Set.range param

/-- A multigraph drawn in the plane on a finite vertex set, with a crossing
count. Vertices are points in `ℝ²`; edges are an indexed family (`Fin numEdges`)
of arcs between vertices — the `Fin` indexing carries edge multiplicity without
needing `DecidableEq` on arcs. `crossings` counts pairs of edges whose interiors
cross. -/
structure DrawnMultigraph where
  V : Finset (ℝ × ℝ)
  numEdges : ℕ
  endpoints : Fin numEdges → (ℝ × ℝ) × (ℝ × ℝ)
  endpoints_mem : ∀ e, (endpoints e).1 ∈ V ∧ (endpoints e).2 ∈ V
  arc : Fin numEdges → SimpleCurveArc
  crossings : ℕ

/-- The edge multiplicity between two points `p q`: the number of edges whose
endpoint pair is `(p, q)` or `(q, p)`. -/
noncomputable def DrawnMultigraph.multiplicity (G : DrawnMultigraph) (p q : ℝ × ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card

/-- Interior of an arc: the image of the *open* unit interval `(0,1)` under
`param` (endpoints excluded, so arcs that share a vertex are still allowed to
have disjoint interiors). -/
def interiorOfArc (a : SimpleCurveArc) : Set (ℝ × ℝ) :=
  a.param '' {t : Set.Icc (0 : ℝ) 1 | (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1}

/-- The true number of crossings of a drawing: the number of unordered edge-index
pairs `i < j` whose arc *interiors* intersect. This is the geometric quantity the
crossing lemma lower-bounds; the structure's `crossings` field is only required to
be *at least* this (see `WellDrawn`), since the field is otherwise unconstrained. -/
noncomputable def DrawnMultigraph.crossingCount (G : DrawnMultigraph) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin G.numEdges × Fin G.numEdges)).filter
    (fun ij => ij.1 < ij.2 ∧
      (interiorOfArc (G.arc ij.1) ∩ interiorOfArc (G.arc ij.2)).Nonempty)).card

/-- **Well-drawn:** the declared `crossings` count is at least the true number of
interior crossings. Without this the `crossings` field is free and the crossing
inequality — a *lower* bound on `crossings` — is vacuously falsifiable by declaring
`crossings := 0` (witness: the complete multigraph). `WellDrawn` is exactly the
hypothesis that rules that out, and it holds by `le_refl` for any drawing that
sets `crossings := crossingCount`. -/
def DrawnMultigraph.WellDrawn (G : DrawnMultigraph) : Prop :=
  G.crossingCount ≤ G.crossings

/-- Finite multigraph crossing inequality (Székely / ACNS, multigraph form):
for a plane-drawn multigraph with edge multiplicity ≤ M, that is `WellDrawn`
(its `crossings` field is at least the true interior-crossing count), and has
e ≥ 4·M·v edges, e³ ≤ 64·M·v²·cr. Kept entirely in ℕ and cubed (no rpow). The
`WellDrawn` hypothesis is load-bearing: the conclusion lower-bounds `crossings`,
so without it the statement is vacuously falsifiable (declare `crossings := 0`). -/
def CrossingLemmaMultigraphStatement : Prop :=
  ∀ (G : DrawnMultigraph) (M : ℕ),
    0 < M →
    (∀ p q, G.multiplicity p q ≤ M) →
    G.WellDrawn →
    4 * M * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings

/-! ## BR-0 / BR-1 — drawing → genus-0-map bridge: rotation from geometry

This section adds the route-(B) companion definitions (BR-0) and the analysis
core (BR-1) of the PdZ drawing→genus-0-map bridge, following
`docs/formalization/problem-98-pdz-ps-drawing-to-genus0-map-bridge-packet-2026-05-25.md`
§4 and §6. Everything is additive: the carriers `SimpleCurveArc`,
`DrawnMultigraph` above are untouched.

The deliverable is `vertexRotation`: under the **pinned** regularity hypothesis
`ArcsRotationRegular` (predicate ARR, §6), the incident arc-ends at each vertex
carry a well-defined circular order — a genuine `Equiv.Perm` — read off from the
first-crossing angles on a small circle. `ArcsRotationRegular` is a *threaded
hypothesis*; its discharge for the PdZ algebraic arcs is a separate lane and is
**not** attempted here (and the arcs are never assumed semialgebraic).

### Layer 1 — generic order theory (no geometry)

A finite type with a linear order has a canonical cyclic-successor permutation;
it depends only on the `<` relation, and it really is "go to the next element in
the order." This is the combinatorial heart of "a cyclic order is a permutation,"
fully geometry-free. -/

/-- The increasing bijection `Fin (card β) ≃o β` for an explicit linear order. -/
noncomputable def isoFin {β : Type*} [Fintype β] (L : LinearOrder β) :
    Fin (Fintype.card β) ≃o β :=
  letI := L; Fintype.orderIsoFinOfCardEq β rfl

/-- `isoFin L` strictly increases the `L`-order. -/
theorem isoFin_lt {β : Type*} [Fintype β] (L : LinearOrder β)
    {a b : Fin (Fintype.card β)} (hab : a < b) : L.lt (isoFin L a) (isoFin L b) := by
  letI := L
  exact (isoFin L).strictMono hab

/-- Cyclic-successor permutation of `Fin n`, transported along an equivalence. -/
def permOfEquiv {β : Type*} {n : ℕ} (eq : Fin n ≃ β) : Equiv.Perm β :=
  (eq.symm.trans (finRotate n)).trans eq

/-- `permOfEquiv` depends only on the forward map of the equivalence. -/
theorem permOfEquiv_congr {β : Type*} {n : ℕ} (eq₁ eq₂ : Fin n ≃ β)
    (h : (eq₁ : Fin n → β) = eq₂) : permOfEquiv eq₁ = permOfEquiv eq₂ := by
  have : eq₁ = eq₂ := Equiv.ext (fun x => congrFun h x)
  rw [this]

/-- **The cyclic-successor permutation determined by a linear order** on a
fintype `β`: list `β` in increasing order and send each element to the next,
wrapping the last back to the first. -/
noncomputable def rotationOfOrder {β : Type*} [Fintype β] (L : LinearOrder β) :
    Equiv.Perm β :=
  permOfEquiv (isoFin L).toEquiv

/-- The rotation sends the `i`-th smallest element (in the `L`-order) to the
`(i+1 mod n)`-th smallest: it genuinely is the cyclic successor in the order. -/
theorem rotationOfOrder_apply_isoFin {β : Type*} [Fintype β] (L : LinearOrder β)
    (i : Fin (Fintype.card β)) :
    rotationOfOrder L (isoFin L i) = isoFin L (finRotate (Fintype.card β) i) := by
  simp only [rotationOfOrder, permOfEquiv, Equiv.trans_apply, OrderIso.coe_toEquiv]
  congr 2
  exact (isoFin L).symm_apply_apply i

/-- Two strictly monotone maps `Fin k → β` onto the same finite linear order
agree (both are *the* increasing enumeration). -/
theorem strictMono_fin_unique {β : Type*} [LinearOrder β] [Fintype β] {k : ℕ}
    (h : Fintype.card β = k) {f g : Fin k → β} (hf : StrictMono f) (hg : StrictMono g) :
    f = g := by
  have hcard : (Finset.univ : Finset β).card = k := by simpa using h
  rw [Finset.orderEmbOfFin_unique hcard (fun _ => Finset.mem_univ _) hf,
      Finset.orderEmbOfFin_unique hcard (fun _ => Finset.mem_univ _) hg]

/-- **Order-only dependence of the rotation.** If two linear orders on `β` have
the same strict-less-than relation, they give the same cyclic-successor
permutation. (The presentation of the order is irrelevant; only `<` matters.) -/
theorem rotationOfOrder_congr {β : Type*} [Fintype β] (L₁ L₂ : LinearOrder β)
    (hlt : ∀ a b : β, L₁.lt a b ↔ L₂.lt a b) :
    rotationOfOrder L₁ = rotationOfOrder L₂ := by
  apply permOfEquiv_congr
  letI := L₁
  refine strictMono_fin_unique rfl (isoFin L₁).strictMono ?_
  intro a b hab
  exact (hlt _ _).mpr (isoFin_lt L₂ hab)

/-! ### Layer 2 — BR-0 companion definitions (geometry) -/

/-- **Geometric crossing-freeness (BR-0):** distinct edges have disjoint arc
interiors. -/
def CrossingFree (G : DrawnMultigraph) : Prop :=
  ∀ i j : Fin G.numEdges, i ≠ j →
    Disjoint (interiorOfArc (G.arc i)) (interiorOfArc (G.arc j))

/-- The starting parameter of an oriented end: `0` for `false`, `1` for `true`. -/
def endParam (b : Bool) : Set.Icc (0 : ℝ) 1 :=
  if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

/-- The point in `ℝ²` where end `b` of arc `a` is anchored. -/
def endAnchor (a : SimpleCurveArc) (b : Bool) : ℝ × ℝ := a.param (endParam b)

/-- **Incident oriented ends at `p` (BR-1):** the finite set of pairs `(i, b)`
whose anchored endpoint equals `p`. `b = false` is the param-`0` end, `b = true`
the param-`1` end. Indexed by `Fin G.numEdges × Bool`, avoiding any need for
`DecidableEq SimpleCurveArc`. -/
noncomputable def incidentEnds (G : DrawnMultigraph) (p : ℝ × ℝ) :
    Finset (Fin G.numEdges × Bool) := by
  classical
  exact Finset.univ.filter
    (fun e : Fin G.numEdges × Bool =>
      (if e.2 then (G.endpoints e.1).2 = p else (G.endpoints e.1).1 = p))

/-- Angle of a plane point `q` as seen from the center `p`, via `Complex.arg`. -/
noncomputable def angleAt (p q : ℝ × ℝ) : ℝ := Complex.arg ⟨q.1 - p.1, q.2 - p.2⟩

/-- `t` is the **first crossing** of the sphere `∂B(p,r)` by end `e = (i,b)` of
`G`: the arc reaches distance `r` from `p` at parameter `t`, and stays strictly
inside the closed ball on the open segment between the start `endParam b` and `t`.
(The transversal "leaves the closed ball" content is supplied by ARR's stability
clause, not re-derived here.) -/
def IsFirstCrossing (G : DrawnMultigraph) (p : ℝ × ℝ) (e : Fin G.numEdges × Bool)
    (r : ℝ) (t : Set.Icc (0 : ℝ) 1) : Prop :=
  dist ((G.arc e.1).param t) p = r ∧
    ∀ s : Set.Icc (0 : ℝ) 1,
      (min (endParam e.2 : ℝ) (t : ℝ) < (s : ℝ) ∧ (s : ℝ) < max (endParam e.2 : ℝ) (t : ℝ)) →
        dist ((G.arc e.1).param s) p < r

/-- **The pinned regularity predicate ARR** (germ-stable local order), verbatim
from §6 of the bridge packet. For every vertex `p` there exist a radius `r_p > 0`
and an angular-position function `α` on incident-ends × radii such that:

* **(a)** for each incident end and each `0 < r ≤ r_p`, the value `α e r` is the
  angle of a genuine first crossing of `∂B(p,r)` (the first crossing, hence the
  angle, is well-defined);
* **(b1)** the angle map is injective on incident ends at each such `r` (distinct
  ends get distinct first-crossing angles); and
* **(b2)** the induced strict angular order is constant in `r` on `(0, r_p]`.

The predicate talks only about the arcs and small circles; it mentions no
permutation, combinatorial map, or planarity, and it does **not** assume the arcs
are semialgebraic. It is a threaded hypothesis: its discharge for the PdZ
algebraic arcs lives in the algebraic lane, not here. -/
def ArcsRotationRegular (G : DrawnMultigraph) : Prop :=
  ∀ p ∈ G.V, ∃ (rp : ℝ) (α : (Fin G.numEdges × Bool) → ℝ → ℝ),
    0 < rp ∧
    (∀ e ∈ incidentEnds G p, ∀ r, 0 < r → r ≤ rp →
      ∃ t : Set.Icc (0 : ℝ) 1,
        IsFirstCrossing G p e r t ∧ α e r = angleAt p ((G.arc e.1).param t)) ∧
    (∀ r, 0 < r → r ≤ rp →
      Set.InjOn (fun e => α e r) (incidentEnds G p : Set (Fin G.numEdges × Bool))) ∧
    (∀ e₁ ∈ incidentEnds G p, ∀ e₂ ∈ incidentEnds G p, ∀ r, 0 < r → r ≤ rp →
      ∀ r', 0 < r' → r' ≤ rp → (α e₁ r < α e₂ r ↔ α e₁ r' < α e₂ r'))

/-! ### Layer 3 — BR-1: the vertex rotation, from ARR -/

/-- The angle function `α` restricted to the *subtype* `↥(incidentEnds G p)` at
radius `r`, used as the sorting key for the rotation. -/
noncomputable def endAngleKey (G : DrawnMultigraph) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ) :
    ↥(incidentEnds G p) → ℝ := fun e => α (e : Fin G.numEdges × Bool) r

/-- `InjOn` of the angle map on `incidentEnds` ⇒ injectivity of the subtype key. -/
theorem endAngleKey_injective (G : DrawnMultigraph) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ)
    (h : Set.InjOn (fun e => α e r) (incidentEnds G p : Set (Fin G.numEdges × Bool))) :
    Function.Injective (endAngleKey G p α r) :=
  fun a b hab => Subtype.ext (h a.2 b.2 hab)

/-- The vertex rotation built from a concrete angle function `α` and radius `r`,
given injectivity of the angle map at `r`: sort incident ends by first-crossing
angle and take the cyclic successor. -/
noncomputable def vertexRotationAtRadius (G : DrawnMultigraph) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ)
    (hinj : Function.Injective (endAngleKey G p α r)) :
    Equiv.Perm ↥(incidentEnds G p) :=
  rotationOfOrder (LinearOrder.lift' (endAngleKey G p α r) hinj)

/-- **Radius-independence of the rotation.** If the angle map at two radii induces
the same strict order on incident ends, the two rotations agree. -/
theorem vertexRotationAtRadius_congr (G : DrawnMultigraph) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r r' : ℝ)
    (hinj : Function.Injective (endAngleKey G p α r))
    (hinj' : Function.Injective (endAngleKey G p α r'))
    (hord : ∀ a b : ↥(incidentEnds G p),
      endAngleKey G p α r a < endAngleKey G p α r b ↔
      endAngleKey G p α r' a < endAngleKey G p α r' b) :
    vertexRotationAtRadius G p α r hinj = vertexRotationAtRadius G p α r' hinj' :=
  rotationOfOrder_congr _ _ (fun a b => hord a b)

/-- The ARR-supplied radius at vertex `p` (chosen witness). -/
noncomputable def arrRadius (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) : ℝ :=
  (hARR p hp).choose

/-- The ARR-supplied angle function at vertex `p` (chosen witness). -/
noncomputable def arrAngle (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) : (Fin G.numEdges × Bool) → ℝ → ℝ :=
  (hARR p hp).choose_spec.choose

theorem arrRadius_pos (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) : 0 < arrRadius G hARR hp :=
  (hARR p hp).choose_spec.choose_spec.1

theorem arrAngle_injOn (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ arrRadius G hARR hp) :
    Set.InjOn (fun e => arrAngle G hARR hp e r)
      (incidentEnds G p : Set (Fin G.numEdges × Bool)) :=
  (hARR p hp).choose_spec.choose_spec.2.2.1 r hr0 hr

theorem arrAngle_orderStable (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    {e₁ : Fin G.numEdges × Bool} (h₁ : e₁ ∈ incidentEnds G p)
    {e₂ : Fin G.numEdges × Bool} (h₂ : e₂ ∈ incidentEnds G p)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ arrRadius G hARR hp)
    {r' : ℝ} (hr'0 : 0 < r') (hr' : r' ≤ arrRadius G hARR hp) :
    (arrAngle G hARR hp e₁ r < arrAngle G hARR hp e₂ r ↔
     arrAngle G hARR hp e₁ r' < arrAngle G hARR hp e₂ r') :=
  (hARR p hp).choose_spec.choose_spec.2.2.2 e₁ h₁ e₂ h₂ r hr0 hr r' hr'0 hr'

/-- **The vertex rotation** at `p ∈ G.V`, under `ArcsRotationRegular G`: the
circular order of incident arc-ends given by the first-crossing angles on a small
circle `∂B(p, r_p)`, as a permutation of the incident ends. (Canonical choice:
read off at the ARR-supplied radius `r_p`.) -/
noncomputable def vertexRotation (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) : Equiv.Perm ↥(incidentEnds G p) :=
  vertexRotationAtRadius G p (arrAngle G hARR hp) (arrRadius G hARR hp)
    (endAngleKey_injective G p _ _
      (arrAngle_injOn G hARR hp (arrRadius_pos G hARR hp) le_rfl))

/-- **`rotation_wellDefined`** — the vertex rotation is a well-defined permutation,
independent of the radius used to read off the angular order. Under
`ArcsRotationRegular G`, for *every* admissible radius `r ∈ (0, r_p]` the rotation
built from the first-crossing angles at radius `r` equals the canonical
`vertexRotation`. This is the success condition of the §6 construction: by ARR
(a) each first crossing (hence each angle) is well-defined; by (b1) distinct ends
get distinct angles, so the sort is a genuine permutation; and by (b2) the induced
cyclic order is constant in `r`, so the `r ↓ 0` limit exists and equals the value
at any admissible `r`. -/
theorem rotation_wellDefined (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ arrRadius G hARR hp) :
    vertexRotationAtRadius G p (arrAngle G hARR hp) r
        (endAngleKey_injective G p _ _ (arrAngle_injOn G hARR hp hr0 hr)) =
      vertexRotation G hARR hp := by
  unfold vertexRotation
  refine vertexRotationAtRadius_congr G p (arrAngle G hARR hp) r
    (arrRadius G hARR hp) _ _ ?_
  intro a b
  exact arrAngle_orderStable G hARR hp a.2 b.2 hr0 hr (arrRadius_pos G hARR hp) le_rfl

/-! ### Non-vacuity checks (guarding against an unsatisfiable hypothesis)

These rule out the failure mode where `ArcsRotationRegular` is internally
contradictory (so `vertexRotation` would exist but be built on `False`), and
confirm the rotation is a genuine permutation. -/

/-- Consistency: a drawing with no vertices vacuously satisfies ARR. In
particular `ArcsRotationRegular` is *not* equivalent to `False`. -/
theorem arcsRotationRegular_of_no_vertices (G : DrawnMultigraph) (hV : G.V = ∅) :
    ArcsRotationRegular G := by
  intro p hp
  rw [hV] at hp
  simp at hp

/-- Structural non-vacuity: on a vertex with at most one incident end, the
rotation is the identity — a genuine (if trivial) permutation. -/
theorem rotationOfOrder_eq_one_of_card_le_one {β : Type*} [Fintype β]
    (L : LinearOrder β) (hcard : Fintype.card β ≤ 1) : rotationOfOrder L = 1 := by
  have : Subsingleton β := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact Equiv.ext (fun _ => Subsingleton.elim _ _)

#check @CrossingLemmaMultigraphStatement
#check DrawnMultigraph
#check @vertexRotation
#check @rotation_wellDefined

end CrossingLemma.PDZ
