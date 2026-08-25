/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Finite multigraph crossing lemma — standalone combinatorial surface

This file freezes the carrier types and the `Prop` statement of the finite
bounded-multiplicity crossing inequality used by the Pach–de Zeeuw incidence
development. Székely's 1997 Theorem 7 is the original bounded-multiplicity result.
The exact `4·M·v` threshold and `1/64` constant represented here are recorded in
Pach–Tóth, _A crossing lemma for multigraphs_, eq. (1), and follow from the random
thinning proof in Tóth, _Generalizations of the Crossing Lemma_, Theorem 7
(arXiv v1: Theorem 0.3.1), <https://arxiv.org/abs/2509.14074>.

For comparison, the sorry-free public Lean 4 development
`wpegden/crossing-consequences` (commit
`8769d142033fce042f502bf2857afb6b1375b5c3`) proves a `SimpleGraph` crossing
lemma with denominator `100` and derives the sharper denominator `64` internally.
It has no bounded-multiplicity parameter, so it does not prove the proposition
surface in this file.

It is **mathlib-only**: it imports no `CrossingLemma.*` module. The crossing
lemma surface mentions no algebraic curves, `auxCurve`, or
`PreparedBipartiteInput`, so it is developed and elaborated in isolation, and
downstream PDZ files import *this* surface rather than the reverse.

This file lays down carriers (`SimpleCurveArc`, `DrawnMultigraph`), the
edge-multiplicity counter, the basic drawing-validity predicate
`DrawnMultigraph.ArcsJoinEndpoints`, and the frozen statement
`CrossingLemmaMultigraphStatement`, together with small statement-level
specialization lemmas. The statement is kept entirely in `ℕ` and entirely cubed
(`e³ ≤ 64·M·v²·cr`), avoiding `Real.rpow` on the critical path.

These definitions follow the Pach–de Zeeuw / Pach–Sharir crossing-lemma
development (§3.4 / §4.1 / §4.2); the field structure, the `Fin numEdges` edge indexing,
the `0 < M` and `4·M·v ≤ e` threshold, and the `e³ ≤ 64·M·v²·cr` conclusion are
load-bearing and verified against arXiv 1308.0177.
-/

set_option linter.style.longLine false

namespace CrossingLemma

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

/-- The endpoint parameter of an oriented end: `0` for `false`, `1` for `true`. -/
def endParam (b : Bool) : Set.Icc (0 : ℝ) 1 :=
  if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

/-- The point in `ℝ²` where end `b` of arc `a` is anchored. -/
def endAnchor (a : SimpleCurveArc) (b : Bool) : ℝ × ℝ := a.param (endParam b)

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

/-- The declared graph endpoints agree with the endpoints of the drawn arcs.

This is the first topological-drawing condition from Tóth's survey
_Generalizations of the Crossing Lemma_, §0.2: in a drawing, vertices are points
and edges are arcs connecting the corresponding vertices. It is kept separate
from `WellDrawn`: `WellDrawn` controls the crossing counter, while
`ArcsJoinEndpoints` says the geometric arcs really draw the declared graph. -/
def DrawnMultigraph.ArcsJoinEndpoints (G : DrawnMultigraph) : Prop :=
  ∀ e : Fin G.numEdges,
    endAnchor (G.arc e) false = (G.endpoints e).1 ∧
      endAnchor (G.arc e) true = (G.endpoints e).2

/-- An arc that joins its declared endpoints cannot be a loop: injectivity of
the simple arc separates the endpoint parameters `0` and `1`. -/
theorem DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints {G : DrawnMultigraph}
    (hjoin : G.ArcsJoinEndpoints) (e : Fin G.numEdges) :
    (G.endpoints e).1 ≠ (G.endpoints e).2 := by
  intro hsame
  have hanchor : endAnchor (G.arc e) false = endAnchor (G.arc e) true := by
    rw [(hjoin e).1, (hjoin e).2, hsame]
  have hparam : endParam false = endParam true := (G.arc e).inj hanchor
  have hval := congrArg Subtype.val hparam
  norm_num [endParam] at hval

/-- The two edges `i` and `j` have four pairwise-distinct declared endpoints. -/
def DrawnMultigraph.FourDistinctEndpoints (G : DrawnMultigraph)
    (i j : Fin G.numEdges) : Prop :=
  (G.endpoints i).1 ≠ (G.endpoints i).2 ∧
  (G.endpoints i).1 ≠ (G.endpoints j).1 ∧
  (G.endpoints i).1 ≠ (G.endpoints j).2 ∧
  (G.endpoints i).2 ≠ (G.endpoints j).1 ∧
  (G.endpoints i).2 ≠ (G.endpoints j).2 ∧
  (G.endpoints j).1 ≠ (G.endpoints j).2

/-- Every counted crossing is between independent edges.

This is the formal version of the ACNS/Leighton proof's phrase “only
independent edges can cross” (Tóth, _Generalizations of the Crossing Lemma_,
proof of Theorem 0.2.1). It is the condition that makes a crossing survive a
vertex sample with probability `p^4`. -/
def DrawnMultigraph.CrossingsAreIndependent (G : DrawnMultigraph) : Prop :=
  ∀ i j : Fin G.numEdges, i ≠ j →
    (interiorOfArc (G.arc i) ∩ interiorOfArc (G.arc j)).Nonempty →
      G.FourDistinctEndpoints i j

/-- Finite bounded-multiplicity crossing inequality: for a plane-drawn multigraph
with edge multiplicity ≤ M, whose arcs join their
declared endpoints, that is `WellDrawn` (its `crossings` field is at least the
true interior-crossing count), and has e ≥ 4·M·v edges, e³ ≤ 64·M·v²·cr. Kept
entirely in ℕ and cubed (no rpow). The `WellDrawn` hypothesis is load-bearing:
the conclusion lower-bounds `crossings`, so without it the statement is
vacuously falsifiable (declare `crossings := 0`). The `ArcsJoinEndpoints`
hypothesis is the basic drawing-validity condition from the literature.

Székely's 1997 Theorem 7 is the original bounded-multiplicity theorem. The exact
`e³ ≤ 64·M·v²·cr` form is Pach–Tóth, eq. (1); Tóth's 2026 Theorem 7 proof gives
the random-thinning derivation and the averaged weak formula used by
`CrossingLemma.crossingLemma_of_weakBound`. This declaration states the proposition;
it does not prove it. Pegden's public Lean crossing-lemma proof covers only the
simple-graph (`M = 1`) sampling argument and does not supply the multiplicity-uniform
random-thinning premise. -/
def CrossingLemmaMultigraphStatement : Prop :=
  ∀ (G : DrawnMultigraph) (M : ℕ),
    0 < M →
    (∀ p q, G.multiplicity p q ≤ M) →
    G.ArcsJoinEndpoints →
    G.WellDrawn →
    4 * M * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings

/-- The simple-graph crossing lemma surface, i.e. the `M = 1` specialization of
`CrossingLemmaMultigraphStatement`.

This is the layer used by the Szemerédi--Trotter construction below: its
constructed drawing has at most one edge between any pair of vertices. The
literature source is the Crossing Lemma of Ajtai--Chvátal--Newborn--Szemerédi
and Leighton, stated for simple graphs as Theorem 0.2.1 in Tóth's survey
_Generalizations of the Crossing Lemma_: if `e(G) ≥ 4 n(G)`, then
`cr(G) ≥ e(G)^3 / (64 n(G)^2)`. This project keeps the conclusion in the
division-free natural-number form `e³ ≤ 64 v² cr`.

The public Lean 4 development `wpegden/crossing-consequences` proves a theorem
with denominator `100` for its own `SimpleGraph` crossing-number model; its proof
contains the denominator-`64` inequality as a local intermediate result. Reuse here
would still require a bridge between its drawing/crossing-number model and
`DrawnMultigraph`. -/
def SimpleCrossingLemmaStatement : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.WellDrawn →
    4 * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * G.V.card ^ 2 * G.crossings

/-- The simple crossing lemma restricted to drawings whose counted crossings are
between independent edges. This is the exact drawing-level hypothesis used by
the ACNS/Leighton random-induced-subgraph proof, where every surviving crossing
has four distinct endpoint vertices and hence survival probability `p^4`. -/
def IndependentSimpleCrossingLemmaStatement : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    4 * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * G.V.card ^ 2 * G.crossings

/-- The bounded-multiplicity multigraph crossing lemma immediately specializes
to the simple-graph crossing lemma by taking `M = 1`. -/
theorem simpleCrossingLemma_of_multigraphCrossingLemma
    (hCL : CrossingLemmaMultigraphStatement) :
    SimpleCrossingLemmaStatement := by
  intro G hmult hjoin hwd hthresh
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    hCL G 1 (by norm_num) hmult hjoin hwd (by simpa using hthresh)

/-- The unrestricted simple crossing lemma implies the independent-drawing
version by forgetting the independence hypothesis. -/
theorem independentSimpleCrossingLemma_of_simpleCrossingLemma
    (hCL : SimpleCrossingLemmaStatement) :
    IndependentSimpleCrossingLemmaStatement := by
  intro G hmult hjoin _hcross hwd hthresh
  exact hCL G hmult hjoin hwd hthresh

/-! ## Drawing → genus-0-map bridge: rotation from geometry

This section adds the companion definitions and the analysis
core of the drawing→genus-0-map bridge, §4 and §6. Everything is additive: the carriers
`SimpleCurveArc`,
`DrawnMultigraph` above are untouched.

The deliverable is `vertexRotation`: under the **pinned** regularity hypothesis
`ArcsRotationRegular` (predicate ARR, §6), the incident arc-ends at each vertex
carry a well-defined circular order — a genuine `Equiv.Perm` — read off from the
first-crossing angles on a small circle. `ArcsRotationRegular` is a *threaded
hypothesis*; its discharge for the Pach–de Zeeuw algebraic arcs is a separate concern and is
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

/-- `finRotate` commutes with the cardinality cast `finCongr`. -/
theorem finRotate_finCongr {a b : ℕ} (h : a = b) (i : Fin a) :
    finRotate b (finCongr h i) = finCongr h (finRotate a i) := by
  subst h
  simp [finCongr]

/-- **Equivariance of the cyclic-successor permutation.** If an equivalence
`e : α ≃ β` identifies the strict orders `Lα` and `Lβ`, then the corresponding
rotations are conjugate by `e`. -/
theorem rotationOfOrder_permCongr {α β : Type*} [Fintype α] [Fintype β]
    (Lα : LinearOrder α) (Lβ : LinearOrder β) (e : α ≃ β)
    (hlt : ∀ a b : α, Lβ.lt (e a) (e b) ↔ Lα.lt a b) :
    e.permCongr (rotationOfOrder Lα) = rotationOfOrder Lβ := by
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have henum : ∀ i : Fin (Fintype.card α),
      e (isoFin Lα i) = isoFin Lβ (finCongr hcard i) := by
    have hfg :
        (fun i : Fin (Fintype.card α) => e (isoFin Lα i)) =
          fun i : Fin (Fintype.card α) => isoFin Lβ (finCongr hcard i) := by
      apply strictMono_fin_unique hcard.symm
      · intro i j hij
        exact (hlt _ _).mpr (isoFin_lt Lα hij)
      · intro i j hij
        exact isoFin_lt Lβ (by simpa [finCongr] using hij)
    intro i
    exact congrFun hfg i
  ext b
  let a : α := e.symm b
  let i : Fin (Fintype.card α) := (isoFin Lα).symm a
  have hai : isoFin Lα i = a := by
    rw [show i = (isoFin Lα).symm a by rfl, OrderIso.apply_symm_apply]
  have hbi : isoFin Lβ (finCongr hcard i) = b := by
    calc
      isoFin Lβ (finCongr hcard i) = e (isoFin Lα i) := (henum i).symm
      _ = e a := by rw [hai]
      _ = b := by simp [a]
  rw [Equiv.permCongr_apply]
  calc
    e (rotationOfOrder Lα (e.symm b))
        = e (isoFin Lα (finRotate (Fintype.card α) i)) := by
            rw [show e.symm b = a by rfl, ← hai, rotationOfOrder_apply_isoFin]
    _ = isoFin Lβ (finCongr hcard (finRotate (Fintype.card α) i)) := by
          simpa using henum (finRotate (Fintype.card α) i)
    _ = isoFin Lβ (finRotate (Fintype.card β) (finCongr hcard i)) := by
          rw [← finRotate_finCongr hcard i]
    _ = rotationOfOrder Lβ (isoFin Lβ (finCongr hcard i)) := by
          rw [rotationOfOrder_apply_isoFin]
    _ = rotationOfOrder Lβ b := by rw [hbi]

/-! ### Layer 2 — companion definitions (geometry) -/

/-- **Geometric crossing-freeness:** distinct edges have disjoint arc
interiors. -/
def CrossingFree (G : DrawnMultigraph) : Prop :=
  ∀ i j : Fin G.numEdges, i ≠ j →
    Disjoint (interiorOfArc (G.arc i)) (interiorOfArc (G.arc j))

/-- **Incident oriented ends at `p`:** the finite set of pairs `(i, b)`
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
from §6 of the accompanying drawing→map development. For every vertex `p` there exist a radius
`r_p > 0`
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
algebraic arcs lives in the algebraic development, not here. -/
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

/-! ### Layer 3 — the vertex rotation, from ARR -/

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

/-- If two local angle keys induce the same strict order on the incident ends at
`p`, they define the same rotation at radius `r`. -/
theorem vertexRotationAtRadius_orderCongr (G : DrawnMultigraph) (p : ℝ × ℝ)
    {α β : (Fin G.numEdges × Bool) → ℝ → ℝ} {r : ℝ}
    (hinj : Function.Injective (endAngleKey G p α r))
    (hinj' : Function.Injective (endAngleKey G p β r))
    (hord : ∀ a b : ↥(incidentEnds G p),
      endAngleKey G p α r a < endAngleKey G p α r b ↔
        endAngleKey G p β r a < endAngleKey G p β r b) :
    vertexRotationAtRadius G p α r hinj = vertexRotationAtRadius G p β r hinj' := by
  unfold vertexRotationAtRadius
  exact rotationOfOrder_congr _ _ (fun a b => hord a b)

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

theorem arrAngle_firstCrossing (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    {e : Fin G.numEdges × Bool} (he : e ∈ incidentEnds G p)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ arrRadius G hARR hp) :
    ∃ t : Set.Icc (0 : ℝ) 1,
      IsFirstCrossing G p e r t ∧
        arrAngle G hARR hp e r = angleAt p ((G.arc e.1).param t) :=
  (hARR p hp).choose_spec.choose_spec.2.1 e he r hr0 hr

theorem endAnchor_eq_of_mem_incidentEnds (G : DrawnMultigraph)
    (hjoin : G.ArcsJoinEndpoints)
    {p : ℝ × ℝ} {e : Fin G.numEdges × Bool} (he : e ∈ incidentEnds G p) :
    endAnchor (G.arc e.1) e.2 = p := by
  rcases e with ⟨i, b⟩
  rw [incidentEnds, Finset.mem_filter] at he
  cases b
  · simpa [endAnchor, endParam] using (hjoin i).1.trans he.2
  · simpa [endAnchor, endParam] using (hjoin i).2.trans he.2

  theorem isFirstCrossing_unique_of_arcsJoinEndpoints
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    {p : ℝ × ℝ} {e : Fin G.numEdges × Bool} (he : e ∈ incidentEnds G p)
    {r : ℝ} (hr0 : 0 < r)
    {t t' : Set.Icc (0 : ℝ) 1}
    (ht : IsFirstCrossing G p e r t) (ht' : IsFirstCrossing G p e r t') :
    t = t' := by
  have hstart : dist ((G.arc e.1).param (endParam e.2)) p = 0 := by
    change dist (endAnchor (G.arc e.1) e.2) p = 0
    rw [endAnchor_eq_of_mem_incidentEnds G hjoin he]
    simp
  have ht_ne_start : (t : ℝ) ≠ (endParam e.2 : ℝ) := by
    intro hEq
    have hdist : dist ((G.arc e.1).param t) p = 0 := by
      have htEq : t = endParam e.2 := Subtype.ext hEq
      rw [htEq]
      exact hstart
    rw [ht.1] at hdist
    linarith
  have ht'_ne_start : (t' : ℝ) ≠ (endParam e.2 : ℝ) := by
    intro hEq
    have hdist : dist ((G.arc e.1).param t') p = 0 := by
      have htEq : t' = endParam e.2 := Subtype.ext hEq
      rw [htEq]
      exact hstart
    rw [ht'.1] at hdist
    linarith
  rcases e with ⟨i, b⟩
  cases b
  · have ht_pos : 0 < (t : ℝ) := by
      have hnonzero : (t : ℝ) ≠ 0 := by simpa [endParam] using ht_ne_start
      exact lt_of_le_of_ne t.2.1 (by simpa [eq_comm] using hnonzero)
    have ht'_pos : 0 < (t' : ℝ) := by
      have hnonzero : (t' : ℝ) ≠ 0 := by simpa [endParam] using ht'_ne_start
      exact lt_of_le_of_ne t'.2.1 (by simpa [eq_comm] using hnonzero)
    by_cases hlt : (t : ℝ) < t'
    · have hbetween : min (endParam false : ℝ) (t' : ℝ) < (t : ℝ) ∧
          (t : ℝ) < max (endParam false : ℝ) (t' : ℝ) := by
        constructor <;> simp [endParam, ht_pos, hlt, t'.2.1]
      have hlt_r := ht'.2 t hbetween
      rw [ht.1] at hlt_r
      linarith
    · by_cases hgt : (t' : ℝ) < t
      · have hbetween : min (endParam false : ℝ) (t : ℝ) < (t' : ℝ) ∧
            (t' : ℝ) < max (endParam false : ℝ) (t : ℝ) := by
          constructor <;> simp [endParam, ht'_pos, hgt, t.2.1]
        have hlt_r := ht.2 t' hbetween
        rw [ht'.1] at hlt_r
        linarith
      · apply Subtype.ext
        linarith
  · have ht_lt_one : (t : ℝ) < 1 := by
      have hne : (t : ℝ) ≠ 1 := by simpa [endParam] using ht_ne_start
      exact lt_of_le_of_ne t.2.2 hne
    have ht'_lt_one : (t' : ℝ) < 1 := by
      have hne : (t' : ℝ) ≠ 1 := by simpa [endParam] using ht'_ne_start
      exact lt_of_le_of_ne t'.2.2 hne
    by_cases hlt : (t : ℝ) < t'
    · have hbetween : min (endParam true : ℝ) (t : ℝ) < (t' : ℝ) ∧
          (t' : ℝ) < max (endParam true : ℝ) (t : ℝ) := by
        constructor <;> simp [endParam, ht'_lt_one, hlt, t.2.2]
      have hlt_r := ht.2 t' hbetween
      rw [ht'.1] at hlt_r
      linarith
    · by_cases hgt : (t' : ℝ) < t
      · have hbetween : min (endParam true : ℝ) (t' : ℝ) < (t : ℝ) ∧
            (t : ℝ) < max (endParam true : ℝ) (t' : ℝ) := by
          constructor <;> simp [endParam, ht_lt_one, hgt, t'.2.2]
        have hlt_r := ht'.2 t hbetween
        rw [ht.1] at hlt_r
        linarith
      · apply Subtype.ext
        linarith

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

/-- Any ARR witness family at `p` yields the canonical `vertexRotation`, provided
the drawing arcs really join their declared endpoints. The first-crossing
uniqueness theorem identifies the witness angles with the chosen ARR angles on a
common admissible circle. -/
theorem vertexRotation_eq_of_witness
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G) (hjoin : G.ArcsJoinEndpoints)
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    {rp : ℝ} {α : (Fin G.numEdges × Bool) → ℝ → ℝ}
    (hfirst : ∀ e ∈ incidentEnds G p, ∀ r, 0 < r → r ≤ rp →
      ∃ t : Set.Icc (0 : ℝ) 1,
        IsFirstCrossing G p e r t ∧ α e r = angleAt p ((G.arc e.1).param t))
    (hinj : ∀ r, 0 < r → r ≤ rp →
      Set.InjOn (fun e => α e r) (incidentEnds G p : Set (Fin G.numEdges × Bool)))
    (hstable : ∀ e₁ ∈ incidentEnds G p, ∀ e₂ ∈ incidentEnds G p, ∀ r, 0 < r → r ≤ rp →
      ∀ r', 0 < r' → r' ≤ rp -> (α e₁ r < α e₂ r ↔ α e₁ r' < α e₂ r'))
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ rp) :
    vertexRotationAtRadius G p α r
        (endAngleKey_injective G p _ _ (hinj r hr0 hr)) =
      vertexRotation G hARR hp := by
  let s := min r (arrRadius G hARR hp)
  have hs0 : 0 < s := lt_min hr0 (arrRadius_pos G hARR hp)
  have hs_r : s ≤ r := min_le_left _ _
  have hs_arr : s ≤ arrRadius G hARR hp := min_le_right _ _
  have hs_rp : s ≤ rp := le_trans hs_r hr
  have hrot_r :
      vertexRotationAtRadius G p α r
          (endAngleKey_injective G p _ _ (hinj r hr0 hr)) =
        vertexRotationAtRadius G p α s
          (endAngleKey_injective G p _ _ (hinj s hs0 hs_rp)) := by
    refine vertexRotationAtRadius_congr G p α r s
      (endAngleKey_injective G p _ _ (hinj r hr0 hr))
      (endAngleKey_injective G p _ _ (hinj s hs0 hs_rp)) ?_
    intro a b
    exact hstable a a.2 b b.2 r hr0 hr s hs0 hs_rp
  have hkey :
      ∀ e : ↥(incidentEnds G p),
        endAngleKey G p α s e = endAngleKey G p (arrAngle G hARR hp) s e := by
    intro e
    obtain ⟨t, ht, hα⟩ := hfirst e e.2 s hs0 hs_rp
    obtain ⟨t', ht', hα'⟩ := arrAngle_firstCrossing G hARR hp e.2 hs0 hs_arr
    have htt : t = t' :=
      isFirstCrossing_unique_of_arcsJoinEndpoints G hjoin e.2 hs0 ht ht'
    calc
      endAngleKey G p α s e = angleAt p ((G.arc e.1.1).param t) := hα
      _ = angleAt p ((G.arc e.1.1).param t') := by rw [htt]
      _ = endAngleKey G p (arrAngle G hARR hp) s e := by
            simpa [endAngleKey] using hα'.symm
  have hrot_s :
      vertexRotationAtRadius G p α s
          (endAngleKey_injective G p _ _ (hinj s hs0 hs_rp)) =
        vertexRotationAtRadius G p (arrAngle G hARR hp) s
          (endAngleKey_injective G p _ _ (arrAngle_injOn G hARR hp hs0 hs_arr)) := by
    refine vertexRotationAtRadius_orderCongr G p
      (endAngleKey_injective G p _ _ (hinj s hs0 hs_rp))
      (endAngleKey_injective G p _ _ (arrAngle_injOn G hARR hp hs0 hs_arr)) ?_
    intro a b
    rw [← hkey a, ← hkey b]
  calc
    vertexRotationAtRadius G p α r
        (endAngleKey_injective G p _ _ (hinj r hr0 hr))
      = vertexRotationAtRadius G p α s
          (endAngleKey_injective G p _ _ (hinj s hs0 hs_rp)) := hrot_r
    _ = vertexRotationAtRadius G p (arrAngle G hARR hp) s
          (endAngleKey_injective G p _ _ (arrAngle_injOn G hARR hp hs0 hs_arr)) := hrot_s
    _ = vertexRotation G hARR hp := rotation_wellDefined G hARR hp hs0 hs_arr

/-- A vertex with at most one incident end has trivial rotation. -/
theorem vertexRotation_eq_one_of_card_le_one (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) {p : ℝ × ℝ} (hp : p ∈ G.V)
    (hcard : Fintype.card ↥(incidentEnds G p) ≤ 1) :
    vertexRotation G hARR hp = 1 := by
  unfold vertexRotation
  letI : Subsingleton ↥(incidentEnds G p) := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact Equiv.ext (fun _ => Subsingleton.elim _ _)

/-- The radius-parametrized rotation is also trivial when the incident-end set
has at most one element. -/
theorem vertexRotationAtRadius_eq_one_of_card_le_one (G : DrawnMultigraph)
    (p : ℝ × ℝ) (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ)
    (hinj : Function.Injective (endAngleKey G p α r))
    (hcard : Fintype.card ↥(incidentEnds G p) ≤ 1) :
    vertexRotationAtRadius G p α r hinj = 1 := by
  unfold vertexRotationAtRadius
  letI : Subsingleton ↥(incidentEnds G p) := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact Equiv.ext (fun _ => Subsingleton.elim _ _)

/-! ### Edge-permutation invariance -/

section EdgePermutation

variable (G : DrawnMultigraph)

/-- Reindex the edge family of a drawing by a permutation of `Fin numEdges`. -/
def DrawnMultigraph.permuteEdges (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges)) :
    DrawnMultigraph where
  V := G.V
  numEdges := G.numEdges
  endpoints i := G.endpoints (π i)
  endpoints_mem i := by simpa using G.endpoints_mem (π i)
  arc i := G.arc (π i)
  crossings := G.crossings

/-- Edge permutation preserves the arc-endpoint condition. -/
theorem permuteEdges_arcsJoinEndpoints
    (π : Equiv.Perm (Fin G.numEdges)) (hjoin : G.ArcsJoinEndpoints) :
    (G.permuteEdges π).ArcsJoinEndpoints := by
  intro i
  exact hjoin (π i)

/-- Membership in `incidentEnds` commutes with permuting the edge indices. -/
theorem mem_incidentEnds_permuteEdges_iff
    (π : Equiv.Perm (Fin G.numEdges))
    {p : ℝ × ℝ} {e : Fin (G.permuteEdges π).numEdges × Bool} :
    e ∈ incidentEnds (G.permuteEdges π) p ↔ (π e.1, e.2) ∈ incidentEnds G p := by
  rcases e with ⟨i, b⟩
  cases b
  · constructor <;> intro h
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.permuteEdges] using h.2⟩
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.permuteEdges] using h.2⟩
  · constructor <;> intro h
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.permuteEdges] using h.2⟩
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.permuteEdges] using h.2⟩

/-- The first-crossing predicate is unchanged by permuting the edge indices. -/
theorem permuteEdges_isFirstCrossing_iff
    (π : Equiv.Perm (Fin G.numEdges))
    {p : ℝ × ℝ} {e : Fin (G.permuteEdges π).numEdges × Bool}
    {r : ℝ} {t : Set.Icc (0 : ℝ) 1} :
    IsFirstCrossing (G.permuteEdges π) p e r t ↔
      IsFirstCrossing G p (π e.1, e.2) r t := by
  rcases e with ⟨i, b⟩
  cases b <;> simp [IsFirstCrossing, DrawnMultigraph.permuteEdges]

/-- The explicit ARR witness obtained by transporting the chosen local angle data
of `G` along an edge permutation. -/
noncomputable def permuteEdges_arrRotationRegularWitness
    (π : Equiv.Perm (Fin G.numEdges)) (hARR : ArcsRotationRegular G)
    {p : ℝ × ℝ} (hp : p ∈ G.V) :
    ∃ (rp : ℝ) (α : (Fin (G.permuteEdges π).numEdges × Bool) → ℝ → ℝ),
      0 < rp ∧
      (∀ e ∈ incidentEnds (G.permuteEdges π) p, ∀ r, 0 < r → r ≤ rp →
        ∃ t : Set.Icc (0 : ℝ) 1,
          IsFirstCrossing (G.permuteEdges π) p e r t ∧
            α e r = angleAt p (((G.permuteEdges π).arc e.1).param t)) ∧
      (∀ r, 0 < r → r ≤ rp →
        Set.InjOn (fun e => α e r)
          (incidentEnds (G.permuteEdges π) p : Set (Fin (G.permuteEdges π).numEdges × Bool))) ∧
      (∀ e₁ ∈ incidentEnds (G.permuteEdges π) p, ∀ e₂ ∈ incidentEnds (G.permuteEdges π) p,
        ∀ r, 0 < r → r ≤ rp → ∀ r', 0 < r' → r' ≤ rp →
          (α e₁ r < α e₂ r ↔ α e₁ r' < α e₂ r')) := by
  refine ⟨arrRadius G hARR hp, (fun e r => arrAngle G hARR hp (π e.1, e.2) r),
    arrRadius_pos G hARR hp, ?_, ?_, ?_⟩
  · intro e he r hr0 hr
    have heG : (π e.1, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he
    obtain ⟨t, hcross, hangle⟩ := arrAngle_firstCrossing G hARR hp heG hr0 hr
    exact ⟨t, (permuteEdges_isFirstCrossing_iff (G := G) π).mpr hcross, hangle⟩
  · intro r hr0 hr e₁ he₁ e₂ he₂ heq
    have he₁G : (π e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₁
    have he₂G : (π e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₂
    have hmap := arrAngle_injOn G hARR hp hr0 hr he₁G he₂G heq
    exact Prod.ext (π.injective (congrArg Prod.fst hmap)) ((Prod.ext_iff.mp hmap).2)
  · intro e₁ he₁ e₂ he₂ r hr0 hr r' hr'0 hr'
    have he₁G : (π e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₁
    have he₂G : (π e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₂
    simpa using arrAngle_orderStable G hARR hp he₁G he₂G hr0 hr hr'0 hr'

/-- A definitionally transparent ARR witness for the permuted drawing, obtained
from the chosen local angle data of `G`. -/
noncomputable def permuteEdges_arrRotationRegular
    (π : Equiv.Perm (Fin G.numEdges)) (hARR : ArcsRotationRegular G) :
    ArcsRotationRegular (G.permuteEdges π) :=
  fun _ hp => permuteEdges_arrRotationRegularWitness G π hARR hp

/-- `ArcsRotationRegular` is invariant under permuting the edge indices: the
same local radii and first-crossing angle witnesses are read through `π`. -/
theorem permuteEdges_arcsRotationRegular
    (π : Equiv.Perm (Fin G.numEdges)) (hARR : ArcsRotationRegular G) :
    ArcsRotationRegular (G.permuteEdges π) :=
  permuteEdges_arrRotationRegular G π hARR

/-- The incident-end subtype of a permuted drawing is canonically equivalent to
the original incident-end subtype. -/
noncomputable def incidentEndsPermuteEquiv (π : Equiv.Perm (Fin G.numEdges)) (p : ℝ × ℝ) :
    ↥(incidentEnds (G.permuteEdges π) p) ≃ ↥(incidentEnds G p) where
  toFun e := ⟨(π e.1.1, e.1.2), (mem_incidentEnds_permuteEdges_iff (G := G) π).mp e.2⟩
  invFun e := ⟨(π.symm e.1.1, e.1.2), by
    rcases e with ⟨⟨i, b⟩, hi⟩
    rw [incidentEnds, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    cases b
    · rw [incidentEnds, Finset.mem_filter] at hi
      simpa [DrawnMultigraph.permuteEdges] using hi
    · rw [incidentEnds, Finset.mem_filter] at hi
      simpa [DrawnMultigraph.permuteEdges] using hi⟩
  left_inv := by
    rintro ⟨⟨i, b⟩, hi⟩
    simp
  right_inv := by
    rintro ⟨⟨i, b⟩, hi⟩
    simp

@[simp] theorem incidentEndsPermuteEquiv_apply_coe
    (π : Equiv.Perm (Fin G.numEdges)) (p : ℝ × ℝ)
    (e : ↥(incidentEnds (G.permuteEdges π) p)) :
    ((incidentEndsPermuteEquiv (G := G) π p e : ↥(incidentEnds G p)) :
      Fin G.numEdges × Bool) = (π e.1.1, e.1.2) := rfl

@[simp] theorem incidentEndsPermuteEquiv_symm_apply_coe
    (π : Equiv.Perm (Fin G.numEdges)) (p : ℝ × ℝ)
    (e : ↥(incidentEnds G p)) :
    (((incidentEndsPermuteEquiv (G := G) π p).symm e).1 : Fin G.numEdges × Bool) =
      (π.symm e.1.1, e.1.2) := rfl

/-- Injectivity of the local angle key is preserved by permuting the edge
indices. -/
theorem endAngleKey_injective_permuteEdges
    (π : Equiv.Perm (Fin G.numEdges)) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ)
    (hinj : Function.Injective (endAngleKey G p α r)) :
    Function.Injective
      (endAngleKey (G.permuteEdges π) p (fun e r => α (π e.1, e.2) r) r) := by
  intro a b hab
  have hmap :
      incidentEndsPermuteEquiv (G := G) π p a =
        incidentEndsPermuteEquiv (G := G) π p b := by
    apply hinj
    simpa [endAngleKey, incidentEndsPermuteEquiv, DrawnMultigraph.permuteEdges] using hab
  exact (incidentEndsPermuteEquiv (G := G) π p).injective hmap

/-- The local vertex rotation at a fixed admissible radius conjugates along an
edge-index permutation. -/
theorem vertexRotationAtRadius_permuteEdges
    (π : Equiv.Perm (Fin G.numEdges)) (p : ℝ × ℝ)
    (α : (Fin G.numEdges × Bool) → ℝ → ℝ) (r : ℝ)
    (hinj : Function.Injective (endAngleKey G p α r)) :
    (incidentEndsPermuteEquiv (G := G) π p).permCongr
      (vertexRotationAtRadius (G.permuteEdges π) p
        (fun e r => α (π e.1, e.2) r) r
        (endAngleKey_injective_permuteEdges (G := G) π p α r hinj))
      = vertexRotationAtRadius G p α r hinj := by
  unfold vertexRotationAtRadius
  refine rotationOfOrder_permCongr _ _ (incidentEndsPermuteEquiv (G := G) π p) ?_
  intro a b
  change
    endAngleKey G p α r ((incidentEndsPermuteEquiv (G := G) π p) a) <
      endAngleKey G p α r ((incidentEndsPermuteEquiv (G := G) π p) b) ↔
    endAngleKey (G.permuteEdges π) p (fun e r => α (π e.1, e.2) r) r a <
      endAngleKey (G.permuteEdges π) p (fun e r => α (π e.1, e.2) r) r b
  change α (((incidentEndsPermuteEquiv (G := G) π p) a).1) r <
      α (((incidentEndsPermuteEquiv (G := G) π p) b).1) r ↔
    α (π a.1.1, a.1.2) r < α (π b.1.1, b.1.2) r
  rw [incidentEndsPermuteEquiv_apply_coe, incidentEndsPermuteEquiv_apply_coe]

/-- The chosen vertex rotations for the explicit permuted ARR witness conjugate
along the induced equivalence on incident ends. -/
theorem vertexRotation_permuteEdges
    (π : Equiv.Perm (Fin G.numEdges)) (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular G) {p : ℝ × ℝ} (hp : p ∈ G.V) :
    (incidentEndsPermuteEquiv (G := G) π p).permCongr
      (vertexRotation (G.permuteEdges π) (permuteEdges_arrRotationRegular G π hARR) hp)
      = vertexRotation G hARR hp := by
  let hARRπ : ArcsRotationRegular (G.permuteEdges π) :=
    permuteEdges_arrRotationRegular G π hARR
  have hfirstπ :
      ∀ e ∈ incidentEnds (G.permuteEdges π) p, ∀ r, 0 < r → r ≤ arrRadius G hARR hp →
        ∃ t : Set.Icc (0 : ℝ) 1,
          IsFirstCrossing (G.permuteEdges π) p e r t ∧
            (fun e r => arrAngle G hARR hp (π e.1, e.2) r) e r =
              angleAt p (((G.permuteEdges π).arc e.1).param t) := by
    intro e he r hr0 hr
    have heG : (π e.1, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he
    obtain ⟨t, ht, hα⟩ := arrAngle_firstCrossing G hARR hp heG hr0 hr
    exact ⟨t, (permuteEdges_isFirstCrossing_iff (G := G) π).mpr ht, hα⟩
  have hinjπ :
      ∀ r, 0 < r → r ≤ arrRadius G hARR hp →
        Set.InjOn (fun e => arrAngle G hARR hp (π e.1, e.2) r)
          (incidentEnds (G.permuteEdges π) p : Set (Fin (G.permuteEdges π).numEdges × Bool)) := by
    intro r hr0 hr e₁ he₁ e₂ he₂ heq
    have he₁G : (π e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₁
    have he₂G : (π e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₂
    have hmap := arrAngle_injOn G hARR hp hr0 hr he₁G he₂G heq
    exact Prod.ext (π.injective (congrArg Prod.fst hmap)) ((Prod.ext_iff.mp hmap).2)
  have hstableπ :
      ∀ e₁ ∈ incidentEnds (G.permuteEdges π) p, ∀ e₂ ∈ incidentEnds (G.permuteEdges π) p,
        ∀ r, 0 < r → r ≤ arrRadius G hARR hp →
          ∀ r', 0 < r' → r' ≤ arrRadius G hARR hp →
            ((fun e r => arrAngle G hARR hp (π e.1, e.2) r) e₁ r <
                (fun e r => arrAngle G hARR hp (π e.1, e.2) r) e₂ r ↔
              (fun e r => arrAngle G hARR hp (π e.1, e.2) r) e₁ r' <
                (fun e r => arrAngle G hARR hp (π e.1, e.2) r) e₂ r') := by
    intro e₁ he₁ e₂ he₂ r hr0 hr r' hr'0 hr'
    have he₁G : (π e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₁
    have he₂G : (π e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp he₂
    simpa using arrAngle_orderStable G hARR hp he₁G he₂G hr0 hr hr'0 hr'
  have hrotπ :
      vertexRotationAtRadius (G.permuteEdges π) p
          (fun e r => arrAngle G hARR hp (π e.1, e.2) r) (arrRadius G hARR hp)
          (endAngleKey_injective (G.permuteEdges π) p _ _
            (hinjπ (arrRadius G hARR hp) (arrRadius_pos G hARR hp) le_rfl)) =
        vertexRotation (G.permuteEdges π) hARRπ hp := by
    exact vertexRotation_eq_of_witness (G := G.permuteEdges π) hARRπ
      (permuteEdges_arcsJoinEndpoints G π hjoin) hp hfirstπ hinjπ hstableπ
      (arrRadius_pos G hARR hp) le_rfl
  have hrot0 :
      (incidentEndsPermuteEquiv (G := G) π p).permCongr
        (vertexRotationAtRadius (G.permuteEdges π) p
          (fun e r => arrAngle G hARR hp (π e.1, e.2) r) (arrRadius G hARR hp)
          (endAngleKey_injective (G.permuteEdges π) p _ _
            (hinjπ (arrRadius G hARR hp) (arrRadius_pos G hARR hp) le_rfl))) =
          vertexRotation G hARR hp := by
    simpa [vertexRotation] using
      vertexRotationAtRadius_permuteEdges G π p (arrAngle G hARR hp)
        (arrRadius G hARR hp)
        (endAngleKey_injective G p _ _
          (arrAngle_injOn G hARR hp (arrRadius_pos G hARR hp) le_rfl))
  calc
    (incidentEndsPermuteEquiv (G := G) π p).permCongr
        (vertexRotation (G.permuteEdges π) (permuteEdges_arrRotationRegular G π hARR) hp)
      = (incidentEndsPermuteEquiv (G := G) π p).permCongr
          (vertexRotationAtRadius (G.permuteEdges π) p
            (fun e r => arrAngle G hARR hp (π e.1, e.2) r) (arrRadius G hARR hp)
            (endAngleKey_injective (G.permuteEdges π) p _ _
              (hinjπ (arrRadius G hARR hp) (arrRadius_pos G hARR hp) le_rfl))) := by
              rw [hrotπ]
    _ = vertexRotation G hARR hp := hrot0

/-- Geometric crossing-freeness is invariant under reindexing the edge family:
the drawing arcs are unchanged, only their `Fin numEdges` labels move through
`π`. -/
theorem permuteEdges_crossingFree_iff
    (π : Equiv.Perm (Fin G.numEdges)) :
    CrossingFree (G.permuteEdges π) ↔ CrossingFree G := by
  constructor
  · intro h i j hij
    simpa [DrawnMultigraph.permuteEdges] using
      h (π.symm i) (π.symm j) (π.symm.injective.ne hij)
  · intro h i j hij
    simpa [DrawnMultigraph.permuteEdges] using
      h (π i) (π j) (π.injective.ne hij)

end EdgePermutation

/-! ### Edge-prefix inheritance -/

section EdgePrefix

variable (G : DrawnMultigraph)

/-- The drawing obtained by keeping the first `m` edges in the current edge
order. This is the ordered-prefix object used for tree-first / same-face
insertion inductions after a convenient reindexing of the edge family. -/
def DrawnMultigraph.prefixEdges (G : DrawnMultigraph) (m : ℕ) (hm : m ≤ G.numEdges) :
    DrawnMultigraph where
  V := G.V
  numEdges := m
  endpoints i := G.endpoints (Fin.castLE hm i)
  endpoints_mem i := by simpa using G.endpoints_mem (Fin.castLE hm i)
  arc i := G.arc (Fin.castLE hm i)
  crossings := G.crossings

/-- Edge prefixes preserve the arc-endpoint condition. -/
theorem prefixEdges_arcsJoinEndpoints
    (m : ℕ) (hm : m ≤ G.numEdges) (hjoin : G.ArcsJoinEndpoints) :
    (G.prefixEdges m hm).ArcsJoinEndpoints := by
  intro i
  exact hjoin (Fin.castLE hm i)

/-- Membership in `incidentEnds` commutes with passing to an ordered prefix. -/
theorem mem_incidentEnds_prefixEdges_iff
    (m : ℕ) (hm : m ≤ G.numEdges)
    {p : ℝ × ℝ} {e : Fin (G.prefixEdges m hm).numEdges × Bool} :
    e ∈ incidentEnds (G.prefixEdges m hm) p ↔ (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p := by
  rcases e with ⟨i, b⟩
  cases b
  · constructor <;> intro h
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.prefixEdges] using h.2⟩
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.prefixEdges] using h.2⟩
  · constructor <;> intro h
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.prefixEdges] using h.2⟩
    · rw [incidentEnds, Finset.mem_filter] at h ⊢
      exact ⟨Finset.mem_univ _, by simpa [DrawnMultigraph.prefixEdges] using h.2⟩

/-- If a vertex is incident to some dart in a shorter ordered prefix, it remains
incident to the corresponding dart in every longer prefix. -/
theorem exists_mem_incidentEnds_prefixEdges_of_le
    {m n : ℕ} (hm : m ≤ G.numEdges) (hn : n ≤ G.numEdges) (hmn : m ≤ n)
    {p : ℝ × ℝ}
    (h : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p) :
    ∃ e : Fin n × Bool, e ∈ incidentEnds (G.prefixEdges n hn) p := by
  rcases h with ⟨e, he⟩
  refine ⟨(Fin.castLE hmn e.1, e.2), ?_⟩
  have heG : (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p :=
    (mem_incidentEnds_prefixEdges_iff (G := G) (m := m) (hm := hm)).mp he
  have hcast : Fin.castLE hn (Fin.castLE hmn e.1) = Fin.castLE hm e.1 := by
    ext
    rfl
  exact (mem_incidentEnds_prefixEdges_iff (G := G) (m := n) (hm := hn)).mpr
    (by simpa [hcast] using heG)

private theorem castLE_castSucc_eq_castLE {m n : ℕ}
    (hm : m ≤ n) (hm' : m + 1 ≤ n) (i : Fin m) :
    Fin.castLE hm' i.castSucc = Fin.castLE hm i := by
  apply Fin.ext
  rfl

/-- Passing from prefix length `m` to `m + 1` preserves incident-end membership
for the carried-over darts `i.castSucc`. -/
theorem mem_incidentEnds_prefixEdges_castSucc_iff
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ} {e : Fin m × Bool} :
    (e.1.castSucc, e.2) ∈ incidentEnds (G.prefixEdges (m + 1) hm') p ↔
      e ∈ incidentEnds (G.prefixEdges m hm) p := by
  constructor
  · intro h
    have hG : (Fin.castLE hm' e.1.castSucc, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) (m := m + 1) (hm := hm')).mp h
    exact (mem_incidentEnds_prefixEdges_iff (G := G) (m := m) (hm := hm)).mpr
      (by
        simpa [castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using hG)
  · intro h
    have hG : (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) (m := m) (hm := hm)).mp h
    exact (mem_incidentEnds_prefixEdges_iff (G := G) (m := m + 1) (hm := hm')).mpr
      (by
        simpa [castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using hG)

private theorem last_dart_mem_incidentEnds_prefixEdges
    (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (b : Bool) {p : ℝ × ℝ}
    (hp : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
          else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p) :
    (Fin.last m, b) ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := by
  unfold incidentEnds
  change (Fin.last m, b) ∈ Finset.univ.filter
    (fun e : Fin (m + 1) × Bool =>
      if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
      else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  cases b <;> simpa [DrawnMultigraph.prefixEdges] using hp

/-- The distinguished new incident end at the endpoint `p` of the last edge of
the successor prefix `m + 1`. -/
noncomputable def incident_ends_prefix_step_endpoint_new_dart
    (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (b : Bool) {p : ℝ × ℝ}
    (hp : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
          else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p) :
    ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
  ⟨(Fin.last m, b), last_dart_mem_incidentEnds_prefixEdges (G := G) m hm' b hp⟩

private theorem other_last_dart_not_mem_incidentEnds_prefixEdges
    (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (b : Bool) {p : ℝ × ℝ}
    (hp : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
          else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    (Fin.last m, !b) ∉ incidentEnds (G.prefixEdges (m + 1) hm') p := by
  intro h
  unfold incidentEnds at h
  change (Fin.last m, !b) ∈ Finset.univ.filter
    (fun e : Fin (m + 1) × Bool =>
      if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
      else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p) at h
  rw [Finset.mem_filter] at h
  cases b <;> exact hp h.2

private theorem eq_new_of_mem_incidentEnds_last
    (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    {e : Fin (m + 1) × Bool}
    (he : e ∈ incidentEnds (G.prefixEdges (m + 1) hm') p)
    (hlast : e.1 = Fin.last m) :
    e = (Fin.last m, b) := by
  rcases e with ⟨i, c⟩
  subst hlast
  cases b <;> cases c
  · rfl
  · exfalso
    exact
      (other_last_dart_not_mem_incidentEnds_prefixEdges (G := G) m hm' false hpother) he
  · exfalso
    exact
      (other_last_dart_not_mem_incidentEnds_prefixEdges (G := G) m hm' true hpother) he
  · rfl

/-- At an endpoint `p` of the newly added last edge of the prefix `m + 1`, the
old incident ends are exactly the incident ends of the longer prefix with that
new dart removed. This is the endpoint-level bijection used to express the
successor prefix rotation as a splice of the predecessor rotation. -/
noncomputable def incident_ends_prefix_step_endpoint_old_equiv
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    ↥(incidentEnds (G.prefixEdges m hm) p) ≃
      {e : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) //
        e ≠ incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew} where
  toFun e := by
    let d := e.1
    have hdmem : e.1 ∈ incidentEnds (G.prefixEdges m hm) p := e.2
    let e' : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
      ⟨(d.1.castSucc, d.2), (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) m hm hm').mpr hdmem⟩
    refine ⟨e', ?_⟩
    intro hEq
    have hcoe : e'.1 = (Fin.last m, b) := by
      exact congrArg Subtype.val hEq
    have hfirst : d.1.castSucc = Fin.last m := by
      exact congrArg Prod.fst hcoe
    exact Fin.castSucc_ne_last d.1 hfirst
  invFun e := by
    let dsub := e.1
    let d := dsub.1
    have hdmem : d ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := by
      change dsub.1 ∈ incidentEnds (G.prefixEdges (m + 1) hm') p
      exact dsub.2
    have hnotlast : d.1 ≠ Fin.last m := by
      intro hlast
      have hneweq : d = (Fin.last m, b) :=
        eq_new_of_mem_incidentEnds_last (G := G) m hm' b hpnew hpother hdmem hlast
      apply e.2
      apply Subtype.ext
      exact hneweq
    let i : Fin m := d.1.castPred hnotlast
    have hcastmem : (i.castSucc, d.2) ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := by
      have hd : (i.castSucc, d.2) = d := by
        apply Prod.ext
        · exact Fin.castSucc_castPred _ _
        · rfl
      simpa [hd] using hdmem
    refine ⟨(i, d.2), (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) m hm hm').mp hcastmem⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rcases e with ⟨e, hne⟩
    let d := e.1
    have hdmem : e.1 ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := e.2
    have hnotlast : d.1 ≠ Fin.last m := by
      intro hlast
      apply hne
      apply Subtype.ext
      exact eq_new_of_mem_incidentEnds_last (G := G) m hm' b hpnew hpother hdmem hlast
    let i : Fin m := d.1.castPred hnotlast
    apply Subtype.ext
    apply Prod.ext
    · change i.castSucc = d.1
      exact Fin.castSucc_castPred d.1 hnotlast
    · rfl

/-- The first-crossing predicate depends only on the underlying arc, so it is
unchanged on an ordered prefix after casting the edge index into the ambient
drawing. -/
theorem prefixEdges_isFirstCrossing_iff
    (m : ℕ) (hm : m ≤ G.numEdges)
    {p : ℝ × ℝ} {e : Fin (G.prefixEdges m hm).numEdges × Bool}
    {r : ℝ} {t : Set.Icc (0 : ℝ) 1} :
    IsFirstCrossing (G.prefixEdges m hm) p e r t ↔
      IsFirstCrossing G p (Fin.castLE hm e.1, e.2) r t := by
  rcases e with ⟨i, b⟩
  cases b <;> simp [IsFirstCrossing, DrawnMultigraph.prefixEdges]

/-- Geometric crossing-freeness is inherited by every ordered prefix. -/
theorem prefixEdges_crossingFree
    (m : ℕ) (hm : m ≤ G.numEdges) (hcross : CrossingFree G) :
    CrossingFree (G.prefixEdges m hm) := by
  intro i j hij
  have hijG : Fin.castLE hm i ≠ Fin.castLE hm j := by
    intro h
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val h
  simpa [DrawnMultigraph.prefixEdges] using hcross (Fin.castLE hm i) (Fin.castLE hm j) hijG

/-- The pinned local rotation-regularity witness restricts to every ordered
prefix of the drawing. -/
theorem prefixEdges_arcsRotationRegular
    (m : ℕ) (hm : m ≤ G.numEdges) (hARR : ArcsRotationRegular G) :
    ArcsRotationRegular (G.prefixEdges m hm) := by
  intro p hp
  obtain ⟨rp, α, hrp, hfirst, hinj, hstable⟩ := hARR p hp
  refine ⟨rp, (fun e r => α (Fin.castLE hm e.1, e.2) r), hrp, ?_, ?_, ?_⟩
  · intro e he r hr0 hrr
    have heG : (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) m hm).mp he
    obtain ⟨t, ht, hα⟩ := hfirst (Fin.castLE hm e.1, e.2) heG r hr0 hrr
    exact ⟨t, (prefixEdges_isFirstCrossing_iff (G := G) m hm).mpr ht, hα⟩
  · intro r hr0 hrr e₁ he₁ e₂ he₂ heq
    have he₁G : (Fin.castLE hm e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) m hm).mp he₁
    have he₂G : (Fin.castLE hm e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) m hm).mp he₂
    have hcast :
        (Fin.castLE hm e₁.1, e₁.2) = (Fin.castLE hm e₂.1, e₂.2) :=
      hinj r hr0 hrr he₁G he₂G heq
    have hfirst : Fin.castLE hm e₁.1 = Fin.castLE hm e₂.1 := by
      exact congrArg (fun x : Fin G.numEdges × Bool => x.1) hcast
    have hsecond : e₁.2 = e₂.2 := by
      exact congrArg (fun x : Fin G.numEdges × Bool => x.2) hcast
    apply Prod.ext
    · apply Fin.ext
      simpa using congrArg Fin.val hfirst
    · exact hsecond
  · intro e₁ he₁ e₂ he₂ r hr0 hrr r' hr'0 hr'r
    have he₁G : (Fin.castLE hm e₁.1, e₁.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) m hm).mp he₁
    have he₂G : (Fin.castLE hm e₂.1, e₂.2) ∈ incidentEnds G p :=
      (mem_incidentEnds_prefixEdges_iff (G := G) m hm).mp he₂
    exact hstable (Fin.castLE hm e₁.1, e₁.2) he₁G
      (Fin.castLE hm e₂.1, e₂.2) he₂G r hr0 hrr r' hr'0 hr'r

end EdgePrefix

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

/-- A nontrivial cyclic order has no fixed points. -/
theorem rotationOfOrder_apply_ne_self_of_two_le {β : Type*} [Fintype β]
    (L : LinearOrder β) (hcard : 2 ≤ Fintype.card β) (b : β) :
    rotationOfOrder L b ≠ b := by
  intro hb
  obtain ⟨i, rfl⟩ := (isoFin L).surjective b
  have hfix : finRotate (Fintype.card β) i = i := by
    apply (isoFin L).injective
    simpa [rotationOfOrder_apply_isoFin] using hb
  have hne : finRotate (Fintype.card β) i ≠ i := by
    have hsupport : i ∈ (finRotate (Fintype.card β)).support := by
      rw [support_finRotate_of_le hcard]
      simp
    exact (Equiv.Perm.mem_support.mp hsupport)
  exact hne hfix

#check @CrossingLemmaMultigraphStatement
#check DrawnMultigraph
#check @vertexRotation
#check @rotation_wellDefined

end CrossingLemma
