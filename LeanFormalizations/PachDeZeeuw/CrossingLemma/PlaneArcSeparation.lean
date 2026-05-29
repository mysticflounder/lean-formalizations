/-
Erdős 98 — Card BR-3b, geometric residual (MS): local arc-separation.

# What this file is

A **standalone, pure plane-topology** development of the (MS) lemma — the one
research-grade geometric input of card BR-3b of the PDZ route-(B) bridge
(`docs/formalization/problem-98-pdz-ps-drawing-to-genus0-map-bridge-packet-2026-05-25.md`,
§7).  It is deliberately divorced from the combinatorial-map machinery: it does
**not** import `CrossingLemma`, `CombinatorialMap`, or any `Branch2/` file, and it
does not mention `DrawnMultigraph`/`CrossingFree` (sibling agents own those).
Everything here is stated over an abstract topological space and specialised to
`ℝ × ℝ` only where the geometry bites.

# The statement, informally

> (MS) A simple arc `β` whose interior is disjoint from a closed set `A`, with
> both endpoints in the closure of a single **simply connected** connected
> component `R` of `ℝ² ∖ A`, splits `R` into exactly two connected components.

The simply-connected restriction is the whole point: it removes the
genus/winding content and is what makes (MS) **strictly weaker** than the Jordan
curve theorem (pinned: `nthdegree get 01KSHGYWMT6QZV7N008TR123AV`).  We therefore
never attempt Jordan, plane separation of an arbitrary simple closed curve, or
`IsSemialgebraic` — all three are out of scope and absent from mathlib v4.27.0.

# Honest status (PROVEN vs CONJECTURED)

This file splits (MS) into a sorry-free **componentology** core plus a single,
loudly-marked geometric residual.  Concretely:

* §1  `arcInterior`, `SimpleArc` and the *two-sided open partition* predicate
      `IsTwoSidedPartition` — definitions.                          [definitions]
* §2  `arc_endpoint_mem_closure`  — the endpoint-closure continuity fact.
                                                                    [PROVEN, sorry-free]
* §3  componentology:  a two-sided open partition has exactly two connected
      components (`exactly_two_of_isTwoSidedPartition` and helpers).
                                                                    [PROVEN, sorry-free]
* §4  `SplitsIntoTwo` predicate and the assembled (MS) statement
      `local_arc_separation`, whose ONLY use of `sorry` is the irreducible
      Jordan-strength residual `exists_twoSidedPartition_of_arc` (§5).
                                                                    [statement PROVEN-to-elaborate;
                                                                     residual CONJECTURED, sorry]

See the bottom-of-file gap report for the precise residual obligation and why it
is the genuinely hard, non-elementary part.
-/
import Mathlib

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

/-! ## §1  Arcs, interiors, and the two-sided-partition predicate -/

/-- The (open) interior parameter interval `(0,1) ⊆ ℝ`. -/
def unitIoo : Set ℝ := Set.Ioo (0 : ℝ) 1

/-- A simple arc in a topological space `X`: a continuous injective map from the
closed unit interval.  Modelled on the project's `SimpleCurveArc` but kept local
and over an arbitrary `X` (we only ever need `X = ℝ × ℝ`). -/
structure SimpleArc (X : Type*) [TopologicalSpace X] where
  /-- The parametrisation. -/
  toFun : Set.Icc (0 : ℝ) 1 → X
  /-- Continuity of the parametrisation. -/
  continuous_toFun : Continuous toFun
  /-- Injectivity (the arc is *simple*). -/
  injective_toFun : Function.Injective toFun

attribute [coe] SimpleArc.toFun

instance {X : Type*} [TopologicalSpace X] :
    CoeFun (SimpleArc X) (fun _ => Set.Icc (0 : ℝ) 1 → X) := ⟨SimpleArc.toFun⟩

namespace SimpleArc

variable {X : Type*} [TopologicalSpace X]

/-- The two endpoints of the arc as elements of `Set.Icc 0 1`. -/
def src : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
def tgt : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

/-- The full carrier (image) of the arc. -/
def carrier (β : SimpleArc X) : Set X := Set.range β

/-- The *interior* of the arc: the image of the open parameter interval `(0,1)`.
Endpoints are excluded, so arcs meeting only at shared endpoints are allowed. -/
def arcInterior (β : SimpleArc X) : Set X :=
  β '' {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo}

end SimpleArc

/-- **Two-sided open partition of a set `W`.**  A pair of ambient-open sets
`U, V` that partition `W` into two nonempty disjoint connected pieces.  This is
the *conclusion shape* of (MS): producing such a `U, V` for `W = R ∖ β` is the
whole content; once we have it, "exactly two components" is pure connectedness
plumbing (§3).

`U`, `V` are open **in the ambient space `X`** — that ambient openness is exactly
the Jordan-strength fact the geometric residual (§5) must supply. -/
structure IsTwoSidedPartition {X : Type*} [TopologicalSpace X]
    (W U V : Set X) : Prop where
  isOpen_left : IsOpen U
  isOpen_right : IsOpen V
  disjoint : Disjoint U V
  union_eq : U ∪ V = W
  nonempty_left : U.Nonempty
  nonempty_right : V.Nonempty
  preconnected_left : IsPreconnected U
  preconnected_right : IsPreconnected V

/-! ## §2  The endpoint-closure continuity fact  [PROVEN]

If the interior of `β` lies in a set `R`, then both endpoints lie in `closure R`.
This is the elementary continuity half of (MS); it uses no separation theory. -/

/-- `0` lies in the closure of the open parameter interval `(0,1)`. -/
theorem zero_mem_closure_unitIoo : (0 : ℝ) ∈ closure unitIoo := by
  rw [unitIoo, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  constructor <;> norm_num

/-- `1` lies in the closure of the open parameter interval `(0,1)`. -/
theorem one_mem_closure_unitIoo : (1 : ℝ) ∈ closure unitIoo := by
  rw [unitIoo, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  constructor <;> norm_num

/-- The image of the interior parameter set under `Subtype.val : Icc 0 1 → ℝ`
is exactly the open interval `(0,1)`. -/
theorem image_param_eq_unitIoo :
    ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) '' {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo}
      = unitIoo := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro hx
    refine ⟨⟨x, ?_⟩, hx, rfl⟩
    rw [unitIoo, Set.mem_Ioo] at hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- The subtype point `src = ⟨0,_⟩` is in the closure of the interior parameter
set inside `Set.Icc 0 1`.  Proof: pull through the inducing embedding
`Set.Icc 0 1 ↪ ℝ` (`closure_subtype`) and use `0 ∈ closure (Ioo 0 1)`. -/
theorem src_mem_closure_param :
    (SimpleArc.src : Set.Icc (0 : ℝ) 1) ∈
      closure {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} := by
  rw [closure_subtype, image_param_eq_unitIoo]
  exact zero_mem_closure_unitIoo

/-- The subtype point `tgt = ⟨1,_⟩` is in the closure of the interior parameter
set inside `Set.Icc 0 1`. -/
theorem tgt_mem_closure_param :
    (SimpleArc.tgt : Set.Icc (0 : ℝ) 1) ∈
      closure {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} := by
  rw [closure_subtype, image_param_eq_unitIoo]
  exact one_mem_closure_unitIoo

/-- **Endpoint-closure continuity fact (PROVEN).**  If the interior of a simple
arc `β` is contained in a set `R`, then the source endpoint `β src` lies in
`closure R`.  (No separation theory; pure continuity + density of `(0,1)` in
`[0,1]`.) -/
theorem arc_src_mem_closure {X : Type*} [TopologicalSpace X]
    (β : SimpleArc X) {R : Set X} (hβR : β.arcInterior ⊆ R) :
    β SimpleArc.src ∈ closure R := by
  have hmaps : Set.MapsTo β {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} R := by
    intro p hp
    exact hβR ⟨p, hp, rfl⟩
  have hcw : ContinuousWithinAt β {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo}
      SimpleArc.src :=
    (β.continuous_toFun.continuousWithinAt)
  exact hcw.mem_closure src_mem_closure_param hmaps

/-- **Endpoint-closure continuity fact (PROVEN), target endpoint.** -/
theorem arc_tgt_mem_closure {X : Type*} [TopologicalSpace X]
    (β : SimpleArc X) {R : Set X} (hβR : β.arcInterior ⊆ R) :
    β SimpleArc.tgt ∈ closure R := by
  have hmaps : Set.MapsTo β {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} R := by
    intro p hp
    exact hβR ⟨p, hp, rfl⟩
  have hcw : ContinuousWithinAt β {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo}
      SimpleArc.tgt :=
    (β.continuous_toFun.continuousWithinAt)
  exact hcw.mem_closure tgt_mem_closure_param hmaps

/-! ## §3  Componentology of a two-sided partition  [PROVEN]

The connectedness plumbing: a two-sided open partition `W = U ∪ V` has the two
pieces `U`, `V` as its connected components, hence *exactly two* components.
Pure `IsPreconnected` reasoning; no geometry, no simple connectivity. -/

variable {X : Type*} [TopologicalSpace X]

/-- In a two-sided open partition, the relative connected component (inside `W`)
of any point of `U` is exactly `U`. -/
theorem connectedComponentIn_left_eq {W U V : Set X}
    (h : IsTwoSidedPartition W U V) {x : X} (hx : x ∈ U) :
    connectedComponentIn W x = U := by
  have hxW : x ∈ W := h.union_eq ▸ Or.inl hx
  apply Set.Subset.antisymm
  · -- the component is preconnected, sits in `W = U ∪ V`, meets `U`, so ⊆ `U`
    have hsub : connectedComponentIn W x ⊆ U ∪ V := by
      rw [h.union_eq]; exact connectedComponentIn_subset W x
    have hmeet : (connectedComponentIn W x ∩ U).Nonempty :=
      ⟨x, mem_connectedComponentIn hxW, hx⟩
    exact (isPreconnected_connectedComponentIn).subset_left_of_subset_union
      h.isOpen_left h.isOpen_right h.disjoint hsub hmeet
  · -- `U` is preconnected, contains `x`, sits in `W`, so ⊆ the component
    exact h.preconnected_left.subset_connectedComponentIn hx
      (h.union_eq ▸ Set.subset_union_left)

/-- In a two-sided open partition, the relative connected component of any point
of `V` is exactly `V`. -/
theorem connectedComponentIn_right_eq {W U V : Set X}
    (h : IsTwoSidedPartition W U V) {x : X} (hx : x ∈ V) :
    connectedComponentIn W x = V := by
  have hxW : x ∈ W := h.union_eq ▸ Or.inr hx
  apply Set.Subset.antisymm
  · have hsub : connectedComponentIn W x ⊆ V ∪ U := by
      rw [Set.union_comm, h.union_eq]; exact connectedComponentIn_subset W x
    have hmeet : (connectedComponentIn W x ∩ V).Nonempty :=
      ⟨x, mem_connectedComponentIn hxW, hx⟩
    exact (isPreconnected_connectedComponentIn).subset_left_of_subset_union
      h.isOpen_right h.isOpen_left h.disjoint.symm hsub hmeet
  · exact h.preconnected_right.subset_connectedComponentIn hx
      (h.union_eq ▸ Set.subset_union_right)

/-- **Splitting predicate.**  `W` splits into *exactly two* connected components:
there are two points whose relative components are distinct, and every point of
`W` has one of those two as its component.  Stated purely via
`connectedComponentIn`, avoiding the `ConnectedComponents` quotient cardinality. -/
def SplitsIntoTwo (W : Set X) : Prop :=
  ∃ x₁ ∈ W, ∃ x₂ ∈ W,
    connectedComponentIn W x₁ ≠ connectedComponentIn W x₂ ∧
    ∀ y ∈ W, connectedComponentIn W y = connectedComponentIn W x₁ ∨
             connectedComponentIn W y = connectedComponentIn W x₂

/-- **Componentology core (PROVEN).**  A two-sided open partition splits `W` into
exactly two connected components, namely `U` and `V`. -/
theorem exactly_two_of_isTwoSidedPartition {W U V : Set X}
    (h : IsTwoSidedPartition W U V) : SplitsIntoTwo W := by
  obtain ⟨x₁, hx₁⟩ := h.nonempty_left
  obtain ⟨x₂, hx₂⟩ := h.nonempty_right
  have hx₁W : x₁ ∈ W := h.union_eq ▸ Or.inl hx₁
  have hx₂W : x₂ ∈ W := h.union_eq ▸ Or.inr hx₂
  have hc₁ : connectedComponentIn W x₁ = U := connectedComponentIn_left_eq h hx₁
  have hc₂ : connectedComponentIn W x₂ = V := connectedComponentIn_right_eq h hx₂
  refine ⟨x₁, hx₁W, x₂, hx₂W, ?_, ?_⟩
  · -- distinct: `U ≠ V` since they are disjoint and both nonempty
    rw [hc₁, hc₂]
    intro hUV
    have : x₁ ∈ U ∩ V := ⟨hx₁, hUV ▸ hx₁⟩
    exact (Set.disjoint_iff.mp h.disjoint) this
  · -- every point's component is `U` or `V`
    intro y hy
    rw [hc₁, hc₂]
    rcases (h.union_eq ▸ hy : y ∈ U ∪ V) with hyU | hyV
    · exact Or.inl (connectedComponentIn_left_eq h hyU)
    · exact Or.inr (connectedComponentIn_right_eq h hyV)

/-- **Converse componentology (PROVEN).**  For an *open* `W` in a locally
connected space, a `SplitsIntoTwo` witness yields a genuine two-sided open
partition: the two distinct relative components are the two sides.  Combined with
`exactly_two_of_isTwoSidedPartition`, this shows the two formulations coincide for
open `W` (see `splitsIntoTwo_iff_isTwoSidedPartition`), so the residual's
conclusion shape is canonical. -/
theorem isTwoSidedPartition_of_splitsIntoTwo [LocallyConnectedSpace X]
    {W : Set X} (hW : IsOpen W) (h : SplitsIntoTwo W) :
    ∃ U V, IsTwoSidedPartition W U V := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hne, hcover⟩ := h
  refine ⟨connectedComponentIn W x₁, connectedComponentIn W x₂,
    { isOpen_left := hW.connectedComponentIn
      isOpen_right := hW.connectedComponentIn
      disjoint := ?_
      union_eq := ?_
      nonempty_left := ⟨x₁, mem_connectedComponentIn hx₁⟩
      nonempty_right := ⟨x₂, mem_connectedComponentIn hx₂⟩
      preconnected_left := isPreconnected_connectedComponentIn
      preconnected_right := isPreconnected_connectedComponentIn }⟩
  · -- distinct relative components are disjoint
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hne ((connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm)
  · -- the two components cover `W`
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset W x₁)
        (connectedComponentIn_subset W x₂)
    · intro y hy
      rcases hcover y hy with hy1 | hy2
      · exact Or.inl (hy1 ▸ mem_connectedComponentIn hy)
      · exact Or.inr (hy2 ▸ mem_connectedComponentIn hy)

/-- **Equivalence of the two split formulations for open sets (PROVEN).**
`SplitsIntoTwo W ↔ ∃ U V, IsTwoSidedPartition W U V`, for `W` open in a locally
connected space. -/
theorem splitsIntoTwo_iff_isTwoSidedPartition [LocallyConnectedSpace X]
    {W : Set X} (hW : IsOpen W) :
    SplitsIntoTwo W ↔ ∃ U V, IsTwoSidedPartition W U V :=
  ⟨isTwoSidedPartition_of_splitsIntoTwo hW,
    fun ⟨_, _, h⟩ => exactly_two_of_isTwoSidedPartition h⟩

/-! ## §4  The (MS) statement and its assembly

`R` is a connected component of `ℝ² ∖ A` (`A` closed); we record the hypotheses
abstractly so the statement is self-contained.  The simply-connected hypothesis
is carried as `IsSimplyConnected R` (mathlib's subspace predicate). -/

/-- Ambient plane.  (`ℝ × ℝ`; the carrier `DrawnMultigraph` uses the same type,
though we do not import it.)  `ℝ × ℝ` is a finite-dimensional real normed space,
hence locally (path-)connected — so connected components of open sets are open,
which §3 needs. -/
abbrev Plane := ℝ × ℝ

/-- The hypotheses of (MS), bundled — the **crosscut** configuration.  `R` is a
*simply connected, open* connected component of the complement of a closed set
`A`, and `β` is a simple arc whose interior lies in `R` and whose **two endpoints
lie on the frontier `∂R`** (a *crosscut* of `R`).

**Why frontier, not merely `closure R` (a CORRECTNESS fix).**  The loose informal
phrasing "endpoints in the closure of `R`" is *not* sufficient for separation: an
arc with an endpoint in the open interior of `R` (e.g. a chord both of whose ends
sit inside a disk) does **not** separate `R` — its complement in `R` stays
connected, so "splits into exactly two" is FALSE.  Separation needs the endpoints
on `∂R`, i.e. the standard crosscut hypothesis.  In the BR-3b application the
endpoints are existing vertices/points of the arrangement `A ⊆ ∂R`, so this is
automatically met.  (Note `frontier R ⊆ closure R`, so the endpoint-closure facts
of §2 still apply; frontier is strictly stronger.) -/
structure ArcInRegion (A R : Set Plane) (β : SimpleArc Plane) : Prop where
  isClosed_A : IsClosed A
  isOpen_R : IsOpen R
  /-- `R` is a connected component of the complement `ℝ² ∖ A`. -/
  isComponent : ∃ x ∈ R, R = connectedComponentIn Aᶜ x
  simplyConnected : IsSimplyConnected R
  interior_subset : β.arcInterior ⊆ R
  /-- interior disjoint from `A` is implied by `interior ⊆ R ⊆ Aᶜ`; recorded. -/
  interior_disjoint_A : Disjoint β.arcInterior A
  /-- **Crosscut condition**: the source endpoint lies on the frontier of `R`. -/
  src_mem_frontier : β SimpleArc.src ∈ frontier R
  /-- **Crosscut condition**: the target endpoint lies on the frontier of `R`. -/
  tgt_mem_frontier : β SimpleArc.tgt ∈ frontier R

/-- The set that (MS) claims splits in two: the region with the arc removed. -/
def regionMinusArc (R : Set Plane) (β : SimpleArc Plane) : Set Plane :=
  R \ β.carrier

/-- The carrier of an arc in the plane is compact (continuous image of the compact
`Set.Icc 0 1`).  [PROVEN] -/
theorem carrier_isCompact (β : SimpleArc Plane) : IsCompact β.carrier :=
  isCompact_range β.continuous_toFun

/-- The carrier of an arc in the plane is closed (compact in a Hausdorff space).
[PROVEN] -/
theorem carrier_isClosed (β : SimpleArc Plane) : IsClosed β.carrier :=
  (carrier_isCompact β).isClosed

/-- **The region-minus-arc is open in the plane (PROVEN).**  `R` open minus the
closed carrier is open.  This is exactly what makes the §3 componentology
applicable: the connected components of an *open* subset of the (locally
connected) plane are themselves ambient-open, so the two "sides" the residual
must produce are guaranteed open once they are shown to be the components. -/
theorem regionMinusArc_isOpen {R : Set Plane} (β : SimpleArc Plane)
    (hR : IsOpen R) : IsOpen (regionMinusArc R β) :=
  hR.sdiff (carrier_isClosed β)

/-! ## §5  The irreducible geometric residual  [CONJECTURED — the sole `sorry`]

Everything above is sorry-free.  The remaining content of (MS) is the production
of a two-sided open partition of `regionMinusArc R β` from the arc geometry +
simple connectivity of `R`.  THIS IS THE GENUINELY HARD, NON-ELEMENTARY PART and
is the *only* `sorry` in this file.  See the gap report at the bottom for why it
is Jordan-strength even with the simply-connected hypothesis, and for the precise
sub-obligations a future proof must discharge. -/

/-- **THE GEOMETRIC RESIDUAL (CONJECTURED; `sorry`).**  Under the (MS)
hypotheses, the region-minus-arc admits a two-sided open partition.

Producing the two open "sides" `U, V` (open *in the plane*, each connected,
disjoint, covering `R ∖ β`) is the irreducible Jordan-strength content.  Marked
`sorry`; NOT proven.  Do not depend on this for any axiom-clean result. -/
theorem exists_twoSidedPartition_of_arc {A R : Set Plane} {β : SimpleArc Plane}
    (h : ArcInRegion A R β) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β) U V := by
  sorry

/-- **(MS) — local arc-separation lemma.**  Assembled from the sorry-free
componentology (§3) and the geometric residual (§5).  Because it consumes
`exists_twoSidedPartition_of_arc`, this theorem currently inherits that lemma's
`sorry`; it is NOT axiom-clean.  The *statement* is the deliverable; its proof is
complete **modulo** the single residual. -/
theorem local_arc_separation {A R : Set Plane} {β : SimpleArc Plane}
    (h : ArcInRegion A R β) :
    SplitsIntoTwo (regionMinusArc R β) := by
  obtain ⟨U, V, hUV⟩ := exists_twoSidedPartition_of_arc h
  exact exactly_two_of_isTwoSidedPartition hUV

/-! ## §6  Gap report — what is PROVEN, what is the residual, why it is hard

### PROVEN, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`

* `arc_src_mem_closure`, `arc_tgt_mem_closure` — endpoint-closure continuity fact.
* `connectedComponentIn_left_eq`, `connectedComponentIn_right_eq`,
  `exactly_two_of_isTwoSidedPartition` — a two-sided open partition has exactly
  two connected components.
* `isTwoSidedPartition_of_splitsIntoTwo`, `splitsIntoTwo_iff_isTwoSidedPartition`
  — converse + equivalence for open `W` (the conclusion shape is canonical).
* `carrier_isCompact`, `carrier_isClosed`, `regionMinusArc_isOpen` — the
  region-minus-arc is open in the plane (so its components are ambient-open).

`local_arc_separation` (the assembled (MS)) is PROVEN **modulo exactly one**
residual; it carries `sorryAx` solely through `exists_twoSidedPartition_of_arc`.

### THE RESIDUAL (CONJECTURED, the only `sorry`):  `exists_twoSidedPartition_of_arc`

> Given `A` closed, `R` an open simply connected component of `Aᶜ`, and `β` a
> simple arc with `arcInterior ⊆ R` and both endpoints on `frontier R` (a
> crosscut), the open set `R ∖ β.carrier` decomposes as `U ∪ V` with `U,V`
> nonempty, disjoint, plane-open, and connected.

This is the **crosscut theorem** for a simply connected planar domain (Newman,
*Elements of the Topology of Plane Sets of Points*; Pommerenke, *Boundary
Behaviour of Conformal Maps*, Prop. 2.12).  It is TRUE, and it is genuinely
non-elementary.

**Why simple connectivity does not make it elementary in mathlib v4.27.0.**
The classical proofs go through one of:
  (a) **Riemann mapping + boundary correspondence**: conformally map `R` to the
      open disk; a crosscut maps to a crosscut of the disk, where separation is
      explicit.  Mathlib v4.27.0 has NEITHER the Riemann mapping theorem (searched:
      no `RiemannMapping` / uniformization / biholomorphism-to-disk anywhere in
      `Mathlib/`; only the local `Conformal`/`Schwarz` material exists) NOR the
      Carathéodory boundary correspondence.  Not portable.
  (b) **Jordan curve / Jordan–Schoenflies**: close `β` up to a loop through an
      arc of `∂R` (or to ∞) and invoke separation.  Mathlib has NO Jordan curve
      theorem (`docs/1000.yaml` lists it UNFORMALIZED, no `decl`), no plane
      separation, no Schoenflies.  Not portable.
  (c) **Direct π₁/homology**: removing a crosscut changes `H₀`/`π₀` by exactly
      one.  This is the route that should connect to `IsSimplyConnected R`
      (mathlib gives `simply_connected_iff_paths_homotopic'`: any two paths in `R`
      with fixed ends are `Path.Homotopic`), but mathlib has **no Mayer–Vietoris,
      no π₀-of-a-complement, no `H₁`(open planar set)** API to execute it.

**Precise residual sub-obligations** (a future proof must supply ALL of):
  1. **`R ∖ β.carrier` is NONEMPTY and DISCONNECTED** ("at least two"): exhibit
     two points of `R ∖ β.carrier` in different components.  Requires the
     *non-existence* of a connecting path — the separating direction.  No mathlib
     primitive yields this without (a)/(b)/(c).
  2. **AT MOST two components**: every point of `R ∖ β.carrier` lies in one of two
     designated components.  Equally Jordan-strength.
  3. **Each side is connected** (`IsPreconnected U`, `IsPreconnected V`): the two
     sides are not further subdivided — uses simple connectivity of `R` crucially
     (false without it: an annulus crosscut can leave a connected-but-not-simply
     -connected piece, or for a non-crosscut arc the complement stays connected).

**Honest classification:** the residual is **CONJECTURED-feasible, NOT
PROVEN-tractable** in Lean.  It is strictly weaker than the Jordan curve theorem
(the simply-connected restriction removes the genus/winding content, per
`nthdegree get 01KSHGYWMT6QZV7N008TR123AV`), but "weaker than JCT" ≠ "short in
Lean": mathlib has no plane-graph-faces / region-separation / Mayer–Vietoris API,
so it is a from-scratch bespoke development.  Effort: the dominant remaining
variance of card BR-3b (rated ~1–4 sessions in the route-(B) plan §7).

**OUT OF SCOPE (do NOT attempt here):** the full Jordan curve theorem; global
plane separation of an arbitrary simple closed curve; `IsSemialgebraic` /
o-minimal structure — all three are absent from mathlib and explicitly off the
table for this lemma.
-/

end CrossingLemma.PlaneArcSeparation
