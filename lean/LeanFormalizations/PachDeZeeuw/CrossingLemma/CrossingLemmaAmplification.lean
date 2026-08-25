/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

/-!
# Cleared-parameter amplification of the bounded-multiplicity crossing lemma

This file proves the arithmetic amplification step of the bounded-multiplicity
crossing lemma. It derives the cubed target

  `CrossingLemmaMultigraphStatement`  :  `e³ ≤ 64·M·v²·cr`
  (when `0 < M`, multiplicity `≤ M`, the arcs join their declared endpoints,
  and `e ≥ 4·M·v`)

(defined in `CrossingLemma.lean`) **from an assumed weak bound** `hweak`.

The exact provenance of that weak bound is Géza Tóth, _Generalizations of the Crossing
Lemma_, Theorem 7 (arXiv v1: Theorem 0.3.1),
<https://arxiv.org/abs/2509.14074>, DOI
<https://doi.org/10.1007/978-3-032-18810-6_16>. Its proof first samples vertices with
probability `p`, then retains at most one edge from each parallel class, with each
original edge retained with probability `1/M`. Thus edges and crossings survive with
probabilities `p²/M` and `p⁴/M²`, respectively. Applying the simple planar weak bound
to the resulting simple graph gives the formula encoded by `WeakAveragedBound` below.
That random-thinning producer is **not yet formalized here**.

A public Lean 4 comparison is the sorry-free development
[`wpegden/crossing-consequences`](https://github.com/wpegden/crossing-consequences),
commit `8769d142033fce042f502bf2857afb6b1375b5c3`. Its
`Tablet.CrossingLemma` theorem is stated for `SimpleGraph` with denominator `100`,
and its proof locally derives the sharper simple-graph inequality
`e³ ≤ 64·v²·cr`. It therefore formalizes the `M = 1` vertex-sampling argument,
but it has no multiplicity parameter and does not prove `WeakAveragedBound`.

It imports `Mathlib`, the standalone `CrossingLemma` surface, and the standalone
combinatorial-map planar edge bound. It mentions no algebraic curves. The umbrella
module `PachDeZeeuw.CrossingLemma` imports this file, but that does not turn the
assumed `WeakAveragedBound` into a proof.

## The mathematics, and why `hweak` has the shape it does (read before trusting the constant)

The standard simple-graph crossing lemma `cr ≥ e³/(64 v²)` (`e ≥ 4v`) is proved by:
*weak bound* `cr ≥ e − 3v` (delete one edge per crossing → planar → Euler `e ≤ 3v−6`),
then *probabilistic amplification* — keep each vertex independently with probability
`p`, so `E[v_p] = p v`, `E[e_p] = p² e`, `E[cr_p] = p⁴ cr` (each crossing has 4
distinct endpoints); the weak bound in expectation gives `p⁴ cr ≥ p² e − 3 p v`, and
`p = 4v/e ≤ 1` (legal since `e ≥ 4v`) yields exactly `cr ≥ e³/(64 v²)`.

**Two facts explain the precise shape of `hweak` below.**

1. **The single `M` comes from thinning parallel classes, not from the linear
   multigraph weak bound alone.** Vertex-subset averaging of
   `e_S ≤ 3 M v_S + cr_S` yields the weaker `e³ ≤ 64 M² v² cr`. Tóth's Theorem 7
   proof obtains the sharp single-`M` dependence by the additional `1/M` edge-thinning
   step above. Székely's 1997 Theorem 7 is the original bounded-multiplicity theorem;
   Pach–Tóth, _A crossing lemma for multigraphs_, eq. (1), records the final
   `cr ≥ e³/(64 M v²)` consequence. Neither is the source of the intermediate formula:
   that formula occurs explicitly in Tóth's proof.

2. **The integer optimal-`s` choice is genuinely obstructed; the rational sampling
   parameter `p` is essential.**
   The *derandomized* (sum-over-size-`s`-subsets) version replaces `p` by `s/v` with
   integer `s ∈ {4,…,v}` and uses the double-count identities
   `Σ_{|S|=s} e_S = e·C(v−2,s−2)`, `Σ_{|S|=s} cr_S = cr·C(v−4,s−4)`,
   `Σ_{|S|=s} v_S = s·C(v,s)` (all verified by brute force). When the continuous optimum
   `s* = 4·M·v²/e` falls **below 4** (large-`e` regime, e.g. `v=8, e=332, M=1` gives
   `s* ≈ 0.77`), no admissible integer `s ≥ 4` exists, and the integer averaging loses
   up to a factor ≈ 2 in the constant — so the *exact* `1/64` is **not** recoverable by
   pure integer averaging. The variable rational parameter is essential. Accordingly
   `hweak` is stated as the **cleared, division-free rational-`p` form**, which the
   averaging/probabilistic argument supplies directly and which the single substitution
   `p = 4Mv/e` turns into the exact target in clean ℕ arithmetic — no discretization.

### Statement of `hweak` (the cleared division-free form)

Writing `p = a/b` and multiplying the real bound `p⁴ cr ≥ M p² e − 3 M² p v` through by
`b⁴ > 0` gives the subtraction-free ℕ inequality

  `M · a² · b² · e  ≤  a⁴ · cr  +  3 · M² · a · b³ · v`     (for all `0 < a ≤ b`).

At `a = 4·M·v`, `b = e` this reduces (cancel `4 M³ v²`) to exactly `e³ ≤ 64 M v² cr`.
This is `WeakAveragedBound` below. Tóth's Theorem 7 proof derives it in the form
`p⁴/M² · cr ≥ p²/M · e - 3p · v`; multiplying by `M²` and clearing `p = a/b`
gives the displayed natural-number inequality. Lean proves that this hypothesis implies
the target, but the global `M`-uniform producer for the hypothesis remains open.

## Honest status

* **PROVEN sorry-free:** `crossingLemma_of_weakBound` — the reduction
  `WeakAveragedBound → CrossingLemmaMultigraphStatement`. This is the deliverable's
  core: the amplification arithmetic itself, carried entirely in ℕ, no `rpow`.
* **PROVEN sorry-free:** the Bernoulli vertex-sampling layer for simple independent
  drawings:
  `IndependentSimpleInducedWeakBound → IndependentSimpleWeakAveragedBound`, including
  the cleared finite-sum double counts for `E[v_p] = pv`, `E[e_p] = p²e`, and
  `E[cr_p] = p⁴cr`.
* **STATEMENT-SURFACE:** `WeakAveragedBound` — supported by Tóth's Theorem 7
  proof, but not produced by any theorem in this library. Pegden's public
  simple-graph formalization covers the `M = 1` sampling argument only; it does
  not supply the parallel-class thinning quantified here.
* **Scaffolding, sorry-free:** the surviving-count definitions
  (`edgesOn`, `crossingPairs`, `crossingsOn`) and endpoint-set count lemmas used by
  the rational-parameter averaging proof.
* **Labelled OBSTRUCTION (`sorry`):** `vertexSubsetAveraging_bound` — the integer
  double-count master inequality, which (a) needs the `C(v−2,s−2)` / `C(v−4,s−4)` /
  `C(v,s)` `Finset.powersetCard` double counts AND (b) per fact 2 above *cannot* close
  the exact constant by itself. It is present only as documentation of the integer
  route and is **not used** by `crossingLemma_of_weakBound`.

No `axiom` is introduced. Axiom status of any downstream consumer is verified centrally;
this file does not assert axiom-cleanliness.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open scoped BigOperators

/-! ## 1. The assumed weak bound (`hweak`)

The cleared, division-free real-`p` averaging bound. Quantified over all `G` and `M`
so it can serve as a single hypothesis of the top theorem; the substance is the
per-`(a,b)` inequality, with `p = a/b` ranging over `(0,1]`. -/

/-- **`WeakAveragedBound`** — the bounded-multiplicity averaged weak bound.

For every drawn multigraph `G` and multiplicity cap `M > 0` with
`G.multiplicity ≤ M` everywhere, `G.ArcsJoinEndpoints`, and `G` `WellDrawn`,
and for every rational sampling parameter `p = a/b ∈ (0,1]` (encoded as
`0 < a ≤ b` in `ℕ`, cleared by `b⁴`):

  `M · a² · b² · e  ≤  a⁴ · cr  +  3 · M² · a · b³ · v`,

where `e = G.numEdges`, `v = G.V.card`, `cr = G.crossings`.

Literature provenance: Tóth, _Generalizations of the Crossing Lemma_, Theorem 7
(arXiv v1: Theorem 0.3.1), derives
`p⁴/M² · cr ≥ p²/M · e - 3p · v`. Multiplying by `M²`, setting `p = a/b`, and
clearing `b⁴` gives exactly the displayed inequality. The factors `M` and `3M²`
come from retaining at most one edge per parallel class after vertex sampling.

This declaration is a literature-backed statement-surface: no theorem in this library
currently proves it. The sorry-free public Lean development
`wpegden/crossing-consequences` proves the simple-graph sampling argument (and derives
the `1/64` simple-graph inequality internally), but it does not quantify a multiplicity
cap or formalize Tóth's parallel-class thinning. -/
def WeakAveragedBound : Prop :=
  ∀ (G : DrawnMultigraph) (M : ℕ),
    0 < M →
    (∀ p q, G.multiplicity p q ≤ M) →
    G.ArcsJoinEndpoints →
    G.WellDrawn →
    ∀ a b : ℕ, 0 < a → a ≤ b →
      M * a ^ 2 * b ^ 2 * G.numEdges ≤
        a ^ 4 * G.crossings + 3 * M ^ 2 * a * b ^ 3 * G.V.card

/-- **`SimpleWeakAveragedBound`** — the simple-graph averaged weak bound.

This is the cleared, rational-parameter form of the expectation inequality in
the standard ACNS/Leighton proof of the Crossing Lemma, as stated in Theorem
0.2.1 of the arXiv version of Tóth's _Generalizations of the Crossing Lemma_
(<https://arxiv.org/abs/2509.14074>). For a simple
drawn graph (`multiplicity ≤ 1`) whose arcs join their declared endpoints and
`p = a / b ∈ (0,1]`, the weak bound `cr(G') ≥ e(G') - 3 n(G')` on the random
induced subgraph gives

  `p⁴ cr(G) ≥ p² e(G) - 3 p n(G)`.

After multiplying by `b⁴`, this becomes

  `a² b² e ≤ a⁴ cr + 3 a b³ v`.

This statement is kept separate from `WeakAveragedBound`: it is the exact
`M = 1` layer needed by the Szemerédi--Trotter/grid-rich path. -/
def SimpleWeakAveragedBound : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.WellDrawn →
    ∀ a b : ℕ, 0 < a → a ≤ b →
      a ^ 2 * b ^ 2 * G.numEdges ≤
        a ^ 4 * G.crossings + 3 * a * b ^ 3 * G.V.card

/-- **`IndependentSimpleWeakAveragedBound`** — the simple averaged weak bound
for drawings whose counted crossings are independent.

This is the precise drawing-level form of the ACNS/Leighton expectation step:
the extra `G.CrossingsAreIndependent` hypothesis is what makes the crossing
survival probability `p^4`. -/
def IndependentSimpleWeakAveragedBound : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ a b : ℕ, 0 < a → a ≤ b →
      a ^ 2 * b ^ 2 * G.numEdges ≤
        a ^ 4 * G.crossings + 3 * a * b ^ 3 * G.V.card

/-- The simple averaged weak bound for one fixed drawing.  This is the local
form actually used by the Szemerédi--Trotter incidence graph: once the weak
inequality is known for that drawing, the remaining amplification is pure
arithmetic. -/
def LocalSimpleWeakAveragedBound (G : DrawnMultigraph) : Prop :=
  ∀ a b : ℕ, 0 < a → a ≤ b →
    a ^ 2 * b ^ 2 * G.numEdges ≤
      a ^ 4 * G.crossings + 3 * a * b ^ 3 * G.V.card

/-! ## 2. The amplification: `WeakAveragedBound → CrossingLemmaMultigraphStatement`

The deliverable's core. From `hweak` instantiated at `a = 4·M·v`, `b = e`, the cubed
target follows by pure ℕ arithmetic (a single cancellation), with no `Real.rpow`. -/

/-- A drawn multigraph with no vertices has no edges (endpoints must lie in `V = ∅`). -/
theorem numEdges_eq_zero_of_no_vertices (G : DrawnMultigraph) (hV : G.V.card = 0) :
    G.numEdges = 0 := by
  by_contra h
  -- a positive `numEdges` gives an edge `0 : Fin G.numEdges`, whose first endpoint ∈ V.
  have hpos : 0 < G.numEdges := Nat.pos_of_ne_zero h
  have hmem := (G.endpoints_mem ⟨0, hpos⟩).1
  rw [Finset.card_eq_zero] at hV
  rw [hV] at hmem
  exact (Finset.notMem_empty _) hmem

/-- **Cleared-parameter amplification [PROVEN, sorry-free].**

`CrossingLemmaMultigraphStatement` follows from the assumed weak bound
`WeakAveragedBound`. The target `e³ ≤ 64·M·v²·cr` is the exact-constant
bounded-multiplicity consequence recorded in Pach–Tóth, eq. (1), while the assumed
weak formula comes from Tóth's Theorem 7 proof. This theorem formalizes only the
substitution `p = 4·M·v/e` and its cancellation, carried entirely in `ℕ`; it does not
prove `WeakAveragedBound`.

The proof: with `v := G.V.card`, `e := G.numEdges`, `cr := G.crossings`:
* if `v = 0` then `e = 0` and the target is `0 ≤ 0`;
* otherwise `v ≥ 1` and `M ≥ 1`, so `0 < 4·M·v ≤ e` (the second from the threshold
  hypothesis). Instantiate `hweak` at `a = 4·M·v`, `b = e`:
  `M·(4Mv)²·e²·e ≤ (4Mv)⁴·cr + 3·M²·(4Mv)·e³·v`, i.e.
  `16·M³·v²·e³ ≤ 256·M⁴·v⁴·cr + 12·M³·v²·e³`, hence
  `4·M³·v²·e³ ≤ 256·M⁴·v⁴·cr`. Cancelling the positive factor `4·M³·v²`
  gives `e³ ≤ 64·M·v²·cr`. -/
theorem crossingLemma_of_weakBound (hweak : WeakAveragedBound) :
    CrossingLemmaMultigraphStatement := by
  intro G M hM hmult hjoin hwd hthresh
  set v := G.V.card with hv
  set e := G.numEdges with he
  set cr := G.crossings with hcr
  -- Case `v = 0`: then `e = 0` and the goal is trivial.
  rcases Nat.eq_zero_or_pos v with hv0 | hvpos
  · have he0 : e = 0 := by
      rw [he]; exact numEdges_eq_zero_of_no_vertices G (by rw [← hv]; exact hv0)
    rw [he0, hv0]; simp
  -- Case `v ≥ 1`. Instantiate hweak at a = 4*M*v, b = e.
  · have ha : 0 < 4 * M * v := by positivity
    have hab : 4 * M * v ≤ e := hthresh
    have key := hweak G M hM hmult hjoin hwd (4 * M * v) e ha hab
    -- `key : M * (4*M*v)^2 * e^2 * e ≤ (4*M*v)^4 * cr + 3 * M^2 * (4*M*v) * e^3 * v`
    -- Extract the cleared intermediate `4*M^3*v^2*e^3 ≤ 256*M^4*v^4*cr`.
    have hmid : 4 * M ^ 3 * v ^ 2 * e ^ 3 ≤ 256 * M ^ 4 * v ^ 4 * cr := by
      nlinarith [key, sq_nonneg M, sq_nonneg v, sq_nonneg e]
    -- Rewrite both sides as a common positive multiple of the target, then cancel.
    have hposfac : 0 < 4 * M ^ 3 * v ^ 2 := by positivity
    have hrw : 256 * M ^ 4 * v ^ 4 * cr = (4 * M ^ 3 * v ^ 2) * (64 * M * v ^ 2 * cr) := by ring
    have hrw2 : 4 * M ^ 3 * v ^ 2 * e ^ 3 = (4 * M ^ 3 * v ^ 2) * e ^ 3 := by ring
    rw [hrw, hrw2] at hmid
    exact Nat.le_of_mul_le_mul_left hmid hposfac

/-- The local `M = 1` amplification: a fixed drawing satisfying the averaged
weak inequality obeys the cubed crossing bound in the high-edge regime. -/
theorem simpleCrossingBound_of_localWeakAveragedBound
    {G : DrawnMultigraph} (hweak : LocalSimpleWeakAveragedBound G)
    (hthresh : 4 * G.V.card ≤ G.numEdges) :
    G.numEdges ^ 3 ≤ 64 * G.V.card ^ 2 * G.crossings := by
  set v := G.V.card with hv
  set e := G.numEdges with he
  set cr := G.crossings with hcr
  rcases Nat.eq_zero_or_pos v with hv0 | hvpos
  · have he0 : e = 0 := by
      rw [he]; exact numEdges_eq_zero_of_no_vertices G (by rw [← hv]; exact hv0)
    rw [he0, hv0]; simp
  · have ha : 0 < 4 * v := by positivity
    have hab : 4 * v ≤ e := hthresh
    have key := hweak (4 * v) e ha hab
    have hmid : 4 * v ^ 2 * e ^ 3 ≤ 256 * v ^ 4 * cr := by
      nlinarith [key, sq_nonneg v, sq_nonneg e]
    have hposfac : 0 < 4 * v ^ 2 := by positivity
    have hrw : 256 * v ^ 4 * cr = (4 * v ^ 2) * (64 * v ^ 2 * cr) := by ring
    have hrw2 : 4 * v ^ 2 * e ^ 3 = (4 * v ^ 2) * e ^ 3 := by ring
    rw [hrw, hrw2] at hmid
    exact Nat.le_of_mul_le_mul_left hmid hposfac

/-- **Simple crossing lemma from the simple averaged weak bound.**

This is the `M = 1` amplification arithmetic in the standard crossing-lemma
proof. The only input is `SimpleWeakAveragedBound`; the proof then substitutes
`p = 4v/e`, encoded as `a = 4v`, `b = e`, and cancels the positive factor
`4v²`. -/
theorem simpleCrossingLemma_of_simpleWeakAveragedBound
    (hweak : SimpleWeakAveragedBound) :
    SimpleCrossingLemmaStatement := by
  intro G hmult hjoin hwd hthresh
  exact simpleCrossingBound_of_localWeakAveragedBound
    (fun a b ha hab => hweak G hmult hjoin hwd a b ha hab) hthresh

/-- The independent-drawing simple crossing lemma follows from the independent
simple averaged weak bound by the same `p = 4v/e` arithmetic. -/
theorem independentSimpleCrossingLemma_of_independentSimpleWeakAveragedBound
    (hweak : IndependentSimpleWeakAveragedBound) :
    IndependentSimpleCrossingLemmaStatement := by
  intro G hmult hjoin hcross hwd hthresh
  exact simpleCrossingBound_of_localWeakAveragedBound
    (fun a b ha hab => hweak G hmult hjoin hcross hwd a b ha hab) hthresh

/-! ## 3. Scaffolding for the integer-averaging route (documentation only)

These definitions and the `OBSTRUCTION` master inequality record the *derandomized
finite-sum* route the task envisioned. They are **not** used by
`crossingLemma_of_weakBound` (which takes the cleared real-`p` form directly), and are
kept so a future agent can see exactly where the integer route stands and why it cannot
close the exact constant alone (module docstring, fact 2).

The surviving-count quantities avoid constructing a sub-`DrawnMultigraph`: they count
directly which edges/crossings survive restricting to a vertex subset `S`. -/

section IntegerRoute

variable (G : DrawnMultigraph)

/-- Number of edges of `G` with **both** endpoints in the vertex subset `S` (the edge
count of the induced sub-drawing on `S`). -/
noncomputable def edgesOn (S : Finset (ℝ × ℝ)) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin G.numEdges => (G.endpoints i).1 ∈ S ∧ (G.endpoints i).2 ∈ S)).card

/-- The set of **independent** crossing edge-pairs `(i, j)` with `i < j` whose four
endpoints are pairwise distinct. The standard crossing lemma counts only such pairs
(adjacent edges are assumed not to cross), and it is exactly these that contribute the
`C(v−4, s−4)` factor in the averaging double count. Stored as a `Finset` of ordered
pairs `i < j` (via `Fin.val`) to avoid double counting. -/
noncomputable def crossingPairs : Finset (Fin G.numEdges × Fin G.numEdges) := by
  classical
  exact Finset.univ.filter
    (fun ij : Fin G.numEdges × Fin G.numEdges =>
      ij.1.val < ij.2.val ∧
      (interiorOfArc (G.arc ij.1) ∩ interiorOfArc (G.arc ij.2)).Nonempty ∧
      DrawnMultigraph.FourDistinctEndpoints G ij.1 ij.2)

/-- Number of independent crossing pairs all four of whose endpoints lie in `S` (the
crossing count of the induced sub-drawing on `S`, restricted to independent pairs). -/
noncomputable def crossingsOn (S : Finset (ℝ × ℝ)) : ℕ := by
  classical
  exact ((crossingPairs G).filter
    (fun ij : Fin G.numEdges × Fin G.numEdges =>
      (G.endpoints ij.1).1 ∈ S ∧ (G.endpoints ij.1).2 ∈ S ∧
      (G.endpoints ij.2).1 ∈ S ∧ (G.endpoints ij.2).2 ∈ S)).card

/-- The edge-index finset underlying `edgesOn G S`. -/
noncomputable def edgeSetOn (S : Finset (ℝ × ℝ)) : Finset (Fin G.numEdges) := by
  classical
  exact Finset.univ.filter
    (fun i : Fin G.numEdges => (G.endpoints i).1 ∈ S ∧ (G.endpoints i).2 ∈ S)

/-- The crossing-pair finset underlying `crossingsOn G S`. -/
noncomputable def crossingPairsOn (S : Finset (ℝ × ℝ)) :
    Finset (Fin G.numEdges × Fin G.numEdges) := by
  classical
  exact (crossingPairs G).filter
    (fun ij : Fin G.numEdges × Fin G.numEdges =>
      (G.endpoints ij.1).1 ∈ S ∧ (G.endpoints ij.1).2 ∈ S ∧
      (G.endpoints ij.2).1 ∈ S ∧ (G.endpoints ij.2).2 ∈ S)

/-- `edgeSetOn` has cardinality `edgesOn`. -/
theorem edgeSetOn_card (S : Finset (ℝ × ℝ)) :
    (edgeSetOn G S).card = edgesOn G S := by
  rfl

/-- `crossingPairsOn` has cardinality `crossingsOn`. -/
theorem crossingPairsOn_card (S : Finset (ℝ × ℝ)) :
    (crossingPairsOn G S).card = crossingsOn G S := by
  rfl

/-- On the full vertex set, `edgesOn` counts every edge (both endpoints are in `V`). -/
theorem edgesOn_univ : edgesOn G G.V = G.numEdges := by
  classical
  unfold edgesOn
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro i _
  exact ⟨(G.endpoints_mem i).1, (G.endpoints_mem i).2⟩

/-- On the full vertex set, `crossingsOn` counts every independent crossing pair. -/
theorem crossingsOn_univ : crossingsOn G G.V = (crossingPairs G).card := by
  classical
  unfold crossingsOn
  rw [Finset.filter_true_of_mem]
  intro ij _hij
  exact ⟨(G.endpoints_mem ij.1).1, (G.endpoints_mem ij.1).2,
    (G.endpoints_mem ij.2).1, (G.endpoints_mem ij.2).2⟩

/-- `edgesOn` is monotone in the vertex subset. -/
theorem edgesOn_mono {S T : Finset (ℝ × ℝ)} (h : S ⊆ T) : edgesOn G S ≤ edgesOn G T := by
  classical
  unfold edgesOn
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, h hi.2.1, h hi.2.2⟩

/-- `crossingsOn` is monotone in the vertex subset. -/
theorem crossingsOn_mono {S T : Finset (ℝ × ℝ)} (h : S ⊆ T) :
    crossingsOn G S ≤ crossingsOn G T := by
  classical
  unfold crossingsOn
  apply Finset.card_le_card
  intro ij hij
  rw [Finset.mem_filter] at hij ⊢
  exact ⟨hij.1, h hij.2.1, h hij.2.2.1, h hij.2.2.2.1, h hij.2.2.2.2⟩

/-- The independent crossing-pair scaffold is a subcount of the true geometric
crossing count. -/
theorem crossingPairs_card_le_crossingCount :
    (crossingPairs G).card ≤ G.crossingCount := by
  classical
  unfold crossingPairs DrawnMultigraph.crossingCount
  apply Finset.card_le_card
  intro ij hij
  rw [Finset.mem_filter] at hij ⊢
  exact ⟨hij.1, hij.2.1, hij.2.2.1⟩

/-- Under `WellDrawn`, the independent crossing-pair scaffold is bounded by the
declared crossing counter. -/
theorem crossingPairs_card_le_crossings (hwd : G.WellDrawn) :
    (crossingPairs G).card ≤ G.crossings :=
  (crossingPairs_card_le_crossingCount G).trans hwd

/-! ### Deleting one edge from each surviving crossing pair -/

/-- A finset of edge indices contains no independent crossing pair counted by
`crossingPairs G`. This is the finite-set form of "crossing-free" needed for
the deletion-to-planar weak bound. -/
def NoCrossingPairsInEdgeSet (E : Finset (Fin G.numEdges)) : Prop :=
  ∀ ij : Fin G.numEdges × Fin G.numEdges,
    ij ∈ crossingPairs G → ij.1 ∈ E → ij.2 ∈ E → False

/-- The deletion set for `S`: for each surviving crossing pair, delete its first
edge. This is the deterministic version of the literature instruction "delete
one edge at each crossing". -/
noncomputable def crossingDeletionSet (S : Finset (ℝ × ℝ)) : Finset (Fin G.numEdges) :=
  (crossingPairsOn G S).image Prod.fst

/-- The remaining surviving edges after deleting the first edge of every
surviving crossing pair. -/
noncomputable def remainingEdgeSet (S : Finset (ℝ × ℝ)) : Finset (Fin G.numEdges) :=
  edgeSetOn G S \ crossingDeletionSet G S

/-- The number of deleted edges is at most the number of surviving crossing
pairs. Multiple crossing pairs may delete the same first edge, so this is an
inequality, not an equality. -/
theorem crossingDeletionSet_card_le (S : Finset (ℝ × ℝ)) :
    (crossingDeletionSet G S).card ≤ crossingsOn G S := by
  unfold crossingDeletionSet
  calc
    ((crossingPairsOn G S).image Prod.fst).card ≤ (crossingPairsOn G S).card :=
      Finset.card_image_le
    _ = crossingsOn G S := crossingPairsOn_card G S

/-- Remaining edges are surviving edges. -/
theorem remainingEdgeSet_subset_edgeSetOn (S : Finset (ℝ × ℝ)) :
    remainingEdgeSet G S ⊆ edgeSetOn G S := by
  intro e he
  exact (Finset.mem_sdiff.mp he).1

/-- Deleting one edge from each surviving crossing pair loses at most
`crossingsOn G S` edges. -/
theorem edgesOn_le_remainingEdgeSet_card_add_crossingsOn (S : Finset (ℝ × ℝ)) :
    edgesOn G S ≤ (remainingEdgeSet G S).card + crossingsOn G S := by
  rw [← edgeSetOn_card G S]
  have hbase : (edgeSetOn G S).card ≤
      (edgeSetOn G S \ crossingDeletionSet G S).card +
        (crossingDeletionSet G S).card :=
    Finset.card_le_card_sdiff_add_card
  exact hbase.trans (Nat.add_le_add_left (crossingDeletionSet_card_le G S) _)

/-- After deleting the first edge of every surviving crossing pair, no counted
independent crossing pair remains. -/
theorem remainingEdgeSet_noCrossingPairs (S : Finset (ℝ × ℝ)) :
    NoCrossingPairsInEdgeSet G (remainingEdgeSet G S) := by
  classical
  intro ij hij hi hj
  have hi_edge : ij.1 ∈ edgeSetOn G S := (Finset.mem_sdiff.mp hi).1
  have hi_notdel : ij.1 ∉ crossingDeletionSet G S := (Finset.mem_sdiff.mp hi).2
  have hj_edge : ij.2 ∈ edgeSetOn G S := (Finset.mem_sdiff.mp hj).1
  rw [edgeSetOn, Finset.mem_filter] at hi_edge hj_edge
  have hijOn : ij ∈ crossingPairsOn G S := by
    rw [crossingPairsOn, Finset.mem_filter]
    exact ⟨hij, hi_edge.2.1, hi_edge.2.2, hj_edge.2.1, hj_edge.2.2⟩
  have hdel : ij.1 ∈ crossingDeletionSet G S := by
    rw [crossingDeletionSet, Finset.mem_image]
    exact ⟨ij, hijOn, rfl⟩
  exact hi_notdel hdel

/-- If counted crossings are independent, a finset with no counted crossing
pairs is geometrically crossing-free: distinct chosen edges have disjoint arc
interiors. This is the set-level form of the ACNS/Leighton hypothesis that
"only independent edges can cross". -/
theorem disjoint_interiors_of_noCrossingPairsInEdgeSet
    (hcross : G.CrossingsAreIndependent) {E : Finset (Fin G.numEdges)}
    (hfree : NoCrossingPairsInEdgeSet G E)
    {i j : Fin G.numEdges} (hi : i ∈ E) (hj : j ∈ E) (hne : i ≠ j) :
    Disjoint (interiorOfArc (G.arc i)) (interiorOfArc (G.arc j)) := by
  classical
  rw [Set.disjoint_left]
  intro x hxi hxj
  by_cases hlt : i.val < j.val
  · have hnonempty :
        (interiorOfArc (G.arc i) ∩ interiorOfArc (G.arc j)).Nonempty :=
      ⟨x, hxi, hxj⟩
    have hij : (i, j) ∈ crossingPairs G := by
      rw [crossingPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hlt, hnonempty, hcross i j hne hnonempty⟩
    exact hfree (i, j) hij hi hj
  · have hgt : j.val < i.val := by
      have hle : j.val ≤ i.val := Nat.le_of_not_lt hlt
      exact Nat.lt_of_le_of_ne hle (fun hval => hne (Fin.ext hval.symm))
    have hnonempty :
        (interiorOfArc (G.arc j) ∩ interiorOfArc (G.arc i)).Nonempty :=
      ⟨x, hxj, hxi⟩
    have hji : (j, i) ∈ crossingPairs G := by
      rw [crossingPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgt, hnonempty, hcross j i hne.symm hnonempty⟩
    exact hfree (j, i) hji hj hi

/-- The deterministic one-edge-per-crossing deletion leaves a geometrically
crossing-free surviving edge set, provided all true crossings in `G` are between
independent edges. -/
theorem remainingEdgeSet_disjoint_interiors
    (hcross : G.CrossingsAreIndependent) (S : Finset (ℝ × ℝ))
    {i j : Fin G.numEdges} (hi : i ∈ remainingEdgeSet G S)
    (hj : j ∈ remainingEdgeSet G S) (hne : i ≠ j) :
    Disjoint (interiorOfArc (G.arc i)) (interiorOfArc (G.arc j)) :=
  disjoint_interiors_of_noCrossingPairsInEdgeSet G hcross
    (remainingEdgeSet_noCrossingPairs G S) hi hj hne

/-! ### Abstract carrier for a crossing-free surviving edge set -/

/-- Forget a surviving edge set `E` over vertex set `S` to the abstract finite
multigraph consumed by the planar edge bound. -/
def abstractizeEdgeSet (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges))
    (hE : E ⊆ edgeSetOn G S) : AbstractPlanarizedMultigraph where
  Vertex := ↥S
  Edge := ↥E
  vertexFintype := FinsetCoe.fintype S
  edgeFintype := FinsetCoe.fintype E
  edgeVerts e := by
    have he : (e : Fin G.numEdges) ∈ edgeSetOn G S := hE e.2
    rw [edgeSetOn, Finset.mem_filter] at he
    exact s(⟨(G.endpoints e).1, he.2.1⟩, ⟨(G.endpoints e).2, he.2.2⟩)

/-- The abstract surviving-edge-set vertex count is `|S|`. -/
theorem abstractizeEdgeSet_vertex_card
    (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges)) (hE : E ⊆ edgeSetOn G S) :
    Fintype.card (abstractizeEdgeSet G S E hE).Vertex = S.card := by
  simp only [abstractizeEdgeSet]
  exact Fintype.card_coe S

/-- The abstract surviving-edge-set edge count is `|E|`. -/
theorem abstractizeEdgeSet_edge_card
    (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges)) (hE : E ⊆ edgeSetOn G S) :
    Fintype.card (abstractizeEdgeSet G S E hE).Edge = E.card := by
  simp only [abstractizeEdgeSet]
  exact Fintype.card_coe E

/-- Multiplicity `≤ M` transfers from the drawing to any surviving edge-set
carrier. -/
theorem abstractizeEdgeSet_pairMultiplicityBound
    (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges)) (M : ℕ)
    (hE : E ⊆ edgeSetOn G S) (hmult : ∀ p q, G.multiplicity p q ≤ M) :
    PairMultiplicityBound (abstractizeEdgeSet G S E hE) M := by
  classical
  refine fun uv => ?_
  refine Sym2.ind (fun a b => ?_) uv
  have hpred : ∀ e : ↥E,
      ((abstractizeEdgeSet G S E hE).edgeVerts e = s(a, b)) ↔
        (G.endpoints (e : Fin G.numEdges) = (a.val, b.val) ∨
          G.endpoints (e : Fin G.numEdges) = (b.val, a.val)) := by
    intro e
    simp only [abstractizeEdgeSet, Sym2.eq_iff, Prod.ext_iff, Subtype.ext_iff]
  have hmaps : Set.MapsTo (fun e : ↥E => (e : Fin G.numEdges))
      (↑(Finset.univ.filter fun e : ↥E =>
        (abstractizeEdgeSet G S E hE).edgeVerts e = s(a, b)))
      (↑(Finset.univ.filter fun i : Fin G.numEdges =>
        G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val))) := by
    intro e he
    have he' : e ∈ Finset.univ.filter fun e : ↥E =>
        (abstractizeEdgeSet G S E hE).edgeVerts e = s(a, b) := he
    rw [Finset.mem_filter] at he'
    change (e : Fin G.numEdges) ∈ Finset.univ.filter fun i : Fin G.numEdges =>
        G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hpred e).mp he'.2⟩
  have hinj : (↑(Finset.univ.filter fun e : ↥E =>
        (abstractizeEdgeSet G S E hE).edgeVerts e = s(a, b)) : Set ↥E).InjOn
      (fun e : ↥E => (e : Fin G.numEdges)) := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hcard_le :
      (Finset.univ.filter fun e : ↥E =>
        (abstractizeEdgeSet G S E hE).edgeVerts e = s(a, b)).card ≤
      (Finset.univ.filter fun i : Fin G.numEdges =>
        G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card :=
    Finset.card_le_card_of_injOn (fun e : ↥E => (e : Fin G.numEdges)) hmaps hinj
  have hmulteq :
      (Finset.univ.filter fun i : Fin G.numEdges =>
        G.endpoints i = (a.val, b.val) ∨ G.endpoints i = (b.val, a.val)).card
        = G.multiplicity a.val b.val := by
    rw [DrawnMultigraph.multiplicity]
  exact hcard_le.trans ((hmulteq.trans_le (hmult a.val b.val)))

/-- With multiplicity `≤ 1`, surviving edges inject into ordered endpoint pairs
in `S`; this handles the small-vertex cases of the planar edge bound. -/
theorem edgeSetOn_card_le_sq_of_multiplicity_one
    (S : Finset (ℝ × ℝ)) (hmult : ∀ p q, G.multiplicity p q ≤ 1) :
    (edgeSetOn G S).card ≤ S.card ^ 2 := by
  classical
  let f : Fin G.numEdges → (ℝ × ℝ) × (ℝ × ℝ) := fun e => G.endpoints e
  have hmaps : Set.MapsTo f (↑(edgeSetOn G S)) (↑(S ×ˢ S)) := by
    intro e he
    have he' : e ∈ edgeSetOn G S := he
    rw [edgeSetOn, Finset.mem_filter] at he'
    exact Finset.mem_product.mpr he'.2
  have hinj : (↑(edgeSetOn G S) : Set (Fin G.numEdges)).InjOn f := by
    intro e₁ _ e₂ _ hsame
    by_contra hne
    let p := (G.endpoints e₁).1
    let q := (G.endpoints e₁).2
    have he₁f : e₁ ∈ Finset.univ.filter
        (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inl rfl⟩
    have he₂f : e₂ ∈ Finset.univ.filter
        (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
      rw [Finset.mem_filter]
      have hpair : G.endpoints e₂ = (p, q) := hsame.symm
      exact ⟨Finset.mem_univ _, Or.inl hpair⟩
    have hlt : 1 < (Finset.univ.filter
        (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card := by
      rw [Finset.one_lt_card]
      exact ⟨e₁, he₁f, e₂, he₂f, hne⟩
    have hm : (Finset.univ.filter
        (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card ≤ 1 := by
      simpa [DrawnMultigraph.multiplicity, p, q] using hmult p q
    omega
  calc
    (edgeSetOn G S).card ≤ (S ×ˢ S).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = S.card ^ 2 := by rw [Finset.card_product]; ring

/-- With multiplicity `≤ M`, surviving edges are bounded by `M` times the
number of ordered endpoint pairs in `S`. This is the multiplicity-general
small-vertex estimate used by the multigraph crossing-lemma bridge. -/
theorem edgeSetOn_card_le_mul_sq_of_multiplicity
    (S : Finset (ℝ × ℝ)) (M : ℕ) (hmult : ∀ p q, G.multiplicity p q ≤ M) :
    (edgeSetOn G S).card ≤ M * S.card ^ 2 := by
  classical
  let f : Fin G.numEdges → (ℝ × ℝ) × (ℝ × ℝ) := fun e => G.endpoints e
  have hmaps : Set.MapsTo f (↑(edgeSetOn G S)) (↑(S ×ˢ S)) := by
    intro e he
    have he' : e ∈ edgeSetOn G S := he
    rw [edgeSetOn, Finset.mem_filter] at he'
    exact Finset.mem_product.mpr he'.2
  have hfiber_bound : ∀ uv ∈ (S ×ˢ S),
      ((edgeSetOn G S).filter fun e : Fin G.numEdges => f e = uv).card ≤ M := by
    intro uv huv
    have hsubset :
        (edgeSetOn G S).filter fun e : Fin G.numEdges => f e = uv
          ⊆ Finset.univ.filter fun i : Fin G.numEdges =>
            G.endpoints i = uv ∨ G.endpoints i = (uv.2, uv.1) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, Or.inl (by simpa [f] using hi.2)⟩
    have hle :
        ((edgeSetOn G S).filter fun e : Fin G.numEdges => f e = uv).card ≤
          (Finset.univ.filter fun i : Fin G.numEdges =>
            G.endpoints i = uv ∨ G.endpoints i = (uv.2, uv.1)).card :=
      Finset.card_le_card hsubset
    simpa [DrawnMultigraph.multiplicity] using hle.trans (hmult uv.1 uv.2)
  have hcard : (S ×ˢ S).card = S.card ^ 2 := by
    rw [Finset.card_product]
    ring
  calc
    (edgeSetOn G S).card =
        ∑ uv ∈ (S ×ˢ S), ((edgeSetOn G S).filter fun e : Fin G.numEdges => f e = uv).card := by
          simpa [f] using (Finset.card_eq_sum_card_fiberwise hmaps)
    _ ≤ ∑ uv ∈ (S ×ˢ S), M := Finset.sum_le_sum hfiber_bound
    _ = M * (S ×ˢ S).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ = M * S.card ^ 2 := by rw [hcard]

/-! ### Weighted powerset count for Bernoulli vertex sampling -/

/-- Weighted superset count. If `T ⊆ U`, then summing
`a ^ |S| * c ^ (|U|-|S|)` over all `S` with `T ⊆ S ⊆ U` gives
`a ^ |T| * (a+c) ^ (|U|-|T|)`.

This is the finite, denominator-free form of the elementary Bernoulli survival
calculation used in the ACNS/Leighton proof: after fixing the vertices in `T`,
each remaining vertex independently contributes either `a` (kept) or `c`
(discarded). -/
theorem weighted_superset_sum {α : Type*} [DecidableEq α]
    (U T : Finset α) (hT : T ⊆ U) (a c : ℕ) :
    (∑ S ∈ (U.powerset.filter (fun S => T ⊆ S)),
        a ^ S.card * c ^ (U.card - S.card))
      = a ^ T.card * (a + c) ^ (U.card - T.card) := by
  rw [← Finset.Icc_eq_filter_powerset T U]
  rw [Finset.Icc_eq_image_powerset hT]
  rw [Finset.sum_image]
  · calc
      (∑ x ∈ (U \ T).powerset, a ^ (T ∪ x).card * c ^ (U.card - (T ∪ x).card))
          = ∑ x ∈ (U \ T).powerset,
              a ^ (T.card + x.card) * c ^ ((U \ T).card - x.card) := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxsub : x ⊆ U \ T := Finset.mem_powerset.mp hx
              have hdisj : Disjoint T x := by
                rw [Finset.disjoint_left]
                intro y hyT hyx
                exact (Finset.mem_sdiff.mp (hxsub hyx)).2 hyT
              have hcard_union : (T ∪ x).card = T.card + x.card :=
                Finset.card_union_of_disjoint hdisj
              have hcard_sdiff : (U \ T).card = U.card - T.card :=
                Finset.card_sdiff_of_subset hT
              have hcard_diff : U.card - (T ∪ x).card = (U \ T).card - x.card := by
                rw [hcard_union, hcard_sdiff]
                omega
              rw [hcard_diff, hcard_union]
        _ = ∑ x ∈ (U \ T).powerset,
              (a ^ T.card) * (a ^ x.card * c ^ ((U \ T).card - x.card)) := by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [pow_add]
              ring
        _ = a ^ T.card *
              ∑ x ∈ (U \ T).powerset, a ^ x.card * c ^ ((U \ T).card - x.card) := by
              rw [Finset.mul_sum]
        _ = a ^ T.card * (a + c) ^ (U.card - T.card) := by
              rw [Finset.sum_pow_mul_eq_add_pow, Finset.card_sdiff_of_subset hT]
  · intro x hx y hy hxy
    change T ∪ x = T ∪ y at hxy
    have hxsub : x ⊆ U \ T := Finset.mem_powerset.mp hx
    have hysub : y ⊆ U \ T := Finset.mem_powerset.mp hy
    apply Finset.ext
    intro z
    constructor
    · intro hz
      have hzunion : z ∈ T ∪ x := Finset.mem_union_right T hz
      rw [hxy] at hzunion
      rcases Finset.mem_union.mp hzunion with hzT | hzy
      · exact False.elim ((Finset.mem_sdiff.mp (hxsub hz)).2 hzT)
      · exact hzy
    · intro hz
      have hzunion : z ∈ T ∪ y := Finset.mem_union_right T hz
      rw [← hxy] at hzunion
      rcases Finset.mem_union.mp hzunion with hzT | hzx
      · exact False.elim ((Finset.mem_sdiff.mp (hysub hz)).2 hzT)
      · exact hzx

/-- Weighted indicator form of `weighted_superset_sum`: the same sum over all
subsets of `U`, with non-supersets contributing zero. -/
theorem weighted_superset_indicator_sum {α : Type*} [DecidableEq α]
    (U T : Finset α) (hT : T ⊆ U) (a c : ℕ) :
    (∑ S ∈ U.powerset, (if T ⊆ S then a ^ S.card * c ^ (U.card - S.card) else 0))
      = a ^ T.card * (a + c) ^ (U.card - T.card) := by
  rw [← Finset.sum_filter]
  exact weighted_superset_sum U T hT a c

/-! ### Endpoint sets for the weighted double counts -/

/-- The two declared endpoint vertices of an edge, as a finset. -/
noncomputable def edgeEndpointSet (e : Fin G.numEdges) : Finset (ℝ × ℝ) := by
  classical
  exact {(G.endpoints e).1, (G.endpoints e).2}

/-- The four declared endpoint vertices of a pair of edges, as a finset. -/
noncomputable def crossingEndpointSet (ij : Fin G.numEdges × Fin G.numEdges) :
    Finset (ℝ × ℝ) := by
  classical
  exact {(G.endpoints ij.1).1, (G.endpoints ij.1).2,
    (G.endpoints ij.2).1, (G.endpoints ij.2).2}

/-- Every endpoint of an edge lies in the drawing's vertex set. -/
theorem edgeEndpointSet_subset (e : Fin G.numEdges) :
    edgeEndpointSet G e ⊆ G.V := by
  classical
  intro p hp
  rw [edgeEndpointSet] at hp
  rw [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp
  · rw [hp]; exact (G.endpoints_mem e).1
  · rw [hp]; exact (G.endpoints_mem e).2

/-- If the arcs join their declared endpoints, an edge endpoint set has size two. -/
theorem edgeEndpointSet_card (hjoin : G.ArcsJoinEndpoints) (e : Fin G.numEdges) :
    (edgeEndpointSet G e).card = 2 := by
  classical
  have hne := DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e
  simp [edgeEndpointSet, hne]

/-- Containment of the two-endpoint finset is exactly survival of the edge in `S`. -/
theorem edgeEndpointSet_subset_iff (e : Fin G.numEdges) (S : Finset (ℝ × ℝ)) :
    edgeEndpointSet G e ⊆ S ↔
      (G.endpoints e).1 ∈ S ∧ (G.endpoints e).2 ∈ S := by
  classical
  constructor
  · intro h
    exact ⟨h (by simp [edgeEndpointSet]), h (by simp [edgeEndpointSet])⟩
  · intro h p hp
    rw [edgeEndpointSet] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · rw [hp]; exact h.1
    · rw [hp]; exact h.2

/-- Every endpoint of an independent crossing pair lies in the drawing's vertex set. -/
theorem crossingEndpointSet_subset (ij : Fin G.numEdges × Fin G.numEdges) :
    crossingEndpointSet G ij ⊆ G.V := by
  classical
  intro p hp
  rw [crossingEndpointSet] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp | hp | hp
  · rw [hp]; exact (G.endpoints_mem ij.1).1
  · rw [hp]; exact (G.endpoints_mem ij.1).2
  · rw [hp]; exact (G.endpoints_mem ij.2).1
  · rw [hp]; exact (G.endpoints_mem ij.2).2

/-- A four-distinct-endpoints crossing pair has endpoint set of size four. -/
theorem crossingEndpointSet_card_of_fourDistinct
    {ij : Fin G.numEdges × Fin G.numEdges}
    (hij : DrawnMultigraph.FourDistinctEndpoints G ij.1 ij.2) :
    (crossingEndpointSet G ij).card = 4 := by
  classical
  rcases hij with ⟨h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
  simp [crossingEndpointSet, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]

/-- Containment of the four-endpoint finset is exactly survival of the crossing
pair in `S`. -/
theorem crossingEndpointSet_subset_iff
    (ij : Fin G.numEdges × Fin G.numEdges) (S : Finset (ℝ × ℝ)) :
    crossingEndpointSet G ij ⊆ S ↔
      (G.endpoints ij.1).1 ∈ S ∧ (G.endpoints ij.1).2 ∈ S ∧
        (G.endpoints ij.2).1 ∈ S ∧ (G.endpoints ij.2).2 ∈ S := by
  classical
  constructor
  · intro h
    exact ⟨h (by simp [crossingEndpointSet]), h (by simp [crossingEndpointSet]),
      h (by simp [crossingEndpointSet]), h (by simp [crossingEndpointSet])⟩
  · intro h p hp
    rw [crossingEndpointSet] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp | hp
    · rw [hp]; exact h.1
    · rw [hp]; exact h.2.1
    · rw [hp]; exact h.2.2.1
    · rw [hp]; exact h.2.2.2

/-- Weighted survival count for one edge: since its two endpoints are distinct,
the total Bernoulli weight of subsets containing both endpoints is
`a² (a+c)^(v-2)`. -/
theorem weighted_edgeEndpointSet_sum (hjoin : G.ArcsJoinEndpoints)
    (e : Fin G.numEdges) (a c : ℕ) :
    (∑ S ∈ G.V.powerset,
      (if edgeEndpointSet G e ⊆ S then a ^ S.card * c ^ (G.V.card - S.card) else 0))
      = a ^ 2 * (a + c) ^ (G.V.card - 2) := by
  have h := weighted_superset_indicator_sum G.V (edgeEndpointSet G e)
    (edgeEndpointSet_subset G e) a c
  rw [edgeEndpointSet_card G hjoin e] at h
  exact h

/-- Membership in `crossingPairs` includes the four-distinct-endpoints condition,
so the corresponding endpoint set has size four. -/
theorem crossingEndpointSet_card_of_mem_crossingPairs
    {ij : Fin G.numEdges × Fin G.numEdges} (hij : ij ∈ crossingPairs G) :
    (crossingEndpointSet G ij).card = 4 := by
  classical
  rw [crossingPairs, Finset.mem_filter] at hij
  exact crossingEndpointSet_card_of_fourDistinct G hij.2.2.2

/-- If the drawing has fewer than four vertices, there are no independent
crossing pairs: every member of `crossingPairs` carries four distinct endpoints
inside `V`. -/
theorem crossingPairs_card_eq_zero_of_card_lt_four (hv : G.V.card < 4) :
    (crossingPairs G).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  apply Finset.ext
  intro ij
  simp only [Finset.notMem_empty, iff_false]
  intro hij
  have hcard := crossingEndpointSet_card_of_mem_crossingPairs G hij
  have hle : (crossingEndpointSet G ij).card ≤ G.V.card :=
    Finset.card_le_card (crossingEndpointSet_subset G ij)
  omega

/-- Weighted survival count for one independent crossing pair: since the two
crossing edges have four distinct endpoints, the total Bernoulli weight of
subsets containing all four endpoints is `a⁴ (a+c)^(v-4)`. -/
theorem weighted_crossingEndpointSet_sum
    {ij : Fin G.numEdges × Fin G.numEdges} (hij : ij ∈ crossingPairs G)
    (a c : ℕ) :
    (∑ S ∈ G.V.powerset,
      (if crossingEndpointSet G ij ⊆ S then
        a ^ S.card * c ^ (G.V.card - S.card) else 0))
      = a ^ 4 * (a + c) ^ (G.V.card - 4) := by
  have h := weighted_superset_indicator_sum G.V (crossingEndpointSet G ij)
    (crossingEndpointSet_subset G ij) a c
  rw [crossingEndpointSet_card_of_mem_crossingPairs G hij] at h
  exact h

/-- Weighted vertex-count identity: the total Bernoulli weight of selected
vertices is `v · a · (a+c)^(v-1)`. This is the cleared finite-sum form of
`E[v_p] = p v`. -/
theorem weighted_vertex_card_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (a c : ℕ) :
    (∑ S ∈ U.powerset, a ^ S.card * c ^ (U.card - S.card) * S.card)
      = U.card * a * (a + c) ^ (U.card - 1) := by
  classical
  calc
    (∑ S ∈ U.powerset, a ^ S.card * c ^ (U.card - S.card) * S.card)
        = ∑ S ∈ U.powerset, ∑ x ∈ U,
            (if x ∈ S then a ^ S.card * c ^ (U.card - S.card) else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hSU : S ⊆ U := Finset.mem_powerset.mp hS
            have hcard : S.card = ∑ x ∈ U, (if x ∈ S then 1 else 0 : ℕ) := by
              calc
                S.card = (U.filter (fun x => x ∈ S)).card := by
                  have hfilter : U.filter (fun x => x ∈ S) = S := by
                    apply Finset.ext
                    intro x
                    rw [Finset.mem_filter]
                    constructor
                    · intro hx
                      exact hx.2
                    · intro hx
                      exact ⟨hSU hx, hx⟩
                  rw [hfilter]
                _ = ∑ x ∈ U, (if x ∈ S then 1 else 0 : ℕ) := by
                  rw [← Finset.sum_filter]
                  simp
            rw [hcard, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxs : x ∈ S <;> simp [hxs]
      _ = ∑ x ∈ U, ∑ S ∈ U.powerset,
            (if x ∈ S then a ^ S.card * c ^ (U.card - S.card) else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ _x ∈ U, a * (a + c) ^ (U.card - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hs : ({x} : Finset α) ⊆ U := by simpa using hx
          have h := weighted_superset_indicator_sum U ({x} : Finset α) hs a c
          simp at h
          exact h
      _ = U.card * a * (a + c) ^ (U.card - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ac_rfl

/-- Weighted edge-count identity: summing the induced edge count over all
vertex subsets with Bernoulli weights gives
`e · a² · (a+c)^(v-2)`. This is the cleared finite-sum form of
`E[e_p] = p² e`. -/
theorem weighted_edgesOn_sum (hjoin : G.ArcsJoinEndpoints) (a c : ℕ) :
    (∑ S ∈ G.V.powerset, a ^ S.card * c ^ (G.V.card - S.card) * edgesOn G S)
      = G.numEdges * (a ^ 2 * (a + c) ^ (G.V.card - 2)) := by
  classical
  calc
    (∑ S ∈ G.V.powerset, a ^ S.card * c ^ (G.V.card - S.card) * edgesOn G S)
        = ∑ S ∈ G.V.powerset, ∑ e ∈ (Finset.univ : Finset (Fin G.numEdges)),
            (if edgeEndpointSet G e ⊆ S then
              a ^ S.card * c ^ (G.V.card - S.card) else 0) := by
            apply Finset.sum_congr rfl
            intro S _hS
            unfold edgesOn
            have hcard :
                (Finset.univ.filter
                  (fun i : Fin G.numEdges =>
                    (G.endpoints i).1 ∈ S ∧ (G.endpoints i).2 ∈ S)).card =
                  ∑ e ∈ (Finset.univ : Finset (Fin G.numEdges)),
                    (if edgeEndpointSet G e ⊆ S then 1 else 0 : ℕ) := by
              rw [Finset.card_eq_sum_ones]
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · apply Finset.filter_congr
                intro e _he
                exact (edgeEndpointSet_subset_iff G e S).symm
              · intro e _he
                simp
            rw [hcard, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _he
            by_cases heS : edgeEndpointSet G e ⊆ S <;> simp [heS]
      _ = ∑ e ∈ (Finset.univ : Finset (Fin G.numEdges)), ∑ S ∈ G.V.powerset,
            (if edgeEndpointSet G e ⊆ S then
              a ^ S.card * c ^ (G.V.card - S.card) else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ _e ∈ (Finset.univ : Finset (Fin G.numEdges)),
            a ^ 2 * (a + c) ^ (G.V.card - 2) := by
          apply Finset.sum_congr rfl
          intro e _he
          exact weighted_edgeEndpointSet_sum G hjoin e a c
      _ = G.numEdges * (a ^ 2 * (a + c) ^ (G.V.card - 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp

/-- Weighted independent-crossing count identity: summing the induced independent
crossing-pair count over all vertex subsets with Bernoulli weights gives
`crossingPairs.card · a⁴ · (a+c)^(v-4)`. This is the cleared finite-sum form of
`E[cr_p] = p⁴ cr` for independent crossings. -/
theorem weighted_crossingsOn_sum (a c : ℕ) :
    (∑ S ∈ G.V.powerset, a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S)
      = (crossingPairs G).card * (a ^ 4 * (a + c) ^ (G.V.card - 4)) := by
  classical
  calc
    (∑ S ∈ G.V.powerset, a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S)
        = ∑ S ∈ G.V.powerset, ∑ ij ∈ crossingPairs G,
            (if crossingEndpointSet G ij ⊆ S then
              a ^ S.card * c ^ (G.V.card - S.card) else 0) := by
            apply Finset.sum_congr rfl
            intro S _hS
            unfold crossingsOn
            have hcard :
                ((crossingPairs G).filter
                  (fun ij : Fin G.numEdges × Fin G.numEdges =>
                    (G.endpoints ij.1).1 ∈ S ∧ (G.endpoints ij.1).2 ∈ S ∧
                    (G.endpoints ij.2).1 ∈ S ∧ (G.endpoints ij.2).2 ∈ S)).card =
                  ∑ ij ∈ crossingPairs G,
                    (if crossingEndpointSet G ij ⊆ S then 1 else 0 : ℕ) := by
              rw [Finset.card_eq_sum_ones]
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · apply Finset.filter_congr
                intro ij _hij
                exact (crossingEndpointSet_subset_iff G ij S).symm
              · intro ij _hij
                simp
            rw [hcard, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ij _hij
            by_cases hijS : crossingEndpointSet G ij ⊆ S <;> simp [hijS]
      _ = ∑ ij ∈ crossingPairs G, ∑ S ∈ G.V.powerset,
            (if crossingEndpointSet G ij ⊆ S then
              a ^ S.card * c ^ (G.V.card - S.card) else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ ij ∈ crossingPairs G,
            a ^ 4 * (a + c) ^ (G.V.card - 4) := by
          apply Finset.sum_congr rfl
          intro ij hij
          exact weighted_crossingEndpointSet_sum G hij a c
      _ = (crossingPairs G).card * (a ^ 4 * (a + c) ^ (G.V.card - 4)) := by
          rw [Finset.sum_const]
          simp

/-! ### From the local weak inequality to the averaged weak bound -/

/-- **Independent simple induced weak bound.**

For every induced subdrawing on a vertex subset `S`, the number of surviving
edges is at most the number of surviving independent crossing pairs plus
`3 |S|`. This is the exact local weak inequality in the ACNS/Leighton proof:
delete one edge for each crossing and apply the simple planar edge bound
`e ≤ 3v` (or `e ≤ 3v - 6` in the nondegenerate literature form).

Literature anchors: this is the deletion-to-planar step used in the proof of
the Crossing Lemma of Ajtai--Chvátal--Newborn--Szemerédi and Leighton (stated
as Theorem 0.2.1 in Tóth's survey), and in the branching-multigraph setting it
appears as Pach--Tóth, *A crossing lemma for multigraphs*, Lemma 2.1 and
Corollary 2.2 (`c(G) ≥ e - 3n + 6`).

This file proves the simple `M = 1` averaging theorem from this local inequality.
This deterministic proposition is a planar prerequisite, not the multigraph
`WeakAveragedBound`: Tóth's Theorem 7 proof additionally thins every parallel class.
The remaining work here is the geometric planarization/Euler layer that supplies this
proposition for actual drawings. -/
def IndependentSimpleInducedWeakBound : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      edgesOn G S ≤ crossingsOn G S + 3 * S.card

/-- **Independent simple crossing-free edge bound.**

Every crossing-free subset `E` of the surviving edge set over `S` has at most
`3 |S|` edges. This is the exact crossing-free planar edge estimate that supplies
the deletion step in the ACNS/Leighton proof. In the literature this is the
`e ≤ 3n - 6` planar bound with the harmless weaker form `e ≤ 3n`; in
Pach--Tóth, *A crossing lemma for multigraphs*, it is Lemma 2.1.

This proposition is deliberately stated for arbitrary crossing-free edge
subsets, so the theorem below can delete one edge from each surviving crossing
pair and apply it to the remainder. -/
def IndependentSimpleCrossingFreeEdgeBound : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), E ⊆ edgeSetOn G S →
        NoCrossingPairsInEdgeSet G E → E.card ≤ 3 * S.card

/-- **Independent simple crossing-free planarization.**

This is the remaining faithful geometric obligation corresponding to the
planar part of the ACNS/Leighton proof and to Pach--Tóth,
*A crossing lemma for multigraphs*, Lemma 2.1: after restricting to a vertex
set `S` and a crossing-free surviving edge set `E`, the drawn arcs determine a
genus-zero simple planarization of the abstract edge carrier.

The proposition is intentionally stronger and more geometric than the numerical
edge bound above. The theorem below proves that this planarization statement,
together with the already-proved Euler edge bound for genus-zero maps, implies
`IndependentSimpleCrossingFreeEdgeBound`. -/
def IndependentSimpleCrossingFreePlanarization : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          HasGenusZeroSimplePlanarization (abstractizeEdgeSet G S E hE)

/-- **Independent simple crossing-free planarization, nondegenerate form.**

This is the exact planarization obligation needed for the planar edge-bound
step: a genus-zero simple planarization is required only for vertex subsets
with `3 ≤ |S|`.  This matches the literature use of the simple planar graph
bound `e ≤ 3v - 6`; the cases `|S| ≤ 2` are handled separately by the
multiplicity-one injection into endpoint pairs.

This nondegenerate version avoids asking the genus-zero map witness for empty,
one-vertex, or two-vertex carriers, where the Euler witness formulation is not
the planar-edge-bound input actually used. -/
def IndependentSimpleCrossingFreePlanarizationLarge : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V → 3 ≤ S.card →
      ∀ E : Finset (Fin G.numEdges), ∀ hE : E ⊆ edgeSetOn G S,
        NoCrossingPairsInEdgeSet G E →
          HasGenusZeroSimplePlanarization (abstractizeEdgeSet G S E hE)

/-- **Componentwise crossing-free planarization.**

A crossing-free surviving edge set may be disconnected.  This is the
componentwise form of the planar part of the ACNS/Leighton deletion argument:
the edge set is partitioned into connected pieces `Ec i`, supported on disjoint
vertex sets `Vc i`; each nondegenerate piece carries the same genus-zero simple
planarization witness used by `planar_multigraph_edge_bound`.  The two cardinal
equalities/inequalities are the finite bookkeeping form of summing the connected
planar bounds over components. -/
def ComponentwiseCrossingFreePlanarization (G : DrawnMultigraph)
    (S : Finset (ℝ × ℝ)) (E : Finset (Fin G.numEdges)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), ∃ Vc : ι → Finset (ℝ × ℝ),
    ∃ Ec : ι → Finset (Fin G.numEdges),
      E.card = ∑ i, (Ec i).card ∧
      (∑ i, (Vc i).card) ≤ S.card ∧
      (∀ i, Vc i ⊆ S) ∧
      (∀ i, ∃ hEc : Ec i ⊆ edgeSetOn G (Vc i),
        3 ≤ (Vc i).card →
          HasGenusZeroSimplePlanarization (abstractizeEdgeSet G (Vc i) (Ec i) hEc))

/-- **Independent simple crossing-free componentwise planarization.**

This is the faithful disconnected version of the crossing-free planarization
obligation.  It matches the literature use of Pach--Tóth,
*A crossing lemma for multigraphs*, Lemma 2.1 / Corollary 2.2: after deleting
one edge from each crossing, apply the simple planar edge bound component by
component, then sum. -/
def IndependentSimpleCrossingFreeComponentwisePlanarization : Prop :=
  ∀ (G : DrawnMultigraph),
    (∀ p q, G.multiplicity p q ≤ 1) →
    G.ArcsJoinEndpoints →
    G.CrossingsAreIndependent →
    G.WellDrawn →
    ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      ∀ E : Finset (Fin G.numEdges), E ⊆ edgeSetOn G S →
        NoCrossingPairsInEdgeSet G E →
          ComponentwiseCrossingFreePlanarization G S E

/-- A componentwise genus-zero planarization gives the numerical
crossing-free edge bound `|E| ≤ 3 |S|`.

For large components this applies `e ≤ 3v - 6`; for components with at most two
vertices it uses the already-proved multiplicity-one injection into ordered
endpoint pairs.  This is the disconnected summation layer missing from the
connected residual-map endpoint. -/
theorem edge_card_le_three_mul_vertices_of_componentwise_planarization
    {G : DrawnMultigraph} {S : Finset (ℝ × ℝ)} {E : Finset (Fin G.numEdges)}
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hcomp : ComponentwiseCrossingFreePlanarization G S E) :
    E.card ≤ 3 * S.card := by
  classical
  rcases hcomp with ⟨ι, hι, Vc, Ec, hEcard, hVsum, hpieces⟩
  letI := hι
  have hpiece_bound : ∀ i : ι, (Ec i).card ≤ 3 * (Vc i).card := by
    intro i
    rcases hpieces.2 i with ⟨hEc, hpl⟩
    by_cases hv : 3 ≤ (Vc i).card
    · let A := abstractizeEdgeSet G (Vc i) (Ec i) hEc
      have hplanar : HasGenusZeroSimplePlanarization A := hpl hv
      have hmultA : PairMultiplicityBound A 1 :=
        abstractizeEdgeSet_pairMultiplicityBound G (Vc i) (Ec i) 1 hEc hmult
      have hvA : 3 ≤ Fintype.card A.Vertex := by
        rw [show Fintype.card A.Vertex = (Vc i).card from
          abstractizeEdgeSet_vertex_card G (Vc i) (Ec i) hEc]
        exact hv
      have hbound := planar_multigraph_edge_bound A 1 hplanar hmultA hvA
      have hedge : Fintype.card A.Edge = (Ec i).card :=
        abstractizeEdgeSet_edge_card G (Vc i) (Ec i) hEc
      have hvert : Fintype.card A.Vertex = (Vc i).card :=
        abstractizeEdgeSet_vertex_card G (Vc i) (Ec i) hEc
      rw [hedge, hvert] at hbound
      calc
        (Ec i).card ≤ 1 * (3 * (Vc i).card - 6) := hbound
        _ ≤ 3 * (Vc i).card := by omega
    · have hsmall : (Vc i).card ≤ 2 := by omega
      have hEcard : (Ec i).card ≤ (edgeSetOn G (Vc i)).card :=
        Finset.card_le_card hEc
      have hedgeSq := edgeSetOn_card_le_sq_of_multiplicity_one G (Vc i) hmult
      calc
        (Ec i).card ≤ (edgeSetOn G (Vc i)).card := hEcard
        _ ≤ (Vc i).card ^ 2 := hedgeSq
        _ ≤ 3 * (Vc i).card := by nlinarith
  have hsum :
      (∑ i : ι, (Ec i).card) ≤ ∑ i : ι, 3 * (Vc i).card :=
    Finset.sum_le_sum fun i _ => hpiece_bound i
  have hsum3 :
      (∑ i : ι, 3 * (Vc i).card) = 3 * ∑ i : ι, (Vc i).card := by
    simpa using (Finset.mul_sum (s := (Finset.univ : Finset ι))
      (f := fun i => (Vc i).card) (a := 3)).symm
  calc
    E.card = ∑ i : ι, (Ec i).card := hEcard
    _ ≤ ∑ i : ι, 3 * (Vc i).card := hsum
    _ = 3 * ∑ i : ι, (Vc i).card := hsum3
    _ ≤ 3 * S.card := Nat.mul_le_mul_left 3 hVsum

/-- Componentwise crossing-free planarization is sufficient for the existing
crossing-free numerical edge-bound hypothesis. -/
theorem independentSimpleCrossingFreeEdgeBound_of_componentwise_planarization
    (hpl : IndependentSimpleCrossingFreeComponentwisePlanarization) :
    IndependentSimpleCrossingFreeEdgeBound := by
  intro G hmult hjoin hcross hwd S hS E hE hfree
  exact edge_card_le_three_mul_vertices_of_componentwise_planarization hmult
    (hpl G hmult hjoin hcross hwd S hS E hE hfree)

/-- A genus-zero planarization for every crossing-free surviving edge set implies
the crossing-free numerical edge bound `|E| ≤ 3 |S|`.

For `|S| ≥ 3`, this is exactly the planar multigraph edge bound
`e ≤ 3v - 6` (with multiplicity bound `1`) applied to the abstract carrier. For
`|S| ≤ 2`, multiplicity `≤ 1` injects the surviving edge set into ordered
endpoint pairs in `S`, giving the weaker but sufficient `|E| ≤ |S|² ≤ 3|S|`. -/
theorem independentSimpleCrossingFreeEdgeBound_of_planarization
    (hpl : IndependentSimpleCrossingFreePlanarization) :
    IndependentSimpleCrossingFreeEdgeBound := by
  intro G hmult hjoin hcross hwd S hS E hE hfree
  classical
  by_cases hv : 3 ≤ S.card
  · let A := abstractizeEdgeSet G S E hE
    have hplanar : HasGenusZeroSimplePlanarization A :=
      hpl G hmult hjoin hcross hwd S hS E hE hfree
    have hmultA : PairMultiplicityBound A 1 :=
      abstractizeEdgeSet_pairMultiplicityBound G S E 1 hE hmult
    have hvA : 3 ≤ Fintype.card A.Vertex := by
      rw [show Fintype.card A.Vertex = S.card from
        abstractizeEdgeSet_vertex_card G S E hE]
      exact hv
    have hbound := planar_multigraph_edge_bound A 1 hplanar hmultA hvA
    have hedge : Fintype.card A.Edge = E.card :=
      abstractizeEdgeSet_edge_card G S E hE
    have hvert : Fintype.card A.Vertex = S.card :=
      abstractizeEdgeSet_vertex_card G S E hE
    rw [hedge, hvert] at hbound
    calc
      E.card ≤ 1 * (3 * S.card - 6) := hbound
      _ ≤ 3 * S.card := by omega
  · have hsmall : S.card ≤ 2 := by omega
    have hEcard : E.card ≤ (edgeSetOn G S).card := Finset.card_le_card hE
    have hedgeSq := edgeSetOn_card_le_sq_of_multiplicity_one G S hmult
    calc
      E.card ≤ (edgeSetOn G S).card := hEcard
      _ ≤ S.card ^ 2 := hedgeSq
      _ ≤ 3 * S.card := by nlinarith

/-- The nondegenerate planarization hypothesis is sufficient for the
crossing-free numerical edge bound.  This is the faithful form of the
ACNS/Leighton and Pach--Tóth planar step: use `e ≤ 3v - 6` only when
`3 ≤ v`, and use the multiplicity-one endpoint-pair injection for `v ≤ 2`. -/
theorem independentSimpleCrossingFreeEdgeBound_of_planarizationLarge
    (hpl : IndependentSimpleCrossingFreePlanarizationLarge) :
    IndependentSimpleCrossingFreeEdgeBound := by
  intro G hmult hjoin hcross hwd S hS E hE hfree
  classical
  by_cases hv : 3 ≤ S.card
  · let A := abstractizeEdgeSet G S E hE
    have hplanar : HasGenusZeroSimplePlanarization A :=
      hpl G hmult hjoin hcross hwd S hS hv E hE hfree
    have hmultA : PairMultiplicityBound A 1 :=
      abstractizeEdgeSet_pairMultiplicityBound G S E 1 hE hmult
    have hvA : 3 ≤ Fintype.card A.Vertex := by
      rw [show Fintype.card A.Vertex = S.card from
        abstractizeEdgeSet_vertex_card G S E hE]
      exact hv
    have hbound := planar_multigraph_edge_bound A 1 hplanar hmultA hvA
    have hedge : Fintype.card A.Edge = E.card :=
      abstractizeEdgeSet_edge_card G S E hE
    have hvert : Fintype.card A.Vertex = S.card :=
      abstractizeEdgeSet_vertex_card G S E hE
    rw [hedge, hvert] at hbound
    calc
      E.card ≤ 1 * (3 * S.card - 6) := hbound
      _ ≤ 3 * S.card := by omega
  · have hsmall : S.card ≤ 2 := by omega
    have hEcard : E.card ≤ (edgeSetOn G S).card := Finset.card_le_card hE
    have hedgeSq := edgeSetOn_card_le_sq_of_multiplicity_one G S hmult
    calc
      E.card ≤ (edgeSetOn G S).card := hEcard
      _ ≤ S.card ^ 2 := hedgeSq
      _ ≤ 3 * S.card := by nlinarith

/-- Delete one edge from each surviving independent crossing pair, then apply
the crossing-free planar edge bound to the remaining edge set. This is the
finite combinatorial content of Pach--Tóth Corollary 2.2:
`c(G) ≥ e - 3n + 6`, weakened to `e ≤ c(G) + 3n`. -/
theorem independentSimpleInducedWeakBound_of_crossingFreeEdgeBound
    (hplanar : IndependentSimpleCrossingFreeEdgeBound) :
    IndependentSimpleInducedWeakBound := by
  intro G hmult hjoin hcross hwd S hS
  have hdelete := edgesOn_le_remainingEdgeSet_card_add_crossingsOn G S
  have hrem := hplanar G hmult hjoin hcross hwd S hS
    (remainingEdgeSet G S)
    (remainingEdgeSet_subset_edgeSetOn G S)
    (remainingEdgeSet_noCrossingPairs G S)
  calc
    edgesOn G S ≤ (remainingEdgeSet G S).card + crossingsOn G S := hdelete
    _ ≤ 3 * S.card + crossingsOn G S := Nat.add_le_add_right hrem _
    _ = crossingsOn G S + 3 * S.card := by omega

/-- Nondegenerate crossing-free planarization supplies the local induced weak
bound after the deterministic one-edge-per-crossing deletion. -/
theorem independentSimpleInducedWeakBound_of_crossingFreePlanarizationLarge
    (hpl : IndependentSimpleCrossingFreePlanarizationLarge) :
    IndependentSimpleInducedWeakBound :=
  independentSimpleInducedWeakBound_of_crossingFreeEdgeBound
    (independentSimpleCrossingFreeEdgeBound_of_planarizationLarge hpl)

/-- The ACNS/Leighton Bernoulli vertex-sampling step for one fixed drawing.

The proof is the same finite-sum argument as
`independentSimpleWeakAveragedBound_of_inducedWeakBound`, but the hypothesis is
local to `G`: every induced vertex subset of this one drawing satisfies
`edgesOn S ≤ crossingsOn S + 3 |S|`.  This is the form needed for the
Szemerédi--Trotter incidence graph without first proving a global crossing
lemma for arbitrary drawings. -/
theorem localSimpleWeakAveragedBound_of_inducedWeakBound
    {G : DrawnMultigraph}
    (hjoin : G.ArcsJoinEndpoints) (hwd : G.WellDrawn)
    (hweakSub : ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      edgesOn G S ≤ crossingsOn G S + 3 * S.card) :
    LocalSimpleWeakAveragedBound G := by
  intro a b ha hab
  classical
  by_cases hv4 : 4 ≤ G.V.card
  · set c := b - a with hc
    have hbc : a + c = b := by omega
    have hsum :
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) * edgesOn G S) ≤
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) := by
      apply Finset.sum_le_sum
      intro S hS
      exact Nat.mul_le_mul_left _ (hweakSub S (Finset.mem_powerset.mp hS))
    have hsplit :
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) =
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
          3 * (∑ S ∈ G.V.powerset,
            a ^ S.card * c ^ (G.V.card - S.card) * S.card) := by
      calc
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) =
            ∑ S ∈ G.V.powerset,
              (a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S +
                3 * (a ^ S.card * c ^ (G.V.card - S.card) * S.card)) := by
            apply Finset.sum_congr rfl
            intro S _hS
            ring
        _ = (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
            (∑ S ∈ G.V.powerset,
              3 * (a ^ S.card * c ^ (G.V.card - S.card) * S.card)) := by
            rw [Finset.sum_add_distrib]
        _ = (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
            3 * (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * S.card) := by
            rw [Finset.mul_sum]
    have hsum' :
        G.numEdges * (a ^ 2 * b ^ (G.V.card - 2)) ≤
          (crossingPairs G).card * (a ^ 4 * b ^ (G.V.card - 4)) +
            3 * (G.V.card * a * b ^ (G.V.card - 1)) := by
      have h := hsum
      rw [hsplit, weighted_edgesOn_sum G hjoin a c, weighted_crossingsOn_sum G a c,
        weighted_vertex_card_sum G.V a c] at h
      rw [hbc] at h
      exact h
    have hleft_rw :
        G.numEdges * (a ^ 2 * b ^ (G.V.card - 2)) =
          b ^ (G.V.card - 4) * (a ^ 2 * b ^ 2 * G.numEdges) := by
      have hpow : G.V.card - 2 = (G.V.card - 4) + 2 := by omega
      rw [hpow, pow_add]
      ring
    have hright_rw :
        (crossingPairs G).card * (a ^ 4 * b ^ (G.V.card - 4)) +
            3 * (G.V.card * a * b ^ (G.V.card - 1)) =
          b ^ (G.V.card - 4) *
            (a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card) := by
      have hpow : G.V.card - 1 = (G.V.card - 4) + 3 := by omega
      rw [hpow, pow_add]
      ring
    have hfact :
        b ^ (G.V.card - 4) * (a ^ 2 * b ^ 2 * G.numEdges) ≤
          b ^ (G.V.card - 4) *
            (a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card) := by
      rw [← hleft_rw, ← hright_rw]
      exact hsum'
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hpowpos : 0 < b ^ (G.V.card - 4) := Nat.pow_pos hbpos
    have hcancel :
        a ^ 2 * b ^ 2 * G.numEdges ≤
          a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card :=
      Nat.le_of_mul_le_mul_left hfact hpowpos
    have hcp : (crossingPairs G).card ≤ G.crossings :=
      crossingPairs_card_le_crossings G hwd
    exact hcancel.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (a ^ 4) hcp) _)
  · have hvlt : G.V.card < 4 := Nat.lt_of_not_ge hv4
    have hweakV := hweakSub G.V (by intro x hx; exact hx)
    rw [edgesOn_univ G, crossingsOn_univ G,
      crossingPairs_card_eq_zero_of_card_lt_four G hvlt] at hweakV
    have he3v : G.numEdges ≤ 3 * G.V.card := by
      simpa using hweakV
    have hcoeff : a ^ 2 * b ^ 2 ≤ a * b ^ 3 := by
      calc
        a ^ 2 * b ^ 2 = (a * b ^ 2) * a := by ring
        _ ≤ (a * b ^ 2) * b := Nat.mul_le_mul_left _ hab
        _ = a * b ^ 3 := by ring
    have hscale : a ^ 2 * b ^ 2 * G.numEdges ≤ a * b ^ 3 * G.numEdges :=
      Nat.mul_le_mul_right G.numEdges hcoeff
    calc
      a ^ 2 * b ^ 2 * G.numEdges ≤ a * b ^ 3 * G.numEdges := hscale
      _ ≤ a * b ^ 3 * (3 * G.V.card) := Nat.mul_le_mul_left _ he3v
      _ = 3 * a * b ^ 3 * G.V.card := by ring
      _ ≤ a ^ 4 * G.crossings + 3 * a * b ^ 3 * G.V.card := by
          exact Nat.le_add_left _ _

/-- The ACNS/Leighton Bernoulli vertex-sampling step, in cleared finite-sum form:
the local induced-subdrawing weak inequality implies
`IndependentSimpleWeakAveragedBound`.

For `|V| ≥ 4`, the proof sums
`edgesOn S ≤ crossingsOn S + 3 |S|` with weight
`a^|S| (b-a)^(|V|-|S|)`, uses the three identities
`E[e_p] = p²e`, `E[cr_p] = p⁴cr`, `E[v_p] = pv`, and cancels
`b^(|V|-4)`. For `|V| < 4`, no independent crossing pair can exist, so the
local weak bound at `S = V` gives `e ≤ 3v`, which directly implies the cleared
inequality for every `0 < a ≤ b`. -/
theorem independentSimpleWeakAveragedBound_of_inducedWeakBound
    (hweak : IndependentSimpleInducedWeakBound) :
    IndependentSimpleWeakAveragedBound := by
  intro G hmult hjoin hcross hwd a b ha hab
  classical
  have hweakSub := hweak G hmult hjoin hcross hwd
  by_cases hv4 : 4 ≤ G.V.card
  · set c := b - a with hc
    have hbc : a + c = b := by omega
    have hsum :
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) * edgesOn G S) ≤
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) := by
      apply Finset.sum_le_sum
      intro S hS
      exact Nat.mul_le_mul_left _ (hweakSub S (Finset.mem_powerset.mp hS))
    have hsplit :
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) =
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
          3 * (∑ S ∈ G.V.powerset,
            a ^ S.card * c ^ (G.V.card - S.card) * S.card) := by
      calc
        (∑ S ∈ G.V.powerset,
          a ^ S.card * c ^ (G.V.card - S.card) *
            (crossingsOn G S + 3 * S.card)) =
            ∑ S ∈ G.V.powerset,
              (a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S +
                3 * (a ^ S.card * c ^ (G.V.card - S.card) * S.card)) := by
            apply Finset.sum_congr rfl
            intro S _hS
            ring
        _ = (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
            (∑ S ∈ G.V.powerset,
              3 * (a ^ S.card * c ^ (G.V.card - S.card) * S.card)) := by
            rw [Finset.sum_add_distrib]
        _ = (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * crossingsOn G S) +
            3 * (∑ S ∈ G.V.powerset,
              a ^ S.card * c ^ (G.V.card - S.card) * S.card) := by
            rw [Finset.mul_sum]
    have hsum' :
        G.numEdges * (a ^ 2 * b ^ (G.V.card - 2)) ≤
          (crossingPairs G).card * (a ^ 4 * b ^ (G.V.card - 4)) +
            3 * (G.V.card * a * b ^ (G.V.card - 1)) := by
      have h := hsum
      rw [hsplit, weighted_edgesOn_sum G hjoin a c, weighted_crossingsOn_sum G a c,
        weighted_vertex_card_sum G.V a c] at h
      rw [hbc] at h
      exact h
    have hleft_rw :
        G.numEdges * (a ^ 2 * b ^ (G.V.card - 2)) =
          b ^ (G.V.card - 4) * (a ^ 2 * b ^ 2 * G.numEdges) := by
      have hpow : G.V.card - 2 = (G.V.card - 4) + 2 := by omega
      rw [hpow, pow_add]
      ring
    have hright_rw :
        (crossingPairs G).card * (a ^ 4 * b ^ (G.V.card - 4)) +
            3 * (G.V.card * a * b ^ (G.V.card - 1)) =
          b ^ (G.V.card - 4) *
            (a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card) := by
      have hpow : G.V.card - 1 = (G.V.card - 4) + 3 := by omega
      rw [hpow, pow_add]
      ring
    have hfact :
        b ^ (G.V.card - 4) * (a ^ 2 * b ^ 2 * G.numEdges) ≤
          b ^ (G.V.card - 4) *
            (a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card) := by
      rw [← hleft_rw, ← hright_rw]
      exact hsum'
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hpowpos : 0 < b ^ (G.V.card - 4) := Nat.pow_pos hbpos
    have hcancel :
        a ^ 2 * b ^ 2 * G.numEdges ≤
          a ^ 4 * (crossingPairs G).card + 3 * a * b ^ 3 * G.V.card :=
      Nat.le_of_mul_le_mul_left hfact hpowpos
    have hcp : (crossingPairs G).card ≤ G.crossings :=
      crossingPairs_card_le_crossings G hwd
    exact hcancel.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (a ^ 4) hcp) _)
  · have hvlt : G.V.card < 4 := Nat.lt_of_not_ge hv4
    have hweakV := hweakSub G.V (by intro x hx; exact hx)
    rw [edgesOn_univ G, crossingsOn_univ G,
      crossingPairs_card_eq_zero_of_card_lt_four G hvlt] at hweakV
    have he3v : G.numEdges ≤ 3 * G.V.card := by
      simpa using hweakV
    have hcoeff : a ^ 2 * b ^ 2 ≤ a * b ^ 3 := by
      calc
        a ^ 2 * b ^ 2 = (a * b ^ 2) * a := by ring
        _ ≤ (a * b ^ 2) * b := Nat.mul_le_mul_left _ hab
        _ = a * b ^ 3 := by ring
    have hscale : a ^ 2 * b ^ 2 * G.numEdges ≤ a * b ^ 3 * G.numEdges :=
      Nat.mul_le_mul_right G.numEdges hcoeff
    calc
      a ^ 2 * b ^ 2 * G.numEdges ≤ a * b ^ 3 * G.numEdges := hscale
      _ ≤ a * b ^ 3 * (3 * G.V.card) := Nat.mul_le_mul_left _ he3v
      _ = 3 * a * b ^ 3 * G.V.card := by ring
      _ ≤ a ^ 4 * G.crossings + 3 * a * b ^ 3 * G.V.card := by
          exact Nat.le_add_left _ _

/-- Nondegenerate crossing-free planarization is enough to run the full
ACNS/Leighton averaged weak-bound proof. -/
theorem independentSimpleWeakAveragedBound_of_crossingFreePlanarizationLarge
    (hpl : IndependentSimpleCrossingFreePlanarizationLarge) :
    IndependentSimpleWeakAveragedBound :=
  independentSimpleWeakAveragedBound_of_inducedWeakBound
    (independentSimpleInducedWeakBound_of_crossingFreePlanarizationLarge hpl)

/-- **OBSTRUCTION — `vertexSubsetAveraging_bound` [BLOCKED, `sorry`; NOT used by the main
theorem].**

The integer double-count master inequality. Summing an assumed per-subset weak bound
`edgesOn G S ≤ 3·M·S.card + crossingsOn G S` over all `S ∈ G.V.powersetCard s` and
applying the three binomial double counts

  `Σ_{|S|=s} edgesOn G S      = G.numEdges · C(v−2, s−2)`,
  `Σ_{|S|=s} crossingsOn G S  = (crossingPairs G).card · C(v−4, s−4)`,
  `Σ_{|S|=s} S.card           = s · C(v, s)`,

yields `e·C(v−2,s−2) ≤ 3·M·s·C(v,s) + cr·C(v−4,s−4)`.

OBSTRUCTION, two parts (both PROVEN off-line; see module docstring):
* **(a) the double counts** need `Finset.powersetCard` fiberwise card identities
  (`Σ_{|S|=s} [x ⊆ S] = C(v−|x|, s−|x|)` for a fixed `x ⊆ V` of size 2 or 4). These are
  standard but unbuilt here; `crossingsOn` further needs the four-endpoints set to have
  card 4 so its surviving count is governed by `C(v−4,s−4)` — encoded in `crossingPairs`.
* **(b) even granting (a), this master inequality CANNOT close the exact `1/64`
  constant by integer averaging**: when the continuous optimum `s* = 4Mv²/e < 4` (large
  `e`), no admissible `s ≥ 4` exists and the bound degrades by up to a factor ≈ 2. The
  real-valued parameter is essential — which is why `crossingLemma_of_weakBound` uses the
  cleared real-`p` `WeakAveragedBound` instead.

Honest classification: part (a) CONJECTURED-feasible / mechanical-laborious (the
`powersetCard` double counts; ~1–2 sessions); part (b) PROVEN-obstructed for the *exact*
constant — the integer route reaches only a *looser* constant, so this lemma is a dead
end for the target and is retained only as documentation. Feasibility of an exact-constant
proof via this route: NOT feasible (proven). -/
theorem vertexSubsetAveraging_bound (M s : ℕ) (hs4 : 4 ≤ s) (hsv : s ≤ G.V.card)
    (hweakSub : ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      edgesOn G S ≤ 3 * M * S.card + crossingsOn G S) :
    G.numEdges * Nat.choose (G.V.card - 2) (s - 2) ≤
      3 * M * s * Nat.choose G.V.card s
        + (crossingPairs G).card * Nat.choose (G.V.card - 4) (s - 4) := by
  -- OBSTRUCTION (a): powersetCard double counts; see docstring. NOT used downstream.
  sorry

end IntegerRoute

end CrossingLemma
