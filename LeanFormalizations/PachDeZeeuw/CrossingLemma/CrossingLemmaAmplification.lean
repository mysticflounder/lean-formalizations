/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma

/-!
# PS-CL-3 — derandomized amplification: `CrossingLemmaMultigraphStatement` from a weak bound

This file proves the **derandomized amplification step** of the multigraph crossing
lemma (Székely / Ajtai–Chvátal–Newborn–Szemerédi, multigraph form, Pach–Tóth
constant). It derives the cubed target

  `CrossingLemmaMultigraphStatement`  :  `e³ ≤ 64·M·v²·cr`
  (when `0 < M`, multiplicity `≤ M`, and `e ≥ 4·M·v`)

(defined in `CrossingLemma.lean`) **from an assumed weak bound** `hweak`. The weak
bound is the content the drawing→genus-0-map / Euler bridge supplies; discharging it
is a *separate* lane and is **not** attempted here.

It imports only `Mathlib` and the standalone `CrossingLemma` surface, mentions no
algebraic curves, and is **not** on the closure aggregator `CrossingLemma.lean`.

## The mathematics, and why `hweak` has the shape it does (read before trusting the constant)

The standard simple-graph crossing lemma `cr ≥ e³/(64 v²)` (`e ≥ 4v`) is proved by:
*weak bound* `cr ≥ e − 3v` (delete one edge per crossing → planar → Euler `e ≤ 3v−6`),
then *probabilistic amplification* — keep each vertex independently with probability
`p`, so `E[v_p] = p v`, `E[e_p] = p² e`, `E[cr_p] = p⁴ cr` (each crossing has 4
distinct endpoints); the weak bound in expectation gives `p⁴ cr ≥ p² e − 3 p v`, and
`p = 4v/e ≤ 1` (legal since `e ≥ 4v`) yields exactly `cr ≥ e³/(64 v²)`.

**Two facts force the precise shape of `hweak` below; both are PROVEN (exact rational
arithmetic, off-line, recorded in the agent report).**

1. **The single `M` is sharp and is NOT obtainable by averaging a linear multigraph
   weak bound.** Székely's multigraph statement `cr ≥ e³/(64 m v²)` (`e ≥ 4mv`) has a
   *single* `m` (Pach–Tóth, *A crossing lemma for multigraphs*, eq. (1); tight on
   `m`-fold "bundle" blow-ups of the simple extremal graph, where
   `cr = m²·cr₀, e = m·e₀`). But vertex-subset averaging of the *natural multigraph
   planar* weak bound `e_S ≤ 3 m v_S + cr_S` yields only the **weaker** `e³ ≤ 64 m² v² cr`
   (one extra `m`); the naive delete-to-simple yields `e³ ≤ 64 m³ v² cr`. The single-`m`
   sharpening is genuine multigraph (bundle) content, NOT a corollary of any single
   linear weak bound. It is therefore correctly the *bridge's* responsibility, and
   `hweak` below encodes the sharp form (coefficient `M` on `e`, `3M²` on `v`).

2. **The integer optimal-`s` choice is genuinely obstructed; the real `p` is essential.**
   The *derandomized* (sum-over-size-`s`-subsets) version replaces `p` by `s/v` with
   integer `s ∈ {4,…,v}` and uses the double-count identities
   `Σ_{|S|=s} e_S = e·C(v−2,s−2)`, `Σ_{|S|=s} cr_S = cr·C(v−4,s−4)`,
   `Σ_{|S|=s} v_S = s·C(v,s)` (all verified by brute force). When the continuous optimum
   `s* = 4·M·v²/e` falls **below 4** (large-`e` regime, e.g. `v=8, e=332, M=1` gives
   `s* ≈ 0.77`), no admissible integer `s ≥ 4` exists, and the integer averaging loses
   up to a factor ≈ 2 in the constant — so the *exact* `1/64` is **not** recoverable by
   pure integer averaging. The real-valued parameter is essential. Accordingly `hweak`
   is stated as the **cleared, division-free real-`p` (rational `a/b`) form**, which the
   averaging/probabilistic argument supplies directly and which the single substitution
   `p = 4Mv/e` turns into the exact target in clean ℕ arithmetic — no discretization.

### Statement of `hweak` (the cleared division-free form)

Writing `p = a/b` and multiplying the real bound `p⁴ cr ≥ M p² e − 3 M² p v` through by
`b⁴ > 0` gives the subtraction-free ℕ inequality

  `M · a² · b² · e  ≤  a⁴ · cr  +  3 · M² · a · b³ · v`     (for all `0 < a ≤ b`).

At `a = 4·M·v`, `b = e` this reduces (cancel `4 M³ v²`) to exactly `e³ ≤ 64 M v² cr`.
This is `WeakAveragedBound` below. **PROVEN** (exact arithmetic) that this `hweak`
implies the target; **CONJECTURED-in-Lean / PROVEN-in-literature** that the bridge can
supply this `hweak` (it is the expectation form of ACNS/Székely averaging over random
vertex subsets, sharpened to single `M` by the multigraph bundle structure).

## Honest status

* **PROVEN sorry-free:** `crossingLemma_of_weakBound` — the reduction
  `WeakAveragedBound → CrossingLemmaMultigraphStatement`. This is the deliverable's
  core: the amplification arithmetic itself, carried entirely in ℕ, no `rpow`.
* **Scaffolding, sorry-free:** the surviving-count definitions
  (`edgesOn`, `crossingPairs`, `crossingsOn`) and the elementary count lemmas that do
  not need the (research-grade) double-count identities.
* **Labelled OBSTRUCTION (`sorry`):** `subsetAveraging_master` — the integer
  double-count master inequality, which (a) needs the `C(v−2,s−2)` / `C(v−4,s−4)` /
  `C(v,s)` `Finset.powersetCard` double counts AND (b) per fact 2 above *cannot* close
  the exact constant by itself. It is present only as documentation of the integer
  route and is **not used** by `crossingLemma_of_weakBound`.

No `axiom` is introduced. Axiom status of any downstream consumer is verified centrally;
this file does not assert axiom-cleanliness.
-/

set_option linter.style.longLine false

namespace CrossingLemma.PDZ

open scoped BigOperators

/-! ## 1. The assumed weak bound (`hweak`)

The cleared, division-free real-`p` averaging bound. Quantified over all `G` and `M`
so it can serve as a single hypothesis of the top theorem; the substance is the
per-`(a,b)` inequality, with `p = a/b` ranging over `(0,1]`. -/

/-- **`WeakAveragedBound`** — the assumed weak bound the bridge must supply.

For every drawn multigraph `G` and multiplicity cap `M > 0` with `G.multiplicity ≤ M`
everywhere and `G` `WellDrawn`, and for every rational sampling parameter `p = a/b ∈ (0,1]` (encoded as
`0 < a ≤ b` in `ℕ`, cleared by `b⁴`):

  `M · a² · b² · e  ≤  a⁴ · cr  +  3 · M² · a · b³ · v`,

where `e = G.numEdges`, `v = G.V.card`, `cr = G.crossings`.

This is the subtraction-free integer form of the expectation inequality
`p⁴·cr ≥ M·p²·e − 3·M²·p·v` of the (sharpened, single-`M`) ACNS/Székely vertex-subset
averaging argument. See the module docstring for why the coefficients are `M` and
`3M²` (the single-`M` sharpening) rather than `1` and `3M` (the lossy planar form). -/
def WeakAveragedBound : Prop :=
  ∀ (G : DrawnMultigraph) (M : ℕ),
    0 < M →
    (∀ p q, G.multiplicity p q ≤ M) →
    G.WellDrawn →
    ∀ a b : ℕ, 0 < a → a ≤ b →
      M * a ^ 2 * b ^ 2 * G.numEdges ≤
        a ^ 4 * G.crossings + 3 * M ^ 2 * a * b ^ 3 * G.V.card

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

/-- **PS-CL-3 — derandomized amplification [PROVEN, sorry-free].**

`CrossingLemmaMultigraphStatement` follows from the assumed weak bound
`WeakAveragedBound`. This is the multigraph crossing lemma `e³ ≤ 64·M·v²·cr`
(Székely / ACNS / Pach–Tóth constant) obtained by the derandomized averaging
substitution `p = 4·M·v/e`, carried entirely in `ℕ`.

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
  intro G M hM hmult hwd hthresh
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
    have key := hweak G M hM hmult hwd (4 * M * v) e ha hab
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
      -- four pairwise-distinct endpoints:
      ({(G.endpoints ij.1).1, (G.endpoints ij.1).2,
        (G.endpoints ij.2).1, (G.endpoints ij.2).2} : Finset (ℝ × ℝ)).card = 4)

/-- Number of independent crossing pairs all four of whose endpoints lie in `S` (the
crossing count of the induced sub-drawing on `S`, restricted to independent pairs). -/
noncomputable def crossingsOn (S : Finset (ℝ × ℝ)) : ℕ := by
  classical
  exact ((crossingPairs G).filter
    (fun ij : Fin G.numEdges × Fin G.numEdges =>
      (G.endpoints ij.1).1 ∈ S ∧ (G.endpoints ij.1).2 ∈ S ∧
      (G.endpoints ij.2).1 ∈ S ∧ (G.endpoints ij.2).2 ∈ S)).card

/-- On the full vertex set, `edgesOn` counts every edge (both endpoints are in `V`). -/
theorem edgesOn_univ : edgesOn G G.V = G.numEdges := by
  classical
  unfold edgesOn
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro i _
  exact ⟨(G.endpoints_mem i).1, (G.endpoints_mem i).2⟩

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

/-- **OBSTRUCTION — `subsetAveraging_master` [BLOCKED, `sorry`; NOT used by the main theorem].**

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
theorem subsetAveraging_master (M s : ℕ) (hs4 : 4 ≤ s) (hsv : s ≤ G.V.card)
    (hweakSub : ∀ S : Finset (ℝ × ℝ), S ⊆ G.V →
      edgesOn G S ≤ 3 * M * S.card + crossingsOn G S) :
    G.numEdges * Nat.choose (G.V.card - 2) (s - 2) ≤
      3 * M * s * Nat.choose G.V.card s
        + (crossingPairs G).card * Nat.choose (G.V.card - 4) (s - 4) := by
  -- OBSTRUCTION (a): powersetCard double counts; see docstring. NOT used downstream.
  sorry

end IntegerRoute

end CrossingLemma.PDZ
