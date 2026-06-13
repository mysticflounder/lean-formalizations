# Closing the cotree `sorry` in `SzemerediTrotter.lean`

Target: the single remaining `sorry` at
`LeanFormalizations/PachDeZeeuw/PachSharir/SzemerediTrotter.lean` in
`straightLineCanonicalComponentResidualMapPlanarityOfARR`, in the
`hstep` later-cotree branch (`lvertex.length - 1 < m`).

This is a Lean **formalization** task. The mathematics (planar tree/cotree
decomposition: complementary primal/dual spanning trees, dual-map incidence,
reverse leaf-peeling face splitting) is settled and already scaffolded in the
repo. There is no missing *theorem* in the literature to find — only formal
packaging to assemble. Every building-block lemma named below exists.

---

## 0. Status (2026-06-12)

**DONE & building (committed):** the OnEdgeSet cotree-block plumbing. This
cleared the first hard blocker, described next.

**The blocker that was cleared — selector mismatch.** The tree/cotree position
permutation `π` (from `exists_treeCotreePositionPermutation_of_graphConnected`)
places the cotree block using the **edge-set-restricted** selector
`faceEdgeOfLeafOrderOnEdgeSetReverse {non-tree edges} …`, with the cotree tree
`Tface ≤ faceGraphOnEdgeSet {non-tree edges}`. But every block lemma originally
consumed the **unrestricted** `faceEdgeOfLeafOrderReverse` (with
`T ≤ faceGraph`).

There is **no bridge** `faceEdgeOfLeafOrderOnEdgeSetReverse = faceEdgeOfLeafOrderReverse`
and one cannot exist: `Edge.ends` is many-to-one on dual edges (a 4-cycle's two
faces share all four edges), and the two selectors are independent
`Classical.choose` calls that agree only on the *face pair*, not on edge
identity. So the unrestricted block lemma could **never** be invoked with the
real `π`. (This was a latent mis-statement, now fixed.)

**Fix applied (the workhorse is selector-agnostic).** The deepest workhorse
`exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq`
consumes a *bare dart* `d`, not a selector. So the selector only enters at two
mechanical spots. We:

1. Added `DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block`
   in `ResidualMapProperties.lean` (analog of the unrestricted `_next_` lemma,
   reducing to the already-present OnEdgeSet `_last_` lemma).
2. Retargeted the block lemma
   `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_current_splitPool_eq`
   (was `…faceEdgeOfLeafOrderReverse…`) to the OnEdgeSet selector
   (`Sₑ : Set …Edge`, `T ≤ faceGraphOnEdgeSet Sₑ`, selector in `hπcotree`+`hsplit`).
   The ~660-line internals are untouched.
3. Retargeted the stComponentDrawing wrapper
   `stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_choose_splitPool_eq`
   the same way (edge set named `Sₑ` to avoid the existing `S : Finset (ℝ×ℝ)`).

The whole library builds (only the target `sorry` warning + pre-existing
`simpa` lints remain). This wrapper's `hπcotree` now matches `hπrest` exactly.

---

## 1. Index bookkeeping (unchanged, verified)

```
a := lvertex.length - 1          -- tree block size
b := lface.length  - 1           -- cotree block size  (a + b = numEdges, Euler)
t := m - a                       -- cotree offset; later branch ⇒ 1 ≤ t ≤ b-1

-- to PRODUCE the step at global offset m (SameFaceData at offset m):
i : Fin b := ⟨t - 1, _⟩          -- predecessor edge   (NOT t)
j : Fin b := ⟨t,     _⟩          -- current edge
m = a + i.1 + 1 = a + j.1
hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1     -- holds: both = b - t + 1
```

The OnEdgeSet wrapper produces `ResidualMapPrefixStepSameFaceData … (a+i.1+1)`
= SameFaceData at offset `m`, from predecessor same-face data at offset
`a + i.1 = m - 1`.

---

## 2. The seed (offset `a`, `t = 0`)

Use, as the induction base, the **SameFaceData** tree-prefix lemma (NOT the
Insertion variant the `m = a` branch already uses):

```
stComponentDrawing_prefixPermute_exists_residualMapPrefixStepSameFaceData_of_treePrefix_next
```

It yields `Nonempty (ResidualMapPrefixStepSameFaceData (G.permuteEdges π) (lvertex.length-1) …)`
— the predecessor data the first successor (`t = 1`, `i.1 = 0`) consumes.

---

## 3. The successor (offset `m`, `1 ≤ t ≤ b-1`)

Feed the predecessor SameFaceData fields (`c₁ c₂ hc hsame hvertex`, supplied as
`s₁ s₂ hs hsame hvertex`) into the OnEdgeSet wrapper from §0.3, with:

- `Sₑ := {e | residualMapEdgeEquiv G hARRG e ∉ Set.range (G.treeEdgeOfLeafOrder …)}`
  (the exact set in `hTface_sub` / `hπrest`);
- `T := Tface`, `hTsub := hTface_sub`, `l := lface`, `parent := parentFace`,
  `hparent := hparentFace`, `hblock := hblock`, `hπcotree := hπrest`;
- `i, j, hprefix` per §1; `hm/hm'/hm''` from `hm, hm'` (offsets `m-1, m, m+1`).

Then `.toInsertion` on the resulting SameFaceData to discharge the branch.

---

## 4. What the successor still needs — THE REMAINING HARD PART {{NEEDS_PROOF}}

The wrapper takes `hcoverage` and `hchoose` as **hypotheses**. They are not
free; §4 of the previous plan ("the rest is already in the library") was wrong
about `hchoose`.

1. **`hcoverage`** (endpoint coverage of prefix `m`) — AVAILABLE. Producer:
   `incidentCoverage_permuted_treePrefix_of_leafOrder_of_le` (and siblings) in
   `ResidualMapProperties.lean`.

2. **`hchoose`** (the split-pool side selection for the current cotree edge) —
   **NOT yet assembled.** The building blocks exist:
   - `residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_face_pair_eq_of_forall_adj_ne_current_parent`
     produces the split-pool equality **from** a label-constancy hypothesis
     `hadj`;
   - the reverse-prefix transport
     `residualMap_prefixStep_faceEdgeOfLeafOrderReverse_next_unpeeled_prefix_face_label_eq_of_forall_adj_ne_current_parent`
     propagates constancy along the unpeeled prefix.
   - But the **base** `hadj` — "the split-pool side label is constant across
     the next unpeeled dual prefix, except across the current parent edge" — is
     itself the **leaf-peeling invariant** that must be established for the
     actual split-pool `label` and **carried through the induction**. This is
     the genuine unfinished mathematics (the planar same-face / co-faciality
     content of reverse leaf-peeling). The recent commits "Add reverse cotree
     leaf-peeling invariants" / "Derive reverse cotree side labels" are partial
     progress toward it.

   {{NEEDS_PROOF}} A producer
   `…_choose_splitPool_eq_of_<leaf-peeling-invariant>` (stComponentDrawing
   level) that discharges the wrapper's `hchoose` from the carried invariant
   does not yet exist and is the next sub-project.

3. The label-constancy invariant must be **maintained**: after inserting cotree
   edge `j`, re-establish `hadj` for the next unpeeled prefix. Threading this
   alongside the SameFaceData chain is the bulk of the induction.

---

## 5. Main-branch shape (`straightLineCanonicalComponentResidualMapPlanarityOfARR`)

Replace the `sorry` with:

1. `a := lvertex.length - 1`, `b := lface.length - 1`, `t := m - a`.
2. A local cotree-offset induction (on `t`, base = §2 seed, step = §3 wrapper)
   producing `Nonempty (ResidualMapPrefixStepSameFaceData … (a+t) …)`, carrying
   the §4.3 label-constancy invariant.
3. `.toInsertion` to finish as a plain `ResidualMapPrefixStepInsertion`.

---

## 6. Effort

- §0 (selector plumbing): **DONE**, builds.
- §2/§3/§5 (induction scaffold, index/ARR bookkeeping, `hcoverage`): tractable
  assembly, ~1 session once §4.2 exists.
- §4.2/§4.3 (the `hchoose` producer from the carried leaf-peeling invariant):
  the hard core, its own sub-project — frame as **a separate session** of
  combinatorial-map work, not a loose end.

Verification: `./lake-build.sh LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter`,
then `#print axioms straightLineCanonicalComponentResidualMapPlanarityOfARR`
(expect only Lean core axioms; no `sorryAx`).
