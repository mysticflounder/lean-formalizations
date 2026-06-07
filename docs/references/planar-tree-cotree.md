# Tree-Cotree Decompositions

Source:

- Jeff Erickson, *Computational Topology*, Lecture 10, “Tree-Cotree Decompositions”
- PDF: https://jeffe.cs.illinois.edu/teaching/comptop/2020/notes/10-planar-tree-cotree.pdf

Relevant material:

- The duality between even subgraphs and edge cuts.
- The duality between cycles and bonds.
- The spanning-tree / spanning-cotree complement theorem for a planar map.

Working paraphrase of the key theorem:

If `Σ = (V, E, F)` is a connected planar map and `E` is partitioned as `T ⊔ C`,
then `T` is a spanning tree of `Σ` if and only if the complementary dual edges
`C*` form a spanning tree of the dual map `Σ*`.

Equivalent reading:

- Choose any spanning tree `T` of the primal map.
- The remaining edges `C = E \ T` correspond to a spanning tree in the dual map.

Why this matters here:

- The local residual-map lemmas already turn individual edge additions into
  `ResidualMapPrefixStepInsertion` witnesses once an order is fixed.
- The missing global witness is the tree-first / cotree-second edge order.
- This theorem is the exact combinatorial bridge needed to convert a spanning
  tree on `vertexGraph` into the dual-side edge order on `faceGraph`.

Notes for formalization:

- The planar-map complement theorem should be stated in the combinatorial-map
  layer, not as a generic graph theorem, because the face side is carried by the
  dual map.
- The face-count lemma in `CombinatorialMap.Basic` is a useful corollary once the
  primal tree phase is in place, but it does not replace this complement theorem.
