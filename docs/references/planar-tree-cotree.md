# Tree-Cotree Decompositions

Source:

- Jeff Erickson, *Computational Topology*, Lecture 10, “Tree-Cotree Decompositions”
- PDF: https://jeffe.cs.illinois.edu/teaching/comptop/2020/notes/10-planar-tree-cotree.pdf
- Sergei K. Lando and Alexander K. Zvonkin, *Graphs on Surfaces and Their
  Applications*, §1.3.3 (maps as dart permutations `σ`, `α`, `φ`).

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
- `CrossingLemma.exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident`
  constructs the actual leaf-insertion witness from the tree-order local data:
  the old endpoint has an incident dart in the predecessor prefix and the other
  endpoint is fresh.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`
  constructs the two predecessor corners at old endpoints and turns a
  predecessor-face `SameCycle` proof for those corners into the actual
  `ResidualMapPrefixStepInsertion.sameFace` witness.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one`
  discharges that `SameCycle` condition in the one-face predecessor case.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_planar_tree_prefix`
  obtains the one-face hypothesis from the planar tree-prefix count
  `|E| = |V| - 1`.
- The missing global witness is the tree-first / cotree-second edge order.
- This theorem is the exact combinatorial bridge needed to convert a spanning
  tree on `vertexGraph` into the dual-side edge order on `faceGraph`.

Formalized bridge pieces now available:

- `CombinatorialMap.vertexGraphEdge` and
  `CombinatorialMap.exists_vertexEdgeInjection_of_leafOrder` construct concrete
  primal map-edge witnesses from a leaf order on a vertex-graph spanning tree.
- `CombinatorialMap.faceGraphEdge`,
  `CombinatorialMap.exists_faceEdgeInjection_of_leafOrder`, and
  `CombinatorialMap.dualEdgeEquiv` do the corresponding cotree-side extraction.
- `CombinatorialMap.dualVertexEquivFace` identifies dual vertices with original
  face classes, and `CombinatorialMap.exists_dart_faceGraphEdge_faces` unwraps a
  face-graph adjacency into a concrete dart `d` whose original edge separates the
  two original face classes `Face_mk d` and `Face_mk (edgePerm d)`.
- `SimpleGraph.Equiv.Perm.exists_map_fin_twoBlocks` and
  `SimpleGraph.Equiv.Perm.exists_map_fintype_twoBlocks` assemble disjoint primal
  and cotree edge injections into one two-block ambient edge permutation.
- `SimpleGraph.Equiv.Perm.exists_castLE_map_fin`,
  `SimpleGraph.Equiv.Perm.exists_twoBlocks_map_fin`, and
  `SimpleGraph.Equiv.Perm.exists_twoBlocks_map_fintype` provide the inverse
  block convention used by ordered prefixes: a block position evaluates to the
  selected edge.
- `CombinatorialMap.card_vertexTreeLeafOrder_add_dualVertexLeafOrder_eq_card_edge`
  formalizes the von Staudt count
  `|E| = (|V|-1)+(|V(M.dual)|-1)` in the list-length form used by leaf orders.
- `CombinatorialMap.exists_edgePermutation_of_disjoint_vertex_dual_leafOrder_edges`
  turns disjoint concrete primal/cotree edge injections into the single
  tree-first/cotree-second edge permutation.
- `CombinatorialMap.exists_edgePositionPermutation_of_disjoint_vertex_dual_leafOrder_edges`
  gives the corresponding position-valued version, matching the way an edge
  permutation is read as an ordered edge list.
- `CrossingLemma.DrawnMultigraph.treeEdgeOfLeafOrder`,
  `CrossingLemma.DrawnMultigraph.treeEdgeOfLeafOrder_spec`, and
  `CrossingLemma.DrawnMultigraph.treeEdgeOfLeafOrder_injective` name the
  concrete drawing edges selected by the parent edges in a vertex-tree leaf
  order, record their endpoint alternatives, and prove that these selected
  drawing edges are distinct.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident`
  packages the tree-phase endpoint incidence conditions into the constructor
  `ResidualMapPrefixStepInsertion.leaf`, with no additional planarity
  hypothesis.
- `CrossingLemma.endAngleKey_prefix_step_endpoint_old_iff` formalizes the
  local fact that adding the new dart at an endpoint does not reorder the
  carried-over incident darts.
- `CrossingLemma.two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident`
  supplies the common cardinality witness: one old incident dart plus the new
  last-edge dart.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`
  packages the same-face local data into constructor-facing corners and the
  final `ResidualMapPrefixStepInsertion.sameFace` witness, assuming the
  predecessor `SameCycle` condition for those corners.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one`
  combines that local same-face witness with
  `CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one`, giving the first
  cotree-step witness once the primal tree prefix has been counted to one face.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_planar_tree_prefix`
  combines the same local witness with
  `CombinatorialMap.card_face_eq_one_of_isPlanar_of_card_edge_eq_card_vertex_sub_one`,
  matching the planar tree-prefix form used in the tree-cotree transition.

Still missing:

- The planar-map complement theorem itself: for a connected planar
  combinatorial map, the complement of a chosen primal spanning tree is a dual
  spanning tree.  The count half and finite edge-order assembly are now
  formalized; the missing part is the graph-theoretic complement/disjointness
  and dual connected/acyclic proof.
- The residual-map face-stability proof that the cotree block, in reverse leaf
  order, supplies the `SameCycle` hypotheses required by the same-face insertion
  witness.

Notes for formalization:

- The planar-map complement theorem should be stated in the combinatorial-map
  layer, not as a generic graph theorem, because the face side is carried by the
  dual map.
- The same-face insertion layer is written in the Lando--Zvonkin §1.3.3
  dart-permutation language: `σ` is the vertex rotation, `α` is the edge
  involution, and `φ` is the face permutation.
- The face-count lemma in `CombinatorialMap.Basic` is a useful corollary once the
  primal tree phase is in place, but it does not replace this complement theorem.
