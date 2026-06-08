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
- `CombinatorialMap.faceEdgeOfLeafOrder_spec_cases` and
  `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec_cases` split the unordered
  cotree endpoint statement into the two dart orientations, matching the
  constructor-facing corner data for same-face residual insertions.
- `CombinatorialMap.faceEdgeOfLeafOrderReverse`,
  `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec`, and
  `CombinatorialMap.exists_faceEdgeInjection_of_leafOrderReverse` read a dual
  leaf-insertion order backwards, the cotree-block convention where inserted
  dual edges peel leaves from the remaining dual tree.
- `SimpleGraph.connected_induce_take_of_leaf_insertion_parent` proves that each
  nonempty prefix of a parent leaf-insertion order is connected, and
  `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_connected`
  specializes this to the unpeeled dual prefix at a reverse cotree step.
- `SimpleGraph.Connected.apply_eq_of_forall_adj`,
  `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj`,
  and
  `CombinatorialMap.faceEdgeOfLeafOrderReverse_leaf_parent_label_eq_of_forall_adj`
  transport any edge-local split-face label invariant across that connected
  unpeeled prefix.
- `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj`
  turns the leaf/parent label equality into a constructor-facing cotree edge:
  the selected reverse cotree edge has a concrete dart representative whose two
  original incident faces receive equal labels.
- `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj`
  specializes this label transport to the split-face quotient for inserting an
  edge through one face: the selected reverse cotree edge has equal
  `insertedFaceSplitPoolEquiv` labels on its two old incident faces.
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
- `CrossingLemma.residualMapEdgeEquiv_edge_mk` and
  `CrossingLemma.DrawnMultigraph.permuted_prefix_last_endpoints_eq_or_eq_swap_of_residualMapEdgeEquiv`
  adapt a residual-map edge class selected by the cotree layer to the ordered
  drawing-prefix convention: the next permuted prefix edge has the two anchors
  of the selected residual dart and its opposite dart, up to orientation.
- `CrossingLemma.DrawnMultigraph.permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv`
  packages those two orientations with the non-loop endpoint inequalities
  required by the same-face prefix-step insertion constructor.
- `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv`
  combines a selected residual edge class, old endpoint incidence at its two
  anchors, and splice-corner face equality into the actual
  `ResidualMapPrefixStepInsertion.sameFace` witness.
- `CombinatorialMap.EdgeInsertion.insertedLeafEdgeMapAt` and
  `CrossingLemma.isPlanar_insertedLeafEdgeMapAt` make leaf insertion
  orientation-parametric: either of the two new darts may be the dart threaded
  into the old vertex cycle.  This matches the residual-map endpoint convention
  under `prefixStepDartEquiv`, where endpoint `.1` is `false` and endpoint `.2`
  is `true`.
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
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq`
  is the constructor-facing form needed by the cotree label invariant: equality
  of the predecessor face classes for the actual selected splice corners
  supplies the same-face witness.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one`
  combines that local same-face witness with
  `CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one`, giving the first
  cotree-step witness once the primal tree prefix has been counted to one face.
- `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_planar_tree_prefix`
  combines the same local witness with
  `CombinatorialMap.card_face_eq_one_of_isPlanar_of_card_edge_eq_card_vertex_sub_one`,
  matching the planar tree-prefix form used in the tree-cotree transition.
- `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq`
  and
  `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq`
  express the face-stability invariant needed after the first cotree step:
  carried old darts are in one successor face exactly when their images agree
  in the split-face quotient.
- `CrossingLemma.residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq`
  is the quotient-face equality form of the same criterion, matching the
  `Face_mk` equality consumed by the same-face prefix-step constructor.
- `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj`
  composes reverse cotree split-pool label transport with that residual
  same-face criterion: under a label invariant on the unpeeled dual prefix, the
  selected reverse cotree edge has equal successor face classes after the
  current same-face insertion.
- `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_inl_right`
  completes the old-corner side labels for a split face: the old cut corner
  `c₂` lands on side `1`, the same side as the new dart `dartA`, while the
  existing side lemmas put `c₁` and `dartB` on side `0`.
- `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_not_sameCycle_inl_corners`
  and `CrossingLemma.residualMap_prefixStep_sameFace_old_corners_not_sameCycle`
  package those side labels as the split-separation fact used by the cotree
  face-label invariant: after the insertion, the two old cut corners lie in
  different successor faces.
- `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_left_dartB`
  and `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_right_dartA`
  package the complementary local face witnesses: the old cut corner `c₁`
  remains in the successor face of `dartB`, and `c₂` remains in the successor
  face of `dartA`.
- `CrossingLemma.residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true`
  and
  `CrossingLemma.residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false`
  transport those witnesses through the prefix-step isomorphism, where `dartB`
  is the successor dart `(Fin.last m, true)` and `dartA` is
  `(Fin.last m, false)`.

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
