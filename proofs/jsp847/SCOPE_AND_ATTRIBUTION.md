# Statement correspondence and attribution

## Original problem

- Catalog: JSP-000847, “How many cliques are needed to partition all edges of a dense graph?”
- Original source: P. Erdős, [*Some unsolved problems in graph theory and combinatorial analysis* (1971)](https://www.renyi.hu/~p_erdos/1971-25.pdf), printed page 101, item 11.
- Modern problem reference: [Erdős problem 1017](https://www.erdosproblems.com/1017).

The original question distinguishes edge-disjoint clique partitions from covers and seeks a nontrivial improvement on `floor(n^2/4)` when the graph has more than that many edges. The present theorem supplies an explicit linear saving in the edge surplus, uniformly for every finite graph.

## Formal correspondence

`CliquePartition G` contains a finite set of vertex blocks. Every block has at least two vertices and spans a complete subgraph. For every edge, `owns` requires exactly one block containing both endpoints. Thus edges are covered once, not merely at least once.

`edgeCount G` counts unoriented edges using `SimpleGraph.edgeFinset.card`. `partitionNumber G` is the minimum block count. [PartitionExistence.lean](Erdos1017/PartitionExistence.lean) proves both existence and attainment, so the minimum is not based on an assumed witness. `balancedThreshold n` is natural-number division `n^2 / 4`.

The final theorems quantify over every finite vertex type and every simple graph on it. They require no density premise, seed graph, auxiliary partition, asymptotic threshold, or parity restriction. Their dense specialization saves at least `ceil((e-A)/5000)` pieces when `e>A`. The empty graph is handled in the final proof. The exact value of the two-variable extremal function and an optimal saving constant are not asserted.

The fixed statement proposed for mathematical review is:

```
5000 * partitionNumber G + edgeCount G <=
  5001 * balancedThreshold (Fintype.card V)
```

The witness theorem proves the same expression with an actual partition's count. Both are in [Final.lean](Erdos1017/Final.lean).

## Mathematical sources and roles

- P. Erdős, A. W. Goodman and L. Pósa: the classical clique-partition bound underlying the question.
- E. Győri and A. V. Kostochka, *On a problem of G. O. H. Katona and T. Tarján*, Acta Mathematica Academiae Scientiarum Hungaricae 34 (1979), 321–327, Theorem 2, pp. 325–327: the weighted exact-partition theorem. The [volume archive](https://real-j.mtak.hu/7442/) supplies the original publication. This project proves its upper-bound part by finite induction in [WeightedFoundation.lean](Erdos1017/WeightedFoundation.lean); it is not an assumed axiom.
- F. R. K. Chung, [*On the decomposition of graphs* (1981)](https://fanchung.ucsd.edu/mypaps/fanpap/23decompositions.pdf): related weighted decomposition formulation and context.
- Bo Ning, [arXiv:2608.11536v1](https://arxiv.org/html/2608.11536v1), Lemmas 4.2–4.4 and 4.6: the finite extraction and triangle-repacking route adapted here. The present assembly uses a maximum-degree cut, an explicit cyclic matching coloring, and the clique-partition deficit to obtain the displayed uniform integer bound.

The exact bound and its complete proof are supplied together in this project for review. These source attributions distinguish the classical mathematical ingredients from the present formalization and quantitative assembly.

## Formalization authorship and relevant earlier submissions

The original Lean formalization in this directory is contributed by [@peilinliu66-dev](https://github.com/peilinliu66-dev), with AI assistance. It was implemented from the mathematical arguments above; no third-party Lean proof body is vendored. Mathlib is obtained as a separately pinned dependency with its own license.

[PR #629](https://github.com/TheJustinSunPrize/awards/pull/629) formalizes the classical `cp(G) <= floor(n^2/4)` bound, and [PR #600](https://github.com/TheJustinSunPrize/awards/pull/600) supplies balanced-bipartite sharpness. The contribution here is the uniform surplus-dependent saving for every dense graph, including its weighted foundation and an actual exact partition witness. [PR #3900](https://github.com/TheJustinSunPrize/awards/pull/3900) concerns a specific small-graph case.
