# A uniform dense clique-partition bound

Version: 2026-10-03. The complete formal proof is in the accompanying Lean
source. All 23 project modules have been cleanly rebuilt and the three main
targets have passed the recorded axiom audit. This note explains the mathematical
argument and its correspondence to Erdős’s 1971 request for a nontrivial dense
sharpening of the edge-disjoint clique-partition bound.

Write n=|V|, e=|E|, p=cp(G), A=floor(n²/4), and d=n²/4−p.

## Exact partitions and weighted foundation

Blocks are finite cliques of order at least two, with unique edge ownership.
The single-edge partition proves existence. The well-ordering of the natural
numbers gives attained minima for count and total block order.

The weighted theorem is proved by induction on a finite active vertex set S.
Choose x with maximum number k of other nonneighbors. If every neighbor has
fewer than k nonneighbors, complement greedy coloring partitions N(x) into at
most k cliques. Cone these over x. The added weight is at most |S|−1.

Otherwise choose adjacent y with the same k. Let Z be a maximum clique in the
common neighborhood, t=|Z|, allowing t=0. First use Z∪{x,y} as one clique block and remove its edges. The residual
neighborhoods R=N(x)\({y}∪Z), B=N(y)\({x}∪Z) each have fewer than k internal
nonneighbors, because every vertex misses the opposite apex or some Z vertex
outside its residual set. Cone a k-color vertex-clique partition of R over x.
Each B vertex loses at most t−1 further neighbors, with natural subtraction:
its R fiber intersects B in a clique of order at most t. Cone the remaining B
graph using k+(t−1) colors. The total added weight is at most 2(|S|−1).

The remainder has one or two fewer active vertices. The corresponding
floor-square increments yield a partition of total order at most floor(n²/2)
=2A. This is the upper-bound part of Győri–Kostochka's exact-partition proof;
no equality characterization is used.

## Minimum-weight skeleton and cut

Choose a minimum-weight partition. If r blocks have order at least 3, then
2·blockcount+r≤weight≤n²/2, so r≤2d. Its single-edge blocks form a graph H.
A triangle in H could replace three two-vertex blocks by one three-vertex
block, reducing weight6 to3. Hence H is triangle-free and e(H)≥n²/4−3d.

For a maximum-degree vertex of H, put X=N_H(v), Y=V\X. X is independent.
The sum of degrees over Y gives e(H)+e(H[Y])≤|X||Y|. Consequently, writing
D=n²/4−e(H), one has e(H[Y])≤D, missing crossing pairs≤2D, and
(|X|−n/2)²≤2D. Restricting the original partition to X and Y gives genuine
partitions of both induced graphs, each with at most 5d pieces. In G the same
cut has at most6d missing crossing pairs and squared imbalance at most6d.

## Explicit triangle repacking

Orient the cut so X has at least as many internal edges as Y; let m=e(G[X]).
Label X by Z/|X|Z and color an edge by the sum of its endpoint labels. Each
color is a matching. Finite translate averaging retains min(|X|,|Y|) colors,
discarding ell edges with

    |X| ell <= (|X|−min(|X|,|Y|)) m.

Assign retained colors to distinct Y vertices as triangle apices. A missing
crossing pair rejects at most one candidate because each color is a matching.
The valid triangles are pairwise edge-disjoint. Combining them, unused edges
and the actual Y-side partition gives an actual partition Q with

    |Q| + m <= crossingEdges + 2ell + 2missingPairs + YpartitionCount.

If 10000d≤n², the squared imbalance implies19n≤40|X|≤21n and both sides are
nonempty. It follows that 9ell≤m. The displayed partition inequality implies
m≤36d and e−n²/4≤72d. If 10000d>n², the elementary e≤n²/2 bound instead gives
e−n²/4≤2500d. Thus the latter uniform real inequality holds in every case.

## Exact integer endpoint

When e>A, p<A: otherwise a partition of weight≤2A must have exactly A blocks,
all of order2, forcing e=A. Thus A−p≥1. The square remainder gives
0≤n²/4−A≤1/4. Absorbing this bounded floor error into the positive integer
deficit yields e−A≤5000(A−p). If e≤A, the classical p≤A bound gives the same
final inequality. The empty graph is handled explicitly.

The resulting statement is 5000p+e≤5001A, and the attained count minimum yields
an actual partition witness. The extraction/repacking route is attributed to
Ning's finite lemmas, with the explicit cut and color simplifications above.

## Original problem and conclusion

Erdős, *Some unsolved problems in graph theory and combinatorial analysis*
(1971), printed page 101, item 11, asks for a nontrivial sharpening of the
edge-disjoint clique-partition bound when e > floor(n²/4).
For every such graph, the proved integer endpoint is equivalent to

    cp(G) <= A - ceil((e(G)-A)/5000),   A = floor(n²/4).

It therefore saves at least one clique for every positive surplus and gives a
uniform saving linear in that surplus. This statement covers every finite order,
both parities, and all densities. The proof also returns an actual exact
partition attaining the bound. The constant 5000 is the explicit constant
proved here; no optimal-constant assertion is needed.

The detailed attribution and source locations are in
[SCOPE_AND_ATTRIBUTION.md](SCOPE_AND_ATTRIBUTION.md). The target theorem is
`Erdos1017.exists_partition_dense_saving` in [Final.lean](Erdos1017/Final.lean),
and the minimum-number form is `Erdos1017.uniform_integer_dense_saving`.
