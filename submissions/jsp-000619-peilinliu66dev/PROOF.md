# Complete proof of the distinct-cycle-length bound

Let L(G) be the set of lengths of actual simple cycles of G. We prove,
for every integer s>=1, every k>=576, and every finite nonempty simple
graph G of minimum degree at least k and girth greater than 2s,

    k^s <= 24 * 192^s * |L(G)|.

## 1. Moore bound and expansion

A nonempty graph H with minimum degree at least d+1 and no cycle of
length at most 2s, where d,s>=1, has more than d^s vertices. Fix a root.
Two distinct simple paths of length n<=s with the same endpoints would
produce a cycle of length at most 2n<=2s. Thus their endpoints are
distinct. A path of length n<s can be extended through every neighbor
of its last vertex except its predecessor: any other already visited
neighbor would produce a forbidden cycle. Each path therefore has at
least d extensions, and different extensions remain distinct paths.
There are at least d+1 paths of length one, hence more than d^s paths
of length s. Their distinct endpoints prove the vertex bound. The Lean
module counts these actual simple paths; the bound is not an assumption.

We also use this finite core lemma: if the degree sum of a nonempty
graph on a vertex set Y is at least 2r|Y|, it has a nonempty induced
subgraph of minimum degree at least r. Choose a smallest nonempty subset
whose induced degree sum is at least 2r times its size. A vertex of
degree less than r can be deleted without destroying that inequality,
contradicting minimality. The singleton case is impossible when r>=1.

Now suppose H has minimum degree at least 6(d+1), with the same girth
condition. Every nonempty X with 3|X|<=d^s has more than 2|X| external
neighbors. Otherwise Y=X union boundary(X) has size at most 3|X|, all
neighbors of X lie in Y, and the degree sum of H[Y] is at least
6(d+1)|X|>=2(d+1)|Y|. The core lemma and Moore bound give
d^s<|B|<=|Y|<=3|X|<=d^s, a contradiction.

## 2. Finite DFS produces a long simple path

If 0<m<=|V(H)| and every m-element set has more than 2m external
neighbors, H contains a simple path of length at least 2m. Run DFS with
finished vertices S, stack U, and unvisited vertices T. The stack is a
simple path and there are no edges between S and T. At the first state
with |S|=m, boundary(S) is contained in U, so |U|>2m. The stack has at
least 2m edges. The Lean proof reaches a state with exactly m finished
vertices by well-founded induction on 2|T|+|U|. Every push, pop, or restart
strictly decreases this nonnegative integer, while preserving the DFS
invariants and never passing the desired number of finished vertices.

## 3. A dense BFS band

First restrict G to any connected component, preserving its minimum
degree and girth. Build a BFS parent tree, with level function l.
Adjacent vertices have levels differing by at most one. Assign every
edge vw to the band i=min(l(v),l(w)). Its vertices lie in levels i,i+1;
the upper layer has no edges in this band. Every edge is assigned once,
and each vertex belongs to at most two band vertex sets.

If the minimum degree is at least 48(d+1), the total degree sum is at
least 48(d+1)|V|. Some nonempty band has degree sum at least
12(d+1) times its vertex count: otherwise summing the band inequalities
would give a total at most 24(d+1)|V|, a contradiction. The core lemma
supplies a nonempty induced band subgraph of minimum degree at least
6(d+1). It inherits the girth bound.

Put m=floor(d^s/3), assuming d>=6. Then m>=2 and 3m<=d^s. The Moore
bound ensures enough vertices; the expansion and DFS lemmas supply a
simple path P of at least 2m edges in that band.

## 4. Distinct actual cycle lengths

From each disjoint pair of path positions (0,1),(2,3),...,(2m-2,2m-1),
select a vertex at the lower band level i. Such a vertex exists because
every band edge has minimum endpoint level i. These give m distinct
vertices at level i. Let their deepest common tree ancestor have level
r<i. The branches just below that ancestor partition the selected
vertices nontrivially. Select a vertex a so that at least half the
selected vertices lie in other branches; one of the two path directions
from a retains at least half of these. Thus at least m/4 selected
vertices lie on the same side of a in P and in different tree branches.

For every such vertex b, the tree path from a to b is simple, has the
same length 2(i-r)>=2, and all its internal vertices have level below i.
It meets P only at its endpoints, because every P vertex has level at
least i. Its union with the a-to-b segment of P is an actual simple
cycle. With a fixed and all b on the same side, the segment lengths are
distinct; adding the common tree-path length preserves distinctness.
Consequently m<=4|L(G)|. Cycle witnesses transfer injectively from the
chosen component back to the original graph.

## 5. Uniform constants and quantifiers

Given k>=576, put d=floor(k/96) and m=floor(d^s/3). Then d>=6,
48(d+1)<=k, k<=192d, and d^s>=6. Integer division gives
d^s<=6m. Combining the preceding estimates yields

    k^s <= 192^s d^s <= 6*192^s*m <= 24*192^s*|L(G)|.

The constant c_s=1/(24*192^s) is positive for every s>=1, and the
threshold 576 is uniform. All auxiliary statements, including the
Moore bound, are proved and instantiated in the final Lean endpoint.

Mathematical attribution and the precise formalization scope are in
[README.md](README.md).
