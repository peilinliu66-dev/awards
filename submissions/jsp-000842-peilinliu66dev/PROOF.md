# Finite proof of the explicit threshold estimate

Let k,n be natural numbers, n>=5k+5, m=n-k, and let G be a finite simple
graph on n vertices with at least
T+1=choose(m-1,2)+choose(k+2,2)+1 edges. Thus m>=4k+5>=5.

Choose an m-element vertex set U maximizing the number of induced edges.
Write H=G[U], let d be its minimum degree, and choose w in U of degree d.
For each u outside U, compare U with U-w+u. Maximality gives

    |N_G(u) intersect U| - indicator(u adjacent w) <= d.

Hence each of the k outside vertices sends at most d+1 edges into U.
Edges wholly outside U number at most choose(k,2). Splitting all edges
into the three disjoint classes yields

    e(G) <= e(H) + k*d + choose(k+1,2).                 (1)

Suppose H is not Hamiltonian, and choose an edge-maximal non-Hamiltonian
supergraph F of H on the same m vertices. Such a graph exists by finite
maximization. Let D(x) denote its degree. If nonadjacent u,v satisfied
D(u)+D(v)>=m, the maximality would make F+uv Hamiltonian. Removing uv
from a Hamiltonian cycle that uses this new edge gives a spanning path
x1=u,...,xm=v in F. There are D(u) indices i with u adjacent x_(i+1)
and D(v) indices i with v adjacent x_i, all among 1,...,m-1. Their sum
exceeds m-1, so some index satisfies both conditions. Splicing along

    u,x2,...,xi,v,x_(m-1),...,x_(i+1),u

gives a Hamiltonian cycle of F, a contradiction. A Hamiltonian cycle
not using the new edge already gives the contradiction. Consequently

    D(u)+D(v) <= m-1 for every nonadjacent pair.        (2)

Since complete graphs of order at least three are Hamiltonian, F has
a nonadjacent pair. Choose such a pair of maximum degree sum and orient
it so that t=D(u)<=D(v). Then d<=t and 2t<=m-1. If t=0, F has an
isolated vertex, so e(H)<=choose(m-1,2) and d=0. Equation (1) contradicts
the assumed edge lower bound.

Otherwise t>=1. Vertex v has at least t nonneighbors. Every such
nonneighbor x satisfies D(x)<=t, by the maximal degree-sum choice of
u,v. Select t of them. Edges with at least one selected endpoint are
at most the sum of these t degrees, hence at most t^2; the remaining
edges are at most choose(m-t,2). Thus e(H)<=choose(m-t,2)+t^2, and (1)
implies e(G)<=B=choose(m-t,2)+t^2+kt+choose(k+1,2).

Integer expansion gives

    2(B-T) = (t-1)(3t+2k+4-2m).

Since 2t<=m-1, we have

    2(3t+2k+4-2m) <= 4k+5-m <= 0.

As t-1>=0, B<=T, again contradicting e(G)>=T+1. Therefore H is
Hamiltonian. Its cycle has exactly |U|=m=n-k edges and transfers to G.
Taking f(k)=5k+5 proves the requested uniform threshold estimate.

The mathematics and scope are attributed in [README.md](README.md).
This argument does not establish the optimal threshold or Woodall's
stronger all-cycle-length conclusion.
