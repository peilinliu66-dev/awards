# An elementary integer construction for Erdős 808

The graph sum-product conjecture was disproved by Alon, Ruzsa and Solymosi,
*Sums, products, and ratios along the edges of a graph*, Theorem 3,
[author preprint](https://arxiv.org/abs/1802.06405).
The following nonoptimal reciprocal-factor construction is the mathematical
argument formalized in this package.

## 1. Vertices and edges

Let g,h be positive integers, D=(g+1)!, and B=(g+2)h. For
2 <= i <= g+1 and 0 <= u < h, put

    L(i,u) = Di(B+u),       R(i,u) = (D/i)(B+u).

The divisor i divides D, so all labels are positive integers. For each i,
join every R(i,u) to every L(i,v), with 0 <= u,v < h.

To prove that the left labels are distinct, suppose i<j. Then

    iu < ih <= (g+1)h < B,
    i(B+u) < (i+1)B <= jB <= j(B+v).

This rules out equality across different i. With i fixed, cancellation
gives equality of u. Equal right labels, after multiplication by ij and
cancellation of D, give j(B+u)=i(B+v). The same separation argument gives
i=j and then u=v.

Finally, for any permitted u and any left-side index j,

    R(i,u) <= D(B+u) < 2DB <= Dj(B+v) = L(j,v).

Here u<h<=B and j>=2. The two sides are disjoint. Hence all 2gh vertex
labels are distinct. Each component is a complete bipartite graph with
h vertices on each side, and components have disjoint vertex sets. In
particular the canonical edge pairs have strictly increasing endpoints,
no loops or repetitions, and

    n = |A| = 2gh,          e = |E| = gh².

## 2. Counting the outputs

The product on an edge in the i-th block is

    R(i,u)L(i,v) = D²(B+u)(B+v),

independent of i. There are at most h² products.

The sum on such an edge is

    R(i,u)+L(i,v) = (D/i)((i²+1)B + i²v + u).

Since 0 <= i²v+u < (i²+1)h <= ((g+1)²+1)h, there are at most
((g+1)²+1)h sums in each block, and at most g((g+1)²+1)h in total.
For g>=1, ((g+1)²+1)<=5g². Consequently

    |A +_G A| + |A *_G A| <= 5g³h + h².

All bounds are image-cardinality bounds on the actual finite sets. There
is no assertion that different parameters always produce different sums
or products; collisions only strengthen the required upper bounds.

## 3. One fixed parameter pair, every size threshold

For any positive integer t, set g=8t⁴ and h=4096t¹². Then

    n = 65536t¹⁶ = (2t)¹⁶,
    e = 134217728t²⁸ >= 67108864t²⁶ = n^(13/8).

The output bound becomes

    5g³h+h² = 27262976t²⁴
             < 33554432t²⁵
             = (2t)²⁵
             = n^(25/16).

The strict inequality uses t>=1. The real-power identities are proved
from Mathlib's real-power multiplication theorem, with nonnegative bases.
Given any threshold N, take t=N+1; then N<=t<=(2t)¹⁶=n.

Finally 13/8=1+5/8 and 25/16=1+5/8-1/16. Thus the fixed choices c=5/8
and epsilon=1/16 yield counterexamples beyond every N. The maximum of
two nonnegative cardinalities is at most their sum, so this disproves
both the max version of the question and the sum version.

## 4. Formal endpoints

- `finite_construction`: arbitrary positive g,h, exact vertex and edge
  counts, positivity and graph validity, and the combined output bound.
- `arbitrarily_large_counterexamples`: every threshold N, with the fixed
  exponents 13/8 and 25/16 and genuine sum/product image cardinalities.
- `erdos_808`: the complete negation of `OriginalConjecture`.
- `erdos_808_sum`: the complete negation of `OriginalSumConjecture`.

The package uses no prime-counting estimates, supplied mathematical
axioms, finite-instance stand-ins, or asymptotic assumptions.
