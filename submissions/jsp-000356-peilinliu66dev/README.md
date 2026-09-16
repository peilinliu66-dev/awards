# JSP-000356 / Erdős 437: square initial products

This package formalizes the complete affirmative answer to the original
[Erdős problem 437](https://www.erdosproblems.com/437), listed as
[JSP-000356](../../problems/catalog-0301-0400.md#jsp-000356), and also proves
that the maximal number of square initial products has density zero.

## Statement correspondence

For every real epsilon > 0, there is a real X0 such that, for every real
x >= X0, there is a finite strictly increasing sequence of positive integers
at most x with more than x^(1-epsilon) square nonempty initial products.
This is `JSP356.erdos_437_real`; it includes all sufficiently large real
cutoffs, not just an integer subsequence or one fixed epsilon.

For a finite set A of positive integers, `prefixProduct A t` is the product
of its members at most t. `squareCuts A` contains exactly those t in A for
which this product is square. Thus the empty prefix is not counted.
`sequenceSquareCuts` uses actual sequences `Fin m -> Nat`. The source proves
that increasing enumeration of A preserves the count.

`JSP356.erdos_437` combines `OriginalLowerQuestion` with
`DensityZeroUpperQuestion`. The latter says that for every epsilon > 0,
all sufficiently large integer N and every A contained in {1,...,N}, the
number of square nonempty prefixes is strictly smaller than epsilon*N.
Consequently the maximal count L(x) satisfies L(x)=x^(1-o(1)) and L(x)=o(x).
These maximum-function statements are interpretations of the explicit
uniform/existential theorems; no separate definition of L is used in Lean.
The later, sharper stretched-exponential estimates are not asserted here.

## Proof

Let r=pi(y). Products of k distinct primes at most y form a set of
binomial(r,k) distinct positive integers at most y^k. Among any r+1 such
integers, linear dependence of their prime-exponent parity vectors over
ZMod 2 gives a nonempty subset with square product. Partition the ordered
set into successive blocks of size r+1, choose one such subset per block,
and concatenate the chosen subsets. Each block endpoint is a distinct
square prefix. This gives the all-parameter finite bound
floor(binomial(pi(y),k)/(pi(y)+1)).

The Mathlib Chebyshev lower estimate and elementary logarithmic limits
imply, for each k, an eventual lower count greater than y^(k+1) at the
cutoff y^(k+4). Choosing k with k*epsilon>4 and bracketing an arbitrary
cutoff between successive (k+4)-th powers gives the original full endpoint.
The real-cutoff theorem includes an explicit floor step.

For the upper bound, consecutive square prefixes divide a sequence into
ordered nonempty square-product blocks. For fixed positive H, long blocks
consume disjoint H-element integer intervals. In a short block, every
prime greater than H divides at most one member and hence has even
valuation there. A squarefree-factor decomposition therefore places each
short block's minimum among at most 2^H*(sqrt(N)+1) possible integers.
The number K of blocks satisfies

    K <= N/H + 2^H*(Nat.sqrt N + 1).

The proof supplies the explicit implication
(4*Q*2^(2*Q))^2 <= N => Q*K <= N, and then the uniform density-zero bound.
The prefix-to-block construction and square cancellation are both proved.

## Files and reproduction

- `JSP356Finite.lean`: parity dependence, ordered packing, prime products,
  and the exact interpretation by increasing sequences.
- `JSP356Asymptotic.lean`: Chebyshev estimates and full lower endpoint.
- `Erdos437Upper.lean`: finite ordered-block upper bound and sublinearity.
- `JSP356UpperBridge.lean`: actual prefix-to-block construction.
- `Proof.lean`: combined theorem and terminal axiom reports.

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. Transitive revisions are fixed
in `lake-manifest.json`. From this directory run:

```sh
lake exe cache get
lake build
```

Actual package-directory `lake build`: PASS (8711 jobs).
Build evidence and source SHA-256 hashes are in `verification/`. The final
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. There are
no proof placeholders, custom axioms, native decision procedures, or
external proof oracles. Local verification reuses the pinned compiled
Mathlib cache; it is not official prize verification.

## Attribution and submission

The mathematical answer is known: Bui–Pratt–Zaharescu (2024), with its
application to this problem explained in
[Terence Tao's exposition of 9 August 2024](https://terrytao.wordpress.com/2024/08/09/a-result-of-bui-pratt-zaharescu-and-erdos-problem-437/).
The fixed-degree prime-product lower argument formalizes an elementary
specialization of the parity-packing mechanism. This submission seeks
formalization recognition, not mathematical discovery credit.

A pre-submission search of the official repository's 169 public Issue/PR
records through number 170 found no matching JSP-000356 / Erdős 437 entry.
That is a bounded public search, not a claim of global priority.

Proposed formalization recipient: `RECIPIENT-JSP-000356-PEILINLIU66DEV-A`;
public submitting account: `peilinliu66-dev`. Recipient confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No award or payment is
asserted. Source code is supplied under Apache-2.0.
