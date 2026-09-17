# JSP-000665 / Erdős 808: graph-restricted sum-product counterexamples

This package formalizes a complete negative answer to
[Erdős problem 808](https://www.erdosproblems.com/808), catalogued as
[JSP-000665](../../problems/catalog-0601-0700.md#JSP-000665).

## Exact statement

The conjecture says that for every real c > 0 and epsilon > 0 there is a
threshold N such that every set A of at least N distinct positive integers,
together with a finite simple undirected graph on A having at least
|A|^(1+c) edges, has

    max(|A +_G A|, |A *_G A|) >= |A|^(1+c-epsilon).

The two sets contain the sums and products along graph edges. Vertices are
represented by `A : Finset Nat`. Edges are represented canonically by
`E : Finset (Nat × Nat)` with `GraphOn A E`: each pair has both endpoints
in A and its first endpoint is strictly smaller than its second. This is
the usual finite simple undirected graph encoding: loops are excluded,
there is no multiplicity, and each unordered edge is counted exactly once.
Every finite simple graph on a set of natural numbers has such an encoding.
`sumValues E` and `productValues E` are the actual images of E under addition
and multiplication, not upper-bound proxy functions.

`JSP665.erdos_808 : ¬ JSP665.OriginalConjecture` disproves the full max
statement. `JSP665.erdos_808_sum : ¬ JSP665.OriginalSumConjecture` also
disproves the version with the sum of the two cardinalities in place of max.
There are no unproved combinatorial, number-theoretic, or asymptotic
hypotheses in either terminal theorem.

The explicit theorem `JSP665.arbitrarily_large_counterexamples N` works
for every natural-number threshold N and returns positive integer A and
valid edges E with

    N <= |A|,
    |A|^(13/8) <= |E|,
    |A +_G A| + |A *_G A| < |A|^(25/16).

Thus the fixed positive parameters c = 5/8 and epsilon = 1/16 refute the
original universally quantified conjecture. This is an arbitrary-size
construction, not a finite numerical check or a conditional reduction.

## Construction and attribution

The mathematics is attributed to Noga Alon, Imre Z. Ruzsa, and József
Solymosi, [Sums, products, and ratios along the edges of a graph](https://arxiv.org/abs/1802.06405),
Publicacions Matemàtiques 64 (2020), 143–155, Theorem 3. This formalization
uses a deliberately nonoptimal integer-interval version of the reciprocal
factor construction, avoiding prime-counting estimates. It claims the
formalization and explicit correspondence to the complete question, not
discovery of the known mathematical result.

For positive g,h, the construction has exactly 2gh vertices and gh² edges,
and the sum of the output cardinalities is at most 5g³h+h². Choosing
g=8t⁴ and h=4096t¹² gives |A|=(2t)¹⁶ and the stated strict inequalities.
Taking t=N+1 supplies every required threshold. See `PROOF.md` for the
complete mathematical argument and `JSP665.lean` for the kernel-checked proof.

## Reproduction

Lean is pinned to `leanprover/lean4:v4.33.1`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive dependency
revisions are fixed in `lake-manifest.json`. From this directory run:

```sh
lake exe cache get
lake build
```

`Proof.lean` imports the complete proof and prints its terminal axioms.
All source modules are default Lake build roots.

Local `lake build` passed on 2026-09-17. The finite construction, arbitrary-size
counterexample theorem, and both original-conjecture negations use only
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The build
reused the pinned compiled Mathlib cache; every package proof module was
compiled from source. See `verification/lake-build.log`,
`verification/axioms.json`, `verification/local-build.json`, and
`verification/source-sha256.txt`. These are local reproduction records,
not official prize verification.

Proposed formalization recipient: `RECIPIENT-JSP-000665-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No official verification,
award decision, or payment is asserted. Source code is under Apache-2.0.
