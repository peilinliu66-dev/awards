# JSP-000697 / Erdős 841: original density-zero question

This package addresses the original near-linear-exceptional-set question in
[Erdős problem 841](https://www.erdosproblems.com/841), catalogued as
[JSP-000697](../../problems/catalog-0601-0700.md#jsp-000697).

## Exact statement

For a positive integer n, let t(n) be the least nonnegative integer t for
which a finite subset S of {n+1,...,n+t} satisfies that n times the product
of S is a square. The members of S are distinct. Empty S is allowed,
giving t(n)=0 precisely for square n. The source proves existence of an
admissible delay, defines its actual minimum, and proves its minimality.

For EVERY function eta: Nat -> Real tending to zero, the source proves

    #{1 <= n <= N : 2 <= n and n^(1-eta(n)) <= t(n)} / N -> 0.

The terminal theorem `JSP697.erdos_841_limit` states this ordinary limit.
`JSP697.erdos_841_full_original` gives all quantifiers explicitly:
for every such eta and every real epsilon>0, there exists N0 such that
EVERY integer N>=N0 has exceptional count strictly below epsilon*N.
No sign, monotonicity, rate, or uniformity hypothesis on eta is imposed.
This is the original n^(1-o(1)) density-zero question, rather than only
a statement about t(n)/n, a finite experiment, or a selected subsequence.

The later, stronger Dickman-distribution theorem and finer pointwise
estimates are outside this submission's claimed scope. The broad catalog
title asks for estimates; the precise original question above is the
statement for which recognition is requested.

## Proof outline

For n=ab, a=b makes n square. Otherwise the three distinct integers
a(b+1), (a+1)b, (a+1)(b+1) lie between n+1 and n+a+b+1, and their product
times n equals [ab(a+1)(b+1)]^2. Thus t(ab)<=a+b+1.

Suppose 2<=Y<=n and 2n+Y<t(n)Y. Choose the least divisor d of n with
d>=Y and write n=db. If b>=Y, the rectangle construction contradicts
the displayed inequality. Hence b<Y. For a prime p dividing d, write
d=pc; minimality gives c<Y. Therefore n=mp with p prime and m=bc<Y^2.

Let C(N,L,M) contain all mp<=N with 1<=m<=M and p prime, p>=L.
Chebyshev's theta bound and the elementary harmonic bound give

    #C(N,L,M) * log L <= 3N * (1 + log M).

For integer k>=7 and q sufficiently large, bracket any cutoff N by
q^(k+1)<=N<(q+1)^(k+1). If exceptional n is between q^k and N,
its near-linear delay is at least q^(k-1). Using Y=q^3 above puts it
in C(N,q^(k-6),q^6). The smaller n contribute at most q^k, giving

    exceptional count / N <= 1/q + 21/(k-6).

Choose k first and then a sufficiently large threshold for q. The proof
brackets every sufficiently large N, so the density conclusion holds
without restricting cutoffs. Finally eta(n)->0 supplies every fixed
near-linear exponent bound required in this argument.

## Files and reproduction

`JSP697.lean` contains the entire proof. `Proof.lean` imports it and prints
the terminal axiom dependencies. Lean is pinned to
`leanprover/lean4:v4.33.1`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive dependencies
are fixed in `lake-manifest.json`. From this package directory run:

```sh
lake exe cache get
lake build
```

Actual package-directory `lake build`: PASS (8708 jobs). Terminal axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders, custom axioms, native decision procedures,
or external proof oracles. Build logs and source SHA-256 hashes are in
`verification/`. Local verification reuses pinned Mathlib compiled caches;
it is not official prize verification. Linter warnings concern unused
variables and tactic sequencing only.

## Attribution and existing work

The mathematical problem and its answer are known. See Bui, Pratt and
Zaharescu, [A problem of Erdős-Graham-Granville-Selfridge on integral points on hyperelliptic curves](https://arxiv.org/abs/2211.12467)
(2024 publication), which proves a stronger distribution result.
The present contribution is the explicit elementary density argument's
Lean formalization and accompanying statement correspondence, not a
claim to discovery of the mathematical answer.

A current public source in
[rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos841Problem.lean)
was inspected at file hash `1ecb9da4973b6c1ccd853d413955a7be94a570fc`:
169 lines, with four custom axioms (`t`, `trivial_lower_bound`,
`selfridge_equality`, `selfridge_upper_bound`). It does not contain
the density theorem formalized here. This prior related work is disclosed;
this submission does not claim the first public mention of formalizing E841.

A bounded search of 443 official public Issue/PR records through #444
found no matching JSP-000697 / Erdős 841 submission. A search miss is
not a proof of global priority; maintainers should assess competing work.

Proposed formalization recipient: `RECIPIENT-JSP-000697-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`. Identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No official verification,
award decision, or payment is asserted. Source code is under Apache-2.0.
