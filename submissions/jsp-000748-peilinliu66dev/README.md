# JSP-000748 / Erdős 900: long paths in the fixed-edge random graph

This package formalizes the complete statement of
[Erdős problem 900](https://www.erdosproblems.com/900), catalogued as
[JSP-000748](../../problems/catalog-0701-0800.md#jsp-000748).

## Exact statement and correspondence

There exists a single function f: Real -> Real such that:

- For every real c>1/2, 0<f(c)<1.
- As c approaches 1/2 from above, f(c) tends to 0.
- As c tends to infinity, f(c) tends to 1.
- For every fixed c>1/2, a uniformly sampled simple labelled graph with n
  vertices and exactly floor(c*n) edges has a simple path with at least
  f(c)*n edges with probability tending to 1 as n tends to infinity.

The original source uses "cn edges". This formalization makes the rounding
convention explicit as floor(c*n). Path length is the number of edges,
not the number of vertices. The real length threshold is equivalent to
an integer path length at least ceil(f(c)*n). The proof accounts for the
one-edge difference between stack size and path length.

The explicit witness is

    b(c) = (2*c - 1) / (8*c),
    f(c) = max(b(c)^2 / 2, 1 - 8/sqrt(c)).

`JSP748.erdos_900` proves `JSP748.OriginalStatement`, containing all these
quantifiers and both coefficient limits. `JSP748.erdos_900_fixed_c`
states the probability limit for every fixed c>1/2. The result does not
assume that c stays a prescribed distance from 1/2; its threshold may
depend on c. No uniform assertion for a varying c=c(n) is claimed.

`edgeUniverse n` is the finite set of two-element subsets of `Fin n`.
`graphFamily n m` is its m-element powerset family, so every graph with
exactly m edges occurs once. `pathProbability` is the exact ratio of
successful graphs to all such graphs. `HasPathAtLeast` uses a genuine
`SimpleGraph.Walk` satisfying `IsPath`. Eventually floor(c*n)<=choose(n,2)
is proved; the finitely many impossible small sample sizes do not affect
the limit. The final theorem concerns this fixed-edge model directly.

## Proof outline

An adaptive reveal tree queries each possible edge exactly once, choosing
the next edge using only previous answers. Its encoding and decoding form
a weight-preserving bijection between m-edge graphs and binary words of
length choose(n,2) and weight m. Exact prefix counts and the first two
factorial moments yield the hypergeometric mean and variance. Finite
Chebyshev bounds then control a lower tail without assuming independence.

A graph-specific depth-first search maintains finished vertices S,
unseen vertices T, a simple-path stack U, queried edges Q, and positive
queried edges P. The source proves all root, pop, negative-answer, and
positive-answer invariant preservation rules, including the S-by-T cut
query bound. Well-founded recursion constructs the actual adaptive tree.
When no sufficiently long path exists, its prefix contains too few
positive answers, so the hypergeometric lower-tail estimate applies.

Two explicit elementary numerical certificates supply a positive
coefficient for every c>1/2 and a coefficient approaching one for large c.
Their hypotheses are proved, not added to either final theorem. Floor
estimates, eventual admissibility, and limit algebra complete the passage
to all sufficiently large n. Both branches are combined by the displayed
maximum, and both required limits of the same f are proved.

## Files and reproduction

`JSP748.lean` is the complete self-contained proof; `Proof.lean` imports it
and prints terminal axiom dependencies. Lean is pinned to
`leanprover/lean4:v4.33.1`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive dependencies
are fixed in `lake-manifest.json`. From this package directory run:

```sh
lake exe cache get
lake build
```

Actual package-directory `lake build`: PASS (8708 jobs, exit 0). Both terminal
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders, custom axioms, native decision procedures,
or external proof oracles. Build logs and source SHA-256 hashes are in
`verification/`. Local verification reuses the pinned Mathlib compiled
cache; it is not official prize verification. The build emits non-failing
linter and tactic-suggestion messages.

Repository validation, link checks, generation, consistency checks, and
history checks against `f4e7173d89dfe91022a185427d63452c8ffbf6ae` pass.
The unchanged repository unit suite passes 19 of 22 tests on this Windows
host. Three previously observed failures concern historical statement
immutability, Windows backslash Git paths, and symlink privileges
(WinError 1314). These are repository/environment checks, separate from
the successful Lean kernel build.

## Attribution and prior work

The mathematical result is due to Ajtai, Komlós and Szemerédi,
[The longest path in a random graph](https://doi.org/10.1007/bf02579172)
(Combinatorica, 1981). The depth-first-search proof method follows
Krivelevich and Sudakov,
[The phase transition in random graphs: a simple proof](https://arxiv.org/abs/1201.6529).
This submission claims the Lean formalization and explicit correspondence
to the complete original statement, not discovery of the mathematical result.

A bounded pre-submission search covered 470 official public Issue/PR records
through #471 and found no matching JSP-000748 / Erdos 900 submission.
A search miss does not establish global priority. Two public Lean drafts
were inspected and are disclosed:

- [rjwalters/lean-genius, Erdos900Problem.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos900Problem.lean)
  (file blob `3ed425d7dfd658e65238373fe16313ce28b3dfec`, 287 lines)
  contains 19 custom axiom declarations and three proof placeholders.
  Its probability and path-coefficient definitions are placeholders, while
  the AKS statement and endpoint limits are postulated as axioms.
- [ryantuck/erdos-ai, 900.lean](https://github.com/ryantuck/erdos-ai/blob/f32b2886f8f005d481533036d0af4fe36e8e48f7/deepmind/deepmind/900.lean)
  (file blob `db4a1e33b881711a7227055f47272af08a8098de`, 70 lines)
  contains a genuine fixed-edge-model statement with the final proof
  still left as a placeholder.

Neither inspected source supplies the complete proof without custom axioms
or placeholders submitted here. These prior drafts mean that this is not the first public discussion
or statement formalization of E900; maintainers should assess attribution
and competing complete work.

The current catalog records `Lean proof: No` and `Eligible to claim: No`.
This package requests review of the completed formalization and of any
applicable recognition eligibility. It does not change the catalog or
assert that submission automatically qualifies for a payment.

Proposed formalization recipient: `RECIPIENT-JSP-000748-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No official verification,
award decision, or payment is asserted. Source code is under Apache-2.0.
