# JSP-000656 / Erdős 799: sublinear list chromatic number

This package formalizes the original asymptotic question in
[Erdős problem 799](https://www.erdosproblems.com/799), catalogued as
[JSP-000656](../../problems/catalog-0601-0700.md#jsp-000656).

## Exact statement and correspondence

For every real epsilon>0, the fraction of all simple labelled graphs G
on n vertices satisfying choiceNumber(G)>epsilon*n tends to zero as
n tends to infinity. All graphs are equally likely, so this is exactly
the random graph G(n,1/2). The final counting theorem makes the sample
space cardinality explicit:

    #{G on Fin n : epsilon*n < choiceNumber(G)} / 2^(choose(n,2)) -> 0.

`JSP656.erdos_799` proves `JSP656.OriginalStatement`, and
`JSP656.erdos_799_counting` states the displayed ratio directly.
The convergence runs through every sufficiently large integer n.

`choiceNumber G` is the actual least k for which every assignment of
finite color lists of size at least k admits a proper coloring choosing
from those lists. Existence, minimality, and the equivalence
`choiceNumber G <= k` iff `KChoosable G k` are proved. This is the list
chromatic number, not ordinary chromatic number or a numerical surrogate.

Although its initial definition uses natural-number color labels,
`KChoosable.color_lists` proves the same property for arbitrary color
types and arbitrary finite lists: the union of all input lists is finite
and can be relabeled. Lists may differ at every vertex. No pseudorandomness,
independent-set extraction, Hall, or counting hypothesis is retained in
either final theorem.

## Proof outline

The deterministic list-coloring lemma says: if every vertex subset of
size at least s contains an independent m-set, and n<=k*m, then the
graph is (k+s)-choosable. While a color occurs in at least s remaining
lists, color an independent m-set with it and remove that color from
the remaining lists. There are at most k such steps. At the end, each
remaining list has at least s colors and every color has bounded
multiplicity; incidence counting verifies Hall's condition and gives
distinct representatives. This works for the actual arbitrary input lists.

For fixed m and a grid of m^2*t vertices, the t^2 affine blocks
{(i,a*i+b): 0<=i<m}, with 0<=a,b<t, each have m vertices and meet
pairwise in at most one vertex. Their internal unordered edge-coordinate
sets are therefore disjoint. The source constructs the packing and its
edge-coordinate injection, then proves an explicit finite counting
bijection. For a fixed vertex subset, the probability that none of the
blocks is independent is exactly

    (1 - 2^(-choose(m,2)))^(t^2).

A union bound over at most 2^n vertex subsets shows that, for fixed
positive m and d, the probability of failing the independent-set
property for subsets of size at least floor(n/d)+1 tends to zero.
The quadratic exponent dominates the exponential factor 2^n; this
limit and all floor estimates are proved in Lean.

For a given epsilon>0, choose a fixed integer m>max(4/epsilon,1),
then take d=m and k=s=floor(n/m)+1. The deterministic lemma gives
choiceNumber(G)<=2*(floor(n/m)+1)<=epsilon*n eventually, except on
the already controlled exceptional set. This completes the original
o(n) assertion. The later sharper asymptotic estimates are not claimed.

## Files and reproduction

- `JSP656ListColoring.lean`: the finite arbitrary-list coloring lemma.
- `JSP656ChoiceNumber.lean`: the genuine least list-coloring threshold,
  arbitrary-color-type bridge, and deterministic bound.
- `JSP656Random.lean`: exact graph/bit counting, grid packing, exceptional
  probabilities, limits, and an assembly adapter.
- `JSP656.lean`: discharges the adapter with the proved list-coloring
  theorem and proves the complete original statement.
- `Proof.lean`: imports the complete result and prints terminal axioms.

Lean is pinned to `leanprover/lean4:v4.33.1`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive dependencies
are fixed in `lake-manifest.json`. From this package directory run:

```sh
lake exe cache get
lake build
```

Actual package-directory `lake build`: PASS (8711 jobs, exit 0). Both terminal
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders, custom mathematical axioms, native decision
procedures, or external proof oracles. Build logs and source SHA-256 hashes
are in `verification/`. Local verification reuses the pinned compiled
Mathlib cache and is not official prize verification. The build emits
non-failing linter warnings.

Repository validation, link checks, generation, consistency checks, and
history checks against `f4e7173d89dfe91022a185427d63452c8ffbf6ae` pass.
The unchanged repository unit suite was not repeated for this proof-only
package: the preceding run on the same base and Windows host passed
19 of 22 tests, with three recorded Windows path/history and symlink
privilege failures. These repository checks are separate from the
successful full Lean kernel build of this package.

## Attribution and prior work

Noga Alon solved the mathematical problem in 1992 with a stronger bound;
see [Choice numbers of graphs: a probabilistic approach](https://www.math.tau.ac.il/~nogaa/PDFS/choice.pdf),
Combinatorics, Probability and Computing 1 (1992), 107-114.
This submission concerns the Lean formalization of the original o(n)
conclusion and its exact statement correspondence, not discovery of the
mathematical result or the sharper estimates from later work.

A bounded search of 478 official public Issue/PR records through #479,
snapshotted on 2026-09-17 at 04:55 UTC, found no matching JSP-000656 /
Erdos 799 submission in their titles or bodies. This does not cover every
comment or later submissions and does not establish global priority.

A related public draft in
[rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/98630041efbcca1a31cee1c2aca8c035c2e9af57/proofs/Proofs/Erdos799Problem.lean)
(file blob `713c6dfde6917fe8adaf193064dde5e5e9b22029`, 174 lines)
was inspected. It declares `listChromaticRandom` and
`alon_krivelevich_sudakov_1999` as custom axioms; its terminal theorem
invokes the latter. It does not construct the actual random-graph model
or discharge that probabilistic theorem. This prior related formalization
attempt is disclosed; the present package supplies the actual invariant,
finite graph model, counting proof, and complete endpoint without custom
mathematical axioms. Maintainers should assess attribution and competing work.

The current catalog records `Lean proof: No` and `Eligible to claim: No`.
This package requests review of the completed formalization and any
applicable recognition eligibility. It does not change those catalog
fields or assert automatic entitlement to a payment.

Proposed formalization recipient: `RECIPIENT-JSP-000656-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No official verification,
award decision, or payment is asserted. Source code is under Apache-2.0.
