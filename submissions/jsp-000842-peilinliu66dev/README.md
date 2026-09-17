# JSP-000842 / Erdős 1012: an explicit threshold for a cycle of length n-k

This package formalizes the uniform estimate `f(k) = 5*k+5` for the
threshold requested in [Erdős problem 1012](https://www.erdosproblems.com/1012),
catalogued as [JSP-000842](../../problems/catalog-0801-0900.md#JSP-000842).
The original question asks to determine or estimate such a function.

## Exact statement and scope

For every pair of natural numbers k,n with `5*k+5 <= n`, every finite
simple graph G on n vertices satisfying

    choose(n-k-1, 2) + choose(k+2, 2) + 1 <= e(G)

contains a cycle of exactly n-k edges, hence n-k distinct cycle vertices.
This includes k=0 and every larger k. There are no unproved graph-theoretic
assumptions on the terminal theorem and no fixed upper bound on k or n.
The precise endpoint is:

```lean
theorem JSP842.erdos_1012_explicit_threshold
    (k n : ℕ) (hn : 5 * k + 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeFinset.card) :
    ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n - k
```

`JSP842.erdos_1012` proves the existential `OriginalStatement` by supplying
`threshold k := 5*k+5`. Thus the package supplies an explicit estimate in
the sense requested by the original question. It does not claim the
optimal threshold, Woodall's sharper sufficient range `n >= 2*k+3`, or
Woodall's stronger conclusion about every intermediate cycle length.

## Proof

Put m=n-k. Choose an m-element vertex subset whose induced graph H has
the maximum possible number of edges, and let d be its minimum degree.
Replacing a minimum-degree vertex by any outside vertex shows that each
outside vertex has at most d+1 neighbors in H. Therefore

    e(G) <= e(H) + k*d + choose(k+1, 2).

If H is not Hamiltonian, extend it to an edge-maximal non-Hamiltonian
graph F on the same vertices. The package proves Ore's edge-addition
lemma by explicitly splicing a Hamiltonian path into a Hamiltonian cycle.
It follows that the degree sum of each nonadjacent pair in F is at most
m-1. Choose a nonadjacent pair with maximum degree sum and let t be the
smaller endpoint degree. The t=0 case is immediate. Otherwise there are
t vertices of degree at most t, whence

    e(H) <= choose(m-t, 2) + t*t,    d <= t,    2*t <= m-1.

For B=choose(m-t,2)+t*t+k*t+choose(k+1,2) and
T=choose(m-1,2)+choose(k+2,2), the integer factorization

    2*(B-T) = (t-1)*(3*t+2*k+4-2*m)

is nonpositive because m>=4*k+5. This contradicts e(G)>=T+1, so H has
a Hamiltonian cycle. The final bridge transports that cycle to G and
proves its length is exactly n-k. See [PROOF.md](PROOF.md) for the full
finite argument.

## Files and reproduction

- `JSP842Arithmetic.lean`: binomial identities and integer inequalities.
- `JSP842DenseSubset.lean`: maximum-induced-subgraph swap and edge count.
- `JSP842ClosedBound.lean`: edge bound for a graph closed under Ore addition.
- `JSP842ThresholdBound.lean`: the uniform numerical contradiction.
- `JSP842Maximal.lean`: a maximal non-Hamiltonian supergraph.
- `JSP842CycleBridge.lean`: complete-graph Hamiltonicity and cycle transport.
- `JSP842Ore.lean`: the proved Ore edge-addition lemma.
- `JSP842Assembly.lean`: connects the finite counting and graph lemmas.
- `JSP842.lean`: unconditional original-problem endpoints.
- `Proof.lean`: imports the complete development and prints terminal axioms.

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. All transitive revisions are
fixed in `lake-manifest.json`. From this directory run:

```sh
lake exe cache get
lake build
```

Local `lake build` passed on 2026-09-17 (8716 jobs). Both terminal
theorems report exactly `[propext, Classical.choice, Quot.sound]`.
All package proof modules were compiled from source; the pinned compiled
Mathlib cache was reused. No source uses `sorry`, `admit`, custom axioms,
or `native_decide`. See `verification/lake-build.log`,
`verification/local-build.json`, and `verification/source-sha256.txt`.
These are local reproduction records, not official prize verification.

## Attribution and prior work

This is known mathematics, not a claim of a newly discovered mathematical
theorem. The primary problem page and the official catalog attribute the
question and existence result to Erdős, *Remarks on a paper of Pósa*
(1962), 227-229 [Er62e]; the k=0 result to Ore,
[Arc coverings of graphs](https://doi.org/10.1007/bf02412090) (1961),
315-321 [Or61]; the k=1 result to Bondy,
[Large cycles in graphs](https://doi.org/10.1016/0012-365x%2871%2990019-7)
(1971/72), 121-132 [Bo71b]; and the stronger general result to Woodall,
*Sufficient conditions for circuits in graphs* (1972), 739-755 [Wo72].
The proof uses the classical Ore closure method with elementary finite
extremal counting. This submission claims the Lean formalization of the
explicit estimate and its correspondence to the original question.

A bounded check on 2026-09-17 at 05:36:58 UTC inspected 498 official public Issue/PR records through #499 and found no JSP-000842 / Erdős 1012 / original-URL match in titles or bodies. The compact evidence and raw-snapshot hash are in `verification/official-search-summary.json`. A single focused public code query found related Lean files, but the inspected graph-existence endpoints depended on custom axioms or `sorry`; complete axiom-free related files handled threshold arithmetic. See [novelty.md](novelty.md) for exact scope and prior-work disclosure. This check does not establish global priority.

The reviewed catalog lists `Solved`, `Lean proof: No`, and
`Eligible to claim: No`. Organizer assessment is requested for the
formalization and its eligibility; no status change or award is asserted.

Proposed formalization recipient: `RECIPIENT-JSP-000842-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a
self-submission with a direct interest in possible recognition. No
official verification, recipient confirmation, award decision, or payment
is asserted. Source code is under Apache-2.0.
