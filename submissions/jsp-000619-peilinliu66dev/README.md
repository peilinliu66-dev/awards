# JSP-000619 / Erdős 752: distinct cycle lengths in high-girth graphs

This package formalizes the complete asymptotic assertion in
[Erdős problem 752](https://www.erdosproblems.com/752), catalogued as
[JSP-000619](../../problems/catalog-0601-0700.md#JSP-000619).

For every integer s>=1 and every k>=576, a finite nonempty simple graph
with minimum degree at least k and no simple cycle of length at most 2s has

    |{lengths of simple cycles in G}| >= k^s / (24 * 192^s).

Thus c_s=1/(24*192^s)>0 and k_0=576 witness the requested Omega_s(k^s)
bound. The result covers every s and all sufficiently large k, with no
assumption of connectedness, bipartiteness, or regularity. It counts
distinct lengths of actual `SimpleGraph.Walk.IsCycle` witnesses.

## Unconditional endpoints

`JSP619.erdos_752_nat` proves the exact natural-number inequality
`k^s <= (24*192^s) * (cycleLengths G).card`.
`JSP619.erdos_752_explicit` proves its real-valued form.
`JSP619.erdos_752` quantifies over s first, then supplies a positive
constant and threshold uniformly over all finite nonempty simple graphs.

The intermediate `MooreBound` interface is proved as
`JSP619.mooreBound_proved` and instantiated in every endpoint. The final
theorems take no unproved Moore, expansion, path, core, or cycle hypothesis.

## Proof and attribution

The mathematics is known. The proof follows the expansion, BFS-layer,
and tree-return-path method of B. Sudakov and J. Verstraëte,
[*Cycle lengths in sparse graphs*](https://arxiv.org/abs/0707.2117),
Combinatorica 28 (2008), 357-372, Theorem 2.2, with weaker explicit
constants. The implementation uses edge-disjoint BFS bands, a proved
finite DFS argument, and explicit simple-path splicing. See
[PROOF.md](PROOF.md) for the full mathematical argument.

The authors' [addendum](https://people.math.ethz.ch/~sudakovb/addenda.pdf)
concerns the later theta-graph Lemma 2.4. This development uses neither
that lemma nor a claim about consecutive even cycle lengths.
The requested contribution is Lean formalization, not discovery of the
known theorem or an optimal constant.

## Source organization and reproduction

- `JSP619Moore`: high-girth path counting and the Moore bound.
- `JSP619ExpansionPath`: finite DFS and a long simple path.
- `JSP619LocalExpansion`: a proved minimum-degree core and small-set expansion.
- `JSP619CycleSplice`: actual simple-cycle construction and exact lengths.
- `JSP619Basic`, `JSP619CycleCore`: induced-graph counting and fan counting.
- `JSP619Layers`: BFS parents, ancestors, branch selection, equal-length returns.
- `JSP619Bands`: finite double counting and a dense band core.
- `JSP619Components`: connected-component reduction preserving degree.
- `JSP619Expansion`, `JSP619CycleExtraction`, `JSP619Assembly`: full assembly.
- `JSP619`, `Proof`: unconditional original-problem endpoints and axiom reports.

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. All transitive revisions are
fixed in `lake-manifest.json`. Run:

```sh
lake exe cache get
lake build
```

The independent package build and terminal axiom reports are recorded in
`verification/lake-build.log` and `verification/local-build.json`.
The local `lake build` passed with 8,720 jobs. A separate
`lake env lean Proof.lean` check also passed; all three endpoints depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

## Requested review and recipient

The reviewed catalog lists `Solved`, `Lean proof: No`, and
`Eligible to claim: No`. Please assess the formalization and eligibility;
this package does not change the catalog or assert an award.

Proposed formalization recipient: `RECIPIENT-JSP-000619-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a
self-submission with a direct interest in possible recognition. No
official verification, confirmed recipient, award, or payment is claimed.
Source code is licensed under Apache-2.0.
