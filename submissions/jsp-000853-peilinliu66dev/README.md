# JSP-000853 / Erdős 1025: complete free-set asymptotic

This package formalizes the complete known order-of-magnitude answer to
[Erdős problem 1025](https://www.erdosproblems.com/1025), listed as
[JSP-000853](../../problems/catalog-0801-0900.md#jsp-000853).

## Statement correspondence

An admissible map sends each **unordered two-element subset** of an
`n`-element set to a member of that set outside the input pair.
A subset `S` is free when the image of every pair in `S` lies outside `S`.
The extremal function `g(n)` is the minimum, over all admissible maps,
of their maximum free-set size.

`PairMap`, `PairMap.Free`, `independenceNumber`, and `g` in `Proof.lean`
encode these definitions directly. Inputs have exactly two distinct elements;
there are no diagonal inputs and no ordered-pair asymmetry. The minimum's
domain is proved nonempty in the parameter range used below.

The principal theorem `Erdos1025.erdos_1025` proves

```lean
theorem erdos_1025 (n : ℕ) (hn : 9 ≤ n) :
    (1 / 4 : ℝ) * Real.sqrt n ≤ g n ∧
    (g n : ℝ) ≤ 4 * Real.sqrt n
```

Thus `g(n) = Θ(√n)`. Both bounds hold for every `n ≥ 9`, including
non-squares. This answers the original asymptotic question; no optimal
leading constant or exact formula is asserted.

The intermediate integer theorem `full_answer` gives
`Nat.sqrt n ≤ 2 * g n` and `g n ≤ 2 * (Nat.sqrt n + 1)`.

## Proof outline

For the lower bound, associate to each pair its union with its image, obtaining
at most `n.choose 2` triples. Exact incidence counting over all fixed-size
samples, followed by deletion of at most one vertex per contained triple,
produces a free set of size at least half the integer square root of `n`.

For the upper bound, embed the vertices into a square grid of side
`Nat.sqrt n + 1`. A suitable pair maps to its oriented corner if that corner
exists in the embedded vertex set; otherwise it maps to an arbitrary
nonendpoint. Every free set is covered by its row maxima and column maxima,
so has at most twice the grid side. This construction works on arbitrary
embedded subsets of the grid.

## Mathematical attribution

The mathematics is known. The lower-bound method is due to Spencer (1972),
*Turán's theorem for k-graphs*, Discrete Mathematics 2, 183–186.
The binary single-valued case was solved by Füredi (1991),
*Maximal Independent Subsets in Steiner Systems and in Planar Sets*,
SIAM Journal on Discrete Mathematics 4, 196–199.
The formalized grid argument follows the construction ideas in Section 2 of
[Conlon–Fox–Sudakov, *Short proofs of some extremal results II* (2016)](https://people.math.ethz.ch/~sudakovb/essays-in-combinatorics2.pdf),
which also acknowledges Füredi's earlier result. This submission requests
formalization credit, not discovery credit for the mathematical result.

## Reproduction

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. All transitive revisions
are fixed in `lake-manifest.json`.

From this directory with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
```

The last command also prints the principal theorem's axioms:
`[propext, Classical.choice, Quot.sound]`.
No `sorry`, custom axiom, `native_decide`, or external oracle is used.
The proof's SHA-256 and the local package build log are in `verification/`.
Local verification uses the pinned compiled Mathlib cache; it is not an
official prize verification or an independent rebuild of Mathlib.

## Submission and overlap disclosure

[PR #145](https://github.com/TheJustinSunPrize/awards/pull/145) already
submits a complete formalization of the same problem. This separately
developed implementation uses fixed-size sampling and the row/column-maxima
cover argument described above. It does not claim first submission,
exclusive priority, or an entitlement to an award.

The proposed formalization recipient is
`RECIPIENT-JSP-000853-PEILINLIU66DEV-A`, with public submitting account
`peilinliu66-dev`; recipient confirmation is pending. The applicant has a
direct interest in possible recognition. Codex and ChatGPT Pro assisted
development. Please assess whether this overlapping contribution qualifies
under the published rules. Source code is provided under Apache-2.0.
