# JSP-000698 / Erdős 842: cycle-plus-triangles graphs

This package formalizes the complete three-colorability statement in
[Erdős problem 842](https://www.erdosproblems.com/842), catalogued as
[JSP-000698](../../problems/catalog-0601-0700.md#JSP-000698).

## Exact statement and correspondence

For every natural number n, every finite simple graph formed by the union
of a spanning Hamiltonian cycle and n vertex-disjoint triangles covering
all 3*n vertices has a proper coloring with three colors.

The terminal theorem `JSP698.erdos_842` takes a finite vertex type W, a
triangle enumeration `tri : (Fin n × Fin 3) ≃ W`, a cyclic enumeration
`ham : W ≃ Fin (3*n)`, and a simple graph G on W. The equivalence `tri`
means that each vertex belongs to exactly one of the n triples: these
are disjoint and cover all vertices. `CycleEdge ham u v` means that
u and v occupy cyclically consecutive positions in either direction;
`TriangleEdge tri u v` means that u and v are distinct vertices of the
same triple. The sole graph hypothesis is

    G.Adj u v -> CycleEdge ham u v or TriangleEdge tri u v.

Thus the theorem proves the result for the union itself and, more
generally, every subgraph of that union. The cycle and triangle edges
are allowed to overlap. No disjointness between those two edge families
is assumed. The output is Mathlib's `G.Colorable 3`, a proper coloring
by `Fin 3`; `JSP698.erdos_842_chromaticNumber_le` gives
`G.chromaticNumber <= 3`. Both results quantify over every n, including
n=0, which is treated as the empty graph. No parity, coefficient, or
transversal-count hypothesis remains in either terminal theorem.

## Proof outline

The proof follows the finite algebraic approach of Petrov. There is one
variable per vertex and one binomial factor per cycle-edge copy and
triangle-edge copy. Repeated underlying edges retain their separate
factors. The complete edge-polynomial expansion is proved explicitly.
For each triangle, a monomial term determines a chord between two of its
vertices and an orientation. A fixed finite balance table identifies
exactly which terms contribute to the central monomial, with exponent
two at every vertex.

The chord-crossing matrix is constructed from the finite cyclic order.
Its symmetry, zero diagonal, and even cross-block sums are proved from
the endpoint definitions. An algebraic odd-transversal theorem then
shows that the number of choices of one chord from each triangle whose
induced crossing degrees are all even is odd. The theorem is proved in
the package for arbitrary finite odd-sized blocks and is applied here
with blocks of size three.

For each such chord choice, the cycle balance equations have exactly two
complementary binary states. Their integer signs agree. Pairing them
and using the odd transversal count proves that the central coefficient
of the actual edge polynomial is congruent to 2 modulo 4. It is therefore
nonzero. The polynomial bridge invokes Mathlib's proved combinatorial
Nullstellensatz, with the degree bound established for the actual edge
polynomial, to obtain a proper three-coloring. Finally the coloring is
transported through the arbitrary triangle and Hamiltonian enumerations.

## Files and reproduction

- `JSP698OddTransversal.lean`: the finite odd-transversal parity theorem.
- `JSP698PolynomialBridge.lean`: the nonzero-coefficient-to-coloring bridge.
- `JSP698ChordCoefficient.lean`: the exact polynomial expansion, concrete
  chord matrix, binary-state pairing, coefficient congruence, and full
  original-graph theorem.
- `Proof.lean`: imports the complete result and prints terminal axioms.

Lean is pinned to `leanprover/lean4:v4.33.1`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and all transitive dependencies
are fixed in `lake-manifest.json`. From this package directory run:

```sh
lake exe cache get
lake build
```

Local `lake build` passed on 2026-09-17. The central-coefficient theorem
and both original-problem terminal theorems report only
`[propext, Classical.choice, Quot.sound]`. No source uses `sorry`, `admit`,
additional axioms, or `native_decide`. The build reused the pinned
compiled Mathlib cache; all package proof modules were built from source.
See `verification/lake-build.log`, `verification/local-build.json`, and
`verification/source-sha256.txt`. These are local reproduction records,
not official prize verification.

## Attribution and prior work

The mathematical theorem was proved by Herbert Fleischner and Michael
Stiebitz in [A solution to a colouring problem of P. Erdős](https://doi.org/10.1016/0012-365X(92)90588-7),
Discrete Mathematics (1992), 39-48. The parity and coefficient route used
here follows Fedor Petrov,
[General Parity Result and Cycle-plus-Triangles Graphs](https://arxiv.org/abs/1512.06205)
(2015). This submission claims the Lean formalization and its explicit
correspondence to the complete statement, not discovery of the known
mathematical theorem.

A bounded search on 2026-09-17 at approximately 04:55 UTC inspected
478 public official Issue/PR titles and bodies through #479 and found
no matching JSP-000698 / Erdős 842 submission. Three broader topic hits
concerned other problems. One focused GitHub code search for the original
problem URL in Lean files returned zero matches. See [novelty.md](novelty.md)
for scope and exclusions. This does not establish global priority.

The reviewed catalog lists `Solved`, `Lean proof: No`, and
`Eligible to claim: No`. This submission requests assessment of the
formalization and eligibility under the published rules.

Proposed formalization recipient: `RECIPIENT-JSP-000698-PEILINLIU66DEV-A`.
Public submitting account: `peilinliu66-dev`; identity confirmation is
pending. Codex and ChatGPT Pro assisted development. This is a self-submission
with a direct interest in possible recognition. No official verification,
award decision, or payment is asserted. Source code is under Apache-2.0.
