# JSP-000137 / Erdős 131: non-dividing sets

This document fixes the mathematical scope and attribution for the verified
source-completion package. The clean rebuild and all ten dependency-closure
audits passed; see `VERIFICATION.md` and `BUILD_REPORT.json`.

## Exact statement

A finite set A of positive integers is non-dividing when, for every a in A and
every nonempty subset S of A excluding a, the integer a does not divide the
sum of S. Let F(N) be the maximum size of such a set contained in {1,…,N}.

The endpoint is

```
lim_(N→∞) log(F(N))/log(N) = 1/5.
```

It is represented by `Nondividing.main_log_limit` and by the separately stated
`Erdos131Research.OriginalStatement.original_growth` in `Erdos131Audit.lean`.
The latter repeats the literal finite-set definition and proves definitional
equality with the imported statement. The target uses all nonempty subsets,
not a fixed number of summands. No external structural or geometric hypothesis
appears in its type.

Original scope references:

- P. Erdős (1975), printed p. 309, [original article](https://www.numdam.org/article/AST_1975__24-25__295_0.pdf).
- P. Erdős, V. Lev, G. Rauzy, C. Sándor and A. Sárközy, *Greedy algorithm,
  arithmetic progressions, subset sums and divisibility*, Discrete Mathematics
  200 (1999), 119–135, Property Q, p. 6 of the
  [author's source](https://math.haifa.ac.il/seva/Papers/greeda.dvi),
  [DOI](https://doi.org/10.1016/S0012-365X(98)00385-9).

## Mathematical proof

The projective normalization and matching exponent are attributed to Theofil
Xeff's *A Projective Approach to Non-Dividing Sets*, in the
[pinned manuscript](https://github.com/theofilxeff/erdos_131/blob/aeafec6479cf23b584a65fce6cb6dc1005be3b1f/Manuscript.tex).
The repository version is dated 2026-07-24. The manuscript records AI assistance
and credits GPT-5.6 Sol for the projective idea.

The argument first reduces to a dyadic shell, then normalizes integer vectors
by the linear functional encoding divisibility. This lowers the convex
geometric dimension by one while retaining the relevant divisibility
relations. The projective density increment and descent yield the exponent
1/5, together with the matching lower bound.

Underlying mathematical sources include Conlon–Fox–Pham,
[*Homogeneous structures in subset sums and non-averaging sets*](https://arxiv.org/abs/2311.01416),
and Pham–Zakharov,
[*Sharp bound for the Erdős–Straus non-averaging set problem*](https://doi.org/10.1007/s00039-025-00728-8).

## Formalization contributions

- **Theofil Xeff / theofilxeff:** the original `Nondividing` project, including
  projective normalization, density increment, descent, and final growth
  assembly, pinned to `aeafec6479cf23b584a65fce6cb6dc1005be3b1f`.
- **peilinliu66-dev, with AI assistance:** proof adapters for the eight external
  interfaces; compatibility of the generalized arithmetic progression and
  scale conventions; the nonempty-body repair at the actual John-theorem
  call sites; the sufficient positive dimension constant for difference-body
  volume; the original-scope audit and reproducible integration package.
- **plby/lean-proofs contributors, as named in the source headers:** the
  separately pinned generic CFP, Pham–Zakharov, discrete-John, and zonotope
  proof dependencies at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- **deancureton/MovingSofa contributors:** the Apache-2.0 compact-convex
  helper sources adapted from `4d5569131940815f47a9ccf3e90a4c5043c56127`;
  the source notices and license are retained under `THIRD_PARTY/`.

The integration retrieves the two upstream projects separately at their exact
commits and applies the published adapters and focused changes. Their original
source attribution and terms are retained. The public adapter package contains
the original contribution and the licensed helper extracts, with source hashes
identifying the assembled version checked by Lean.

## External inputs replaced

The verification entry checks the actual dependency closures of convex density,
discrete John, Blaschke selection, convex-body volume continuity, full-rank
lattice counting, CFP structure, zonotope rounding, and the difference-body
volume bound, followed by both final growth endpoints.

Two deliberate interface choices preserve the final scope: the nonempty-body
hypothesis is proved at every affected call site, and the descent uses a proved
positive dimension-dependent volume constant. The latter does not assert the
sharp Rogers–Shephard binomial constant. Neither change adds a premise to the
growth theorem.

## Relevant catalog submissions

[PR #4616](https://github.com/TheJustinSunPrize/awards/pull/4616) proves a
seven-element example for two summands in [1,30].
[PR #2103](https://github.com/TheJustinSunPrize/awards/pull/2103) identifies its
result as a numerical component. The present endpoint is the unrestricted
growth limit for the original arbitrary-subset property.
