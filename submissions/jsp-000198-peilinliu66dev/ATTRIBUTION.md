# Mathematical and code attribution

The complete package formalizes known mathematics. No new mathematical discovery or global formalization priority is claimed.

## Mathematical sources

- **Paul Erdős and George Szekeres:** the classical existence of arbitrarily large finite convex configurations in sufficiently large general-position planar sets. The added ES25 modules formalize a finite Ramsey route to a 25-point convex subset; they do not claim a new Erdős–Szekeres theorem or an efficient bound.
- **Heiko Harborth:** the exact empty-pentagon threshold g(5)=10 and its nine-point lower-bound configuration, *Elemente der Mathematik* 33 (1978), 116–118. The triangle and quadrilateral thresholds are classical elementary results. Their Lean proofs are reused from the small-k source below.
- **J. D. Horton:** [*Sets with No Empty Convex 7-Gons*](https://doi.org/10.4153/CMB-1983-077-8), *Canadian Mathematical Bulletin* 26(4) (1983), 482–484. The full k>=7 counterexample branch is his recursive construction.
- **Carlos M. Nicolás:** [*The Empty Hexagon Theorem*](https://doi.org/10.1007/s00454-007-1343-6), *Discrete & Computational Geometry* 38 (2007), 389–397. The new six-gon development follows his minimal-configuration and convex-layer argument, including the actual matching and coverage cases of Theorem 4.

The reused small-k development also includes the convex-pentagon selection result associated with Kalbfleisch, Kalbfleisch, and Stanton, using Bonnice's convex-layer proof. Its original module-level mathematical attribution is retained.

## Reused Lean sources

| Source | Fixed revision and scope | License |
|---|---|---|
| [CollinYuanjieRen/awards, small-k submission](https://github.com/CollinYuanjieRen/awards/tree/b8bb4f7803f921a7970abc880291ad9372111360/submissions/jsp-000198-smallk-cyr), [official PR #283](https://github.com/TheJustinSunPrize/awards/pull/283) | `b8bb4f7803f921a7970abc880291ad9372111360`; `EmptyPentagon/` definitions, convex-hull foundations, and complete exact k=3,4,5 proofs | MIT code permission explicitly applied by the submission README; retained in `EmptyPentagon/LICENSE` and `UPSTREAM.md` |
| [tester-lean/jsp-000198-horton-lean](https://github.com/tester-lean/jsp-000198-horton-lean/tree/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0), [official PR #73](https://github.com/TheJustinSunPrize/awards/pull/73) | `313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0`; `Prize/` geometry and all-N, all-k>=7 Horton counterexamples | MIT; retained in `Prize/LICENSE_MIT` |

These are substantial pre-existing formalizations. Their mathematical proof bodies and contributors are credited to the upstream projects. In particular, neither the small-k results nor the Horton Lean proof is represented as newly authored in this package. `EmptyPentagon/TriangleInterior.lean` itself credits reused Horton geometry; that attribution remains in place.

The small-k source targeted Lean 4.34.0-rc1 and the Horton source Lean 4.34.0. Both were compiled locally against Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The small-k port adapts a few renamed conditional-simplification APIs; the Horton proof bodies required no changes. Source headers, provenance files, and endpoint checks were added while preserving theorem meanings.

## Added formalization and integration

The new work comprises the explicit finite Ramsey/ES25 proof, the Nicolás convex-layer and empty-hexagon development, and the model and final-assembly bridges. These modules prove their finite selections, geometric configurations, and coverage statements rather than assuming abstract substitutes. Their role is to formalize and connect known mathematics.

The ES25 prerequisite, normalization, local geometry, three-layer finish, Cases II/I.C/I.B/I.A, and scope and model bridges have passed. The I.A proof supplies the internal adapter's parameter with actual geometric support and partial-cap counting, giving unconditional six-gon and original-model classification theorems. Finite sign certificates were discovered computationally and then proved by explicit ring identities and sign reasoning in Lean; no external solver result is assumed.

Codex and ChatGPT Pro assisted the new proof development, compatibility fixes, and documentation. The upstream small-k project's own account of its development assistance remains attributable to that project; importing its code does not transfer its authorship to the submitting account.

## Notices to retain

The full MIT notices accompany their respective code:

- `EmptyPentagon/LICENSE`: copyright 2026 The Justin Sun Prize contributors.
- `Prize/LICENSE_MIT`: copyright 2026 JSP-000198 formalization contributors.
- `LICENSE-NICOLAS` and applicable source notices: copyright 2026 JSP198 formalization contributors, with the individual module notices retained.

Upstream PR283 documentation is offered under CC BY 4.0. If its documentation is redistributed or adapted, preserve the author/source acknowledgment, license information, and identification of changes alongside it. These three publication documents are newly written summaries; they do not substitute for the original code notices and provenance records.

The intended submitting account and beneficiary is `peilinliu66-dev`. This is a self-submission seeking review of the formalization contribution and eligibility of this completed formalization; recognition remains for the project administrators to determine.
