# JSP-000420 / Erdős 524: submission overlap check

Checked 2026-10-04, approximately 14:46–14:50 UTC. This is a bounded public-source check, not a guarantee that no other formalization exists.

- The current official catalog describes the random-sign polynomial maximum and still records Open / Lean proof No. JSP identifiers are not Erdős problem numbers.
- Awards PRs #4292 and #3804 explicitly identify JSP-000420 as Erdős #420. The latter lists prime/arithmetic component statements. These do not establish the random-polynomial theorem. PR #3683 links the same `Erdos420.lean` source.
- Awards PR #3169 claims a formalization of Erdős #524 while naming JSP-000524. Its cited `plby/lean-proofs` path `src/latest/ErdosProblems/Erdos524.lean` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` returned HTTP 404 on this check. A missing cited file does not establish a complete prior proof.
- `rjwalters/lean-genius`, `proofs/Proofs/Erdos524Problem.lean`, current blob `008a2a7cab0b3879372540b83ca4121d6a905410`, contains `axiom erdos_524_main : erdos_524_order_of_magnitude`.
- `daedalus/alphaproof-nexus`, `problems/erdos/524/Erdos524.lean`, current blob `a6a4f2fd39e0f4c8ac4e3298e0179aa3cd41c2fc`, contains an empty EVOLVE block and no theorem proving the envelopes.
- `ryantuck/erdos-ai`, `deepmind/deepmind/524.lean`, current blob `934feece150e26389dd116faf4d059a40d40d7bb`, has `sorry` in the main and lower/upper-bound statements.
- No existing PR by `peilinliu66-dev` for JSP-000420 was returned by the submission search.

The analytic result is already public: Brayden Letwin and Mehtaab Sawhney, *On the maxima of Littlewood polynomials on [-1,1]*, arXiv:2604.19294v1, 21 April 2026, Theorems 1.1 and 1.2 and equation (1.1). The submission must credit that work and the Salem–Zygmund upper envelope, and claim the present AI-assisted formalization only. No mathematical novelty, global formalization priority, official verification, or award entitlement is asserted.

References:
- https://github.com/TheJustinSunPrize/awards/blob/e9e118d00022d693151d87af0c69d180dc5e5efd/problems/catalog-0401-0500.md#JSP-000420
- https://github.com/TheJustinSunPrize/awards/pull/4292
- https://github.com/TheJustinSunPrize/awards/pull/3804
- https://github.com/TheJustinSunPrize/awards/pull/3683
- https://github.com/TheJustinSunPrize/awards/pull/3169
- https://arxiv.org/html/2604.19294v1
