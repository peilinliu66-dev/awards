# Sources, reuse, and licensing

This package combines an existing Lean proof for \(r\ge4\) with new formalization of the small parameters and a uniform interface for the actual maximum and strict least cutoff. It does not claim a new mathematical solution or global formalization priority.

## Mathematical sources

1. [Erdős Problem 776](https://www.erdosproblems.com/776), the threshold problem for antichains with a prescribed multiplicity on each occupied level.
2. **Yixin He and Quanyu Tang**, *An Erdős–Trotter problem on antichains with multiplicity r on each occurring level*, [arXiv:2602.09803v2](https://arxiv.org/html/2602.09803v2), 21 March 2026. The problem convention, small-parameter values, and universal upper-bound argument are the relevant mathematical inputs; see the initial definitions and remarks, Lemma 2.5, and Appendix A. This paper is already cited by the award catalog.
3. **mthiim and contributors**, [`mthiim/erdos_776`](https://github.com/mthiim/erdos_776/tree/1ca43203123642edaac45bf00b6fc333c848b4c9), fixed commit **`1ca43203123642edaac45bf00b6fc333c848b4c9`**. This supplies the complete \(r\ge4\) exact-threshold proof and its substantial Lean implementation, including the combinatorial and computational foundations. That proof is credited to its existing authors.

## Code reused and work added

| Part | Origin and changes |
|---|---|
| `Erdos776/` core | Copied from the fixed mthiim commit under MIT. Ported from the original Lean/Mathlib 4.30.0 environment to the pinned 4.33.1 environment, with API and elaboration repairs. The underlying theorem statements are preserved. |
| `Erdos776.Uniform.ProblemDefinitions` | Definitions extracted from the upstream problem interface to permit small-parameter modules to depend on the definitions without importing the final large certificate. These are reused definitions. |
| Two smaller finite certificates | Existing Boolean statements retained; their former native computations replaced by ordinary kernel-checked proofs. |
| Lower-window certificate, \(r=29,\ldots,377\) | Existing Boolean statement retained and split into 11 native-evaluated groups with a proved range-combination bridge. This still relies on native evaluation and its generated axioms. |
| `JSP636UpperBound` | New Lean proof of the known uniform occupied-level upper bound. |
| `JSP636SmallParameters` | New Lean formalization of the complete \(r=2,3\) branches, using the known mathematics and upstream proved profile/construction machinery. |
| `JSP636Maximum` | New interface for the finite maximum, proved equal to the upstream maximum; constructive thinning from at-least to exact multiplicity. The existence of an upstream maximum definition is explicitly acknowledged. |
| `JSP636ExactThreshold`, `JSP636`, `Proof` | Uniform all-parameter/all-cutoff statements, integration, and endpoint checks; the final assembled theorem and independent package build passed locally. |

Codex and ChatGPT Pro assisted with proof development, source adaptation, finite-certificate engineering, and documentation. This does not transfer authorship of the reused core or the mathematical sources to the submitting account.

## License and computational boundary

The upstream project is [MIT licensed](https://github.com/mthiim/erdos_776/blob/1ca43203123642edaac45bf00b6fc333c848b4c9/LICENSE), with the notice:

```text
Copyright (c) 2026 mthiim and contributors
```

The full notice and permission text must accompany the copied and modified source; retain `LICENSE` and `LICENSE-JSP636-MIT.txt` in the final package. New extension code is supplied under MIT, with the upstream attribution preserved. The target environment is Lean `4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The 11 production `native_decide` groups are not represented as pure-kernel certificates. Each generates a native-evaluation axiom under the target Lean version. The [final endpoint report](verification/terminal-axioms.log) lists the standard three axioms and 11 such generated axioms. The independent package build and separate endpoint check both passed; see the [build record](verification/local-build.json). The separately verified pure-kernel \(r=377\) performance probe is outside the production theorem dependency chain and does not certify the other 348 table values.

Submitting account and proposed beneficiary: **`peilinliu66-dev`**. This is a self-submission requesting administrator review of the formalization contribution, attribution, computational trust boundary, and eligibility; it does not assert an award or recognition decision.
