# JSP-000636 / Erdős 776: the full multiplicity threshold

**Verification status: PASS.** The full all-parameter theorem and the independent package build have passed locally under the pinned environment. The final endpoints depend on the standard three logical axioms and 11 disclosed native-evaluation axioms; see the actual verification records below.

This development targets the complete threshold question in [Erdős Problem 776](https://www.erdosproblems.com/776), including both small parameters and the original exact-multiplicity convention. It extends and ports the existing MIT-licensed [mthiim formalization](https://github.com/mthiim/erdos_776/tree/1ca43203123642edaac45bf00b6fc333c848b4c9). The mathematics is known; the contribution submitted for consideration is formalization, integration, and version adaptation.

## Statement and scope

For an antichain \(\mathcal F\subseteq 2^{[n]}\), write \(L(\mathcal F)=\{|A|:A\in\mathcal F\}\). Let \(g(n,r)\) be the **maximum** of \(|L(\mathcal F)|\) over families with at least \(r\) members on every occupied level. For every integer \(r\ge2\), define

| Multiplicity | \(b(r)\) |
|---|---:|
| \(r=2\) | \(3\) |
| \(r=3\) | \(8\) |
| \(4\le r\le10\) | \(2r+4\) |
| \(r\ge11\) | \(2r+5\) |

The final endpoint characterizes **every** proposed cutoff \(N\in\mathbb N\):

\[
\left[\forall n>N,\quad g(n,r)=n-3\right]\quad\Longleftrightarrow\quad b(r)\le N.
\]

Thus \(b(r)\) is the least strict cutoff. The inequality is \(n>N\), not \(n\ge N\). The maximum is essential: \(g(3,2)=1\), although an empty family also realizes zero occupied levels. A separate endpoint proves the identical result when every occupied level has **exactly** \(r\) members, by constructing a subfamily that preserves all occupied levels. The result does not purport to compute every value of \(g\) below the cutoff.

```lean
theorem JSP636.erdos776 (r : ℕ) (hr : 2 ≤ r) (N : ℕ) :
    (∀ n : ℕ, N < n → JSP636.g n r = n - 3) ↔
      JSP636.thresholdFormula r ≤ N
```

`JSP636.erdos776_exactThreshold_iff` gives uniqueness of the least cutoff; `JSP636.erdos776_original_exact_multiplicity` covers the exact-multiplicity convention. `JSP636.g_eq_extremalOccupiedLevels` identifies the new maximum interface with the upstream maximum.

## Contents and attribution

- `Erdos776/`: the substantial existing \(r\ge4\) development by **mthiim and contributors**, fixed at `1ca43203123642edaac45bf00b6fc333c848b4c9`, with compatibility repairs and the finite-certificate changes described below.
- `JSP636UpperBound.lean` and `JSP636SmallParameters.lean`: the universal upper bound and complete \(r=2,3\) branches, using the mathematics of [Yixin He and Quanyu Tang](https://arxiv.org/html/2602.09803v2) and the proved upstream profile criterion.
- `JSP636Maximum.lean` and `JSP636ExactThreshold.lean`: finite maxima, levelwise thinning to exact multiplicity, and the uniform least-cutoff theorem.
- `JSP636.lean` / `Proof.lean`: final imports and endpoint checks.

See [PROOF.md](PROOF.md) for the mathematical connection and [ATTRIBUTION.md](ATTRIBUTION.md) for reuse and licensing. No new solution of a previously open mathematical problem, or global priority, is asserted.

## Verification and computational trust

| Check | Verified status |
|---|---|
| Upper bound, complete small-parameter module, maximum/exact-multiplicity bridge | PASS; checked endpoints use `propext`, `Classical.choice`, `Quot.sound` |
| Original finite certificates for \(r=4,\ldots,10\) and \(r=11,\ldots,28\) | PASS after replacement by kernel-checked proofs |
| Original lower-window table for \(r=29,\ldots,377\) | PASS in 11 `native_decide` groups, covering all 349 values |
| Final all-parameter dependency chain | **PASS** |
| Independent package build, source hash manifest, final endpoint axiom report | **PASS**; see [local build record](verification/local-build.json) |

The large table retains a **native-evaluation trust boundary**. Under Lean 4.33.1, each `native_decide` group introduces a generated native-evaluation axiom. One actual checked example is

```text
Erdos776.Uniform.lowerWindowNative285_certificate._native.native_decide.ax_1_1
```

The actual final endpoint dependency set is the standard three axioms **plus 11 generated native-evaluation axioms**, as recorded in the [terminal axiom report](verification/terminal-axioms.log). This is not a proof depending only on the standard three axioms, and the native computations are not ordinary kernel-reduced certificates. The unchanged finite Boolean checks are proved groupwise and combined by Lean range arguments. No new mathematical hypothesis is added.

A separate pure-kernel experiment successfully checked \(r=377\), but it is **not** the certificate for the full 349-value table and is not part of the final theorem's production dependency chain.

## Reproduction

Pinned environment: `leanprover/lean4:v4.33.1`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. From the completed package directory:

```text
lake exe cache get
lake build
lake env lean Proof.lean
```

The independent `lake build` and separate `lake env lean Proof.lean` both passed. All local proof modules were built from source with external `LEAN_PATH` removed; the pinned compiled Mathlib cache was reused. Records: [build log](verification/lake-build.log), [source hashes](verification/source-sha256.txt), [terminal axioms](verification/terminal-axioms.log), and [environment and command results](verification/local-build.json). These are local reproduction records, not organizer-designated independent verification.

## Review request

Submitting account and proposed beneficiary: **`peilinliu66-dev`** (`RECIPIENT-JSP-000636-PEILINLIU66DEV-A`). This is a self-submission, developed with Codex and ChatGPT Pro assistance. We request administrator review of the formalization, its disclosed reuse and computational trust boundary, and its eligibility for recognition. No award, eligibility determination, or payment is claimed.
