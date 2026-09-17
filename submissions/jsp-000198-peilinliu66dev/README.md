# JSP-000198 / Erdős 216: empty convex polygon thresholds

Complete Lean formalization of the finite-threshold classification for [Erdős Problem 216](https://www.erdosproblems.com/216), with exact small thresholds and a proved finite empty-hexagon bound. Independent package build and the unconditional endpoint axiom checks passed.

| Polygon size | Proved statement |
|---|---|
| k=3 | g(3)=3 |
| k=4 | g(4)=5 |
| k=5 | g(5)=10 |
| k=6 | A least threshold g6 exists and g6<=B |
| Every k>=7 | For every N there is an N-point general-position counterexample, with integer coordinates |

Here B=`Horton.es25Bound` is the explicit finite number T(50), where T(0)=0 and T(t+1)=2^(2*T(t)). This proves finiteness for six-gons; it does not establish the sharp numerical value g(6)=30. For every k>=3, a finite threshold exists if and only if k<=6.

The original model `Prize.Geometry.ForcesEmptyKGon N k` quantifies over all sets with **at least N points**. Convexity and emptiness use the actual convex hull and its topological interior. `ModelBridge.lean` proves equivalence with the reused orientation-based, exactly-N model.

## Entry points and reproduction

- `JSP198.FinalAssembly.erdos216_classification`: all five rows in one theorem.
- `JSP198.FinalAssembly.original_six_threshold`: a true least six-gon threshold.
- `JSP198.FinalAssembly.finite_threshold_iff`: finiteness exactly for k<=6.
- `JSP198.FinalAssembly.remainingCaseIACore`: the formerly separate I.A obligation is now proved, not supplied by the user.

These declarations are in `FinalClassification.lean` and `JSP198NicolasCaseIAComplete.lean`; `Proof.lean` imports and checks the unconditional endpoints. The internal conditional assembly is instantiated by a complete proof and introduces no remaining mathematical assumption.

```text
lake exe cache get
lake build
lake env lean Proof.lean
```

Pinned Lean: `leanprover/lean4:v4.33.1`. Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`, with pinned transitive dependencies.

The independent package build passed (8804 jobs). Its proof modules were compiled from source, with external `LEAN_PATH` removed and the pinned Mathlib cache reused. Separate final endpoint checks report exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no native-evaluation or assumed SAT-unsatisfiability axioms. SAT was used only to discover finite sign certificates; each certificate is proved by explicit field identities and sign case splits inside Lean.

See `verification/final-build.json`, `verification/final-build.log`, `verification/final-axioms.log`, and `source-manifest.json`. Earlier preparation logs are retained as history and are superseded by the final records. These are local reproduction records, not organizer-designated independent review.

## Proof and attribution

[PROOF.md](PROOF.md) describes the complete argument. It combines a finite Ramsey/convex-25 theorem, a minimal convex-layer reduction, and the full Nicolás case analysis. In I.A the actual sampled replacement has k+4 vertices, minimality forces at least k+5 deleted outer vertices, and the proved local cover bounds that number by k+4.

The mathematics is known. Substantial MIT-licensed small-k Lean proofs are reused from [CollinYuanjieRen/awards](https://github.com/CollinYuanjieRen/awards/tree/b8bb4f7803f921a7970abc880291ad9372111360/submissions/jsp-000198-smallk-cyr), and all-k>=7 proofs from [tester-lean/jsp-000198-horton-lean](https://github.com/tester-lean/jsp-000198-horton-lean/tree/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0). Their notices and attribution are retained.

The added work formalizes the classical Erdős–Szekeres/Nicolás six-gon route, ports the reused developments, and connects all branches and models. See [ATTRIBUTION.md](ATTRIBUTION.md) for mathematical sources, exact revisions and licenses. No new mathematical discovery or global priority is claimed. Codex and ChatGPT Pro assisted development.

Submitting account and proposed formalization recipient: `peilinliu66-dev`. This self-submission requests administrator review of attribution and reward eligibility; no award or payment is asserted.
