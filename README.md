# Erdős 524: compiled lower and upper envelopes

Status: **MAIN THEOREMS COMPILED AND AXIOM-AUDITED** (4 October 2026).

For independent uniform signs omega_i, define

    P_N(x) = sum_(i=0)^N omega_i x^i,
    M_N = sup_(x in [-1,1]) |P_N(x)|.

The constant coefficient is included. `Erdos524.erdos_524` proves, jointly
almost surely over the full integer sequence,

    liminf_N log(M_N/sqrt(N)) / (log log N)^(1/3)
        = -(3*pi^2/4)^(1/3),
    limsup_N M_N/sqrt(N log log N) = sqrt(2).

The public statement is in `Erdos524/Main.lean`. `littlewoodPolynomial` uses
exactly `sum i in Finset.range (N+1), omega i * x^i`; `littlewoodMaximum` is
its continuous-map supremum norm on the compact interval [-1,1]. The measure
is the actual infinite product of the law assigning probability one-half to
each of -1 and +1.

`Erdos524.erdos_524_of_independent_signs` transfers these original endpoints to
any probability space with a measurable independent sequence whose individual
laws are the stated uniform sign law. The transfer is proved from the actual
sequence law, not assumed as an extra theorem.

## Stronger inverse normalization

`Erdos524.erdos_524_inverse_refinement` additionally proves

    liminf_N M_N / [sqrt(N) F^-1(1/sqrt(log N))] = 1,

where this formalization defines F directly as the infimum of all nonempty
finite centered Gaussian box probabilities with covariance

    K_0(u,v) = integral_(s=0)^1 exp(-(u+v)s) ds,  u,v >= 0.

The tuples may include zero, repeated or unordered points. The formal proof
establishes positivity, continuity, strict increase, both endpoint limits, the
unique inverse on (0,1), and

    log F(exp(-L)) / L^3 -> -2/(3*pi^2).

No Brownian-path construction, Itô-integral existence, or independently
formalized identification with an Itô-integral distribution is claimed. The
original logarithmic and upper-envelope theorem above is unconditional and
does not require such an identification. `Erdos524.erdos_524_complete` combines
the two original endpoints and this finite-covariance inverse refinement.

## What is proved in the dependency chain

- Finite Anderson comparison for actual Gaussian measures, including singular
  linear images, via coordinate symmetrization, fiber volume and layer-cake.
- Cauchy determinants, positive definiteness, inverse diagonals, explicit rational
  interpolation and exact Gaussian regression/residual laws.
- The exact finite-[0,1] Laplace covariance and PSD cutoff/domination estimates.
- The sharp two-sided finite Gaussian small-ball estimate, with all mesh,
  potential, residual, sample-box and scalar budgets discharged.
- Fourth-order finite Rademacher/Gaussian replacement and actual polynomial CDF
  comparisons; odd/even phase independence; finite step-kernel Gram coupling.
- Actual all-interval polynomial tails and finite Gaussian grid interpolation,
  giving full polynomial upper and lower probability comparisons with F.
- Quantitative F dilation and inverse-scale probability margins, with a proved
  finite Gaussian likelihood-ratio argument instead of a Gaussian B axiom.
- The actual infinite-sign model, finite marginal laws, fresh-block independence
  and exact polynomial/norm splitting.
- Factorial-square sparse blocks, adaptive even dyadic dense blocks, summable
  error budgets, both Borel–Cantelli directions and all-integer interpolation.
- Sharp sign-walk maximal concentration, Gaussian moderate tails, independent
  geometric blocks, and both directions of the upper envelope.
- The original constant coefficient, index convention, diverging normalizations
  and the conversion from sqrt(2N log log N) to the stated sqrt(2) constant.

The smoothing error uses a proved universal cutoff-derivative constant C and
(75/6)*C*b^3/(N*eta^4). The ordinary exposition uses different numerical
constants. No equality between those presentations' constants is asserted;
the formal asymptotic arguments discharge the actual implemented constants.

## Exact environment and reproduction

- Lean: `leanprover/lean4:v4.35.0-rc3`
- Compiler commit: `470d5ce1400764999581fd26d5d72b00d990b0f4`
- Mathlib: `119fab72f5ecf69de785450dfb8f8b58ca5f310e`
- Full dependency pins: `lake-manifest.json`

With the pinned official Lean/Lake toolchain available:

    lake exe cache get
    lake build Erdos524
    lake env lean FinalTheoremAudit.lean
    lake env lean StatementCheck.lean
    lake env lean InverseLiminfAudit.lean
    lake env lean ConstantTermAudit.lean
    lake env lean LogarithmicLiminfAudit.lean
    lake env lean Erdos524/UpperEnvelopeLowerAudit.lean
    lake env lean Erdos524/ArbitrarySignModelAudit.lean

Run the other included `*Audit.lean` files to inspect supporting endpoints.
The fresh final build recompiles this project's own sources. The official
Mathlib/dependency caches may be reused; this is not a source rebuild of all
Mathlib or an independent implementation of Lean's kernel.

The separately spelled-out `StatementCheck.lean` verifies the original probability
measure, coefficient indexing, full interval and both constants by elaborating
directly against the public theorem. This is a specification self-check.

Every audited endpoint reports only
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or new
mathematical `axiom` declarations occur in the included project sources.
`VERIFICATION.json` records the exact included source set and audit outputs;
`SHA256SUMS.txt` identifies the source/evidence files. Build logs and official
toolchain provenance are in `build-evidence/`.

## Additional proof-certificate validation

Nanoda 0.4.17 checked the exported dependency closure of
`Erdos524.erdos_524_complete`: **69,909 declarations, no errors, exit code0**.
The configuration permits exactly propext, Classical.choice and Quot.sound,
and treats any other axiom as a hard error. The source build and this separate
checker run are distinct validations; neither is an external mathematical
peer-review attestation.

The proof export is 553,361,464 bytes, SHA256
`80b02f10e90517201fac59831d958ba60b3877322a3d77ab2ac4866499db7338`.
It is deliberately not bundled. Its export command, tiny checker log, logical
configuration and printed target are included in `build-evidence/`. Configuration
file paths are normalized to relative paths for reproduction; settings are
otherwise unchanged. With the corresponding export/checker tools on PATH:

    lake env leanexport Erdos524.Main -- Erdos524.erdos_524_complete > build-evidence/main-proof.export.jsonl
    touch build-evidence/nanoda-target.txt
    (cd build-evidence && nanoda_bin nanoda-config.json)

A fresh whole-import Lean kernel replay of `Erdos524.Main` also completed
successfully: exit code 0, 660.69 seconds. This is the official Lean checker,
separate from the independent Nanoda check above. The exact command and result
are in `build-evidence/kernel-replay-result.json`:

    lake env leanchecker --fresh --verbose Erdos524.Main

## Mathematical sources and scope

Formalization attribution: AI-assisted formalization prepared under the direction
of the submitting account peilinliu66-dev. Mathematical authorship is credited
separately below.

- Brayden Letwin and Mehtaab Sawhney, *On the maxima of Littlewood polynomials
  on [-1,1]*, arXiv:2604.19294v1, Theorem 1.1:
  https://arxiv.org/html/2604.19294v1
- The upper envelope is attributed to Salem and Zygmund in that primary source.
- The original Erdős question is on printed page 253 of *Some unsolved problems*
  (1961): https://renyi.hu/~p_erdos/1961-22.pdf
- Anderson, Steiner symmetrization, Cauchy determinants and Gaussian regression
  are classical ingredients. Lean and Mathlib contributors supply the imported
  formal foundations and APIs.

`MathematicalProof.txt` preserves the analytic proof exposition. Its opening
status describes the current implementation; historical implementation remarks
inside the unchanged exposition are not the build-status authority.

This is a formal recovery of known mathematics. Compilation does not establish
first-global formalization priority, official prize eligibility, acceptance or
an award. Those require the separate catalog/scope/duplicate review.
