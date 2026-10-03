# JSP137 / Erdős 131: compiled source completion

This package completes the eight external inputs of Theofil Xeff's pinned
projective proof and connects them to the literal original growth theorem.
The mathematical argument and exponent are attributed to Theofil Xeff; the
generic CFP/PZ/John geometry is attributed to its separately acquired sources.

Endpoint: `Erdos131Research.OriginalStatement.original_growth`. It proves
`log F(N) / log N → 1/5`, with F the maximum cardinality in [1,N] and the
condition forbidding divisibility by every nonempty subset of the other
elements. No fixed-k restriction or extra structural premise is introduced.

See BUILD_REPORT.json for final clean-build status, exact commands, and
verification. The required ten axiom closures contain only `propext`,
`Classical.choice`, and `Quot.sound`; raw logs are supplied under verification/.

## Reproduce

Acquire clean checkouts separately, without running upstream setup scripts:

    git clone --filter=blob:none https://github.com/theofilxeff/erdos_131.git upstream-author
    git -C upstream-author checkout --detach aeafec6479cf23b584a65fce6cb6dc1005be3b1f
    git clone --filter=blob:none https://github.com/plby/lean-proofs.git upstream-plby
    git -C upstream-plby checkout --detach 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
    python integrate.py --author upstream-author --plby upstream-plby --output assembled
    cd assembled
    lake exe cache get $(cat MATHLIB_IMPORTS.txt)
    lake build Erdos131Audit
    lake env lean Erdos131Audit.lean

The fixed toolchain is Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17.
Mathlib is pinned to db584cd6d46c92f209a44c0f1c829460d327499d; all transitive
package revisions are locked in lake-manifest.json. The original author's
repository used Lean 4.32.0. This adapter project's stated 4.33.0 pin is retained.

The assembler verifies both source commits and clean tracked trees, applies
the original integration changes, then hash-checked compiler repairs. It
performs source assembly only. It does not compile, download, or publish.
COMPILATION_PATCHES.diff is the reviewable patch to separately acquired source.

## Scope and licensing

The author's repository has no license in the inspected pinned tree; its
complete proof source is deliberately excluded from this redistributable
package and must be acquired separately. The generic plby closure is also
acquired separately. The archive contains 19 adapter/helper/overlay Lean
files, source acquisition/assembly code, focused patches, notices, and
verification records. It does not relicense upstream source.

Discrete John explicitly requires a nonempty convex body; all three actual
uses discharge that premise. The difference-body estimate uses a proved
positive dimension-only constant rather than claiming the sharp binomial
constant. Neither adjustment weakens the final theorem.

See `VERIFICATION.md` for the checked dependency closures and `STATEMENT_AND_ATTRIBUTION.md` for the exact statement, source correspondence and contribution roles.
