# Verification of JSP-000137 / Erdős 131

## Fixed source

- Lean: `leanprover/lean4:v4.33.0`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Author proof: `theofilxeff/erdos_131@aeafec6479cf23b584a65fce6cb6dc1005be3b1f`.
- Generic proof dependencies: `plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Licensed helper source: `deancureton/MovingSofa@4d5569131940815f47a9ccf3e90a4c5043c56127`.

The source assembler checks the clean upstream checkouts and exact commit pins,
then applies the published adapters and hash-checked focused patches.
`ASSEMBLED_SOURCE_SHA256.json` identifies all 404 Lean files and the three
toolchain/project/dependency configuration files. A separately assembled tree
matched all 407 checked files byte for byte.

## Build and audit

On 2026-10-03, the clean full endpoint build completed with exit code 0:
4,101 Lake jobs, including fresh recompilation of all 401 local modules in
the endpoint dependency closure. The standalone `lake env lean Erdos131Audit.lean`
audit also returned exit code 0. Source hashes remained unchanged through
the clean rebuild. The pinned Mathlib dependency cache was reused.

The final literal target is
`Erdos131Research.OriginalStatement.original_growth` in `Erdos131Audit.lean`.
It imports the actual final proof and reproduces the arbitrary-nonempty-subset
definition and finite maximum, with definitional equality to the author source.
Its type has no additional premise.

The standalone audit reports precisely `propext`, `Classical.choice`, and
`Quot.sound` for each of these ten dependency closures:

1. `Nondividing.External.cfp_structure`
2. `Nondividing.External.discrete_john`
3. `Nondividing.External.zonotope_rounding`
4. `Nondividing.External.convex_density_set`
5. `Nondividing.External.blaschke_selection`
6. `Nondividing.External.convexBody_volume_tendsto`
7. `Nondividing.External.rogers_shephard`
8. `Nondividing.External.full_rank_lattice_points_le_volume`
9. `Nondividing.main_log_limit`
10. `Erdos131Research.OriginalStatement.original_growth`

Raw results and commands are in `BUILD_REPORT.json` and `verification/`.

## Reproduce

Acquire the fixed upstream sources separately, assemble the complete source
tree, and use the pinned toolchain:

```sh
git clone --filter=blob:none https://github.com/theofilxeff/erdos_131.git upstream-author
git -C upstream-author checkout --detach aeafec6479cf23b584a65fce6cb6dc1005be3b1f
git clone --filter=blob:none https://github.com/plby/lean-proofs.git upstream-plby
git -C upstream-plby checkout --detach 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
python integrate.py --author upstream-author --plby upstream-plby --output assembled
cd assembled
lake exe cache get $(cat MATHLIB_IMPORTS.txt)
lake build Erdos131Audit
lake env lean Erdos131Audit.lean
```

To repeat the clean project rebuild after an earlier build, run `lake clean`
before `lake build Erdos131Audit`. The recorded clean rebuild recompiled the
local proof dependency closure using the pinned Mathlib dependency cache.

The assembler performs source assembly only; it does not invoke the upstream
projects' setup hooks. The separately acquired author and generic dependency
sources retain their existing attribution and terms. See
`STATEMENT_AND_ATTRIBUTION.md` and `THIRD_PARTY/`.
