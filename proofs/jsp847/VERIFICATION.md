# Reproduction and verification

Verification date: 2026-10-03 UTC.

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Complete transitive dependency revisions: [lake-manifest.json](lake-manifest.json).
- Source checksums: [SOURCE_SHA256SUMS.txt](SOURCE_SHA256SUMS.txt).

Use the published proof branch and the full 40-character commit named in the contribution PR. From this project directory, with the pinned Lean toolchain installed:

```bash
sha256sum -c SOURCE_SHA256SUMS.txt
lean --version
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LEAN_NUM_THREADS=2
lake update
mapfile -t imports < mathlib-imports.txt
lake exe cache get "${imports[@]}"
lake clean
lake build
lake env lean Audit.lean
```

The source checksum check is made before setup. The tracked manifest records all dependency commits; setup should preserve those revisions. The selected cache command obtains Mathlib imports and their transitive dependencies. A full Mathlib cache is also compatible but unnecessary.

## Recorded result

- All 23 project modules were freshly compiled after clearing the project build products.
- `lake build`: exit 0. [Complete clean-build log](logs/build-clean.log).
- `lake env lean Audit.lean`: exit 0. [Complete type and axiom audit](logs/audit-final.log).
- There are 24 Lean source files: the 23 built modules and the separately checked audit entry.
- Mathlib dependencies used the pinned cache. The clean-build claim is for all project modules, not a cold recompilation of every Mathlib dependency.

The audit prints the concrete partition type, the complete target types, and the axiom dependencies of:

```
Erdos1017.exists_weighted_partition
Erdos1017.exists_partition_dense_saving
Erdos1017.uniform_integer_dense_saving
```

Each reports exactly:

```
[propext, Classical.choice, Quot.sound]
```

No target depends on `sorryAx` or a newly postulated theorem. The source audit found no `sorry`, `admit`, added axioms, `unsafe`, or `native_decide` proof shortcuts. Build warnings are recorded in the log.

The publication copy preserves all verified Lean, toolchain, and manifest bytes. Documentation was prepared for publication after verification; it does not change the checked statements or proof terms. Machine-readable results are in [verification-summary.json](verification-summary.json).
