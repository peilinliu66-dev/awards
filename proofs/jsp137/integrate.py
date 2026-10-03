#!/usr/bin/env python3
"""Assemble source only from separately obtained pinned checkouts.

This script never compiles Lean, runs Lake, downloads, or publishes anything.
The separately obtained author's proof is deliberately not redistributed here.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
from apply_compilation_patches import apply_compilation_patches

AUTHOR_COMMIT = "aeafec6479cf23b584a65fce6cb6dc1005be3b1f"
PLBY_COMMIT = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
MATHLIB_COMMIT = "db584cd6d46c92f209a44c0f1c829460d327499d"


def replace_exact(text: str, old: str, new: str, count: int = 1) -> str:
    actual = text.count(old)
    if actual != count:
        raise ValueError(f"Expected {count} occurrence(s), found {actual}: {old!r}")
    return text.replace(old, new)


def patch_author_source(relative: str, text: str) -> str:
    """Only the three discharged nonempty premises and dimension constants."""
    if relative in ("Nondividing/CapConeVolume.lean", "Nondividing/IrredIncrement.lean"):
        count = 4 if relative.endswith("CapConeVolume.lean") else 1
        text = replace_exact(text, "Nat.choose (2 * d) d",
                             "Erdos131Research.rogersConstant d", count)
        text = replace_exact(text,
            "have hbinom_pos : 0 < binom := Nat.choose_pos (by omega)",
            "have hbinom_pos : 0 < binom := Erdos131Research.rogersConstant_pos d")
    if relative == "Nondividing/Geometry/ConvexLatticeJohn.lean":
        text = replace_exact(text,
            "hdim (sectionBody_isCompact H M) (sectionBody_convex H M)\n",
            "hdim (sectionBody_isCompact H M) (sectionBody_convex H M)\n"
            "      (by\n"
            "        refine ⟨0, ?_⟩\n"
            "        change (0 : Fin d → ℝ) ∈ realCoordinateBox M ∧ (0 : Fin d → ℝ) ∈ H\n"
            "        exact ⟨by simp [mem_realCoordinateBox], H.zero_mem⟩)\n")
    if relative == "Nondividing/Geometry/SlabVolume.lean":
        text = replace_exact(text,
            "hE2 (Module.finrank ℝ H) H K S rfl hcompact hconvex hsymmK hKH hzK rfl",
            "hE2 (Module.finrank ℝ H) H K S rfl hcompact hconvex\n"
            "      (by\n"
            "        refine ⟨0, ?_⟩\n"
            "        change (0 : Fin d → ℝ) ∈ slabBody N a hτw ∧ (0 : Fin d → ℝ) ∈ H\n"
            "        exact ⟨by simp [mem_slabBody, realBox, hτw], H.zero_mem⟩)\n"
            "      hsymmK hKH hzK rfl")
    if relative == "Nondividing/IrredIncrement.lean":
        text = replace_exact(text,
            "hjohn d ⊤ (Kd : Set (Fin d → ℝ)) A hfr Kd.isCompact Kd.convex\n",
            "hjohn d ⊤ (Kd : Set (Fin d → ℝ)) A hfr Kd.isCompact Kd.convex Kd.nonempty\n")
    return text


def imports(text: str) -> list[str]:
    # Ignore comments. Lean import declarations contain module names only.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    found = []
    for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", text, re.M):
        found.extend(match.group(1).split())
    return found


def verify_commit(directory: Path, expected: str) -> None:
    result = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                            capture_output=True, text=True, check=True)
    if result.stdout.strip() != expected:
        raise ValueError(f"Wrong commit at {directory}; expected {expected}")
    # Working-tree edits must not silently change the pinned source.
    result = subprocess.run(["git", "-C", str(directory), "status", "--porcelain",
                             "--untracked-files=no"], capture_output=True, text=True, check=True)
    if result.stdout.strip():
        raise ValueError(f"Tracked working-tree changes at {directory}; use a clean checkout")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--author", required=True, type=Path)
    parser.add_argument("--plby", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    author, plby, output = args.author.resolve(), args.plby.resolve(), args.output.resolve()
    verify_commit(author, AUTHOR_COMMIT)
    verify_commit(plby, PLBY_COMMIT)
    if output.exists():
        raise ValueError("Output must be a new directory; nothing is overwritten")
    output.mkdir(parents=True)
    origin = {}
    author_files = [author / "Nondividing.lean"] + sorted((author / "Nondividing").rglob("*.lean"))
    for path in author_files:
        rel = str(path.relative_to(author))
        target = output / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(patch_author_source(rel, path.read_text()), encoding="utf-8")
        origin[rel] = {"source": "theofilxeff/erdos_131", "commit": AUTHOR_COMMIT,
                       "license": "No license found in inspected pinned tree; separate acquisition"}
    for source in (package / "Erdos131Research", package / "overlay"):
        for path in source.rglob("*.lean"):
            rel = str(path.relative_to(package if source.name == "Erdos131Research" else source))
            target = output / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
            origin[rel] = {"source": "this source-completion package", "state": "COMPILED_ADAPTER_SOURCE"}
    for name in ("Erdos131Audit.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json", "MATHLIB_IMPORTS.txt"):
        shutil.copy2(package / name, output / name)
    # Copy only the imported generic dependency closure. Never execute its Lake
    # configuration or unrelated post-update hooks during assembly.
    queue = list(output.rglob("*.lean"))
    seen = set()
    while queue:
        path = queue.pop()
        for module in imports(path.read_text()):
            if module == "Mathlib" or module.startswith("Mathlib."):
                continue
            if module in seen:
                continue
            seen.add(module)
            rel = module.replace(".", "/") + ".lean"
            target = output / rel
            if target.exists():
                queue.append(target)
                continue
            upstream = plby / "src/latest" / rel
            if not upstream.is_file():
                raise FileNotFoundError(f"Unresolved non-Mathlib import: {module}")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(upstream, target)
            origin[rel] = {"source": "plby/lean-proofs", "commit": PLBY_COMMIT,
                           "license": "Preserve original file notices and upstream license"}
            queue.append(target)
    apply_compilation_patches(output, package)
    shutil.copytree(package / "THIRD_PARTY", output / "THIRD_PARTY")
    for source, name in ((plby / "src/latest/LICENSE", "plby-latest-LICENSE"),
                         (plby / "LICENSE", "plby-root-LICENSE")):
        if source.is_file():
            shutil.copy2(source, output / "THIRD_PARTY" / name)
    for rel, record in origin.items():
        record["sha256"] = hashlib.sha256((output / rel).read_bytes()).hexdigest()
    (output / "SOURCE_MANIFEST.json").write_text(json.dumps({
        "state": "ASSEMBLED_PINNED_SOURCE", "mathlib": MATHLIB_COMMIT,
        "files": origin}, indent=2, ensure_ascii=False) + "\n")
    print(f"Assembled {len(origin)} source files at {output}. No Lean or Lake process was run.")


if __name__ == "__main__":
    main()
