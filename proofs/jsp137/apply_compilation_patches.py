"""Apply exact, hash-checked textual repairs to separately acquired fixed sources."""
import hashlib,json
from pathlib import Path

def apply_compilation_patches(output: Path, package: Path) -> None:
    for item in json.loads((package / "COMPILATION_PATCHES.json").read_text()):
        relative=Path(item["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Invalid patch target")
        target=output/relative
        before=target.read_bytes()
        if hashlib.sha256(before).hexdigest()!=item["original_sha256"]:
            raise ValueError(f"Patch input hash differs: {relative}")
        lines=before.decode().splitlines(keepends=True)
        for edit in reversed(item["edits"]):
            lines[edit["start_line"]:edit["end_line"]]=edit["replacement"].splitlines(keepends=True)
        after="".join(lines).encode()
        if hashlib.sha256(after).hexdigest()!=item["patched_sha256"]:
            raise ValueError(f"Patch output hash differs: {relative}")
        target.write_bytes(after)
