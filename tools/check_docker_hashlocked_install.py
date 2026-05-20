"""Static Dockerfile checks for hash-locked Python dependency installs."""

from __future__ import annotations

from pathlib import Path
from typing import Any


def evaluate_dockerfile(path: Path, *, require_digest: bool = False) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    lines = [line.strip() for line in text.splitlines()]
    checks = {
        "file_exists": path.exists(),
        "copies_runtime_lock": "requirements-core.lock.txt" in text,
        "uses_require_hashes": "--require-hashes" in text,
        "does_not_install_unlocked_runtime_requirements": _does_not_install_unlocked_runtime_requirements(lines),
        "base_images_pinned_by_digest": _base_images_pinned_by_digest(lines),
    }
    warnings: list[str] = []
    if require_digest and not checks["base_images_pinned_by_digest"]:
        warnings.append("base_images_not_pinned_by_digest")
    ok = (
        checks["file_exists"]
        and checks["copies_runtime_lock"]
        and checks["uses_require_hashes"]
        and checks["does_not_install_unlocked_runtime_requirements"]
        and (checks["base_images_pinned_by_digest"] or not require_digest)
    )
    return {
        "schema": "zenodex/docker_hashlocked_install_check/v1",
        "path": str(path),
        "ok": ok,
        "checks": checks,
        "warnings": warnings,
    }


def _does_not_install_unlocked_runtime_requirements(lines: list[str]) -> bool:
    for line in lines:
        if line.startswith("#"):
            continue
        if "pip install" not in line:
            continue
        if "requirements-core.txt" in line and "requirements-core.lock.txt" not in line:
            return False
        if "-r requirements.txt" in line or "-r requirements-core.txt" in line:
            return False
    return True


def _base_images_pinned_by_digest(lines: list[str]) -> bool:
    from_lines = [line for line in lines if line.upper().startswith("FROM ")]
    return bool(from_lines) and all("@sha256:" in line for line in from_lines)
