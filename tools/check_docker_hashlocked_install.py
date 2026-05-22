#!/usr/bin/env python3
"""Check that the production Dockerfile uses hash-locked Python installs."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def _from_images(text: str) -> list[str]:
    images: list[str] = []
    for match in re.finditer(r"(?m)^\s*FROM\s+([^\s]+)(?:\s+AS\s+\S+)?\s*$", text):
        images.append(match.group(1))
    return images


def evaluate_dockerfile(path: Path, *, require_digest: bool = False) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    images = _from_images(text)
    checks = {
        "exists": path.exists(),
        "copies_runtime_lock": "COPY requirements-core.lock.txt" in text,
        "uses_require_hashes": "--require-hashes -r requirements-core.lock.txt" in text,
        "does_not_install_unlocked_runtime_requirements": "requirements-core.txt" not in text,
        "has_base_images": bool(images),
        "base_images_pinned_by_digest": bool(images) and all("@sha256:" in image for image in images),
    }
    if not require_digest:
        digest_ok = True
    else:
        digest_ok = checks["base_images_pinned_by_digest"]
    ok = all(
        bool(checks[name])
        for name in (
            "exists",
            "copies_runtime_lock",
            "uses_require_hashes",
            "does_not_install_unlocked_runtime_requirements",
            "has_base_images",
        )
    ) and digest_ok
    warnings = []
    if images and not checks["base_images_pinned_by_digest"]:
        warnings.append("base_images_not_pinned_by_digest")
    return {
        "schema": "zenodex/docker_hashlocked_install_check/v1",
        "ok": ok,
        "path": str(path),
        "require_digest": bool(require_digest),
        "checks": checks,
        "base_images": images,
        "warnings": warnings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dockerfile", type=Path, default=ROOT / "Dockerfile")
    parser.add_argument("--strict-digest", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    report = evaluate_dockerfile(args.dockerfile, require_digest=bool(args.strict_digest))
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for name, value in report["checks"].items():
            if name == "base_images_pinned_by_digest" and not args.strict_digest and not value:
                status = "warn"
            else:
                status = "ok" if value else "fail"
            print(f"{name}: {status}")
        for warning in report["warnings"]:
            print(f"warning: {warning}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
