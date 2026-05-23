#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DOCKERFILE = ROOT / "Dockerfile.hashlocked"
PIP_INSTALL_RE = re.compile(r"\bpip(?:[0-9.]+)?\s+install\b")
ROOT_LOCK_RE = re.compile(r"(?:^|[\s\"'=])requirements-core\.lock\.txt(?:$|[\s\"'])")
ROOT_UNLOCKED_RE = re.compile(r"(?:^|[\s\"'=])requirements-core\.txt(?:$|[\s\"'])")
API_HOST_RE = re.compile(r"\bAPI_HOST\s*=\s*\"?127\.0\.0\.1\"?")
USER_RE = re.compile(r"^\s*USER\s+([^\s#]+)\s*$", re.IGNORECASE)
SECRET_RE = re.compile(r"(--privkey\b|\b(?:privkey|private_key|mnemonic|password|secret|api_token|access_token)\b)", re.IGNORECASE)


def _from_images(text: str) -> list[str]:
    images: list[str] = []
    for match in re.finditer(r"(?m)^\s*FROM\s+([^\s]+)(?:\s+AS\s+\S+)?\s*$", text):
        images.append(match.group(1))
    return images


def _display_path(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def _logical_lines(text: str) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    buf = ""
    start = 1
    for line_no, raw in enumerate(text.splitlines(), start=1):
        current = raw.rstrip()
        if not buf:
            start = line_no
            buf = current
        else:
            buf = f"{buf} {current.lstrip()}"
        if current.endswith("\\"):
            buf = buf[:-1].rstrip()
            continue
        out.append((start, buf))
        buf = ""
    if buf:
        out.append((start, buf))
    return out


def check_docker_hashlocked_install(root: Path = ROOT, dockerfile: Path | None = None) -> dict[str, Any]:
    path = dockerfile or (root / "Dockerfile.hashlocked")
    display = _display_path(path, root)
    findings: list[dict[str, Any]] = []

    if not path.is_file():
        findings.append(
            {
                "path": display,
                "line": 0,
                "code": "missing_dockerfile",
                "message": "Dockerfile.hashlocked is missing",
            }
        )
        return {"ok": False, "path": display, "findings": findings}

    text = path.read_text(encoding="utf-8")
    logical_lines = _logical_lines(text)

    if "requirements-core.lock.txt" not in text:
        findings.append(
            {
                "path": display,
                "line": 0,
                "code": "missing_lockfile_reference",
                "message": "Dockerfile.hashlocked must reference requirements-core.lock.txt",
            }
        )

    matched_lock_install = False
    for line_no, line in logical_lines:
        if not PIP_INSTALL_RE.search(line):
            continue
        if ROOT_UNLOCKED_RE.search(line):
            findings.append(
                {
                    "path": display,
                    "line": line_no,
                    "code": "unlocked_requirements_install",
                    "message": "final dependency install must not use requirements-core.txt",
                }
            )
        if ROOT_LOCK_RE.search(line):
            matched_lock_install = True
            if "--require-hashes" not in line:
                findings.append(
                    {
                        "path": display,
                        "line": line_no,
                        "code": "missing_require_hashes",
                        "message": "requirements-core.lock.txt install must include --require-hashes",
                    }
                )

    if not matched_lock_install:
        findings.append(
            {
                "path": display,
                "line": 0,
                "code": "missing_lock_install_command",
                "message": "Dockerfile.hashlocked must install requirements-core.lock.txt with pip",
            }
        )

    if not API_HOST_RE.search(text):
        findings.append(
            {
                "path": display,
                "line": 0,
                "code": "api_host_not_loopback",
                "message": "Dockerfile.hashlocked must set or preserve API_HOST=127.0.0.1",
            }
        )

    user_matches = [(line_no, match.group(1)) for line_no, line in logical_lines if (match := USER_RE.match(line))]
    if not user_matches:
        findings.append(
            {
                "path": display,
                "line": 0,
                "code": "missing_non_root_user",
                "message": "Dockerfile.hashlocked must set a non-root final USER",
            }
        )
    else:
        user_line, user_name = user_matches[-1]
        if user_name.lower() == "root":
            findings.append(
                {
                    "path": display,
                    "line": user_line,
                    "code": "root_final_user",
                    "message": "Dockerfile.hashlocked final USER must not be root",
                }
            )

    for line_no, line in logical_lines:
        secret_match = SECRET_RE.search(line)
        if secret_match is None:
            continue
        findings.append(
            {
                "path": display,
                "line": line_no,
                "code": "obvious_secret_reference",
                "message": f"Dockerfile.hashlocked must not reference obvious secret material: {secret_match.group(1)}",
            }
        )

    return {"ok": not findings, "path": display, "findings": findings}


def evaluate_dockerfile(path: Path, *, require_digest: bool = False) -> dict[str, Any]:
    if not path.is_file():
        return {
            "schema": "zenodex/docker_hashlocked_install_check/v1",
            "ok": False,
            "path": str(path),
            "require_digest": bool(require_digest),
            "checks": {
                "exists": False,
                "copies_runtime_lock": False,
                "uses_require_hashes": False,
                "does_not_install_unlocked_runtime_requirements": False,
                "has_base_images": False,
                "base_images_pinned_by_digest": False,
            },
            "base_images": [],
            "warnings": [],
        }

    text = path.read_text(encoding="utf-8")
    images = _from_images(text)
    checks = {
        "exists": True,
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
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--dockerfile", type=Path, default=None)
    parser.add_argument("--strict-digest", action="store_true")
    parser.add_argument("--json", action="store_true", help="accepted for compatibility; output is always JSON")
    args = parser.parse_args(argv)

    if args.dockerfile is None:
        report = check_docker_hashlocked_install(root=args.root, dockerfile=None)
        digest_report = evaluate_dockerfile(args.root / "Dockerfile.hashlocked", require_digest=bool(args.strict_digest))
        report["warnings"] = digest_report["warnings"]
        report["base_images"] = digest_report["base_images"]
        if not digest_report["ok"]:
            report["ok"] = False
            report["findings"].append(
                {
                    "path": report["path"],
                    "line": 0,
                    "code": "digest_or_hashlocked_contract_failed",
                    "message": "Dockerfile.hashlocked failed the digest or hash-locked install contract",
                    "checks": digest_report["checks"],
                }
            )
    else:
        dockerfile = args.dockerfile
        if not dockerfile.is_absolute():
            dockerfile = args.root / dockerfile
        report = evaluate_dockerfile(dockerfile, require_digest=bool(args.strict_digest))

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
