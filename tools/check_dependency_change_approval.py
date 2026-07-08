#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEPENDENCY_APPROVAL_PREFIX = "docs/dependency-approvals/"
WATCHED_PATHS = (
    "requirements.txt",
    "requirements-core.txt",
    "requirements-agents.txt",
    "requirements-dev.txt",
    "requirements-core.lock.txt",
    "requirements-agents.lock.txt",
    "requirements-dev.lock.txt",
    "pyproject.toml",
    "Dockerfile",
    "tools/dex-ui/package.json",
    "tools/dex-ui/package-lock.json",
)


def _git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def _resolve_base_ref(explicit_base_ref: str | None) -> str:
    if explicit_base_ref:
        return explicit_base_ref
    if github_base := os.environ.get("GITHUB_BASE_REF"):
        return f"origin/{github_base}"
    for fallback in ("origin/main", "origin/master"):
        try:
            _git("rev-parse", "--verify", fallback)
            return fallback
        except subprocess.CalledProcessError:
            continue
    raise RuntimeError(
        "could not determine base ref; pass --base-ref or run in CI with GITHUB_BASE_REF available"
    )


def _changed_files(base_ref: str) -> list[str]:
    merge_base = _git("merge-base", "HEAD", base_ref)
    committed = _git("diff", "--name-only", f"{merge_base}..HEAD").splitlines()
    untracked = _git("ls-files", "--others", "--exclude-standard").splitlines()
    changed = {line for line in committed + untracked if line}
    return sorted(changed)


def _is_dependency_file(path: str) -> bool:
    return path in WATCHED_PATHS


def _has_approval_note(changed_files: list[str]) -> bool:
    for path in changed_files:
        if path.startswith(DEPENDENCY_APPROVAL_PREFIX) and path.endswith(".md"):
            return True
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Fail pull requests closed when dependency manifests change without a repo-visible approval note "
            "under docs/dependency-approvals/."
        )
    )
    parser.add_argument("--base-ref", help="Git ref used as merge-base baseline, for example origin/main")
    args = parser.parse_args(argv)

    try:
        base_ref = _resolve_base_ref(args.base_ref)
        changed = _changed_files(base_ref)
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"warning: dependency approval check skipped: {exc}", file=sys.stderr)
        return 0

    dependency_changes = [path for path in changed if _is_dependency_file(path)]
    if not dependency_changes:
        print("ok")
        return 0

    if _has_approval_note(changed):
        print("ok")
        return 0

    print("error: dependency-bearing files changed without a matching approval note", file=sys.stderr)
    print("changed dependency files:", file=sys.stderr)
    for path in dependency_changes:
        print(f"  - {path}", file=sys.stderr)
    print(
        f"add a markdown note under {DEPENDENCY_APPROVAL_PREFIX} describing the change, rationale, risk, and rollback plan",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
