#!/usr/bin/env python3
"""Validate changed-file hygiene evidence and execute its pinned pytest nodes."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.check_test_hygiene_v1 import (
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    REPO_ROOT,
    ChangedPathV1,
    TestHygieneError,
    check_repository,
    collect_git_changed_paths,
)


def run_declared_pytest_nodes(
    node_ids: Sequence[str],
    *,
    repo_root: Path = REPO_ROOT,
    python_executable: str = sys.executable,
) -> None:
    """Run already-validated node IDs as an argv vector without shell parsing."""

    if not node_ids:
        return
    subprocess.run(
        [python_executable, "-m", "pytest", "-q", *node_ids],
        cwd=repo_root,
        check=True,
    )


def _parse_changed_file(value: str) -> ChangedPathV1:
    status, separator, path = value.partition(":")
    if not separator:
        raise TestHygieneError("--changed-file must use STATUS:path")
    return ChangedPathV1(status=status, path=path)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--evidence-dir", type=Path, default=DEFAULT_EVIDENCE_DIR)
    parser.add_argument("--base-ref")
    parser.add_argument("--changed-file", action="append", default=[])
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.base_ref and args.changed_file:
            raise TestHygieneError("use either --base-ref or --changed-file")
        if args.base_ref:
            changed = collect_git_changed_paths(REPO_ROOT, cast(str, args.base_ref))
        else:
            changed = tuple(
                _parse_changed_file(value)
                for value in cast(list[str], args.changed_file)
            )
        report = check_repository(
            repo_root=REPO_ROOT,
            contract_path=cast(Path, args.contract),
            evidence_dir=cast(Path, args.evidence_dir),
            changed_paths=changed,
        )
        run_declared_pytest_nodes(
            cast(list[str], report["pytest_node_ids"]), repo_root=REPO_ROOT
        )
    except TestHygieneError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as exc:
        print(
            f"error: declared hygiene evidence failed with exit {exc.returncode}",
            file=sys.stderr,
        )
        return exc.returncode or 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "test-hygiene-v1: evidence passed "
            f"critical={report['critical_path_count']} "
            f"nodes={len(cast(list[str], report['pytest_node_ids']))}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
