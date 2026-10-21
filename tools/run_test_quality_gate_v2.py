#!/usr/bin/env python3
"""Validate V2 obligations and execute the exact V1-pinned pytest nodes."""

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
    REPO_ROOT,
    ChangedPathV1,
    collect_git_changed_paths,
)
from tools.check_test_quality_v2 import check_test_quality_repository
from tools.run_test_hygiene_gate_v1 import run_declared_pytest_nodes
from tools.test_hygiene_model_v1 import TestHygieneError
from tools.test_quality_model_v2 import DEFAULT_CONTRACT, DEFAULT_EVIDENCE_DIR


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
        changed = (
            collect_git_changed_paths(REPO_ROOT, cast(str, args.base_ref))
            if args.base_ref
            else tuple(_parse_changed_file(value) for value in cast(list[str], args.changed_file))
        )
        report = check_test_quality_repository(
            repo_root=REPO_ROOT,
            quality_contract_path=cast(Path, args.contract),
            quality_evidence_dir=cast(Path, args.evidence_dir),
            changed_paths=changed,
        )
        run_declared_pytest_nodes(cast(list[str], report["pytest_node_ids"]), repo_root=REPO_ROOT)
    except TestHygieneError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as exc:
        print(
            f"error: declared quality evidence failed with exit {exc.returncode}",
            file=sys.stderr,
        )
        return exc.returncode or 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "test-quality-v2: evidence passed "
            f"critical={report['critical_path_count']} "
            f"nodes={len(cast(list[str], report['pytest_node_ids']))}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
