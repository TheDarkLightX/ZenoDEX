#!/usr/bin/env python3
"""Build an artifact-pinned local recursive STARK replay bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.recursive_stark_replay_manifest import (  # noqa: E402
    BUILD_REPORT_SCHEMA_V1,
    NamedArtifactInput,
    RecursiveStarkReplayBundleError,
    build_recursive_stark_replay_bundle_v1,
)


def _named_input(value: str) -> NamedArtifactInput:
    if "=" not in value:
        raise argparse.ArgumentTypeError("expected NAME=PATH")
    name, raw_path = value.split("=", 1)
    if not name or not raw_path:
        raise argparse.ArgumentTypeError("expected non-empty NAME=PATH")
    try:
        return NamedArtifactInput(name=name, path=Path(raw_path))
    except RecursiveStarkReplayBundleError as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-export-report", type=Path, required=True)
    parser.add_argument("--artifact-directory", type=Path, required=True)
    parser.add_argument("--source", type=_named_input, action="append", required=True)
    parser.add_argument("--toolchain", type=_named_input, action="append", required=True)
    parser.add_argument("--proof", type=_named_input, action="append", required=True)
    parser.add_argument("--request", type=_named_input, action="append", required=True)
    parser.add_argument("--verification", type=_named_input, action="append", required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(list(argv) if argv is not None else sys.argv[1:])
    try:
        report = build_recursive_stark_replay_bundle_v1(
            artifact_export_report_path=args.artifact_export_report,
            artifact_directory=args.artifact_directory,
            source_files=args.source,
            toolchain_files=args.toolchain,
            proof_files=args.proof,
            request_files=args.request,
            verification_files=args.verification,
            output_directory=args.out_dir,
        )
    except (RecursiveStarkReplayBundleError, OSError) as exc:
        report = {
            "schema": BUILD_REPORT_SCHEMA_V1,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
            "production_ready": False,
            "public_claim_allowed": False,
        }
        print(json.dumps(report, sort_keys=True))
        return 2
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
