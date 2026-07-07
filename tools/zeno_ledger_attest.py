#!/usr/bin/env python3
"""Verify a ZenoLedger range and emit a watcher attestation."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0
from src.integration.zeno_ledger_watcher import (
    build_compact_watcher_attestation_v0,
    build_watcher_attestation_v0,
    compact_verify_report_v0,
)
from tools.zeno_ledger_verify import verify_zeno_ledger_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.attest_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger range and emit a watcher attestation")
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", type=Path)
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--watcher-id", required=True)
    parser.add_argument("--observed-time-ms", required=True, type=int)
    parser.add_argument("--verifier-ref", default="tools/zeno_ledger_verify.py@v0")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    profile: Mapping[str, Any] | None = None
    if args.profile is not None:
        profile = _load_json_object(args.profile)

    verify_report = verify_zeno_ledger_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        profile_path=args.profile,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
    )

    try:
        if verify_report.get("ok") is not True:
            raise ValueError("verify report rejected")
        attestation = build_watcher_attestation_v0(
            verify_report=verify_report,
            watcher_id=args.watcher_id,
            observed_time_ms=args.observed_time_ms,
            verifier_ref=args.verifier_ref,
            profile=profile,
        )
        compact_verify_report = compact_verify_report_v0(verify_report)
        compact_attestation = build_compact_watcher_attestation_v0(
            verify_report=compact_verify_report,
            watcher_id=args.watcher_id,
            observed_time_ms=args.observed_time_ms,
            verifier_ref=args.verifier_ref,
            profile=profile,
        )
        if args.out is not None:
            _write_json(args.out, attestation)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "verify_report": verify_report,
            "attestation": attestation,
            "compact_verify_report": compact_verify_report,
            "compact_attestation": compact_attestation,
        }
        if args.out is not None:
            report["attestation_path"] = str(args.out)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "verify_report": verify_report,
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
