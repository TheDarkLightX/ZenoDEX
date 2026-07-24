#!/usr/bin/env python3
# ruff: noqa: E402
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
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.zeno_ledger_verify import (
    REPLAY_BOUND_MODE,
    STRUCTURAL_DIAGNOSTIC_MODE,
    verify_zeno_ledger_v0,
)

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
    parser.add_argument(
        "--profile",
        required=True,
        type=Path,
        help="Governed ledger profile whose policy is bound into the attestation",
    )
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--pre-snapshots-dir", type=Path)
    parser.add_argument("--engine-config", type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--structural-only", action="store_true")
    mode.add_argument("--require-state-replay", action="store_true")
    parser.add_argument("--require-rejection-receipt-replay", action="store_true")
    parser.add_argument("--watcher-id", required=True)
    parser.add_argument("--observed-time-ms", required=True, type=int)
    parser.add_argument("--verifier-ref", default="tools/zeno_ledger_verify.py@v0")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    profile = _load_json_object(args.profile)

    verify_report = verify_zeno_ledger_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        profile_path=args.profile,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
        mode=REPLAY_BOUND_MODE if args.require_state_replay else STRUCTURAL_DIAGNOSTIC_MODE,
        pre_snapshots_dir=args.pre_snapshots_dir,
        engine_config_path=args.engine_config,
        require_rejection_receipt_replay=bool(args.require_rejection_receipt_replay),
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
        if args.out is not None:
            _write_json(args.out, attestation)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "verify_report": verify_report,
            "attestation": attestation,
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
