#!/usr/bin/env python3
"""Build a ZenoLedger BLS signer registry."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.make_signer_registry_report.v0"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_signer(raw: str) -> dict[str, Any]:
    parts = raw.split(":")
    if len(parts) not in (3, 4, 5):
        raise ValueError("--signer must be signer_id:key_id:public_key[:weight[:status]]")
    signer_id, key_id, public_key = parts[:3]
    weight = int(parts[3]) if len(parts) >= 4 else 1
    status = parts[4] if len(parts) >= 5 else "active"
    return {
        "signer_id": signer_id,
        "key_id": key_id,
        "public_key": public_key,
        "weight": weight,
        "status": status,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build a ZenoLedger BLS signer registry")
    parser.add_argument("--registry-id", required=True)
    parser.add_argument(
        "--payload-kind",
        required=True,
        choices=[
            "watcher_attestation",
            "mirror_index",
            "tau_export_packet",
            "checkpoint",
            "oracle_authority_profile",
            "proof_verification_report",
            "route_interval_policy_root_bundle",
        ],
    )
    parser.add_argument("--threshold", required=True, type=int)
    parser.add_argument("--signer", required=True, action="append")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        registry = build_signer_registry_v0(
            registry_id=args.registry_id,
            payload_kind=args.payload_kind,
            threshold=args.threshold,
            signers=[_parse_signer(raw) for raw in args.signer],
        )
        if args.out is not None:
            _write_json(args.out, registry)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "registry": registry,
        }
        if args.out is not None:
            report["registry_path"] = str(args.out)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
