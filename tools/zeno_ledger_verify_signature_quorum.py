#!/usr/bin/env python3
"""Verify a ZenoLedger artifact against a BLS signer-registry quorum."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_signature import infer_artifact_hash_v0
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.verify_signature_quorum_cli_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger signature quorum")
    parser.add_argument("--artifact", required=True, type=Path)
    parser.add_argument("--registry", required=True, type=Path)
    parser.add_argument("--envelope", required=True, action="append", type=Path)
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
        ],
    )
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        artifact = _load_json_object(args.artifact)
        registry = _load_json_object(args.registry)
        envelopes = [_load_json_object(path) for path in args.envelope]
        payload_hash = infer_artifact_hash_v0(artifact=artifact, payload_kind=args.payload_kind)
        quorum_report = verify_signature_quorum_v0(
            registry=registry,
            payload_kind=args.payload_kind,
            payload_hash=payload_hash,
            envelopes=envelopes,
        )
        if args.out is not None:
            _write_json(args.out, quorum_report)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "payload_kind": args.payload_kind,
            "payload_hash": payload_hash,
            "registry_hash": registry["registry_hash"],
            "quorum_report": quorum_report,
        }
        if args.out is not None:
            report["quorum_report_path"] = str(args.out)
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
