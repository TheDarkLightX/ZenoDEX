#!/usr/bin/env python3
"""Verify a ZenoLedger signed artifact envelope."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_signature import (
    SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
    SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
    infer_artifact_hash_v0,
    validate_bls_signed_artifact_envelope_v0,
    validate_signed_artifact_envelope_v0,
)


REPORT_SCHEMA = "zenodex.zeno_ledger.verify_artifact_signature_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger signed artifact envelope")
    parser.add_argument("--artifact", required=True, type=Path)
    parser.add_argument("--envelope", required=True, type=Path)
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
    parser.add_argument(
        "--algorithm",
        choices=[
            SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
            SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        ],
        default=SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
    )
    parser.add_argument("--secret-hex")
    parser.add_argument("--public-key-hex")
    args = parser.parse_args(argv)

    try:
        artifact = _load_json_object(args.artifact)
        envelope = _load_json_object(args.envelope)
        payload_hash = infer_artifact_hash_v0(artifact=artifact, payload_kind=args.payload_kind)
        if args.algorithm == SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0:
            if args.secret_hex is None:
                raise ValueError("--secret-hex is required for HMAC testnet signatures")
            if args.public_key_hex is not None:
                raise ValueError("--public-key-hex is only valid for BLS release signatures")
            validate_signed_artifact_envelope_v0(
                envelope=envelope,
                expected_payload_kind=args.payload_kind,
                expected_payload_hash=payload_hash,
                secret_hex=args.secret_hex,
            )
        else:
            if args.public_key_hex is None:
                raise ValueError("--public-key-hex is required for BLS release signatures")
            if args.secret_hex is not None:
                raise ValueError("--secret-hex is only valid for HMAC testnet signatures")
            validate_bls_signed_artifact_envelope_v0(
                envelope=envelope,
                expected_payload_kind=args.payload_kind,
                expected_payload_hash=payload_hash,
                expected_public_key=args.public_key_hex,
            )
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "algorithm": args.algorithm,
            "payload_kind": args.payload_kind,
            "payload_hash": payload_hash,
            "envelope_hash": envelope["envelope_hash"],
        }
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
