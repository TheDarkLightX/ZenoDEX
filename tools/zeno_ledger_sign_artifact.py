#!/usr/bin/env python3
"""Sign a ZenoLedger artifact hash with a testnet or release envelope."""

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
    build_bls_signed_artifact_envelope_v0,
    build_signed_artifact_envelope_v0,
    infer_artifact_hash_v0,
)


REPORT_SCHEMA = "zenodex.zeno_ledger.sign_artifact_report.v0"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Sign a ZenoLedger artifact hash")
    parser.add_argument("--artifact", required=True, type=Path)
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
    parser.add_argument("--signer-id", required=True)
    parser.add_argument("--key-id", required=True)
    parser.add_argument(
        "--algorithm",
        choices=[
            SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
            SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        ],
        default=SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
    )
    parser.add_argument("--secret-hex")
    parser.add_argument("--bls-private-key-hex")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)

    try:
        artifact = _load_json_object(args.artifact)
        payload_hash = infer_artifact_hash_v0(artifact=artifact, payload_kind=args.payload_kind)
        if args.algorithm == SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0:
            if args.secret_hex is None:
                raise ValueError("--secret-hex is required for HMAC testnet signatures")
            if args.bls_private_key_hex is not None:
                raise ValueError("--bls-private-key-hex is only valid for BLS release signatures")
            envelope = build_signed_artifact_envelope_v0(
                payload_kind=args.payload_kind,
                payload_hash=payload_hash,
                signer_id=args.signer_id,
                key_id=args.key_id,
                secret_hex=args.secret_hex,
            )
        else:
            if args.bls_private_key_hex is None:
                raise ValueError("--bls-private-key-hex is required for BLS release signatures")
            if args.secret_hex is not None:
                raise ValueError("--secret-hex is only valid for HMAC testnet signatures")
            envelope = build_bls_signed_artifact_envelope_v0(
                payload_kind=args.payload_kind,
                payload_hash=payload_hash,
                signer_id=args.signer_id,
                key_id=args.key_id,
                private_key_hex=args.bls_private_key_hex,
            )
        if args.out is not None:
            _write_json(args.out, envelope)
        report = {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "algorithm": args.algorithm,
            "payload_kind": args.payload_kind,
            "payload_hash": payload_hash,
            "envelope": envelope,
        }
        if args.out is not None:
            report["envelope_path"] = str(args.out)
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
