#!/usr/bin/env python3
"""Verify a local ZenoLedger light-client checkpoint quorum."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_signer_registry import (  # noqa: E402
    validate_signer_registry_v0,
    verify_signature_quorum_v0,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_checkpoint_v0,
)
from tools.zeno_ledger_verify import (  # noqa: E402
    STRUCTURAL_DIAGNOSTIC_MODE,
    ZERO_ROOT,
    verify_zeno_ledger_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.light_client_checkpoint_report.v0"
CHECKPOINT_PAYLOAD_KIND = "checkpoint"


def light_client_signature_set_root_v0(registry: Mapping[str, Any]) -> str:
    """Commit the header to the signer registry and threshold used for finality."""

    validate_signer_registry_v0(registry)
    body = {
        "registry_hash": registry["registry_hash"],
        "payload_kind": CHECKPOINT_PAYLOAD_KIND,
        "threshold": registry["threshold"],
    }
    return hash_v0("light_client_signature_set_root_v0", body)


def light_client_checkpoint_hash_v0(checkpoint: Mapping[str, Any]) -> str:
    """Hash the checkpoint payload signed by the release quorum."""

    obj = dict(checkpoint)
    validate_checkpoint_v0(obj)
    return hash_v0("light_client_checkpoint_v0", obj)


def validate_light_client_checkpoint_v0(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    checkpoints_dir: Path,
    registry: Mapping[str, Any],
    envelopes: Sequence[Mapping[str, Any]],
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str = ZERO_ROOT,
    profile_path: Path | None = None,
    proof_metadata_dir: Path | None = None,
    proof_verification_report_dir: Path | None = None,
    require_proof_verification_report: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    verify_report = verify_zeno_ledger_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        profile_path=profile_path,
        from_height=from_height,
        to_height=to_height,
        trusted_prev_header_hash=trusted_prev_header_hash,
        proof_metadata_dir=proof_metadata_dir,
        proof_verification_report_dir=proof_verification_report_dir,
        require_proof_verification_report=require_proof_verification_report,
        mode=STRUCTURAL_DIAGNOSTIC_MODE,
    )
    if verify_report.get("ok") is not True:
        errors.append("structural range diagnostic rejected")

    registry_obj = dict(registry)
    try:
        expected_signature_set_root = light_client_signature_set_root_v0(registry_obj)
    except Exception as exc:
        expected_signature_set_root = None
        errors.append(f"signer registry rejected: {exc}")

    header_path = headers_dir / f"{to_height}.json"
    checkpoint_path = checkpoints_dir / f"{to_height}.json"
    target_header: dict[str, Any] | None = None
    target_checkpoint: dict[str, Any] | None = None
    checkpoint_hash: str | None = None
    quorum_report: dict[str, Any] | None = None
    try:
        target_header = dict(_load_json_object(header_path))
        target_checkpoint = dict(_load_json_object(checkpoint_path))
        validate_checkpoint_header_binding_v0(target_checkpoint, target_header)
        if target_checkpoint.get("height") != to_height:
            raise ValueError("target checkpoint height mismatch")
        if (
            verify_report.get("last_header_hash") is not None
            and target_checkpoint.get("header_hash") != verify_report.get("last_header_hash")
        ):
            raise ValueError("target checkpoint does not match verified range tip")
        if target_checkpoint.get("signature_set") != []:
            raise ValueError("target checkpoint signature_set must be empty; external quorum report is authoritative")
        if (
            expected_signature_set_root is not None
            and target_checkpoint.get("signature_set_root") != expected_signature_set_root
        ):
            raise ValueError("target checkpoint signature_set_root does not match signer registry root")
        checkpoint_hash = light_client_checkpoint_hash_v0(target_checkpoint)
        quorum_report = verify_signature_quorum_v0(
            registry=registry_obj,
            payload_kind=CHECKPOINT_PAYLOAD_KIND,
            payload_hash=checkpoint_hash,
            envelopes=envelopes,
        )
    except Exception as exc:
        errors.append(f"checkpoint quorum rejected: {exc}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "from_height": from_height,
        "to_height": to_height,
        "trusted_prev_header_hash": trusted_prev_header_hash,
        "target_header_path": str(header_path),
        "target_checkpoint_path": str(checkpoint_path),
        "target_header_hash": None if target_checkpoint is None else target_checkpoint.get("header_hash"),
        "checkpoint_hash": checkpoint_hash,
        "expected_signature_set_root": expected_signature_set_root,
        "quorum_report": quorum_report,
        "range_verify_report": verify_report,
    }


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", required=True, type=Path)
    parser.add_argument("--registry", required=True, type=Path)
    parser.add_argument("--envelope", required=True, action="append", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--proof-metadata-dir", type=Path)
    parser.add_argument("--proof-verification-report-dir", type=Path)
    parser.add_argument("--require-proof-verification-report", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    registry = _load_json_object(args.registry)
    envelopes = [_load_json_object(path) for path in args.envelope]
    report = validate_light_client_checkpoint_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
        profile_path=args.profile,
        proof_metadata_dir=args.proof_metadata_dir,
        proof_verification_report_dir=args.proof_verification_report_dir,
        require_proof_verification_report=args.require_proof_verification_report,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
