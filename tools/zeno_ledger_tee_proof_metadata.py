#!/usr/bin/env python3
"""Build ZenoLedger proof metadata from a verified TEE advisory receipt."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.confidential_extension_receipts import verify_confidential_extension_receipt  # noqa: E402
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    build_proof_metadata_v0,
    hash_v0,
    proof_metadata_hash_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.tee_proof_metadata_report.v0"


def _load_json_object(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(obj: Mapping[str, Any], key: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _require_nonnegative_int(obj: Mapping[str, Any], key: str) -> int:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{key} must be a non-negative int")
    return value


def _receipt_body(receipt: Mapping[str, Any]) -> Mapping[str, Any]:
    body = _require_mapping(receipt.get("body"), name="receipt.body")
    _require_str(body, "extension_id")
    _require_str(body, "provider_id")
    _require_str(body, "request_id")
    _require_str(body, "policy_version")
    _require_str(body, "policy_digest")
    _require_str(body, "measurement")
    _require_mapping(body.get("host"), name="receipt.body.host")
    _require_mapping(body.get("accounting"), name="receipt.body.accounting")
    attestation = _require_mapping(body.get("attestation"), name="receipt.body.attestation")
    _require_nonnegative_int(attestation, "attestation_epoch")
    return body


def _run_tee_attestation_verifier_cmd(
    *,
    command: Path,
    attestation_payload: Mapping[str, Any],
    receipt_body: Mapping[str, Any],
) -> None:
    if not command.is_file():
        raise ValueError("TEE attestation verifier command missing")
    proc = subprocess.run(
        [str(command)],
        input=json.dumps(dict(attestation_payload), sort_keys=True, separators=(",", ":")),
        text=True,
        capture_output=True,
        timeout=60,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise ValueError(f"TEE attestation verifier command failed: {detail}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError("TEE attestation verifier command returned invalid JSON") from exc
    if not isinstance(payload, Mapping):
        raise ValueError("TEE attestation verifier command returned non-object JSON")
    if payload.get("ok") is not True:
        error = payload.get("error")
        if not isinstance(error, str) or error == "":
            error = "unknown verifier rejection"
        raise ValueError(f"TEE attestation verifier rejected receipt: {error}")
    result = payload.get("result")
    if not isinstance(result, Mapping):
        raise ValueError("TEE attestation verifier returned missing result object")
    if result.get("measurement") != receipt_body["measurement"]:
        raise ValueError("TEE attestation verifier measurement mismatch")
    if result.get("policy_digest") != receipt_body["policy_digest"]:
        raise ValueError("TEE attestation verifier policy_digest mismatch")
    if result.get("attestation_epoch") != receipt_body["attestation"]["attestation_epoch"]:
        raise ValueError("TEE attestation verifier attestation_epoch mismatch")


def build_tee_proof_metadata_v0(
    *,
    receipt: Mapping[str, Any],
    header: Mapping[str, Any],
    conflict_schedule_hash: str,
    feature_suite_hash: str,
    dependency_lock_hash: str,
    approved_measurements: list[str],
) -> dict[str, Any]:
    """Convert a verified confidential-extension receipt into proof metadata."""

    validate_header_v0(dict(header))
    ok, err = verify_confidential_extension_receipt(dict(receipt), approved_measurements=set(approved_measurements))
    if not ok:
        raise ValueError(f"confidential extension receipt rejected: {err}")
    body = _receipt_body(receipt)
    host = _require_mapping(body["host"], name="receipt.body.host")
    accounting = _require_mapping(body["accounting"], name="receipt.body.accounting")
    attestation = _require_mapping(body["attestation"], name="receipt.body.attestation")
    public_input = {
        "extension_id": body["extension_id"],
        "provider_id": body["provider_id"],
        "request_id": body["request_id"],
        "policy_version": body["policy_version"],
        "policy_digest": body["policy_digest"],
        "measurement": body["measurement"],
        "receipt_hash": receipt["receipt_hash"],
        "current_epoch": attestation["current_epoch"],
        "attestation_epoch": attestation["attestation_epoch"],
        "max_attestation_age": attestation["max_attestation_age"],
    }
    journal = {
        "journal_version": 1,
        **public_input,
        "host": dict(host),
        "accounting": dict(accounting),
    }
    return build_proof_metadata_v0(
        chain_id=str(header["chain_id"]),
        height=int(header["height"]),
        proof_kind="tee_attestation_v0",
        program_id=f"tee:{body['extension_id']}:{body['policy_version']}",
        verifier_id=f"tee:confidential-attestation-verifier:v1:{body['provider_id']}",
        proof_commitment=hash_v0("tee_confidential_extension_receipt_v0", receipt),
        public_input_hash=hash_v0("tee_confidential_extension_public_input_v0", public_input),
        journal_hash=hash_v0("tee_confidential_extension_journal_v0", journal),
        pre_state_root=str(header["pre_state_root"]),
        post_state_root=str(header["post_state_root"]),
        tx_root=str(header["tx_root"]),
        evidence_root=str(header["evidence_root"]),
        body_root=str(header["body_root"]),
        conflict_schedule_hash=conflict_schedule_hash,
        feature_suite_hash=feature_suite_hash,
        dependency_lock_hash=dependency_lock_hash,
        tee_measurement_hash=hash_v0("tee_confidential_extension_measurement_v0", body["measurement"]),
    )


def _report(
    *,
    metadata: dict[str, Any],
    metadata_path: Path | None,
    header_bound: bool,
    body_checked: bool,
    tee_verified: bool,
) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "metadata_path": None if metadata_path is None else str(metadata_path),
        "proof_journal_hash": proof_metadata_hash_v0(metadata),
        "proof_kind": metadata["proof_kind"],
        "program_id": metadata["program_id"],
        "verifier_id": metadata["verifier_id"],
        "tee_measurement_hash": metadata["tee_measurement_hash"],
        "header_bound": header_bound,
        "body_checked": body_checked,
        "tee_verified": tee_verified,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", required=True, type=Path, help="Confidential extension receipt JSON")
    parser.add_argument("--header", required=True, type=Path, help="ZenoLedger v0 header JSON")
    parser.add_argument("--body", type=Path, help="Optional ZenoLedger body JSON to check against the header")
    parser.add_argument("--out", type=Path, help="Optional output path for proof metadata JSON")
    parser.add_argument("--conflict-schedule-hash", required=True)
    parser.add_argument("--feature-suite-hash", required=True)
    parser.add_argument("--dependency-lock-hash", required=True)
    parser.add_argument("--approved-measurement", action="append", default=[])
    parser.add_argument(
        "--require-bound-header",
        action="store_true",
        help="Require header.proof_journal_hash to equal the generated metadata hash",
    )
    parser.add_argument("--attestation-payload", type=Path)
    parser.add_argument(
        "--tee-attestation-verify-cmd",
        type=Path,
        help="Optional verifier command that accepts the raw attestation payload JSON on stdin",
    )
    parser.add_argument(
        "--require-tee-attestation-verifier",
        action="store_true",
        help="Fail unless --tee-attestation-verify-cmd and --attestation-payload are supplied and accepted",
    )
    args = parser.parse_args(argv)

    try:
        receipt = _load_json_object(args.receipt)
        header = _load_json_object(args.header)
        body_checked = False
        if args.body is not None:
            validate_header_body_roots_v0(header, _load_json_object(args.body))
            body_checked = True

        receipt_body = _receipt_body(receipt)
        tee_verified = False
        if args.require_tee_attestation_verifier:
            if args.tee_attestation_verify_cmd is None:
                raise ValueError("--require-tee-attestation-verifier requires --tee-attestation-verify-cmd")
            if args.attestation_payload is None:
                raise ValueError("--require-tee-attestation-verifier requires --attestation-payload")
        if args.tee_attestation_verify_cmd is not None:
            if args.attestation_payload is None:
                raise ValueError("--tee-attestation-verify-cmd requires --attestation-payload")
            _run_tee_attestation_verifier_cmd(
                command=args.tee_attestation_verify_cmd,
                attestation_payload=_load_json_object(args.attestation_payload),
                receipt_body=receipt_body,
            )
            tee_verified = True

        approved_measurements = list(args.approved_measurement)
        if receipt_body["measurement"] not in approved_measurements:
            raise ValueError("receipt measurement is not in --approved-measurement")
        metadata = build_tee_proof_metadata_v0(
            receipt=receipt,
            header=header,
            conflict_schedule_hash=args.conflict_schedule_hash,
            feature_suite_hash=args.feature_suite_hash,
            dependency_lock_hash=args.dependency_lock_hash,
            approved_measurements=approved_measurements,
        )
        metadata_hash = proof_metadata_hash_v0(metadata)
        header_bound = header["proof_journal_hash"] == metadata_hash
        if args.require_bound_header:
            validate_proof_metadata_header_binding_v0(metadata, header)
            header_bound = True
        if args.out is not None:
            _write_json(args.out, metadata)
        print(
            json.dumps(
                _report(
                    metadata=metadata,
                    metadata_path=args.out,
                    header_bound=header_bound,
                    body_checked=body_checked,
                    tee_verified=tee_verified,
                ),
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    except Exception as exc:  # noqa: BLE001
        print(
            json.dumps(
                {
                    "schema": REPORT_SCHEMA,
                    "ok": False,
                    "error": str(exc),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
