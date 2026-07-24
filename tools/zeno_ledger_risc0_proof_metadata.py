#!/usr/bin/env python3
"""Build non-authoritative ZenoLedger metadata diagnostics for a Risc0 proof.

ProofMetadataV0 contains ledger roots that the legacy Spot journal does not
authenticate. This adapter may copy those roots into a diagnostic metadata
proposal so archived tooling can reproduce its historical hash. It cannot mint
proof authority from that proposal or from a caller-selected verifier command.
"""

from __future__ import annotations

import argparse
import base64
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.proof_toolchain_lock import proof_toolchain_lock_hash_v0  # noqa: E402
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    ZERO_ROOT_V0,
    build_proof_metadata_v0,
    hash_v0,
    proof_metadata_hash_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.risc0_proof_metadata_diagnostic.v0"
REPORT_STATUS = "non_authoritative_header_derived_metadata"
HEADER_DERIVED_FIELDS = (
    "chain_id",
    "height",
    "pre_state_root",
    "post_state_root",
    "tx_root",
    "evidence_root",
    "body_root",
)
LEGACY_AUTHORITY_BUILDER_ERROR = (
    "build_risc0_proof_metadata_v0 is disabled because ProofMetadataV0 ledger "
    "roots are header-derived; use the explicitly diagnostic builder"
)
TAU_STATE_PROOF_SCHEMA = "tau_state_proof"
TAU_STATE_PROOF_SCHEMA_VERSION = 1
RISC0_ZENODEX_SPOT_PROOF_TYPE_V1 = "risc0.zenodex_spot_transition.v1"
RISC0_VERIFY_REQUEST_SCHEMA = "tau_state_proof_verify"
RISC0_VERIFY_REQUEST_SCHEMA_VERSION = 1


def _load_json_object(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _require_str(obj: Mapping[str, Any], key: str, *, allow_empty: bool = False) -> str:
    value = obj.get(key)
    if not isinstance(value, str):
        raise TypeError(f"{key} must be a string")
    if not allow_empty and value == "":
        raise ValueError(f"{key} must be non-empty")
    return value


def _normalize_hex32(value: str, *, name: str, allow_empty: bool = False) -> str:
    if allow_empty and value == "":
        return ""
    raw = value.lower()
    if raw.startswith("0x"):
        raw = raw[2:]
    if len(raw) != 64:
        raise ValueError(f"{name} must be 32-byte hex")
    try:
        bytes.fromhex(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be hex") from exc
    return raw


def _header_root_hex(header: Mapping[str, Any], field: str) -> str:
    return _normalize_hex32(_require_str(header, field), name=f"header.{field}")


def _validate_risc0_tau_state_proof(envelope: Mapping[str, Any]) -> dict[str, Any]:
    expected = {"schema", "schema_version", "state_hash", "proof_type", "proof", "meta"}
    if set(envelope.keys()) != expected:
        raise ValueError("risc0 envelope keys mismatch")
    if envelope.get("schema") != TAU_STATE_PROOF_SCHEMA:
        raise ValueError("risc0 envelope schema mismatch")
    if envelope.get("schema_version") != TAU_STATE_PROOF_SCHEMA_VERSION:
        raise ValueError("risc0 envelope schema_version mismatch")
    proof_type = _require_str(envelope, "proof_type")
    if proof_type != RISC0_ZENODEX_SPOT_PROOF_TYPE_V1:
        raise ValueError("unsupported risc0 proof_type")

    state_hash = _normalize_hex32(_require_str(envelope, "state_hash"), name="state_hash")
    proof_b64 = _require_str(envelope, "proof")
    try:
        base64.b64decode(proof_b64, validate=True)
    except Exception as exc:  # noqa: BLE001
        raise ValueError("proof must be valid base64") from exc

    meta = envelope.get("meta")
    if not isinstance(meta, Mapping):
        raise TypeError("meta must be a JSON object")
    expected_meta = {
        "risc0_image_id",
        "txs_commitment",
        "ingress_commitment",
        "pre_nonce_root",
        "post_nonce_root",
        "accepted_receipts_root",
        "pre_app_hash",
        "post_app_hash",
    }
    if set(meta.keys()) != expected_meta:
        raise ValueError("risc0 meta keys mismatch")

    image_id = _normalize_hex32(_require_str(meta, "risc0_image_id"), name="meta.risc0_image_id")
    txs_commitment = _normalize_hex32(_require_str(meta, "txs_commitment"), name="meta.txs_commitment")
    ingress_commitment = _normalize_hex32(
        _require_str(meta, "ingress_commitment"),
        name="meta.ingress_commitment",
    )
    pre_nonce_root = _normalize_hex32(_require_str(meta, "pre_nonce_root"), name="meta.pre_nonce_root")
    post_nonce_root = _normalize_hex32(_require_str(meta, "post_nonce_root"), name="meta.post_nonce_root")
    accepted_receipts_root = _normalize_hex32(
        _require_str(meta, "accepted_receipts_root"),
        name="meta.accepted_receipts_root",
    )
    pre_app_hash = _normalize_hex32(
        _require_str(meta, "pre_app_hash", allow_empty=True),
        name="meta.pre_app_hash",
        allow_empty=True,
    )
    post_app_hash = _normalize_hex32(_require_str(meta, "post_app_hash"), name="meta.post_app_hash")
    return {
        "schema": TAU_STATE_PROOF_SCHEMA,
        "schema_version": TAU_STATE_PROOF_SCHEMA_VERSION,
        "state_hash": state_hash,
        "proof_type": proof_type,
        "proof": proof_b64,
        "meta": {
            "risc0_image_id": image_id,
            "txs_commitment": txs_commitment,
            "ingress_commitment": ingress_commitment,
            "pre_nonce_root": pre_nonce_root,
            "post_nonce_root": post_nonce_root,
            "accepted_receipts_root": accepted_receipts_root,
            "pre_app_hash": pre_app_hash,
            "post_app_hash": post_app_hash,
        },
    }


def build_header_derived_risc0_proof_metadata_diagnostic_v0(
    *,
    proof_envelope: Mapping[str, Any],
    header: Mapping[str, Any],
    conflict_schedule_hash: str,
    feature_suite_hash: str,
    dependency_lock_hash: str,
    toolchain_lock_hash: str,
) -> dict[str, Any]:
    """Build a header-derived metadata proposal with no proof authority.

    ``pre_state_root``, ``post_state_root``, ``tx_root``, ``evidence_root``,
    and ``body_root`` come from the caller's header. The legacy Spot journal
    does not authenticate those ZenoLedger-domain roots. Consumers must retain
    this function's diagnostic-only provenance and must not use its return
    value as an authenticated verifier result.
    """

    proof = _validate_risc0_tau_state_proof(proof_envelope)
    validate_header_v0(dict(header))
    meta = proof["meta"]
    if not isinstance(meta, Mapping):
        raise TypeError("normalized proof meta must be a mapping")

    public_input = {
        "proof_type": proof["proof_type"],
        "state_hash": proof["state_hash"],
        "txs_commitment": meta["txs_commitment"],
        "ingress_commitment": meta["ingress_commitment"],
        "pre_nonce_root": meta["pre_nonce_root"],
        "post_nonce_root": meta["post_nonce_root"],
        "accepted_receipts_root": meta["accepted_receipts_root"],
        "pre_app_hash_present": meta["pre_app_hash"] != "",
        "pre_app_hash": meta["pre_app_hash"],
        "post_app_hash": meta["post_app_hash"],
    }
    journal = {
        "journal_version": 1,
        **public_input,
    }

    return build_proof_metadata_v0(
        chain_id=str(header["chain_id"]),
        height=int(header["height"]),
        proof_kind="risc0_zkvm_v0",
        program_id=f"risc0:{proof['proof_type']}:{meta['risc0_image_id']}",
        verifier_id=f"risc0:receipt-verifier:v1:{proof['proof_type']}",
        proof_commitment=hash_v0("risc0_tau_state_proof_envelope_v0", proof),
        public_input_hash=hash_v0("risc0_tau_state_proof_public_input_v0", public_input),
        journal_hash=hash_v0("risc0_tau_state_proof_journal_v0", journal),
        pre_state_root=str(header["pre_state_root"]),
        post_state_root=str(header["post_state_root"]),
        tx_root=str(header["tx_root"]),
        evidence_root=str(header["evidence_root"]),
        body_root=str(header["body_root"]),
        conflict_schedule_hash=conflict_schedule_hash,
        feature_suite_hash=feature_suite_hash,
        dependency_lock_hash=dependency_lock_hash,
        toolchain_lock_hash=toolchain_lock_hash,
    )


def build_risc0_proof_metadata_v0(
    *,
    proof_envelope: Mapping[str, Any],
    header: Mapping[str, Any],
    conflict_schedule_hash: str,
    feature_suite_hash: str,
    dependency_lock_hash: str,
    toolchain_lock_hash: str,
) -> dict[str, Any]:
    """Reject the ambiguous legacy authority-bearing builder entry point."""

    del (
        proof_envelope,
        header,
        conflict_schedule_hash,
        feature_suite_hash,
        dependency_lock_hash,
        toolchain_lock_hash,
    )
    raise ValueError(LEGACY_AUTHORITY_BUILDER_ERROR)


def _run_risc0_verifier_cmd(*, command: Path, proof: Mapping[str, Any]) -> None:
    if not command.is_file():
        raise ValueError("risc0 verifier command missing")
    request = {
        "schema": RISC0_VERIFY_REQUEST_SCHEMA,
        "schema_version": RISC0_VERIFY_REQUEST_SCHEMA_VERSION,
        "state_hash": proof["state_hash"],
        "proof": dict(proof),
        "tau_state": {"app_hash": proof["meta"]["post_app_hash"]},
        "context": {"app_hash_pre": proof["meta"]["pre_app_hash"]},
    }
    proc = subprocess.run(
        [str(command)],
        input=json.dumps(request, sort_keys=True, separators=(",", ":")),
        text=True,
        capture_output=True,
        timeout=60,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise ValueError(f"risc0 verifier command failed: {detail}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise ValueError("risc0 verifier command returned invalid JSON") from exc
    if not isinstance(payload, Mapping):
        raise ValueError("risc0 verifier command returned non-object JSON")
    if payload.get("ok") is not True:
        error = payload.get("error")
        if not isinstance(error, str) or error == "":
            error = "unknown verifier rejection"
        raise ValueError(f"risc0 verifier rejected proof: {error}")


def _report(
    *,
    metadata: dict[str, Any],
    metadata_path: Path | None,
    header_bound: bool,
    body_checked: bool,
    post_app_hash_checked: bool,
    post_state_root_checked: bool,
    pre_state_root_checked: bool,
    caller_selected_verifier_accepted: bool,
) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": REPORT_STATUS,
        "authority_scope": "none",
        "metadata_path": None if metadata_path is None else str(metadata_path),
        "proof_journal_hash": proof_metadata_hash_v0(metadata),
        "proof_kind": metadata["proof_kind"],
        "program_id": metadata["program_id"],
        "verifier_id": metadata["verifier_id"],
        "toolchain_lock_hash": metadata["toolchain_lock_hash"],
        "header_bound": header_bound,
        "body_checked": body_checked,
        "post_app_hash_checked": post_app_hash_checked,
        "post_state_root_checked": post_state_root_checked,
        "pre_state_root_checked": pre_state_root_checked,
        "caller_selected_verifier_accepted": caller_selected_verifier_accepted,
        "header_derived_fields": list(HEADER_DERIVED_FIELDS),
        "metadata_roots_authenticated_by_risc0": False,
        "proof_authority_satisfied": False,
        "settlement_authority": False,
        "production_authority": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", required=True, type=Path, help="Risc0 tau_state_proof envelope JSON")
    parser.add_argument("--header", required=True, type=Path, help="ZenoLedger v0 header JSON")
    parser.add_argument("--body", type=Path, help="Optional ZenoLedger body JSON to check against the header")
    parser.add_argument("--out", type=Path, help="Optional output path for proof metadata JSON")
    parser.add_argument("--conflict-schedule-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--feature-suite-hash", default=ZERO_ROOT_V0)
    parser.add_argument("--dependency-lock-hash", default=ZERO_ROOT_V0)
    parser.add_argument(
        "--toolchain-lock-hash",
        help="Proof toolchain lock hash. Defaults to the local repo manifest hash.",
    )
    parser.add_argument(
        "--require-bound-header",
        action="store_true",
        help=(
            "Require structural equality between header.proof_journal_hash and the diagnostic "
            "metadata hash; this does not establish proof authority"
        ),
    )
    parser.add_argument(
        "--require-post-app-hash-header-app-hash",
        action="store_true",
        help="Require the Risc0 post_app_hash journal field to equal header.app_hash",
    )
    parser.add_argument(
        "--require-post-app-hash-header-post-state-root",
        action="store_true",
        help="Require the Risc0 post_app_hash journal field to equal header.post_state_root",
    )
    parser.add_argument(
        "--require-pre-app-hash-header-pre-state-root",
        action="store_true",
        help="Require the Risc0 pre_app_hash journal field to equal header.pre_state_root when pre_app_hash is present",
    )
    parser.add_argument(
        "--risc0-verify-cmd",
        type=Path,
        help="Optional external Risc0 verifier command that accepts tau_state_proof_verify JSON on stdin",
    )
    parser.add_argument(
        "--require-risc0-verifier",
        action="store_true",
        help=(
            "Fail unless the caller-selected --risc0-verify-cmd accepts the proof envelope; "
            "this remains non-authoritative"
        ),
    )
    args = parser.parse_args(argv)

    try:
        proof = _load_json_object(args.proof)
        header = _load_json_object(args.header)
        body_checked = False
        if args.body is not None:
            validate_header_body_roots_v0(header, _load_json_object(args.body))
            body_checked = True

        normalized_proof = _validate_risc0_tau_state_proof(proof)
        caller_selected_verifier_accepted = False
        if args.require_risc0_verifier and args.risc0_verify_cmd is None:
            raise ValueError("--require-risc0-verifier requires --risc0-verify-cmd")
        if args.risc0_verify_cmd is not None:
            _run_risc0_verifier_cmd(command=args.risc0_verify_cmd, proof=normalized_proof)
            caller_selected_verifier_accepted = True
        if args.require_post_app_hash_header_app_hash:
            post_app_hash = normalized_proof["meta"]["post_app_hash"]
            header_app_hash = str(header["app_hash"]).lower()
            if header_app_hash.startswith("0x"):
                header_app_hash = header_app_hash[2:]
            if post_app_hash != header_app_hash:
                raise ValueError("risc0 post_app_hash/header app_hash mismatch")
        if args.require_post_app_hash_header_post_state_root:
            post_app_hash = normalized_proof["meta"]["post_app_hash"]
            if post_app_hash != _header_root_hex(header, "post_state_root"):
                raise ValueError("risc0 post_app_hash/header post_state_root mismatch")
        if args.require_pre_app_hash_header_pre_state_root:
            pre_app_hash = normalized_proof["meta"]["pre_app_hash"]
            header_pre_state_root = _header_root_hex(header, "pre_state_root")
            if pre_app_hash != "" and pre_app_hash != header_pre_state_root:
                raise ValueError("risc0 pre_app_hash/header pre_state_root mismatch")

        metadata = build_header_derived_risc0_proof_metadata_diagnostic_v0(
            proof_envelope=normalized_proof,
            header=header,
            conflict_schedule_hash=args.conflict_schedule_hash,
            feature_suite_hash=args.feature_suite_hash,
            dependency_lock_hash=args.dependency_lock_hash,
            toolchain_lock_hash=args.toolchain_lock_hash or proof_toolchain_lock_hash_v0(ROOT),
        )
        metadata_hash = proof_metadata_hash_v0(metadata)
        header_bound = header["proof_journal_hash"] == metadata_hash
        if args.require_bound_header or header["proof_journal_hash"] != ZERO_ROOT_V0:
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
                    post_app_hash_checked=args.require_post_app_hash_header_app_hash,
                    post_state_root_checked=args.require_post_app_hash_header_post_state_root,
                    pre_state_root_checked=args.require_pre_app_hash_header_pre_state_root,
                    caller_selected_verifier_accepted=caller_selected_verifier_accepted,
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
                    "status": "rejected",
                    "authority_scope": "none",
                    "metadata_roots_authenticated_by_risc0": False,
                    "proof_authority_satisfied": False,
                    "settlement_authority": False,
                    "production_authority": False,
                    "error": str(exc),
                },
                sort_keys=True,
            )
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
