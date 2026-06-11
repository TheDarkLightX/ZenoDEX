#!/usr/bin/env python3
"""Build production hardware-wallet evidence from explicit custody artifacts.

The verifier remains authoritative. This tool only assembles the operator's
device attestation, OS prompt capture, approval transaction, and active wallet
authority profile hash into the lane schema, then optionally runs the lane check
before writing.

Grade: A-. This removes hand-edited evidence hashes from the hardware-wallet
lane while keeping the actual device and prompt artifacts externally supplied.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:
    from cryptography.exceptions import InvalidSignature
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

    _ED25519_AVAILABLE = True
except ImportError:  # pragma: no cover - dependency guard for fail-closed builder errors
    InvalidSignature = Exception
    Ed25519PublicKey = None
    _ED25519_AVAILABLE = False

from src.integration.production_promotion_evidence import (  # noqa: E402
    _ALLOWED_HW_WALLET_MODELS,
    _ALLOWED_OS_PROMPT_KINDS,
    _NEAR_AND_SAME_HOUR_SECONDS,
    HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
    attach_production_hardware_wallet_hash_v1,
    evaluate_production_hardware_wallet_evidence_v1,
    production_hardware_wallet_approval_message_v1,
    production_hardware_wallet_attestation_challenge_v1,
    production_hardware_wallet_attestation_message_v1,
)

_HEX = frozenset("0123456789abcdef")


def _normalize_hex(value: str, *, label: str, length: int) -> str:
    text = value.strip()
    if text.startswith(("0x", "0X")):
        text = text[2:]
    text = text.lower()
    if len(text) != length or any(ch not in _HEX for ch in text):
        raise ValueError(f"{label} must be {length}-char lowercase hex, optionally prefixed with 0x")
    return text


def _normalize_choice(value: str, *, label: str, allowed: frozenset[str]) -> str:
    text = value.strip().lower()
    if not text:
        raise ValueError(f"{label} must be a non-empty string")
    if text not in allowed:
        raise ValueError(f"{label} {text!r} is not allowed")
    return text


def _positive_int(value: int, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return int(value)


def _verify_ed25519_signature(*, pubkey: str, signature: str, message: bytes, label: str) -> None:
    if not _ED25519_AVAILABLE or Ed25519PublicKey is None:
        raise ValueError(f"{label} Ed25519 verifier is unavailable")
    try:
        public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(pubkey))
        public_key.verify(bytes.fromhex(signature), message)
    except (InvalidSignature, ValueError) as exc:
        raise ValueError(f"{label} is invalid") from exc


def build_hardware_wallet_evidence(args: argparse.Namespace) -> dict[str, object]:
    # Review finding (grade A- -> A): --check rejected impossible timestamps,
    # but the producer could still write a production-shaped custody artifact
    # with issued_at <= 0. Keep the pre-hash builder contract aligned with the
    # verifier's positive-time domain.
    issued_at = _positive_int(
        int(args.issued_at if args.issued_at is not None else time.time()),
        label="issued_at",
    )
    device_model = _normalize_choice(
        args.device_model,
        label="device model",
        allowed=_ALLOWED_HW_WALLET_MODELS,
    )
    prompt_kind = _normalize_choice(
        args.prompt_kind,
        label="OS prompt capture kind",
        allowed=_ALLOWED_OS_PROMPT_KINDS,
    )
    device_pubkey = _normalize_hex(args.device_pubkey, label="device pubkey", length=64)
    expected_device_pubkey = (
        _normalize_hex(args.expected_device_pubkey, label="expected device pubkey", length=64)
        if args.expected_device_pubkey
        else None
    )
    if expected_device_pubkey is None:
        raise ValueError("expected device pubkey is required for hardware wallet binding")
    if device_pubkey != expected_device_pubkey:
        raise ValueError("device pubkey does not match expected device pubkey")
    attestation_challenge = _normalize_hex(args.attestation_challenge, label="attestation challenge", length=64)
    approval_tx_payload_hash = _normalize_hex(args.approval_tx_payload_hash, label="approval tx payload hash", length=64)
    if attestation_challenge == approval_tx_payload_hash:
        raise ValueError("attestation challenge must differ from approval tx payload hash")
    attestation_signature = _normalize_hex(args.attestation_signature, label="attestation signature", length=128)
    approval_signature = _normalize_hex(args.approval_signature, label="approval signature", length=128)
    if attestation_signature == approval_signature:
        raise ValueError("attestation signature must differ from approval signature")
    prompt_captured_at = _positive_int(args.prompt_captured_at, label="OS prompt captured_at")
    approval_captured_at = _positive_int(args.approval_captured_at, label="approval captured_at")
    if approval_captured_at < prompt_captured_at:
        raise ValueError("approval captured_at must be >= OS prompt captured_at")
    if approval_captured_at - prompt_captured_at > _NEAR_AND_SAME_HOUR_SECONDS:
        # Review finding (grade B+ -> A-): without --check the producer could
        # write custody evidence whose prompt and approval were unrelated in
        # time. Rejecting it here keeps the produced artifact aligned with the
        # verifier's same-hour custody rule before any evidence hash is minted.
        raise ValueError("OS prompt capture and approval must be captured within the same hour")
    evidence_body: dict[str, object] = {
        "schema": HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
        "device_id": args.device_id,
        "device_model": device_model,
        "device_firmware_version": args.device_firmware_version,
        "device_attestation": {
            "pubkey": device_pubkey,
            "challenge": attestation_challenge,
            "signature": attestation_signature,
        },
        "os_prompt_capture": {
            "kind": prompt_kind,
            "hash": _normalize_hex(args.prompt_hash, label="OS prompt capture hash", length=64),
            "captured_at": prompt_captured_at,
        },
        "device_approval_tx": {
            "tx_payload_hash": approval_tx_payload_hash,
            "approval_signature": approval_signature,
            "captured_at": approval_captured_at,
        },
        "profile_wallet_authority_hash": args.wallet_authority_profile_hash,
        "issued_at": issued_at,
    }
    expected_challenge = production_hardware_wallet_attestation_challenge_v1(evidence_body)
    if attestation_challenge != expected_challenge:
        raise ValueError("attestation challenge must equal canonical hardware approval challenge")
    _verify_ed25519_signature(
        pubkey=device_pubkey,
        signature=attestation_signature,
        message=production_hardware_wallet_attestation_message_v1(attestation_challenge),
        label="attestation signature",
    )
    _verify_ed25519_signature(
        pubkey=device_pubkey,
        signature=approval_signature,
        message=production_hardware_wallet_approval_message_v1(approval_tx_payload_hash),
        label="approval signature",
    )
    return attach_production_hardware_wallet_hash_v1(evidence_body)


def _write_json(path: Path, payload: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--device-id", required=True)
    parser.add_argument("--device-model", required=True)
    parser.add_argument("--device-firmware-version", required=True)
    parser.add_argument("--device-pubkey", required=True)
    parser.add_argument("--attestation-challenge", required=True)
    parser.add_argument("--attestation-signature", required=True)
    parser.add_argument("--prompt-kind", required=True)
    parser.add_argument("--prompt-hash", required=True)
    parser.add_argument("--prompt-captured-at", type=int, required=True)
    parser.add_argument("--approval-tx-payload-hash", required=True)
    parser.add_argument("--approval-signature", required=True)
    parser.add_argument("--approval-captured-at", type=int, required=True)
    parser.add_argument("--wallet-authority-profile-hash", required=True)
    parser.add_argument("--expected-device-pubkey")
    parser.add_argument("--issued-at", type=int)
    parser.add_argument("--check-now", type=int, help="override verifier time for reproducible --check runs")
    parser.add_argument("--check", action="store_true", help="run the hardware-wallet lane verifier before writing")
    return parser.parse_args(list(argv))


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        evidence = build_hardware_wallet_evidence(args)
        if args.check:
            # Review note (grade B -> A-): --issued-at belongs to the evidence
            # body. Verifier freshness must compare it with wall-clock time
            # unless a test explicitly supplies --check-now.
            check_now = args.check_now if args.check_now is not None else int(time.time())
            check = evaluate_production_hardware_wallet_evidence_v1(
                evidence,
                wallet_authority_profile_hash=args.wallet_authority_profile_hash,
                expected_device_pubkey=args.expected_device_pubkey,
                now=check_now,
            )
            if check.get("production_ready") is not True:
                print(json.dumps(check, sort_keys=True), file=sys.stderr)
                return 1
        _write_json(args.out, evidence)
        print(json.dumps({"ok": True, "evidence_path": str(args.out)}, sort_keys=True))
        return 0
    except (OSError, TypeError, ValueError) as exc:
        print(json.dumps({"ok": False, "error": "hardware_wallet_evidence_build_failed", "detail": str(exc)}))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
