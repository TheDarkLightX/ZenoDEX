#!/usr/bin/env python3
"""Local ZenoKeyManager v0 CLI."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_key_import_v0 import build_tau_import_challenge_v0, import_tau_bls_key_descriptor_v0
from src.integration.zeno_key_manager import KeyRef, KeyUsePolicy, SignRequestContext, TauNetKeyImportEvidence
from src.integration.zeno_key_manager_v0 import (
    BACKEND_TAU_BLS_IMPORT,
    KeyBackendDescriptor,
    SignAdmissionRequest,
    evaluate_sign_admission_v0,
)


def _load_json_arg(value: str) -> Any:
    path = Path(value)
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return json.loads(value)


def _cmd_tau_challenge(args: argparse.Namespace) -> int:
    packet = build_tau_import_challenge_v0(
        key_id=args.key_ref,
        tau_chain_id=args.tau_chain_id,
        policy_hash=args.policy_hash,
        nonce=args.nonce,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))
    return 0


def _cmd_tau_import(args: argparse.Namespace) -> int:
    evidence = TauNetKeyImportEvidence(
        key_id=args.key_ref,
        tau_public_key=args.tau_public_key,
        tau_chain_id=args.tau_chain_id,
        tau_account_id=args.tau_account_id,
        challenge_hash=args.challenge_hash,
        challenge_signature_hash=args.challenge_signature_hash,
        policy_hash=args.policy_hash,
        verified_at_epoch=args.verified_at_epoch,
        expires_at_epoch=args.expires_at_epoch,
    )
    receipt = import_tau_bls_key_descriptor_v0(
        evidence=evidence,
        current_epoch=args.current_epoch,
        metadata={"label": args.label} if args.label else None,
    )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


def _cmd_sign_check(args: argparse.Namespace) -> int:
    key_ref = KeyRef.from_public_dict(_load_json_arg(args.key_ref_json))
    payload = _load_json_arg(args.payload_json)
    if not isinstance(payload, dict):
        raise ValueError("payload-json must decode to an object")
    policy = KeyUsePolicy(
        allowed_payload_kinds=tuple(args.allowed_payload_kind),
        allowed_chain_ids=tuple(args.allowed_chain_id),
        allowed_purposes=tuple(args.allowed_purpose),
        valid_from_epoch=args.valid_from_epoch,
        valid_until_epoch=args.valid_until_epoch,
    )
    context = SignRequestContext(
        payload_kind=args.payload_kind,
        chain_id=args.chain_id,
        purpose=args.purpose,
        current_epoch=args.current_epoch,
    )
    backend = KeyBackendDescriptor(
        key_id=key_ref.key_id,
        backend_kind=args.backend_kind,
        backend_id=args.backend_id,
        policy_hash=args.backend_policy_hash,
        active=not args.backend_inactive,
        no_raw_private_key_exposure=not args.allow_raw_private_key_exposure,
    )
    receipt = evaluate_sign_admission_v0(
        SignAdmissionRequest(
            key_ref=key_ref,
            backend=backend,
            policy=policy,
            context=context,
            payload=payload,
            seen_nonces=tuple(args.seen_nonce),
        )
    )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if receipt["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    tau_challenge = sub.add_parser("tau-challenge", help="build a Tau key-import challenge")
    tau_challenge.add_argument("--key-ref", required=True)
    tau_challenge.add_argument("--tau-chain-id", required=True)
    tau_challenge.add_argument("--policy-hash", required=True)
    tau_challenge.add_argument("--nonce", required=True)
    tau_challenge.set_defaults(func=_cmd_tau_challenge)

    tau_import = sub.add_parser("tau-import", help="import a Tau BLS public key with challenge evidence")
    tau_import.add_argument("--key-ref", required=True)
    tau_import.add_argument("--tau-public-key", required=True)
    tau_import.add_argument("--tau-chain-id", required=True)
    tau_import.add_argument("--tau-account-id")
    tau_import.add_argument("--challenge-hash", required=True)
    tau_import.add_argument("--challenge-signature-hash", required=True)
    tau_import.add_argument("--policy-hash", required=True)
    tau_import.add_argument("--verified-at-epoch", type=int, required=True)
    tau_import.add_argument("--expires-at-epoch", type=int, required=True)
    tau_import.add_argument("--current-epoch", type=int, required=True)
    tau_import.add_argument("--label")
    tau_import.set_defaults(func=_cmd_tau_import)

    sign_check = sub.add_parser("sign-check", help="evaluate local signing admission without signing")
    sign_check.add_argument("--key-ref-json", required=True, help="JSON object or path")
    sign_check.add_argument("--payload-json", required=True, help="JSON object or path")
    sign_check.add_argument("--payload-kind", required=True)
    sign_check.add_argument("--chain-id", required=True)
    sign_check.add_argument("--purpose", default="sign")
    sign_check.add_argument("--current-epoch", type=int, required=True)
    sign_check.add_argument("--allowed-payload-kind", action="append", required=True)
    sign_check.add_argument("--allowed-chain-id", action="append", required=True)
    sign_check.add_argument("--allowed-purpose", action="append", default=["sign"])
    sign_check.add_argument("--valid-from-epoch", type=int, default=0)
    sign_check.add_argument("--valid-until-epoch", type=int)
    sign_check.add_argument("--backend-kind", default=BACKEND_TAU_BLS_IMPORT)
    sign_check.add_argument("--backend-id", default="local-backend")
    sign_check.add_argument("--backend-policy-hash", required=True)
    sign_check.add_argument("--backend-inactive", action="store_true")
    sign_check.add_argument("--allow-raw-private-key-exposure", action="store_true")
    sign_check.add_argument("--seen-nonce", type=int, action="append", default=[])
    sign_check.set_defaults(func=_cmd_sign_check)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
