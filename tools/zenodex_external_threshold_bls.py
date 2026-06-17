#!/usr/bin/env python3
"""CLI client for the external threshold-BLS signer contract."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenodex_external_threshold_bls import (  # noqa: E402
    build_external_threshold_bls_sign_request_v0,
    run_external_threshold_bls_signer_v0,
    validate_external_threshold_bls_evidence_v0,
    validate_external_threshold_bls_sign_request_v0,
    validate_external_threshold_bls_signer_artifact_v0,
    verify_external_threshold_bls_signature_receipt_v0,
)


def _load_json_arg(value: str) -> Any:
    path = Path(value)
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return json.loads(value)


def _load_mapping(value: str, *, name: str) -> Mapping[str, Any]:
    payload = _load_json_arg(value)
    if not isinstance(payload, Mapping):
        raise ValueError(f"{name} must decode to a JSON object")
    return payload


def _write_or_print(payload: Mapping[str, Any], *, out: str | None) -> None:
    text = json.dumps(dict(payload), indent=2, sort_keys=True) + "\n"
    if out is None:
        print(text, end="")
        return
    Path(out).write_text(text, encoding="utf-8")


def _command_tail(args: list[str]) -> list[str]:
    tail = list(args)
    if tail and tail[0] == "--":
        tail = tail[1:]
    if not tail:
        raise ValueError("signer command is required after --")
    return tail


def _build_request(args: argparse.Namespace) -> dict[str, Any]:
    evidence = _load_mapping(args.evidence, name="evidence")
    payload = _load_mapping(args.payload_json, name="payload-json")
    validate_external_threshold_bls_evidence_v0(evidence)
    request = build_external_threshold_bls_sign_request_v0(
        key_id=args.key_id,
        evidence_hash=str(evidence["evidence_hash"]),
        payload=payload,
    )
    validate_external_threshold_bls_sign_request_v0(request)
    return request


def _cmd_request(args: argparse.Namespace) -> int:
    _write_or_print(_build_request(args), out=args.out)
    return 0


def _cmd_sign(args: argparse.Namespace) -> int:
    evidence = _load_mapping(args.evidence, name="evidence")
    payload = _load_mapping(args.payload_json, name="payload-json")
    validate_external_threshold_bls_signer_artifact_v0(
        evidence=evidence,
        signer_artifact_path=Path(args.signer_artifact),
    )
    request = build_external_threshold_bls_sign_request_v0(
        key_id=args.key_id,
        evidence_hash=str(evidence["evidence_hash"]),
        payload=payload,
    )
    receipt = run_external_threshold_bls_signer_v0(
        command=_command_tail(args.signer_command),
        request=request,
        timeout_s=args.timeout_s,
        max_stdout_bytes=args.max_stdout_bytes,
    )
    ok, err = verify_external_threshold_bls_signature_receipt_v0(receipt, evidence=evidence, payload=payload)
    if not ok:
        print(f"error: external threshold BLS signer receipt rejected: {err}", file=sys.stderr)
        return 1
    _write_or_print(receipt, out=args.out)
    return 0


def _cmd_verify(args: argparse.Namespace) -> int:
    evidence = _load_mapping(args.evidence, name="evidence")
    payload = _load_mapping(args.payload_json, name="payload-json")
    receipt = _load_mapping(args.receipt, name="receipt")
    ok, err = verify_external_threshold_bls_signature_receipt_v0(receipt, evidence=evidence, payload=payload)
    report = {
        "schema": "zenodex/external_threshold_bls/verify_cli_receipt/v0",
        "ok": ok,
        "error": err,
        "receipt_hash": receipt.get("receipt_hash"),
    }
    _write_or_print(report, out=args.out)
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    request = sub.add_parser("request", help="build a canonical external signer request")
    request.add_argument("--key-id", required=True)
    request.add_argument("--evidence", required=True)
    request.add_argument("--payload-json", required=True)
    request.add_argument("--out")
    request.set_defaults(func=_cmd_request)

    sign = sub.add_parser("sign", help="run an external signer command and verify its receipt")
    sign.add_argument("--key-id", required=True)
    sign.add_argument("--evidence", required=True)
    sign.add_argument("--payload-json", required=True)
    sign.add_argument("--signer-artifact", required=True)
    sign.add_argument("--timeout-s", type=float, default=30.0)
    sign.add_argument("--max-stdout-bytes", type=int, default=256_000)
    sign.add_argument("--out")
    sign.add_argument("signer_command", nargs=argparse.REMAINDER)
    sign.set_defaults(func=_cmd_sign)

    verify = sub.add_parser("verify", help="verify an external threshold-BLS signature receipt")
    verify.add_argument("--evidence", required=True)
    verify.add_argument("--payload-json", required=True)
    verify.add_argument("--receipt", required=True)
    verify.add_argument("--out")
    verify.set_defaults(func=_cmd_verify)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
