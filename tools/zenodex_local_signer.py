#!/usr/bin/env python3
"""Create and use a browser-independent ZenoDEX local signer vault."""

from __future__ import annotations

import argparse
import getpass
import hmac
import ipaddress
import json
import secrets
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0  # noqa: E402
from src.integration.zenodex_local_signer import (  # noqa: E402
    RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR,
    create_local_signer_vault,
    read_local_signer_vault,
    verify_local_signer_dex_signature_receipt,
    verify_local_signer_public_receipt,
    write_local_signer_vault,
)


def _read_passphrase(*, passphrase_stdin: bool) -> str:
    if passphrase_stdin:
        return sys.stdin.readline().rstrip("\n")
    first = getpass.getpass("Passphrase: ")
    second = getpass.getpass("Confirm passphrase: ")
    if first != second:
        raise ValueError("passphrases do not match")
    return first


def _read_unlock_passphrase(*, passphrase_stdin: bool) -> str:
    if passphrase_stdin:
        return sys.stdin.readline().rstrip("\n")
    return getpass.getpass("Passphrase: ")


def _read_json_arg(raw: str) -> dict[str, Any]:
    candidate = Path(raw)
    if candidate.exists():
        data = candidate.read_text(encoding="utf-8")
    else:
        data = raw
    value = json.loads(data)
    if not isinstance(value, dict):
        raise TypeError("JSON input must be an object")
    return value


def _print_json(value: object) -> None:
    sys.stdout.buffer.write(canonical_json_bytes_v0(value) + b"\n")


def _is_loopback_host(host: str) -> bool:
    text = str(host or "").strip().lower()
    if text == "localhost":
        return True
    try:
        return ipaddress.ip_address(text).is_loopback
    except ValueError:
        return False


def _approval_summary(*, kind: str, chain_id: str, payload: dict[str, Any]) -> dict[str, Any]:
    request = {
        "schema": "zenodex/local_signer/approval_request/v0",
        "kind": kind,
        "chain_id": chain_id,
        "payload": payload,
    }
    summary: dict[str, Any] = {
        "schema": "zenodex/local_signer/approval_summary/v0",
        "kind": kind,
        "chain_id": chain_id,
        "request_hash": hash_v0("local_signer_approval_request_v0", request),
    }
    if kind == "tau_transaction":
        operations = dict(payload.get("operations") or {})
        summary.update(
            {
                "sender_pubkey": payload.get("sender_pubkey"),
                "sequence_number": payload.get("sequence_number"),
                "expiration_time": payload.get("expiration_time"),
                "fee_limit": str(payload.get("fee_limit", "0")),
                "operation_count": len(operations),
                "operation_streams": sorted(str(key) for key in operations.keys()),
                "operations": operations,
            }
        )
    elif kind == "dex_intent":
        fields = payload.get("fields")
        if not isinstance(fields, dict):
            common = {"module", "version", "kind", "intent_id", "sender_pubkey", "deadline", "salt", "signature"}
            fields = {key: value for key, value in payload.items() if key not in common}
        summary.update(
            {
                "sender_pubkey": payload.get("sender_pubkey"),
                "module": payload.get("module"),
                "kind": payload.get("kind"),
                "intent_id": payload.get("intent_id"),
                "deadline": payload.get("deadline"),
                "nonce": fields.get("nonce"),
                "recipient": fields.get("recipient"),
                "fields": fields,
            }
        )
    return summary


def cmd_create(args: argparse.Namespace) -> int:
    vault = create_local_signer_vault(
        key_id=args.key_id,
        passphrase=_read_passphrase(passphrase_stdin=args.passphrase_stdin),
        chain_id=args.chain_id,
        allowed_chain_ids=tuple(args.allowed_chain_id or (args.chain_id,)),
        label=args.label,
        created_at_epoch=args.created_at_epoch,
    )
    write_local_signer_vault(args.vault, vault, overwrite=args.overwrite)
    receipt = vault.public_receipt()
    ok, err = verify_local_signer_public_receipt(receipt)
    if not ok:
        raise RuntimeError(err or "public receipt verification failed")
    _print_json(receipt)
    return 0


def cmd_import(args: argparse.Namespace) -> int:
    vault = create_local_signer_vault(
        key_id=args.key_id,
        passphrase=_read_passphrase(passphrase_stdin=args.passphrase_stdin),
        chain_id=args.chain_id,
        allowed_chain_ids=tuple(args.allowed_chain_id or (args.chain_id,)),
        label=args.label,
        created_at_epoch=args.created_at_epoch,
        private_key_hex=args.private_key_hex,
    )
    write_local_signer_vault(args.vault, vault, overwrite=args.overwrite)
    receipt = vault.public_receipt()
    ok, err = verify_local_signer_public_receipt(receipt)
    if not ok:
        raise RuntimeError(err or "public receipt verification failed")
    _print_json(receipt)
    return 0


def cmd_receipt(args: argparse.Namespace) -> int:
    vault = read_local_signer_vault(args.vault)
    receipt = vault.public_receipt()
    ok, err = verify_local_signer_public_receipt(receipt)
    if not ok:
        raise RuntimeError(err or "public receipt verification failed")
    _print_json(receipt)
    return 0


def cmd_sign_dex_intent(args: argparse.Namespace) -> int:
    vault = read_local_signer_vault(args.vault)
    intent = _read_json_arg(args.intent_json)
    receipt = vault.sign_dex_intent(
        passphrase=_read_unlock_passphrase(passphrase_stdin=args.passphrase_stdin),
        intent=intent,
        chain_id=args.chain_id,
    )
    ok, err = verify_local_signer_dex_signature_receipt(receipt, intent=intent)
    if not ok:
        raise RuntimeError(err or "signature receipt verification failed")
    _print_json(receipt)
    return 0


def cmd_sign_tau_transaction_payload(args: argparse.Namespace) -> int:
    raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)


class _LocalSignerHttpHandler(BaseHTTPRequestHandler):
    server_version = "ZenoDEXLocalSigner/0"

    def log_message(self, fmt: str, *args: object) -> None:
        if getattr(self.server, "quiet", False):
            return
        super().log_message(fmt, *args)

    def _cors_origin(self) -> str | None:
        origin = self.headers.get("Origin")
        allowed = getattr(self.server, "allowed_origins", set())
        if origin and origin in allowed:
            return origin
        return None

    def _reject_disallowed_origin(self, *, require_origin: bool) -> bool:
        origin = self.headers.get("Origin")
        allowed = getattr(self.server, "allowed_origins", set())
        if require_origin and not origin:
            self._write_json(403, {"ok": False, "error": "origin_required"})
            return True
        if origin and origin not in allowed:
            self._write_json(403, {"ok": False, "error": "origin_not_allowed"})
            return True
        return False

    def _reject_missing_pairing_token(self) -> bool:
        expected = getattr(self.server, "pairing_token", "")
        observed = self.headers.get("X-ZenoDEX-Signer-Token") or ""
        if not expected or not hmac.compare_digest(str(expected), str(observed)):
            self._write_json(403, {"ok": False, "error": "signer_pairing_token_required"})
            return True
        return False

    def _write_json(self, status: int, value: object) -> None:
        data = canonical_json_bytes_v0(value) + b"\n"
        self.send_response(status)
        self.send_header("content-type", "application/json")
        self.send_header("content-length", str(len(data)))
        origin = self._cors_origin()
        if origin:
            self.send_header("access-control-allow-origin", origin)
            self.send_header("vary", "Origin")
        self.end_headers()
        self.wfile.write(data)

    def _write_options(self) -> None:
        self.send_response(204)
        origin = self._cors_origin()
        if origin:
            self.send_header("access-control-allow-origin", origin)
            self.send_header("vary", "Origin")
        self.send_header("access-control-allow-methods", "GET, POST, OPTIONS")
        self.send_header("access-control-allow-headers", "content-type, x-zenodex-signer-token")
        self.send_header("content-length", "0")
        self.end_headers()

    def _read_json_body(self) -> dict[str, Any]:
        raw_length = self.headers.get("content-length", "0")
        try:
            length = int(raw_length)
        except ValueError as exc:
            raise ValueError("invalid content-length") from exc
        if length < 0 or length > 1_000_000:
            raise ValueError("request body size out of range")
        data = self.rfile.read(length)
        value = json.loads(data.decode("utf-8") or "{}")
        if not isinstance(value, dict):
            raise TypeError("request body must be a JSON object")
        return value

    def _require_approval(self, *, kind: str, chain_id: str, payload: dict[str, Any]) -> None:
        mode = getattr(self.server, "approval_mode", "prompt")
        if mode == "unattended":
            return
        if mode != "prompt":
            raise PermissionError("signing_approval_mode_unsupported")
        summary = _approval_summary(kind=kind, chain_id=chain_id, payload=payload)
        lock = self.server.approval_lock  # type: ignore[attr-defined]
        approval_input = self.server.approval_input  # type: ignore[attr-defined]
        with lock:
            print("ZenoDEX local signer approval requested:", file=sys.stderr)
            print(json.dumps(summary, indent=2, sort_keys=True), file=sys.stderr)
            print("Type 'approve' to sign: ", end="", file=sys.stderr, flush=True)
            answer = approval_input.readline()
            if answer.strip() != "approve":
                raise PermissionError("signing_request_rejected")

    def do_OPTIONS(self) -> None:
        self._write_options()

    def do_GET(self) -> None:
        vault = self.server.vault  # type: ignore[attr-defined]
        chain_id = self.server.chain_id  # type: ignore[attr-defined]
        if self.path == "/health":
            self._write_json(200, {"ok": True, "provider": "zenodex-local-signer-v0"})
            return
        if self.path == "/public-receipt":
            receipt = vault.public_receipt(
                approval_mode=getattr(self.server, "approval_mode", "prompt"),
                signer_user_approval_required=getattr(self.server, "approval_mode", "prompt") == "prompt",
                browser_bridge_auth_required=True,
            )
            self._write_json(
                200,
                {
                    "ok": True,
                    "wallet": {
                        "address": vault.public_key,
                        "chainId": chain_id,
                        "signerProvider": "zenodex-local-signer-v0",
                        "publicReceipt": receipt,
                    },
                },
            )
            return
        self._write_json(404, {"ok": False, "error": "not_found"})

    def do_POST(self) -> None:
        if self._reject_disallowed_origin(require_origin=True):
            return
        if urlsplit(self.path).path == "/sign-tau-transaction-payload":
            self._write_json(
                410,
                {
                    "ok": False,
                    "error": RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR,
                },
            )
            return
        vault = self.server.vault  # type: ignore[attr-defined]
        passphrase = self.server.passphrase  # type: ignore[attr-defined]
        default_chain_id = self.server.chain_id  # type: ignore[attr-defined]
        try:
            body = self._read_json_body()
            chain_id = str(body.get("chainId") or body.get("chain_id") or default_chain_id)
            if self.path == "/public-receipt":
                receipt = vault.public_receipt(
                    approval_mode=getattr(self.server, "approval_mode", "prompt"),
                    signer_user_approval_required=getattr(self.server, "approval_mode", "prompt") == "prompt",
                    browser_bridge_auth_required=True,
                )
                self._write_json(
                    200,
                    {
                        "ok": True,
                        "signerPairingToken": self.server.pairing_token,  # type: ignore[attr-defined]
                        "wallet": {
                            "address": vault.public_key,
                            "chainId": chain_id,
                            "signerProvider": "zenodex-local-signer-v0",
                            "publicReceipt": receipt,
                        },
                    },
                )
                return
            if self.path == "/sign-dex-intent":
                if self._reject_missing_pairing_token():
                    return
                intent = body.get("intent")
                if not isinstance(intent, dict):
                    raise TypeError("intent must be a JSON object")
                self._require_approval(kind="dex_intent", chain_id=chain_id, payload=intent)
                receipt = vault.sign_dex_intent(
                    passphrase=passphrase,
                    intent=intent,
                    chain_id=chain_id,
                )
                self._write_json(200, {"ok": True, "signature": receipt["signature"], "signature_receipt": receipt})
                return
            self._write_json(404, {"ok": False, "error": "not_found"})
        except Exception as exc:
            self._write_json(400, {"ok": False, "error": str(exc)})


def cmd_serve(args: argparse.Namespace) -> int:
    vault = read_local_signer_vault(args.vault)
    if not _is_loopback_host(args.host):
        raise ValueError("serve host must be loopback")
    if args.approval_mode == "unattended" and not args.i_understand_unattended_signing:
        raise ValueError("unattended signing requires --i-understand-unattended-signing")
    passphrase = _read_unlock_passphrase(passphrase_stdin=args.passphrase_stdin)
    chain_id = args.chain_id or vault.chain_id
    # Fail fast on a bad passphrase before binding a local signing endpoint.
    vault.require_valid_passphrase(passphrase)
    allowed_origins = set(args.cors_origin or ["http://127.0.0.1:5173", "http://localhost:5173"])
    server = ThreadingHTTPServer((args.host, args.port), _LocalSignerHttpHandler)
    server.vault = vault
    server.passphrase = passphrase
    server.chain_id = chain_id
    server.allowed_origins = allowed_origins
    server.approval_mode = args.approval_mode
    server.pairing_token = secrets.token_urlsafe(32)
    server.approval_input = sys.stdin
    server.approval_lock = threading.Lock()
    server.quiet = args.quiet
    if not args.quiet:
        print(
            f"zenodex-local-signer serving on http://{args.host}:{server.server_address[1]}",
            file=sys.stderr,
        )
        if args.approval_mode == "prompt":
            print("signing approval mode: prompt", file=sys.stderr)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        return 0
    finally:
        server.server_close()
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    create = sub.add_parser("create", help="create an encrypted local signer vault")
    create.add_argument("--vault", required=True, type=Path)
    create.add_argument("--key-id", required=True)
    create.add_argument("--chain-id", required=True)
    create.add_argument("--allowed-chain-id", action="append", default=[])
    create.add_argument("--label")
    create.add_argument("--created-at-epoch", type=int)
    create.add_argument("--overwrite", action="store_true")
    create.add_argument("--passphrase-stdin", action="store_true")
    create.set_defaults(func=cmd_create)

    import_cmd = sub.add_parser("import", help="import an existing private key into an encrypted local signer vault")
    import_cmd.add_argument("--vault", required=True, type=Path)
    import_cmd.add_argument("--key-id", required=True)
    import_cmd.add_argument("--chain-id", required=True)
    import_cmd.add_argument("--private-key-hex", required=True)
    import_cmd.add_argument("--allowed-chain-id", action="append", default=[])
    import_cmd.add_argument("--label")
    import_cmd.add_argument("--created-at-epoch", type=int)
    import_cmd.add_argument("--overwrite", action="store_true")
    import_cmd.add_argument("--passphrase-stdin", action="store_true")
    import_cmd.set_defaults(func=cmd_import)

    receipt = sub.add_parser("receipt", help="print the public receipt for a vault")
    receipt.add_argument("--vault", required=True, type=Path)
    receipt.set_defaults(func=cmd_receipt)

    sign = sub.add_parser("sign-dex-intent", help="sign a DEX intent JSON object")
    sign.add_argument("--vault", required=True, type=Path)
    sign.add_argument("--chain-id", required=True)
    sign.add_argument("--intent-json", required=True)
    sign.add_argument("--passphrase-stdin", action="store_true")
    sign.set_defaults(func=cmd_sign_dex_intent)

    sign_tau = sub.add_parser(
        "sign-tau-transaction-payload",
        help="refuse the retired historical Tau transaction signing route",
    )
    sign_tau.add_argument("--vault", required=True, type=Path)
    sign_tau.add_argument("--chain-id", required=True)
    sign_tau.add_argument("--payload-json", required=True)
    sign_tau.add_argument("--passphrase-stdin", action="store_true")
    sign_tau.set_defaults(func=cmd_sign_tau_transaction_payload)

    serve = sub.add_parser("serve", help="serve a loopback HTTP signer bridge for the encrypted vault")
    serve.add_argument("--vault", required=True, type=Path)
    serve.add_argument("--chain-id")
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8799)
    serve.add_argument("--cors-origin", action="append", default=[])
    serve.add_argument("--approval-mode", choices=("prompt", "unattended"), default="prompt")
    serve.add_argument("--i-understand-unattended-signing", action="store_true")
    serve.add_argument("--passphrase-stdin", action="store_true")
    serve.add_argument("--quiet", action="store_true")
    serve.set_defaults(func=cmd_serve)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return int(args.func(args))
    except Exception as exc:
        print(f"zenodex-local-signer: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
