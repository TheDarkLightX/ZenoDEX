"""
Tau Net Testnet RPC client helpers (local node).

This module talks to the Tau Testnet Alpha node's TCP command interface
(`external/tau-testnet/server.py`) and constructs properly signed `sendtx`
payloads.
"""

from __future__ import annotations

import hashlib
import json
import re
import socket
import time
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional

from ..state.canonical import canonical_json_bytes, domain_sep_bytes

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None  # type: ignore[assignment]
    _BLS_AVAILABLE = False

try:
    # Used only for secret-key validation (range checks).
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except Exception:  # pragma: no cover - optional dependency
    _BLS12_381_CURVE_ORDER = None


class TauNetRpcError(RuntimeError):
    pass


@dataclass(frozen=True)
class TauNetTcpConfig:
    host: str = "127.0.0.1"
    port: int = 65432
    timeout_s: float = 3.0
    recv_max_bytes: int = 1_048_576


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise TauNetRpcError("py_ecc.bls is required for Tau tx signing (install py-ecc)")


def _parse_privkey_int(privkey: int) -> int:
    sk = int(privkey)
    if sk <= 0:
        raise ValueError("privkey must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return sk


def _parse_privkey_bytes(privkey: bytes | bytearray) -> int:
    raw = bytes(privkey)
    if len(raw) != 32:
        raise ValueError("privkey bytes must be length 32")
    sk = int.from_bytes(raw, byteorder="big", signed=False)
    return _parse_privkey_int(sk)


def _parse_privkey_hex_32_bytes(hex_str: str, *, label: str) -> bytes:
    if not re.fullmatch(r"[0-9a-fA-F]+", hex_str or ""):
        raise ValueError(f"{label} must contain only 0-9a-f")
    raw = bytes.fromhex(hex_str)
    if len(raw) != 32:
        raise ValueError(f"{label} must decode to 32 bytes, got {len(raw)}")
    return raw


def _parse_privkey_str(privkey: str) -> int:
    s = privkey.strip()
    if not s:
        raise ValueError("privkey must be non-empty")

    if s.lower().startswith("0x"):
        raw = _parse_privkey_hex_32_bytes(s[2:], label="privkey hex")
        return _parse_privkey_int(int.from_bytes(raw, byteorder="big", signed=False))

    # Accept bare 32-byte hex (64 chars), including digit-only keys.
    if len(s) == 64 and re.fullmatch(r"[0-9a-fA-F]+", s):
        return _parse_privkey_int(int.from_bytes(bytes.fromhex(s), byteorder="big", signed=False))

    if re.fullmatch(r"[0-9]+", s):
        return _parse_privkey_int(int(s, 10))

    raise ValueError("privkey must be 32-byte hex (0x... or 64 hex chars) or a positive integer string")


def _parse_privkey_to_int(privkey: str | int | bytes | bytearray) -> int:
    if isinstance(privkey, int):
        return _parse_privkey_int(privkey)
    if isinstance(privkey, (bytes, bytearray)):
        return _parse_privkey_bytes(privkey)
    if isinstance(privkey, str):
        return _parse_privkey_str(privkey)
    raise TypeError("privkey must be str|int|bytes")


def bls_pubkey_hex_from_privkey(privkey: str | int | bytes | bytearray) -> str:
    _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    return G2Basic.SkToPk(sk_int).hex()  # type: ignore[union-attr]


def _tx_signing_message_bytes(payload: Mapping[str, Any]) -> bytes:
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "operations": payload["operations"],
        "fee_limit": payload["fee_limit"],
    }
    return json.dumps(signing_dict, sort_keys=True, separators=(",", ":")).encode("utf-8")


def sign_tau_transaction_payload(payload_wo_sig: Dict[str, Any], *, privkey: str | int | bytes | bytearray) -> str:
    _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    msg_bytes = _tx_signing_message_bytes(payload_wo_sig)
    msg_hash = hashlib.sha256(msg_bytes).digest()
    sig_bytes = G2Basic.Sign(sk_int, msg_hash)  # type: ignore[union-attr]
    return sig_bytes.hex()


def build_signed_tau_transaction(
    *,
    privkey: str | int | bytes | bytearray,
    sequence_number: int,
    expiration_time: int,
    operations: Dict[str, Any],
    fee_limit: str | int = "0",
) -> Dict[str, Any]:
    _require_bls()
    sender_pubkey = bls_pubkey_hex_from_privkey(privkey)
    payload: Dict[str, Any] = {
        "sender_pubkey": sender_pubkey,
        "sequence_number": int(sequence_number),
        "expiration_time": int(expiration_time),
        "operations": dict(operations),
        "fee_limit": str(fee_limit),
    }
    payload["signature"] = sign_tau_transaction_payload(payload, privkey=privkey)
    return payload


def sign_dex_intent_for_engine(
    intent_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
) -> str:
    """
    Sign an intent according to `src.integration.dex_engine` signature policy.

    Returns a hex signature string with a `0x` prefix.
    """
    _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be a non-empty string")

    common = {"module", "version", "kind", "intent_id", "sender_pubkey", "deadline", "salt"}
    fields: Dict[str, Any] = {
        k: v for k, v in dict(intent_dict).items() if k not in common and k != "signature"
    }
    signing_dict: Dict[str, Any] = {
        "module": intent_dict.get("module"),
        "version": intent_dict.get("version"),
        "kind": intent_dict.get("kind"),
        "intent_id": intent_dict.get("intent_id"),
        "sender_pubkey": intent_dict.get("sender_pubkey"),
        "deadline": intent_dict.get("deadline"),
        "fields": fields,
    }
    salt = intent_dict.get("salt")
    if salt is not None:
        signing_dict["salt"] = salt

    signing_payload = canonical_json_bytes(signing_dict)
    msg = domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + signing_payload
    msg_hash = hashlib.sha256(msg).digest()
    sig_bytes = G2Basic.Sign(sk_int, msg_hash)  # type: ignore[union-attr]
    return "0x" + sig_bytes.hex()


def sign_perp_op_for_engine(
    op_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    """
    Sign a perps operation according to `src.integration.perp_engine` signature policy.

    The per-op signature is used for peer-to-peer authorization in clearinghouse markets
    (e.g. joint market init, matched position updates, oracle-authorized price publication).

    The signed message is:
    - domain-separated by `chain_id` (prevents cross-network replay),
    - encoded as canonical JSON (stable hash),
    - bound to `signer_pubkey` and a monotone `nonce` (replay protection).

    The exact fields included in the signed payload depend on `op_dict["action"]`
    and are defined by the engine's signing policy. This helper delegates to
    `src.integration.perp_engine._perp_op_signing_dict` to ensure both sides stay in sync.

    Returns a hex signature string with a `0x` prefix.
    """
    _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be a non-empty string")
    if not isinstance(signer_pubkey, str) or not signer_pubkey:
        raise ValueError("signer_pubkey must be a non-empty string")
    if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce <= 0:
        raise ValueError("nonce must be a positive int")

    from .perp_engine import _perp_op_signing_dict

    signing_dict = _perp_op_signing_dict(dict(op_dict), signer_pubkey=signer_pubkey, nonce=int(nonce))
    signing_payload = canonical_json_bytes(signing_dict)
    msg = domain_sep_bytes(f"perp_op_sig:{chain_id}", version=1) + signing_payload
    msg_hash = hashlib.sha256(msg).digest()
    sig_bytes = G2Basic.Sign(sk_int, msg_hash)  # type: ignore[union-attr]
    return "0x" + sig_bytes.hex()


class TauNetTcpClient:
    def __init__(self, config: TauNetTcpConfig = TauNetTcpConfig()) -> None:
        if not isinstance(config.port, int) or not (0 <= config.port <= 65535):
            raise ValueError("invalid port")
        if not isinstance(config.timeout_s, (int, float)) or config.timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if not isinstance(config.recv_max_bytes, int) or config.recv_max_bytes <= 0:
            raise ValueError("recv_max_bytes must be positive")
        self._cfg = config

    def rpc(self, cmd: str) -> str:
        if not isinstance(cmd, str) or not cmd.strip():
            raise ValueError("cmd must be a non-empty string")
        wire = cmd.strip()
        if not wire.endswith("\r\n"):
            wire += "\r\n"
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.settimeout(self._cfg.timeout_s)
            sock.connect((self._cfg.host, self._cfg.port))
            sock.sendall(wire.encode("utf-8"))
            buf = bytearray()
            remaining = self._cfg.recv_max_bytes
            while remaining > 0:
                try:
                    chunk = sock.recv(min(65536, remaining))
                except socket.timeout as exc:
                    partial = bytes(buf).decode("utf-8", errors="replace")
                    raise TauNetRpcError(
                        f"rpc timed out after {self._cfg.timeout_s}s waiting for response to {cmd!r}; partial={partial!r}"
                    ) from exc
                if not chunk:
                    break
                buf += chunk
                remaining -= len(chunk)
                if b"\n" in buf:
                    break

        # Tau Testnet's TCP server keeps connections open and terminates each response with a newline.
        if b"\n" in buf:
            line, _, _rest = bytes(buf).partition(b"\n")
            line = line.rstrip(b"\r")
            return line.decode("utf-8", errors="replace")

        # Fallback (unexpected): return what we got.
        return bytes(buf).decode("utf-8", errors="replace")

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        resp = self.rpc(f"getsequence {sender_pubkey_hex}").strip()
        if resp.startswith("SEQUENCE:"):
            _, v = resp.split(":", 1)
            return int(v.strip())
        raise TauNetRpcError(f"unexpected getsequence response: {resp!r}")

    def get_balance(self, address_hex: str) -> int:
        resp = self.rpc(f"getbalance {address_hex}").strip()
        if resp.startswith("BALANCE:"):
            _, v = resp.split(":", 1)
            return int(v.strip())
        raise TauNetRpcError(f"unexpected getbalance response: {resp!r}")

    def sendtx(self, payload: Mapping[str, Any]) -> str:
        blob = json.dumps(dict(payload), separators=(",", ":"), sort_keys=True)
        return self.rpc(f"sendtx '{blob}'").strip()

    def createblock(self) -> str:
        return self.rpc("createblock").strip()

    def getappstate(self, *, full: bool = False) -> str:
        return self.rpc("getappstate full" if full else "getappstate").strip()

    def getdexstate(self, *, full: bool = False) -> str:
        # Back-compat alias; Tau Testnet now exposes `getappstate`.
        return self.getappstate(full=full)

    def getstateproof(self, *, full: bool = False) -> str:
        return self.rpc("getstateproof full" if full else "getstateproof").strip()

    def send_signed_tx(
        self,
        *,
        privkey: str | int | bytes | bytearray,
        operations: Dict[str, Any],
        fee_limit: str | int = "0",
        expiration_seconds: int = 3600,
        sequence_number: Optional[int] = None,
    ) -> str:
        sender = bls_pubkey_hex_from_privkey(privkey)
        seq = int(sequence_number) if sequence_number is not None else self.get_sequence(sender)
        expiry = int(time.time()) + int(expiration_seconds)
        payload = build_signed_tau_transaction(
            privkey=privkey,
            sequence_number=seq,
            expiration_time=expiry,
            operations=operations,
            fee_limit=fee_limit,
        )
        return self.sendtx(payload)
