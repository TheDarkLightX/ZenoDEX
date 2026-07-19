"""Production-safe Tau TCP transport and signed-payload verification.

This module is deliberately incapable of constructing signatures, accepting
private keys, or producing blocks.  Production wallet handlers use it only to
read Tau state, encode already-prepared operation streams, verify externally
signed transactions, and submit those transactions to ``sendtx``.

Local development signing helpers live under :mod:`src.nonproduction` and are
removed before the production runtime tree enters the final OCI image.
"""

from __future__ import annotations

import hashlib
import json
import re
import socket
from dataclasses import dataclass
from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes

try:
    from py_ecc.bls import G2Basic

    _BLS_VERIFIER_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_VERIFIER_AVAILABLE = False


class TauNetRpcError(RuntimeError):
    """Raised when Tau's bounded TCP request/response contract fails."""


@dataclass(frozen=True)
class TauNetTcpConfig:
    host: str = "127.0.0.1"
    port: int = 65432
    timeout_s: float = 3.0
    recv_max_bytes: int = 1_048_576


_DEFAULT_TAU_NET_TCP_CONFIG = TauNetTcpConfig()
_SAFE_RPC_COMMANDS = frozenset(
    {"getappstate", "getbalance", "getsequence", "getstateproof", "sendtx"}
)


def tau_rpc_response_is_success(response: object) -> bool:
    """Return true only for Tau RPC responses that explicitly report success."""

    if not isinstance(response, str):
        return False
    text = response.strip().upper()
    return text == "SUCCESS" or text.startswith("SUCCESS:") or text.startswith("SUCCESS ")


def tau_rpc_invalid_sequence_numbers(response: object) -> tuple[int, int] | None:
    """Parse Tau's invalid-sequence response as ``(expected, got)`` when present."""

    if not isinstance(response, str):
        return None
    match = re.search(
        r"invalid\s+sequence\s+number\s*:\s*expected\s+([0-9]+)\s*,\s*got\s+([0-9]+)",
        response,
        flags=re.IGNORECASE,
    )
    if match is None:
        return None
    return int(match.group(1)), int(match.group(2))


def _tau_transaction_signing_message_bytes(payload: Mapping[str, Any]) -> bytes:
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "operations": payload["operations"],
        "fee_limit": payload["fee_limit"],
    }
    return canonical_json_bytes(signing_dict)


def encode_tau_operations_for_wire(operations: Mapping[str, Any]) -> dict[str, Any]:
    """Encode operation streams into the exact Tau Testnet wire format."""

    encoded_ops: dict[str, Any] = {}
    for key, value in dict(operations).items():
        if key in ("0", "1"):
            encoded_ops[key] = value
            continue
        if isinstance(value, bool):
            raise ValueError(f"operation stream {key!r}: bool values are not allowed")
        if isinstance(value, (str, int)):
            encoded_ops[key] = value
            continue
        encoded_ops[key] = canonical_json_bytes(value).decode("utf-8")
    return encoded_ops


def verify_tau_transaction_payload_signature(payload: Mapping[str, Any]) -> bool:
    """Verify an externally signed Tau transaction; fail closed on malformed input."""

    if not _BLS_VERIFIER_AVAILABLE:
        return False
    try:
        sender_pubkey = payload["sender_pubkey"]
        signature = payload["signature"]
        if not isinstance(sender_pubkey, str) or not isinstance(signature, str):
            return False
        msg_hash = hashlib.sha256(_tau_transaction_signing_message_bytes(payload)).digest()
        pubkey_bytes = bytes.fromhex(sender_pubkey)
        signature_bytes = bytes.fromhex(signature)
        return bool(G2Basic.Verify(pubkey_bytes, msg_hash, signature_bytes))
    except Exception:
        return False


class TauNetTcpClient:
    """Bounded Tau RPC client with no signing or block-production methods."""

    def __init__(self, config: TauNetTcpConfig = _DEFAULT_TAU_NET_TCP_CONFIG) -> None:
        if not isinstance(config.port, int) or not (0 <= config.port <= 65535):
            raise ValueError("invalid port")
        if not isinstance(config.timeout_s, (int, float)) or config.timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if not isinstance(config.recv_max_bytes, int) or config.recv_max_bytes <= 0:
            raise ValueError("recv_max_bytes must be positive")
        self._cfg = config

    def rpc(self, cmd: str) -> str:
        """Send one allowlisted production RPC command.

        The generic transport remains useful for verification/chaos probes, but
        it must not be an escape hatch to ``createblock`` or another node-admin
        command. Embedded line delimiters are rejected before framing.
        """

        if not isinstance(cmd, str) or not cmd.strip():
            raise ValueError("cmd must be a non-empty string")
        if "\r" in cmd or "\n" in cmd:
            raise ValueError("cmd must be exactly one Tau RPC command")
        command = cmd.strip().split(maxsplit=1)[0]
        if command not in _SAFE_RPC_COMMANDS:
            raise ValueError(f"Tau RPC command is not available in production: {command}")
        return self._exchange(cmd)

    def _exchange(self, cmd: str) -> str:
        if not isinstance(cmd, str) or not cmd.strip():
            raise ValueError("cmd must be a non-empty string")
        if "\r" in cmd or "\n" in cmd:
            raise ValueError("cmd must be exactly one Tau RPC command")
        wire = cmd.strip() + "\r\n"
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.settimeout(self._cfg.timeout_s)
            try:
                sock.connect((self._cfg.host, self._cfg.port))
                sock.sendall(wire.encode("utf-8"))
            except socket.timeout as exc:
                raise TauNetRpcError(
                    f"rpc timed out after {self._cfg.timeout_s}s connecting or sending request"
                ) from exc
            except OSError as exc:
                raise TauNetRpcError(f"rpc connection failed: {exc}") from exc
            buf = bytearray()
            remaining = self._cfg.recv_max_bytes
            while remaining > 0:
                try:
                    chunk = sock.recv(min(65536, remaining))
                except socket.timeout as exc:
                    raise TauNetRpcError(
                        f"rpc timed out after {self._cfg.timeout_s}s waiting for response"
                    ) from exc
                except OSError as exc:
                    raise TauNetRpcError(
                        f"rpc connection failed while waiting for response: {exc}"
                    ) from exc
                if not chunk:
                    break
                buf += chunk
                remaining -= len(chunk)
                if b"\n" in buf:
                    break

        if b"\n" in buf:
            line, _, _rest = bytes(buf).partition(b"\n")
            line = line.rstrip(b"\r")
            return line.decode("utf-8", errors="replace")
        if buf:
            raise TauNetRpcError("rpc connection closed before response terminator")
        raise TauNetRpcError("rpc connection closed without response")

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        response = self.rpc(f"getsequence {sender_pubkey_hex}").strip()
        if response.startswith("SEQUENCE:"):
            _, value = response.split(":", 1)
            return int(value.strip())
        raise TauNetRpcError(f"unexpected getsequence response: {response!r}")

    def get_balance(self, address_hex: str) -> int:
        response = self.rpc(f"getbalance {address_hex}").strip()
        if response.startswith("BALANCE:"):
            _, value = response.split(":", 1)
            return int(value.strip())
        raise TauNetRpcError(f"unexpected getbalance response: {response!r}")

    def sendtx(self, payload: Mapping[str, Any]) -> str:
        blob = json.dumps(dict(payload), separators=(",", ":"), sort_keys=True)
        return self.rpc(f"sendtx {blob}").strip()

    def getappstate(self, *, full: bool = False) -> str:
        return self.rpc("getappstate full" if full else "getappstate").strip()

    def getdexstate(self, *, full: bool = False) -> str:
        """Backward-compatible read-only alias for Tau's ``getappstate``."""

        return self.getappstate(full=full)

    def getstateproof(self, *, full: bool = False) -> str:
        return self.rpc("getstateproof full" if full else "getstateproof").strip()


__all__ = (
    "TauNetRpcError",
    "TauNetTcpClient",
    "TauNetTcpConfig",
    "encode_tau_operations_for_wire",
    "tau_rpc_invalid_sequence_numbers",
    "tau_rpc_response_is_success",
    "verify_tau_transaction_payload_signature",
)
