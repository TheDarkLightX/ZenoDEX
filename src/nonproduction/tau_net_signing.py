"""Local-development Tau signing and explicit block-production helpers.

This module is test/tool support, not a production transaction surface.  The
production container removes the entire :mod:`src.nonproduction` package before
copying the curated runtime tree into its final OCI stage.
"""

from __future__ import annotations

import hashlib
import re
import time
from typing import Any, Mapping

from src.core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from src.core.perp_submission_auth_message import hash_perp_op_auth_message_v1
from src.integration.tau_net_rpc import (
    TauNetRpcError,
    TauNetTcpConfig,
    encode_tau_operations_for_wire,
)
from src.integration.tau_net_rpc import (
    TauNetTcpClient as ProductionTauNetTcpClient,
)
from src.state.canonical import canonical_json_bytes

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

try:
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except Exception:  # pragma: no cover - optional dependency
    _BLS12_381_CURVE_ORDER = None


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise TauNetRpcError("py_ecc.bls is required for Tau tx signing (install py-ecc)")


def _coerce_nonnegative_int(value: object, *, label: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{label} must be a non-negative integer")
    if not isinstance(value, (int, float, str, bytes, bytearray)):
        raise ValueError(f"{label} must be a non-negative integer")
    try:
        parsed = int(value)
    except Exception as exc:
        raise ValueError(f"{label} must be a non-negative integer") from exc
    if isinstance(value, float) and not value.is_integer():
        raise ValueError(f"{label} must be a non-negative integer")
    if parsed < 0:
        raise ValueError(f"{label} must be a non-negative integer")
    return parsed


def _parse_privkey_int(privkey: int) -> int:
    secret_key = int(privkey)
    if secret_key <= 0:
        raise ValueError("privkey must be positive")
    if _BLS12_381_CURVE_ORDER is not None and secret_key >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return secret_key


def _parse_privkey_bytes(privkey: bytes | bytearray) -> int:
    raw = bytes(privkey)
    if len(raw) != 32:
        raise ValueError("privkey bytes must be length 32")
    return _parse_privkey_int(int.from_bytes(raw, byteorder="big", signed=False))


def _parse_privkey_hex_32_bytes(hex_str: str, *, label: str) -> bytes:
    if not re.fullmatch(r"[0-9a-fA-F]+", hex_str or ""):
        raise ValueError(f"{label} must contain only 0-9a-f")
    raw = bytes.fromhex(hex_str)
    if len(raw) != 32:
        raise ValueError(f"{label} must decode to 32 bytes, got {len(raw)}")
    return raw


def _parse_privkey_str(privkey: str) -> int:
    text = privkey.strip()
    if not text:
        raise ValueError("privkey must be non-empty")
    if text.lower().startswith("0x"):
        raw = _parse_privkey_hex_32_bytes(text[2:], label="privkey hex")
        return _parse_privkey_int(int.from_bytes(raw, byteorder="big", signed=False))
    if len(text) == 64 and re.fullmatch(r"[0-9a-fA-F]+", text):
        return _parse_privkey_int(int.from_bytes(bytes.fromhex(text), byteorder="big", signed=False))
    if re.fullmatch(r"[0-9]+", text):
        return _parse_privkey_int(int(text, 10))
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
    secret_key = _parse_privkey_to_int(privkey)
    return G2Basic.SkToPk(secret_key).hex()


def _tx_signing_message_bytes(payload: Mapping[str, Any]) -> bytes:
    return canonical_json_bytes(
        {
            "sender_pubkey": payload["sender_pubkey"],
            "sequence_number": payload["sequence_number"],
            "expiration_time": payload["expiration_time"],
            "operations": payload["operations"],
            "fee_limit": payload["fee_limit"],
        }
    )


def sign_tau_transaction_payload(
    payload_wo_sig: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
) -> str:
    _require_bls()
    secret_key = _parse_privkey_to_int(privkey)
    msg_hash = hashlib.sha256(_tx_signing_message_bytes(payload_wo_sig)).digest()
    return G2Basic.Sign(secret_key, msg_hash).hex()


def build_signed_tau_transaction(
    *,
    privkey: str | int | bytes | bytearray,
    sequence_number: int,
    expiration_time: int,
    operations: Mapping[str, Any],
    fee_limit: str | int = "0",
) -> dict[str, Any]:
    _require_bls()
    payload: dict[str, Any] = {
        "sender_pubkey": bls_pubkey_hex_from_privkey(privkey),
        "sequence_number": _coerce_nonnegative_int(sequence_number, label="sequence_number"),
        "expiration_time": _coerce_nonnegative_int(expiration_time, label="expiration_time"),
        "operations": encode_tau_operations_for_wire(operations),
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
    _require_bls()
    secret_key = _parse_privkey_to_int(privkey)
    msg_hash = hash_dex_intent_auth_message_v1(intent_dict, chain_id=chain_id)
    return "0x" + G2Basic.Sign(secret_key, msg_hash).hex()


def sign_perp_op_for_engine(
    op_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    _require_bls()
    secret_key = _parse_privkey_to_int(privkey)
    if not isinstance(signer_pubkey, str) or not signer_pubkey:
        raise ValueError("signer_pubkey must be a non-empty string")
    if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce <= 0:
        raise ValueError("nonce must be a positive int")
    msg_hash = hash_perp_op_auth_message_v1(
        op_dict,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=nonce,
    )
    return "0x" + G2Basic.Sign(secret_key, msg_hash).hex()


class NonProductionTauNetTcpClient(ProductionTauNetTcpClient):
    """Local-only RPC extension capable of block creation and raw-key signing."""

    def rpc(self, cmd: str) -> str:
        """Use the uncurated local-node command surface for test tooling only."""

        return self._exchange(cmd)

    def createblock(self) -> str:
        return self.rpc("createblock").strip()

    def send_signed_tx(
        self,
        *,
        privkey: str | int | bytes | bytearray,
        operations: Mapping[str, Any],
        fee_limit: str | int = "0",
        expiration_seconds: int = 3600,
        sequence_number: int | None = None,
    ) -> str:
        sender = bls_pubkey_hex_from_privkey(privkey)
        sequence = self.get_sequence(sender) if sequence_number is None else int(sequence_number)
        payload = build_signed_tau_transaction(
            privkey=privkey,
            sequence_number=sequence,
            expiration_time=int(time.time()) + int(expiration_seconds),
            operations=operations,
            fee_limit=fee_limit,
        )
        return self.sendtx(payload)


__all__ = (
    "NonProductionTauNetTcpClient",
    "TauNetRpcError",
    "TauNetTcpConfig",
    "bls_pubkey_hex_from_privkey",
    "build_signed_tau_transaction",
    "sign_dex_intent_for_engine",
    "sign_perp_op_for_engine",
    "sign_tau_transaction_payload",
)
