"""Pure BLS signing helpers independent of any network or retired Tau bridge."""

from __future__ import annotations

import re
from typing import Any, Mapping, cast

from ..core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from ..core.perp_submission_auth_message import hash_perp_op_auth_message_v1

try:
    from py_ecc.bls import G2Basic

    BLS_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    BLS_AVAILABLE = False

try:
    from py_ecc.optimized_bls12_381 import curve_order as BLS12_381_CURVE_ORDER
except ImportError:  # pragma: no cover - optional dependency
    BLS12_381_CURVE_ORDER = None


class BlsSigningUnavailableError(RuntimeError):
    """Raised when the optional deterministic BLS implementation is absent."""


def require_bls() -> None:
    if not BLS_AVAILABLE:
        raise BlsSigningUnavailableError("py_ecc.bls is required for BLS signing (install py-ecc)")


def parse_privkey_to_int(privkey: str | int | bytes | bytearray) -> int:
    """Parse one exact positive BLS12-381 secret scalar."""

    if isinstance(privkey, bool):
        raise TypeError("privkey must be str|int|bytes")
    if isinstance(privkey, int):
        secret = privkey
    elif isinstance(privkey, (bytes, bytearray)):
        raw = bytes(privkey)
        if len(raw) != 32:
            raise ValueError("privkey bytes must be length 32")
        secret = int.from_bytes(raw, byteorder="big", signed=False)
    elif isinstance(privkey, str):
        value = privkey.strip()
        if not value:
            raise ValueError("privkey must be non-empty")
        if value.lower().startswith("0x"):
            encoded = value[2:]
            if re.fullmatch(r"[0-9a-fA-F]+", encoded or "") is None:
                raise ValueError("privkey hex must contain only 0-9a-f")
            raw = bytes.fromhex(encoded)
            if len(raw) != 32:
                raise ValueError(f"privkey hex must decode to 32 bytes, got {len(raw)}")
            secret = int.from_bytes(raw, byteorder="big", signed=False)
        elif len(value) == 64 and re.fullmatch(r"[0-9a-fA-F]+", value) is not None:
            secret = int.from_bytes(bytes.fromhex(value), byteorder="big", signed=False)
        elif re.fullmatch(r"[0-9]+", value) is not None:
            secret = int(value, 10)
        else:
            raise ValueError(
                "privkey must be 32-byte hex (0x... or 64 hex chars) or a positive integer string"
            )
    else:
        raise TypeError("privkey must be str|int|bytes")
    if secret <= 0:
        raise ValueError("privkey must be positive")
    if BLS12_381_CURVE_ORDER is not None and secret >= int(BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return secret


def bls_pubkey_hex_from_privkey(privkey: str | int | bytes | bytearray) -> str:
    require_bls()
    bls = cast(Any, G2Basic)
    return bls.SkToPk(parse_privkey_to_int(privkey)).hex()


def sign_dex_intent_for_engine(
    intent_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
) -> str:
    """Sign the exact domain-separated DEX intent authorization message."""

    require_bls()
    bls = cast(Any, G2Basic)
    message_hash = hash_dex_intent_auth_message_v1(intent_dict, chain_id=chain_id)
    return "0x" + bls.Sign(parse_privkey_to_int(privkey), message_hash).hex()


def sign_perp_op_for_engine(
    op_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    """Sign the exact domain-separated perps operation authorization message."""

    require_bls()
    bls = cast(Any, G2Basic)
    if not isinstance(signer_pubkey, str) or not signer_pubkey:
        raise ValueError("signer_pubkey must be a non-empty string")
    if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce <= 0:
        raise ValueError("nonce must be a positive int")
    message_hash = hash_perp_op_auth_message_v1(
        op_dict,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=nonce,
    )
    return "0x" + bls.Sign(parse_privkey_to_int(privkey), message_hash).hex()
