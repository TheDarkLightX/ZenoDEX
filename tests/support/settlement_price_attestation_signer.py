"""Test-only signer for settlement price attestation verifier fixtures."""

from __future__ import annotations

from py_ecc.bls import G2Basic
from py_ecc.optimized_bls12_381 import curve_order

from src.integration.settlement_price_attestation import (
    SettlementSpotPriceAttestation,
    settlement_spot_price_attestation_from_external_signature,
    settlement_spot_price_attestation_signing_message,
)
from src.integration.settlement_price_provenance import SettlementSpotPricePacket


def _private_key_int(value: str | int | bytes | bytearray) -> int:
    if isinstance(value, bool):
        raise TypeError("privkey must be str|int|bytes and not bool")
    if isinstance(value, int):
        private_key = value
    elif isinstance(value, (bytes, bytearray)):
        raw = bytes(value)
        if len(raw) != 32:
            raise ValueError("privkey bytes must be length 32")
        private_key = int.from_bytes(raw, byteorder="big", signed=False)
    elif isinstance(value, str):
        text = value.strip()
        if not text:
            raise ValueError("privkey must be non-empty")
        if text.lower().startswith("0x"):
            text = text[2:]
        if len(text) == 64 and all(ch in "0123456789abcdefABCDEF" for ch in text):
            private_key = int.from_bytes(bytes.fromhex(text), byteorder="big", signed=False)
        elif text.isdigit():
            private_key = int(text, 10)
        else:
            raise ValueError("privkey must be 32-byte hex or a positive integer string")
    else:
        raise TypeError("privkey must be str|int|bytes")
    if private_key <= 0:
        raise ValueError("privkey must be positive")
    if private_key >= int(curve_order):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return private_key


def build_settlement_spot_price_attestation(
    *,
    packet: SettlementSpotPricePacket,
    signer_privkey: str | int | bytes | bytearray,
) -> SettlementSpotPriceAttestation:
    """Produce an external signature solely for verifier-focused tests."""
    private_key = _private_key_int(signer_privkey)
    signer_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
    message = settlement_spot_price_attestation_signing_message(
        packet=packet,
        signer_pubkey=signer_pubkey,
    )
    signature = "0x" + G2Basic.Sign(private_key, message).hex()
    return settlement_spot_price_attestation_from_external_signature(
        packet=packet,
        signer_pubkey=signer_pubkey,
        signature=signature,
    )
