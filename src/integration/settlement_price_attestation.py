from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex

from .settlement_attestation_policy import (
    SettlementAttestationPolicy,
    check_settlement_attestation_policy,
    coerce_settlement_attestation_policy,
)
from .settlement_price_provenance import SettlementSpotPricePacket, verify_settlement_spot_price_packet

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

try:
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except ImportError:  # pragma: no cover - optional dependency
    _BLS12_381_CURVE_ORDER = None


SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA = "zenodex/settlement-spot-price-attestation/v1"
_PRICE_ATTESTATION_VERIFY_CACHE: dict[tuple[object, ...], tuple[bool, str | None]] = {}


@dataclass(frozen=True)
class SettlementSpotPriceAttestation:
    packet: SettlementSpotPricePacket
    signer_pubkey: str
    signed_at_epoch: int
    packet_hash: str
    signature: str
    schema: str = SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.packet, SettlementSpotPricePacket):
            raise TypeError("packet must be a SettlementSpotPricePacket")
        object.__setattr__(
            self,
            "signer_pubkey",
            canonical_hex_fixed_allow_0x(self.signer_pubkey, nbytes=48, name="signer_pubkey"),
        )
        if not isinstance(self.signed_at_epoch, int) or isinstance(self.signed_at_epoch, bool) or self.signed_at_epoch < 0:
            raise ValueError("signed_at_epoch must be a non-negative int")
        object.__setattr__(
            self,
            "packet_hash",
            canonical_hex_fixed_allow_0x(self.packet_hash, nbytes=32, name="packet_hash"),
        )
        object.__setattr__(
            self,
            "signature",
            canonical_hex_fixed_allow_0x(self.signature, nbytes=96, name="signature"),
        )

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet": self.packet.to_dict(),
            "signer_pubkey": self.signer_pubkey,
            "signed_at_epoch": int(self.signed_at_epoch),
            "packet_hash": self.packet_hash,
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["signature"] = self.signature
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSpotPriceAttestation":
        if not isinstance(payload, Mapping):
            raise ValueError("attestation must be an object")
        packet_payload = payload.get("packet")
        if not isinstance(packet_payload, Mapping):
            raise ValueError("attestation.packet must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            packet=SettlementSpotPricePacket.from_dict(packet_payload),
            signer_pubkey=str(payload.get("signer_pubkey", "")),
            signed_at_epoch=int(payload.get("signed_at_epoch", -1)),
            packet_hash=str(payload.get("packet_hash", "")),
            signature=str(payload.get("signature", "")),
        )


def build_settlement_spot_price_attestation(
    *,
    packet: SettlementSpotPricePacket,
    signer_privkey: str | int | bytes | bytearray,
    attestation_policy: SettlementAttestationPolicy | Mapping[str, Any] | None = None,
) -> SettlementSpotPriceAttestation:
    ok, err = verify_settlement_spot_price_packet(packet=packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(signer_privkey)
    signer_pubkey = canonical_hex_fixed_allow_0x(
        "0x" + bls.SkToPk(sk_int).hex(),
        nbytes=48,
        name="signer_pubkey",
    )
    signed_at_epoch = int(packet.now_epoch)
    policy = coerce_settlement_attestation_policy(attestation_policy)
    if policy is not None:
        policy_check = check_settlement_attestation_policy(
            policy=policy,
            consumer_now_epoch=signed_at_epoch,
            policy_reference_epoch=signed_at_epoch,
            signer_pubkeys=(signer_pubkey,),
            packet_source_ids=_packet_source_ids(packet),
        )
        if not policy_check.ok:
            raise ValueError(f"attestation_policy rejected settlement spot price attestation: {policy_check.error}")
    packet_hash = _packet_hash_hex(packet)
    unsigned = {
        "schema": SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA,
        "packet": packet.to_dict(),
        "signer_pubkey": signer_pubkey,
        "signed_at_epoch": signed_at_epoch,
        "packet_hash": packet_hash,
    }
    signature = "0x" + bls.Sign(sk_int, _attestation_message_bytes(unsigned)).hex()
    return SettlementSpotPriceAttestation(
        packet=packet,
        signer_pubkey=signer_pubkey,
        signed_at_epoch=signed_at_epoch,
        packet_hash=packet_hash,
        signature=signature,
    )


def settlement_spot_price_attestation_signer_pubkey_from_privkey(
    signer_privkey: str | int | bytes | bytearray,
) -> str:
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(signer_privkey)
    return canonical_hex_fixed_allow_0x(
        "0x" + bls.SkToPk(sk_int).hex(),
        nbytes=48,
        name="signer_pubkey",
    )


def verify_settlement_spot_price_attestation(
    *,
    attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
) -> tuple[bool, str | None]:
    if not isinstance(attestation, SettlementSpotPriceAttestation):
        return False, "attestation must be a SettlementSpotPriceAttestation"
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        return False, "consumer_now_epoch must be a non-negative int"
    if (
        not isinstance(max_attestation_age_epochs, int)
        or isinstance(max_attestation_age_epochs, bool)
        or max_attestation_age_epochs < 0
    ):
        return False, "max_attestation_age_epochs must be a non-negative int"

    ok, err = verify_settlement_spot_price_packet(packet=attestation.packet)
    if not ok:
        return False, f"invalid settlement spot price packet: {err}"
    if not attestation.packet.provenance_ok:
        return False, "settlement spot price packet is not provenance_ok"
    expected_packet_hash = _packet_hash_hex(attestation.packet)
    if attestation.packet_hash != expected_packet_hash:
        return False, "packet_hash mismatch"
    if int(attestation.signed_at_epoch) != int(attestation.packet.now_epoch):
        return False, "signed_at_epoch must equal packet.now_epoch"
    if int(consumer_now_epoch) < int(attestation.signed_at_epoch):
        return False, "attestation signed_at_epoch is in the future"
    if int(consumer_now_epoch) - int(attestation.signed_at_epoch) > int(max_attestation_age_epochs):
        return False, "settlement spot price attestation is stale"

    normalized_allowlist = _canonical_allowed_signers(allowed_signers)
    cache_key = _price_attestation_verify_cache_key(
        attestation=attestation,
        consumer_now_epoch=int(consumer_now_epoch),
        max_attestation_age_epochs=int(max_attestation_age_epochs),
        normalized_allowlist=normalized_allowlist,
    )
    cached = _PRICE_ATTESTATION_VERIFY_CACHE.get(cache_key)
    if cached is not None:
        return cached
    if normalized_allowlist is not None:
        allowed_sources = normalized_allowlist.get(attestation.signer_pubkey)
        if allowed_sources is None:
            result = (False, "signer_pubkey not allowlisted")
            _cache_attestation_verify_result(cache_key, result)
            return result
        for source_id in _packet_source_ids(attestation.packet):
            if source_id not in allowed_sources:
                result = (False, f"source_id not allowlisted for signer: {source_id}")
                _cache_attestation_verify_result(cache_key, result)
                return result

    bls = _require_bls()
    unsigned = attestation.to_unsigned_dict()
    try:
        pubkey_bytes = bytes.fromhex(attestation.signer_pubkey[2:])
        sig_bytes = bytes.fromhex(attestation.signature[2:])
        if not bool(bls.Verify(pubkey_bytes, _attestation_message_bytes(unsigned), sig_bytes)):
            result = (False, "settlement spot price attestation signature invalid")
            _cache_attestation_verify_result(cache_key, result)
            return result
    except Exception as exc:
        result = (False, f"settlement spot price attestation verification error: {exc}")
        _cache_attestation_verify_result(cache_key, result)
        return result
    result = (True, None)
    _cache_attestation_verify_result(cache_key, result)
    return result


def verify_settlement_spot_price_attestation_payload(
    *,
    payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
) -> tuple[bool, str | None]:
    try:
        attestation = SettlementSpotPriceAttestation.from_dict(payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        allowed_signers=allowed_signers,
    )


def _canonical_allowed_signers(
    allowed_signers: Mapping[str, Sequence[str]] | None,
) -> dict[str, frozenset[str]] | None:
    if allowed_signers is None:
        return None
    if not isinstance(allowed_signers, Mapping):
        raise TypeError("allowed_signers must be a mapping when provided")
    normalized: dict[str, frozenset[str]] = {}
    for raw_pubkey, raw_sources in allowed_signers.items():
        pubkey = canonical_hex_fixed_allow_0x(str(raw_pubkey), nbytes=48, name="allowed_signer_pubkey")
        if not isinstance(raw_sources, Sequence) or isinstance(raw_sources, (str, bytes, bytearray)):
            raise TypeError("allowed_signer source ids must be a sequence of strings")
        source_ids = []
        for raw_source in raw_sources:
            if not isinstance(raw_source, str):
                raise TypeError("allowed_signer source ids must be strings")
            source_id = raw_source.strip()
            if not source_id:
                raise ValueError("allowed_signer source ids must be non-empty")
            source_ids.append(source_id)
        normalized[pubkey] = frozenset(source_ids)
    return normalized


def _packet_hash_hex(packet: SettlementSpotPricePacket) -> str:
    return sha256_hex(
        domain_sep_bytes("settlement_spot_price_packet", version=1) + canonical_json_bytes(packet.to_dict())
    )


def _packet_source_ids(packet: SettlementSpotPricePacket) -> tuple[str, ...]:
    return tuple(entry.source_id for entry in packet.entries)


def _attestation_message_bytes(unsigned_payload: Mapping[str, Any]) -> bytes:
    return domain_sep_bytes("settlement_spot_price_attestation", version=1) + canonical_json_bytes(dict(unsigned_payload))


def _price_attestation_verify_cache_key(
    *,
    attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    normalized_allowlist: Mapping[str, frozenset[str]] | None,
) -> tuple[object, ...]:
    allowlist_key = None
    if normalized_allowlist is not None:
        allowlist_key = tuple(
            sorted((pubkey, tuple(sorted(source_ids))) for pubkey, source_ids in normalized_allowlist.items())
        )
    return (
        attestation.packet_hash,
        attestation.signer_pubkey,
        int(attestation.signed_at_epoch),
        attestation.signature,
        attestation.packet.price_vector_sha256,
        attestation.packet.provenance_vector_sha256,
        int(attestation.packet.now_epoch),
        int(attestation.packet.max_staleness_epochs),
        bool(attestation.packet.provenance_ok),
        tuple(
            (entry.asset, int(entry.price), int(entry.observed_epoch), int(entry.age_epochs), entry.source_id)
            for entry in attestation.packet.entries
        ),
        int(consumer_now_epoch),
        int(max_attestation_age_epochs),
        allowlist_key,
    )


def _cache_attestation_verify_result(
    key: tuple[object, ...],
    result: tuple[bool, str | None],
) -> None:
    if len(_PRICE_ATTESTATION_VERIFY_CACHE) >= 512:
        _PRICE_ATTESTATION_VERIFY_CACHE.clear()
    _PRICE_ATTESTATION_VERIFY_CACHE[key] = result


def _parse_privkey_to_int(privkey: str | int | bytes | bytearray) -> int:
    if isinstance(privkey, int):
        sk = int(privkey)
    elif isinstance(privkey, (bytes, bytearray)):
        raw = bytes(privkey)
        if len(raw) != 32:
            raise ValueError("privkey bytes must be length 32")
        sk = int.from_bytes(raw, byteorder="big", signed=False)
    elif isinstance(privkey, str):
        text = privkey.strip()
        if not text:
            raise ValueError("privkey must be non-empty")
        if text.lower().startswith("0x"):
            text = text[2:]
        if len(text) == 64 and all(ch in "0123456789abcdefABCDEF" for ch in text):
            sk = int.from_bytes(bytes.fromhex(text), byteorder="big", signed=False)
        elif text.isdigit():
            sk = int(text, 10)
        else:
            raise ValueError("privkey must be 32-byte hex or a positive integer string")
    else:
        raise TypeError("privkey must be str|int|bytes")
    if sk <= 0:
        raise ValueError("privkey must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return sk


def _require_bls() -> Any:
    if not _BLS_AVAILABLE or G2Basic is None:
        raise ValueError("py_ecc.bls is required for settlement price attestation signing and verification")
    return G2Basic
