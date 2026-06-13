from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes, domain_sep_bytes, sha256_hex

from .settlement_attestation_policy import (
    SettlementAttestationPolicy,
    check_settlement_attestation_policy,
)
from .settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
    verify_settlement_spot_price_packet,
)
from .settlement_signer_registry import (
    SettlementSignerRegistrySnapshot,
    load_attestation_policy_and_registry_snapshot,
)

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


SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA = "zenodex/settlement-spot-price-attestation/v2"
SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1 = "zenodex/settlement-spot-price-attestation/v1"
SETTLEMENT_SPOT_PRICE_ATTESTATION_BUNDLE_SCHEMA = "zenodex/settlement-spot-price-attestation-bundle/v1"
_PRICE_ATTESTATION_VERIFY_CACHE: dict[tuple[object, ...], tuple[bool, str | None]] = {}


@dataclass(frozen=True)
class SettlementSpotPriceAttestation:
    packet: SettlementSpotPricePacket
    signer_pubkey: str
    signed_at_epoch: int
    packet_hash: str
    signature: str
    attestation_policy_id: str | None = None
    attestation_policy_epoch: int | None = None
    attestation_policy_chain_id: int | None = None
    attestation_policy_registry_contract: str | None = None
    attestation_policy_root: str | None = None
    attestation_policy_hash: str | None = None
    schema: str = SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA

    @property
    def is_policy_bound(self) -> bool:
        return self.schema == SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA

    def __post_init__(self) -> None:
        if self.schema not in (
            SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA,
            SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1,
        ):
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.schema == SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA and all(
            getattr(self, name) is None
            for name in (
                "attestation_policy_id",
                "attestation_policy_epoch",
                "attestation_policy_chain_id",
                "attestation_policy_registry_contract",
                "attestation_policy_root",
                "attestation_policy_hash",
            )
        ):
            object.__setattr__(self, "schema", SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1)
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
        if self.is_policy_bound:
            if not isinstance(self.attestation_policy_id, str) or not self.attestation_policy_id.strip():
                raise ValueError("attestation_policy_id must be a non-empty string")
            object.__setattr__(self, "attestation_policy_id", self.attestation_policy_id.strip())
            for name in ("attestation_policy_epoch", "attestation_policy_chain_id"):
                value = getattr(self, name)
                if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                    raise ValueError(f"{name} must be a non-negative int")
            object.__setattr__(
                self,
                "attestation_policy_registry_contract",
                canonical_hex_fixed_allow_0x(
                    self.attestation_policy_registry_contract,
                    nbytes=20,
                    name="attestation_policy_registry_contract",
                ),
            )
            object.__setattr__(
                self,
                "attestation_policy_root",
                canonical_hex_fixed_allow_0x(self.attestation_policy_root, nbytes=32, name="attestation_policy_root"),
            )
            object.__setattr__(
                self,
                "attestation_policy_hash",
                canonical_hex_fixed_allow_0x(self.attestation_policy_hash, nbytes=32, name="attestation_policy_hash"),
            )
        else:
            for name in (
                "attestation_policy_id",
                "attestation_policy_epoch",
                "attestation_policy_chain_id",
                "attestation_policy_registry_contract",
                "attestation_policy_root",
                "attestation_policy_hash",
            ):
                if getattr(self, name) is not None:
                    raise ValueError(f"{name} must be absent for an unbound v1 attestation")
        object.__setattr__(
            self,
            "signature",
            canonical_hex_fixed_allow_0x(self.signature, nbytes=96, name="signature"),
        )

    def to_unsigned_dict(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "schema": self.schema,
            "packet": self.packet.to_dict(),
            "signer_pubkey": self.signer_pubkey,
            "signed_at_epoch": int(self.signed_at_epoch),
            "packet_hash": self.packet_hash,
        }
        if self.is_policy_bound:
            payload.update(
                {
                    "attestation_policy_id": self.attestation_policy_id,
                    "attestation_policy_epoch": int(self.attestation_policy_epoch),
                    "attestation_policy_chain_id": int(self.attestation_policy_chain_id),
                    "attestation_policy_registry_contract": self.attestation_policy_registry_contract,
                    "attestation_policy_root": self.attestation_policy_root,
                    "attestation_policy_hash": self.attestation_policy_hash,
                }
            )
        return payload

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
        schema = str(payload.get("schema", ""))
        if schema == SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1:
            for name in (
                "attestation_policy_id",
                "attestation_policy_epoch",
                "attestation_policy_chain_id",
                "attestation_policy_registry_contract",
                "attestation_policy_root",
                "attestation_policy_hash",
            ):
                if payload.get(name) is not None:
                    raise ValueError(f"{name} must be absent for an unbound v1 attestation")
            return cls(
                schema=schema,
                packet=SettlementSpotPricePacket.from_dict(packet_payload),
                signer_pubkey=str(payload.get("signer_pubkey", "")),
                signed_at_epoch=int(payload.get("signed_at_epoch", -1)),
                packet_hash=str(payload.get("packet_hash", "")),
                signature=str(payload.get("signature", "")),
            )
        return cls(
            schema=schema,
            packet=SettlementSpotPricePacket.from_dict(packet_payload),
            signer_pubkey=str(payload.get("signer_pubkey", "")),
            signed_at_epoch=int(payload.get("signed_at_epoch", -1)),
            packet_hash=str(payload.get("packet_hash", "")),
            attestation_policy_id=str(payload.get("attestation_policy_id", "")),
            attestation_policy_epoch=int(payload.get("attestation_policy_epoch", -1)),
            attestation_policy_chain_id=int(payload.get("attestation_policy_chain_id", -1)),
            attestation_policy_registry_contract=str(payload.get("attestation_policy_registry_contract", "")),
            attestation_policy_root=str(payload.get("attestation_policy_root", "")),
            attestation_policy_hash=str(payload.get("attestation_policy_hash", "")),
            signature=str(payload.get("signature", "")),
        )


@dataclass(frozen=True)
class SettlementSpotPriceAttestationBundle:
    packet: SettlementSpotPricePacket
    packet_hash: str
    signed_at_epoch: int
    attestations: tuple[SettlementSpotPriceAttestation, ...]
    schema: str = SETTLEMENT_SPOT_PRICE_ATTESTATION_BUNDLE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SPOT_PRICE_ATTESTATION_BUNDLE_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.packet, SettlementSpotPricePacket):
            raise TypeError("packet must be a SettlementSpotPricePacket")
        object.__setattr__(
            self,
            "packet_hash",
            canonical_hex_fixed_allow_0x(self.packet_hash, nbytes=32, name="packet_hash"),
        )
        if not isinstance(self.signed_at_epoch, int) or isinstance(self.signed_at_epoch, bool) or self.signed_at_epoch < 0:
            raise ValueError("signed_at_epoch must be a non-negative int")
        if not isinstance(self.attestations, tuple):
            if not isinstance(self.attestations, (list, tuple)):
                raise TypeError("attestations must be a non-empty sequence of SettlementSpotPriceAttestation")
            object.__setattr__(self, "attestations", tuple(self.attestations))
        if not self.attestations:
            raise ValueError("attestations must be non-empty")
        seen_signers: set[str] = set()
        expected_policy_binding: tuple[object, ...] | None = None
        for attestation in self.attestations:
            if not isinstance(attestation, SettlementSpotPriceAttestation):
                raise TypeError("attestations must contain SettlementSpotPriceAttestation values")
            if int(attestation.signed_at_epoch) != int(self.signed_at_epoch):
                raise ValueError("bundle attestation signed_at_epoch must match bundle.signed_at_epoch")
            if attestation.signer_pubkey in seen_signers:
                raise ValueError("bundle attestation signer_pubkey values must be distinct")
            policy_binding = _attestation_policy_binding_tuple(attestation)
            if expected_policy_binding is None:
                expected_policy_binding = policy_binding
            elif policy_binding != expected_policy_binding:
                raise ValueError("bundle attestation policy bindings must be identical")
            seen_signers.add(attestation.signer_pubkey)
        expected_packet = _build_bundle_consensus_packet(self.attestations)
        expected_packet_hash = _packet_hash_hex(expected_packet)
        if self.packet != expected_packet:
            raise ValueError("bundle packet must equal the lower-median consensus packet derived from attestations")
        if self.packet_hash != expected_packet_hash:
            raise ValueError("bundle packet_hash must match bundle.packet")
        if int(self.signed_at_epoch) != int(self.packet.now_epoch):
            raise ValueError("bundle signed_at_epoch must equal bundle.packet.now_epoch")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet": self.packet.to_dict(),
            "packet_hash": self.packet_hash,
            "signed_at_epoch": int(self.signed_at_epoch),
            "attestations": [attestation.to_dict() for attestation in self.attestations],
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSpotPriceAttestationBundle":
        if not isinstance(payload, Mapping):
            raise ValueError("attestation bundle must be an object")
        packet_payload = payload.get("packet")
        attestation_payloads = payload.get("attestations")
        if not isinstance(packet_payload, Mapping):
            raise ValueError("attestation bundle.packet must be an object")
        if not isinstance(attestation_payloads, list):
            raise ValueError("attestation bundle.attestations must be an array")
        return cls(
            schema=str(payload.get("schema", "")),
            packet=SettlementSpotPricePacket.from_dict(packet_payload),
            packet_hash=str(payload.get("packet_hash", "")),
            signed_at_epoch=int(payload.get("signed_at_epoch", -1)),
            attestations=tuple(SettlementSpotPriceAttestation.from_dict(item) for item in attestation_payloads),
        )


@dataclass(frozen=True)
class SettlementSpotPriceAttestationBundleConsensusCheckResult:
    ok: bool
    error: str | None = None
    error_code: str | None = None
    details: Mapping[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "ok": bool(self.ok),
            "error": self.error,
            "error_code": self.error_code,
            "details": None if self.details is None else dict(self.details),
        }

    def telemetry_payload(self) -> dict[str, Any]:
        return self.to_dict()


def build_settlement_spot_price_attestation(
    *,
    packet: SettlementSpotPricePacket,
    signer_privkey: str | int | bytes | bytearray,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
) -> SettlementSpotPriceAttestation:
    ok, err = verify_settlement_spot_price_packet(packet=packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    if attestation_policy is None and attestation_registry_snapshot is None:
        _require_bls()
        sk_int = _parse_privkey_to_int(signer_privkey)
        signer_pubkey = settlement_spot_price_attestation_signer_pubkey_from_privkey(signer_privkey)
        signed_at_epoch = int(packet.now_epoch)
        packet_hash = _packet_hash_hex(packet)
        unsigned = {
            "schema": SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1,
            "packet": packet.to_dict(),
            "signer_pubkey": signer_pubkey,
            "signed_at_epoch": signed_at_epoch,
            "packet_hash": packet_hash,
        }
        signature = "0x" + G2Basic.Sign(sk_int, _attestation_message_bytes(unsigned)).hex()
        return SettlementSpotPriceAttestation(
            schema=SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA_V1,
            packet=packet,
            signer_pubkey=signer_pubkey,
            signed_at_epoch=signed_at_epoch,
            packet_hash=packet_hash,
            signature=signature,
        )
    attestation_policy, _loaded_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=None,
        consumer_now_epoch=int(packet.now_epoch),
    )
    if attestation_policy is None:
        raise ValueError("build_settlement_spot_price_attestation requires attestation_policy or attestation_registry_snapshot")
    _require_bls()
    sk_int = _parse_privkey_to_int(signer_privkey)
    signer_pubkey = settlement_spot_price_attestation_signer_pubkey_from_privkey(signer_privkey)
    signed_at_epoch = int(packet.now_epoch)
    packet_hash = _packet_hash_hex(packet)
    policy_hash = attestation_policy.policy_hash_hex()
    unsigned = {
        "schema": SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA,
        "packet": packet.to_dict(),
        "signer_pubkey": signer_pubkey,
        "signed_at_epoch": signed_at_epoch,
        "packet_hash": packet_hash,
        "attestation_policy_id": attestation_policy.policy_id,
        "attestation_policy_epoch": int(attestation_policy.policy_epoch),
        "attestation_policy_chain_id": int(attestation_policy.chain_id),
        "attestation_policy_registry_contract": attestation_policy.registry_contract,
        "attestation_policy_root": attestation_policy.registry_root,
        "attestation_policy_hash": policy_hash,
    }
    signature = "0x" + G2Basic.Sign(sk_int, _attestation_message_bytes(unsigned)).hex()
    return SettlementSpotPriceAttestation(
        packet=packet,
        signer_pubkey=signer_pubkey,
        signed_at_epoch=signed_at_epoch,
        packet_hash=packet_hash,
        attestation_policy_id=attestation_policy.policy_id,
        attestation_policy_epoch=int(attestation_policy.policy_epoch),
        attestation_policy_chain_id=int(attestation_policy.chain_id),
        attestation_policy_registry_contract=attestation_policy.registry_contract,
        attestation_policy_root=attestation_policy.registry_root,
        attestation_policy_hash=policy_hash,
        signature=signature,
    )


def build_settlement_spot_price_attestation_bundle(
    *,
    attestations: tuple[SettlementSpotPriceAttestation, ...] | list[SettlementSpotPriceAttestation],
) -> SettlementSpotPriceAttestationBundle:
    if not isinstance(attestations, (list, tuple)):
        raise TypeError("attestations must be a non-empty sequence of SettlementSpotPriceAttestation")
    if not attestations:
        raise ValueError("attestations must be non-empty")
    first = attestations[0]
    if not isinstance(first, SettlementSpotPriceAttestation):
        raise TypeError("attestations must contain SettlementSpotPriceAttestation values")
    consensus_packet = _build_bundle_consensus_packet(tuple(attestations))
    return SettlementSpotPriceAttestationBundle(
        packet=consensus_packet,
        packet_hash=_packet_hash_hex(consensus_packet),
        signed_at_epoch=int(consensus_packet.now_epoch),
        attestations=tuple(attestations),
    )


def settlement_spot_price_attestation_signer_pubkey_from_privkey(
    signer_privkey: str | int | bytes | bytearray,
) -> str:
    _require_bls()
    sk_int = _parse_privkey_to_int(signer_privkey)
    return canonical_hex_fixed_allow_0x(
        "0x" + G2Basic.SkToPk(sk_int).hex(),
        nbytes=48,
        name="signer_pubkey",
    )


def verify_settlement_spot_price_attestation(
    *,
    attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
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
    policy_context_provided = (
        attestation_policy is not None
        or attestation_registry_snapshot is not None
        or attestation_registry_snapshot_loader is not None
    )
    if policy_context_provided:
        try:
            attestation_policy, attestation_registry_snapshot = load_attestation_policy_and_registry_snapshot(
                attestation_policy=attestation_policy,
                attestation_registry_snapshot=attestation_registry_snapshot,
                attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
                consumer_now_epoch=int(consumer_now_epoch),
            )
        except Exception as exc:
            return False, str(exc)
    elif attestation.is_policy_bound:
        return False, "policy-bound attestation requires attestation_policy or attestation_registry_snapshot to verify"

    ok, err = _verify_settlement_spot_price_attestation_packet_consistency(
        attestation=attestation,
        consumer_now_epoch=int(consumer_now_epoch),
        max_attestation_age_epochs=int(max_attestation_age_epochs),
    )
    if not ok:
        return False, err

    if policy_context_provided:
        if not attestation.is_policy_bound:
            return False, "attestation lacks policy binding required by the provided attestation_policy context"
        policy_check = check_settlement_attestation_policy(
            policy=attestation_policy,
            consumer_now_epoch=int(consumer_now_epoch),
            policy_reference_epoch=int(attestation.signed_at_epoch),
            signer_pubkeys=(attestation.signer_pubkey,),
            packet_source_ids=_packet_source_ids(attestation.packet),
        )
        if not policy_check.ok:
            return False, policy_check.error
        ok, err = _verify_settlement_spot_price_attestation_policy_binding(
            attestation=attestation,
            attestation_policy=attestation_policy,
        )
        if not ok:
            return False, err
    try:
        normalized_allowlist = _canonical_allowed_signers(allowed_signers)
    except Exception as exc:
        return False, str(exc)
    if normalized_allowlist is not None:
        allowed_sources = normalized_allowlist.get(attestation.signer_pubkey)
        if allowed_sources is None:
            return False, "signer_pubkey not allowlisted"
        for source_id in _packet_source_ids(attestation.packet):
            if source_id not in allowed_sources:
                return False, f"source_id not allowlisted for signer: {source_id}"
    cache_key = _price_attestation_verify_cache_key(
        attestation=attestation,
        consumer_now_epoch=int(consumer_now_epoch),
        max_attestation_age_epochs=int(max_attestation_age_epochs),
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        normalized_allowlist=normalized_allowlist,
    )
    cached = _PRICE_ATTESTATION_VERIFY_CACHE.get(cache_key)
    if cached is not None:
        return cached

    result = _verify_settlement_spot_price_attestation_signature(attestation=attestation)
    _cache_attestation_verify_result(cache_key, result)
    return result


def verify_settlement_spot_price_attestation_bundle(
    *,
    bundle: SettlementSpotPriceAttestationBundle,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
) -> tuple[bool, str | None]:
    if not isinstance(bundle, SettlementSpotPriceAttestationBundle):
        return False, "bundle must be a SettlementSpotPriceAttestationBundle"
    if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
        return False, "consumer_now_epoch must be a non-negative int"
    if (
        not isinstance(max_attestation_age_epochs, int)
        or isinstance(max_attestation_age_epochs, bool)
        or max_attestation_age_epochs < 0
    ):
        return False, "max_attestation_age_epochs must be a non-negative int"
    try:
        attestation_policy, attestation_registry_snapshot = load_attestation_policy_and_registry_snapshot(
            attestation_policy=attestation_policy,
            attestation_registry_snapshot=attestation_registry_snapshot,
            attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
            consumer_now_epoch=int(consumer_now_epoch),
        )
    except Exception as exc:
        return False, str(exc)

    for attestation in bundle.attestations:
        ok, err = _verify_settlement_spot_price_attestation_packet_consistency(
            attestation=attestation,
            consumer_now_epoch=int(consumer_now_epoch),
            max_attestation_age_epochs=int(max_attestation_age_epochs),
        )
        if not ok:
            return False, err
        ok, err = _verify_settlement_spot_price_attestation_signature(attestation=attestation)
        if not ok:
            return False, err

    policy_check = check_settlement_attestation_policy(
        policy=attestation_policy,
        consumer_now_epoch=int(consumer_now_epoch),
        policy_reference_epoch=int(bundle.signed_at_epoch),
        signer_pubkeys=tuple(attestation.signer_pubkey for attestation in bundle.attestations),
        packet_source_ids=_packet_source_ids(bundle.packet),
    )
    if not policy_check.ok:
        return False, policy_check.error
    for attestation in bundle.attestations:
        ok, err = _verify_settlement_spot_price_attestation_policy_binding(
            attestation=attestation,
            attestation_policy=attestation_policy,
        )
        if not ok:
            return False, err
    consensus_check = check_settlement_spot_price_attestation_bundle_consensus(
        bundle=bundle,
        attestation_policy=attestation_policy,
    )
    if not consensus_check.ok:
        return False, consensus_check.error
    return True, None


def verify_settlement_spot_price_attestation_bundle_payload(
    *,
    payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
) -> tuple[bool, str | None]:
    try:
        bundle = SettlementSpotPriceAttestationBundle.from_dict(payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_spot_price_attestation_bundle(
        bundle=bundle,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
    )


def check_settlement_spot_price_attestation_bundle_consensus(
    *,
    bundle: SettlementSpotPriceAttestationBundle,
    attestation_policy: SettlementAttestationPolicy | None,
) -> SettlementSpotPriceAttestationBundleConsensusCheckResult:
    if attestation_policy is None:
        details = {
            "bundle_signer_pubkeys": tuple(attestation.signer_pubkey for attestation in bundle.attestations),
            "bundle_signed_at_epoch": int(bundle.signed_at_epoch),
        }
        return SettlementSpotPriceAttestationBundleConsensusCheckResult(
            ok=False,
            error=_format_bundle_consensus_error(
                "bundle consensus check requires attestation_policy",
                details=details,
            ),
            error_code="attestation_bundle_policy_missing",
            details=details,
        )
    try:
        expected_packet = _build_bundle_consensus_packet(bundle.attestations)
    except Exception as exc:
        details = {
            "policy_id": attestation_policy.policy_id,
            "policy_epoch": int(attestation_policy.policy_epoch),
            "bundle_signer_pubkeys": tuple(attestation.signer_pubkey for attestation in bundle.attestations),
            "bundle_signed_at_epoch": int(bundle.signed_at_epoch),
        }
        return SettlementSpotPriceAttestationBundleConsensusCheckResult(
            ok=False,
            error=_format_bundle_consensus_error(str(exc), details=details),
            error_code="attestation_bundle_packet_shape_mismatch",
            details=details,
        )
    if bundle.packet != expected_packet:
        details = {
            "policy_id": attestation_policy.policy_id,
            "policy_epoch": int(attestation_policy.policy_epoch),
            "consensus_method": attestation_policy.bundle_price_consensus_method,
            "expected_packet_hash": _packet_hash_hex(expected_packet),
            "observed_packet_hash": bundle.packet_hash,
        }
        return SettlementSpotPriceAttestationBundleConsensusCheckResult(
            ok=False,
            error=_format_bundle_consensus_error(
                "bundle packet does not match derived consensus packet",
                details=details,
            ),
            error_code="attestation_bundle_packet_consensus_mismatch",
            details=details,
        )
    per_asset = _bundle_price_deviation_details(bundle.attestations, expected_packet)
    max_observed_spread_bps = max((item["max_deviation_bps"] for item in per_asset.values()), default=0)
    details = {
        "policy_id": attestation_policy.policy_id,
        "policy_epoch": int(attestation_policy.policy_epoch),
        "consensus_method": attestation_policy.bundle_price_consensus_method,
        "allowed_max_bundle_price_spread_bps": int(attestation_policy.max_bundle_price_spread_bps),
        "observed_max_bundle_price_spread_bps": int(max_observed_spread_bps),
        "per_asset": per_asset,
    }
    if max_observed_spread_bps > int(attestation_policy.max_bundle_price_spread_bps):
        return SettlementSpotPriceAttestationBundleConsensusCheckResult(
            ok=False,
            error=_format_bundle_consensus_error(
                "bundle price disagreement exceeds attestation policy bound",
                details=details,
            ),
            error_code="attestation_bundle_price_spread_too_wide",
            details=details,
        )
    return SettlementSpotPriceAttestationBundleConsensusCheckResult(
        ok=True,
        error=None,
        error_code=None,
        details=details,
    )


def _verify_settlement_spot_price_attestation_packet_consistency(
    *,
    attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
) -> tuple[bool, str | None]:
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
    return True, None


def _build_bundle_consensus_packet(
    attestations: tuple[SettlementSpotPriceAttestation, ...],
) -> SettlementSpotPricePacket:
    if not attestations:
        raise ValueError("bundle attestations must be non-empty")
    template = attestations[0].packet
    template_key = _bundle_packet_shape_key(template)
    per_asset_prices: dict[str, list[int]] = {entry.asset: [int(entry.price)] for entry in template.entries}
    for attestation in attestations[1:]:
        if _bundle_packet_shape_key(attestation.packet) != template_key:
            raise ValueError(
                f"bundle attestation packet shape mismatch for signer_pubkey={attestation.signer_pubkey}"
            )
        for entry in attestation.packet.entries:
            per_asset_prices[entry.asset].append(int(entry.price))
    consensus_entries = tuple(
        SettlementSpotPriceEntry(
            asset=entry.asset,
            price=_lower_median(per_asset_prices[entry.asset]),
            observed_epoch=int(entry.observed_epoch),
            age_epochs=int(entry.age_epochs),
            source_id=entry.source_id,
        )
        for entry in template.entries
    )
    return build_settlement_spot_price_packet(
        entries=consensus_entries,
        now_epoch=int(template.now_epoch),
        max_staleness_epochs=int(template.max_staleness_epochs),
        cross_module_sync_required=bool(template.cross_module_sync_required),
        cross_module_sync_contract=template.cross_module_sync_contract,
    )


def _bundle_packet_shape_key(packet: SettlementSpotPricePacket) -> tuple[object, ...]:
    sync_contract_key = None if packet.cross_module_sync_contract is None else canonical_json_bytes(
        packet.cross_module_sync_contract
    )
    return (
        int(packet.now_epoch),
        int(packet.max_staleness_epochs),
        bool(packet.cross_module_sync_required),
        bool(packet.cross_module_sync_ok),
        bool(packet.unique_assets),
        bool(packet.all_positive),
        bool(packet.all_fresh),
        bool(packet.provenance_ok),
        sync_contract_key,
        tuple(
            (
                entry.asset,
                int(entry.observed_epoch),
                int(entry.age_epochs),
                entry.source_id,
            )
            for entry in packet.entries
        ),
    )


def _lower_median(values: list[int]) -> int:
    ordered = sorted(int(value) for value in values)
    return int(ordered[(len(ordered) - 1) // 2])


def _bundle_price_deviation_details(
    attestations: tuple[SettlementSpotPriceAttestation, ...],
    consensus_packet: SettlementSpotPricePacket,
) -> dict[str, dict[str, Any]]:
    observed_by_asset: dict[str, list[int]] = {entry.asset: [] for entry in consensus_packet.entries}
    for attestation in attestations:
        for entry in attestation.packet.entries:
            observed_by_asset[entry.asset].append(int(entry.price))
    out: dict[str, dict[str, Any]] = {}
    for entry in consensus_packet.entries:
        median_price = int(entry.price)
        observed_prices = tuple(observed_by_asset[entry.asset])
        max_deviation_bps = max(
            (_deviation_bps(observed_price, median_price) for observed_price in observed_prices),
            default=0,
        )
        out[entry.asset] = {
            "median_price": median_price,
            "observed_prices": observed_prices,
            "max_deviation_bps": int(max_deviation_bps),
            "source_id": entry.source_id,
        }
    return out


def _deviation_bps(value: int, median_value: int) -> int:
    if int(median_value) <= 0:
        raise ValueError("bundle consensus median_price must be positive")
    return (abs(int(value) - int(median_value)) * 10_000) // int(median_value)


def _format_bundle_consensus_error(message: str, *, details: Mapping[str, Any]) -> str:
    ordered_items = ", ".join(f"{key}={details[key]!r}" for key in sorted(details))
    return f"{message}; {ordered_items}" if ordered_items else message


def _verify_settlement_spot_price_attestation_signature(
    *,
    attestation: SettlementSpotPriceAttestation,
) -> tuple[bool, str | None]:
    _require_bls()
    unsigned = attestation.to_unsigned_dict()
    try:
        pubkey_bytes = bytes.fromhex(attestation.signer_pubkey[2:])
        sig_bytes = bytes.fromhex(attestation.signature[2:])
        if not bool(G2Basic.Verify(pubkey_bytes, _attestation_message_bytes(unsigned), sig_bytes)):
            return False, "settlement spot price attestation signature invalid"
    except Exception as exc:
        return False, f"settlement spot price attestation verification error: {exc}"
    return True, None


def _verify_settlement_spot_price_attestation_policy_binding(
    *,
    attestation: SettlementSpotPriceAttestation,
    attestation_policy: SettlementAttestationPolicy | None,
) -> tuple[bool, str | None]:
    if attestation_policy is None:
        return False, "settlement spot price attestation requires attestation_policy"
    observed = {
        "attestation_policy_id": attestation.attestation_policy_id,
        "attestation_policy_epoch": int(attestation.attestation_policy_epoch),
        "attestation_policy_chain_id": int(attestation.attestation_policy_chain_id),
        "attestation_policy_registry_contract": attestation.attestation_policy_registry_contract,
        "attestation_policy_root": attestation.attestation_policy_root,
        "attestation_policy_hash": attestation.attestation_policy_hash,
    }
    expected = {
        "attestation_policy_id": attestation_policy.policy_id,
        "attestation_policy_epoch": int(attestation_policy.policy_epoch),
        "attestation_policy_chain_id": int(attestation_policy.chain_id),
        "attestation_policy_registry_contract": attestation_policy.registry_contract,
        "attestation_policy_root": attestation_policy.registry_root,
        "attestation_policy_hash": attestation_policy.policy_hash_hex(),
    }
    if observed != expected:
        detail_items = {
            "observed_attestation_policy_id": observed["attestation_policy_id"],
            "observed_attestation_policy_epoch": observed["attestation_policy_epoch"],
            "observed_attestation_policy_chain_id": observed["attestation_policy_chain_id"],
            "observed_attestation_policy_registry_contract": observed["attestation_policy_registry_contract"],
            "observed_attestation_policy_root": observed["attestation_policy_root"],
            "observed_attestation_policy_hash": observed["attestation_policy_hash"],
            "expected_attestation_policy_id": expected["attestation_policy_id"],
            "expected_attestation_policy_epoch": expected["attestation_policy_epoch"],
            "expected_attestation_policy_chain_id": expected["attestation_policy_chain_id"],
            "expected_attestation_policy_registry_contract": expected["attestation_policy_registry_contract"],
            "expected_attestation_policy_root": expected["attestation_policy_root"],
            "expected_attestation_policy_hash": expected["attestation_policy_hash"],
        }
        return False, _format_bundle_consensus_error("attestation policy binding mismatch", details=detail_items)
    return True, None


def verify_settlement_spot_price_attestation_payload(
    *,
    payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    allowed_signers: Mapping[str, Sequence[str]] | None = None,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
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
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
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
    version = 2 if str(unsigned_payload.get("schema", "")) == SETTLEMENT_SPOT_PRICE_ATTESTATION_SCHEMA else 1
    return domain_sep_bytes("settlement_spot_price_attestation", version=version) + canonical_json_bytes(dict(unsigned_payload))


def _price_attestation_verify_cache_key(
    *,
    attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    attestation_policy: SettlementAttestationPolicy | None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None,
    normalized_allowlist: Mapping[str, frozenset[str]] | None = None,
) -> tuple[object, ...]:
    policy_key = None if attestation_policy is None else (
        attestation_policy.policy_id,
        int(attestation_policy.policy_epoch),
        attestation_policy.registry_root,
        attestation_policy.policy_hash_hex(),
    )
    snapshot_key = None if attestation_registry_snapshot is None else (
        int(attestation_registry_snapshot.chain_id),
        attestation_registry_snapshot.registry_contract,
        attestation_registry_snapshot.registry_root,
        int(attestation_registry_snapshot.snapshot_block_number),
        attestation_registry_snapshot.snapshot_block_hash,
        attestation_registry_snapshot.snapshot_hash_hex(),
    )
    return (
        attestation.schema,
        attestation.packet_hash,
        attestation.signer_pubkey,
        int(attestation.signed_at_epoch),
        attestation.attestation_policy_id,
        None if attestation.attestation_policy_epoch is None else int(attestation.attestation_policy_epoch),
        None if attestation.attestation_policy_chain_id is None else int(attestation.attestation_policy_chain_id),
        attestation.attestation_policy_registry_contract,
        attestation.attestation_policy_root,
        attestation.attestation_policy_hash,
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
        policy_key,
        snapshot_key,
        None
        if normalized_allowlist is None
        else tuple(sorted((pubkey, tuple(sorted(sources))) for pubkey, sources in normalized_allowlist.items())),
    )


def _cache_attestation_verify_result(
    key: tuple[object, ...],
    result: tuple[bool, str | None],
) -> None:
    if len(_PRICE_ATTESTATION_VERIFY_CACHE) >= 512:
        _PRICE_ATTESTATION_VERIFY_CACHE.clear()
    _PRICE_ATTESTATION_VERIFY_CACHE[key] = result


def _attestation_policy_binding_tuple(attestation: SettlementSpotPriceAttestation) -> tuple[object, ...]:
    return (
        attestation.attestation_policy_id,
        None if attestation.attestation_policy_epoch is None else int(attestation.attestation_policy_epoch),
        None if attestation.attestation_policy_chain_id is None else int(attestation.attestation_policy_chain_id),
        attestation.attestation_policy_registry_contract,
        attestation.attestation_policy_root,
        attestation.attestation_policy_hash,
    )


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


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise ValueError("py_ecc.bls is required for settlement price attestation signing and verification")
