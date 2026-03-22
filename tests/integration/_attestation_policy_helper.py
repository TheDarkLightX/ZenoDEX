from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import Any

from src.integration.settlement_attestation_policy import SettlementAttestationPolicy
from src.integration.settlement_price_attestation import SettlementSpotPriceAttestation
from src.integration.settlement_signer_registry import SettlementSignerRegistryAnchor, SettlementSignerRegistrySnapshot


def _packet_entry_source_ids_from_payload(packet_payload: Mapping[str, Any]) -> tuple[str, ...]:
    entries = packet_payload.get("entries")
    if not isinstance(entries, Sequence):
        raise ValueError("attestation payload packet.entries must be a sequence")
    source_ids: list[str] = []
    for entry in entries:
        if not isinstance(entry, Mapping):
            raise ValueError("attestation payload packet entry must be an object")
        source_id = entry.get("source_id")
        if not isinstance(source_id, str) or not source_id:
            raise ValueError("attestation payload packet entry source_id must be a non-empty string")
        source_ids.append(source_id)
    return tuple(dict.fromkeys(source_ids))


def _attestation_fields(attestation: SettlementSpotPriceAttestation | Mapping[str, Any]) -> tuple[str, int, tuple[str, ...]]:
    if isinstance(attestation, SettlementSpotPriceAttestation):
        return (
            attestation.signer_pubkey,
            int(attestation.signed_at_epoch),
            tuple(dict.fromkeys(entry.source_id for entry in attestation.packet.entries)),
        )
    if not isinstance(attestation, Mapping):
        raise TypeError("attestation must be a SettlementSpotPriceAttestation or payload mapping")
    signer_pubkey = attestation.get("signer_pubkey")
    signed_at_epoch = attestation.get("signed_at_epoch")
    packet_payload = attestation.get("packet")
    if not isinstance(signer_pubkey, str) or not signer_pubkey:
        raise ValueError("attestation payload signer_pubkey must be a non-empty string")
    if not isinstance(signed_at_epoch, int) or isinstance(signed_at_epoch, bool) or signed_at_epoch < 0:
        raise ValueError("attestation payload signed_at_epoch must be a non-negative int")
    if not isinstance(packet_payload, Mapping):
        raise ValueError("attestation payload packet must be an object")
    return signer_pubkey, int(signed_at_epoch), _packet_entry_source_ids_from_payload(packet_payload)


def make_attestation_policy(
    attestation: SettlementSpotPriceAttestation | Mapping[str, Any],
    *,
    policy_id: str = "settlement-attestation-policy-v1",
    policy_epoch: int = 1,
    chain_id: int = 1,
    registry_contract: str = "0x" + "12" * 20,
    registry_root: str = "0x" + "34" * 32,
    governance_approved: bool = True,
    timelock_elapsed: bool = True,
    multisig_approved: bool = True,
    min_distinct_signers: int = 1,
    min_distinct_sources: int | None = None,
    allowed_sources: Sequence[str] | None = None,
    effective_from_epoch: int | None = None,
    expires_at_epoch: int | None = None,
) -> SettlementAttestationPolicy:
    signer_pubkey, signed_at_epoch, packet_source_ids = _attestation_fields(attestation)
    canonical_sources = tuple(dict.fromkeys(packet_source_ids if allowed_sources is None else allowed_sources))
    if min_distinct_sources is None:
        min_distinct_sources = max(1, len(canonical_sources))
    if effective_from_epoch is None:
        effective_from_epoch = max(0, signed_at_epoch - 1)
    if expires_at_epoch is None:
        expires_at_epoch = signed_at_epoch + 100
    return SettlementAttestationPolicy(
        policy_id=policy_id,
        policy_epoch=policy_epoch,
        chain_id=chain_id,
        registry_contract=registry_contract,
        registry_root=registry_root,
        effective_from_epoch=effective_from_epoch,
        expires_at_epoch=expires_at_epoch,
        governance_approved=governance_approved,
        timelock_elapsed=timelock_elapsed,
        multisig_approved=multisig_approved,
        min_distinct_signers=min_distinct_signers,
        min_distinct_sources=min_distinct_sources,
        allowed_signers={signer_pubkey: canonical_sources},
    )


def make_attestation_policy_payload(
    attestation: SettlementSpotPriceAttestation | Mapping[str, Any],
    **kwargs: Any,
) -> dict[str, Any]:
    return make_attestation_policy(attestation, **kwargs).to_dict()


def make_attestation_registry_snapshot(
    attestation: SettlementSpotPriceAttestation | Mapping[str, Any],
    *,
    snapshot_block_number: int = 1_234_567,
    snapshot_block_hash: str = "0x" + "56" * 32,
    **policy_kwargs: Any,
) -> SettlementSignerRegistrySnapshot:
    policy = make_attestation_policy(attestation, **policy_kwargs)
    return SettlementSignerRegistrySnapshot(
        chain_id=int(policy.chain_id),
        registry_contract=policy.registry_contract,
        registry_root=policy.registry_root,
        snapshot_block_number=snapshot_block_number,
        snapshot_block_hash=snapshot_block_hash,
        policy=policy,
    )


def make_attestation_registry_snapshot_payload(
    attestation: SettlementSpotPriceAttestation | Mapping[str, Any],
    **kwargs: Any,
) -> dict[str, Any]:
    return make_attestation_registry_snapshot(attestation, **kwargs).to_dict()


def make_attestation_registry_anchor(
    attestation: SettlementSpotPriceAttestation | Mapping[str, Any],
    *,
    anchor_block_number: int = 1_234_890,
    anchor_block_hash: str = "0x" + "78" * 32,
    **policy_kwargs: Any,
) -> SettlementSignerRegistryAnchor:
    policy = make_attestation_policy(attestation, **policy_kwargs)
    return SettlementSignerRegistryAnchor(
        chain_id=int(policy.chain_id),
        registry_contract=policy.registry_contract,
        policy_id=policy.policy_id,
        policy_epoch=int(policy.policy_epoch),
        registry_root=policy.registry_root,
        policy_hash=policy.policy_hash_hex(),
        anchor_block_number=anchor_block_number,
        anchor_block_hash=anchor_block_hash,
    )
