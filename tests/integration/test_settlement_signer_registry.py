from __future__ import annotations

import importlib.util

import pytest

from tests.integration._attestation_policy_helper import (
    make_attestation_policy,
    make_attestation_registry_snapshot,
)

from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)
from src.integration.settlement_signer_registry import (
    InMemorySettlementSignerRegistrySnapshotLoader,
    SettlementSignerRegistrySnapshot,
    check_settlement_attestation_policy_registry_binding,
    coerce_settlement_signer_registry_snapshot,
    load_attestation_policy_and_registry_snapshot,
    resolve_attestation_policy_and_registry_snapshot,
)


pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _attestation():
    packet = build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(
                asset="0x" + "01" * 32,
                price=100,
                observed_epoch=95,
                age_epochs=5,
                source_id="oracle:a",
            ),
            SettlementSpotPriceEntry(
                asset="0x" + "02" * 32,
                price=120,
                observed_epoch=97,
                age_epochs=3,
                source_id="oracle:b",
            ),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )
    return build_settlement_spot_price_attestation(packet=packet, signer_privkey=7)


def test_settlement_signer_registry_snapshot_round_trips_and_resolves_policy() -> None:
    attestation = _attestation()
    snapshot = make_attestation_registry_snapshot(attestation)

    rebuilt = SettlementSignerRegistrySnapshot.from_dict(snapshot.to_dict())
    coerced = coerce_settlement_signer_registry_snapshot(snapshot.to_dict())
    resolved_policy, resolved_snapshot = resolve_attestation_policy_and_registry_snapshot(
        attestation_policy=None,
        attestation_registry_snapshot=snapshot.to_dict(),
    )

    assert rebuilt == snapshot
    assert coerced == snapshot
    assert resolved_snapshot == snapshot
    assert resolved_policy == snapshot.policy
    assert rebuilt.snapshot_hash_hex() == snapshot.snapshot_hash_hex()


def test_settlement_signer_registry_binding_rejects_policy_drift() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation, policy_epoch=2)

    result = check_settlement_attestation_policy_registry_binding(
        policy=policy,
        registry_snapshot=snapshot,
    )

    assert result.ok is False
    assert result.error_code == "attestation_registry_binding_policy_epoch_mismatch"
    assert result.error is not None
    assert result.error.startswith("attestation policy_epoch does not match registry snapshot policy")
    assert result.details is not None
    assert result.details["policy_epoch"] == 1
    assert result.details["snapshot_policy_epoch"] == 2


def test_settlement_signer_registry_loader_returns_bound_snapshot() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    loader = InMemorySettlementSignerRegistrySnapshotLoader(
        {
            (
                int(policy.chain_id),
                policy.registry_contract,
                policy.policy_id,
                int(policy.policy_epoch),
            ): snapshot
        }
    )

    resolved_policy, resolved_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=loader,
        consumer_now_epoch=103,
    )

    assert resolved_policy == policy
    assert resolved_snapshot == snapshot
