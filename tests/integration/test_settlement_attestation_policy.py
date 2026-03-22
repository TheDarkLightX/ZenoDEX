from __future__ import annotations

import importlib.util

import pytest

from tests.integration._attestation_policy_helper import make_attestation_policy

from src.integration.settlement_attestation_policy import (
    SettlementAttestationPolicy,
    check_settlement_attestation_policy,
    coerce_settlement_attestation_policy,
)
from src.integration.settlement_price_attestation import build_settlement_spot_price_attestation
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)


pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _packet():
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="0x" + "01" * 32, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset="0x" + "02" * 32, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


def _attestation():
    return build_settlement_spot_price_attestation(packet=_packet(), signer_privkey=7)


def test_settlement_attestation_policy_round_trips_and_hashes_stably() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)
    rebuilt = SettlementAttestationPolicy.from_dict(policy.to_dict())
    coerced = coerce_settlement_attestation_policy(policy.to_dict())

    assert rebuilt == policy
    assert coerced == policy
    assert rebuilt.policy_hash_hex() == policy.policy_hash_hex()


@pytest.mark.parametrize(
    ("policy_kwargs", "expected_error"),
    [
        ({"governance_approved": False}, "attestation policy governance approval missing"),
        ({"timelock_elapsed": False}, "attestation policy timelock not elapsed"),
        ({"multisig_approved": False}, "attestation policy multisig approval missing"),
    ],
)
def test_settlement_attestation_policy_rejects_missing_governance_controls(
    policy_kwargs: dict[str, object],
    expected_error: str,
) -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation, **policy_kwargs)

    result = check_settlement_attestation_policy(
        policy=policy,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is False
    assert result.error == expected_error


def test_settlement_attestation_policy_rejects_unmet_signer_quorum() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation, min_distinct_signers=2)

    result = check_settlement_attestation_policy(
        policy=policy,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is False
    assert result.error == "attestation policy signer quorum not met"


def test_settlement_attestation_policy_rejects_unlisted_source() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation, allowed_sources=("oracle:a",), min_distinct_sources=1)

    result = check_settlement_attestation_policy(
        policy=policy,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is False
    assert result.error == "source_id not allowlisted by attestation policy: oracle:b"


def test_settlement_attestation_policy_accepts_active_single_attestation_policy() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation)

    result = check_settlement_attestation_policy(
        policy=policy,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is True
    assert result.error is None
