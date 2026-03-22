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
    policy = make_attestation_policy(attestation, max_bundle_price_spread_bps=125)
    rebuilt = SettlementAttestationPolicy.from_dict(policy.to_dict())
    coerced = coerce_settlement_attestation_policy(policy.to_dict())

    assert rebuilt == policy
    assert coerced == policy
    assert rebuilt.policy_hash_hex() == policy.policy_hash_hex()
    assert rebuilt.bundle_price_consensus_method == "lower_median"
    assert rebuilt.max_bundle_price_spread_bps == 125


@pytest.mark.parametrize("field_name", ["governance_approved", "timelock_elapsed", "multisig_approved"])
def test_settlement_attestation_policy_rejects_truthy_string_booleans(field_name: str) -> None:
    attestation = _attestation()
    policy_payload = make_attestation_policy(attestation).to_dict()
    policy_payload[field_name] = "false"

    with pytest.raises(TypeError, match=rf"^{field_name} must be a bool$"):
        SettlementAttestationPolicy.from_dict(policy_payload)

    with pytest.raises(TypeError, match=rf"^{field_name} must be a bool$"):
        coerce_settlement_attestation_policy(policy_payload)


@pytest.mark.parametrize(
    ("policy_kwargs", "expected_error", "expected_code"),
    [
        (
            {"governance_approved": False},
            "attestation policy governance approval missing",
            "attestation_policy_governance_missing",
        ),
        (
            {"timelock_elapsed": False},
            "attestation policy timelock not elapsed",
            "attestation_policy_timelock_not_elapsed",
        ),
        (
            {"multisig_approved": False},
            "attestation policy multisig approval missing",
            "attestation_policy_multisig_missing",
        ),
    ],
)
def test_settlement_attestation_policy_rejects_missing_governance_controls(
    policy_kwargs: dict[str, object],
    expected_error: str,
    expected_code: str,
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
    assert result.error is not None
    assert result.error.startswith(expected_error)
    assert result.error_code == expected_code
    assert result.details is not None
    assert result.details["policy_id"] == policy.policy_id


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
    assert result.error is not None
    assert result.error.startswith("attestation policy signer quorum not met")
    assert result.error_code == "attestation_policy_signer_quorum_not_met"
    assert result.details is not None
    assert result.details["required_distinct_signers"] == 2
    assert result.details["observed_distinct_signers"] == 1


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
    assert result.error is not None
    assert result.error.startswith("source_id not allowlisted by attestation policy: oracle:b")
    assert result.error_code == "attestation_policy_source_not_allowlisted"
    assert "violating_source=oracle:b" in result.error
    assert result.details is not None
    assert result.details["allowlisted_sources_for_observed_signers"][attestation.signer_pubkey] == ("oracle:a",)


def test_settlement_attestation_policy_accepts_active_single_attestation_policy() -> None:
    attestation = _attestation()
    policy = make_attestation_policy(attestation, max_bundle_price_spread_bps=75)

    result = check_settlement_attestation_policy(
        policy=policy,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is True
    assert result.error is None
    assert result.error_code is None
    assert result.details is not None
    assert result.details["policy_hash"] == policy.policy_hash_hex()
    assert result.details["bundle_price_consensus_method"] == "lower_median"
    assert result.details["max_bundle_price_spread_bps"] == 75


def test_settlement_attestation_policy_missing_policy_exposes_debuggable_telemetry() -> None:
    attestation = _attestation()

    result = check_settlement_attestation_policy(
        policy=None,
        consumer_now_epoch=103,
        signer_pubkeys=(attestation.signer_pubkey,),
        packet_source_ids=tuple(entry.source_id for entry in attestation.packet.entries),
    )

    assert result.ok is False
    assert result.error is not None
    assert result.error.startswith("settlement spot price attestation requires attestation_policy")
    assert result.error_code == "attestation_policy_missing"
    assert result.details is not None
    assert result.details["observed_distinct_signers"] == 1
    assert result.details["observed_distinct_sources"] == 2
    telemetry = result.telemetry_payload()
    assert telemetry["error_code"] == "attestation_policy_missing"
    assert telemetry["details"]["consumer_now_epoch"] == 103
