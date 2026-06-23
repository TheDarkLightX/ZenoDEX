from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_OBSERVATION_PACKET_CONTRACT_V1,
    build_autotrader_observation_packet_contract_v1_step,
)


def test_build_autotrader_observation_packet_contract_v1_step() -> None:
    step = build_autotrader_observation_packet_contract_v1_step(
        primary_source_kind_code=1,
        primary_trust_tier_code=2,
        primary_quote_receipt_present=1,
        primary_quote_receipt_verified=1,
        primary_quote_epoch_present=1,
        primary_source_available=1,
        primary_auth_ok=1,
        primary_binding_ok=1,
        external_signal_count=2,
        advisory_external_count=1,
        trusted_external_count=1,
    )
    assert AUTOTRADER_OBSERVATION_PACKET_CONTRACT_V1.spec_id == "autotrader_observation_packet_contract_v1"
    assert step["i11"] == 1


def test_build_autotrader_observation_packet_contract_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="primary_source_available must be 0 or 1"):
        build_autotrader_observation_packet_contract_v1_step(
            primary_source_kind_code=1,
            primary_trust_tier_code=2,
            primary_quote_receipt_present=1,
            primary_quote_receipt_verified=1,
            primary_quote_epoch_present=1,
            primary_source_available=2,
            primary_auth_ok=1,
            primary_binding_ok=1,
            external_signal_count=0,
            advisory_external_count=0,
            trusted_external_count=0,
        )
