from __future__ import annotations

import pytest

from src.kernels.python.strategy_external_signal_contract_v1_adapter import (
    ADVISORY_EXTERNAL_SOURCE_CODE,
    ADVISORY_TRUST_TIER_CODE,
    ATTESTED_EXTERNAL_SOURCE_CODE,
    ATTESTED_TRUST_TIER_CODE,
    VERIFIED_TRUST_TIER_CODE,
    check_strategy_external_signal_contract,
)


def test_external_signal_contract_accepts_advisory_external_signal() -> None:
    result = check_strategy_external_signal_contract(
        source_kind_code=ADVISORY_EXTERNAL_SOURCE_CODE,
        trust_tier_code=ADVISORY_TRUST_TIER_CODE,
        freshness_ok=False,
        auth_ok=False,
        advisory_only=True,
    )
    assert result.ok is True
    assert result.error is None


def test_external_signal_contract_accepts_attested_external_signal() -> None:
    result = check_strategy_external_signal_contract(
        source_kind_code=ATTESTED_EXTERNAL_SOURCE_CODE,
        trust_tier_code=ATTESTED_TRUST_TIER_CODE,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=False,
    )
    assert result.ok is True
    assert result.error is None

    verified = check_strategy_external_signal_contract(
        source_kind_code=ATTESTED_EXTERNAL_SOURCE_CODE,
        trust_tier_code=VERIFIED_TRUST_TIER_CODE,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=False,
    )
    assert verified.ok is True


def test_external_signal_contract_rejects_invalid_source_and_trust_combinations() -> None:
    bad_source = check_strategy_external_signal_contract(
        source_kind_code=99,
        trust_tier_code=ADVISORY_TRUST_TIER_CODE,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )
    assert bad_source.ok is False
    assert bad_source.error == "source_kind_unsupported"

    bad_trust = check_strategy_external_signal_contract(
        source_kind_code=ADVISORY_EXTERNAL_SOURCE_CODE,
        trust_tier_code=99,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )
    assert bad_trust.ok is False
    assert bad_trust.error == "trust_tier_invalid"

    bad_advisory = check_strategy_external_signal_contract(
        source_kind_code=ADVISORY_EXTERNAL_SOURCE_CODE,
        trust_tier_code=ATTESTED_TRUST_TIER_CODE,
        freshness_ok=True,
        auth_ok=True,
        advisory_only=True,
    )
    assert bad_advisory.ok is False
    assert bad_advisory.error == "advisory_external_invalid"

    bad_attested = check_strategy_external_signal_contract(
        source_kind_code=ATTESTED_EXTERNAL_SOURCE_CODE,
        trust_tier_code=ATTESTED_TRUST_TIER_CODE,
        freshness_ok=False,
        auth_ok=True,
        advisory_only=False,
    )
    assert bad_attested.ok is False
    assert bad_attested.error == "attested_external_invalid"


def test_external_signal_contract_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="source_kind_code must be an int"):
        check_strategy_external_signal_contract(
            source_kind_code=True,
            trust_tier_code=ADVISORY_TRUST_TIER_CODE,
            freshness_ok=True,
            auth_ok=True,
            advisory_only=True,
        )
    with pytest.raises(ValueError, match="trust_tier_code out of u8 range"):
        check_strategy_external_signal_contract(
            source_kind_code=ADVISORY_EXTERNAL_SOURCE_CODE,
            trust_tier_code=-1,
            freshness_ok=True,
            auth_ok=True,
            advisory_only=True,
        )
    with pytest.raises(TypeError, match="freshness_ok must be a bool"):
        check_strategy_external_signal_contract(
            source_kind_code=ADVISORY_EXTERNAL_SOURCE_CODE,
            trust_tier_code=ADVISORY_TRUST_TIER_CODE,
            freshness_ok=1,
            auth_ok=True,
            advisory_only=True,
        )
