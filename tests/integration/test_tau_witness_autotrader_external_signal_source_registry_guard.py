from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1,
    build_autotrader_external_signal_source_registry_guard_v1_step,
)


def test_build_autotrader_external_signal_source_registry_guard_v1_step() -> None:
    step = build_autotrader_external_signal_source_registry_guard_v1_step(
        registry_entry_present=1,
        registry_entry_enabled=1,
        observed_source_kind_code=3,
        observed_trust_tier_code=2,
        advisory_only=0,
        auth_ok=1,
        freshness_ok=1,
        registered_source_kind_code=3,
        allow_advisory=0,
        allow_attested=1,
        allow_verified=1,
        allow_protocol=0,
        require_advisory_only=0,
        require_auth=1,
        require_freshness=1,
    )
    assert (
        AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1.spec_id
        == "autotrader_external_signal_source_registry_guard_v1"
    )
    assert step["i15"] == 1


def test_build_autotrader_external_signal_source_registry_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="registry_entry_present must be 0 or 1"):
        build_autotrader_external_signal_source_registry_guard_v1_step(
            registry_entry_present=2,
            registry_entry_enabled=1,
            observed_source_kind_code=3,
            observed_trust_tier_code=2,
            advisory_only=0,
            auth_ok=1,
            freshness_ok=1,
            registered_source_kind_code=3,
            allow_advisory=0,
            allow_attested=1,
            allow_verified=1,
            allow_protocol=0,
            require_advisory_only=0,
            require_auth=1,
            require_freshness=1,
        )
