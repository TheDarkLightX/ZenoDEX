from __future__ import annotations

import pytest

from src.kernels.python.strategy_external_signal_source_registry_guard_v1_adapter import (
    ADVISORY_TRUST_TIER_CODE,
    ATTESTED_TRUST_TIER_CODE,
    PROTOCOL_TRUST_TIER_CODE,
    VERIFIED_TRUST_TIER_CODE,
    check_strategy_external_signal_source_registry_guard,
)


def _check(**overrides: object):
    kwargs: dict[str, object] = {
        "registry_entry_present": True,
        "registry_entry_enabled": True,
        "observed_source_kind_code": 3,
        "observed_trust_tier_code": VERIFIED_TRUST_TIER_CODE,
        "advisory_only": False,
        "auth_ok": True,
        "freshness_ok": True,
        "registered_source_kind_code": 3,
        "allow_advisory": False,
        "allow_attested": True,
        "allow_verified": True,
        "allow_protocol": False,
        "require_advisory_only": False,
        "require_auth": True,
        "require_freshness": True,
    }
    kwargs.update(overrides)
    return check_strategy_external_signal_source_registry_guard(**kwargs)


def test_signal_source_registry_guard_accepts_matching_verified_signal() -> None:
    result = _check()
    assert result.ok is True
    assert result.error is None


def test_signal_source_registry_guard_rejects_missing_disabled_and_kind_mismatch() -> None:
    missing = _check(registry_entry_present=False)
    assert missing.ok is False
    assert missing.error == "source_registry_entry_missing"

    disabled = _check(registry_entry_enabled=False)
    assert disabled.ok is False
    assert disabled.error == "source_registry_entry_disabled"

    kind = _check(registered_source_kind_code=4)
    assert kind.ok is False
    assert kind.error == "source_registry_kind_mismatch"


def test_signal_source_registry_guard_rejects_trust_and_requirement_failures() -> None:
    trust = _check(
        observed_trust_tier_code=ATTESTED_TRUST_TIER_CODE,
        allow_attested=False,
        allow_verified=True,
    )
    assert trust.ok is False
    assert trust.error == "source_registry_trust_tier_rejected"

    advisory = _check(require_advisory_only=True, advisory_only=False)
    assert advisory.ok is False
    assert advisory.error == "source_registry_advisory_mode_required"

    auth = _check(require_auth=True, auth_ok=False)
    assert auth.ok is False
    assert auth.error == "source_registry_auth_required"

    freshness = _check(require_freshness=True, freshness_ok=False)
    assert freshness.ok is False
    assert freshness.error == "source_registry_freshness_required"


def test_signal_source_registry_guard_covers_other_trust_tiers_and_type_errors() -> None:
    advisory = _check(
        observed_trust_tier_code=ADVISORY_TRUST_TIER_CODE,
        advisory_only=True,
        allow_advisory=True,
        allow_attested=False,
        allow_verified=False,
        require_auth=False,
        require_freshness=False,
    )
    assert advisory.ok is True

    protocol = _check(
        observed_trust_tier_code=PROTOCOL_TRUST_TIER_CODE,
        allow_attested=False,
        allow_verified=False,
        allow_protocol=True,
        require_auth=False,
        require_freshness=False,
    )
    assert protocol.ok is True

    unknown_tier = _check(
        observed_trust_tier_code=255,
        allow_advisory=False,
        allow_attested=False,
        allow_verified=False,
        allow_protocol=False,
    )
    assert unknown_tier.ok is False
    assert unknown_tier.error == "source_registry_trust_tier_rejected"

    with pytest.raises(TypeError, match="registry_entry_present must be a bool"):
        _check(registry_entry_present=1)
    with pytest.raises(TypeError, match="observed_source_kind_code must be an int"):
        _check(observed_source_kind_code="bad")
    with pytest.raises(ValueError, match="registered_source_kind_code out of u8 range"):
        _check(registered_source_kind_code=-1)
