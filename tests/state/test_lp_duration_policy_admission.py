from __future__ import annotations

import importlib
import sys
from dataclasses import fields

import pytest

from src.integration.lp_position_age_gate import (
    LPDurationRiskPolicy,
    admit_lp_duration_risk_policy_context_v1,
)
from src.state import lp_duration_policy_schema
from src.state.lp_duration_policy_admission import (
    _LP_DURATION_POLICY_ADMISSION_REGISTRY_V1,
    FCIS_REGISTERED_REGISTRY_IDS,
    FCIS_REQUIRED_REGISTRY_IDS,
)
from src.state.lp_duration_policy_context import (
    admit_optional_lp_duration_policy_v1,
)
from src.state.lp_duration_policy_schema import (
    LP_DURATION_POLICY_FIELD_NAMES_V1,
    LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1,
    LP_DURATION_POLICY_RECORD_SCHEMA_V1,
    LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1,
    LPDurationPolicyRecordTagV1,
)
from src.state.lp_duration_transitions import LPDurationRiskPolicyV1
from src.state.snapshot_combinators import (
    AdmitCode,
    AdmitOk,
    AdmitReject,
    SchemaRegistrationV1,
)


def _legacy_policy() -> LPDurationRiskPolicy:
    return LPDurationRiskPolicy(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )


def test_policy_schema_registry_is_exact_and_manifest_bound() -> None:
    assert tuple(
        registration.tag for registration in LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1
    ) == tuple(LPDurationPolicyRecordTagV1)
    for registration in LP_DURATION_POLICY_RECORD_REGISTRATIONS_V1:
        assert tuple(item.name for item in fields(registration.source_type)) == tuple(
            item.name for item in fields(registration.owned_type)
        )
    assert (
        tuple(field.name for field in LP_DURATION_POLICY_RECORD_SCHEMA_V1.declared_fields)
        == LP_DURATION_POLICY_FIELD_NAMES_V1
    )
    schema_ids = tuple(
        registration.schema_id for registration in LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1
    )
    assert schema_ids == FCIS_REQUIRED_REGISTRY_IDS
    assert schema_ids == FCIS_REGISTERED_REGISTRY_IDS
    assert _LP_DURATION_POLICY_ADMISSION_REGISTRY_V1.schema_ids == FCIS_REGISTERED_REGISTRY_IDS


def test_policy_profile_import_fails_closed_when_builder_registry_drifts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module_name = "src.state.lp_duration_policy_admission"
    registered = LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1[0]
    drifted = (
        SchemaRegistrationV1(
            "zenodex/fcis/context/lp-duration-policy-drift/v1",
            registered.schema,
        ),
    )
    with monkeypatch.context() as scoped:
        scoped.setattr(
            lp_duration_policy_schema,
            "LP_DURATION_POLICY_SCHEMA_REGISTRATIONS_V1",
            drifted,
        )
        sys.modules.pop(module_name, None)
        with pytest.raises(RuntimeError, match="registry manifest drift"):
            importlib.import_module(module_name)

    sys.modules.pop(module_name, None)
    restored = importlib.import_module(module_name)
    assert (
        restored._LP_DURATION_POLICY_ADMISSION_REGISTRY_V1.schema_ids
        == FCIS_REGISTERED_REGISTRY_IDS
    )


def test_legacy_policy_projection_uses_the_closed_admission_profile() -> None:
    source = _legacy_policy()

    result = admit_lp_duration_risk_policy_context_v1(source)

    assert type(result) is AdmitOk
    assert type(result.value) is LPDurationRiskPolicyV1
    assert result.value == LPDurationRiskPolicyV1(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )


def test_policy_admission_accepts_none_through_the_same_optional_schema() -> None:
    result = admit_lp_duration_risk_policy_context_v1(None)

    assert result == AdmitOk(None)


def test_policy_admission_revalidates_and_reconstructs_exact_owned_input() -> None:
    source = LPDurationRiskPolicyV1(base_age_seconds=60, multiplier=2)

    result = admit_optional_lp_duration_policy_v1(source)

    assert type(result) is AdmitOk
    assert result.value == source
    assert result.value is not source


def test_policy_admission_rejects_integer_bool_at_the_declared_field_path() -> None:
    source = _legacy_policy()
    object.__setattr__(source, "base_age_seconds", True)

    result = admit_lp_duration_risk_policy_context_v1(source)

    assert result == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("base_age_seconds",),
    )


def test_policy_admission_rejects_negative_value_at_the_declared_field_path() -> None:
    source = _legacy_policy()
    object.__setattr__(source, "decay_seconds", -1)

    result = admit_lp_duration_risk_policy_context_v1(source)

    assert result == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        ("decay_seconds",),
    )


def test_policy_admission_rejects_cross_field_domain_invariant() -> None:
    source = _legacy_policy()
    object.__setattr__(source, "base_age_seconds", 3_601)

    result = admit_lp_duration_risk_policy_context_v1(source)

    assert result == AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())


def test_policy_projection_rejects_missing_field_without_partial_value() -> None:
    source = _legacy_policy()
    object.__delattr__(source, "multiplier")

    result = admit_lp_duration_risk_policy_context_v1(source)

    assert result == AdmitReject(AdmitCode.MISSING_FIELD, ("multiplier",))
    assert not hasattr(result, "value")


def test_policy_subclass_rejects_before_hostile_attribute_access() -> None:
    class HostilePolicy(LPDurationRiskPolicy):
        def __getattribute__(self, name: str) -> object:
            try:
                armed = object.__getattribute__(self, "_hostile_armed")
            except AttributeError:
                armed = False
            if armed and not name.startswith("__"):
                raise AssertionError("hostile policy behavior executed")
            return object.__getattribute__(self, name)

    source = HostilePolicy()
    object.__setattr__(source, "_hostile_armed", True)

    assert admit_lp_duration_risk_policy_context_v1(source) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        (),
    )


def test_policy_projection_rejects_unknown_instance_field() -> None:
    source = _legacy_policy()
    object.__setattr__(source, "unexpected", 1)

    assert admit_lp_duration_risk_policy_context_v1(source) == AdmitReject(
        AdmitCode.UNKNOWN_FIELD,
        (),
    )


def test_policy_projection_matches_combinator_unknown_before_missing_precedence() -> None:
    source = _legacy_policy()
    object.__delattr__(source, "multiplier")
    object.__setattr__(source, "unexpected", 1)

    assert admit_lp_duration_risk_policy_context_v1(source) == AdmitReject(
        AdmitCode.UNKNOWN_FIELD,
        (),
    )


def test_accepted_policy_owns_values_against_later_source_corruption() -> None:
    source = _legacy_policy()
    result = admit_lp_duration_risk_policy_context_v1(source)
    assert type(result) is AdmitOk
    exact = result.value

    object.__setattr__(source, "base_age_seconds", 999)
    object.__setattr__(source, "multiplier", 7)

    assert type(exact) is LPDurationRiskPolicyV1
    assert exact.base_age_seconds == 60
    assert exact.multiplier == 2


def test_corrupted_owned_policy_is_revalidated_by_the_combinator() -> None:
    source = LPDurationRiskPolicyV1(base_age_seconds=60, multiplier=2)
    object.__setattr__(source, "multiplier", 0)

    assert admit_optional_lp_duration_policy_v1(source) == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        ("multiplier",),
    )
