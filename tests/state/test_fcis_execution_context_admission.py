from __future__ import annotations

import subprocess
import sys
from dataclasses import fields
from pathlib import Path

from src.state.fcis_execution_context import (
    admit_fcis_settlement_execution_context_v1,
    admit_fcis_step_execution_context_v1,
)
from src.state.fcis_execution_context_admission import (
    _FCIS_EXECUTION_CONTEXT_ADMISSION_REGISTRY_V1,
    FCIS_REGISTERED_REGISTRY_IDS,
    FCIS_REQUIRED_REGISTRY_IDS,
)
from src.state.fcis_execution_context_codec import (
    encode_fcis_execution_context_v1,
)
from src.state.fcis_execution_context_schema import (
    FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1,
    FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1,
    FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1,
    FCIS_FEE_SPLIT_POLICY_RECORD_SCHEMA_V1,
    FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1,
    FCIS_LP_DURATION_POLICY_RECORD_SCHEMA_V1,
    FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1,
    FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1,
    FCIS_STEP_CONTEXT_FIELD_NAMES_V1,
    FCIS_STEP_CONTEXT_RECORD_SCHEMA_V1,
)
from src.state.fcis_execution_context_values import (
    FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISExecutionContextRecordTagV1,
    FCISFeeSplitPolicySourceV1,
    FCISFeeSplitPolicyV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementExecutionContextV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
    settlement_mode_label_v1,
)
from src.state.lp_duration_policy_schema import LPDurationPolicyAdmissionSourceV1
from src.state.lp_duration_policy_values import LPDurationRiskPolicyV1
from src.state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject

_REPO_ROOT = Path(__file__).resolve().parents[2]


def _settlement_source() -> FCISSettlementExecutionContextSourceV1:
    return FCISSettlementExecutionContextSourceV1(
        now=1_000,
        min_lp_position_age_seconds=60,
        mode=FCISSettlementModeV1.STRONG_REPLAY,
        allow_cow_netting=True,
        allow_snapshot_bound_quote_bindings=False,
        protocol_fee_share_bps=100,
        protocol_fee_recipient_pubkey="protocol",
    )


def _fee_source() -> FCISFeeSplitPolicySourceV1:
    return FCISFeeSplitPolicySourceV1(
        buyback_bps=2_000,
        treasury_bps=3_000,
        rewards_bps=5_000,
    )


def _lp_source() -> LPDurationPolicyAdmissionSourceV1:
    return LPDurationPolicyAdmissionSourceV1(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )


def _step_source() -> FCISStepExecutionContextSourceV1:
    return FCISStepExecutionContextSourceV1(
        settlement=_settlement_source(),
        require_all_nonces=True,
        reject_settlements_with_rejected_intents=True,
        fee_split_policy=_fee_source(),
        lp_duration_policy=_lp_source(),
        snapshot_version=4,
    )


def test_execution_context_schema_registry_is_exhaustive_and_manifest_bound() -> None:
    assert tuple(
        registration.tag
        for registration in FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1
    ) == tuple(FCISExecutionContextRecordTagV1)
    for registration in FCIS_EXECUTION_CONTEXT_RECORD_REGISTRATIONS_V1:
        assert tuple(item.name for item in fields(registration.source_type)) == tuple(
            item.name for item in fields(registration.owned_type)
        )
    assert tuple(
        field.name for field in FCIS_SETTLEMENT_CONTEXT_RECORD_SCHEMA_V1.declared_fields
    ) == FCIS_SETTLEMENT_CONTEXT_FIELD_NAMES_V1
    assert tuple(
        field.name for field in FCIS_FEE_SPLIT_POLICY_RECORD_SCHEMA_V1.declared_fields
    ) == FCIS_FEE_SPLIT_POLICY_FIELD_NAMES_V1
    assert tuple(
        field.name for field in FCIS_LP_DURATION_POLICY_RECORD_SCHEMA_V1.declared_fields
    ) == FCIS_LP_DURATION_POLICY_FIELD_NAMES_V1
    assert tuple(
        field.name for field in FCIS_STEP_CONTEXT_RECORD_SCHEMA_V1.declared_fields
    ) == FCIS_STEP_CONTEXT_FIELD_NAMES_V1
    schema_ids = tuple(
        registration.schema_id
        for registration in FCIS_EXECUTION_CONTEXT_SCHEMA_REGISTRATIONS_V1
    )
    assert schema_ids == FCIS_REQUIRED_REGISTRY_IDS
    assert schema_ids == FCIS_REGISTERED_REGISTRY_IDS
    assert (
        _FCIS_EXECUTION_CONTEXT_ADMISSION_REGISTRY_V1.schema_ids
        == FCIS_REGISTERED_REGISTRY_IDS
    )


def test_step_admission_constructs_one_fresh_exact_owned_graph() -> None:
    source = _step_source()

    result = admit_fcis_step_execution_context_v1(source)

    assert type(result) is AdmitOk
    exact = result.value
    assert type(exact) is FCISStepExecutionContextV1
    assert type(exact.settlement) is FCISSettlementExecutionContextV1
    assert type(exact.fee_split_policy) is FCISFeeSplitPolicyV1
    assert type(exact.lp_duration_policy) is LPDurationRiskPolicyV1
    assert settlement_mode_label_v1(exact.settlement.mode) == "strong_replay"
    assert exact.snapshot_version == 4


def test_admitted_context_owns_values_against_later_source_corruption() -> None:
    source = _step_source()
    settlement_source = source.settlement
    fee_source = source.fee_split_policy
    lp_source = source.lp_duration_policy
    result = admit_fcis_step_execution_context_v1(source)
    assert type(result) is AdmitOk
    exact = result.value

    object.__setattr__(settlement_source, "now", 999_999)
    object.__setattr__(fee_source, "buyback_bps", 9_999)
    object.__setattr__(lp_source, "multiplier", 99)
    object.__setattr__(source, "snapshot_version", 1)

    assert exact.settlement.now == 1_000
    assert exact.fee_split_policy == FCISFeeSplitPolicyV1(2_000, 3_000, 5_000)
    assert exact.lp_duration_policy == LPDurationRiskPolicyV1(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )
    assert exact.snapshot_version == 4


def test_context_rejects_bool_as_int_at_the_declared_nested_path() -> None:
    source = _step_source()
    object.__setattr__(source.settlement, "now", True)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("settlement", "now"),
    )


def test_context_rejects_string_mode_at_the_declared_nested_path() -> None:
    source = _step_source()
    object.__setattr__(source.settlement, "mode", "strong_replay")

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        ("settlement", "mode"),
    )


def test_context_rejects_nonzero_protocol_share_without_recipient() -> None:
    source = _step_source()
    object.__setattr__(source.settlement, "protocol_fee_recipient_pubkey", None)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.DOMAIN_INVARIANT,
        ("settlement",),
    )


def test_context_rejects_fee_sum_domain_error_at_record_path() -> None:
    source = _step_source()
    object.__setattr__(source.fee_split_policy, "rewards_bps", 4_999)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.DOMAIN_INVARIANT,
        ("fee_split_policy",),
    )


def test_context_rejects_lp_cross_field_error_at_record_path() -> None:
    source = _step_source()
    object.__setattr__(source.lp_duration_policy, "base_age_seconds", 3_601)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.DOMAIN_INVARIANT,
        ("lp_duration_policy",),
    )


def test_context_rejects_unsupported_snapshot_version_at_exact_path() -> None:
    source = _step_source()
    object.__setattr__(source, "snapshot_version", 5)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        ("snapshot_version",),
    )


def test_context_subclass_rejects_before_hostile_attribute_access() -> None:
    class HostileStepSource(FCISStepExecutionContextSourceV1):
        def __getattribute__(self, name: str) -> object:
            armed = object.__getattribute__(self, "_hostile_armed")
            if armed and not name.startswith("__"):
                raise AssertionError("hostile context behavior executed")
            return object.__getattribute__(self, name)

    base = _step_source()
    source = HostileStepSource(
        settlement=base.settlement,
        require_all_nonces=base.require_all_nonces,
        reject_settlements_with_rejected_intents=(
            base.reject_settlements_with_rejected_intents
        ),
        fee_split_policy=base.fee_split_policy,
        lp_duration_policy=base.lp_duration_policy,
        snapshot_version=base.snapshot_version,
    )
    object.__setattr__(source, "_hostile_armed", True)

    assert admit_fcis_step_execution_context_v1(source) == AdmitReject(
        AdmitCode.WRONG_EXACT_TYPE,
        (),
    )


def test_context_readmission_reconstructs_and_revalidates_owned_graph() -> None:
    first = admit_fcis_step_execution_context_v1(_step_source())
    assert type(first) is AdmitOk

    second = admit_fcis_step_execution_context_v1(first.value)

    assert type(second) is AdmitOk
    assert second.value == first.value
    assert second.value is not first.value
    assert second.value.settlement is not first.value.settlement
    assert second.value.fee_split_policy is not first.value.fee_split_policy
    assert second.value.lp_duration_policy is not first.value.lp_duration_policy

    object.__setattr__(first.value, "snapshot_version", 5)
    assert admit_fcis_step_execution_context_v1(first.value) == AdmitReject(
        AdmitCode.OUT_OF_RANGE,
        ("snapshot_version",),
    )


def test_context_canonical_bytes_are_deterministic_and_schema_bound() -> None:
    first = admit_fcis_step_execution_context_v1(_step_source())
    second = admit_fcis_step_execution_context_v1(_step_source())
    settlement = admit_fcis_settlement_execution_context_v1(_settlement_source())
    assert type(first) is AdmitOk
    assert type(second) is AdmitOk
    assert type(settlement) is AdmitOk

    first_bytes = encode_fcis_execution_context_v1(
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        first.value,
    )
    assert first_bytes == encode_fcis_execution_context_v1(
        FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
        second.value,
    )
    settlement_bytes = encode_fcis_execution_context_v1(
        FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
        settlement.value,
    )
    assert first_bytes != settlement_bytes
    assert FCIS_STEP_CONTEXT_SCHEMA_ID_V1.encode() in first_bytes
    assert FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1.encode() in settlement_bytes


def test_execution_context_facade_imports_in_a_fresh_process() -> None:
    completed = subprocess.run(
        (
            sys.executable,
            "-c",
            "from src.state.fcis_execution_context import "
            "admit_fcis_step_execution_context_v1; "
            "print(admit_fcis_step_execution_context_v1.__name__)",
        ),
        cwd=_REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout.strip() == "admit_fcis_step_execution_context_v1"
