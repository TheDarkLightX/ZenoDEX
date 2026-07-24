"""Canonical bytes for admitted FCIS execution-context values."""

from __future__ import annotations

from .canonical import bounded_json_utf8_size, canonical_json_bytes
from .fcis_execution_context_values import (
    FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1,
    FCIS_STEP_CONTEXT_SCHEMA_ID_V1,
    FCISFeeSplitPolicyV1,
    FCISSettlementExecutionContextV1,
    FCISStepExecutionContextV1,
    settlement_mode_label_v1,
)
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)


def _settlement_projection_v1(
    value: FCISSettlementExecutionContextV1,
) -> dict[str, object]:
    if type(value) is not FCISSettlementExecutionContextV1:
        raise TypeError("settlement context codec requires an exact owned value")
    return {
        "now": value.now,
        "min_lp_position_age_seconds": value.min_lp_position_age_seconds,
        "mode": settlement_mode_label_v1(value.mode),
        "allow_cow_netting": value.allow_cow_netting,
        "allow_snapshot_bound_quote_bindings": value.allow_snapshot_bound_quote_bindings,
        "protocol_fee_share_bps": value.protocol_fee_share_bps,
        "protocol_fee_recipient_pubkey": value.protocol_fee_recipient_pubkey,
    }


def _fee_split_projection_v1(
    value: FCISFeeSplitPolicyV1 | None,
) -> dict[str, object] | None:
    if value is None:
        return None
    if type(value) is not FCISFeeSplitPolicyV1:
        raise TypeError("fee split codec requires None or an exact owned value")
    return {
        "buyback_bps": value.buyback_bps,
        "treasury_bps": value.treasury_bps,
        "rewards_bps": value.rewards_bps,
    }


def _lp_duration_projection_v1(
    value: LPDurationRiskPolicyV1 | None,
) -> dict[str, object] | None:
    if value is None:
        return None
    if type(value) is not LPDurationRiskPolicyV1:
        raise TypeError("LP duration codec requires None or an exact owned value")
    return {
        "base_age_seconds": value.base_age_seconds,
        "max_age_seconds": value.max_age_seconds,
        "churn_window_seconds": value.churn_window_seconds,
        "decay_seconds": value.decay_seconds,
        "multiplier": value.multiplier,
        "max_churn_tier": value.max_churn_tier,
    }


def _step_projection_v1(value: FCISStepExecutionContextV1) -> dict[str, object]:
    if type(value) is not FCISStepExecutionContextV1:
        raise TypeError("step context codec requires an exact owned value")
    return {
        "settlement": _settlement_projection_v1(value.settlement),
        "require_all_nonces": value.require_all_nonces,
        "reject_settlements_with_rejected_intents": (
            value.reject_settlements_with_rejected_intents
        ),
        "fee_split_policy": _fee_split_projection_v1(value.fee_split_policy),
        "lp_duration_policy": _lp_duration_projection_v1(value.lp_duration_policy),
        "snapshot_version": value.snapshot_version,
    }


def encode_fcis_execution_context_v1(schema_id: str, value: object) -> bytes:
    """Encode one exact context under a schema-bound canonical envelope."""

    if schema_id == FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1:
        if type(value) is not FCISSettlementExecutionContextV1:
            raise TypeError("settlement context schema and output disagree")
        projection = _settlement_projection_v1(value)
    elif schema_id == FCIS_STEP_CONTEXT_SCHEMA_ID_V1:
        if type(value) is not FCISStepExecutionContextV1:
            raise TypeError("step context schema and output disagree")
        projection = _step_projection_v1(value)
    else:
        raise ValueError("unknown FCIS execution-context schema")

    envelope = {"schema": schema_id, "value": projection}
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return canonical_json_bytes(envelope)


__all__ = ("encode_fcis_execution_context_v1",)
