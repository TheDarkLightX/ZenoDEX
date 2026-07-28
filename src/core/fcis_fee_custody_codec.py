"""Canonical schema-bound encoding for exact FCIS fee-custody values."""

from __future__ import annotations

from ..state.canonical import bounded_json_utf8_size, canonical_json_bytes
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from ..state.state_snapshot_values import CommittedBalanceTableV1
from ..state.state_transitions import CanonicalBalancePatchV1
from .fcis_fee_custody_values import (
    ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2,
    ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2,
    FEE_ACCUMULATOR_SCHEMA_ID_V2,
    FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2,
    PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2,
    AssetFeeDistributionV2,
    CommittedFeeAccumulatorStateV2,
    FeeCustodyTransitionOkV2,
    FeeDistributionPolicyV2,
    FeeDustEntryV2,
    ProtocolFeeCreditV2,
)


def _credit_projection_v2(value: ProtocolFeeCreditV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "source_custody_pubkey": value.source_custody_pubkey,
        "asset": value.asset,
        "amount": value.amount,
    }


def _policy_projection_v2(value: FeeDistributionPolicyV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "buyback_bps": value.buyback_bps,
        "treasury_bps": value.treasury_bps,
        "rewards_bps": value.rewards_bps,
        "buyback_custody_pubkey": value.buyback_custody_pubkey,
        "treasury_custody_pubkey": value.treasury_custody_pubkey,
        "rewards_custody_pubkey": value.rewards_custody_pubkey,
    }


def _dust_projection_v2(value: FeeDustEntryV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "source_custody_pubkey": value.source_custody_pubkey,
        "asset": value.asset,
        "amount": value.amount,
    }


def _accumulator_projection_v2(
    value: CommittedFeeAccumulatorStateV2,
) -> dict[str, object]:
    value.__post_init__()
    return {"entries": tuple(_dust_projection_v2(entry) for entry in value.entries)}


def _distribution_projection_v2(
    value: AssetFeeDistributionV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "source_custody_pubkey": value.source_custody_pubkey,
        "asset": value.asset,
        "buyback_custody_pubkey": value.buyback_custody_pubkey,
        "treasury_custody_pubkey": value.treasury_custody_pubkey,
        "rewards_custody_pubkey": value.rewards_custody_pubkey,
        "buyback_amount": value.buyback_amount,
        "treasury_amount": value.treasury_amount,
        "rewards_amount": value.rewards_amount,
        "dust_carried": value.dust_carried,
    }


def _balance_projection_v2(
    value: CommittedBalanceTableV1,
) -> tuple[dict[str, object], ...]:
    if type(value) is not CommittedBalanceTableV1:
        raise TypeError("fee custody balance codec requires an exact value")
    value.__post_init__()
    return tuple(
        {
            "pubkey": key[0],
            "asset": key[1],
            "amount": amount,
        }
        for key, amount in value.entries
    )


def _balance_patch_projection_v2(
    value: CanonicalBalancePatchV1 | None,
) -> dict[str, object] | None:
    if value is None:
        return None
    if type(value) is not CanonicalBalancePatchV1:
        raise TypeError("fee custody balance patch codec requires an exact value or None")
    value.__post_init__()
    return {
        "writes": tuple(
            {
                "key": write.key,
                "expected_old": write.expected_old,
                "replacement": write.replacement,
            }
            for write in value.writes
        )
    }


def _transition_result_projection_v2(
    value: FeeCustodyTransitionOkV2,
) -> dict[str, object]:
    if type(value) is not FeeCustodyTransitionOkV2:
        raise TypeError("fee custody transition result codec requires an exact value")
    if type(value.accumulator) is not CommittedFeeAccumulatorStateV2:
        raise TypeError("fee custody transition result accumulator must be exact")
    if type(value.distributions) is not tuple or any(
        type(item) is not AssetFeeDistributionV2 for item in value.distributions
    ):
        raise TypeError("fee custody transition result distributions must be exact")
    return {
        "balances": _balance_projection_v2(value.balances),
        "balance_patch": _balance_patch_projection_v2(value.balance_patch),
        "accumulator": _accumulator_projection_v2(value.accumulator),
        "distributions": tuple(_distribution_projection_v2(item) for item in value.distributions),
    }


def _projection_for_schema_v2(schema_id: str, value: object) -> object:
    if schema_id == PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2:
        if type(value) is not ProtocolFeeCreditV2:
            raise TypeError("protocol fee credit codec requires an exact value")
        return _credit_projection_v2(value)
    if schema_id == PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2:
        if type(value) is not tuple or any(type(item) is not ProtocolFeeCreditV2 for item in value):
            raise TypeError("protocol fee credit batch codec requires an exact tuple")
        return tuple(_credit_projection_v2(item) for item in value)
    if schema_id == FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2:
        if type(value) is not FeeDistributionPolicyV2:
            raise TypeError("fee distribution policy codec requires an exact value")
        return _policy_projection_v2(value)
    if schema_id == FEE_ACCUMULATOR_SCHEMA_ID_V2:
        if type(value) is not CommittedFeeAccumulatorStateV2:
            raise TypeError("fee accumulator codec requires an exact value")
        return _accumulator_projection_v2(value)
    if schema_id == ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2:
        if type(value) is not AssetFeeDistributionV2:
            raise TypeError("asset fee distribution codec requires an exact value")
        return _distribution_projection_v2(value)
    if schema_id == ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2:
        if type(value) is not tuple or any(
            type(item) is not AssetFeeDistributionV2 for item in value
        ):
            raise TypeError("asset fee distribution batch codec requires an exact tuple")
        return tuple(_distribution_projection_v2(item) for item in value)
    if schema_id == FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2:
        if type(value) is not FeeCustodyTransitionOkV2:
            raise TypeError("fee custody transition result codec requires an exact value")
        return _transition_result_projection_v2(value)
    raise ValueError("unknown FCIS fee-custody schema")


def encode_fcis_fee_custody_v2(schema_id: str, value: object) -> bytes:
    """Encode one exact V2 value under an explicit schema envelope."""

    if type(schema_id) is not str:
        raise TypeError("fee-custody schema ID must be an exact string")
    envelope = {
        "schema": schema_id,
        "value": _projection_for_schema_v2(schema_id, value),
    }
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return canonical_json_bytes(envelope)


__all__ = ("encode_fcis_fee_custody_v2",)
