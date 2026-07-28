"""Canonical schema-bound bytes for unmounted SRGD-v1 candidate values."""

from __future__ import annotations

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    sha256_hex,
)
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from .fcis_fee_apportionment_values import (
    ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
    ASSET_FEE_ALLOCATION_SCHEMA_ID_V2,
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2,
    FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
    FEE_DEFICIT_ENTRY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    AssetFeeAllocationV2,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)


def _key_projection_v2(value: FeeApportionmentKeyV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "fee_distribution_domain_id": value.fee_distribution_domain_id,
        "asset": value.asset,
    }


def _candidate_projection_v2(value: FeeAmountCandidateV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "key": _key_projection_v2(value.key),
        "amount": value.amount,
    }


def _deficit_entry_projection_v2(value: FeeDeficitEntryV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "key": _key_projection_v2(value.key),
        "deficit_buyback": value.deficit_buyback,
        "deficit_treasury": value.deficit_treasury,
    }


def _state_projection_v2(
    value: CommittedFeeApportionmentStateV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "algorithm_version": value.algorithm_version,
        "entries": tuple(_deficit_entry_projection_v2(entry) for entry in value.entries),
    }


def _policy_projection_v2(value: FeeDistributionPolicyV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "buyback_bps": value.buyback_bps,
        "treasury_bps": value.treasury_bps,
        "rewards_bps": value.rewards_bps,
        "buyback_destination": value.buyback_destination,
        "treasury_destination": value.treasury_destination,
        "rewards_destination": value.rewards_destination,
    }


def _allocation_projection_v2(value: AssetFeeAllocationV2) -> dict[str, object]:
    value._revalidate()
    return {
        "key": _key_projection_v2(value.key),
        "amount": value.amount,
        "buyback_destination": value.buyback_destination,
        "treasury_destination": value.treasury_destination,
        "rewards_destination": value.rewards_destination,
        "buyback_fraction": value.buyback_fraction,
        "treasury_fraction": value.treasury_fraction,
        "rewards_fraction": value.rewards_fraction,
        "buyback_bonus": value.buyback_bonus,
        "treasury_bonus": value.treasury_bonus,
        "rewards_bonus": value.rewards_bonus,
        "buyback_amount": value.buyback_amount,
        "treasury_amount": value.treasury_amount,
        "rewards_amount": value.rewards_amount,
        "deficit_buyback_pre": value.deficit_buyback_pre,
        "deficit_treasury_pre": value.deficit_treasury_pre,
        "deficit_rewards_pre": value.deficit_rewards_pre,
        "deficit_buyback_post": value.deficit_buyback_post,
        "deficit_treasury_post": value.deficit_treasury_post,
        "deficit_rewards_post": value.deficit_rewards_post,
    }


def _result_projection_v2(
    value: FeeApportionmentTransitionOkV2,
) -> dict[str, object]:
    value._revalidate()
    return {
        "state": _state_projection_v2(value.state),
        "allocations": tuple(
            _allocation_projection_v2(allocation) for allocation in value.allocations
        ),
    }


def _projection_for_schema_v2(schema_id: str, value: object) -> object:
    if schema_id == FEE_APPORTIONMENT_KEY_SCHEMA_ID_V2:
        if type(value) is not FeeApportionmentKeyV2:
            raise TypeError("fee apportionment key codec requires an exact value")
        return _key_projection_v2(value)
    if schema_id == FEE_AMOUNT_CANDIDATE_SCHEMA_ID_V2:
        if type(value) is not FeeAmountCandidateV2:
            raise TypeError("fee amount candidate codec requires an exact value")
        return _candidate_projection_v2(value)
    if schema_id == FEE_AMOUNT_CANDIDATE_BATCH_SCHEMA_ID_V2:
        if type(value) is not tuple or any(
            type(candidate) is not FeeAmountCandidateV2 for candidate in value
        ):
            raise TypeError("fee amount candidate batch codec requires an exact tuple")
        return tuple(_candidate_projection_v2(candidate) for candidate in value)
    if schema_id == FEE_DEFICIT_ENTRY_SCHEMA_ID_V2:
        if type(value) is not FeeDeficitEntryV2:
            raise TypeError("fee deficit entry codec requires an exact value")
        return _deficit_entry_projection_v2(value)
    if schema_id == COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2:
        if type(value) is not CommittedFeeApportionmentStateV2:
            raise TypeError("fee apportionment state codec requires an exact value")
        return _state_projection_v2(value)
    if schema_id == FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2:
        if type(value) is not FeeDistributionPolicyV2:
            raise TypeError("fee distribution policy codec requires an exact value")
        return _policy_projection_v2(value)
    if schema_id == ASSET_FEE_ALLOCATION_SCHEMA_ID_V2:
        if type(value) is not AssetFeeAllocationV2:
            raise TypeError("asset fee allocation codec requires an exact value")
        return _allocation_projection_v2(value)
    if schema_id == ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2:
        if type(value) is not tuple or any(
            type(allocation) is not AssetFeeAllocationV2 for allocation in value
        ):
            raise TypeError("asset fee allocation batch codec requires an exact tuple")
        return tuple(_allocation_projection_v2(allocation) for allocation in value)
    if schema_id == FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2:
        if type(value) is not FeeApportionmentTransitionOkV2:
            raise TypeError("fee apportionment result codec requires an exact value")
        return _result_projection_v2(value)
    raise ValueError("unknown FCIS fee-apportionment schema")


def encode_fcis_fee_apportionment_v2(schema_id: str, value: object) -> bytes:
    """Encode one exact candidate value under an explicit V2 schema."""

    if type(schema_id) is not str:
        raise TypeError("fee-apportionment schema ID must be an exact string")
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


def canonical_sha256_fcis_fee_apportionment_v2(
    schema_id: str,
    value: object,
) -> str:
    """Evidence digest only; this is not a protocol state root."""

    return sha256_hex(encode_fcis_fee_apportionment_v2(schema_id, value))


__all__ = (
    "canonical_sha256_fcis_fee_apportionment_v2",
    "encode_fcis_fee_apportionment_v2",
)
