"""Canonical bytes and roots for unmounted fee-distribution configuration."""

from __future__ import annotations

from typing import cast

from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
)
from .fcis_fee_apportionment_codec import encode_fcis_fee_apportionment_v2
from .fcis_fee_apportionment_values import (
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    FeeDistributionPolicyV2,
)
from .fcis_fee_distribution_configuration_values import (
    FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)


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


def _body_projection_v2(
    value: FeeDistributionConfigurationBodyV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "chain_deployment_id": value.chain_deployment_id,
        "configuration_version": value.configuration_version,
        "fee_distribution_domain_id": value.fee_distribution_domain_id,
        "policy_root": value.policy_root,
        "policy": _policy_projection_v2(value.policy),
        "activation_sequence": value.activation_sequence,
        "algorithm_version": value.algorithm_version,
        "accepted_language_version": value.accepted_language_version,
    }


def _claim_projection_v2(
    value: FeeDistributionConfigurationClaimV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "body": _body_projection_v2(value.body),
        "configuration_root": value.configuration_root,
    }


def _envelope_v2(schema_id: str, projection: object) -> bytes:
    envelope = {"schema": schema_id, "value": projection}
    bounded_json_utf8_size(
        envelope,
        max_bytes=MAX_CANONICAL_BYTES_V1,
        max_depth=MAX_ADMISSION_DEPTH_V1,
        max_items=MAX_ADMISSION_NODES_V1,
    )
    return cast(bytes, canonical_json_bytes(envelope))


def encode_fee_distribution_configuration_v2(
    schema_id: str,
    value: object,
) -> bytes:
    if type(schema_id) is not str:
        raise TypeError("fee configuration schema ID must be an exact string")
    if schema_id == FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2:
        if type(value) is not FeeDistributionConfigurationBodyV2:
            raise TypeError("fee configuration body codec requires an exact value")
        return _envelope_v2(schema_id, _body_projection_v2(value))
    if schema_id == FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2:
        if type(value) is FeeDistributionConfigurationClaimV2:
            return _envelope_v2(schema_id, _claim_projection_v2(value))
        raise TypeError("fee configuration claim codec requires an exact value")
    if schema_id == VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2:
        if type(value) is ValidatedFeeDistributionConfigurationClaimV2:
            claim = FeeDistributionConfigurationClaimV2(
                value.body,
                value.configuration_root,
            )
            return _envelope_v2(schema_id, _claim_projection_v2(claim))
        raise TypeError("validated fee configuration claim codec requires an exact value")
    raise ValueError("unknown fee distribution configuration schema")


def canonical_fee_distribution_policy_root_v2(
    policy: FeeDistributionPolicyV2,
) -> str:
    policy_bytes = encode_fcis_fee_apportionment_v2(
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        policy,
    )
    return cast(
        str,
        sha256_hex(domain_sep_bytes("fee_distribution_policy", version=2) + policy_bytes),
    )


def canonical_fee_distribution_configuration_root_v2(
    body: FeeDistributionConfigurationBodyV2,
) -> str:
    body_bytes = encode_fee_distribution_configuration_v2(
        FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
        body,
    )
    return cast(
        str,
        sha256_hex(domain_sep_bytes("fee_distribution_configuration", version=2) + body_bytes),
    )


__all__ = (
    "canonical_fee_distribution_configuration_root_v2",
    "canonical_fee_distribution_policy_root_v2",
    "encode_fee_distribution_configuration_v2",
)
