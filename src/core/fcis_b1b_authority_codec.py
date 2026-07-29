"""Canonical bytes and audit roots for the unmounted FCIS B1B-1 carriers."""

from __future__ import annotations

from typing import cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    DeploymentBootstrapAnchorClaimV2,
    FCISAuthorityHeaderV2,
    V1ToV2MigrationManifestV2,
)

BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2 = "fcis_deployment_bootstrap_anchor_claim"
MIGRATION_MANIFEST_ROOT_DOMAIN_V2 = "fcis_v1_to_v2_migration_manifest"


def _authority_header_projection_v2(value: FCISAuthorityHeaderV2) -> dict[str, object]:
    value.__post_init__()
    return {
        "chain_deployment_id": value.chain_deployment_id,
        "sequence": value.sequence,
        "fee_distribution_configuration_root": value.fee_distribution_configuration_root,
    }


def _bootstrap_anchor_claim_projection_v2(
    value: DeploymentBootstrapAnchorClaimV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "chain_deployment_id": value.chain_deployment_id,
        "expected_migration_manifest_root": value.expected_migration_manifest_root,
    }


def _migration_manifest_projection_v2(
    value: V1ToV2MigrationManifestV2,
) -> dict[str, object]:
    value.__post_init__()
    return {
        "chain_deployment_id": value.chain_deployment_id,
        "expected_v1_pre_root": value.expected_v1_pre_root,
        "fee_distribution_domain_id": value.fee_distribution_domain_id,
        "expected_initial_configuration_root": value.expected_initial_configuration_root,
        "initial_sequence": value.initial_sequence,
        "initial_configuration_version": value.initial_configuration_version,
        "initial_activation_sequence": value.initial_activation_sequence,
        "source_snapshot_version": value.source_snapshot_version,
        "target_snapshot_version": value.target_snapshot_version,
    }


def _envelope_v2(schema_id: str, projection: dict[str, object]) -> bytes:
    return cast(
        bytes,
        canonical_json_bytes(
            {
                "schema": schema_id,
                "value": projection,
            }
        ),
    )


def encode_fcis_b1b_authority_v2(schema_id: str, value: object) -> bytes:
    if type(schema_id) is not str:
        raise TypeError("B1B authority schema ID must be an exact string")
    if schema_id == FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2:
        if type(value) is not FCISAuthorityHeaderV2:
            raise TypeError("authority-header codec requires an exact value")
        return _envelope_v2(schema_id, _authority_header_projection_v2(value))
    if schema_id == DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2:
        if type(value) is not DeploymentBootstrapAnchorClaimV2:
            raise TypeError("bootstrap-anchor-claim codec requires an exact value")
        return _envelope_v2(schema_id, _bootstrap_anchor_claim_projection_v2(value))
    if schema_id == V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2:
        if type(value) is not V1ToV2MigrationManifestV2:
            raise TypeError("migration-manifest codec requires an exact value")
        return _envelope_v2(schema_id, _migration_manifest_projection_v2(value))
    raise ValueError("unknown B1B authority carrier schema")


def canonical_bootstrap_anchor_claim_root_v2(
    value: DeploymentBootstrapAnchorClaimV2,
) -> str:
    payload = encode_fcis_b1b_authority_v2(
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
        value,
    )
    return cast(
        str,
        sha256_hex(domain_sep_bytes(BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2, version=2) + payload),
    )


def canonical_v1_to_v2_migration_manifest_root_v2(
    value: V1ToV2MigrationManifestV2,
) -> str:
    payload = encode_fcis_b1b_authority_v2(
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
        value,
    )
    return cast(
        str,
        sha256_hex(domain_sep_bytes(MIGRATION_MANIFEST_ROOT_DOMAIN_V2, version=2) + payload),
    )


__all__ = (
    "BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2",
    "MIGRATION_MANIFEST_ROOT_DOMAIN_V2",
    "canonical_bootstrap_anchor_claim_root_v2",
    "canonical_v1_to_v2_migration_manifest_root_v2",
    "encode_fcis_b1b_authority_v2",
)
