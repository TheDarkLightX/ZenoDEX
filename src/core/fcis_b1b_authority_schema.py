"""Closed field registries for the unmounted FCIS B1B-1 carriers."""

from __future__ import annotations

from types import MappingProxyType

from .fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    DeploymentBootstrapAnchorClaimSourceV2,
    FCISAuthorityHeaderSourceV2,
    V1ToV2MigrationManifestSourceV2,
)

FCIS_AUTHORITY_HEADER_FIELDS_V2 = (
    "chain_deployment_id",
    "sequence",
    "fee_distribution_configuration_root",
)
DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2 = (
    "chain_deployment_id",
    "expected_migration_manifest_root",
)
V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2 = (
    "chain_deployment_id",
    "expected_v1_pre_root",
    "fee_distribution_domain_id",
    "expected_initial_configuration_root",
    "initial_sequence",
    "initial_configuration_version",
    "initial_activation_sequence",
    "source_snapshot_version",
    "target_snapshot_version",
)

FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2 = MappingProxyType(
    {
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2: FCIS_AUTHORITY_HEADER_FIELDS_V2,
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2: (
            DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2
        ),
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2: V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2,
    }
)
FCIS_B1B_AUTHORITY_SOURCE_TYPES_BY_SCHEMA_V2 = MappingProxyType(
    {
        FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2: FCISAuthorityHeaderSourceV2,
        DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2: (
            DeploymentBootstrapAnchorClaimSourceV2
        ),
        V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2: V1ToV2MigrationManifestSourceV2,
    }
)
FCIS_B1B_AUTHORITY_REGISTERED_SCHEMA_IDS_V2 = tuple(
    FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2
)

if tuple(FCIS_B1B_AUTHORITY_SOURCE_TYPES_BY_SCHEMA_V2) != (
    FCIS_B1B_AUTHORITY_REGISTERED_SCHEMA_IDS_V2
):
    raise RuntimeError("B1B authority carrier registry drift")

__all__ = (
    "DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2",
    "FCIS_AUTHORITY_HEADER_FIELDS_V2",
    "FCIS_B1B_AUTHORITY_FIELDS_BY_SCHEMA_V2",
    "FCIS_B1B_AUTHORITY_REGISTERED_SCHEMA_IDS_V2",
    "FCIS_B1B_AUTHORITY_SOURCE_TYPES_BY_SCHEMA_V2",
    "V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2",
)
