"""Immutable shared identifiers for the unmounted FCIS M6 research stack.

This module deliberately contains constants and immutable tuples only. It does
not provide a mutable registry, plugin discovery, authority construction, or
runtime dispatch. Later integration tasks may import these values and must
preserve their exact bytes and version labels.
"""

from __future__ import annotations

from typing import Final

M6_PROFILE_REGISTRY_VERSION_V1: Final[str] = "zenodex/fcis/m6-profile-registry/v1"

SEMANTIC_ALLOCATOR_PROFILE_ID_V1: Final[str] = (
    "adaptive-global-quota-entitlement/three-role/v1"
)
SRGD_REPRESENTATION_PROFILE_ID_V1: Final[str] = "srgd-deficit/v1"
AGQE_REPRESENTATION_PROFILE_ID_V1: Final[str] = "agqe-surplus/v1"

FIXED_ROLE_ORDER_ID_V1: Final[str] = (
    "fee-occurrence/role-order/buyback-treasury-rewards/v1"
)
FIXED_ROLE_ORDER_V1: Final[tuple[str, str, str]] = (
    "buyback",
    "treasury",
    "rewards",
)
FEE_DISTRIBUTION_DOMAIN_ID_V1: Final[str] = "protocol-fees"

SLNF_VERSION_V1: Final[str] = "zenodex/fcis/fee-occurrence-slnf/v1"
SOURCE_BOUND_OCCURRENCE_VERSION_V2: Final[str] = (
    "zenodex/fcis/fee-occurrence/source-bound-extractor/v2"
)
LINEAGE_CLOSURE_VERSION_V1: Final[str] = "zenodex/fcis/lineage-closure/v1"
LINEAGE_RECEIPT_EXTENSION_VERSION_V1: Final[str] = (
    "zenodex/fcis/lineage-receipt-extension/v1"
)
LINEAGE_BUNDLE_EXTENSION_VERSION_V1: Final[str] = (
    "zenodex/fcis/lineage-bundle-extension/v1"
)

C3_CLAIM_KEYS_V1: Final[tuple[str, ...]] = (
    "source/command_root",
    "source/execution_context_hash",
    "source/pre_state_root",
    "source/next_state_root",
    "source/support_root",
    "source/support_set_commitment",
    "source/snapshot_commitment",
    "candidate/patch_root",
    "candidate/commit_plan_root",
    "fee/boundary_root",
    "fee/policy_root",
    "fee/witness_tuple_root",
    "fee/semantic_stream_root",
    "fee/lineage_stream_root",
    "authority/budget_hash",
    "authority/acceptance_receipt_root",
    "durability/outbox_plan_root",
    "durability/base_bundle_root",
    "derived/evaluation_certificate_root",
    "derived/receipt_certificate_root",
    "derived/bundle_certificate_root",
    "derived/outbox_certificate_root",
)

TCG_LINEAGE_VERSION_V1: Final[str] = "zenodex/fcis/tcg/lineage/v1"
TCG_TOPOLOGY_VERSION_V1: Final[str] = "zenodex/fcis/tcg/topology/v1"
TCG_EDGE_SUBJECT_VERSION_V1: Final[str] = "zenodex/fcis/tcg/edge-subject/v1"
TCG_INSTANCE_VERSION_V1: Final[str] = "zenodex/fcis/tcg/instance/v1"

DRA_PUBLICATION_ATOM_VERSION_V1: Final[str] = "zenodex/fcis/dra/publication-atom/v1"
DRA_AUTHORIZED_HISTORY_VERSION_V1: Final[str] = (
    "zenodex/fcis/dra/authorized-history/v1"
)
DRA_DURABLE_LAYOUT_VERSION_V1: Final[str] = "zenodex/fcis/dra/durable-snapshot/v1"
DRA_REOPEN_AUTHORIZATION_VERSION_V2: Final[str] = (
    "zenodex/fcis/dra/reopen-authorization/v2"
)

PROOF_CONTEXT_VERSION_V1: Final[str] = "zenodex/fcis/proof-context/v1"
ANF_VERSION_V1: Final[str] = "zenodex/fcis/authority-normal-form/v1"

M6_DOMAIN_IDENTIFIERS_V1: Final[tuple[str, ...]] = (
    FEE_DISTRIBUTION_DOMAIN_ID_V1,
    SLNF_VERSION_V1,
    SOURCE_BOUND_OCCURRENCE_VERSION_V2,
    LINEAGE_CLOSURE_VERSION_V1,
    LINEAGE_RECEIPT_EXTENSION_VERSION_V1,
    LINEAGE_BUNDLE_EXTENSION_VERSION_V1,
    TCG_LINEAGE_VERSION_V1,
    TCG_TOPOLOGY_VERSION_V1,
    TCG_EDGE_SUBJECT_VERSION_V1,
    TCG_INSTANCE_VERSION_V1,
    DRA_PUBLICATION_ATOM_VERSION_V1,
    DRA_AUTHORIZED_HISTORY_VERSION_V1,
    DRA_DURABLE_LAYOUT_VERSION_V1,
    DRA_REOPEN_AUTHORIZATION_VERSION_V2,
    PROOF_CONTEXT_VERSION_V1,
    ANF_VERSION_V1,
)

M6_IDENTIFIER_VALUES_V1: Final[tuple[str, ...]] = (
    M6_PROFILE_REGISTRY_VERSION_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    *M6_DOMAIN_IDENTIFIERS_V1,
    *C3_CLAIM_KEYS_V1,
)

__all__ = (
    "AGQE_REPRESENTATION_PROFILE_ID_V1",
    "ANF_VERSION_V1",
    "C3_CLAIM_KEYS_V1",
    "DRA_AUTHORIZED_HISTORY_VERSION_V1",
    "DRA_DURABLE_LAYOUT_VERSION_V1",
    "DRA_PUBLICATION_ATOM_VERSION_V1",
    "DRA_REOPEN_AUTHORIZATION_VERSION_V2",
    "FEE_DISTRIBUTION_DOMAIN_ID_V1",
    "FIXED_ROLE_ORDER_ID_V1",
    "FIXED_ROLE_ORDER_V1",
    "LINEAGE_BUNDLE_EXTENSION_VERSION_V1",
    "LINEAGE_CLOSURE_VERSION_V1",
    "LINEAGE_RECEIPT_EXTENSION_VERSION_V1",
    "M6_DOMAIN_IDENTIFIERS_V1",
    "M6_IDENTIFIER_VALUES_V1",
    "M6_PROFILE_REGISTRY_VERSION_V1",
    "PROOF_CONTEXT_VERSION_V1",
    "SEMANTIC_ALLOCATOR_PROFILE_ID_V1",
    "SLNF_VERSION_V1",
    "SOURCE_BOUND_OCCURRENCE_VERSION_V2",
    "SRGD_REPRESENTATION_PROFILE_ID_V1",
    "TCG_EDGE_SUBJECT_VERSION_V1",
    "TCG_INSTANCE_VERSION_V1",
    "TCG_LINEAGE_VERSION_V1",
    "TCG_TOPOLOGY_VERSION_V1",
)
