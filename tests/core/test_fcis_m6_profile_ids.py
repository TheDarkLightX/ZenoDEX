"""Mutation-killing tests for the immutable M6 identifier registry."""

from __future__ import annotations

from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    ANF_VERSION_V1,
    C3_CLAIM_KEYS_V1,
    DRA_DURABLE_LAYOUT_VERSION_V1,
    FEE_DISTRIBUTION_DOMAIN_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    FIXED_ROLE_ORDER_V1,
    LINEAGE_CLOSURE_VERSION_V1,
    M6_DOMAIN_IDENTIFIERS_V1,
    M6_IDENTIFIER_VALUES_V1,
    M6_PROFILE_REGISTRY_VERSION_V1,
    PROOF_CONTEXT_VERSION_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SLNF_VERSION_V1,
    SOURCE_BOUND_OCCURRENCE_VERSION_V2,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
    TCG_TOPOLOGY_VERSION_V1,
)


def test_semantic_profile_is_frozen_and_not_a_representation_alias() -> None:
    assert (
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1
        == "adaptive-global-quota-entitlement/three-role/v1"
    )
    assert SEMANTIC_ALLOCATOR_PROFILE_ID_V1 not in {
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        AGQE_REPRESENTATION_PROFILE_ID_V1,
    }


def test_representation_profiles_are_distinct() -> None:
    assert SRGD_REPRESENTATION_PROFILE_ID_V1 == "srgd-deficit/v1"
    assert AGQE_REPRESENTATION_PROFILE_ID_V1 == "agqe-surplus/v1"
    assert SRGD_REPRESENTATION_PROFILE_ID_V1 != AGQE_REPRESENTATION_PROFILE_ID_V1


def test_fixed_role_order_mutant_is_rejected_by_exact_tuple() -> None:
    assert FIXED_ROLE_ORDER_ID_V1 == (
        "fee-occurrence/role-order/buyback-treasury-rewards/v1"
    )
    assert FIXED_ROLE_ORDER_V1 == ("buyback", "treasury", "rewards")


def test_domain_separator_collision_mutant_is_rejected() -> None:
    assert FEE_DISTRIBUTION_DOMAIN_ID_V1 == "protocol-fees"
    assert len(M6_DOMAIN_IDENTIFIERS_V1) == len(set(M6_DOMAIN_IDENTIFIERS_V1))
    assert len(M6_IDENTIFIER_VALUES_V1) == len(set(M6_IDENTIFIER_VALUES_V1))


def test_cross_layer_versions_are_explicit_and_distinct() -> None:
    assert SLNF_VERSION_V1 == "zenodex/fcis/fee-occurrence-slnf/v1"
    assert SOURCE_BOUND_OCCURRENCE_VERSION_V2.endswith("/v2")
    assert SOURCE_BOUND_OCCURRENCE_VERSION_V2 != SLNF_VERSION_V1
    assert LINEAGE_CLOSURE_VERSION_V1.endswith("/v1")
    assert TCG_TOPOLOGY_VERSION_V1 == "zenodex/fcis/tcg/topology/v1"
    assert DRA_DURABLE_LAYOUT_VERSION_V1 == "zenodex/fcis/dra/durable-snapshot/v1"
    assert PROOF_CONTEXT_VERSION_V1 == "zenodex/fcis/proof-context/v1"
    assert ANF_VERSION_V1 == "zenodex/fcis/authority-normal-form/v1"
    assert M6_PROFILE_REGISTRY_VERSION_V1.endswith("/v1")


def test_c3_claim_keys_are_closed_and_unique() -> None:
    assert len(C3_CLAIM_KEYS_V1) == 22
    assert len(C3_CLAIM_KEYS_V1) == len(set(C3_CLAIM_KEYS_V1))
    assert C3_CLAIM_KEYS_V1[0] == "source/command_root"
    assert C3_CLAIM_KEYS_V1[-1] == "derived/outbox_certificate_root"
