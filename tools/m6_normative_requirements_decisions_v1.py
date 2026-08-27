"""Declarative non-lane target decisions for M6 requirements V1.

This module is an IO-free local decision table.  It identifies obligations
that are global by construction and source concepts absent from the provisional
lane-capability manifest.  Its entries are research-only mapping inputs; they
are neither implementation evidence nor an independent oracle.
"""

from __future__ import annotations

from typing import Final

ConceptSpecV1 = tuple[str, str, str]
RequirementTargetSpecsV1 = tuple[tuple[str, tuple[str, ...]], ...]

GLOBAL_OBLIGATION_SPECS_V1: Final[tuple[ConceptSpecV1, ...]] = (
    (
        "closed_command_language_and_profile_isolation",
        "Closed command language and exact profile, deployment, and release isolation",
        "GLOBAL_OBLIGATION_UNIMPLEMENTED",
    ),
    (
        "whole_economic_delta_certificate",
        "Complete whole-economic delta and conservation certificate",
        "GLOBAL_OBLIGATION_UNIMPLEMENTED",
    ),
    (
        "committed_effect_membership",
        "Committed effect membership before external delivery",
        "GLOBAL_OBLIGATION_UNIMPLEMENTED",
    ),
    (
        "atomic_publication_reopen_authority",
        "Atomic publication, retry classification, and reopen authority",
        "GLOBAL_OBLIGATION_UNIMPLEMENTED",
    ),
    (
        "workflow_model_evidence_coverage_registry",
        "Closed workflow, model, implementation, adapter, and evidence coverage registry",
        "GLOBAL_OBLIGATION_UNIMPLEMENTED",
    ),
)

MISSING_TARGET_CONCEPT_SPECS_V1: Final[tuple[ConceptSpecV1, ...]] = (
    (
        "pending_asset_bearing_intent_terminal_owner",
        "Terminal owner for every pending asset-bearing intent",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "perps_request_terminal_owner",
        "Cancellation, expiry, or permanent rejection owner for each pending perps request",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "generic_non_managed_issue",
        "Issue operation for an explicitly allowed generic non-managed asset profile",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "generic_non_managed_burn",
        "Burn operation for an explicitly allowed generic non-managed asset profile",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "perps_realized_pnl_settlement",
        "Exact realized profit-and-loss settlement for a perps epoch",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "zusd_faucet_issuance_rejection",
        "Explicit rejection surface for legacy or test-only zUSD faucet issuance",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "sealed_auction_fee_allocation",
        "Fee allocation owned by sealed-auction settlement",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "sealed_auction_residue_terminal_disposition",
        "Terminal owner for every sealed-auction rounding residue",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "sealed_auction_batch_terminal_state",
        "Explicit terminal state for a settled, cancelled, or expired auction batch",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "sealed_auction_fee_terminal_disposition",
        "Terminal disposition for every sealed-auction fee when a batch cancels or expires",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
        "Terminal disposition for every sealed-auction commitment, bond, inventory reservation, and payment reservation",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
    (
        "external_effect_delivery",
        "Delivery of an exact committed external effect to its registered destination",
        "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST",
    ),
)

GLOBAL_OBLIGATION_EDGE_SPECS_V1: Final[RequirementTargetSpecsV1] = (
    ("RSE-002", ("closed_command_language_and_profile_isolation",)),
    ("RSE-003", ("whole_economic_delta_certificate",)),
    ("RSE-009", ("committed_effect_membership",)),
    ("RSE-010", ("atomic_publication_reopen_authority",)),
    ("RSE-011", ("workflow_model_evidence_coverage_registry",)),
    ("WF-14", ("atomic_publication_reopen_authority",)),
    (
        "WF-17",
        ("atomic_publication_reopen_authority", "workflow_model_evidence_coverage_registry"),
    ),
    ("BDD-033", ("atomic_publication_reopen_authority",)),
    ("BDD-050", ("closed_command_language_and_profile_isolation",)),
    ("BDD-055", ("atomic_publication_reopen_authority",)),
    ("BDD-057", ("atomic_publication_reopen_authority",)),
    ("BDD-058", ("atomic_publication_reopen_authority",)),
    ("BDD-059", ("atomic_publication_reopen_authority",)),
    ("BDD-060", ("atomic_publication_reopen_authority",)),
    ("BDD-061", ("committed_effect_membership",)),
    ("BDD-062", ("committed_effect_membership",)),
    ("BDD-069", ("workflow_model_evidence_coverage_registry",)),
    ("BDD-070", ("workflow_model_evidence_coverage_registry",)),
    ("BDD-071", ("atomic_publication_reopen_authority",)),
    (
        "BDD-072",
        ("atomic_publication_reopen_authority", "closed_command_language_and_profile_isolation"),
    ),
    ("BDD-080", ("atomic_publication_reopen_authority",)),
    ("BDD-081", ("atomic_publication_reopen_authority",)),
    (
        "CE-004",
        ("atomic_publication_reopen_authority", "committed_effect_membership"),
    ),
)

MISSING_TARGET_EDGE_SPECS_V1: Final[RequirementTargetSpecsV1] = (
    ("RSE-007", ("generic_non_managed_issue", "generic_non_managed_burn")),
    (
        "RSE-008",
        ("pending_asset_bearing_intent_terminal_owner", "perps_request_terminal_owner"),
    ),
    ("BDD-018", ("zusd_faucet_issuance_rejection",)),
    ("BDD-041", ("perps_realized_pnl_settlement",)),
    (
        "BDD-077",
        (
            "sealed_auction_fee_allocation",
            "sealed_auction_residue_terminal_disposition",
            "sealed_auction_batch_terminal_state",
        ),
    ),
    (
        "BDD-079",
        (
            "sealed_auction_batch_terminal_state",
            "sealed_auction_fee_terminal_disposition",
            "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
        ),
    ),
    ("WF-15", ("external_effect_delivery",)),
    ("BDD-061", ("external_effect_delivery",)),
    ("BDD-063", ("external_effect_delivery",)),
    ("BDD-064", ("external_effect_delivery",)),
    ("RSE-009", ("external_effect_delivery",)),
)

# WF-09 names two distinct liquidation families.  Every child remains
# ambiguous until a normative source separates the zUSD and perps scenarios.
AMBIGUOUS_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, tuple[tuple[str, str], ...]], ...]] = (
    *(
        (
            requirement_id,
            (("ZUSD_MONETARY", "liquidation"), ("PERPS_MARKET", "liquidation")),
        )
        for requirement_id in ("WF-09", "BDD-034", "BDD-035", "BDD-036", "BDD-037", "BDD-038")
    ),
)

AMBIGUOUS_ROUTE_SPECS_V1: Final[RequirementTargetSpecsV1] = (
    ("WF-09", ("zusd_liquidation_settlement", "perps_epoch_settlement")),
)
