"""Pure core for O005 source-bound semantic-resolution evidence.

The registry names proposed resolution destinations for the exact unresolved
O005 source rows.  It is deliberately incapable of admitting a release,
mounting a route, or authorizing any value movement.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final, NoReturn, cast

try:
    from tools.m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )
except ModuleNotFoundError:
    from m6_normative_requirements_v1 import (  # type: ignore[no-redef]
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )


ARTIFACT_SCHEMA_V1: Final = "zenodex/m6-o005-semantic-resolutions/v1"
CHECK_SCHEMA_V1: Final = "zenodex/m6-o005-semantic-resolutions-check/v1"
GENERATOR_COMMAND_V1: Final = "python3 tools/build_m6_o005_semantic_resolutions_v1.py"
SOURCE_SCHEMA_V1: Final = "zenodex/m6-normative-requirements/v1"
SOURCE_ARTIFACT_PATH_V1: Final = "docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json"
SOURCE_ARTIFACT_SHA256_V1: Final = (
    "29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f"
)
SOURCE_REGISTRY_ROOT_V1: Final = "971e7c5e277697d0bc833a8016f2d47bbbd17c3b4e5c0762990d13772808a3e6"
MAX_ARTIFACT_BYTES_V1: Final = 524_288

_SOURCE_CEILING_FIELDS_V1: Final = (
    "manifest_complete",
    "production_promotion",
    "release_eligible",
    "requirements_closed",
    "semantic_capability_coverage_complete",
    "semantic_closure_complete",
    "semantic_target_inventory_complete",
    "structural_mapping_complete",
    "value_movement_claim_allowed",
)
_ARTIFACT_CEILING_FIELDS_V1: Final = _SOURCE_CEILING_FIELDS_V1
_MISSING_CONCEPT_IDS_V1: Final = (
    "pending_asset_bearing_intent_terminal_owner",
    "perps_request_terminal_owner",
    "generic_non_managed_issue",
    "generic_non_managed_burn",
    "perps_realized_pnl_settlement",
    "zusd_faucet_issuance_rejection",
    "sealed_auction_fee_allocation",
    "sealed_auction_residue_terminal_disposition",
    "sealed_auction_batch_terminal_state",
    "sealed_auction_fee_terminal_disposition",
    "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
    "external_effect_delivery",
)
_SOURCE_ROUTE_IDS_V1: Final = (
    "fee_funded_zdex_purchase_and_burn",
    "zusd_liquidation_settlement",
    "perps_epoch_settlement",
    "strategy_triggered_spot_swap",
)
_UNRESOLVED_POLICY_IDS_V1: Final = tuple(f"UP-{ordinal:02d}" for ordinal in range(1, 21))
_UNRESOLVED_POLICY_STATUS_V1: Final = "UNRESOLVED_POLICY_NOT_SELECTABLE"
_ARTIFACT_FIELDS_V1: Final = frozenset(
    {
        "closed_value_movement_gates",
        "generator_command",
        "manifest_complete",
        "nonclaims",
        "production_authority",
        "production_promotion",
        "projected_future_target_sets",
        "projected_future_structural_totals",
        "registry_root",
        "release_eligible",
        "requirements_closed",
        "resolution_rows",
        "route_resolution_rows",
        "schema",
        "semantic_capability_coverage_complete",
        "semantic_closure_complete",
        "semantic_target_inventory_complete",
        "settlement_authority",
        "source_pins",
        "resolution_to_future_target_relation",
        "source_resolution_bijection_scope",
        "source_resolution_bijection_verified",
        "status",
        "structural_mapping_complete",
        "value_movement_claim_allowed",
        "vm_ledger_contribution",
    }
)
_SOURCE_PINS_FIELDS_V1: Final = frozenset(
    {
        "base_structural_counts_root",
        "missing_target_concept_ids",
        "missing_target_concept_ids_root",
        "o005_requirements_artifact_path",
        "o005_requirements_artifact_sha256",
        "o005_requirements_registry_root",
        "required_route_ids",
        "required_route_ids_root",
        "source_schema",
        "unresolved_policy_ids",
        "unresolved_policy_ids_root",
        "unresolved_policy_status",
    }
)
_RESOLUTION_FIELDS_V1: Final = frozenset(
    {
        "blockers",
        "disposition",
        "lane_id",
        "policy_rules",
        "resolution_id",
        "resolution_kind",
        "source_missing_target_concept_id",
        "target_id",
    }
)
_ROUTE_FIELDS_V1: Final = frozenset(
    {
        "blockers",
        "disposition",
        "forbidden_substitutions",
        "missing_workflow_bdd",
        "requires_source_split",
        "resolution_id",
        "retained_supply_policy",
        "route_steps",
        "source_route_id",
    }
)
_PROJECTED_TOTAL_FIELDS_V1: Final = frozenset(
    {
        "capability_count",
        "current_o005_counts_unchanged",
        "evidence_denominator",
        "exclusion_count",
        "global_obligation_count",
        "invariant_count",
        "label",
        "route_count",
        "total",
    }
)
_PROJECTED_TARGET_SETS_FIELDS_V1: Final = frozenset(
    {
        "base_structural_counts",
        "future_capability_target_ids",
        "future_exclusion_target_ids",
        "future_global_obligation_ids",
        "non_counted_production_rejection_policy_resolution_ids",
    }
)
_VM_LEDGER_FIELDS_V1: Final = frozenset({"closed_gate_count", "gate_closures", "status"})
_RETAINED_SUPPLY_POLICY_FIELDS_V1: Final = frozenset(
    {
        "authoritative_fixed_percentage_floor",
        "formula",
        "p_and_q_domain",
        "q_positive",
        "selection",
        "strict_inequality",
    }
)
_BASE_COUNT_FIELDS_V1: Final = (
    "capability_count",
    "route_count",
    "exclusion_count",
    "invariant_count",
    "global_obligation_count",
)
_EXPECTED_BASE_COUNTS_V1: Final = {
    "capability_count": 103,
    "route_count": 4,
    "exclusion_count": 4,
    "invariant_count": 14,
    "global_obligation_count": 5,
}
_REQUIRED_RELEASE_STATUS_COUNT_V1: Final = 9
_FUTURE_CAPABILITY_TARGET_IDS_V1: Final = (
    "lane_capability:PERPS_MARKET:request_terminal_disposition",
    "lane_capability:ASSET_TRANSFER:profiled_non_managed_issue",
    "lane_capability:ASSET_TRANSFER:profiled_non_managed_burn",
    "lane_capability:PERPS_MARKET:realized_pnl_settlement",
    "lane_capability:SEALED_AUCTION:sealed_auction_fee_allocation",
    "lane_capability:SEALED_AUCTION:sealed_auction_residue_terminal_disposition",
    "lane_capability:SEALED_AUCTION:sealed_auction_batch_terminal_state",
    "lane_capability:SEALED_AUCTION:sealed_auction_fee_terminal_disposition",
    "lane_capability:SEALED_AUCTION:sealed_auction_reservation_terminal_disposition",
    "lane_capability:EXTERNAL_CUSTODY:external_effect_delivery",
)
_FUTURE_EXCLUSION_TARGET_IDS_V1: Final = ("exclusion:zusd_faucet_issuance",)
_FUTURE_GLOBAL_OBLIGATION_IDS_V1: Final = (
    "global_obligation:pending_asset_intent_terminal_coverage",
)
_NON_COUNTED_POLICY_RESOLUTION_IDS_V1: Final[tuple[str, ...]] = ()
_NONCLAIMS_V1: Final = (
    "This registry proves only a source-resolution bijection over the pinned O005 rows.",
    "It creates no module release, route admission, proof, mount, writer, settlement, or value-moving authority.",
    "Projected totals describe a future manifest amendment and leave current O005 counts unchanged.",
    "The registry does not define how Spot output sizing enforces R(S)=ceil(p*S/q) while burning exact received zDEX atoms; clipping and residue behavior remain unresolved and release-blocking.",
    "Fee percentages remain unresolved; buy-and-burn consumes only the governed BUYBACK allocation and preserves hosting compensation, staking, treasury, reserves, and carried residue as separate allocations.",
    "O-010B atomic-failure BDD, terminal BDD, boundary-value evidence, and stateful-history evidence remain missing and release-blocking.",
    "All 20 pinned policy decisions remain unresolved and nonselectable; this registry chooses none of them.",
    "EXTERNAL_CUSTODY is a stable protocol lane identifier and is not a legal characterization of key control.",
    "This artifact does not bind the generator, checker, or core source blobs and is not commit-scoped provenance evidence.",
    "This checker is not wired into release, settlement, or value-movement admission.",
)


@dataclass(frozen=True)
class SemanticResolutionRejectV1(ValueError):
    """Stable, typed rejection for untrusted semantic-resolution bytes."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise SemanticResolutionRejectV1(code, path, detail)


def _expect_exact_fields(value: dict[str, object], fields: frozenset[str], path: str) -> None:
    actual = frozenset(value)
    if actual != fields:
        _reject("JSON_FIELDS", path, "closed field set mismatch")


def _expect_object(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        _reject("JSON_TYPE", path, "must be an exact object")
    return cast(dict[str, object], value)


def _expect_list(value: object, path: str) -> list[object]:
    if type(value) is not list:
        _reject("JSON_TYPE", path, "must be an exact list")
    return cast(list[object], value)


def _expect_str(value: object, path: str) -> str:
    if type(value) is not str:
        _reject("JSON_TYPE", path, "must be an exact string")
    return value


def _expect_bool(value: object, path: str) -> bool:
    if type(value) is not bool:
        _reject("JSON_TYPE", path, "must be an exact boolean")
    return value


def _expect_int(value: object, path: str) -> int:
    if type(value) is not int:
        _reject("JSON_TYPE", path, "must be an exact integer")
    return value


def _expect_optional_str(value: object, path: str) -> str | None:
    if value is None:
        return None
    return _expect_str(value, path)


def _expect_string_tuple(value: object, path: str) -> tuple[str, ...]:
    return tuple(
        _expect_str(item, f"{path}[{index}]")
        for index, item in enumerate(_expect_list(value, path))
    )


def _require_unique(values: tuple[str, ...], path: str) -> None:
    if len(values) != len(set(values)):
        _reject("DUPLICATE_ID", path, "duplicate identifier")


def _sha256_hex(raw: bytes) -> str:
    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", "raw", "must have exact bytes type")
    return hashlib.sha256(raw).hexdigest()


def _require_bounded_bytes_v1(raw: bytes, label: str) -> bytes:
    """Reject hostile types and oversized inputs before any digest work."""

    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", label, "must have exact bytes type")
    if len(raw) > MAX_ARTIFACT_BYTES_V1:
        _reject("JSON_BYTE_LIMIT", label, "byte ceiling exceeded")
    return raw


def _canonical_json_bytes_checked_v1(value: object, path: str) -> bytes:
    """Translate upstream canonical-codec failures into this ABI's reject type."""

    try:
        return canonical_json_bytes_v1(value)
    except RequirementsRejectV1 as exc:
        _reject(exc.code, path, "upstream canonical JSON boundary rejected value")


def _canonical_object_from_bytes(raw: bytes, label: str) -> dict[str, object]:
    """Decode exact immutable bytes and reject alternate JSON encodings."""

    raw = _require_bounded_bytes_v1(raw, label)
    try:
        decoded = decode_json_object_v1(raw, label)
    except RequirementsRejectV1 as exc:
        _reject(exc.code, label, "upstream JSON boundary rejected input")
    if _canonical_json_bytes_checked_v1(decoded, label) != raw:
        _reject("JSON_NONCANONICAL", label, "must use exact canonical JSON bytes")
    return decoded


def _ids_root(values: tuple[str, ...]) -> str:
    return _sha256_hex(_canonical_json_bytes_checked_v1(list(values), "source.ids_root"))


def _base_counts_root(counts: dict[str, int]) -> str:
    return _sha256_hex(_canonical_json_bytes_checked_v1(counts, "source.base_counts_root"))


@dataclass(frozen=True)
class O005SourceSnapshotV1:
    """Owned facts extracted from the immutable O005 requirements artifact."""

    raw_sha256: str
    registry_root: str
    missing_target_concept_ids: tuple[str, ...]
    required_route_ids: tuple[str, ...]
    unresolved_policy_ids: tuple[str, ...]
    base_structural_counts: tuple[tuple[str, int], ...]


def parse_o005_source_snapshot_v1(raw: bytes) -> O005SourceSnapshotV1:
    """Parse the exact O005 source subject without granting it authority."""

    raw = _require_bounded_bytes_v1(raw, "o005_requirements_artifact")
    if _sha256_hex(raw) != SOURCE_ARTIFACT_SHA256_V1:
        _reject("SOURCE_ARTIFACT_SHA256", "source", "exact O005 source bytes drift")
    source = _canonical_object_from_bytes(raw, "o005_requirements_artifact")
    if _expect_str(source.get("schema"), "source.schema") != SOURCE_SCHEMA_V1:
        _reject("SOURCE_SCHEMA", "source.schema", "unexpected O005 source schema")
    for field in _SOURCE_CEILING_FIELDS_V1:
        if _expect_bool(source.get(field), f"source.{field}"):
            _reject("SOURCE_CLAIM_CEILING", f"source.{field}", "must remain false")
    if _expect_str(source.get("production_authority"), "source.production_authority") != "NONE":
        _reject("SOURCE_AUTHORITY", "source.production_authority", "must remain NONE")
    if _expect_str(source.get("settlement_authority"), "source.settlement_authority") != "NONE":
        _reject("SOURCE_AUTHORITY", "source.settlement_authority", "must remain NONE")
    registry_root = _expect_str(source.get("registry_root"), "source.registry_root")
    if registry_root != SOURCE_REGISTRY_ROOT_V1:
        _reject("SOURCE_REGISTRY_ROOT", "source.registry_root", "exact O005 registry root drift")
    unsigned_source = {key: value for key, value in source.items() if key != "registry_root"}
    if (
        _sha256_hex(_canonical_json_bytes_checked_v1(unsigned_source, "source.registry_root"))
        != registry_root
    ):
        _reject("SOURCE_REGISTRY_ROOT", "source.registry_root", "O005 registry root is invalid")

    missing_ids: list[str] = []
    route_ids: list[str] = []
    policy_ids: list[str] = []
    for index, row_value in enumerate(_expect_list(source.get("rows"), "source.rows")):
        row = _expect_object(row_value, f"source.rows[{index}]")
        if _expect_str(row.get("kind"), f"source.rows[{index}].kind") != "UNRESOLVED_POLICY":
            continue
        policy_ids.append(
            _expect_str(row.get("requirement_id"), f"source.rows[{index}].requirement_id")
        )
        if (
            _expect_str(row.get("status"), f"source.rows[{index}].status")
            != _UNRESOLVED_POLICY_STATUS_V1
        ):
            _reject(
                "SOURCE_POLICY_STATUS",
                f"source.rows[{index}].status",
                "unresolved policy became selectable",
            )
    for index, target_value in enumerate(_expect_list(source.get("targets"), "source.targets")):
        target = _expect_object(target_value, f"source.targets[{index}]")
        target_type = _expect_str(target.get("target_type"), f"source.targets[{index}].target_type")
        if target_type == "MISSING_TARGET_CONCEPT":
            missing_ids.append(
                _expect_str(
                    target.get("missing_target_concept_id"),
                    f"source.targets[{index}].missing_target_concept_id",
                )
            )
        if target_type == "REQUIRED_ROUTE":
            route_ids.append(
                _expect_str(target.get("route_id"), f"source.targets[{index}].route_id")
            )
    missing = tuple(missing_ids)
    routes = tuple(route_ids)
    policies = tuple(policy_ids)
    _require_unique(missing, "source.targets.missing_target_concept_id")
    _require_unique(routes, "source.targets.route_id")
    _require_unique(policies, "source.rows.unresolved_policy.requirement_id")
    if missing != _MISSING_CONCEPT_IDS_V1:
        _reject(
            "SOURCE_MISSING_TARGET_CONCEPT_ORDER",
            "source.targets",
            "unexpected missing-concept rows",
        )
    if routes != _SOURCE_ROUTE_IDS_V1:
        _reject("SOURCE_REQUIRED_ROUTE_ORDER", "source.targets", "unexpected required-route rows")
    if policies != _UNRESOLVED_POLICY_IDS_V1:
        _reject("SOURCE_POLICY_ORDER", "source.rows", "unexpected unresolved-policy rows")
    source_counts = _expect_object(source.get("structural_counts"), "source.structural_counts")
    base_counts = tuple(
        (field, _expect_int(source_counts.get(field), f"source.structural_counts.{field}"))
        for field in _BASE_COUNT_FIELDS_V1
    )
    if dict(base_counts) != _EXPECTED_BASE_COUNTS_V1:
        _reject(
            "SOURCE_STRUCTURAL_COUNTS", "source.structural_counts", "unexpected O005 target algebra"
        )
    return O005SourceSnapshotV1(
        raw_sha256=_sha256_hex(raw),
        registry_root=registry_root,
        missing_target_concept_ids=missing,
        required_route_ids=routes,
        unresolved_policy_ids=policies,
        base_structural_counts=base_counts,
    )


@dataclass(frozen=True)
class ResolutionSpecV1:
    resolution_id: str
    source_missing_target_concept_id: str
    resolution_kind: str
    target_id: str | None
    lane_id: str | None
    disposition: str
    blockers: tuple[str, ...]
    policy_rules: tuple[str, ...]

    def to_json(self) -> dict[str, object]:
        return {
            "blockers": list(self.blockers),
            "disposition": self.disposition,
            "lane_id": self.lane_id,
            "policy_rules": list(self.policy_rules),
            "resolution_id": self.resolution_id,
            "resolution_kind": self.resolution_kind,
            "source_missing_target_concept_id": self.source_missing_target_concept_id,
            "target_id": self.target_id,
        }


@dataclass(frozen=True)
class RouteResolutionSpecV1:
    resolution_id: str
    source_route_id: str
    disposition: str
    blockers: tuple[str, ...]
    route_steps: tuple[str, ...]
    forbidden_substitutions: tuple[str, ...]
    requires_source_split: bool
    missing_workflow_bdd: bool
    retained_supply_policy_fields: tuple[tuple[str, str | bool], ...] | None

    def to_json(self) -> dict[str, object]:
        return {
            "blockers": list(self.blockers),
            "disposition": self.disposition,
            "forbidden_substitutions": list(self.forbidden_substitutions),
            "missing_workflow_bdd": self.missing_workflow_bdd,
            "requires_source_split": self.requires_source_split,
            "resolution_id": self.resolution_id,
            "retained_supply_policy": (
                dict(self.retained_supply_policy_fields)
                if self.retained_supply_policy_fields is not None
                else None
            ),
            "route_steps": list(self.route_steps),
            "source_route_id": self.source_route_id,
        }


_RESOLUTION_SPECS_V1: Final = (
    ResolutionSpecV1(
        "pending_asset_intent_terminal_coverage",
        "pending_asset_bearing_intent_terminal_owner",
        "GLOBAL_OBLIGATION",
        "global_obligation:pending_asset_intent_terminal_coverage",
        None,
        "RESEARCH_ONLY_PROPOSED_GLOBAL_OBLIGATION",
        (),
        ("every_pending_asset_bearing_intent_requires_a_terminal_owner",),
    ),
    ResolutionSpecV1(
        "perps_request_terminal_disposition",
        "perps_request_terminal_owner",
        "REQUESTED_CAPABILITY",
        "lane_capability:PERPS_MARKET:request_terminal_disposition",
        "PERPS_MARKET",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-05",),
        ("every_perps_request_requires_a_terminal_disposition",),
    ),
    ResolutionSpecV1(
        "profiled_non_managed_issue",
        "generic_non_managed_issue",
        "REQUESTED_CAPABILITY",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_issue",
        "ASSET_TRANSFER",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("NAMED_VERSIONED_ASSET_PROFILE_REGISTRY_REQUIRED",),
        (
            "registered_ordinary_tokens_require_named_versioned_issue_profiles",
            "registered_ordinary_tokens_default_to_transfer_only",
            "unprofiled_arbitrary_generic_issue_rejects_without_mutation",
            "managed_issue_is_not_an_alias_for_generic_non_managed_issue",
        ),
    ),
    ResolutionSpecV1(
        "profiled_non_managed_burn",
        "generic_non_managed_burn",
        "REQUESTED_CAPABILITY",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_burn",
        "ASSET_TRANSFER",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("NAMED_VERSIONED_ASSET_PROFILE_REGISTRY_REQUIRED",),
        (
            "registered_ordinary_tokens_require_named_versioned_burn_profiles",
            "registered_ordinary_tokens_default_to_transfer_only",
            "unprofiled_arbitrary_generic_burn_rejects_without_mutation",
            "managed_burn_is_not_an_alias_for_generic_non_managed_burn",
        ),
    ),
    ResolutionSpecV1(
        "perps_realized_pnl_settlement",
        "perps_realized_pnl_settlement",
        "REQUESTED_CAPABILITY",
        "lane_capability:PERPS_MARKET:realized_pnl_settlement",
        "PERPS_MARKET",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-05", "UP-17"),
        ("realized_pnl_requires_exact_terminal_settlement",),
    ),
    ResolutionSpecV1(
        "zusd_faucet_issuance",
        "zusd_faucet_issuance_rejection",
        "EXCLUSION",
        "exclusion:zusd_faucet_issuance",
        "ZUSD_MONETARY",
        "REJECT_WITHOUT_MUTATION",
        ("UP-19",),
        ("zusd_faucet_issuance_rejects_without_mutation",),
    ),
    ResolutionSpecV1(
        "sealed_auction_fee_allocation",
        "sealed_auction_fee_allocation",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_allocation",
        "SEALED_AUCTION",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-07", "FEE_POLICY_UNRESOLVED"),
        ("no_fee_percentage_or_allocation_policy_is_declared_here",),
    ),
    ResolutionSpecV1(
        "sealed_auction_residue_terminal_disposition",
        "sealed_auction_residue_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_residue_terminal_disposition",
        "SEALED_AUCTION",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-07",),
        ("every_sealed_auction_residue_requires_a_terminal_disposition",),
    ),
    ResolutionSpecV1(
        "sealed_auction_batch_terminal_state",
        "sealed_auction_batch_terminal_state",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_batch_terminal_state",
        "SEALED_AUCTION",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-07",),
        ("settled_cancelled_and_expired_batches_require_explicit_terminal_states",),
    ),
    ResolutionSpecV1(
        "sealed_auction_fee_terminal_disposition",
        "sealed_auction_fee_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_terminal_disposition",
        "SEALED_AUCTION",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-07", "FEE_POLICY_UNRESOLVED"),
        ("every_cancelled_or_expired_auction_fee_requires_a_terminal_disposition",),
    ),
    ResolutionSpecV1(
        "sealed_auction_reservation_terminal_disposition",
        "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_reservation_terminal_disposition",
        "SEALED_AUCTION",
        "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED",
        ("UP-07",),
        ("commitment_bond_inventory_and_payment_reservations_require_terminal_dispositions",),
    ),
    ResolutionSpecV1(
        "external_effect_delivery",
        "external_effect_delivery",
        "REQUESTED_CAPABILITY",
        "lane_capability:EXTERNAL_CUSTODY:external_effect_delivery",
        "EXTERNAL_CUSTODY",
        "DISABLED_PENDING_COMPLETE_REGISTERED_PROFILE",
        ("COMPLETE_REGISTERED_EXTERNAL_PROFILE_REQUIRED",),
        ("external_effect_delivery_remains_disabled_pending_a_complete_registered_profile",),
    ),
)

_ROUTE_RESOLUTION_SPECS_V1: Final = (
    RouteResolutionSpecV1(
        "fee_funded_zdex_purchase_and_burn",
        "fee_funded_zdex_purchase_and_burn",
        "RESEARCH_ONLY_ROUTE_UNMOUNTED",
        (
            "UP-01",
            "UP-12",
            "UP-14",
            "SPOT_OUTPUT_SIZING_BINDING_UNRESOLVED",
            "MISSING_WORKFLOW_BDD",
            "MISSING_ATOMIC_FAILURE_BDD",
            "MISSING_TERMINAL_BDD",
            "MISSING_BVA_EVIDENCE",
            "MISSING_STATEFUL_HISTORY_EVIDENCE",
        ),
        (
            "consume_only_governed_buyback_quote_asset_fee_allocation",
            "preserve_separate_hosting_staking_treasury_reserve_and_residue_allocations",
            "authenticated_release_selected_spot_purchase",
            "exact_received_zdex_atoms",
            "atomic_burn_of_exact_received_zdex_atoms",
        ),
        ("treasury_burn_substitution", "transfer_burn_substitution"),
        False,
        True,
        (
            ("authoritative_fixed_percentage_floor", False),
            ("formula", "R(S)=ceil(p*S/q)"),
            ("p_and_q_domain", "EXACT_INTEGERS"),
            ("q_positive", True),
            ("selection", "GOVERNED_POLICY"),
            ("strict_inequality", "0 < p < q"),
        ),
    ),
    RouteResolutionSpecV1(
        "zusd_liquidation",
        "zusd_liquidation_settlement",
        "RESEARCH_ONLY_ROUTE_UNMOUNTED_SOURCE_SPLIT_REQUIRED",
        ("UP-04", "UP-17"),
        ("source_split_required_before_route_definition",),
        (),
        True,
        False,
        None,
    ),
    RouteResolutionSpecV1(
        "perps_epoch_settlement",
        "perps_epoch_settlement",
        "RESEARCH_ONLY_ROUTE_UNMOUNTED",
        ("UP-05", "UP-17"),
        ("perps_epoch_settlement_requires_exact_terminal_effects",),
        (),
        False,
        False,
        None,
    ),
    RouteResolutionSpecV1(
        "strategy_triggered_spot_swap",
        "strategy_triggered_spot_swap",
        "RESEARCH_ONLY_ROUTE_UNMOUNTED_SOURCE_SPLIT_REQUIRED",
        ("UP-08", "UP-12", "MISSING_WORKFLOW_BDD"),
        ("strategy_triggered_spot_swap_requires_source_split_and_workflow_bdd",),
        (),
        True,
        True,
        None,
    ),
)


def _resolution_rows_v1() -> list[dict[str, object]]:
    return [spec.to_json() for spec in _RESOLUTION_SPECS_V1]


def _route_rows_v1() -> list[dict[str, object]]:
    return [spec.to_json() for spec in _ROUTE_RESOLUTION_SPECS_V1]


def _classification_target_sets_v1() -> tuple[
    tuple[str, ...], tuple[str, ...], tuple[str, ...], tuple[str, ...]
]:
    capability_ids = tuple(
        cast(str, spec.target_id)
        for spec in _RESOLUTION_SPECS_V1
        if spec.resolution_kind == "REQUESTED_CAPABILITY"
    )
    exclusion_ids = tuple(
        cast(str, spec.target_id)
        for spec in _RESOLUTION_SPECS_V1
        if spec.resolution_kind == "EXCLUSION"
    )
    global_ids = tuple(
        cast(str, spec.target_id)
        for spec in _RESOLUTION_SPECS_V1
        if spec.resolution_kind == "GLOBAL_OBLIGATION"
    )
    policy_ids = tuple(
        spec.resolution_id
        for spec in _RESOLUTION_SPECS_V1
        if spec.resolution_kind == "PRODUCTION_REJECTION_POLICY"
    )
    if (
        capability_ids != _FUTURE_CAPABILITY_TARGET_IDS_V1
        or exclusion_ids != _FUTURE_EXCLUSION_TARGET_IDS_V1
        or global_ids != _FUTURE_GLOBAL_OBLIGATION_IDS_V1
        or policy_ids != _NON_COUNTED_POLICY_RESOLUTION_IDS_V1
    ):
        _reject("STATIC_CLASSIFICATION_TARGETS", "resolution_specs", "fixed target sets drift")
    return capability_ids, exclusion_ids, global_ids, policy_ids


def _projected_target_sets_v1(snapshot: O005SourceSnapshotV1) -> dict[str, object]:
    capability_ids, exclusion_ids, global_ids, policy_ids = _classification_target_sets_v1()
    return {
        "base_structural_counts": dict(snapshot.base_structural_counts),
        "future_capability_target_ids": list(capability_ids),
        "future_exclusion_target_ids": list(exclusion_ids),
        "future_global_obligation_ids": list(global_ids),
        "non_counted_production_rejection_policy_resolution_ids": list(policy_ids),
    }


def _projected_totals_v1(target_sets: dict[str, object]) -> dict[str, object]:
    base = _expect_object(
        target_sets.get("base_structural_counts"), "projected.base_structural_counts"
    )
    capability_ids = _expect_string_tuple(
        target_sets.get("future_capability_target_ids"), "projected.future_capability_target_ids"
    )
    exclusion_ids = _expect_string_tuple(
        target_sets.get("future_exclusion_target_ids"), "projected.future_exclusion_target_ids"
    )
    global_ids = _expect_string_tuple(
        target_sets.get("future_global_obligation_ids"), "projected.future_global_obligation_ids"
    )
    capability_count = _expect_int(
        base.get("capability_count"), "projected.base.capability_count"
    ) + len(capability_ids)
    route_count = _expect_int(base.get("route_count"), "projected.base.route_count")
    exclusion_count = _expect_int(
        base.get("exclusion_count"), "projected.base.exclusion_count"
    ) + len(exclusion_ids)
    invariant_count = _expect_int(base.get("invariant_count"), "projected.base.invariant_count")
    global_obligation_count = _expect_int(
        base.get("global_obligation_count"), "projected.base.global_obligation_count"
    ) + len(global_ids)
    total = (
        capability_count + route_count + exclusion_count + invariant_count + global_obligation_count
    )
    evidence_denominator = (
        capability_count + route_count
    ) * _REQUIRED_RELEASE_STATUS_COUNT_V1 + exclusion_count
    return {
        "capability_count": capability_count,
        "current_o005_counts_unchanged": True,
        "evidence_denominator": evidence_denominator,
        "exclusion_count": exclusion_count,
        "global_obligation_count": global_obligation_count,
        "invariant_count": invariant_count,
        "label": "PROJECTED_AFTER_FUTURE_CAPABILITY_MANIFEST_AMENDMENT_NON_PROMOTIONAL",
        "route_count": route_count,
        "total": total,
    }


def _unsigned_artifact_v1(snapshot: O005SourceSnapshotV1) -> dict[str, object]:
    """Render a deterministic research registry from a validated source snapshot."""

    target_sets = _projected_target_sets_v1(snapshot)
    return {
        "closed_value_movement_gates": 0,
        "generator_command": GENERATOR_COMMAND_V1,
        "manifest_complete": False,
        "nonclaims": list(_NONCLAIMS_V1),
        "production_authority": "NONE",
        "production_promotion": False,
        "projected_future_target_sets": target_sets,
        "projected_future_structural_totals": _projected_totals_v1(target_sets),
        "release_eligible": False,
        "requirements_closed": False,
        "resolution_rows": _resolution_rows_v1(),
        "route_resolution_rows": _route_rows_v1(),
        "schema": ARTIFACT_SCHEMA_V1,
        "semantic_capability_coverage_complete": False,
        "semantic_closure_complete": False,
        "semantic_target_inventory_complete": False,
        "settlement_authority": "NONE",
        "source_pins": {
            "base_structural_counts_root": _base_counts_root(dict(snapshot.base_structural_counts)),
            "missing_target_concept_ids": list(snapshot.missing_target_concept_ids),
            "missing_target_concept_ids_root": _ids_root(snapshot.missing_target_concept_ids),
            "o005_requirements_artifact_path": SOURCE_ARTIFACT_PATH_V1,
            "o005_requirements_artifact_sha256": snapshot.raw_sha256,
            "o005_requirements_registry_root": snapshot.registry_root,
            "required_route_ids": list(snapshot.required_route_ids),
            "required_route_ids_root": _ids_root(snapshot.required_route_ids),
            "source_schema": SOURCE_SCHEMA_V1,
            "unresolved_policy_ids": list(snapshot.unresolved_policy_ids),
            "unresolved_policy_ids_root": _ids_root(snapshot.unresolved_policy_ids),
            "unresolved_policy_status": _UNRESOLVED_POLICY_STATUS_V1,
        },
        "source_resolution_bijection_scope": "EXACT_12_MISSING_CONCEPTS_AND_4_REQUIRED_ROUTES",
        "source_resolution_bijection_verified": True,
        "resolution_to_future_target_relation": "ONE_TO_ONE_FUTURE_TARGETS",
        "status": "RESEARCH_ONLY_SOURCE_RESOLUTION_BIJECTION",
        "structural_mapping_complete": False,
        "value_movement_claim_allowed": False,
        "vm_ledger_contribution": {
            "closed_gate_count": 0,
            "gate_closures": [],
            "status": "NO_VM_GATE_PROMOTION",
        },
    }


def _build_semantic_resolution_artifact_from_snapshot_v1(
    snapshot: O005SourceSnapshotV1,
) -> bytes:
    """Render fixed rows after the source bytes have been parsed internally."""

    unsigned = _unsigned_artifact_v1(snapshot)
    unsigned_bytes = _canonical_json_bytes_checked_v1(unsigned, "artifact.unsigned")
    artifact = {**unsigned, "registry_root": _sha256_hex(unsigned_bytes)}
    return _canonical_json_bytes_checked_v1(artifact, "artifact")


def build_semantic_resolution_artifact_v1(source_raw: bytes) -> bytes:
    """Construct generated bytes only after parsing the exact source bytes."""

    snapshot = parse_o005_source_snapshot_v1(source_raw)
    return _build_semantic_resolution_artifact_from_snapshot_v1(snapshot)


def _validate_resolution_rows_v1(value: object) -> None:
    rows = _expect_list(value, "artifact.resolution_rows")
    if len(rows) != len(_MISSING_CONCEPT_IDS_V1):
        _reject("RESOLUTION_ROW_COUNT", "artifact.resolution_rows", "unexpected row count")
    source_ids: list[str] = []
    resolution_ids: list[str] = []
    for index, row_value in enumerate(rows):
        row = _expect_object(row_value, f"artifact.resolution_rows[{index}]")
        _expect_exact_fields(row, _RESOLUTION_FIELDS_V1, f"artifact.resolution_rows[{index}]")
        source_ids.append(
            _expect_str(
                row.get("source_missing_target_concept_id"),
                f"artifact.resolution_rows[{index}].source_missing_target_concept_id",
            )
        )
        resolution_ids.append(
            _expect_str(
                row.get("resolution_id"), f"artifact.resolution_rows[{index}].resolution_id"
            )
        )
        _expect_str(
            row.get("resolution_kind"), f"artifact.resolution_rows[{index}].resolution_kind"
        )
        _expect_optional_str(row.get("target_id"), f"artifact.resolution_rows[{index}].target_id")
        _expect_optional_str(row.get("lane_id"), f"artifact.resolution_rows[{index}].lane_id")
        _expect_str(row.get("disposition"), f"artifact.resolution_rows[{index}].disposition")
        _expect_string_tuple(row.get("blockers"), f"artifact.resolution_rows[{index}].blockers")
        _expect_string_tuple(
            row.get("policy_rules"), f"artifact.resolution_rows[{index}].policy_rules"
        )
    if tuple(source_ids) != _MISSING_CONCEPT_IDS_V1:
        _reject("RESOLUTION_SOURCE_ORDER", "artifact.resolution_rows", "source-concept order drift")
    _require_unique(tuple(resolution_ids), "artifact.resolution_rows.resolution_id")
    if rows != _resolution_rows_v1():
        _reject(
            "RESOLUTION_SEMANTICS", "artifact.resolution_rows", "fixed resolution semantics drift"
        )


def _validate_retained_supply_policy_v1(policy: object, index: int) -> None:
    if policy is None:
        return
    path = f"artifact.route_resolution_rows[{index}].retained_supply_policy"
    policy_object = _expect_object(policy, path)
    _expect_exact_fields(policy_object, _RETAINED_SUPPLY_POLICY_FIELDS_V1, path)
    if _expect_str(policy_object.get("formula"), f"{path}.formula") != "R(S)=ceil(p*S/q)":
        _reject("RETAINED_SUPPLY_POLICY", path, "formula drift")
    if (
        _expect_str(policy_object.get("p_and_q_domain"), f"{path}.p_and_q_domain")
        != "EXACT_INTEGERS"
    ):
        _reject("RETAINED_SUPPLY_POLICY", path, "integer domain drift")
    if (
        _expect_str(policy_object.get("strict_inequality"), f"{path}.strict_inequality")
        != "0 < p < q"
    ):
        _reject("RETAINED_SUPPLY_POLICY", path, "inequality drift")
    if not _expect_bool(policy_object.get("q_positive"), f"{path}.q_positive"):
        _reject("RETAINED_SUPPLY_POLICY", path, "q must be positive")
    if _expect_str(policy_object.get("selection"), f"{path}.selection") != "GOVERNED_POLICY":
        _reject("RETAINED_SUPPLY_POLICY", path, "selection drift")
    if _expect_bool(
        policy_object.get("authoritative_fixed_percentage_floor"),
        f"{path}.authoritative_fixed_percentage_floor",
    ):
        _reject("RETAINED_SUPPLY_POLICY", path, "fixed floor must remain false")


def _validate_route_rows_v1(value: object) -> None:
    rows = _expect_list(value, "artifact.route_resolution_rows")
    if len(rows) != len(_SOURCE_ROUTE_IDS_V1):
        _reject("ROUTE_ROW_COUNT", "artifact.route_resolution_rows", "unexpected row count")
    source_ids: list[str] = []
    resolution_ids: list[str] = []
    for index, row_value in enumerate(rows):
        row = _expect_object(row_value, f"artifact.route_resolution_rows[{index}]")
        _expect_exact_fields(row, _ROUTE_FIELDS_V1, f"artifact.route_resolution_rows[{index}]")
        source_ids.append(
            _expect_str(
                row.get("source_route_id"),
                f"artifact.route_resolution_rows[{index}].source_route_id",
            )
        )
        resolution_ids.append(
            _expect_str(
                row.get("resolution_id"), f"artifact.route_resolution_rows[{index}].resolution_id"
            )
        )
        _expect_str(row.get("disposition"), f"artifact.route_resolution_rows[{index}].disposition")
        _expect_string_tuple(
            row.get("blockers"), f"artifact.route_resolution_rows[{index}].blockers"
        )
        _expect_string_tuple(
            row.get("route_steps"), f"artifact.route_resolution_rows[{index}].route_steps"
        )
        _expect_string_tuple(
            row.get("forbidden_substitutions"),
            f"artifact.route_resolution_rows[{index}].forbidden_substitutions",
        )
        _expect_bool(
            row.get("requires_source_split"),
            f"artifact.route_resolution_rows[{index}].requires_source_split",
        )
        _expect_bool(
            row.get("missing_workflow_bdd"),
            f"artifact.route_resolution_rows[{index}].missing_workflow_bdd",
        )
        _validate_retained_supply_policy_v1(row.get("retained_supply_policy"), index)
    if tuple(source_ids) != _SOURCE_ROUTE_IDS_V1:
        _reject("ROUTE_SOURCE_ORDER", "artifact.route_resolution_rows", "source-route order drift")
    _require_unique(tuple(resolution_ids), "artifact.route_resolution_rows.resolution_id")
    if rows != _route_rows_v1():
        _reject("ROUTE_SEMANTICS", "artifact.route_resolution_rows", "fixed route semantics drift")


def _validate_source_pins_v1(value: object) -> None:
    pins = _expect_object(value, "artifact.source_pins")
    _expect_exact_fields(pins, _SOURCE_PINS_FIELDS_V1, "artifact.source_pins")
    if (
        _expect_str(pins.get("source_schema"), "artifact.source_pins.source_schema")
        != SOURCE_SCHEMA_V1
    ):
        _reject(
            "SOURCE_PIN_SCHEMA", "artifact.source_pins.source_schema", "unexpected source schema"
        )
    if (
        _expect_str(pins.get("o005_requirements_artifact_path"), "artifact.source_pins.path")
        != SOURCE_ARTIFACT_PATH_V1
    ):
        _reject("SOURCE_PIN_PATH", "artifact.source_pins.path", "unexpected source path")
    missing = _expect_string_tuple(
        pins.get("missing_target_concept_ids"), "artifact.source_pins.missing_target_concept_ids"
    )
    routes = _expect_string_tuple(
        pins.get("required_route_ids"), "artifact.source_pins.required_route_ids"
    )
    policies = _expect_string_tuple(
        pins.get("unresolved_policy_ids"), "artifact.source_pins.unresolved_policy_ids"
    )
    if missing != _MISSING_CONCEPT_IDS_V1 or routes != _SOURCE_ROUTE_IDS_V1:
        _reject("SOURCE_PIN_IDS", "artifact.source_pins", "unexpected pinned source identifiers")
    if policies != _UNRESOLVED_POLICY_IDS_V1:
        _reject("SOURCE_PIN_POLICIES", "artifact.source_pins", "unexpected policy identifiers")
    if (
        _expect_str(
            pins.get("unresolved_policy_status"),
            "artifact.source_pins.unresolved_policy_status",
        )
        != _UNRESOLVED_POLICY_STATUS_V1
    ):
        _reject("SOURCE_PIN_POLICIES", "artifact.source_pins", "policy status drift")
    if _expect_str(
        pins.get("missing_target_concept_ids_root"),
        "artifact.source_pins.missing_target_concept_ids_root",
    ) != _ids_root(missing):
        _reject(
            "SOURCE_PIN_IDS_ROOT",
            "artifact.source_pins.missing_target_concept_ids_root",
            "hash mismatch",
        )
    if _expect_str(
        pins.get("required_route_ids_root"), "artifact.source_pins.required_route_ids_root"
    ) != _ids_root(routes):
        _reject(
            "SOURCE_PIN_IDS_ROOT", "artifact.source_pins.required_route_ids_root", "hash mismatch"
        )
    if _expect_str(
        pins.get("unresolved_policy_ids_root"),
        "artifact.source_pins.unresolved_policy_ids_root",
    ) != _ids_root(policies):
        _reject(
            "SOURCE_PIN_IDS_ROOT",
            "artifact.source_pins.unresolved_policy_ids_root",
            "hash mismatch",
        )
    if _expect_str(
        pins.get("base_structural_counts_root"), "artifact.source_pins.base_structural_counts_root"
    ) != _base_counts_root(_EXPECTED_BASE_COUNTS_V1):
        _reject(
            "SOURCE_PIN_COUNTS_ROOT",
            "artifact.source_pins.base_structural_counts_root",
            "hash mismatch",
        )
    if (
        _expect_str(
            pins.get("o005_requirements_artifact_sha256"),
            "artifact.source_pins.o005_requirements_artifact_sha256",
        )
        != SOURCE_ARTIFACT_SHA256_V1
    ):
        _reject("SOURCE_PIN_SHA256", "artifact.source_pins", "exact O005 source hash drift")
    if (
        _expect_str(
            pins.get("o005_requirements_registry_root"),
            "artifact.source_pins.o005_requirements_registry_root",
        )
        != SOURCE_REGISTRY_ROOT_V1
    ):
        _reject(
            "SOURCE_PIN_REGISTRY_ROOT", "artifact.source_pins", "exact O005 registry root drift"
        )


def _validate_projected_target_sets_v1(value: object) -> dict[str, object]:
    target_sets = _expect_object(value, "artifact.projected_future_target_sets")
    _expect_exact_fields(
        target_sets, _PROJECTED_TARGET_SETS_FIELDS_V1, "artifact.projected_future_target_sets"
    )
    base = _expect_object(
        target_sets.get("base_structural_counts"),
        "artifact.projected_future_target_sets.base_structural_counts",
    )
    if base != _EXPECTED_BASE_COUNTS_V1:
        _reject(
            "PROJECTED_BASE_COUNTS",
            "artifact.projected_future_target_sets.base_structural_counts",
            "O005 base count drift",
        )
    capability_ids = _expect_string_tuple(
        target_sets.get("future_capability_target_ids"),
        "artifact.projected_future_target_sets.future_capability_target_ids",
    )
    exclusion_ids = _expect_string_tuple(
        target_sets.get("future_exclusion_target_ids"),
        "artifact.projected_future_target_sets.future_exclusion_target_ids",
    )
    global_ids = _expect_string_tuple(
        target_sets.get("future_global_obligation_ids"),
        "artifact.projected_future_target_sets.future_global_obligation_ids",
    )
    policy_ids = _expect_string_tuple(
        target_sets.get("non_counted_production_rejection_policy_resolution_ids"),
        "artifact.projected_future_target_sets.non_counted_production_rejection_policy_resolution_ids",
    )
    if (
        capability_ids != _FUTURE_CAPABILITY_TARGET_IDS_V1
        or exclusion_ids != _FUTURE_EXCLUSION_TARGET_IDS_V1
        or global_ids != _FUTURE_GLOBAL_OBLIGATION_IDS_V1
        or policy_ids != _NON_COUNTED_POLICY_RESOLUTION_IDS_V1
    ):
        _reject(
            "PROJECTED_TARGET_SETS",
            "artifact.projected_future_target_sets",
            "fixed classification target sets drift",
        )
    return target_sets


def _validate_projected_totals_v1(value: object, target_sets: dict[str, object]) -> None:
    totals = _expect_object(value, "artifact.projected_future_structural_totals")
    _expect_exact_fields(
        totals, _PROJECTED_TOTAL_FIELDS_V1, "artifact.projected_future_structural_totals"
    )
    for field in (
        "capability_count",
        "evidence_denominator",
        "exclusion_count",
        "global_obligation_count",
        "invariant_count",
        "route_count",
        "total",
    ):
        _expect_int(totals.get(field), f"artifact.projected_future_structural_totals.{field}")
    _expect_bool(
        totals.get("current_o005_counts_unchanged"),
        "artifact.projected_future_structural_totals.current_o005_counts_unchanged",
    )
    _expect_str(totals.get("label"), "artifact.projected_future_structural_totals.label")
    if totals != _projected_totals_v1(target_sets):
        _reject(
            "PROJECTED_TOTALS",
            "artifact.projected_future_structural_totals",
            "fixed projected totals drift",
        )


def _validate_claim_ceiling_v1(artifact: dict[str, object]) -> None:
    for field in _ARTIFACT_CEILING_FIELDS_V1:
        if _expect_bool(artifact.get(field), f"artifact.{field}"):
            _reject("CLAIM_CEILING", f"artifact.{field}", "must remain false")
    if _expect_str(artifact.get("production_authority"), "artifact.production_authority") != "NONE":
        _reject("CLAIM_CEILING", "artifact.production_authority", "must remain NONE")
    if _expect_str(artifact.get("settlement_authority"), "artifact.settlement_authority") != "NONE":
        _reject("CLAIM_CEILING", "artifact.settlement_authority", "must remain NONE")
    if (
        _expect_int(
            artifact.get("closed_value_movement_gates"), "artifact.closed_value_movement_gates"
        )
        != 0
    ):
        _reject("VM_GATE_PROMOTION", "artifact.closed_value_movement_gates", "must remain zero")
    ledger = _expect_object(
        artifact.get("vm_ledger_contribution"), "artifact.vm_ledger_contribution"
    )
    _expect_exact_fields(ledger, _VM_LEDGER_FIELDS_V1, "artifact.vm_ledger_contribution")
    if (
        _expect_int(
            ledger.get("closed_gate_count"), "artifact.vm_ledger_contribution.closed_gate_count"
        )
        != 0
    ):
        _reject(
            "VM_GATE_PROMOTION",
            "artifact.vm_ledger_contribution.closed_gate_count",
            "must remain zero",
        )
    if _expect_string_tuple(
        ledger.get("gate_closures"), "artifact.vm_ledger_contribution.gate_closures"
    ):
        _reject(
            "VM_GATE_PROMOTION",
            "artifact.vm_ledger_contribution.gate_closures",
            "must remain empty",
        )
    if (
        _expect_str(ledger.get("status"), "artifact.vm_ledger_contribution.status")
        != "NO_VM_GATE_PROMOTION"
    ):
        _reject("VM_GATE_PROMOTION", "artifact.vm_ledger_contribution.status", "unexpected status")


def parse_semantic_resolution_artifact_v1(raw: bytes) -> dict[str, object]:
    """Validate the closed schema before comparing generated source-bound bytes."""

    artifact = _canonical_object_from_bytes(raw, "semantic_resolution_artifact")
    _expect_exact_fields(artifact, _ARTIFACT_FIELDS_V1, "artifact")
    if _expect_str(artifact.get("schema"), "artifact.schema") != ARTIFACT_SCHEMA_V1:
        _reject("ARTIFACT_SCHEMA", "artifact.schema", "unexpected schema")
    if (
        _expect_str(artifact.get("generator_command"), "artifact.generator_command")
        != GENERATOR_COMMAND_V1
    ):
        _reject("GENERATOR_COMMAND", "artifact.generator_command", "unexpected generator command")
    if (
        _expect_str(artifact.get("status"), "artifact.status")
        != "RESEARCH_ONLY_SOURCE_RESOLUTION_BIJECTION"
    ):
        _reject("ARTIFACT_STATUS", "artifact.status", "unexpected status")
    if not _expect_bool(
        artifact.get("source_resolution_bijection_verified"),
        "artifact.source_resolution_bijection_verified",
    ):
        _reject("BIJECTION_STATUS", "artifact.source_resolution_bijection_verified", "must be true")
    if (
        _expect_str(
            artifact.get("source_resolution_bijection_scope"),
            "artifact.source_resolution_bijection_scope",
        )
        != "EXACT_12_MISSING_CONCEPTS_AND_4_REQUIRED_ROUTES"
    ):
        _reject("BIJECTION_SCOPE", "artifact.source_resolution_bijection_scope", "unexpected scope")
    if (
        _expect_str(
            artifact.get("resolution_to_future_target_relation"),
            "artifact.resolution_to_future_target_relation",
        )
        != "ONE_TO_ONE_FUTURE_TARGETS"
    ):
        _reject(
            "TARGET_RELATION",
            "artifact.resolution_to_future_target_relation",
            "unexpected relation",
        )
    if _expect_string_tuple(artifact.get("nonclaims"), "artifact.nonclaims") != _NONCLAIMS_V1:
        _reject("NONCLAIM_SEMANTICS", "artifact.nonclaims", "fixed nonclaim semantics drift")
    _validate_claim_ceiling_v1(artifact)
    _validate_source_pins_v1(artifact.get("source_pins"))
    _validate_resolution_rows_v1(artifact.get("resolution_rows"))
    _validate_route_rows_v1(artifact.get("route_resolution_rows"))
    target_sets = _validate_projected_target_sets_v1(artifact.get("projected_future_target_sets"))
    _validate_projected_totals_v1(artifact.get("projected_future_structural_totals"), target_sets)
    root = _expect_str(artifact.get("registry_root"), "artifact.registry_root")
    unsigned = {key: value for key, value in artifact.items() if key != "registry_root"}
    if root != _sha256_hex(_canonical_json_bytes_checked_v1(unsigned, "artifact.registry_root")):
        _reject("REGISTRY_ROOT", "artifact.registry_root", "canonical root mismatch")
    return artifact


def check_semantic_resolution_artifact_v1(
    raw: bytes,
    source_raw: bytes,
) -> dict[str, object]:
    """Check one artifact after independently parsing the exact source bytes."""

    artifact_sha256 = ""
    expected_root = ""
    try:
        raw = _require_bounded_bytes_v1(raw, "semantic_resolution_artifact")
        artifact_sha256 = _sha256_hex(raw)
        expected = build_semantic_resolution_artifact_v1(source_raw)
        expected_root = _sha256_hex(expected)
        parse_semantic_resolution_artifact_v1(raw)
        if raw != expected:
            _reject(
                "GENERATED_ARTIFACT_DRIFT",
                "artifact",
                "does not equal source-bound generated bytes",
            )
    except SemanticResolutionRejectV1 as exc:
        return _check_report_v1(False, artifact_sha256, expected_root, exc)
    return _check_report_v1(True, artifact_sha256, expected_root, None)


def _check_report_v1(
    ok: bool,
    artifact_sha256: str,
    expected_artifact_sha256: str,
    finding: SemanticResolutionRejectV1 | None,
) -> dict[str, object]:
    findings: list[dict[str, str]] = []
    if finding is not None:
        findings.append({"code": finding.code, "detail": finding.detail, "path": finding.path})
    return {
        "artifact_sha256": artifact_sha256,
        "closed_value_movement_gates": 0,
        "expected_artifact_sha256": expected_artifact_sha256,
        "findings": findings,
        "manifest_complete": False,
        "ok": ok,
        "production_authority": "NONE",
        "production_promotion": False,
        "release_eligible": False,
        "requirements_closed": False,
        "schema": CHECK_SCHEMA_V1,
        "semantic_capability_coverage_complete": False,
        "semantic_closure_complete": False,
        "semantic_target_inventory_complete": False,
        "settlement_authority": "NONE",
        "source_resolution_bijection_verified": ok,
        "structural_mapping_complete": False,
        "value_movement_claim_allowed": False,
        "vm_ledger_closed_gate_count": 0,
    }
