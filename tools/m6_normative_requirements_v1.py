"""Pure core for source-pinned, research-only M6 normative requirements V1.

The build and checker modules own filesystem and Git access.  This module takes
only explicit immutable byte snapshots, returns fresh data, and never grants
economic, release, or publication authority.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from enum import Enum
from typing import Final, NoReturn, TypeVar

try:
    from tools.m6_normative_requirements_decisions_v1 import (
        AMBIGUOUS_CAPABILITY_SPECS_V1,
        AMBIGUOUS_ROUTE_SPECS_V1,
        GLOBAL_OBLIGATION_EDGE_SPECS_V1,
        GLOBAL_OBLIGATION_SPECS_V1,
        MISSING_TARGET_CONCEPT_SPECS_V1,
        MISSING_TARGET_EDGE_SPECS_V1,
    )
except ModuleNotFoundError:
    from m6_normative_requirements_decisions_v1 import (
        AMBIGUOUS_CAPABILITY_SPECS_V1,
        AMBIGUOUS_ROUTE_SPECS_V1,
        GLOBAL_OBLIGATION_EDGE_SPECS_V1,
        GLOBAL_OBLIGATION_SPECS_V1,
        MISSING_TARGET_CONCEPT_SPECS_V1,
        MISSING_TARGET_EDGE_SPECS_V1,
    )

ARTIFACT_SCHEMA_V1: Final = "zenodex/m6-normative-requirements/v1"
CHECK_SCHEMA_V1: Final = "zenodex/m6-normative-requirements-check/v1"
SOURCE_SUBJECT_COMMIT_V1: Final = "99667c04980e60b6298e433e33bf3a4efc77e983"
SOURCE_SUBJECT_TREE_V1: Final = "1284e05d9f5606f28cbd6a1159b54a8fba2477a5"
GENERATOR_COMMAND_V1: Final = "python3 tools/build_m6_normative_requirements_v1.py"
MAX_JSON_BYTES_V1: Final = 1_048_576
MAX_JSON_DEPTH_V1: Final = 64
MAX_JSON_NODES_V1: Final = 100_000
MAX_JSON_STRING_CHARS_V1: Final = 131_072
MAX_JSON_INTEGER_DIGITS_V1: Final = 256
MAX_JSON_INTEGER_MAGNITUDE_EXCLUSIVE_V1: Final = 10**MAX_JSON_INTEGER_DIGITS_V1
MIN_PYTHON_RECURSION_LIMIT_V1: Final = 256
MAX_FINDING_PATH_CHARS_V1: Final = 256
MAX_FINDING_DETAIL_CHARS_V1: Final = 512

ATDD_PATH_V1: Final = "docs/research/m6_global_economic_core_atdd_bdd_v1.json"
LUNA_PATH_V1: Final = "docs/research/m6_global_economic_core_luna_completeness_review_v1.json"
PLAN_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
MANIFEST_PATH_V1: Final = "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
PLAN_CANONICAL_SHA256_V1: Final = "83773cf81dceff2ed94f0214d585d55004a62418b2b4c478b001ffbb1628a34f"

# The source pin binds Plan bytes. This separately binds the admitted JSON value,
# so a later source repin cannot promote or otherwise alter Plan semantics.
_PLAN_FORBIDDEN_VALUE_CLAIM_V1: Final = (
    "FORBIDDEN_UNTIL_ALL_12_VM_GATES_PASS_ON_ONE_EXACT_RELEASE_SUBJECT"
)
_PLAN_O005_ID_V1: Final = "O-005"
_PLAN_O005_CLOSES_V1: Final = ("incomplete_requirements_registry",)
_PLAN_OPEN_GAP_STATUS_V1: Final = "OPEN"
_PLAN_ALLOWED_VM_STATUSES_V1: Final = frozenset({"GAP", "PARTIAL_REQUIRES_CURRENT_RECONCILIATION"})
_PLAN_AUTHORITY_FIELDS_V1: Final = frozenset(
    {"production_authority", "production_ready", "release_ready", "settlement_authority"}
)
_PLAN_ADMISSION_FIELDS_V1: Final = frozenset(
    {"authority_effect", "deterministic_evidence", "human_selection", "llm_review"}
)
_PLAN_REQUIREMENTS_FLOOR_FIELDS_V1: Final = frozenset(
    {
        "classification",
        "closure_rule",
        "completeness_review",
        "confirmed_finding_count",
        "confirmed_findings",
        "manifest_complete",
        "required_expansion_count",
        "required_expansion_ids",
        "scenario_count",
        "unresolved_policy_count",
        "workflow_count",
    }
)
_PLAN_BASELINE_FIELDS_V1: Final = frozenset(
    {
        "architecture_inventory",
        "candidate_disposition",
        "closed_value_movement_gates",
        "current_ledger_status",
        "estimate_warning",
        "explicit_exclusion_count",
        "immediate_blockers",
        "minimum_release_evidence_cell_count",
        "minimum_release_evidence_cell_formula",
        "observed_release_closure_basis_points",
        "promoted_release_evidence_cell_count",
        "required_release_statuses",
        "required_route_count",
        "scope_discovery_confidence",
        "strict_release_closure",
        "unclosed_release_evidence_cell_count",
        "value_movement_gate_count",
    }
)
_PLAN_VM_GATE_FIELDS_V1: Final = frozenset({"gate_id", "status", "title"})
_PLAN_RELEASE_GATE_FIELDS_V1: Final = frozenset(
    {"excluded_capability_status", "required_capability_statuses", "whole_value_movement_claim"}
)
_PLAN_O005_FIELDS_V1: Final = frozenset(
    {"closes", "depends_on", "obligation_id", "phase", "priority", "required_evidence", "title"}
)
_PLAN_GAP_FIELDS_V1: Final = frozenset({"gap_id", "owner_obligation", "status"})

_COMMIT_RE: Final = re.compile(r"^[0-9a-f]{40}$")
_SHA256_RE: Final = re.compile(r"^[0-9a-f]{64}$")

_ATDD_ROOT_FIELDS: Final = frozenset(
    {
        "actors",
        "authority_topology",
        "base_commit",
        "invariants",
        "m6_coverage",
        "managed_asset_policy",
        "nonclaims",
        "open_decisions",
        "production_promotion",
        "schema",
        "source_pins",
        "status",
        "workflows",
    }
)
_LUNA_ROOT_FIELDS: Final = frozenset(
    {
        "confirmed_findings",
        "current_revision",
        "discarded_review_artifacts",
        "nonclaims",
        "production_promotion",
        "required_spec_expansions",
        "review_subject",
        "schema",
        "scope_decisions",
        "source_pins",
        "status",
    }
)
_PLAN_ROOT_FIELDS: Final = frozenset(
    {
        "admission_model",
        "advisory_reviews",
        "authority",
        "baseline_verdict",
        "completeness_estimation_policy",
        "coordination_protocol",
        "current_tau_integration_contract",
        "gap_registry",
        "historical_inputs",
        "next_obligations",
        "nonclaims",
        "normative_inputs",
        "phases",
        "release_gate",
        "requirements_floor",
        "schema",
        "selected_architecture",
        "semantic_anchors",
        "status",
        "subject",
        "unresolved_semantic_decisions",
        "upstream_dependencies",
        "value_movement_gates",
        "vm_gate_promotion",
    }
)
_MANIFEST_ROOT_FIELDS: Final = frozenset(
    {
        "explicit_exclusions",
        "historical_requirements",
        "lanes",
        "manifest_complete",
        "nonclaims",
        "production_promotion",
        "release_eligible",
        "required_cross_lane_routes",
        "schema",
        "semantic_anchors",
        "semantic_contract",
        "status",
    }
)
_WORKFLOW_FIELDS: Final = frozenset(
    {
        "actor",
        "entrypoints",
        "id",
        "name",
        "owner",
        "required_scenario_classes",
        "scenarios",
    }
)
_BDD_FIELDS: Final = frozenset({"class", "given", "id", "requirements", "then", "when"})
_INVARIANT_FIELDS: Final = frozenset({"id", "law", "name"})
_RSE_FIELDS: Final = frozenset({"id", "minimum_acceptance", "required_scenario_classes", "title"})
_CE_FIELDS: Final = frozenset(
    {
        "affected_requirements",
        "classification",
        "evidence",
        "id",
        "required_disposition",
        "severity",
        "status",
        "title",
        "witness",
    }
)
_UP_FIELDS: Final = frozenset({"decision_id", "topic"})
_LANE_FIELDS: Final = frozenset({"capabilities", "disposition", "lane_id"})
_EXCLUSION_FIELDS: Final = frozenset({"capability", "disposition"})
_REQUIREMENTS_FLOOR_FIELDS: Final = frozenset(
    {
        "classification",
        "closure_rule",
        "completeness_review",
        "confirmed_finding_count",
        "confirmed_findings",
        "manifest_complete",
        "required_expansion_count",
        "required_expansion_ids",
        "scenario_count",
        "unresolved_policy_count",
        "workflow_count",
    }
)
_ARTIFACT_ROOT_FIELDS: Final = frozenset(
    {
        "generator_command",
        "m6_historical_links",
        "manifest_complete",
        "nonclaims",
        "production_authority",
        "production_promotion",
        "registry_root",
        "release_eligible",
        "requirements_closed",
        "rows",
        "schema",
        "semantic_anchors",
        "source_pins",
        "status",
        "settlement_authority",
        "source_row_census_complete",
        "semantic_target_inventory_complete",
        "structural_mapping_complete",
        "semantic_closure_complete",
        "semantic_capability_coverage_complete",
        "value_movement_claim_allowed",
        "structural_counts",
        "subject",
        "targets",
    }
)
_ROW_FIELDS: Final = frozenset(
    {
        "edges",
        "kind",
        "parent_requirement_id",
        "requirement_id",
        "source_document",
        "source_fields",
        "status",
    }
)
_EDGE_FIELDS: Final = frozenset({"relation_type", "target_id"})
_TARGET_FIELDS: Final = frozenset(
    {
        "capability_id",
        "exclusion_disposition",
        "exclusion_id",
        "inbound_edges",
        "invariant_id",
        "global_obligation_id",
        "lane_disposition",
        "lane_id",
        "missing_target_concept_id",
        "route_id",
        "source_fields",
        "status",
        "target_id",
        "target_type",
    }
)
_INBOUND_EDGE_FIELDS: Final = frozenset({"relation_type", "requirement_id"})
_SOURCE_PIN_FIELDS: Final = frozenset(
    {
        "admissible_use",
        "git_blob_sha",
        "git_mode",
        "git_object_type",
        "path",
        "sha256",
        "source_gate_status",
        "source_role",
    }
)
_SUBJECT_FIELDS: Final = frozenset(
    {
        "artifact_commit_binding",
        "artifact_commit_status",
        "source_subject_commit",
        "source_subject_tree",
    }
)
_COUNT_FIELDS: Final = frozenset(
    {
        "bdd_count",
        "capability_count",
        "ce_count",
        "ambiguous_capability_scope_count",
        "enabled_capability_bdd_direct_scope_count",
        "enabled_direct_capability_ce_and_rse_only_scope_count",
        "enabled_direct_capability_rse_only_scope_count",
        "enabled_direct_capability_semantic_scope_count",
        "enabled_direct_capability_wf_or_bdd_scope_count",
        "enabled_direct_capability_workflow_only_scope_count",
        "cross_cutting_capability_scope_count",
        "disabled_capability_direct_scope_count",
        "disabled_capability_target_count",
        "exclusion_count",
        "global_obligation_count",
        "invariant_count",
        "missing_target_concept_count",
        "requirement_count",
        "route_count",
        "rse_count",
        "target_count",
        "up_count",
        "workflow_count",
    }
)
_PROHIBITED_STATUSES: Final = frozenset(
    {"IMPLEMENTED", "MOUNTED", "PROVED", "RELEASE_BACKED", "SPECIFIED", "TESTED"}
)


class TargetTypeV1(str, Enum):
    LANE_CAPABILITY = "LANE_CAPABILITY"
    REQUIRED_ROUTE = "REQUIRED_ROUTE"
    EXCLUSION = "EXCLUSION"
    INVARIANT = "INVARIANT"
    GLOBAL_OBLIGATION = "GLOBAL_OBLIGATION"
    MISSING_TARGET_CONCEPT = "MISSING_TARGET_CONCEPT"


class RelationKindV1(str, Enum):
    AMBIGUOUS_SOURCE_SCOPE = "AMBIGUOUS_SOURCE_SCOPE"
    BDD_INVARIANT_REFERENCE = "BDD_INVARIANT_REFERENCE"
    CAPABILITY_POLICY_SCOPE = "CAPABILITY_POLICY_SCOPE"
    CAPABILITY_SEMANTIC_SCOPE = "CAPABILITY_SEMANTIC_SCOPE"
    CE_INVARIANT_REFERENCE = "CE_INVARIANT_REFERENCE"
    CROSS_CUTTING_CONSTRAINT = "CROSS_CUTTING_CONSTRAINT"
    EXCLUSION_SCOPE = "EXCLUSION_SCOPE"
    GLOBAL_OBLIGATION_SCOPE = "GLOBAL_OBLIGATION_SCOPE"
    MISSING_TARGET_CONCEPT_SCOPE = "MISSING_TARGET_CONCEPT_SCOPE"
    REQUIRED_ROUTE_SCOPE = "REQUIRED_ROUTE_SCOPE"
    RSE_INVARIANT_SCOPE = "RSE_INVARIANT_SCOPE"


_RELATION_TARGET_TYPES: Final = {
    RelationKindV1.AMBIGUOUS_SOURCE_SCOPE: (
        TargetTypeV1.LANE_CAPABILITY,
        TargetTypeV1.REQUIRED_ROUTE,
    ),
    RelationKindV1.BDD_INVARIANT_REFERENCE: (TargetTypeV1.INVARIANT,),
    RelationKindV1.CAPABILITY_POLICY_SCOPE: (TargetTypeV1.LANE_CAPABILITY,),
    RelationKindV1.CAPABILITY_SEMANTIC_SCOPE: (TargetTypeV1.LANE_CAPABILITY,),
    RelationKindV1.CE_INVARIANT_REFERENCE: (TargetTypeV1.INVARIANT,),
    RelationKindV1.CROSS_CUTTING_CONSTRAINT: (TargetTypeV1.INVARIANT,),
    RelationKindV1.EXCLUSION_SCOPE: (TargetTypeV1.EXCLUSION,),
    RelationKindV1.GLOBAL_OBLIGATION_SCOPE: (TargetTypeV1.GLOBAL_OBLIGATION,),
    RelationKindV1.MISSING_TARGET_CONCEPT_SCOPE: (TargetTypeV1.MISSING_TARGET_CONCEPT,),
    RelationKindV1.REQUIRED_ROUTE_SCOPE: (TargetTypeV1.REQUIRED_ROUTE,),
    RelationKindV1.RSE_INVARIANT_SCOPE: (TargetTypeV1.INVARIANT,),
}


@dataclass(frozen=True)
class RequirementsRejectV1(ValueError):
    """A stable fail-closed rejection emitted by the deterministic core."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


@dataclass(frozen=True)
class SourcePinV1:
    path: str
    sha256: str
    git_blob_sha: str
    git_mode: str
    git_object_type: str
    source_role: str
    source_gate_status: str
    admissible_use: str

    def to_json(self) -> dict[str, str]:
        return {
            "admissible_use": self.admissible_use,
            "git_blob_sha": self.git_blob_sha,
            "git_mode": self.git_mode,
            "git_object_type": self.git_object_type,
            "path": self.path,
            "sha256": self.sha256,
            "source_gate_status": self.source_gate_status,
            "source_role": self.source_role,
        }


SOURCE_PINS_V1: Final[tuple[SourcePinV1, ...]] = (
    SourcePinV1(
        MANIFEST_PATH_V1,
        "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95",
        "989965363d73b514362f36ce0088f7ba27c8825a",
        "100644",
        "blob",
        "CURRENT_CHECKER_VALID_PROVISIONAL_CLOSED_NAME_MANIFEST",
        "CURRENT_CHECKER_PASS_RESEARCH_ONLY",
        "CLOSED_LANE_CAPABILITY_NAMESPACE_ROUTES_AND_EXCLUSIONS_ONLY",
    ),
    SourcePinV1(
        PLAN_PATH_V1,
        "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f",
        "6da997fe32f39a4c1bf0c89a3f6dfc87a16f863f",
        "100644",
        "blob",
        "CURRENT_CHECKER_VALID_RESEARCH_PLAN_PENDING_ADMISSION",
        "CURRENT_CHECKER_PASS_RESEARCH_ONLY",
        "CLOSURE_RULE_COUNTS_IDS_ANCHORS_AND_NONPROMOTION_ONLY",
    ),
    SourcePinV1(
        ATDD_PATH_V1,
        "c7a6b52b6167e0b899aacc233c6db7c6a9fe3235d6aa6918609267a9d030fcfc",
        "aae8a07796643170ba06cc3914ea3179900deba0",
        "100644",
        "blob",
        "RESEARCH_ONLY_DRAFT_DONOR",
        "STALE_INTERNAL_PROVENANCE_RESEARCH_ONLY_DRAFT",
        "EXACT_WORKFLOW_BDD_INVARIANT_AND_M6_LINK_DONOR_ONLY",
    ),
    SourcePinV1(
        LUNA_PATH_V1,
        "b3a1929422b6399a3c30fb1ead4c7732a8802d08b1d4b59e6fc3ea79463b4698",
        "b140b4d204e1ccad07cab3a1b28188ec15e7bfc7",
        "100644",
        "blob",
        "STALE_ADVISORY_REVIEW_DONOR",
        "STALE_INTERNAL_PROVENANCE_ADVISORY_ONLY",
        "EXACT_RSE_CE_CONTENT_DONOR_WITH_PLAN_V2_ADOPTION_ONLY",
    ),
)


@dataclass(frozen=True)
class SourceSnapshotV1:
    captured_git_head: str
    rechecked_git_head: str
    source_subject_tree: str
    source_subject_is_ancestor: bool
    document_bytes: tuple[tuple[str, bytes], ...]
    source_subject_entries: tuple[tuple[str, str, str, str], ...]
    current_head_entries: tuple[tuple[str, str, str, str], ...]


@dataclass(frozen=True)
class EdgeV1:
    relation_type: RelationKindV1
    target_id: str

    def to_json(self) -> dict[str, str]:
        return {"relation_type": self.relation_type.value, "target_id": self.target_id}


@dataclass(frozen=True)
class AtomV1:
    requirement_id: str
    kind: str
    status: str
    parent_requirement_id: str | None
    source_document: str
    source_fields_bytes: bytes
    edges: tuple[EdgeV1, ...]

    def to_json(self) -> dict[str, object]:
        return {
            "edges": [edge.to_json() for edge in self.edges],
            "kind": self.kind,
            "parent_requirement_id": self.parent_requirement_id,
            "requirement_id": self.requirement_id,
            "source_document": self.source_document,
            "source_fields": _decoded_canonical_object_v1(self.source_fields_bytes),
            "status": self.status,
        }


@dataclass(frozen=True)
class TargetSpecV1:
    target_id: str
    target_type: TargetTypeV1
    lane_id: str | None
    capability_id: str | None
    route_id: str | None
    exclusion_id: str | None
    exclusion_disposition: str | None
    invariant_id: str | None
    lane_disposition: str | None
    source_fields_bytes: bytes | None
    global_obligation_id: str | None = None
    missing_target_concept_id: str | None = None

    def __post_init__(self) -> None:
        if type(self.target_type) is not TargetTypeV1 or type(self.target_id) is not str:
            _reject(
                "TARGET_SPEC_DISCRIMINANT",
                "TargetSpecV1",
                "target type and target ID must use exact declared types",
            )
        identity_fields = (
            "lane_id",
            "capability_id",
            "route_id",
            "exclusion_id",
            "exclusion_disposition",
            "invariant_id",
            "lane_disposition",
            "global_obligation_id",
            "missing_target_concept_id",
        )
        for field_name in identity_fields:
            value = getattr(self, field_name)
            if value is not None and (type(value) is not str or not value):
                _reject(
                    "TARGET_SPEC_DISCRIMINANT",
                    self.target_id,
                    f"{field_name} must be a nonempty exact string or absent",
                )
        if self.source_fields_bytes is not None and type(self.source_fields_bytes) is not bytes:
            _reject(
                "TARGET_SPEC_DISCRIMINANT",
                self.target_id,
                "source fields must be exact bytes or absent",
            )
        required_fields = {
            TargetTypeV1.LANE_CAPABILITY: frozenset(
                {"lane_id", "capability_id", "lane_disposition"}
            ),
            TargetTypeV1.REQUIRED_ROUTE: frozenset({"route_id"}),
            TargetTypeV1.EXCLUSION: frozenset({"exclusion_id", "exclusion_disposition"}),
            TargetTypeV1.INVARIANT: frozenset({"invariant_id"}),
            TargetTypeV1.GLOBAL_OBLIGATION: frozenset({"global_obligation_id"}),
            TargetTypeV1.MISSING_TARGET_CONCEPT: frozenset({"missing_target_concept_id"}),
        }
        present_fields = frozenset(
            field_name for field_name in identity_fields if getattr(self, field_name) is not None
        )
        if present_fields != required_fields[self.target_type]:
            _reject(
                "TARGET_SPEC_DISCRIMINANT",
                self.target_id,
                "identity fields do not match target discriminant",
            )

        def component(field_name: str) -> str:
            value = getattr(self, field_name)
            if type(value) is not str or not value:
                _reject(
                    "TARGET_SPEC_DISCRIMINANT",
                    self.target_id,
                    f"missing identity component {field_name}",
                )
            return value

        if self.target_type == TargetTypeV1.LANE_CAPABILITY:
            expected_target_id = (
                f"lane_capability:{component('lane_id')}:{component('capability_id')}"
            )
        elif self.target_type == TargetTypeV1.REQUIRED_ROUTE:
            expected_target_id = f"required_route:{component('route_id')}"
        elif self.target_type == TargetTypeV1.EXCLUSION:
            expected_target_id = f"exclusion:{component('exclusion_id')}"
        elif self.target_type == TargetTypeV1.INVARIANT:
            expected_target_id = f"invariant:{component('invariant_id')}"
        elif self.target_type == TargetTypeV1.GLOBAL_OBLIGATION:
            expected_target_id = f"global_obligation:{component('global_obligation_id')}"
        else:
            expected_target_id = f"missing_target_concept:{component('missing_target_concept_id')}"
        if self.target_id != expected_target_id:
            _reject(
                "TARGET_SPEC_DISCRIMINANT",
                self.target_id,
                "target ID does not match discriminant identity fields",
            )
        source_fields_required = self.target_type in {
            TargetTypeV1.EXCLUSION,
            TargetTypeV1.INVARIANT,
            TargetTypeV1.GLOBAL_OBLIGATION,
            TargetTypeV1.MISSING_TARGET_CONCEPT,
        }
        if source_fields_required != (type(self.source_fields_bytes) is bytes):
            _reject(
                "TARGET_SPEC_DISCRIMINANT",
                self.target_id,
                "source-field presence does not match target discriminant",
            )


@dataclass(frozen=True)
class RegistryV1:
    atoms: tuple[AtomV1, ...]
    targets: tuple[TargetSpecV1, ...]
    semantic_anchors_bytes: bytes
    m6_historical_links: tuple[tuple[str, tuple[str, ...]], ...]

    def to_unsigned_json(self) -> dict[str, object]:
        targets = _render_targets_v1(self.atoms, self.targets)
        return {
            "generator_command": GENERATOR_COMMAND_V1,
            "m6_historical_links": [
                {
                    "historical_requirement_id": historical_id,
                    "provenance_status": "STALE_DRAFT_PROVENANCE_ONLY",
                    "workflow_ids": list(workflow_ids),
                }
                for historical_id, workflow_ids in self.m6_historical_links
            ],
            "manifest_complete": False,
            "nonclaims": list(NONCLAIMS_V1),
            "production_authority": "NONE",
            "production_promotion": False,
            "release_eligible": False,
            "requirements_closed": False,
            "rows": [atom.to_json() for atom in self.atoms],
            "schema": ARTIFACT_SCHEMA_V1,
            "semantic_anchors": _decoded_canonical_object_v1(self.semantic_anchors_bytes),
            "source_pins": [pin.to_json() for pin in SOURCE_PINS_V1],
            "status": "RESEARCH_ONLY_STRUCTURAL_MAPPING_REQUIREMENTS_UNRESOLVED",
            "settlement_authority": "NONE",
            "source_row_census_complete": True,
            "semantic_target_inventory_complete": False,
            "structural_mapping_complete": False,
            "semantic_closure_complete": False,
            "semantic_capability_coverage_complete": False,
            "value_movement_claim_allowed": False,
            "structural_counts": _structural_counts_v1(self.atoms, self.targets),
            "subject": {
                "artifact_commit_binding": "NONE",
                "artifact_commit_status": "GENERATED_CONTENT_NOT_SELF_REFERENTIAL",
                "source_subject_commit": SOURCE_SUBJECT_COMMIT_V1,
                "source_subject_tree": SOURCE_SUBJECT_TREE_V1,
            },
            "targets": targets,
        }

    def to_json(self) -> dict[str, object]:
        unsigned = self.to_unsigned_json()
        return {
            **unsigned,
            "registry_root": hashlib.sha256(canonical_json_bytes_v1(unsigned)).hexdigest(),
        }


@dataclass(frozen=True)
class CheckFindingV1:
    code: str
    path: str
    detail: str

    def to_json(self) -> dict[str, str]:
        return {"code": self.code, "detail": self.detail, "path": self.path}


@dataclass(frozen=True)
class CheckReportV1:
    findings: tuple[CheckFindingV1, ...]
    artifact_sha256: str
    expected_registry_root: str | None
    source_row_census_complete: bool

    def to_json(self) -> dict[str, object]:
        return {
            "artifact_sha256": self.artifact_sha256,
            "expected_registry_root": self.expected_registry_root,
            "findings": [finding.to_json() for finding in self.findings],
            "manifest_complete": False,
            "ok": not self.findings,
            "production_authority": "NONE",
            "production_promotion": False,
            "release_eligible": False,
            "requirements_closed": False,
            "schema": CHECK_SCHEMA_V1,
            "semantic_capability_coverage_complete": False,
            "semantic_closure_complete": False,
            "semantic_target_inventory_complete": False,
            "settlement_authority": "NONE",
            "source_row_census_complete": self.source_row_census_complete,
            "structural_mapping_complete": False,
            "value_movement_claim_allowed": False,
        }


@dataclass(frozen=True)
class WorkflowSourceV1:
    requirement_id: str
    fields_bytes: bytes
    scenarios: tuple[ScenarioSourceV1, ...]


@dataclass(frozen=True)
class ScenarioSourceV1:
    requirement_id: str
    fields_bytes: bytes
    invariant_ids: tuple[str, ...]


@dataclass(frozen=True)
class SimpleSourceV1:
    requirement_id: str
    fields_bytes: bytes
    invariant_ids: tuple[str, ...]


@dataclass(frozen=True)
class SourceBundleV1:
    workflows: tuple[WorkflowSourceV1, ...]
    invariants: tuple[SimpleSourceV1, ...]
    expansions: tuple[SimpleSourceV1, ...]
    findings: tuple[SimpleSourceV1, ...]
    policies: tuple[SimpleSourceV1, ...]
    capability_pairs: tuple[tuple[str, str, str], ...]
    routes: tuple[str, ...]
    exclusions: tuple[tuple[str, str, bytes], ...]
    semantic_anchors_bytes: bytes
    m6_historical_links: tuple[tuple[str, tuple[str, ...]], ...]


MappingSpecV1 = tuple[tuple[str, str], ...]


def _pairs(lane_id: str, *capability_ids: str) -> MappingSpecV1:
    return tuple((lane_id, capability_id) for capability_id in capability_ids)


def _cap(lane_id: str, capability_id: str, relation_type: RelationKindV1) -> EdgeV1:
    return EdgeV1(relation_type, f"lane_capability:{lane_id}:{capability_id}")


def _route(route_id: str) -> EdgeV1:
    return EdgeV1(RelationKindV1.REQUIRED_ROUTE_SCOPE, f"required_route:{route_id}")


def _exclusion(capability_id: str) -> EdgeV1:
    return EdgeV1(RelationKindV1.EXCLUSION_SCOPE, f"exclusion:{capability_id}")


WORKFLOW_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, MappingSpecV1], ...]] = (
    (
        "WF-01",
        _pairs(
            "ASSET_TRANSFER",
            "account_lifecycle",
            "native_asset_accounting",
            "generic_transfer",
            "transaction_fee",
        ),
    ),
    (
        "WF-02",
        _pairs(
            "SPOT_LIQUIDITY",
            "exact_in_swap",
            "exact_out_swap",
            "governed_route",
            "atomic_batch",
            "fee_allocation",
        ),
    ),
    (
        "WF-03",
        _pairs(
            "SPOT_LIQUIDITY", "lp_issue", "lp_burn", "pool_close", "residue_terminal_disposition"
        ),
    ),
    ("WF-04", _pairs("ZUSD_MONETARY", "collateral_deposit", "collateral_withdraw")),
    ("WF-05", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("WF-06", _pairs("ZUSD_MONETARY", "zusd_repay", "vault_owner_close")),
    ("WF-07", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    (
        "WF-08",
        _pairs(
            "ZUSD_MONETARY",
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "stability_pool_claim",
        ),
    ),
    ("WF-09", ()),
    (
        "WF-10",
        _pairs(
            "PERPS_MARKET",
            "position_open",
            "position_adjust",
            "funding_accrual",
            "fee_allocation",
            "insurance_reserve",
            "terminal_closeout",
        ),
    ),
    (
        "WF-11",
        _pairs(
            "PROOF_REWARDS",
            "reward_reserve",
            "verified_result_binding",
            "claimant_binding",
            "claim_nullifier",
            "reward_payout",
            "task_terminal_state",
        ),
    ),
    ("WF-12", _pairs("ORACLE_MARKET", "report_submit", "report_finality")),
    (
        "WF-13",
        _pairs(
            "GOVERNANCE_MIGRATION",
            "release_activation",
            "schema_migration",
            "writer_epoch_rotation",
        ),
    ),
    ("WF-14", ()),
    ("WF-15", _pairs("EXTERNAL_CUSTODY", "outbox_acknowledgment", "destination_idempotency")),
    ("WF-16", ()),
    ("WF-17", ()),
    (
        "WF-18",
        _pairs(
            "SEALED_AUCTION",
            "bid_commitment",
            "bond_accounting_location",
            "bid_reveal",
            "deterministic_clearing",
            "payment_settlement",
            "inventory_settlement",
            "refund",
            "slash",
            "auction_cancel",
            "auction_expiry",
        ),
    ),
)

# These are deliberately scenario-specific.  BDD rows never inherit their
# workflow's full capability edge set.
BDD_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, MappingSpecV1], ...]] = (
    ("BDD-001", _pairs("ASSET_TRANSFER", "generic_transfer", "native_asset_accounting")),
    ("BDD-002", _pairs("ASSET_TRANSFER", "generic_transfer")),
    ("BDD-003", _pairs("ASSET_TRANSFER", "generic_transfer")),
    ("BDD-004", _pairs("ASSET_TRANSFER", "generic_transfer")),
    ("BDD-005", _pairs("SPOT_LIQUIDITY", "exact_in_swap", "fee_allocation")),
    ("BDD-006", _pairs("SPOT_LIQUIDITY", "exact_in_swap")),
    ("BDD-007", _pairs("SPOT_LIQUIDITY", "atomic_batch")),
    ("BDD-008", _pairs("SPOT_LIQUIDITY", "exact_in_swap")),
    ("BDD-009", _pairs("SPOT_LIQUIDITY", "lp_issue")),
    ("BDD-010", _pairs("SPOT_LIQUIDITY", "lp_issue")),
    (
        "BDD-011",
        _pairs("SPOT_LIQUIDITY", "lp_burn", "fee_allocation", "residue_terminal_disposition"),
    ),
    ("BDD-012", _pairs("SPOT_LIQUIDITY", "pool_close", "residue_terminal_disposition")),
    ("BDD-013", _pairs("ZUSD_MONETARY", "collateral_deposit")),
    ("BDD-014", _pairs("ZUSD_MONETARY", "collateral_withdraw")),
    ("BDD-015", _pairs("ZUSD_MONETARY", "collateral_withdraw")),
    ("BDD-016", _pairs("ZUSD_MONETARY", "collateral_deposit", "collateral_withdraw")),
    ("BDD-017", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("BDD-018", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("BDD-019", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("BDD-020", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("BDD-021", _pairs("ZUSD_MONETARY", "zusd_mint")),
    ("BDD-022", _pairs("ZUSD_MONETARY", "zusd_repay")),
    ("BDD-023", _pairs("ZUSD_MONETARY", "zusd_repay")),
    ("BDD-024", _pairs("ZUSD_MONETARY", "zusd_repay")),
    ("BDD-025", _pairs("ZUSD_MONETARY", "vault_owner_close")),
    ("BDD-026", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    ("BDD-027", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    ("BDD-028", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    ("BDD-029", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    ("BDD-030", _pairs("ZUSD_MONETARY", "stability_pool_deposit")),
    (
        "BDD-031",
        _pairs("ZUSD_MONETARY", "stability_pool_deposit", "stability_pool_withdraw"),
    ),
    ("BDD-032", _pairs("ZUSD_MONETARY", "stability_pool_claim", "liquidation")),
    ("BDD-033", ()),
    ("BDD-034", ()),
    ("BDD-035", ()),
    ("BDD-036", ()),
    ("BDD-037", ()),
    ("BDD-038", ()),
    ("BDD-039", _pairs("PERPS_MARKET", "position_open", "position_adjust")),
    ("BDD-040", _pairs("PERPS_MARKET", "position_open", "position_adjust")),
    (
        "BDD-041",
        _pairs(
            "PERPS_MARKET",
            "position_adjust",
            "funding_accrual",
            "fee_allocation",
            "insurance_reserve",
        ),
    ),
    ("BDD-042", _pairs("PERPS_MARKET", "terminal_closeout")),
    ("BDD-043", _pairs("PERPS_MARKET", "position_open", "position_adjust")),
    ("BDD-044", _pairs("PROOF_REWARDS", "reward_reserve", "reward_payout")),
    ("BDD-045", _pairs("PROOF_REWARDS", "verified_result_binding", "claimant_binding")),
    ("BDD-046", _pairs("PROOF_REWARDS", "reward_reserve", "reward_payout")),
    ("BDD-047", _pairs("PROOF_REWARDS", "claim_nullifier")),
    ("BDD-048", _pairs("ORACLE_MARKET", "report_submit", "report_finality")),
    ("BDD-049", _pairs("ORACLE_MARKET", "report_submit")),
    ("BDD-050", ()),
    ("BDD-051", _pairs("ORACLE_MARKET", "report_finality")),
    (
        "BDD-052",
        _pairs(
            "GOVERNANCE_MIGRATION",
            "release_activation",
            "schema_migration",
            "writer_epoch_rotation",
        ),
    ),
    ("BDD-053", _pairs("GOVERNANCE_MIGRATION", "release_activation")),
    ("BDD-054", _pairs("GOVERNANCE_MIGRATION", "schema_migration")),
    ("BDD-055", _pairs("GOVERNANCE_MIGRATION", "writer_epoch_rotation")),
    ("BDD-056", _pairs("GOVERNANCE_MIGRATION", "writer_epoch_rotation")),
    ("BDD-057", ()),
    ("BDD-058", ()),
    ("BDD-059", ()),
    ("BDD-060", ()),
    ("BDD-061", ()),
    ("BDD-062", ()),
    ("BDD-063", _pairs("EXTERNAL_CUSTODY", "destination_idempotency")),
    ("BDD-064", ()),
    ("BDD-065", ()),
    ("BDD-066", ()),
    ("BDD-067", ()),
    ("BDD-068", _pairs("ZUSD_MONETARY", "all_claims_terminal_drain")),
    ("BDD-069", ()),
    ("BDD-070", ()),
    ("BDD-071", ()),
    ("BDD-072", ()),
    ("BDD-073", _pairs("SEALED_AUCTION", "bid_commitment", "bond_accounting_location")),
    ("BDD-074", _pairs("SEALED_AUCTION", "bid_commitment", "bond_accounting_location")),
    ("BDD-075", _pairs("SEALED_AUCTION", "bid_reveal")),
    ("BDD-076", _pairs("SEALED_AUCTION", "bid_reveal")),
    (
        "BDD-077",
        _pairs(
            "SEALED_AUCTION",
            "deterministic_clearing",
            "payment_settlement",
            "inventory_settlement",
            "refund",
            "slash",
        ),
    ),
    ("BDD-078", _pairs("SEALED_AUCTION", "refund", "slash")),
    ("BDD-079", _pairs("SEALED_AUCTION", "auction_cancel", "auction_expiry")),
    ("BDD-080", ()),
    ("BDD-081", ()),
)

RSE_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, MappingSpecV1], ...]] = (
    ("RSE-001", _pairs("ASSET_TRANSFER", "native_asset_accounting")),
    ("RSE-002", ()),
    ("RSE-003", ()),
    ("RSE-004", _pairs("ZDEX_TOKENOMICS", "staking_claim", "reserve_lifecycle")),
    ("RSE-005", _pairs("ZUSD_MONETARY", "vault_owner_close", "multi_vault_redemption")),
    (
        "RSE-006",
        _pairs("PERPS_MARKET", "funding_accrual", "insurance_reserve", "terminal_closeout"),
    ),
    (
        "RSE-007",
        _pairs("SPOT_LIQUIDITY", "pool_create"),
    ),
    (
        "RSE-008",
        _pairs(
            "SEALED_AUCTION",
            "bond_accounting_location",
            "refund",
            "slash",
            "auction_cancel",
            "auction_expiry",
        ),
    ),
    ("RSE-009", _pairs("EXTERNAL_CUSTODY", "outbox_acknowledgment", "destination_idempotency")),
    ("RSE-010", ()),
    ("RSE-011", ()),
)

CE_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, MappingSpecV1], ...]] = (
    ("CE-001", _pairs("ASSET_TRANSFER", "native_asset_accounting")),
    ("CE-002", _pairs("ASSET_TRANSFER", "native_asset_accounting")),
    ("CE-003", _pairs("ASSET_TRANSFER", "generic_transfer")),
    ("CE-004", ()),
    ("CE-005", ()),
    ("CE-006", _pairs("ZDEX_TOKENOMICS", "staking_claim", "reserve_lifecycle")),
    ("CE-007", _pairs("ZUSD_MONETARY", "multi_vault_redemption")),
    ("CE-008", _pairs("ZUSD_MONETARY", "vault_owner_close")),
)

UP_CAPABILITY_SPECS_V1: Final[tuple[tuple[str, MappingSpecV1], ...]] = (
    (
        "UP-01",
        _pairs(
            "ZDEX_TOKENOMICS",
            "fee_routing",
            "staking_claim",
            "host_compensation_claim",
            "treasury_claim",
            "reserve_lifecycle",
            "atomic_purchase_and_burn",
        ),
    ),
    ("UP-02", _pairs("ZDEX_TOKENOMICS", "host_compensation_claim")),
    (
        "UP-03",
        _pairs(
            "FARM_INCENTIVES",
            "lp_stake",
            "stake_activation",
            "emission_accrual",
            "emission_claim",
            "farm_cancellation",
            "farm_terminal_drain",
        ),
    ),
    (
        "UP-04",
        _pairs(
            "ZUSD_MONETARY",
            "vault_open",
            "collateral_deposit",
            "collateral_withdraw",
            "zusd_mint",
            "zusd_repay",
            "vault_owner_close",
            "multi_vault_redemption",
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "stability_pool_claim",
            "liquidation",
            "recovery_mode",
            "all_claims_terminal_drain",
        ),
    ),
    (
        "UP-05",
        _pairs(
            "PERPS_MARKET",
            "margin_deposit",
            "margin_withdraw",
            "position_open",
            "position_adjust",
            "funding_accrual",
            "fee_allocation",
            "liquidation",
            "insurance_reserve",
            "auto_deleveraging",
            "bankruptcy_resolution",
            "terminal_closeout",
        ),
    ),
    (
        "UP-06",
        _pairs(
            "ORACLE_MARKET",
            "query_create",
            "tip_escrow",
            "reporter_bond",
            "report_submit",
            "report_finality",
            "reporter_reward",
            "report_dispute",
            "reward_clawback",
            "reporter_slash",
            "oracle_terminal_drain",
        ),
    ),
    (
        "UP-07",
        _pairs(
            "SEALED_AUCTION",
            "bid_commitment",
            "bond_accounting_location",
            "bid_reveal",
            "deterministic_clearing",
            "payment_settlement",
            "inventory_settlement",
            "refund",
            "slash",
            "auction_cancel",
            "auction_expiry",
        ),
    ),
    (
        "UP-08",
        _pairs(
            "STRATEGY_ESCROW",
            "value_reservation",
            "strategy_activation",
            "strategy_trigger",
            "strategy_replace",
            "strategy_cancel",
            "strategy_expiry",
            "strategy_recovery",
        ),
    ),
    (
        "UP-09",
        _pairs(
            "PROOF_REWARDS",
            "reward_reserve",
            "verified_result_binding",
            "claimant_binding",
            "claim_nullifier",
            "reward_payout",
            "task_terminal_state",
        ),
    ),
    (
        "UP-10",
        _pairs(
            "GOVERNANCE_MIGRATION",
            "parameter_change",
            "release_activation",
            "treasury_action",
            "writer_epoch_rotation",
            "autonomous_governance_command_submission",
        ),
    ),
    (
        "UP-11",
        _pairs("ASSET_TRANSFER", "tau_originated_asset_registration")
        + _pairs("EXTERNAL_CUSTODY", "external_finality"),
    ),
    (
        "UP-12",
        _pairs(
            "SPOT_LIQUIDITY",
            "pool_create",
            "exact_in_swap",
            "exact_out_swap",
            "governed_route",
            "atomic_batch",
            "lp_issue",
            "lp_burn",
            "pool_close",
            "fee_allocation",
            "residue_terminal_disposition",
        ),
    ),
    (
        "UP-13",
        _pairs(
            "ASSET_TRANSFER", "generic_transfer", "managed_issue", "managed_burn", "transaction_fee"
        ),
    ),
    (
        "UP-14",
        _pairs("ZDEX_TOKENOMICS", "atomic_purchase_and_burn", "retained_supply_hyperdeflation"),
    ),
    (
        "UP-15",
        _pairs(
            "ZDEX_TOKENOMICS",
            "staking_claim",
            "reserve_lifecycle",
            "retained_supply_hyperdeflation",
        ),
    ),
    (
        "UP-16",
        _pairs("ASSET_TRANSFER", "generic_transfer")
        + _pairs("GOVERNANCE_MIGRATION", "parameter_change"),
    ),
    (
        "UP-17",
        _pairs("ORACLE_MARKET", "report_finality")
        + _pairs("ZUSD_MONETARY", "recovery_mode")
        + _pairs("PERPS_MARKET", "funding_accrual"),
    ),
    # UP-18 is an exact local-helper reachability topic.  It cannot create
    # feature coverage for disabled external lock/burn/release/mint/timeout/refund.
    ("UP-18", _pairs("GOVERNANCE_MIGRATION", "release_activation", "writer_epoch_rotation")),
    ("UP-19", _pairs("ASSET_TRANSFER", "managed_issue")),
    ("UP-20", _pairs("ZDEX_TOKENOMICS", "retained_supply_hyperdeflation")),
)

RSE_INVARIANT_SPECS_V1: Final[tuple[tuple[str, tuple[str, ...]], ...]] = (
    ("RSE-001", ("INV-003", "INV-004", "INV-009")),
    ("RSE-002", ("INV-005", "INV-006", "INV-012")),
    ("RSE-003", ("INV-003", "INV-004")),
    ("RSE-004", ("INV-003", "INV-004", "INV-014")),
    ("RSE-005", ("INV-002", "INV-003", "INV-014")),
    ("RSE-006", ("INV-003", "INV-004", "INV-008", "INV-013", "INV-014")),
    ("RSE-007", ("INV-001", "INV-003", "INV-007")),
    ("RSE-008", ("INV-005", "INV-007", "INV-014")),
    ("RSE-009", ("INV-010", "INV-011")),
    ("RSE-010", ("INV-009", "INV-011")),
    ("RSE-011", ("INV-012", "INV-014")),
)

ROUTE_EDGE_SPECS_V1: Final[tuple[tuple[str, tuple[str, ...]], ...]] = (
    ("WF-10", ("perps_epoch_settlement",)),
    ("BDD-041", ("perps_epoch_settlement",)),
    ("UP-01", ("fee_funded_zdex_purchase_and_burn",)),
    ("UP-08", ("strategy_triggered_spot_swap",)),
    ("UP-12", ("fee_funded_zdex_purchase_and_burn", "strategy_triggered_spot_swap")),
    ("UP-14", ("fee_funded_zdex_purchase_and_burn",)),
)

EXCLUSION_EDGE_SPECS_V1: Final[tuple[tuple[str, tuple[str, ...]], ...]] = (
    ("WF-16", ("zusd_emergency_shutdown",)),
    ("BDD-065", ("zusd_emergency_shutdown",)),
    ("BDD-066", ("zusd_emergency_shutdown",)),
    ("BDD-067", ("zusd_emergency_shutdown",)),
    ("UP-10", ("autonomous_governance_publication_authority",)),
    ("UP-12", ("caller_selected_route_or_proof_profile",)),
)

# These edges identify system-wide constraints.  They deliberately do not
# establish direct feature semantics or contribute to capability coverage.
CROSS_CUTTING_INVARIANT_SPECS_V1: Final[tuple[tuple[str, tuple[str, ...]], ...]] = (
    ("WF-14", ("INV-007", "INV-009", "INV-010", "INV-011")),
    ("WF-17", ("INV-012",)),
    ("BDD-069", ("INV-012",)),
    ("BDD-070", ("INV-012",)),
    ("BDD-071", ("INV-012",)),
    ("BDD-072", ("INV-012",)),
)

NONCLAIMS_V1: Final[tuple[str, ...]] = (
    "Structural mapping does not establish requirements completeness.",
    "The ATDD donor has stale internal provenance and remains a research-only draft.",
    "The Luna donor has stale internal provenance and remains advisory only.",
    "No row is evidence of specification completion, implementation, proof, mounting, testing, release eligibility, or production authority.",
    "This registry grants no value-moving, settlement, publication, migration, or promotion authority.",
    "The JSON and Markdown outputs are independently atomic files; a crash can leave a mixed pair until deterministic regeneration reruns.",
    "Atomic replacement assumes a trusted single-writer output directory; inode and byte checks detect substitution but do not defend a directory controlled by the same OS authority.",
)


def _sanitized_finding_text_v1(value: str, limit: int) -> str:
    cleaned = "".join(
        character if ord(character) >= 32 and not 0xD800 <= ord(character) <= 0xDFFF else "?"
        for character in value
    )
    return cleaned if len(cleaned) <= limit else cleaned[: limit - 3] + "..."


@dataclass(frozen=True, slots=True)
class _JsonPathV1:
    """One constant-size path edge retained until a rejection needs rendering."""

    parent: str | _JsonPathV1
    component: str | int


@dataclass(slots=True)
class _JsonBudgetV1:
    """Cumulative work charged while creating one owned JSON snapshot."""

    nodes: int = 0
    string_characters: int = 0


@dataclass(frozen=True, slots=True)
class _JsonVisitV1:
    value: object
    path: str | _JsonPathV1
    depth: int
    destination: list[object] | dict[str, object]
    destination_key: str | None = None


@dataclass(slots=True)
class _JsonListCursorV1:
    values: list[object]
    owned: list[object]
    path: str | _JsonPathV1
    depth: int
    expected_length: int
    next_index: int = 0


@dataclass(slots=True)
class _JsonDictCursorV1:
    values: dict[str, object]
    items: Iterator[tuple[str, object]]
    owned: dict[str, object]
    path: str | _JsonPathV1
    depth: int
    expected_length: int


@dataclass(slots=True)
class _JsonEncodeListCursorV1:
    values: list[object]
    next_index: int = 0


@dataclass(slots=True)
class _JsonEncodeDictCursorV1:
    items: tuple[tuple[str, object], ...]
    next_index: int = 0


def _render_json_path_v1(path: str | _JsonPathV1) -> str:
    """Render only the bounded finding prefix of a lazily represented path."""

    if type(path) is str:
        return path
    components: list[str | int] = []
    current: str | _JsonPathV1 = path
    while type(current) is _JsonPathV1:
        components.append(current.component)
        current = current.parent
    if type(current) is not str:
        raise TypeError("JSON path root must have exact str type")
    root = current
    parts: list[str] = []
    rendered_length = 0
    truncated = False

    def append_prefix(text: str) -> None:
        nonlocal rendered_length, truncated
        remaining = MAX_FINDING_PATH_CHARS_V1 - rendered_length
        if remaining <= 0:
            truncated = True
            return
        if len(text) > remaining:
            parts.append(text[:remaining])
            rendered_length += remaining
            truncated = True
            return
        parts.append(text)
        rendered_length += len(text)

    append_prefix(root)
    for component in reversed(components):
        if truncated:
            break
        if type(component) is int:
            append_prefix("[")
            append_prefix(str(component))
            append_prefix("]")
        else:
            if type(component) is not str:
                raise TypeError("JSON path component must be exact str or int")
            append_prefix(".")
            append_prefix(component)
    rendered = "".join(parts)
    if truncated and MAX_FINDING_PATH_CHARS_V1 >= 3:
        return rendered[: MAX_FINDING_PATH_CHARS_V1 - 3] + "..."
    return rendered


def _reject(code: str, path: str | _JsonPathV1, detail: str) -> NoReturn:
    raise RequirementsRejectV1(
        _sanitized_finding_text_v1(code, 64),
        _sanitized_finding_text_v1(_render_json_path_v1(path), MAX_FINDING_PATH_CHARS_V1),
        _sanitized_finding_text_v1(detail, MAX_FINDING_DETAIL_CHARS_V1),
    )


def _duplicate_key_rejector(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _nonfinite_rejector(value: str) -> NoReturn:
    del value
    raise ValueError("non-finite JSON constant")


def _bounded_parse_int_v1(value: str) -> int:
    digits = value[1:] if value.startswith("-") else value
    if len(digits) > MAX_JSON_INTEGER_DIGITS_V1:
        raise ValueError("JSON integer digit ceiling exceeded")
    return int(value)


def _float_rejector_v1(value: str) -> NoReturn:
    del value
    raise ValueError("floating-point JSON numbers are forbidden")


def _validate_json_string_v1(value: str, path: str | _JsonPathV1) -> None:
    if len(value) > MAX_JSON_STRING_CHARS_V1:
        _reject("JSON_STRING_LIMIT", path, "string exceeds character ceiling")
    if any(0xD800 <= ord(character) <= 0xDFFF for character in value):
        _reject("JSON_LONE_SURROGATE", path, "lone Unicode surrogate is forbidden")


def _charge_json_node_v1(budget: _JsonBudgetV1, path: str | _JsonPathV1) -> None:
    budget.nodes += 1
    if budget.nodes > MAX_JSON_NODES_V1:
        _reject("JSON_NODE_LIMIT", path, "JSON node ceiling exceeded")


def _snapshot_json_string_v1(value: str, path: str | _JsonPathV1, budget: _JsonBudgetV1) -> str:
    """Validate and charge one serialized occurrence of an exact string."""

    _validate_json_string_v1(value, path)
    budget.string_characters += len(value)
    # Every source character needs at least one canonical ASCII byte. Charging
    # aliases by occurrence bounds validation work before canonical expansion.
    if budget.string_characters > MAX_JSON_BYTES_V1:
        _reject("JSON_BYTE_LIMIT", path, "canonical JSON byte ceiling exceeded")
    return value


def _store_owned_json_v1(task: _JsonVisitV1, owned: object) -> None:
    if type(task.destination) is list:
        task.destination.append(owned)
        return
    if type(task.destination) is dict and type(task.destination_key) is str:
        task.destination[task.destination_key] = owned
        return
    raise RuntimeError("invalid internal JSON snapshot destination")


def _owned_json_v1(value: object, path: str) -> object:
    """Create one transitively owned exact-JSON snapshot with an explicit stack."""

    budget = _JsonBudgetV1()
    root: list[object] = []
    stack: list[_JsonVisitV1 | _JsonListCursorV1 | _JsonDictCursorV1] = [
        _JsonVisitV1(value, path, 0, root)
    ]
    while stack:
        task = stack.pop()
        if type(task) is _JsonListCursorV1:
            if len(task.values) != task.expected_length:
                _reject("JSON_MUTATION", task.path, "list length changed during snapshot")
            if task.next_index >= task.expected_length:
                continue
            index = task.next_index
            task.next_index += 1
            try:
                item = task.values[index]
            except IndexError:
                _reject("JSON_MUTATION", task.path, "list changed during snapshot")
            stack.append(task)
            stack.append(
                _JsonVisitV1(
                    item,
                    _JsonPathV1(task.path, index),
                    task.depth + 1,
                    task.owned,
                )
            )
            continue
        if type(task) is _JsonDictCursorV1:
            try:
                key, item = next(task.items)
            except StopIteration:
                if (
                    len(task.values) != task.expected_length
                    or len(task.owned) != task.expected_length
                ):
                    _reject("JSON_MUTATION", task.path, "object changed during snapshot")
                continue
            except RuntimeError:
                _reject("JSON_MUTATION", task.path, "object changed during snapshot")
            _charge_json_node_v1(budget, task.path)
            if type(key) is not str:
                _reject("JSON_KEY_TYPE", task.path, "object keys must have exact str type")
            owned_key = _snapshot_json_string_v1(key, _JsonPathV1(task.path, "<key>"), budget)
            if owned_key in task.owned:
                _reject("JSON_MUTATION", task.path, "object key repeated during snapshot")
            stack.append(task)
            stack.append(
                _JsonVisitV1(
                    item,
                    _JsonPathV1(task.path, owned_key),
                    task.depth + 1,
                    task.owned,
                    owned_key,
                )
            )
            continue
        if type(task) is not _JsonVisitV1:
            raise RuntimeError("invalid internal JSON snapshot task")

        _charge_json_node_v1(budget, task.path)
        if task.depth > MAX_JSON_DEPTH_V1:
            _reject("JSON_DEPTH_LIMIT", task.path, "JSON depth ceiling exceeded")
        current = task.value
        if current is None or type(current) is bool:
            _store_owned_json_v1(task, current)
            continue
        if type(current) is int:
            if (
                not -MAX_JSON_INTEGER_MAGNITUDE_EXCLUSIVE_V1
                < current
                < MAX_JSON_INTEGER_MAGNITUDE_EXCLUSIVE_V1
            ):
                _reject("JSON_INTEGER_LIMIT", task.path, "integer exceeds digit ceiling")
            _store_owned_json_v1(task, current)
            continue
        if type(current) is str:
            _store_owned_json_v1(task, _snapshot_json_string_v1(current, task.path, budget))
            continue
        if type(current) is list:
            owned_list: list[object] = []
            _store_owned_json_v1(task, owned_list)
            stack.append(
                _JsonListCursorV1(
                    values=current,
                    owned=owned_list,
                    path=task.path,
                    depth=task.depth,
                    expected_length=len(current),
                )
            )
            continue
        if type(current) is dict:
            owned_dict: dict[str, object] = {}
            _store_owned_json_v1(task, owned_dict)
            stack.append(
                _JsonDictCursorV1(
                    values=current,
                    items=iter(current.items()),
                    owned=owned_dict,
                    path=task.path,
                    depth=task.depth,
                    expected_length=len(current),
                )
            )
            continue
        _reject("JSON_TYPE", task.path, "unsupported exact JSON value type")
    if len(root) != 1:
        raise RuntimeError("invalid internal JSON snapshot root")
    return root[0]


def _validate_json_v1(value: object, path: str) -> None:
    _owned_json_v1(value, path)


def _require_supported_python_runtime_v1() -> None:
    """Fail closed before low process recursion limits can leak raw failures."""

    if sys.getrecursionlimit() < MIN_PYTHON_RECURSION_LIMIT_V1:
        raise RequirementsRejectV1(
            "JSON_RUNTIME_RECURSION_LIMIT",
            "$",
            "Python recursion limit is below the supported deterministic floor",
        )


def _append_canonical_json_chunk_v1(chunks: list[bytes], encoded_size: int, chunk: str) -> int:
    encoded = chunk.encode("ascii")
    next_size = encoded_size + len(encoded)
    if next_size > MAX_JSON_BYTES_V1:
        _reject("JSON_BYTE_LIMIT", "$", "canonical JSON byte ceiling exceeded")
    chunks.append(encoded)
    return next_size


def _encode_owned_json_v1(value: object) -> bytes:
    """Encode an owned exact-JSON value without Python recursion."""

    chunks: list[bytes] = []
    encoded_size = 0
    stack: list[object | _JsonEncodeListCursorV1 | _JsonEncodeDictCursorV1] = [value]
    while stack:
        task = stack.pop()
        if type(task) is _JsonEncodeListCursorV1:
            if task.next_index >= len(task.values):
                encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, "]")
                continue
            if task.next_index:
                encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, ",")
            item = task.values[task.next_index]
            task.next_index += 1
            stack.append(task)
            stack.append(item)
            continue
        if type(task) is _JsonEncodeDictCursorV1:
            if task.next_index >= len(task.items):
                encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, "}")
                continue
            if task.next_index:
                encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, ",")
            key, item = task.items[task.next_index]
            task.next_index += 1
            encoded_size = _append_canonical_json_chunk_v1(
                chunks, encoded_size, json.encoder.encode_basestring_ascii(key)
            )
            encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, ":")
            stack.append(task)
            stack.append(item)
            continue
        if task is None:
            encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, "null")
            continue
        if type(task) is bool:
            encoded_size = _append_canonical_json_chunk_v1(
                chunks, encoded_size, "true" if task else "false"
            )
            continue
        if type(task) is int:
            encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, str(task))
            continue
        if type(task) is str:
            encoded_size = _append_canonical_json_chunk_v1(
                chunks, encoded_size, json.encoder.encode_basestring_ascii(task)
            )
            continue
        if type(task) is list:
            encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, "[")
            stack.append(_JsonEncodeListCursorV1(task))
            continue
        if type(task) is dict:
            encoded_size = _append_canonical_json_chunk_v1(chunks, encoded_size, "{")
            stack.append(_JsonEncodeDictCursorV1(tuple(sorted(task.items()))))
            continue
        raise RuntimeError("owned JSON snapshot contains an invalid value")
    return b"".join(chunks)


def canonical_json_bytes_v1(value: object) -> bytes:
    """Encode one caller-owned, quiescent exact-JSON value canonically.

    Claim-bearing ingress uses immutable bytes and ``decode_json_object_v1``.
    This helper does not make a concurrently shared mutable object linearizable.
    """

    _require_supported_python_runtime_v1()
    return _encode_owned_json_v1(_owned_json_v1(value, "$"))


def decode_json_object_v1(raw: bytes, label: str) -> dict[str, object]:
    """Decode a closed JSON object at a shell-to-core boundary."""

    _require_supported_python_runtime_v1()
    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", label, "must have exact bytes type")
    if len(raw) > MAX_JSON_BYTES_V1:
        _reject("JSON_BYTE_LIMIT", label, "JSON byte ceiling exceeded")
    try:
        parsed = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_duplicate_key_rejector,
            parse_constant=_nonfinite_rejector,
            parse_float=_float_rejector_v1,
            parse_int=_bounded_parse_int_v1,
        )
    except (
        MemoryError,
        RecursionError,
        UnicodeDecodeError,
        ValueError,
        json.JSONDecodeError,
    ) as exc:
        _reject("JSON_DECODE", label, f"{type(exc).__name__}: {exc}")
    owned = _owned_json_v1(parsed, label)
    if type(owned) is not dict:
        _reject("JSON_ROOT_TYPE", label, "root must be an object")
    return owned


def _decoded_canonical_object_v1(raw: bytes) -> dict[str, object]:
    decoded = decode_json_object_v1(raw, "canonical-source-fields")
    return decoded


def _canonical_object_bytes_v1(value: dict[str, object], path: str) -> bytes:
    _validate_json_v1(value, path)
    return canonical_json_bytes_v1(value)


def _expect_object(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        _reject("TYPE_ERROR", path, "must have exact object type")
    return value


def _expect_list(value: object, path: str) -> list[object]:
    if type(value) is not list:
        _reject("TYPE_ERROR", path, "must have exact list type")
    return value


def _expect_str(value: object, path: str) -> str:
    if type(value) is not str:
        _reject("TYPE_ERROR", path, "must have exact str type")
    return value


def _expect_int(value: object, path: str) -> int:
    if type(value) is not int:
        _reject("TYPE_ERROR", path, "must have exact int type")
    return value


def _expect_bool(value: object, path: str) -> bool:
    if type(value) is not bool:
        _reject("TYPE_ERROR", path, "must have exact bool type")
    return value


def _closed(value: dict[str, object], expected: frozenset[str], path: str) -> dict[str, object]:
    observed = frozenset(value)
    if observed != expected:
        _reject(
            "CLOSED_FIELDS",
            path,
            f"missing={sorted(expected - observed)} extra={sorted(observed - expected)}",
        )
    return value


def _sequence(prefix: str, width: int, count: int) -> tuple[str, ...]:
    return tuple(f"{prefix}{index:0{width}d}" for index in range(1, count + 1))


_TableValueT = TypeVar("_TableValueT")


def _table_value_v1(
    table: tuple[tuple[str, _TableValueT], ...],
    requirement_id: str,
    table_name: str,
) -> _TableValueT:
    keys = tuple(candidate for candidate, _ in table)
    if len(keys) != len(set(keys)):
        _reject(
            "MAPPING_TABLE_DUPLICATE_KEY",
            table_name,
            "mapping table keys must be unique before lookup",
        )
    matches = tuple(value for candidate, value in table if candidate == requirement_id)
    if len(matches) == 1:
        return matches[0]
    _reject("MAPPING_TABLE_MISSING", requirement_id, f"missing {table_name} entry")


def _capability_edges_v1(
    specification: MappingSpecV1, relation_type: RelationKindV1
) -> tuple[EdgeV1, ...]:
    return tuple(
        _cap(lane_id, capability_id, relation_type) for lane_id, capability_id in specification
    )


def _snapshot_documents_v1(snapshot: SourceSnapshotV1) -> dict[str, bytes]:
    for field_name, commit in (
        ("captured_git_head", snapshot.captured_git_head),
        ("rechecked_git_head", snapshot.rechecked_git_head),
    ):
        if type(commit) is not str or not _COMMIT_RE.fullmatch(commit):
            _reject(
                "SUBJECT_TYPE",
                f"snapshot.{field_name}",
                "must be lowercase Git commit SHA",
            )
    if snapshot.captured_git_head != snapshot.rechecked_git_head:
        _reject(
            "SOURCE_HEAD_MOVED",
            "snapshot.rechecked_git_head",
            "Git HEAD changed during source acquisition",
        )
    if (
        type(snapshot.source_subject_tree) is not str
        or not _COMMIT_RE.fullmatch(snapshot.source_subject_tree)
        or snapshot.source_subject_tree != SOURCE_SUBJECT_TREE_V1
    ):
        _reject(
            "SOURCE_SUBJECT_TREE_MISMATCH",
            "snapshot.source_subject_tree",
            "immutable source subject tree drift",
        )
    if type(snapshot.source_subject_is_ancestor) is not bool:
        _reject(
            "SUBJECT_ANCESTRY_TYPE",
            "snapshot.source_subject_is_ancestor",
            "must have exact bool type",
        )
    if not snapshot.source_subject_is_ancestor:
        _reject(
            "SOURCE_SUBJECT_NOT_ANCESTOR",
            "snapshot.source_subject_is_ancestor",
            "immutable source subject must be an ancestor of current Git HEAD",
        )
    if type(snapshot.document_bytes) is not tuple:
        _reject("SOURCE_DOCUMENT_SET", "snapshot.document_bytes", "must have exact tuple type")
    if type(snapshot.source_subject_entries) is not tuple:
        _reject(
            "SOURCE_SUBJECT_ENTRY_SET",
            "snapshot.source_subject_entries",
            "must have exact tuple type",
        )
    if type(snapshot.current_head_entries) is not tuple:
        _reject(
            "CURRENT_HEAD_ENTRY_SET",
            "snapshot.current_head_entries",
            "must have exact tuple type",
        )
    expected_paths = tuple(pin.path for pin in SOURCE_PINS_V1)
    actual_paths: tuple[object, ...] = tuple(
        document[0] if type(document) is tuple and len(document) == 2 else None
        for document in snapshot.document_bytes
    )

    def entry_paths(
        entries: tuple[tuple[str, str, str, str], ...], code: str
    ) -> tuple[object, ...]:
        paths: list[object] = []
        for index, entry in enumerate(entries):
            if type(entry) is not tuple or len(entry) != 4:
                _reject(
                    code,
                    f"snapshot.entries[{index}]",
                    "tree entry must be an exact four-string tuple",
                )
            paths.append(entry[0])
        return tuple(paths)

    source_entry_paths = entry_paths(snapshot.source_subject_entries, "SOURCE_SUBJECT_ENTRY_SET")
    current_entry_paths = entry_paths(snapshot.current_head_entries, "CURRENT_HEAD_ENTRY_SET")
    if actual_paths != expected_paths:
        _reject("SOURCE_DOCUMENT_SET", "snapshot", "source path set or order drift")
    if source_entry_paths != expected_paths:
        _reject(
            "SOURCE_SUBJECT_ENTRY_SET",
            "snapshot.source_subject_entries",
            "source-subject path set or order drift",
        )
    if current_entry_paths != expected_paths:
        _reject(
            "CURRENT_HEAD_ENTRY_SET",
            "snapshot.current_head_entries",
            "current-HEAD path set or order drift",
        )
    documents: dict[str, bytes] = {}
    for pin, document, source_entry, current_entry in zip(
        SOURCE_PINS_V1,
        snapshot.document_bytes,
        snapshot.source_subject_entries,
        snapshot.current_head_entries,
        strict=True,
    ):
        if type(document) is not tuple or len(document) != 2:
            _reject("SOURCE_DOCUMENT_TYPE", pin.path, "must be an exact path/bytes pair")
        path, raw = document
        if type(path) is not str or path != pin.path or type(raw) is not bytes:
            _reject("SOURCE_DOCUMENT_TYPE", pin.path, "must be an exact path/bytes pair")
        if hashlib.sha256(raw).hexdigest() != pin.sha256:
            _reject("SOURCE_SHA256_MISMATCH", pin.path, "source bytes drift")
        expected_entry = (pin.path, pin.git_mode, pin.git_object_type, pin.git_blob_sha)
        for label, entry in (
            ("SOURCE_SUBJECT_ENTRY_MISMATCH", source_entry),
            ("CURRENT_HEAD_ENTRY_MISMATCH", current_entry),
        ):
            if type(entry) is not tuple or len(entry) != 4:
                _reject(label, pin.path, "tree entry must be an exact four-string tuple")
            if any(type(value) is not str for value in entry):
                _reject(label, pin.path, "tree entry fields must have exact str type")
            if entry != expected_entry:
                _reject(label, pin.path, "path, mode, type, or blob drift")
        documents[path] = raw
    return documents


def _source_rows_v1(
    values: list[object],
    expected_fields: frozenset[str],
    id_field: str,
    prefix: str,
    document_path: str,
    field_name: str,
    invariant_field: str | None = None,
) -> tuple[SimpleSourceV1, ...]:
    rows: list[SimpleSourceV1] = []
    seen: set[str] = set()
    for index, raw_row in enumerate(values):
        path = f"{document_path}.{field_name}[{index}]"
        row = _closed(_expect_object(raw_row, path), expected_fields, path)
        requirement_id = _expect_str(row[id_field], f"{path}.{id_field}")
        if not requirement_id.startswith(prefix):
            _reject("SOURCE_IDENTIFIER", f"{path}.{id_field}", f"must begin with {prefix}")
        if requirement_id in seen:
            _reject("SOURCE_DUPLICATE_ID", f"{path}.{id_field}", "duplicate source ID")
        seen.add(requirement_id)
        invariant_ids: tuple[str, ...] = ()
        if invariant_field is not None:
            references = _expect_list(row[invariant_field], f"{path}.{invariant_field}")
            invariant_ids = tuple(
                _expect_str(value, f"{path}.{invariant_field}[{reference_index}]")
                for reference_index, value in enumerate(references)
            )
        rows.append(
            SimpleSourceV1(requirement_id, _canonical_object_bytes_v1(row, path), invariant_ids)
        )
    return tuple(rows)


def _parse_atdd_v1(
    document: dict[str, object],
) -> tuple[
    tuple[WorkflowSourceV1, ...],
    tuple[SimpleSourceV1, ...],
    tuple[tuple[str, tuple[str, ...]], ...],
]:
    fields = _closed(document, _ATDD_ROOT_FIELDS, ATDD_PATH_V1)
    if (
        _expect_str(fields["schema"], f"{ATDD_PATH_V1}.schema")
        != "zenodex/m6-global-economic-core-atdd-bdd/v1"
    ):
        _reject("SOURCE_SCHEMA", ATDD_PATH_V1, "ATDD schema drift")
    if _expect_str(fields["status"], f"{ATDD_PATH_V1}.status") != "RESEARCH_ONLY_DRAFT":
        _reject("SOURCE_STATUS", ATDD_PATH_V1, "ATDD must remain research-only draft")
    if _expect_bool(fields["production_promotion"], f"{ATDD_PATH_V1}.production_promotion"):
        _reject("SOURCE_PROMOTION", ATDD_PATH_V1, "ATDD cannot promote production")
    workflows_raw = _expect_list(fields["workflows"], f"{ATDD_PATH_V1}.workflows")
    if len(workflows_raw) != 18:
        _reject("SOURCE_COUNT", f"{ATDD_PATH_V1}.workflows", "must contain 18 workflows")
    workflows: list[WorkflowSourceV1] = []
    workflow_ids: list[str] = []
    bdd_ids: list[str] = []
    for workflow_index, raw_workflow in enumerate(workflows_raw):
        path = f"{ATDD_PATH_V1}.workflows[{workflow_index}]"
        workflow = _closed(_expect_object(raw_workflow, path), _WORKFLOW_FIELDS, path)
        workflow_id = _expect_str(workflow["id"], f"{path}.id")
        scenarios_raw = _expect_list(workflow["scenarios"], f"{path}.scenarios")
        scenarios: list[ScenarioSourceV1] = []
        for scenario_index, raw_scenario in enumerate(scenarios_raw):
            scenario_path = f"{path}.scenarios[{scenario_index}]"
            scenario = _closed(
                _expect_object(raw_scenario, scenario_path), _BDD_FIELDS, scenario_path
            )
            scenario_id = _expect_str(scenario["id"], f"{scenario_path}.id")
            references = _expect_list(scenario["requirements"], f"{scenario_path}.requirements")
            invariant_ids = tuple(
                _expect_str(reference, f"{scenario_path}.requirements[{reference_index}]")
                for reference_index, reference in enumerate(references)
            )
            if len(invariant_ids) != len(set(invariant_ids)):
                _reject(
                    "SOURCE_DUPLICATE_INVARIANT_REFERENCE",
                    scenario_path,
                    "BDD invariant reference duplicates",
                )
            scenarios.append(
                ScenarioSourceV1(
                    scenario_id,
                    _canonical_object_bytes_v1(scenario, scenario_path),
                    invariant_ids,
                )
            )
            bdd_ids.append(scenario_id)
        workflows.append(
            WorkflowSourceV1(
                workflow_id, _canonical_object_bytes_v1(workflow, path), tuple(scenarios)
            )
        )
        workflow_ids.append(workflow_id)
    if tuple(workflow_ids) != _sequence("WF-", 2, 18):
        _reject(
            "SOURCE_ID_SEQUENCE",
            f"{ATDD_PATH_V1}.workflows",
            "workflow IDs must be WF-01 through WF-18",
        )
    if tuple(bdd_ids) != _sequence("BDD-", 3, 81):
        _reject(
            "SOURCE_ID_SEQUENCE",
            f"{ATDD_PATH_V1}.workflows.scenarios",
            "BDD IDs must be BDD-001 through BDD-081",
        )

    invariants = _source_rows_v1(
        _expect_list(fields["invariants"], f"{ATDD_PATH_V1}.invariants"),
        _INVARIANT_FIELDS,
        "id",
        "INV-",
        ATDD_PATH_V1,
        "invariants",
    )
    if tuple(row.requirement_id for row in invariants) != _sequence("INV-", 3, 14):
        _reject(
            "SOURCE_ID_SEQUENCE", f"{ATDD_PATH_V1}.invariants", "must be INV-001 through INV-014"
        )
    invariant_id_set = {row.requirement_id for row in invariants}
    for workflow_source in workflows:
        for scenario_source in workflow_source.scenarios:
            dangling = sorted(set(scenario_source.invariant_ids) - invariant_id_set)
            if dangling:
                _reject("DANGLING_BDD_INVARIANT", scenario_source.requirement_id, str(dangling))

    coverage = _expect_object(fields["m6_coverage"], f"{ATDD_PATH_V1}.m6_coverage")
    expected_links = _sequence("M6-R", 2, 13)
    if tuple(sorted(coverage)) != expected_links:
        _reject(
            "SOURCE_ID_SEQUENCE", f"{ATDD_PATH_V1}.m6_coverage", "must be M6-R01 through M6-R13"
        )
    historical_links: list[tuple[str, tuple[str, ...]]] = []
    for historical_id in expected_links:
        linked = _expect_list(
            coverage[historical_id], f"{ATDD_PATH_V1}.m6_coverage.{historical_id}"
        )
        workflow_link_ids = tuple(
            _expect_str(value, f"{ATDD_PATH_V1}.m6_coverage.{historical_id}[{index}]")
            for index, value in enumerate(linked)
        )
        if not set(workflow_link_ids).issubset(set(workflow_ids)):
            _reject("DANGLING_M6_LINK", historical_id, "references an absent workflow")
        historical_links.append((historical_id, workflow_link_ids))
    return tuple(workflows), invariants, tuple(historical_links)


def _parse_luna_v1(
    document: dict[str, object],
) -> tuple[tuple[SimpleSourceV1, ...], tuple[SimpleSourceV1, ...]]:
    fields = _closed(document, _LUNA_ROOT_FIELDS, LUNA_PATH_V1)
    if (
        _expect_str(fields["schema"], f"{LUNA_PATH_V1}.schema")
        != "zenodex/m6-global-economic-core-luna-completeness-review/v1"
    ):
        _reject("SOURCE_SCHEMA", LUNA_PATH_V1, "Luna schema drift")
    if (
        _expect_str(fields["status"], f"{LUNA_PATH_V1}.status")
        != "RESEARCH_ONLY_REVIEWED_WITH_BLOCKERS"
    ):
        _reject("SOURCE_STATUS", LUNA_PATH_V1, "Luna status drift")
    if _expect_bool(fields["production_promotion"], f"{LUNA_PATH_V1}.production_promotion"):
        _reject("SOURCE_PROMOTION", LUNA_PATH_V1, "Luna cannot promote production")
    expansions = _source_rows_v1(
        _expect_list(
            fields["required_spec_expansions"], f"{LUNA_PATH_V1}.required_spec_expansions"
        ),
        _RSE_FIELDS,
        "id",
        "RSE-",
        LUNA_PATH_V1,
        "required_spec_expansions",
    )
    findings = _source_rows_v1(
        _expect_list(fields["confirmed_findings"], f"{LUNA_PATH_V1}.confirmed_findings"),
        _CE_FIELDS,
        "id",
        "CE-",
        LUNA_PATH_V1,
        "confirmed_findings",
        "affected_requirements",
    )
    if tuple(row.requirement_id for row in expansions) != _sequence("RSE-", 3, 11):
        _reject("SOURCE_ID_SEQUENCE", LUNA_PATH_V1, "RSE IDs must be RSE-001 through RSE-011")
    if tuple(row.requirement_id for row in findings) != _sequence("CE-", 3, 8):
        _reject("SOURCE_ID_SEQUENCE", LUNA_PATH_V1, "CE IDs must be CE-001 through CE-008")
    return expansions, findings


def _plan_record_v1(
    records: list[object], collection_path: str, id_field: str, expected_id: str
) -> tuple[int, dict[str, object]]:
    matches: list[tuple[int, dict[str, object]]] = []
    for index, raw_record in enumerate(records):
        record_path = f"{collection_path}[{index}]"
        record = _expect_object(raw_record, record_path)
        identifier = _expect_str(record.get(id_field), f"{record_path}.{id_field}")
        if identifier == expected_id:
            matches.append((index, record))
    if len(matches) != 1:
        _reject("SOURCE_OBLIGATION", collection_path, f"must contain exactly one {expected_id}")
    return matches[0]


def _parse_plan_claim_ceiling_v1(fields: dict[str, object]) -> None:
    """Give promotion-bearing fields typed, stable rejects before the full commitment."""

    authority_path = f"{PLAN_PATH_V1}.authority"
    authority = _closed(
        _expect_object(fields["authority"], authority_path),
        _PLAN_AUTHORITY_FIELDS_V1,
        authority_path,
    )
    for field in ("production_authority", "settlement_authority"):
        field_path = f"{authority_path}.{field}"
        if _expect_str(authority.get(field), field_path) != "NONE":
            _reject("SOURCE_PROMOTION", field_path, "authority must remain NONE")
    for field in ("production_ready", "release_ready"):
        field_path = f"{authority_path}.{field}"
        if _expect_bool(authority.get(field), field_path):
            _reject("SOURCE_PROMOTION", field_path, "readiness must remain false")

    admission_path = f"{PLAN_PATH_V1}.admission_model"
    admission = _closed(
        _expect_object(fields["admission_model"], admission_path),
        _PLAN_ADMISSION_FIELDS_V1,
        admission_path,
    )
    if (
        _expect_str(admission.get("authority_effect"), f"{admission_path}.authority_effect")
        != "NONE"
    ):
        _reject("SOURCE_PROMOTION", admission_path, "admission cannot grant authority")

    floor_path = f"{PLAN_PATH_V1}.requirements_floor"
    floor = _closed(
        _expect_object(fields["requirements_floor"], floor_path),
        _PLAN_REQUIREMENTS_FLOOR_FIELDS_V1,
        floor_path,
    )
    if _expect_bool(floor.get("manifest_complete"), f"{floor_path}.manifest_complete"):
        _reject("SOURCE_PROMOTION", floor_path, "requirements floor must remain incomplete")

    baseline_path = f"{PLAN_PATH_V1}.baseline_verdict"
    baseline = _closed(
        _expect_object(fields["baseline_verdict"], baseline_path),
        _PLAN_BASELINE_FIELDS_V1,
        baseline_path,
    )
    closed_gate_count_path = f"{baseline_path}.closed_value_movement_gates"
    if _expect_int(baseline.get("closed_value_movement_gates"), closed_gate_count_path) != 0:
        _reject("SOURCE_PROMOTION", closed_gate_count_path, "zero VM gates must be closed")

    gates_path = f"{PLAN_PATH_V1}.value_movement_gates"
    for index, raw_gate in enumerate(_expect_list(fields["value_movement_gates"], gates_path)):
        gate_path = f"{gates_path}[{index}]"
        gate = _closed(_expect_object(raw_gate, gate_path), _PLAN_VM_GATE_FIELDS_V1, gate_path)
        status_path = f"{gate_path}.status"
        if _expect_str(gate.get("status"), status_path) not in _PLAN_ALLOWED_VM_STATUSES_V1:
            _reject("SOURCE_PROMOTION", status_path, "VM gate status is not an allowed open status")

    release_gate_path = f"{PLAN_PATH_V1}.release_gate"
    release_gate = _closed(
        _expect_object(fields["release_gate"], release_gate_path),
        _PLAN_RELEASE_GATE_FIELDS_V1,
        release_gate_path,
    )
    claim_path = f"{release_gate_path}.whole_value_movement_claim"
    if (
        _expect_str(release_gate.get("whole_value_movement_claim"), claim_path)
        != _PLAN_FORBIDDEN_VALUE_CLAIM_V1
    ):
        _reject("SOURCE_PROMOTION", claim_path, "whole value-movement claim must remain forbidden")


def _parse_o005_closure_v1(fields: dict[str, object]) -> None:
    """Keep O-005's incomplete, non-VM closure scope explicit at the boundary."""

    obligations_path = f"{PLAN_PATH_V1}.next_obligations"
    obligation_index, obligation = _plan_record_v1(
        _expect_list(fields["next_obligations"], obligations_path),
        obligations_path,
        "obligation_id",
        _PLAN_O005_ID_V1,
    )
    obligation_path = f"{obligations_path}[{obligation_index}]"
    _closed(obligation, _PLAN_O005_FIELDS_V1, obligation_path)
    for field in ("phase", "priority"):
        if _expect_str(obligation.get(field), f"{obligation_path}.{field}") != "P1":
            _reject("SOURCE_OBLIGATION", f"{obligation_path}.{field}", "O-005 must remain P1")
    closes_path = f"{obligation_path}.closes"
    closes = tuple(
        _expect_str(value, f"{closes_path}[{index}]")
        for index, value in enumerate(_expect_list(obligation.get("closes"), closes_path))
    )
    for index, close in enumerate(closes):
        if close.startswith("VM-"):
            _reject("SOURCE_PROMOTION", f"{closes_path}[{index}]", "O-005 cannot close a VM gate")
    if closes != _PLAN_O005_CLOSES_V1:
        _reject("SOURCE_OBLIGATION", closes_path, "O-005 closure scope drift")

    gaps_path = f"{PLAN_PATH_V1}.gap_registry"
    gap_index, gap = _plan_record_v1(
        _expect_list(fields["gap_registry"], gaps_path),
        gaps_path,
        "gap_id",
        _PLAN_O005_CLOSES_V1[0],
    )
    gap_path = f"{gaps_path}[{gap_index}]"
    _closed(gap, _PLAN_GAP_FIELDS_V1, gap_path)
    if _expect_str(gap.get("owner_obligation"), f"{gap_path}.owner_obligation") != _PLAN_O005_ID_V1:
        _reject("SOURCE_OBLIGATION", gap_path, "O-005 gap owner drift")
    if _expect_str(gap.get("status"), f"{gap_path}.status") != _PLAN_OPEN_GAP_STATUS_V1:
        _reject("SOURCE_PROMOTION", f"{gap_path}.status", "O-005 gap must remain OPEN")


def _require_plan_semantic_commitment_v1(document: dict[str, object]) -> None:
    actual = hashlib.sha256(canonical_json_bytes_v1(document)).hexdigest()
    if actual != PLAN_CANONICAL_SHA256_V1:
        _reject("PLAN_SEMANTIC_COMMITMENT", PLAN_PATH_V1, "canonical Plan V2 semantics drift")


def _parse_plan_v1(
    raw_document: bytes,
) -> tuple[tuple[SimpleSourceV1, ...], dict[str, object], bytes]:
    """Parse the claim-bearing Plan from one immutable byte snapshot only."""

    fields = _closed(
        decode_json_object_v1(raw_document, PLAN_PATH_V1), _PLAN_ROOT_FIELDS, PLAN_PATH_V1
    )
    if _expect_str(fields["schema"], f"{PLAN_PATH_V1}.schema") != "zenodex/whole-program-plan/v2.1":
        _reject("SOURCE_SCHEMA", PLAN_PATH_V1, "Plan V2 schema drift")
    if (
        _expect_str(fields["status"], f"{PLAN_PATH_V1}.status")
        != "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION"
    ):
        _reject("SOURCE_STATUS", PLAN_PATH_V1, "Plan V2 status drift")
    _parse_plan_claim_ceiling_v1(fields)
    _parse_o005_closure_v1(fields)
    _require_plan_semantic_commitment_v1(fields)

    policies = _source_rows_v1(
        _expect_list(
            fields["unresolved_semantic_decisions"], f"{PLAN_PATH_V1}.unresolved_semantic_decisions"
        ),
        _UP_FIELDS,
        "decision_id",
        "UP-",
        PLAN_PATH_V1,
        "unresolved_semantic_decisions",
    )
    if tuple(row.requirement_id for row in policies) != _sequence("UP-", 2, 20):
        _reject("SOURCE_ID_SEQUENCE", PLAN_PATH_V1, "UP IDs must be UP-01 through UP-20")
    floor = _closed(
        _expect_object(fields["requirements_floor"], f"{PLAN_PATH_V1}.requirements_floor"),
        _REQUIREMENTS_FLOOR_FIELDS,
        f"{PLAN_PATH_V1}.requirements_floor",
    )
    anchors = _expect_object(fields["semantic_anchors"], f"{PLAN_PATH_V1}.semantic_anchors")
    return policies, floor, _canonical_object_bytes_v1(anchors, f"{PLAN_PATH_V1}.semantic_anchors")


def _parse_manifest_v1(
    document: dict[str, object],
) -> tuple[
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
    tuple[tuple[str, str, bytes], ...],
]:
    fields = _closed(document, _MANIFEST_ROOT_FIELDS, MANIFEST_PATH_V1)
    if (
        _expect_str(fields["schema"], f"{MANIFEST_PATH_V1}.schema")
        != "zenodex/m6-capability-manifest/v1"
    ):
        _reject("SOURCE_SCHEMA", MANIFEST_PATH_V1, "manifest schema drift")
    for name in ("manifest_complete", "release_eligible", "production_promotion"):
        if _expect_bool(fields[name], f"{MANIFEST_PATH_V1}.{name}"):
            _reject("SOURCE_PROMOTION", f"{MANIFEST_PATH_V1}.{name}", "must remain false")
    lanes = _expect_list(fields["lanes"], f"{MANIFEST_PATH_V1}.lanes")
    if len(lanes) != 12:
        _reject("SOURCE_COUNT", f"{MANIFEST_PATH_V1}.lanes", "must contain 12 lanes")
    pairs: list[tuple[str, str, str]] = []
    for lane_index, raw_lane in enumerate(lanes):
        path = f"{MANIFEST_PATH_V1}.lanes[{lane_index}]"
        lane = _closed(_expect_object(raw_lane, path), _LANE_FIELDS, path)
        lane_id = _expect_str(lane["lane_id"], f"{path}.lane_id")
        disposition = _expect_str(lane["disposition"], f"{path}.disposition")
        capabilities = _expect_list(lane["capabilities"], f"{path}.capabilities")
        for capability_index, raw_capability in enumerate(capabilities):
            capability_id = _expect_str(raw_capability, f"{path}.capabilities[{capability_index}]")
            pairs.append((lane_id, capability_id, disposition))
    if (
        len(pairs) != 103
        or len({(lane_id, capability_id) for lane_id, capability_id, _ in pairs}) != 103
    ):
        _reject(
            "SOURCE_COUNT", MANIFEST_PATH_V1, "must have 103 unique lane-qualified capabilities"
        )
    routes = tuple(
        _expect_str(route, f"{MANIFEST_PATH_V1}.required_cross_lane_routes[{index}]")
        for index, route in enumerate(
            _expect_list(
                fields["required_cross_lane_routes"],
                f"{MANIFEST_PATH_V1}.required_cross_lane_routes",
            )
        )
    )
    if len(routes) != 4 or len(routes) != len(set(routes)):
        _reject(
            "SOURCE_COUNT",
            f"{MANIFEST_PATH_V1}.required_cross_lane_routes",
            "must have four unique routes",
        )
    exclusions: list[tuple[str, str, bytes]] = []
    for index, raw_exclusion in enumerate(
        _expect_list(fields["explicit_exclusions"], f"{MANIFEST_PATH_V1}.explicit_exclusions")
    ):
        path = f"{MANIFEST_PATH_V1}.explicit_exclusions[{index}]"
        exclusion = _closed(_expect_object(raw_exclusion, path), _EXCLUSION_FIELDS, path)
        exclusions.append(
            (
                _expect_str(exclusion["capability"], f"{path}.capability"),
                _expect_str(exclusion["disposition"], f"{path}.disposition"),
                _canonical_object_bytes_v1(exclusion, path),
            )
        )
    if len(exclusions) != 4 or len({capability for capability, _, _ in exclusions}) != 4:
        _reject(
            "SOURCE_COUNT",
            f"{MANIFEST_PATH_V1}.explicit_exclusions",
            "must have four unique exclusions",
        )
    return tuple(pairs), routes, tuple(exclusions)


def _validate_plan_closure_v1(
    floor: dict[str, object],
    workflows: tuple[WorkflowSourceV1, ...],
    expansions: tuple[SimpleSourceV1, ...],
    findings: tuple[SimpleSourceV1, ...],
    policies: tuple[SimpleSourceV1, ...],
) -> None:
    actual_counts = {
        "workflow_count": len(workflows),
        "scenario_count": sum(len(workflow.scenarios) for workflow in workflows),
        "required_expansion_count": len(expansions),
        "confirmed_finding_count": len(findings),
        "unresolved_policy_count": len(policies),
    }
    for name, expected in actual_counts.items():
        if _expect_int(floor[name], f"{PLAN_PATH_V1}.requirements_floor.{name}") != expected:
            _reject("PLAN_CLOSURE_COUNT", name, "Plan V2 count does not bind source rows")
    if _expect_bool(
        floor["manifest_complete"], f"{PLAN_PATH_V1}.requirements_floor.manifest_complete"
    ):
        _reject("PLAN_PROMOTION", PLAN_PATH_V1, "requirements floor must remain incomplete")
    rse_ids = tuple(
        _expect_str(value, f"{PLAN_PATH_V1}.requirements_floor.required_expansion_ids")
        for value in _expect_list(
            floor["required_expansion_ids"],
            f"{PLAN_PATH_V1}.requirements_floor.required_expansion_ids",
        )
    )
    if rse_ids != tuple(row.requirement_id for row in expansions):
        _reject("PLAN_CLOSURE_IDS", PLAN_PATH_V1, "required expansion IDs drift")
    planned_findings = _expect_list(
        floor["confirmed_findings"], f"{PLAN_PATH_V1}.requirements_floor.confirmed_findings"
    )
    expected_findings = tuple(
        (
            row.requirement_id,
            _expect_str(
                _decoded_canonical_object_v1(row.fields_bytes)["status"],
                f"{row.requirement_id}.status",
            ),
        )
        for row in findings
    )
    observed_findings: list[tuple[str, str]] = []
    for index, raw_finding in enumerate(planned_findings):
        path = f"{PLAN_PATH_V1}.requirements_floor.confirmed_findings[{index}]"
        finding = _closed(
            _expect_object(raw_finding, path), frozenset({"finding_id", "status"}), path
        )
        observed_findings.append(
            (
                _expect_str(finding["finding_id"], f"{path}.finding_id"),
                _expect_str(finding["status"], f"{path}.status"),
            )
        )
    if tuple(observed_findings) != expected_findings:
        _reject(
            "PLAN_CLOSURE_FINDINGS", PLAN_PATH_V1, "Plan V2 does not adopt exact CE IDs/statuses"
        )


def parse_sources_v1(snapshot: SourceSnapshotV1) -> SourceBundleV1:
    """Bind exact bytes, then parse each source in a pure deterministic core."""

    documents = _snapshot_documents_v1(snapshot)
    workflows, invariants, links = _parse_atdd_v1(
        decode_json_object_v1(documents[ATDD_PATH_V1], ATDD_PATH_V1)
    )
    expansions, findings = _parse_luna_v1(
        decode_json_object_v1(documents[LUNA_PATH_V1], LUNA_PATH_V1)
    )
    policies, floor, anchors = _parse_plan_v1(documents[PLAN_PATH_V1])
    pairs, routes, exclusions = _parse_manifest_v1(
        decode_json_object_v1(documents[MANIFEST_PATH_V1], MANIFEST_PATH_V1)
    )
    _validate_plan_closure_v1(floor, workflows, expansions, findings, policies)
    invariant_ids = {row.requirement_id for row in invariants}
    for finding in findings:
        dangling = sorted(set(finding.invariant_ids) - invariant_ids)
        if dangling:
            _reject("DANGLING_CE_INVARIANT", finding.requirement_id, str(dangling))
    return SourceBundleV1(
        workflows,
        invariants,
        expansions,
        findings,
        policies,
        pairs,
        routes,
        exclusions,
        anchors,
        links,
    )


def _target_specs_v1(sources: SourceBundleV1) -> tuple[TargetSpecV1, ...]:
    targets: list[TargetSpecV1] = []
    for lane_id, capability_id, lane_disposition in sources.capability_pairs:
        targets.append(
            TargetSpecV1(
                f"lane_capability:{lane_id}:{capability_id}",
                TargetTypeV1.LANE_CAPABILITY,
                lane_id,
                capability_id,
                None,
                None,
                None,
                None,
                lane_disposition,
                None,
            )
        )
    for route_id in sources.routes:
        targets.append(
            TargetSpecV1(
                f"required_route:{route_id}",
                TargetTypeV1.REQUIRED_ROUTE,
                None,
                None,
                route_id,
                None,
                None,
                None,
                None,
                None,
            )
        )
    for exclusion_id, disposition, fields_bytes in sources.exclusions:
        targets.append(
            TargetSpecV1(
                f"exclusion:{exclusion_id}",
                TargetTypeV1.EXCLUSION,
                None,
                None,
                None,
                exclusion_id,
                disposition,
                None,
                None,
                fields_bytes,
            )
        )
    for invariant in sources.invariants:
        targets.append(
            TargetSpecV1(
                f"invariant:{invariant.requirement_id}",
                TargetTypeV1.INVARIANT,
                None,
                None,
                None,
                None,
                None,
                invariant.requirement_id,
                None,
                invariant.fields_bytes,
            )
        )
    for obligation_id, title, disposition in GLOBAL_OBLIGATION_SPECS_V1:
        fields: dict[str, object] = {
            "disposition": disposition,
            "id": obligation_id,
            "provenance": "LOCAL_EXPLICIT_DECISION_TABLE_RESEARCH_ONLY",
            "title": title,
        }
        targets.append(
            TargetSpecV1(
                target_id=f"global_obligation:{obligation_id}",
                target_type=TargetTypeV1.GLOBAL_OBLIGATION,
                lane_id=None,
                capability_id=None,
                route_id=None,
                exclusion_id=None,
                exclusion_disposition=None,
                invariant_id=None,
                lane_disposition=None,
                source_fields_bytes=_canonical_object_bytes_v1(
                    fields, f"global_obligation:{obligation_id}"
                ),
                global_obligation_id=obligation_id,
            )
        )
    for concept_id, title, disposition in MISSING_TARGET_CONCEPT_SPECS_V1:
        fields = {
            "disposition": disposition,
            "id": concept_id,
            "provenance": "LOCAL_EXPLICIT_DECISION_TABLE_RESEARCH_ONLY",
            "title": title,
        }
        targets.append(
            TargetSpecV1(
                target_id=f"missing_target_concept:{concept_id}",
                target_type=TargetTypeV1.MISSING_TARGET_CONCEPT,
                lane_id=None,
                capability_id=None,
                route_id=None,
                exclusion_id=None,
                exclusion_disposition=None,
                invariant_id=None,
                lane_disposition=None,
                source_fields_bytes=_canonical_object_bytes_v1(
                    fields, f"missing_target_concept:{concept_id}"
                ),
                missing_target_concept_id=concept_id,
            )
        )
    target_ids = tuple(target.target_id for target in targets)
    if len(target_ids) != len(set(target_ids)):
        _reject("TARGET_ID_COLLISION", "targets", "target identity must be globally unique")
    return tuple(targets)


def _edge_extensions_v1(requirement_id: str) -> tuple[EdgeV1, ...]:
    routes = (
        _table_value_v1(ROUTE_EDGE_SPECS_V1, requirement_id, "route")
        if any(candidate == requirement_id for candidate, _ in ROUTE_EDGE_SPECS_V1)
        else ()
    )
    exclusions = (
        _table_value_v1(EXCLUSION_EDGE_SPECS_V1, requirement_id, "exclusion")
        if any(candidate == requirement_id for candidate, _ in EXCLUSION_EDGE_SPECS_V1)
        else ()
    )
    return tuple(_route(route_id) for route_id in routes) + tuple(
        _exclusion(exclusion_id) for exclusion_id in exclusions
    )


def _cross_cutting_invariant_edges_v1(requirement_id: str) -> tuple[EdgeV1, ...]:
    invariant_ids = (
        _table_value_v1(
            CROSS_CUTTING_INVARIANT_SPECS_V1,
            requirement_id,
            "cross-cutting invariant",
        )
        if any(candidate == requirement_id for candidate, _ in CROSS_CUTTING_INVARIANT_SPECS_V1)
        else ()
    )
    return tuple(
        EdgeV1(RelationKindV1.CROSS_CUTTING_CONSTRAINT, f"invariant:{invariant_id}")
        for invariant_id in invariant_ids
    )


def _named_target_edges_v1(
    requirement_id: str,
    table: tuple[tuple[str, tuple[str, ...]], ...],
    relation_kind: RelationKindV1,
    target_prefix: str,
) -> tuple[EdgeV1, ...]:
    target_ids = (
        _table_value_v1(table, requirement_id, relation_kind.value)
        if any(candidate == requirement_id for candidate, _ in table)
        else ()
    )
    return tuple(EdgeV1(relation_kind, f"{target_prefix}:{target_id}") for target_id in target_ids)


def _global_obligation_edges_v1(requirement_id: str) -> tuple[EdgeV1, ...]:
    return _named_target_edges_v1(
        requirement_id,
        GLOBAL_OBLIGATION_EDGE_SPECS_V1,
        RelationKindV1.GLOBAL_OBLIGATION_SCOPE,
        "global_obligation",
    )


def _missing_target_edges_v1(requirement_id: str) -> tuple[EdgeV1, ...]:
    return _named_target_edges_v1(
        requirement_id,
        MISSING_TARGET_EDGE_SPECS_V1,
        RelationKindV1.MISSING_TARGET_CONCEPT_SCOPE,
        "missing_target_concept",
    )


def _ambiguous_scope_edges_v1(requirement_id: str) -> tuple[EdgeV1, ...]:
    capabilities = (
        _table_value_v1(
            AMBIGUOUS_CAPABILITY_SPECS_V1,
            requirement_id,
            "ambiguous capability",
        )
        if any(candidate == requirement_id for candidate, _ in AMBIGUOUS_CAPABILITY_SPECS_V1)
        else ()
    )
    routes = (
        _table_value_v1(AMBIGUOUS_ROUTE_SPECS_V1, requirement_id, "ambiguous route")
        if any(candidate == requirement_id for candidate, _ in AMBIGUOUS_ROUTE_SPECS_V1)
        else ()
    )
    return tuple(
        _cap(lane_id, capability_id, RelationKindV1.AMBIGUOUS_SOURCE_SCOPE)
        for lane_id, capability_id in capabilities
    ) + tuple(
        EdgeV1(RelationKindV1.AMBIGUOUS_SOURCE_SCOPE, f"required_route:{route_id}")
        for route_id in routes
    )


def _atom_v1(
    requirement_id: str,
    kind: str,
    status: str,
    parent_requirement_id: str | None,
    source_document: str,
    source_fields_bytes: bytes,
    edges: tuple[EdgeV1, ...],
) -> AtomV1:
    if not edges and kind != "INVARIANT":
        _reject(
            "VACUOUS_REQUIREMENT", requirement_id, "each atom requires a nonempty typed edge set"
        )
    canonical_edges = tuple(
        sorted(edges, key=lambda edge: (edge.relation_type.value, edge.target_id))
    )
    if len(canonical_edges) != len(set(canonical_edges)):
        _reject("DUPLICATE_EDGE", requirement_id, "edge set must be duplicate-free")
    return AtomV1(
        requirement_id,
        kind,
        status,
        parent_requirement_id,
        source_document,
        source_fields_bytes,
        canonical_edges,
    )


def _scenario_edges_v1(scenario: ScenarioSourceV1) -> tuple[EdgeV1, ...]:
    capabilities = _table_value_v1(
        BDD_CAPABILITY_SPECS_V1, scenario.requirement_id, "BDD capability"
    )
    capability_edges = _capability_edges_v1(capabilities, RelationKindV1.CAPABILITY_SEMANTIC_SCOPE)
    invariant_edges = tuple(
        EdgeV1(RelationKindV1.BDD_INVARIANT_REFERENCE, f"invariant:{invariant_id}")
        for invariant_id in scenario.invariant_ids
    )
    extensions = _edge_extensions_v1(scenario.requirement_id)
    global_edges = _global_obligation_edges_v1(scenario.requirement_id)
    missing_edges = _missing_target_edges_v1(scenario.requirement_id)
    ambiguous_edges = _ambiguous_scope_edges_v1(scenario.requirement_id)
    cross_cutting_edges = _cross_cutting_invariant_edges_v1(scenario.requirement_id)
    domain_targets = tuple(
        edge.target_id
        for edge in capability_edges + extensions + global_edges + missing_edges + ambiguous_edges
        if not edge.target_id.startswith("invariant:")
    )
    if scenario.requirement_id in {"BDD-065", "BDD-066", "BDD-067"}:
        if domain_targets != ("exclusion:zusd_emergency_shutdown",):
            _reject(
                "SHUTDOWN_EXCLUSION_SCOPE",
                scenario.requirement_id,
                "must map shutdown exclusion only",
            )
    elif not domain_targets:
        _reject(
            "SCENARIO_SEMANTIC_SCOPE",
            scenario.requirement_id,
            "non-shutdown scenario must map a typed semantic target",
        )
    return (
        capability_edges
        + invariant_edges
        + extensions
        + global_edges
        + missing_edges
        + ambiguous_edges
        + cross_cutting_edges
    )


def _ce_edges_v1(finding: SimpleSourceV1) -> tuple[EdgeV1, ...]:
    capability_edges = _capability_edges_v1(
        _table_value_v1(CE_CAPABILITY_SPECS_V1, finding.requirement_id, "CE capability"),
        RelationKindV1.CAPABILITY_SEMANTIC_SCOPE,
    )
    invariant_edges = tuple(
        EdgeV1(RelationKindV1.CE_INVARIANT_REFERENCE, f"invariant:{invariant_id}")
        for invariant_id in finding.invariant_ids
    )
    return (
        capability_edges
        + invariant_edges
        + _edge_extensions_v1(finding.requirement_id)
        + _global_obligation_edges_v1(finding.requirement_id)
        + _missing_target_edges_v1(finding.requirement_id)
    )


def _rse_edges_v1(expansion: SimpleSourceV1) -> tuple[EdgeV1, ...]:
    capability_edges = _capability_edges_v1(
        _table_value_v1(RSE_CAPABILITY_SPECS_V1, expansion.requirement_id, "RSE capability"),
        RelationKindV1.CAPABILITY_SEMANTIC_SCOPE,
    )
    invariant_edges = tuple(
        EdgeV1(RelationKindV1.RSE_INVARIANT_SCOPE, f"invariant:{invariant_id}")
        for invariant_id in _table_value_v1(
            RSE_INVARIANT_SPECS_V1, expansion.requirement_id, "RSE invariant"
        )
    )
    return (
        capability_edges
        + invariant_edges
        + _edge_extensions_v1(expansion.requirement_id)
        + _global_obligation_edges_v1(expansion.requirement_id)
        + _missing_target_edges_v1(expansion.requirement_id)
    )


def _build_atoms_v1(sources: SourceBundleV1) -> tuple[AtomV1, ...]:
    atoms: list[AtomV1] = []
    for workflow in sources.workflows:
        atoms.append(
            _atom_v1(
                workflow.requirement_id,
                "WORKFLOW",
                "NORMATIVE_INPUT_UNIMPLEMENTED",
                None,
                ATDD_PATH_V1,
                workflow.fields_bytes,
                _capability_edges_v1(
                    _table_value_v1(
                        WORKFLOW_CAPABILITY_SPECS_V1,
                        workflow.requirement_id,
                        "workflow capability",
                    ),
                    RelationKindV1.CAPABILITY_SEMANTIC_SCOPE,
                )
                + _edge_extensions_v1(workflow.requirement_id)
                + _cross_cutting_invariant_edges_v1(workflow.requirement_id)
                + _ambiguous_scope_edges_v1(workflow.requirement_id)
                + _global_obligation_edges_v1(workflow.requirement_id)
                + _missing_target_edges_v1(workflow.requirement_id),
            )
        )
    for workflow in sources.workflows:
        for scenario in workflow.scenarios:
            atoms.append(
                _atom_v1(
                    scenario.requirement_id,
                    "BDD",
                    "NORMATIVE_INPUT_UNIMPLEMENTED",
                    workflow.requirement_id,
                    ATDD_PATH_V1,
                    scenario.fields_bytes,
                    _scenario_edges_v1(scenario),
                )
            )
    for invariant in sources.invariants:
        atoms.append(
            _atom_v1(
                invariant.requirement_id,
                "INVARIANT",
                "NORMATIVE_INPUT_UNIMPLEMENTED",
                None,
                ATDD_PATH_V1,
                invariant.fields_bytes,
                (),
            )
        )
    for expansion in sources.expansions:
        atoms.append(
            _atom_v1(
                expansion.requirement_id,
                "REQUIRED_SPEC_EXPANSION",
                "REQUIRED_EXPANSION_UNRESOLVED",
                None,
                LUNA_PATH_V1,
                expansion.fields_bytes,
                _rse_edges_v1(expansion),
            )
        )
    for finding in sources.findings:
        atoms.append(
            _atom_v1(
                finding.requirement_id,
                "CONFIRMED_FINDING",
                "ADVISORY_FINDING_REQUIRES_LOCAL_CLOSURE",
                None,
                LUNA_PATH_V1,
                finding.fields_bytes,
                _ce_edges_v1(finding),
            )
        )
    for policy in sources.policies:
        atoms.append(
            _atom_v1(
                policy.requirement_id,
                "UNRESOLVED_POLICY",
                "UNRESOLVED_POLICY_NOT_SELECTABLE",
                None,
                PLAN_PATH_V1,
                policy.fields_bytes,
                _capability_edges_v1(
                    _table_value_v1(UP_CAPABILITY_SPECS_V1, policy.requirement_id, "UP capability"),
                    RelationKindV1.CAPABILITY_POLICY_SCOPE,
                )
                + _edge_extensions_v1(policy.requirement_id),
            )
        )
    if len(atoms) != 152:
        _reject("ATOM_COUNT", "rows", "expected exactly 152 requirement atoms")
    atom_ids = tuple(atom.requirement_id for atom in atoms)
    if len(atom_ids) != len(set(atom_ids)):
        _reject("DUPLICATE_REQUIREMENT_ID", "rows", "atom IDs must be unique")
    return tuple(atoms)


def _validate_edge_targets_v1(atoms: tuple[AtomV1, ...], targets: tuple[TargetSpecV1, ...]) -> None:
    target_by_id = {target.target_id: target for target in targets}
    if len(target_by_id) != len(targets):
        _reject("TARGET_ID_COLLISION", "targets", "duplicate target ID")
    inbound: dict[str, list[EdgeV1]] = {target.target_id: [] for target in targets}
    for atom in atoms:
        for edge in atom.edges:
            target = target_by_id.get(edge.target_id)
            if target is None:
                _reject("UNKNOWN_TARGET", atom.requirement_id, edge.target_id)
            expected_types = _RELATION_TARGET_TYPES.get(edge.relation_type)
            if expected_types is None or target.target_type not in expected_types:
                _reject("RELATION_TARGET_TYPE", atom.requirement_id, edge.target_id)
            inbound[edge.target_id].append(edge)
    invariant_atoms = {atom.requirement_id: atom for atom in atoms if atom.kind == "INVARIANT"}
    for target in targets:
        if (
            target.target_type
            in {
                TargetTypeV1.GLOBAL_OBLIGATION,
                TargetTypeV1.MISSING_TARGET_CONCEPT,
            }
            and not inbound[target.target_id]
        ):
            _reject(
                "DECLARED_TARGET_WITHOUT_INBOUND",
                target.target_id,
                "declared global or missing target requires an exact source-row edge",
            )
        if target.target_type != TargetTypeV1.INVARIANT or target.invariant_id is None:
            continue
        inbound_relations = {edge.relation_type for edge in inbound[target.target_id]}
        if not inbound_relations & {
            RelationKindV1.BDD_INVARIANT_REFERENCE,
            RelationKindV1.CE_INVARIANT_REFERENCE,
            RelationKindV1.RSE_INVARIANT_SCOPE,
        }:
            _reject(
                "INVARIANT_INBOUND_COVERAGE",
                target.target_id,
                "requires BDD, RSE, or CE inbound edge",
            )
        source_atom = invariant_atoms.get(target.invariant_id)
        if source_atom is None or source_atom.edges:
            _reject(
                "INVARIANT_CAPABILITY_SCOPE",
                target.target_id,
                "invariant rows must not manufacture capability coverage",
            )


def build_requirements_registry_v1(snapshot: SourceSnapshotV1) -> RegistryV1:
    """Construct all 152 atoms and their exact inverse target universe."""

    sources = parse_sources_v1(snapshot)
    targets = _target_specs_v1(sources)
    atoms = _build_atoms_v1(sources)
    _validate_edge_targets_v1(atoms, targets)
    return RegistryV1(atoms, targets, sources.semantic_anchors_bytes, sources.m6_historical_links)


def _inbound_edges_v1(atoms: tuple[AtomV1, ...]) -> dict[str, tuple[tuple[str, str], ...]]:
    collected: dict[str, list[tuple[str, str]]] = {}
    for atom in atoms:
        for edge in atom.edges:
            collected.setdefault(edge.target_id, []).append(
                (edge.relation_type.value, atom.requirement_id)
            )
    return {target_id: tuple(sorted(edges)) for target_id, edges in collected.items()}


_SEMANTIC_SOURCE_KINDS_V1: Final = frozenset(
    {"WORKFLOW", "BDD", "REQUIRED_SPEC_EXPANSION", "CONFIRMED_FINDING"}
)


def _semantic_origin_kinds_v1(
    inbound: tuple[tuple[str, str], ...], atom_kind_by_id: dict[str, str]
) -> frozenset[str]:
    return frozenset(
        atom_kind_by_id[requirement_id]
        for relation, requirement_id in inbound
        if relation == RelationKindV1.CAPABILITY_SEMANTIC_SCOPE.value
        and atom_kind_by_id.get(requirement_id) in _SEMANTIC_SOURCE_KINDS_V1
    )


def _target_status_v1(
    target: TargetSpecV1,
    inbound: tuple[tuple[str, str], ...],
    atom_kind_by_id: dict[str, str],
) -> str:
    if target.target_type == TargetTypeV1.LANE_CAPABILITY:
        if target.lane_disposition == "DISABLED_PENDING_COMPLETE_PROFILE":
            return "DISABLED_PENDING_COMPLETE_PROFILE"
        origin_kinds = _semantic_origin_kinds_v1(inbound, atom_kind_by_id)
        has_ambiguous_scope = any(relation == "AMBIGUOUS_SOURCE_SCOPE" for relation, _ in inbound)
        if has_ambiguous_scope and not origin_kinds:
            return "AMBIGUOUS_SOURCE_SCOPE_GAP"
        if "BDD" in origin_kinds:
            return "ENABLED_BDD_DIRECT_REQUIREMENT_SCOPE_UNRESOLVED"
        if origin_kinds == {"WORKFLOW"}:
            return "ENABLED_WORKFLOW_ONLY_REQUIREMENT_SCOPE_UNRESOLVED"
        if origin_kinds == {"REQUIRED_SPEC_EXPANSION"}:
            return "ENABLED_RSE_ONLY_SEMANTIC_GAP"
        if origin_kinds == {"CONFIRMED_FINDING", "REQUIRED_SPEC_EXPANSION"}:
            return "ENABLED_CE_AND_RSE_ONLY_SEMANTIC_GAP"
        if origin_kinds:
            return "ENABLED_MULTI_SOURCE_REQUIREMENT_SCOPE_UNRESOLVED"
        if any(relation == "CAPABILITY_POLICY_SCOPE" for relation, _ in inbound):
            return "POLICY_ONLY_SEMANTIC_GAP"
        return "UNMAPPED_SEMANTIC_GAP"
    if target.target_type == TargetTypeV1.REQUIRED_ROUTE:
        return "REQUIRED_ROUTE_UNRESOLVED"
    if target.target_type == TargetTypeV1.EXCLUSION:
        return "EXCLUSION_NOT_SELECTABLE"
    if target.target_type == TargetTypeV1.INVARIANT:
        return "NORMATIVE_INVARIANT_UNIMPLEMENTED"
    if target.target_type == TargetTypeV1.GLOBAL_OBLIGATION:
        return "GLOBAL_OBLIGATION_UNIMPLEMENTED"
    if target.target_type == TargetTypeV1.MISSING_TARGET_CONCEPT:
        return "MISSING_FROM_PROVISIONAL_CAPABILITY_MANIFEST"
    _reject("INTERNAL_TARGET_TYPE", target.target_id, "unknown target type")


def _render_targets_v1(
    atoms: tuple[AtomV1, ...], targets: tuple[TargetSpecV1, ...]
) -> list[dict[str, object]]:
    inbound_by_target = _inbound_edges_v1(atoms)
    atom_kind_by_id = {atom.requirement_id: atom.kind for atom in atoms}
    rendered: list[dict[str, object]] = []
    for target in targets:
        inbound = inbound_by_target.get(target.target_id, ())
        rendered.append(
            {
                "capability_id": target.capability_id,
                "exclusion_disposition": target.exclusion_disposition,
                "exclusion_id": target.exclusion_id,
                "global_obligation_id": target.global_obligation_id,
                "inbound_edges": [
                    {"relation_type": relation_type, "requirement_id": requirement_id}
                    for relation_type, requirement_id in inbound
                ],
                "invariant_id": target.invariant_id,
                "lane_disposition": target.lane_disposition,
                "lane_id": target.lane_id,
                "missing_target_concept_id": target.missing_target_concept_id,
                "route_id": target.route_id,
                "source_fields": (
                    _decoded_canonical_object_v1(target.source_fields_bytes)
                    if target.source_fields_bytes is not None
                    else None
                ),
                "status": _target_status_v1(target, inbound, atom_kind_by_id),
                "target_id": target.target_id,
                "target_type": target.target_type.value,
            }
        )
    return rendered


def _structural_counts_v1(
    atoms: tuple[AtomV1, ...], targets: tuple[TargetSpecV1, ...]
) -> dict[str, int]:
    kinds = {
        kind: 0
        for kind in (
            "WORKFLOW",
            "BDD",
            "INVARIANT",
            "REQUIRED_SPEC_EXPANSION",
            "CONFIRMED_FINDING",
            "UNRESOLVED_POLICY",
        )
    }
    for atom in atoms:
        if atom.kind not in kinds:
            _reject("INTERNAL_ATOM_KIND", atom.requirement_id, atom.kind)
        kinds[atom.kind] += 1
    target_kinds = {kind: 0 for kind in TargetTypeV1}
    for target in targets:
        if target.target_type not in target_kinds:
            _reject("INTERNAL_TARGET_TYPE", target.target_id, target.target_type.value)
        target_kinds[target.target_type] += 1
    inbound = _inbound_edges_v1(atoms)
    atom_kind_by_id = {atom.requirement_id: atom.kind for atom in atoms}
    semantic_origins_by_target: dict[str, frozenset[str]] = {
        target.target_id: _semantic_origin_kinds_v1(
            inbound.get(target.target_id, ()), atom_kind_by_id
        )
        for target in targets
        if target.target_type == TargetTypeV1.LANE_CAPABILITY
    }
    enabled_targets = {
        target.target_id
        for target in targets
        if target.target_type == TargetTypeV1.LANE_CAPABILITY
        and target.lane_disposition != "DISABLED_PENDING_COMPLETE_PROFILE"
    }
    direct_semantic_scope = {
        target_id for target_id, origins in semantic_origins_by_target.items() if origins
    }
    ambiguous_scope = {
        target.target_id
        for target in targets
        if target.target_type == TargetTypeV1.LANE_CAPABILITY
        and any(
            relation == RelationKindV1.AMBIGUOUS_SOURCE_SCOPE.value
            for relation, _ in inbound.get(target.target_id, ())
        )
    }
    cross_cutting_scope = {
        target.target_id
        for target in targets
        if target.target_type == TargetTypeV1.LANE_CAPABILITY
        and any(
            relation == RelationKindV1.CROSS_CUTTING_CONSTRAINT.value
            for relation, _ in inbound.get(target.target_id, ())
        )
    }
    disabled_targets = {
        target.target_id
        for target in targets
        if target.target_type == TargetTypeV1.LANE_CAPABILITY
        and target.lane_disposition == "DISABLED_PENDING_COMPLETE_PROFILE"
    }
    enabled_direct_scope = direct_semantic_scope & enabled_targets
    wf_or_bdd = {
        target_id
        for target_id, origins in semantic_origins_by_target.items()
        if target_id in enabled_targets and origins & {"WORKFLOW", "BDD"}
    }
    bdd_direct = {
        target_id
        for target_id, origins in semantic_origins_by_target.items()
        if target_id in enabled_targets and "BDD" in origins
    }
    rse_only = {
        target_id
        for target_id, origins in semantic_origins_by_target.items()
        if target_id in enabled_targets and origins == {"REQUIRED_SPEC_EXPANSION"}
    }
    ce_and_rse_only = {
        target_id
        for target_id, origins in semantic_origins_by_target.items()
        if target_id in enabled_targets
        and origins == {"CONFIRMED_FINDING", "REQUIRED_SPEC_EXPANSION"}
    }
    workflow_only = {
        target_id
        for target_id, origins in semantic_origins_by_target.items()
        if target_id in enabled_targets and origins == {"WORKFLOW"}
    }
    return {
        "bdd_count": kinds["BDD"],
        "capability_count": target_kinds[TargetTypeV1.LANE_CAPABILITY],
        "ce_count": kinds["CONFIRMED_FINDING"],
        "ambiguous_capability_scope_count": len(ambiguous_scope),
        "enabled_capability_bdd_direct_scope_count": len(bdd_direct),
        "enabled_direct_capability_ce_and_rse_only_scope_count": len(ce_and_rse_only),
        "enabled_direct_capability_rse_only_scope_count": len(rse_only),
        "enabled_direct_capability_semantic_scope_count": len(enabled_direct_scope),
        "enabled_direct_capability_wf_or_bdd_scope_count": len(wf_or_bdd),
        "enabled_direct_capability_workflow_only_scope_count": len(workflow_only),
        "cross_cutting_capability_scope_count": len(cross_cutting_scope),
        "disabled_capability_direct_scope_count": len(direct_semantic_scope & disabled_targets),
        "disabled_capability_target_count": len(disabled_targets),
        "exclusion_count": target_kinds[TargetTypeV1.EXCLUSION],
        "global_obligation_count": target_kinds[TargetTypeV1.GLOBAL_OBLIGATION],
        "invariant_count": kinds["INVARIANT"],
        "missing_target_concept_count": target_kinds[TargetTypeV1.MISSING_TARGET_CONCEPT],
        "requirement_count": len(atoms),
        "route_count": target_kinds[TargetTypeV1.REQUIRED_ROUTE],
        "rse_count": kinds["REQUIRED_SPEC_EXPANSION"],
        "target_count": len(targets),
        "up_count": kinds["UNRESOLVED_POLICY"],
        "workflow_count": kinds["WORKFLOW"],
    }


def render_registry_markdown_v1(registry: RegistryV1) -> str:
    """Render a deterministic, conservative human view of one registry value."""

    artifact = registry.to_json()
    counts = _expect_object(artifact["structural_counts"], "registry.structural_counts")
    pins = _expect_list(artifact["source_pins"], "registry.source_pins")
    lines = [
        "# ZenoDEX M6 Normative Requirements V1",
        "",
        "Status: research-only structural requirements registry. It grants no production or value-moving authority.",
        "",
        "## Immutable source subject",
        "",
        f"- Source commit: `{SOURCE_SUBJECT_COMMIT_V1}`",
        f"- Source tree: `{SOURCE_SUBJECT_TREE_V1}`",
        "- Artifact Git commit binding: none. This avoids a self-referential generated-artifact HEAD.",
        "",
        "## Structural inventory",
        "",
        f"- Requirement atoms: {counts['requirement_count']} (18 WF, 81 BDD, 14 INV, 11 RSE, 8 CE, 20 UP)",
        f"- Lane-qualified capability targets: {counts['capability_count']}",
        f"- Enabled capability targets with direct semantic scope: {counts['enabled_direct_capability_semantic_scope_count']}",
        f"- Ambiguous capability targets: {counts['ambiguous_capability_scope_count']}",
        f"- Cross-cutting capability targets: {counts['cross_cutting_capability_scope_count']}",
        f"- Disabled capability targets: {counts['disabled_capability_target_count']}",
        f"- Disabled capability targets with direct semantic scope: {counts['disabled_capability_direct_scope_count']}",
        f"- Enabled targets directly scoped by a workflow or BDD row: {counts['enabled_direct_capability_wf_or_bdd_scope_count']}",
        f"- Enabled targets scoped by a BDD row: {counts['enabled_capability_bdd_direct_scope_count']}",
        f"- Enabled direct RSE-only gaps: {counts['enabled_direct_capability_rse_only_scope_count']}",
        f"- Enabled direct CE-plus-RSE-only gaps: {counts['enabled_direct_capability_ce_and_rse_only_scope_count']}",
        f"- Enabled direct workflow-only targets: {counts['enabled_direct_capability_workflow_only_scope_count']}",
        f"- Global obligations: {counts['global_obligation_count']}; missing concepts: {counts['missing_target_concept_count']}",
        f"- Required routes: {counts['route_count']}; exclusions: {counts['exclusion_count']}; invariant targets: {counts['invariant_count']}",
        "- These partitions describe requirements-scope classification. They do not establish feature implementation or semantic closure.",
        "",
        "## Source-gate posture",
        "",
    ]
    for raw_pin in pins:
        pin = _expect_object(raw_pin, "registry.source_pins[]")
        lines.append(
            f"- `{_expect_str(pin['path'], 'pin.path')}`: `{_expect_str(pin['source_gate_status'], 'pin.source_gate_status')}`"
        )
    lines.extend(
        [
            "",
            "## Claim ceiling",
            "",
            "- `manifest_complete=false`",
            "- `requirements_closed=false`",
            "- `release_eligible=false`",
            "- `production_promotion=false`",
            "- `production_authority=NONE`",
            "- `settlement_authority=NONE`",
            "- `source_row_census_complete=true`",
            "- `semantic_target_inventory_complete=false`",
            "- `structural_mapping_complete=false`",
            "- `semantic_closure_complete=false`",
            "- `value_movement_claim_allowed=false`",
            "",
            "The registry records exact donor rows, typed inverse targets, and unresolved gaps. It is neither proof nor implementation evidence.",
            "",
        ]
    )
    return "\n".join(lines)


def _finding_v1(code: str, path: str, detail: str) -> CheckFindingV1:
    return CheckFindingV1(
        _sanitized_finding_text_v1(code, 64),
        _sanitized_finding_text_v1(path, MAX_FINDING_PATH_CHARS_V1),
        _sanitized_finding_text_v1(detail, MAX_FINDING_DETAIL_CHARS_V1),
    )


def _relation_kind_v1(value: str, path: str) -> RelationKindV1:
    try:
        return RelationKindV1(value)
    except ValueError:
        _reject("UNKNOWN_RELATION_KIND", path, "relation kind is outside the closed algebra")


def _target_type_v1(value: str, path: str) -> TargetTypeV1:
    try:
        return TargetTypeV1(value)
    except ValueError:
        _reject("UNKNOWN_TARGET_TYPE", path, "target type is outside the closed algebra")


def _artifact_shape_v1(value: dict[str, object]) -> None:
    _closed(value, _ARTIFACT_ROOT_FIELDS, "artifact")
    _expect_str(value["schema"], "artifact.schema")
    _expect_str(value["generator_command"], "artifact.generator_command")
    _expect_str(value["registry_root"], "artifact.registry_root")
    for name in (
        "manifest_complete",
        "production_promotion",
        "release_eligible",
        "requirements_closed",
        "source_row_census_complete",
        "semantic_target_inventory_complete",
        "structural_mapping_complete",
        "semantic_capability_coverage_complete",
        "semantic_closure_complete",
        "value_movement_claim_allowed",
    ):
        _expect_bool(value[name], f"artifact.{name}")
    _expect_str(value["production_authority"], "artifact.production_authority")
    _expect_str(value["settlement_authority"], "artifact.settlement_authority")
    _expect_str(value["status"], "artifact.status")
    _expect_list(value["nonclaims"], "artifact.nonclaims")
    subject = _closed(
        _expect_object(value["subject"], "artifact.subject"), _SUBJECT_FIELDS, "artifact.subject"
    )
    for name in _SUBJECT_FIELDS:
        _expect_str(subject[name], f"artifact.subject.{name}")
    counts = _closed(
        _expect_object(value["structural_counts"], "artifact.structural_counts"),
        _COUNT_FIELDS,
        "artifact.structural_counts",
    )
    for name in _COUNT_FIELDS:
        _expect_int(counts[name], f"artifact.structural_counts.{name}")
    for index, raw_pin in enumerate(_expect_list(value["source_pins"], "artifact.source_pins")):
        pin_path = f"artifact.source_pins[{index}]"
        pin = _closed(_expect_object(raw_pin, pin_path), _SOURCE_PIN_FIELDS, pin_path)
        for name in _SOURCE_PIN_FIELDS:
            _expect_str(pin[name], f"{pin_path}.{name}")
    seen_requirement_ids: set[str] = set()
    for index, raw_row in enumerate(_expect_list(value["rows"], "artifact.rows")):
        row_path = f"artifact.rows[{index}]"
        row = _closed(_expect_object(raw_row, row_path), _ROW_FIELDS, row_path)
        requirement_id = _expect_str(row["requirement_id"], f"{row_path}.requirement_id")
        if requirement_id in seen_requirement_ids:
            _reject("DUPLICATE_REQUIREMENT_ID", row_path, requirement_id)
        seen_requirement_ids.add(requirement_id)
        _expect_str(row["kind"], f"{row_path}.kind")
        if row["parent_requirement_id"] is not None:
            _expect_str(row["parent_requirement_id"], f"{row_path}.parent_requirement_id")
        _expect_str(row["source_document"], f"{row_path}.source_document")
        _expect_object(row["source_fields"], f"{row_path}.source_fields")
        _expect_str(row["status"], f"{row_path}.status")
        seen_edges: set[tuple[str, str]] = set()
        ordered_edges: list[tuple[str, str]] = []
        for edge_index, raw_edge in enumerate(_expect_list(row["edges"], f"{row_path}.edges")):
            edge_path = f"{row_path}.edges[{edge_index}]"
            edge = _closed(_expect_object(raw_edge, edge_path), _EDGE_FIELDS, edge_path)
            relation_type = _expect_str(edge["relation_type"], f"{edge_path}.relation_type")
            _relation_kind_v1(relation_type, f"{edge_path}.relation_type")
            target_id = _expect_str(edge["target_id"], f"{edge_path}.target_id")
            if (relation_type, target_id) in seen_edges:
                _reject("DUPLICATE_EDGE", edge_path, "duplicate relation/target pair")
            seen_edges.add((relation_type, target_id))
            ordered_edges.append((relation_type, target_id))
        if ordered_edges != sorted(ordered_edges):
            _reject(
                "NONCANONICAL_EDGE_ORDER",
                f"{row_path}.edges",
                "outbound edges must use canonical relation/target order",
            )
    seen_target_ids: set[str] = set()
    for index, raw_target in enumerate(_expect_list(value["targets"], "artifact.targets")):
        target_path = f"artifact.targets[{index}]"
        target = _closed(_expect_object(raw_target, target_path), _TARGET_FIELDS, target_path)
        target_id = _expect_str(target["target_id"], f"{target_path}.target_id")
        if target_id in seen_target_ids:
            _reject("DUPLICATE_TARGET_ID", target_path, target_id)
        seen_target_ids.add(target_id)
        target_type = _expect_str(target["target_type"], f"{target_path}.target_type")
        _target_type_v1(target_type, f"{target_path}.target_type")
        _expect_str(target["status"], f"{target_path}.status")
        for name in (
            "capability_id",
            "exclusion_disposition",
            "exclusion_id",
            "global_obligation_id",
            "invariant_id",
            "lane_disposition",
            "lane_id",
            "missing_target_concept_id",
            "route_id",
        ):
            if target[name] is not None:
                _expect_str(target[name], f"{target_path}.{name}")
        if target["source_fields"] is not None:
            _expect_object(target["source_fields"], f"{target_path}.source_fields")
        seen_inbound: set[tuple[str, str]] = set()
        ordered_inbound: list[tuple[str, str]] = []
        for edge_index, raw_edge in enumerate(
            _expect_list(target["inbound_edges"], f"{target_path}.inbound_edges")
        ):
            edge_path = f"{target_path}.inbound_edges[{edge_index}]"
            edge = _closed(_expect_object(raw_edge, edge_path), _INBOUND_EDGE_FIELDS, edge_path)
            pair = (
                _expect_str(edge["relation_type"], f"{edge_path}.relation_type"),
                _expect_str(edge["requirement_id"], f"{edge_path}.requirement_id"),
            )
            _relation_kind_v1(pair[0], f"{edge_path}.relation_type")
            if pair in seen_inbound:
                _reject("DUPLICATE_INVERSE_EDGE", edge_path, "duplicate inverse edge")
            seen_inbound.add(pair)
            ordered_inbound.append(pair)
        if ordered_inbound != sorted(ordered_inbound):
            _reject(
                "NONCANONICAL_INVERSE_EDGE_ORDER",
                f"{target_path}.inbound_edges",
                "inverse edges must use canonical relation/requirement order",
            )


def _row_index_v1(rows: list[object], path: str) -> dict[str, dict[str, object]]:
    indexed: dict[str, dict[str, object]] = {}
    for index, raw_row in enumerate(rows):
        row = _expect_object(raw_row, f"{path}[{index}]")
        requirement_id = _expect_str(row["requirement_id"], f"{path}[{index}].requirement_id")
        indexed[requirement_id] = row
    return indexed


def _target_index_v1(targets: list[object], path: str) -> dict[str, dict[str, object]]:
    indexed: dict[str, dict[str, object]] = {}
    for index, raw_target in enumerate(targets):
        target = _expect_object(raw_target, f"{path}[{index}]")
        target_id = _expect_str(target["target_id"], f"{path}[{index}].target_id")
        indexed[target_id] = target
    return indexed


def _check_actual_edge_types_v1(actual: dict[str, object]) -> CheckFindingV1 | None:
    targets = _target_index_v1(
        _expect_list(actual["targets"], "artifact.targets"), "artifact.targets"
    )
    for row_index, raw_row in enumerate(_expect_list(actual["rows"], "artifact.rows")):
        row = _expect_object(raw_row, f"artifact.rows[{row_index}]")
        requirement_id = _expect_str(
            row["requirement_id"], f"artifact.rows[{row_index}].requirement_id"
        )
        kind = _expect_str(row["kind"], f"artifact.rows[{row_index}].kind")
        edges = _expect_list(row["edges"], f"artifact.rows[{row_index}].edges")
        if not edges:
            if kind == "INVARIANT":
                continue
            return _finding_v1("VACUOUS_EDGE", requirement_id, "requirement has no typed edge")
        if kind == "INVARIANT":
            return _finding_v1(
                "INVARIANT_EDGE_FORBIDDEN",
                requirement_id,
                "invariant rows cannot manufacture feature coverage",
            )
        for edge_index, raw_edge in enumerate(edges):
            edge = _expect_object(raw_edge, f"artifact.rows[{row_index}].edges[{edge_index}]")
            relation_type = _expect_str(edge["relation_type"], "artifact.edge.relation_type")
            target_id = _expect_str(edge["target_id"], "artifact.edge.target_id")
            target = targets.get(target_id)
            if target is None:
                return _finding_v1("UNKNOWN_TARGET", requirement_id, target_id)
            target_type = _expect_str(target["target_type"], f"target.{target_id}.target_type")
            relation_kind = _relation_kind_v1(relation_type, "artifact.edge.relation_type")
            target_kind = _target_type_v1(target_type, f"target.{target_id}.target_type")
            expected_types = _RELATION_TARGET_TYPES.get(relation_kind)
            if expected_types is None or target_kind not in expected_types:
                return _finding_v1("RELATION_TARGET_TYPE", requirement_id, target_id)
    return None


def _inverse_edges_v1(rows: list[object]) -> dict[str, tuple[tuple[str, str], ...]]:
    collected: dict[str, list[tuple[str, str]]] = {}
    for row_index, raw_row in enumerate(rows):
        row = _expect_object(raw_row, f"artifact.rows[{row_index}]")
        requirement_id = _expect_str(
            row["requirement_id"], f"artifact.rows[{row_index}].requirement_id"
        )
        for edge_index, raw_edge in enumerate(
            _expect_list(row["edges"], f"artifact.rows[{row_index}].edges")
        ):
            edge = _expect_object(raw_edge, f"artifact.rows[{row_index}].edges[{edge_index}]")
            relation_type = _expect_str(edge["relation_type"], "artifact.edge.relation_type")
            target_id = _expect_str(edge["target_id"], "artifact.edge.target_id")
            collected.setdefault(target_id, []).append((relation_type, requirement_id))
    return {target_id: tuple(sorted(edges)) for target_id, edges in collected.items()}


def _first_difference_v1(
    actual: dict[str, object], expected: dict[str, object]
) -> CheckFindingV1 | None:
    for name in (
        "manifest_complete",
        "production_authority",
        "production_promotion",
        "release_eligible",
        "requirements_closed",
        "semantic_capability_coverage_complete",
        "semantic_closure_complete",
        "settlement_authority",
        "source_row_census_complete",
        "semantic_target_inventory_complete",
        "structural_mapping_complete",
        "value_movement_claim_allowed",
    ):
        if actual[name] != expected[name]:
            return _finding_v1("PROMOTION_MUTATION", f"artifact.{name}", "claim ceiling drift")
    actual_pins = _expect_list(actual["source_pins"], "artifact.source_pins")
    expected_pins = _expect_list(expected["source_pins"], "expected.source_pins")
    if actual_pins != expected_pins:
        for index, raw_pin in enumerate(actual_pins):
            pin = _expect_object(raw_pin, f"artifact.source_pins[{index}]")
            if (
                pin.get("source_gate_status")
                in {
                    "CURRENT_GATE_PASS_NORMATIVE",
                    "PROVED",
                    "IMPLEMENTED",
                }
                and index >= 2
            ):
                return _finding_v1(
                    "STALE_DONOR_PROMOTION",
                    f"artifact.source_pins[{index}]",
                    "stale donor elevated",
                )
        return _finding_v1("SOURCE_PIN_DRIFT", "artifact.source_pins", "pins must exactly replay")
    if actual["subject"] != expected["subject"]:
        return _finding_v1(
            "STALE_SUBJECT", "artifact.subject", "source subject or no-self-reference binding drift"
        )
    if actual["structural_counts"] != expected["structural_counts"]:
        return _finding_v1(
            "STRUCTURAL_COUNT_MISMATCH", "artifact.structural_counts", "counts must be recomputed"
        )
    actual_rows = _expect_list(actual["rows"], "artifact.rows")
    expected_rows = _expect_list(expected["rows"], "expected.rows")
    actual_by_id = _row_index_v1(actual_rows, "artifact.rows")
    expected_by_id = _row_index_v1(expected_rows, "expected.rows")
    if tuple(actual_by_id) != tuple(expected_by_id):
        return _finding_v1(
            "SOURCE_ROW_SET_MISMATCH", "artifact.rows", "missing or extra source atom"
        )
    for requirement_id, expected_row in expected_by_id.items():
        actual_row = actual_by_id[requirement_id]
        if actual_row["parent_requirement_id"] != expected_row["parent_requirement_id"]:
            return _finding_v1(
                "BDD_PARENT_MISMATCH", requirement_id, "parent must exactly replay ATDD"
            )
        if (
            actual_row["source_document"] != expected_row["source_document"]
            or actual_row["source_fields"] != expected_row["source_fields"]
        ):
            return _finding_v1(
                "SOURCE_FIELDS_MISMATCH", requirement_id, "source fields must exactly replay"
            )
        if actual_row["status"] in _PROHIBITED_STATUSES:
            return _finding_v1(
                "PROHIBITED_EVIDENCE_STATUS", requirement_id, "row asserts unavailable evidence"
            )
        if actual_row["status"] != expected_row["status"]:
            return _finding_v1("ROW_STATUS_MISMATCH", requirement_id, "typed research status drift")
        if actual_row["edges"] != expected_row["edges"]:
            code = (
                "BDD_SCENARIO_EDGE_MISMATCH"
                if requirement_id.startswith("BDD-")
                else "ROW_EDGES_MISMATCH"
            )
            return _finding_v1(
                code, requirement_id, "direct mapping must exactly replay core table"
            )
    actual_targets = _expect_list(actual["targets"], "artifact.targets")
    expected_targets = _expect_list(expected["targets"], "expected.targets")
    actual_target_ids = tuple(
        _expect_str(
            _expect_object(target, "artifact.target")["target_id"], "artifact.target.target_id"
        )
        for target in actual_targets
    )
    expected_target_ids = tuple(
        _expect_str(
            _expect_object(target, "expected.target")["target_id"], "expected.target.target_id"
        )
        for target in expected_targets
    )
    if actual_target_ids != expected_target_ids:
        return _finding_v1(
            "TARGET_ID_SET_MISMATCH", "artifact.targets", "typed inverse target inventory drift"
        )
    actual_inverse = _inverse_edges_v1(actual_rows)
    for index, raw_target in enumerate(actual_targets):
        target = _expect_object(raw_target, f"artifact.targets[{index}]")
        target_id = _expect_str(target["target_id"], f"artifact.targets[{index}].target_id")
        rendered_inverse = tuple(
            (
                _expect_str(
                    _expect_object(edge, "artifact.inbound")["relation_type"],
                    "artifact.inbound.relation_type",
                ),
                _expect_str(
                    _expect_object(edge, "artifact.inbound")["requirement_id"],
                    "artifact.inbound.requirement_id",
                ),
            )
            for edge in _expect_list(
                target["inbound_edges"], f"artifact.targets[{index}].inbound_edges"
            )
        )
        if rendered_inverse != actual_inverse.get(target_id, ()):
            return _finding_v1(
                "INVERSE_EDGE_MISMATCH", target_id, "inverse edges must derive from source rows"
            )
        expected_target = _expect_object(expected_targets[index], f"expected.targets[{index}]")
        if target != expected_target:
            return _finding_v1(
                "TARGET_MAPPING_MISMATCH",
                target_id,
                "target identity, status, or inverse mapping drift",
            )
    if actual["semantic_anchors"] != expected["semantic_anchors"]:
        return _finding_v1(
            "SEMANTIC_ANCHOR_MISMATCH",
            "artifact.semantic_anchors",
            "anchors must exactly replay Plan V2",
        )
    if actual["m6_historical_links"] != expected["m6_historical_links"]:
        return _finding_v1(
            "HISTORICAL_LINK_MISMATCH",
            "artifact.m6_historical_links",
            "M6-R links are provenance only",
        )
    if actual["registry_root"] != expected["registry_root"]:
        return _finding_v1(
            "REGISTRY_ROOT_MISMATCH",
            "artifact.registry_root",
            "root must bind canonical unsigned body",
        )
    if actual != expected:
        return _finding_v1(
            "ARTIFACT_REGENERATION_MISMATCH", "artifact", "artifact differs from exact regeneration"
        )
    return None


def check_requirements_registry_v1(
    raw_artifact: bytes, snapshot: SourceSnapshotV1
) -> CheckReportV1:
    """Recompute every accepted fact from immutable source bytes and static tables."""

    artifact_sha256 = ""
    try:
        if type(raw_artifact) is not bytes:
            _reject("JSON_BYTES_TYPE", "artifact", "must have exact bytes type")
        if len(raw_artifact) > MAX_JSON_BYTES_V1:
            _reject("JSON_BYTE_LIMIT", "artifact", "JSON byte ceiling exceeded")
        artifact_sha256 = hashlib.sha256(raw_artifact).hexdigest()
        actual = decode_json_object_v1(raw_artifact, "artifact")
        _artifact_shape_v1(actual)
        if canonical_json_bytes_v1(actual) != raw_artifact:
            _reject("NONCANONICAL_ARTIFACT", "artifact", "bytes must use canonical JSON encoding")
        expected = build_requirements_registry_v1(snapshot).to_json()
        expected_root = _expect_str(expected["registry_root"], "expected.registry_root")
        edge_finding = _check_actual_edge_types_v1(actual)
        if edge_finding is not None:
            return CheckReportV1((edge_finding,), artifact_sha256, expected_root, True)
        difference = _first_difference_v1(actual, expected)
        if difference is not None:
            return CheckReportV1((difference,), artifact_sha256, expected_root, True)
        return CheckReportV1((), artifact_sha256, expected_root, True)
    except RequirementsRejectV1 as exc:
        return CheckReportV1(
            (_finding_v1(exc.code, exc.path, exc.detail),),
            artifact_sha256,
            None,
            False,
        )
