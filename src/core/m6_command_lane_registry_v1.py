"""Pure, research-only M6 command-to-lane registry.

This module binds the closed M6 safe-mount command vocabulary to the stable
GlobalSettlementABI V1 lane names and governed route names.  It is a
structural inventory.  It neither selects a release nor authorizes settlement,
value movement, migration, or publication.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final, NoReturn, cast

from src.state.canonical import canonical_json_bytes

from .global_settlement_types_v1 import LaneIdV1
from .m6_safe_mount_types_v1 import (
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    GlobalCommandKindV1,
)

SCHEMA_V1: Final = "zenodex/m6-command-lane-registry/v1"
CHECK_SCHEMA_V1: Final = "zenodex/m6-command-lane-registry-check/v1"
REGISTRY_DOMAIN_V1: Final = "zenodex/m6-command-lane-registry-root/v1"
DECISION_DOMAIN_V1: Final = "zenodex/m6-command-lane-decision-root/v1"
EXPECTED_DECISION_ROOT_V1: Final = (
    "13a1d6a240991823d73af010cdc593234c3fde4652602d2b672ca1ff1a8a9d93"
)
MAX_OWNED_JSON_DEPTH_V1: Final = 16
MAX_OWNED_JSON_NODES_V1: Final = 4096

ACTIVE_PLAN_COMMIT_V1: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ACTIVE_PLAN_REGISTRY_PATH_V1: Final = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
ACTIVE_PLAN_REGISTRY_SHA256_V1: Final = (
    "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"
)
ADMISSION_RECEIPT_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
ADMISSION_RECEIPT_ARTIFACT_SHA256_V1: Final = (
    "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
)
ADMISSION_RECEIPT_PAYLOAD_SHA256_V1: Final = (
    "fdc2d69fe530e0098d66f4a9d5d6297296cdf896b0fb97beb0f959ae054be86d"
)
CAPABILITY_MANIFEST_SHA256_V1: Final = (
    "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95"
)
REQUIREMENTS_ARTIFACT_SHA256_V1: Final = (
    "29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f"
)
REQUIREMENTS_REGISTRY_ROOT_V1: Final = (
    "971e7c5e277697d0bc833a8016f2d47bbbd17c3b4e5c0762990d13772808a3e6"
)
SAFE_MOUNT_SOURCE_COMMIT_V1: Final = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
SAFE_MOUNT_SOURCE_PATH_V1: Final = "src/core/m6_safe_mount_types_v1.py"

GOVERNED_ROUTE_IDS_V1: Final = (
    "fee_funded_zdex_purchase_and_burn",
    "zusd_liquidation_settlement",
    "perps_epoch_settlement",
    "strategy_triggered_spot_swap",
)
EXPECTED_LANE_DISPOSITIONS_V1: Final = tuple(
    (lane.value, "DISABLED_PENDING_COMPLETE_PROFILE")
    if lane is LaneIdV1.EXTERNAL_CUSTODY
    else (lane.value, "REQUIRED_UNRESOLVED")
    for lane in LaneIdV1
)


def _is_lower_hex_v1(value: str, length: int) -> bool:
    return len(value) == length and all(character in "0123456789abcdef" for character in value)


@dataclass(frozen=True)
class CommandLaneRegistryRejectV1(ValueError):
    """Stable rejection at the registry's pure trust boundary."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


class TargetKindV1(str, Enum):
    LANE = "LANE"
    GOVERNED_ROUTE = "GOVERNED_ROUTE"


class ResearchMappingStatusV1(str, Enum):
    SOURCE_RESEARCH_ENABLED_UNRESOLVED_NO_RELEASE = "SOURCE_RESEARCH_ENABLED_UNRESOLVED_NO_RELEASE"
    SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE = (
        "SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE"
    )
    SOURCE_RESEARCH_DISABLED_NO_RELEASE = "SOURCE_RESEARCH_DISABLED_NO_RELEASE"


class SemanticConflictCodeV1(str, Enum):
    SOURCE_RESEARCH_ENABLED_TARGET_DISABLED = "SOURCE_RESEARCH_ENABLED_TARGET_DISABLED"


@dataclass(frozen=True)
class CommandLaneDecisionV1:
    command: GlobalCommandKindV1
    target_kind: TargetKindV1
    target_id: str
    status: ResearchMappingStatusV1

    def __post_init__(self) -> None:
        if type(self.command) is not GlobalCommandKindV1:
            _reject("COMMAND_TYPE", "decision.command", "must be an exact GlobalCommandKindV1")
        if type(self.target_kind) is not TargetKindV1:
            _reject("TARGET_KIND_TYPE", "decision.target_kind", "must be an exact TargetKindV1")
        if type(self.target_id) is not str or not self.target_id:
            _reject("TARGET_ID_TYPE", "decision.target_id", "must be a nonempty exact str")
        if type(self.status) is not ResearchMappingStatusV1:
            _reject("MAPPING_STATUS_TYPE", "decision.status", "must be an exact status enum")
        if self.target_kind is TargetKindV1.LANE and self.target_id not in _lane_ids_v1():
            _reject("UNKNOWN_LANE_TARGET", "decision.target_id", self.target_id)
        if (
            self.target_kind is TargetKindV1.GOVERNED_ROUTE
            and self.target_id not in GOVERNED_ROUTE_IDS_V1
        ):
            _reject("UNKNOWN_ROUTE_TARGET", "decision.target_id", self.target_id)

    def to_json(self) -> dict[str, str]:
        return {
            "command": self.command.value,
            "status": self.status.value,
            "target_id": self.target_id,
            "target_kind": self.target_kind.value,
        }


@dataclass(frozen=True)
class SemanticConflictV1:
    command: GlobalCommandKindV1
    code: SemanticConflictCodeV1
    target_id: str
    target_kind: TargetKindV1
    source_status: ResearchMappingStatusV1
    target_disposition: str
    resolution: str

    def to_json(self) -> dict[str, str]:
        return {
            "code": self.code.value,
            "command": self.command.value,
            "resolution": self.resolution,
            "source_status": self.source_status.value,
            "target_disposition": self.target_disposition,
            "target_id": self.target_id,
            "target_kind": self.target_kind.value,
        }


@dataclass(frozen=True)
class TargetCoverageGapV1:
    target_kind: TargetKindV1
    target_id: str
    code: str

    def to_json(self) -> dict[str, str]:
        return {
            "code": self.code,
            "target_id": self.target_id,
            "target_kind": self.target_kind.value,
        }


@dataclass(frozen=True)
class CommandLaneSourceSnapshotV1:
    captured_head: str
    rechecked_head: str
    safe_mount_source_tree: str
    safe_mount_source_blob: str
    active_plan_registry_sha256: str
    admission_receipt_artifact_sha256: str
    capability_manifest_sha256: str
    requirements_artifact_sha256: str
    requirements_registry_root: str
    lane_dispositions: tuple[tuple[str, str], ...]
    route_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        for name, length in (
            ("captured_head", 40),
            ("rechecked_head", 40),
            ("safe_mount_source_tree", 40),
            ("safe_mount_source_blob", 40),
            ("active_plan_registry_sha256", 64),
            ("admission_receipt_artifact_sha256", 64),
            ("capability_manifest_sha256", 64),
            ("requirements_artifact_sha256", 64),
            ("requirements_registry_root", 64),
        ):
            value = getattr(self, name)
            if type(value) is not str or not _is_lower_hex_v1(value, length):
                _reject("SOURCE_BINDING_TYPE", name, f"must be {length} lowercase hex characters")
        if self.captured_head != self.rechecked_head:
            _reject("HEAD_CHANGED_DURING_CAPTURE", "HEAD", "Git HEAD changed during source capture")
        if type(self.lane_dispositions) is not tuple:
            _reject("TARGET_DISPOSITION_TYPE", "lane_dispositions", "must be an exact tuple")
        for index, row in enumerate(self.lane_dispositions):
            if (
                type(row) is not tuple
                or len(row) != 2
                or type(row[0]) is not str
                or type(row[1]) is not str
            ):
                _reject(
                    "TARGET_DISPOSITION_TYPE",
                    f"lane_dispositions[{index}]",
                    "must be an exact pair of strings",
                )
        if self.lane_dispositions != EXPECTED_LANE_DISPOSITIONS_V1:
            _reject(
                "TARGET_DISPOSITION_DRIFT",
                "lane_dispositions",
                "stable lane disposition table drift",
            )
        if type(self.route_ids) is not tuple or any(
            type(route_id) is not str for route_id in self.route_ids
        ):
            _reject("ROUTE_SET_TYPE", "route_ids", "must be an exact tuple of strings")
        if self.route_ids != GOVERNED_ROUTE_IDS_V1:
            _reject("ROUTE_SET_DRIFT", "route_ids", "capability manifest route table drift")


@dataclass(frozen=True)
class RegistryCheckReportV1:
    artifact_sha256: str
    registry_root: str | None
    ok: bool
    findings: tuple[dict[str, str], ...]

    def to_json(self) -> dict[str, object]:
        return {
            "artifact_sha256": self.artifact_sha256,
            "findings": list(self.findings),
            "mounted": False,
            "ok": self.ok,
            "production_authority": "NONE",
            "registered_command_mapping_complete": self.ok,
            "registry_root": self.registry_root,
            "release_backed": False,
            "requirements_target_coverage_complete": False,
            "schema": CHECK_SCHEMA_V1,
            "semantic_launch_alignment_complete": False,
            "settlement_authority": "NONE",
            "value_movement_claim_allowed": False,
            "whole_economy_command_vocabulary_complete": False,
        }


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CommandLaneRegistryRejectV1(code, path, detail)


def _lane_ids_v1() -> tuple[str, ...]:
    return tuple(lane.value for lane in LaneIdV1)


def _decision(
    command: GlobalCommandKindV1,
    target_kind: TargetKindV1,
    target_id: str,
) -> CommandLaneDecisionV1:
    disabled = command in M6_RESEARCH_DISABLED_COMMANDS_V1
    external_conflict = (
        not disabled
        and target_kind is TargetKindV1.LANE
        and target_id == LaneIdV1.EXTERNAL_CUSTODY.value
    )
    status = (
        ResearchMappingStatusV1.SOURCE_RESEARCH_DISABLED_NO_RELEASE
        if disabled
        else ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE
        if external_conflict
        else ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_UNRESOLVED_NO_RELEASE
    )
    return CommandLaneDecisionV1(command, target_kind, target_id, status)


# This table is deliberately ordered by the source enum.  The core derives the
# command vocabulary from that enum and rejects any stale, duplicate, or omitted
# decision.  Route choices are governed names, never caller-selected releases.
DECISION_TABLE_V1: Final = (
    _decision(GlobalCommandKindV1.SPOT_SWAP, TargetKindV1.LANE, "SPOT_LIQUIDITY"),
    _decision(GlobalCommandKindV1.LP_ADD, TargetKindV1.LANE, "SPOT_LIQUIDITY"),
    _decision(GlobalCommandKindV1.LP_REMOVE, TargetKindV1.LANE, "SPOT_LIQUIDITY"),
    _decision(GlobalCommandKindV1.ZUSD_BORROW, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(GlobalCommandKindV1.ZUSD_REPAY, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(GlobalCommandKindV1.ZUSD_REDEEM, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(
        GlobalCommandKindV1.ZUSD_LIQUIDATE,
        TargetKindV1.GOVERNED_ROUTE,
        "zusd_liquidation_settlement",
    ),
    _decision(GlobalCommandKindV1.STABILITY_POOL_DEPOSIT, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(GlobalCommandKindV1.STABILITY_POOL_WITHDRAW, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(GlobalCommandKindV1.ZUSD_REDISTRIBUTE, TargetKindV1.LANE, "ZUSD_MONETARY"),
    _decision(GlobalCommandKindV1.PERP_OPEN, TargetKindV1.LANE, "PERPS_MARKET"),
    _decision(GlobalCommandKindV1.PERP_CLOSE, TargetKindV1.LANE, "PERPS_MARKET"),
    _decision(
        GlobalCommandKindV1.PERP_FUNDING,
        TargetKindV1.GOVERNED_ROUTE,
        "perps_epoch_settlement",
    ),
    _decision(GlobalCommandKindV1.PERP_LIQUIDATE, TargetKindV1.LANE, "PERPS_MARKET"),
    _decision(GlobalCommandKindV1.ORACLE_SUBMIT, TargetKindV1.LANE, "ORACLE_MARKET"),
    _decision(GlobalCommandKindV1.ORACLE_DISPUTE, TargetKindV1.LANE, "ORACLE_MARKET"),
    _decision(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        TargetKindV1.GOVERNED_ROUTE,
        "fee_funded_zdex_purchase_and_burn",
    ),
    _decision(GlobalCommandKindV1.ZRPF_PROVER_REWARD, TargetKindV1.LANE, "PROOF_REWARDS"),
    _decision(GlobalCommandKindV1.SELLER_AUCTION_COMMIT, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.SELLER_AUCTION_REVEAL, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.SELLER_AUCTION_SETTLE, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.SELLER_AUCTION_EXPIRE, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.PRIVATE_SWAP_COMMIT, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.PRIVATE_SWAP_REVEAL, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.PRIVATE_SWAP_SETTLE, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.PRIVATE_SWAP_CANCEL, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE, TargetKindV1.LANE, "SEALED_AUCTION"),
    _decision(GlobalCommandKindV1.TAU_ESCROW_DEPOSIT, TargetKindV1.LANE, "EXTERNAL_CUSTODY"),
    _decision(GlobalCommandKindV1.TAU_WITHDRAWAL, TargetKindV1.LANE, "EXTERNAL_CUSTODY"),
    _decision(GlobalCommandKindV1.TAU_WITHDRAWAL_ACK, TargetKindV1.LANE, "EXTERNAL_CUSTODY"),
    _decision(GlobalCommandKindV1.FALLBACK_ACTIVATE, TargetKindV1.LANE, "GOVERNANCE_MIGRATION"),
    _decision(GlobalCommandKindV1.TAU_REJOIN, TargetKindV1.LANE, "GOVERNANCE_MIGRATION"),
)


def _validate_decision_table_v1(decisions: tuple[CommandLaneDecisionV1, ...]) -> None:
    if type(decisions) is not tuple:
        _reject("DECISION_TABLE_TYPE", "decisions", "must be an exact tuple")
    for index, decision in enumerate(decisions):
        if type(decision) is not CommandLaneDecisionV1:
            _reject(
                "DECISION_TYPE",
                f"decisions[{index}]",
                "must be an exact CommandLaneDecisionV1",
            )
    expected_commands = tuple(GlobalCommandKindV1)
    commands = tuple(decision.command for decision in decisions)
    if len(commands) != len(set(commands)):
        _reject("DUPLICATE_COMMAND", "decisions", "every source command must occur once")
    if set(commands) != set(expected_commands):
        _reject(
            "COMMAND_SET_DRIFT", "decisions", "decision commands differ from GlobalCommandKindV1"
        )
    if commands != expected_commands:
        _reject("NONCANONICAL_DECISION_ORDER", "decisions", "must follow GlobalCommandKindV1 order")
    for index, decision in enumerate(decisions):
        disabled = decision.command in M6_RESEARCH_DISABLED_COMMANDS_V1
        if (
            disabled
            and decision.status is not ResearchMappingStatusV1.SOURCE_RESEARCH_DISABLED_NO_RELEASE
        ):
            _reject(
                "DISABLED_TO_ACTIVE", f"decisions[{index}]", "disabled source command status drift"
            )
        if (
            not disabled
            and decision.status is ResearchMappingStatusV1.SOURCE_RESEARCH_DISABLED_NO_RELEASE
        ):
            _reject(
                "SOURCE_STATUS_DRIFT",
                f"decisions[{index}]",
                "enabled source command marked disabled",
            )
        if decision.target_id == LaneIdV1.EXTERNAL_CUSTODY.value:
            if (
                decision.status
                is not ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE
            ):
                _reject(
                    "EXTERNAL_CONFLICT_HIDDEN",
                    f"decisions[{index}]",
                    "external command must remain quarantined",
                )
        elif (
            decision.status
            is ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE
        ):
            _reject(
                "QUARANTINE_TARGET_DRIFT",
                f"decisions[{index}]",
                "quarantine is reserved for external conflict",
            )


def _owned_decision_table_v1(
    decisions: tuple[CommandLaneDecisionV1, ...],
) -> tuple[CommandLaneDecisionV1, ...]:
    _validate_decision_table_v1(decisions)
    return tuple(
        CommandLaneDecisionV1(
            command=decision.command,
            target_kind=decision.target_kind,
            target_id=decision.target_id,
            status=decision.status,
        )
        for decision in decisions
    )


def _semantic_conflicts_v1(
    decisions: tuple[CommandLaneDecisionV1, ...],
    lane_dispositions: tuple[tuple[str, str], ...],
) -> tuple[SemanticConflictV1, ...]:
    dispositions = dict(lane_dispositions)
    conflicts: list[SemanticConflictV1] = []
    for decision in decisions:
        if (
            decision.target_kind is TargetKindV1.LANE
            and decision.status
            is ResearchMappingStatusV1.SOURCE_RESEARCH_ENABLED_QUARANTINED_NO_RELEASE
        ):
            conflicts.append(
                SemanticConflictV1(
                    command=decision.command,
                    code=SemanticConflictCodeV1.SOURCE_RESEARCH_ENABLED_TARGET_DISABLED,
                    target_id=decision.target_id,
                    target_kind=decision.target_kind,
                    source_status=decision.status,
                    target_disposition=dispositions[decision.target_id],
                    resolution="QUARANTINED_NO_RELEASE",
                )
            )
    return tuple(conflicts)


def _coverage_gaps_v1(
    decisions: tuple[CommandLaneDecisionV1, ...], route_ids: tuple[str, ...]
) -> tuple[TargetCoverageGapV1, ...]:
    direct_lanes = {
        decision.target_id for decision in decisions if decision.target_kind is TargetKindV1.LANE
    }
    gaps = [
        TargetCoverageGapV1(TargetKindV1.LANE, lane_id, "NO_GLOBAL_COMMAND_VOCABULARY")
        for lane_id in _lane_ids_v1()
        if lane_id not in direct_lanes
    ]
    mapped_routes = {
        decision.target_id
        for decision in decisions
        if decision.target_kind is TargetKindV1.GOVERNED_ROUTE
    }
    gaps.extend(
        TargetCoverageGapV1(TargetKindV1.GOVERNED_ROUTE, route_id, "NO_GLOBAL_COMMAND_VOCABULARY")
        for route_id in route_ids
        if route_id not in mapped_routes
    )
    return tuple(gaps)


def decision_root_v1(decisions: tuple[CommandLaneDecisionV1, ...]) -> str:
    owned_decisions = _owned_decision_table_v1(decisions)
    payload = {
        "decisions": [decision.to_json() for decision in owned_decisions],
        "schema": SCHEMA_V1,
    }
    digest = hashlib.sha256(
        DECISION_DOMAIN_V1.encode("ascii") + b"\0" + canonical_json_bytes(payload)
    )
    root = digest.hexdigest()
    if root != EXPECTED_DECISION_ROOT_V1:
        _reject(
            "DECISION_ROOT_DRIFT",
            "decisions",
            "decision table differs from the independently reviewed root",
        )
    return root


def registry_root_v1(unsigned_artifact: dict[str, object]) -> str:
    if type(unsigned_artifact) is not dict:
        _reject(
            "REGISTRY_ROOT_INPUT",
            "unsigned_artifact",
            "must be an exact object",
        )
    owned_value = _snapshot_owned_json_v1(unsigned_artifact, "unsigned_artifact")
    if type(owned_value) is not dict:
        _reject("REGISTRY_ROOT_INPUT", "unsigned_artifact", "must be an exact object")
    owned = cast(dict[str, object], owned_value)
    if "registry_root" in owned:
        _reject(
            "REGISTRY_ROOT_INPUT",
            "unsigned_artifact",
            "must not contain registry_root",
        )
    digest = hashlib.sha256(
        REGISTRY_DOMAIN_V1.encode("ascii") + b"\0" + canonical_json_bytes(owned)
    )
    return digest.hexdigest()


def _source_pins_json_v1(snapshot: CommandLaneSourceSnapshotV1) -> dict[str, object]:
    return {
        "active_plan": {
            "active_registry_path": ACTIVE_PLAN_REGISTRY_PATH_V1,
            "active_registry_sha256": snapshot.active_plan_registry_sha256,
            "admission_receipt_path": ADMISSION_RECEIPT_PATH_V1,
            "admission_receipt_sha256": snapshot.admission_receipt_artifact_sha256,
            "admission_receipt_payload_sha256": ADMISSION_RECEIPT_PAYLOAD_SHA256_V1,
            "commit": ACTIVE_PLAN_COMMIT_V1,
        },
        "capability_manifest": {
            "path": "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
            "sha256": snapshot.capability_manifest_sha256,
        },
        "m6_safe_mount_types": {
            "commit": SAFE_MOUNT_SOURCE_COMMIT_V1,
            "git_blob": snapshot.safe_mount_source_blob,
            "git_tree": snapshot.safe_mount_source_tree,
            "path": SAFE_MOUNT_SOURCE_PATH_V1,
        },
        "normative_requirements": {
            "registry_root": snapshot.requirements_registry_root,
            "sha256": snapshot.requirements_artifact_sha256,
        },
    }


def _validate_source_pins_v1(snapshot: CommandLaneSourceSnapshotV1) -> None:
    if snapshot.active_plan_registry_sha256 != ACTIVE_PLAN_REGISTRY_SHA256_V1:
        _reject("ACTIVE_PLAN_REGISTRY_SHA_DRIFT", "snapshot", "active plan registry digest drift")
    if snapshot.admission_receipt_artifact_sha256 != ADMISSION_RECEIPT_ARTIFACT_SHA256_V1:
        _reject(
            "ADMISSION_RECEIPT_SHA_DRIFT",
            "snapshot",
            "plan admission receipt digest drift",
        )

    if snapshot.capability_manifest_sha256 != CAPABILITY_MANIFEST_SHA256_V1:
        _reject("CAPABILITY_MANIFEST_SHA_DRIFT", "snapshot", "capability manifest digest drift")
    if snapshot.requirements_artifact_sha256 != REQUIREMENTS_ARTIFACT_SHA256_V1:
        _reject("REQUIREMENTS_ARTIFACT_SHA_DRIFT", "snapshot", "requirements artifact digest drift")
    if snapshot.requirements_registry_root != REQUIREMENTS_REGISTRY_ROOT_V1:
        _reject("REQUIREMENTS_ROOT_DRIFT", "snapshot", "requirements registry root drift")


def _owned_source_snapshot_v1(snapshot: object) -> CommandLaneSourceSnapshotV1:
    if type(snapshot) is not CommandLaneSourceSnapshotV1:
        _reject(
            "SOURCE_SNAPSHOT_TYPE",
            "snapshot",
            "must be an exact CommandLaneSourceSnapshotV1",
        )
    exact = snapshot
    return CommandLaneSourceSnapshotV1(
        captured_head=exact.captured_head,
        rechecked_head=exact.rechecked_head,
        safe_mount_source_tree=exact.safe_mount_source_tree,
        safe_mount_source_blob=exact.safe_mount_source_blob,
        active_plan_registry_sha256=exact.active_plan_registry_sha256,
        admission_receipt_artifact_sha256=exact.admission_receipt_artifact_sha256,
        capability_manifest_sha256=exact.capability_manifest_sha256,
        requirements_artifact_sha256=exact.requirements_artifact_sha256,
        requirements_registry_root=exact.requirements_registry_root,
        lane_dispositions=exact.lane_dispositions,
        route_ids=exact.route_ids,
    )


def build_registry_artifact_v1(snapshot: CommandLaneSourceSnapshotV1) -> dict[str, object]:
    """Build the immutable registry artifact from already-acquired shell inputs."""

    owned_snapshot = _owned_source_snapshot_v1(snapshot)
    _validate_source_pins_v1(owned_snapshot)
    decisions = _owned_decision_table_v1(DECISION_TABLE_V1)
    decision_root = decision_root_v1(decisions)
    conflicts = _semantic_conflicts_v1(decisions, owned_snapshot.lane_dispositions)
    if len(conflicts) != 3:
        _reject(
            "EXTERNAL_CONFLICT_CARDINALITY",
            "semantic_conflicts",
            "expected three external command conflicts",
        )
    coverage_gaps = _coverage_gaps_v1(decisions, owned_snapshot.route_ids)
    unsigned: dict[str, object] = {
        "command_enum": [command.value for command in GlobalCommandKindV1],
        "decision_root": decision_root,
        "decisions": [decision.to_json() for decision in decisions],
        "generator_command": "python3 tools/build_m6_command_lane_registry_v1.py",
        "nonclaims": [
            "This structural registry grants no settlement, release, migration, publication, or value-moving authority.",
            "No decision selects ACTIVE_NEW or any module release.",
            "Structural completeness does not establish semantic launch alignment, release backing, mounting, or value-movement closure.",
            "External commands remain quarantined because the source research-enabled set conflicts with the disabled external capability lane.",
        ],
        "o006": {
            "authority": "NONE",
            "obligation_id": "O-006",
            "status": "STRUCTURAL_COMPLETE_RESEARCH_ONLY",
        },
        "mounted": False,
        "production_authority": "NONE",
        "registered_command_mapping_complete": True,
        "release_backed": False,
        "requirements_target_coverage_complete": False,
        "schema": SCHEMA_V1,
        "semantic_conflicts": [conflict.to_json() for conflict in conflicts],
        "semantic_launch_alignment_complete": False,
        "settlement_authority": "NONE",
        "source_pins": _source_pins_json_v1(owned_snapshot),
        "status": "RESEARCH_ONLY_STRUCTURAL_COMMAND_MAP",
        "target_coverage_gaps": [gap.to_json() for gap in coverage_gaps],
        "value_movement_claim_allowed": False,
        "whole_economy_command_vocabulary_complete": False,
        "vm_ledger_contribution": {
            "contributes_to": [],
            "gate_closures": [],
            "status": "INITIALIZED_NO_VM_GATE_PROMOTION",
        },
    }
    return {**unsigned, "registry_root": registry_root_v1(unsigned)}


def _snapshot_owned_json_node_v1(
    value: object,
    path: str,
    depth: int,
    remaining_nodes: int,
) -> tuple[object, int]:
    if depth > MAX_OWNED_JSON_DEPTH_V1:
        _reject("ARTIFACT_DEPTH", path, "maximum owned JSON depth exceeded")
    if remaining_nodes <= 0:
        _reject("ARTIFACT_NODE_COUNT", path, "maximum owned JSON node count exceeded")
    remaining = remaining_nodes - 1
    if value is None or type(value) in (bool, int, str):
        return value, remaining
    if type(value) is list:
        owned_items: list[object] = []
        for index, item in enumerate(value):
            owned_item, remaining = _snapshot_owned_json_node_v1(
                item, f"{path}[{index}]", depth + 1, remaining
            )
            owned_items.append(owned_item)
        return owned_items, remaining
    if type(value) is dict:
        owned: dict[str, object] = {}
        for key, item in value.items():
            if type(key) is not str:
                _reject("ARTIFACT_KEY_TYPE", path, "object keys must be exact strings")
            owned_item, remaining = _snapshot_owned_json_node_v1(
                item, f"{path}.{key}", depth + 1, remaining
            )
            owned[key] = owned_item
        return owned, remaining
    _reject("ARTIFACT_VALUE_TYPE", path, "must contain only exact JSON value types")


def _snapshot_owned_json_v1(value: object, path: str) -> object:
    """Copy exact bounded JSON values before equality can invoke hostile methods."""

    owned, _remaining = _snapshot_owned_json_node_v1(
        value,
        path,
        0,
        MAX_OWNED_JSON_NODES_V1,
    )
    return owned


def _validated_owned_artifact_v1(
    artifact: object,
    snapshot: CommandLaneSourceSnapshotV1,
) -> dict[str, object]:
    if type(artifact) is not dict:
        _reject("ARTIFACT_ROOT_TYPE", "artifact", "must be an exact object")
    owned_value = _snapshot_owned_json_v1(artifact, "artifact")
    if type(owned_value) is not dict:
        _reject("ARTIFACT_ROOT_TYPE", "artifact", "must be an exact object")
    owned = cast(dict[str, object], owned_value)
    expected = build_registry_artifact_v1(snapshot)
    if owned != expected:
        _reject(
            "ARTIFACT_BINDING_DRIFT", "artifact", "artifact differs from exact typed projection"
        )
    return owned


def validate_registry_artifact_v1(
    artifact: object,
    snapshot: CommandLaneSourceSnapshotV1,
) -> None:
    """Require one exact canonical projection of the typed decision table."""

    _validated_owned_artifact_v1(artifact, snapshot)


def check_registry_artifact_v1(
    artifact: object,
    raw_artifact: bytes,
    snapshot: CommandLaneSourceSnapshotV1,
) -> RegistryCheckReportV1:
    digest = ""
    try:
        if type(raw_artifact) is not bytes:
            _reject("RAW_ARTIFACT_TYPE", "raw_artifact", "must be exact bytes")
        digest = hashlib.sha256(raw_artifact).hexdigest()
        owned = _validated_owned_artifact_v1(artifact, snapshot)
        if canonical_json_bytes(owned) != raw_artifact:
            _reject(
                "RAW_ARTIFACT_BINDING_DRIFT",
                "raw_artifact",
                "raw bytes differ from the validated canonical object",
            )
    except CommandLaneRegistryRejectV1 as exc:
        return RegistryCheckReportV1(
            artifact_sha256=digest,
            registry_root=None,
            ok=False,
            findings=({"code": exc.code, "detail": exc.detail, "path": exc.path},),
        )
    root = owned.get("registry_root")
    return RegistryCheckReportV1(
        artifact_sha256=digest,
        registry_root=root if type(root) is str else None,
        ok=True,
        findings=(),
    )


__all__ = [
    "ACTIVE_PLAN_COMMIT_V1",
    "ACTIVE_PLAN_REGISTRY_PATH_V1",
    "ACTIVE_PLAN_REGISTRY_SHA256_V1",
    "ADMISSION_RECEIPT_ARTIFACT_SHA256_V1",
    "ADMISSION_RECEIPT_PATH_V1",
    "ADMISSION_RECEIPT_PAYLOAD_SHA256_V1",
    "CAPABILITY_MANIFEST_SHA256_V1",
    "CHECK_SCHEMA_V1",
    "CommandLaneDecisionV1",
    "CommandLaneRegistryRejectV1",
    "CommandLaneSourceSnapshotV1",
    "DECISION_TABLE_V1",
    "decision_root_v1",
    "EXPECTED_LANE_DISPOSITIONS_V1",
    "EXPECTED_DECISION_ROOT_V1",
    "GOVERNED_ROUTE_IDS_V1",
    "MAX_OWNED_JSON_NODES_V1",
    "REQUIREMENTS_ARTIFACT_SHA256_V1",
    "REQUIREMENTS_REGISTRY_ROOT_V1",
    "ResearchMappingStatusV1",
    "SAFE_MOUNT_SOURCE_COMMIT_V1",
    "SAFE_MOUNT_SOURCE_PATH_V1",
    "SCHEMA_V1",
    "SemanticConflictCodeV1",
    "TargetKindV1",
    "build_registry_artifact_v1",
    "check_registry_artifact_v1",
    "registry_root_v1",
    "validate_registry_artifact_v1",
]
