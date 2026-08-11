"""Proof-journal and verifier boundary for GlobalSettlementABI V1.

The verifier port is deliberately narrow: callers supply receipt bytes, while
the selected verifier must validate a succinct receipt against the exact root
image and canonical epoch journal.  This Python boundary does not implement a
RISC Zero verifier and therefore remains unmounted reference code.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING, Protocol

from .epoch_effect_composition_v1 import compose_asset_lane_epoch_effect_plans_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_CYCLE_BUDGET_V1,
    MAX_EPOCH_COMMANDS_V1,
    MAX_EPOCH_LEAF_OCCURRENCES_V1,
    MAX_JOURNAL_BYTES_V1,
    MAX_ROUTE_MODULES_V1,
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    _require_nonnegative_int,
    _require_positive_int,
    _require_root,
    _require_semantic_order_unique,
    _require_sorted_unique_tokens,
    _require_token,
    _require_tuple,
    canonical_global_bytes_v1,
    hash_global_v1,
)

if TYPE_CHECKING:
    from .route_composition_receipt_verification_v1 import VerifiedRouteCompositionV1


COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1 = "zenodex/command-aggregation-journal/v1"


@dataclass(frozen=True, slots=True)
class EconomicCommandOccurrenceV1:
    chain_id: str
    deployment_root: str
    height: int
    tx_index: int
    op_index: int
    command_kind: str
    route_release_id: str
    subject_id: str
    grant_root: str
    nonce: int
    profile_root: str
    pre_state_root: str
    consumed_object_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="occurrence chain id")
        _require_root(self.deployment_root, name="occurrence deployment root")
        _require_nonnegative_int(self.height, name="occurrence height")
        _require_nonnegative_int(self.tx_index, name="occurrence tx_index")
        _require_nonnegative_int(self.op_index, name="occurrence op_index")
        _require_token(self.command_kind, name="occurrence command kind")
        _require_root(self.route_release_id, name="occurrence route release id")
        _require_token(self.subject_id, name="occurrence subject id")
        _require_root(self.grant_root, name="occurrence grant root")
        _require_nonnegative_int(self.nonce, name="occurrence nonce")
        _require_root(self.profile_root, name="occurrence profile root")
        _require_root(self.pre_state_root, name="occurrence pre-state root")
        _require_sorted_unique_tokens(
            self.consumed_object_ids,
            name="occurrence consumed object ids",
        )

    @property
    def occurrence_id(self) -> str:
        return hash_global_v1("global-economic-command-occurrence-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "height": self.height,
            "tx_index": self.tx_index,
            "op_index": self.op_index,
            "command_kind": self.command_kind,
            "route_release_id": self.route_release_id,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
            "nonce": self.nonce,
            "profile_root": self.profile_root,
            "pre_state_root": self.pre_state_root,
            "consumed_object_ids": self.consumed_object_ids,
        }


@dataclass(frozen=True, slots=True)
class LaneModuleTransitionJournalV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    lane_id: LaneIdV1
    module_release_id: str
    command_occurrence_id: str
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    private_port_root: str
    receipt_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="module journal chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "module_release_id",
            "command_occurrence_id",
            "pre_lane_root",
            "post_lane_root",
            "effect_plan_root",
            "private_port_root",
            "receipt_root",
            "terminal_obligations_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"module journal {field_name}",
                allow_zero=field_name
                in {
                    "pre_lane_root",
                    "post_lane_root",
                    "private_port_root",
                    "terminal_obligations_root",
                },
            )
        _require_nonnegative_int(self.writer_epoch, name="module journal writer epoch")
        if not isinstance(self.lane_id, LaneIdV1):
            raise TypeError("module journal lane is not closed")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("lane-module-transition-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "lane_id": self.lane_id,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "pre_lane_root": self.pre_lane_root,
            "post_lane_root": self.post_lane_root,
            "effect_plan_root": self.effect_plan_root,
            "private_port_root": self.private_port_root,
            "receipt_root": self.receipt_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


@dataclass(frozen=True, slots=True)
class LaneCompositionJournalV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    lane_id: LaneIdV1
    coordinator_release_id: str
    command_occurrence_id: str
    ordered_module_journal_roots: tuple[str, ...]
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="lane composition chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "coordinator_release_id",
            "command_occurrence_id",
            "pre_lane_root",
            "post_lane_root",
            "effect_plan_root",
            "terminal_obligations_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"lane composition {field_name}",
                allow_zero=field_name
                in {"pre_lane_root", "post_lane_root", "terminal_obligations_root"},
            )
        _require_nonnegative_int(self.writer_epoch, name="lane composition writer epoch")
        if not isinstance(self.lane_id, LaneIdV1):
            raise TypeError("lane composition lane is not closed")
        roots = _require_semantic_order_unique(
            self.ordered_module_journal_roots,
            name="lane composition module journals",
        )
        if not 1 <= len(roots) <= MAX_ROUTE_MODULES_V1:
            raise ValueError("lane composition requires between one and eight module journals")
        for index, root in enumerate(roots):
            _require_root(root, name=f"lane composition module journal[{index}]")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("lane-composition-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "lane_id": self.lane_id,
            "coordinator_release_id": self.coordinator_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "ordered_module_journal_roots": self.ordered_module_journal_roots,
            "pre_lane_root": self.pre_lane_root,
            "post_lane_root": self.post_lane_root,
            "effect_plan_root": self.effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


@dataclass(frozen=True, slots=True)
class RouteCompositionJournalV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    route_release_id: str
    command_occurrence_id: str
    ordered_lane_journal_roots: tuple[str, ...]
    pre_state_root: str
    post_state_root: str
    effect_plan_root: str
    terminal_obligations_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="route composition chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "route_release_id",
            "command_occurrence_id",
            "pre_state_root",
            "post_state_root",
            "effect_plan_root",
            "terminal_obligations_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"route composition {field_name}",
                allow_zero=field_name == "terminal_obligations_root",
            )
        _require_nonnegative_int(self.writer_epoch, name="route composition writer epoch")
        roots = _require_semantic_order_unique(
            self.ordered_lane_journal_roots,
            name="route composition lane journals",
        )
        if not 1 <= len(roots) <= MAX_ROUTE_MODULES_V1:
            raise ValueError("route composition requires between one and eight lane journals")
        for index, root in enumerate(roots):
            _require_root(root, name=f"route composition lane journal[{index}]")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("route-composition-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "route_release_id": self.route_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "ordered_lane_journal_roots": self.ordered_lane_journal_roots,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effect_plan_root": self.effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
        }


@dataclass(frozen=True, slots=True)
class CommandAggregationJournalV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    epoch_height: int
    group_index: int
    first_command_index: int
    ordered_occurrence_ids: tuple[str, ...]
    ordered_route_journal_roots: tuple[str, ...]
    ordered_route_assumption_roots: tuple[str, ...]
    pre_state_root: str
    post_state_root: str
    module_leaf_occurrences: int

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="command aggregation chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "pre_state_root",
            "post_state_root",
        ):
            _require_root(getattr(self, field_name), name=f"command aggregation {field_name}")
        for field_name in (
            "writer_epoch",
            "epoch_height",
            "group_index",
            "first_command_index",
        ):
            _require_nonnegative_int(
                getattr(self, field_name), name=f"command aggregation {field_name}"
            )
        occurrences = _require_semantic_order_unique(
            self.ordered_occurrence_ids, name="command aggregation occurrences"
        )
        routes = _require_semantic_order_unique(
            self.ordered_route_journal_roots, name="command aggregation route journals"
        )
        assumptions = _require_semantic_order_unique(
            self.ordered_route_assumption_roots,
            name="command aggregation route assumptions",
        )
        command_count = len(occurrences)
        if not 1 <= command_count <= 8:
            raise ValueError("command aggregation requires between one and eight routes")
        if len(routes) != command_count or len(assumptions) != command_count:
            raise ValueError("command aggregation route vectors must have exact cardinality")
        for name, roots in (
            ("occurrence", occurrences),
            ("route journal", routes),
            ("route assumption", assumptions),
        ):
            for index, root in enumerate(roots):
                _require_root(root, name=f"command aggregation {name}[{index}]")
        if self.group_index >= 8 or self.first_command_index != self.group_index * 8:
            raise ValueError("command aggregation group position is noncanonical")
        if self.first_command_index + command_count > MAX_EPOCH_COMMANDS_V1:
            raise ValueError("command aggregation exceeds the epoch command ceiling")
        _require_positive_int(
            self.module_leaf_occurrences,
            name="command aggregation module leaf occurrences",
        )
        if not command_count <= self.module_leaf_occurrences <= command_count * 8:
            raise ValueError("command aggregation module leaf count is out of bounds")

    @property
    def journal_root(self) -> str:
        return hash_global_v1("command-aggregation-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1,
            "settlement_abi": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "epoch_height": self.epoch_height,
            "group_index": self.group_index,
            "first_command_index": self.first_command_index,
            "ordered_occurrence_ids": self.ordered_occurrence_ids,
            "ordered_route_journal_roots": self.ordered_route_journal_roots,
            "ordered_route_assumption_roots": self.ordered_route_assumption_roots,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "module_leaf_occurrences": self.module_leaf_occurrences,
        }


class ReceiptKindV1(str, Enum):
    SUCCINCT = "SUCCINCT"
    COMPOSITE = "COMPOSITE"
    CONDITIONAL = "CONDITIONAL"
    FAKE = "FAKE"
    DEVELOPMENT = "DEVELOPMENT"


@dataclass(frozen=True, slots=True)
class GlobalEconomicEpochCertificateV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    height: int
    pre_state_root: str
    post_state_root: str
    ordered_occurrence_ids: tuple[str, ...]
    ordered_route_journal_roots: tuple[str, ...]
    ordered_route_assumption_roots: tuple[str, ...]
    module_leaf_occurrences: int
    aggregation_fanout: int
    aggregation_levels: int
    effect_plan_root: str
    terminal_obligations_root: str
    body_commitment: str
    data_availability_root: str
    finality_root: str
    source_manifest_root: str
    toolchain_manifest_root: str
    root_image_id: str
    receipt_root: str
    receipt_kind: ReceiptKindV1
    journal_bytes: int
    cycle_budget: int

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="epoch chain id")
        for field_name in (
            "deployment_root",
            "profile_root",
            "pre_state_root",
            "post_state_root",
            "effect_plan_root",
            "terminal_obligations_root",
            "body_commitment",
            "data_availability_root",
            "finality_root",
            "source_manifest_root",
            "toolchain_manifest_root",
            "root_image_id",
            "receipt_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"epoch {field_name}",
                allow_zero=field_name == "terminal_obligations_root",
            )
        _require_nonnegative_int(self.writer_epoch, name="epoch writer epoch")
        _require_nonnegative_int(self.height, name="epoch height")
        occurrences = _require_semantic_order_unique(
            self.ordered_occurrence_ids,
            name="epoch occurrence ids",
        )
        routes = _require_semantic_order_unique(
            self.ordered_route_journal_roots,
            name="epoch route journal roots",
        )
        assumptions = _require_semantic_order_unique(
            self.ordered_route_assumption_roots,
            name="epoch route assumption roots",
        )
        if not 1 <= len(occurrences) <= MAX_EPOCH_COMMANDS_V1:
            raise ValueError("epoch must contain between one and 64 commands")
        if len(routes) != len(occurrences) or len(assumptions) != len(occurrences):
            raise ValueError(
                "epoch must contain exactly one route journal and assumption per command"
            )
        for name, roots in (
            ("occurrence", occurrences),
            ("route journal", routes),
            ("route assumption", assumptions),
        ):
            for index, root in enumerate(roots):
                _require_root(root, name=f"epoch {name}[{index}]")
        _require_positive_int(self.module_leaf_occurrences, name="epoch module leaf occurrences")
        if self.module_leaf_occurrences > MAX_EPOCH_LEAF_OCCURRENCES_V1:
            raise ValueError("epoch exceeds 64 module leaf occurrences")
        if self.module_leaf_occurrences < len(occurrences):
            raise ValueError("epoch module leaf count cannot be smaller than command count")
        if self.aggregation_fanout != 8:
            raise ValueError("ABI V1 epoch aggregation fanout must equal eight")
        _require_nonnegative_int(self.aggregation_levels, name="epoch aggregation levels")
        if self.aggregation_levels > 2:
            raise ValueError("ABI V1 permits at most two aggregation levels")
        if not isinstance(self.receipt_kind, ReceiptKindV1):
            raise TypeError("epoch receipt kind is not closed")
        _require_positive_int(self.journal_bytes, name="epoch journal bytes")
        _require_positive_int(self.cycle_budget, name="epoch cycle budget")
        if self.journal_bytes > MAX_JOURNAL_BYTES_V1:
            raise ValueError("epoch journal exceeds ABI V1 byte ceiling")
        if self.cycle_budget > MAX_CYCLE_BUDGET_V1:
            raise ValueError("epoch cycle budget exceeds ABI V1 ceiling")

    @property
    def certificate_root(self) -> str:
        return hash_global_v1("global-economic-epoch-certificate-v1", self.to_canonical())

    def journal_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "height": self.height,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "ordered_occurrence_ids": self.ordered_occurrence_ids,
            "ordered_route_journal_roots": self.ordered_route_journal_roots,
            "ordered_route_assumption_roots": self.ordered_route_assumption_roots,
            "module_leaf_occurrences": self.module_leaf_occurrences,
            "aggregation_fanout": self.aggregation_fanout,
            "aggregation_levels": self.aggregation_levels,
            "effect_plan_root": self.effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
            "body_commitment": self.body_commitment,
            "data_availability_root": self.data_availability_root,
            "finality_root": self.finality_root,
            "source_manifest_root": self.source_manifest_root,
            "toolchain_manifest_root": self.toolchain_manifest_root,
            "root_image_id": self.root_image_id,
        }

    @property
    def canonical_journal_bytes(self) -> bytes:
        return canonical_global_bytes_v1(self.journal_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            **self.journal_canonical(),
            "receipt_root": self.receipt_root,
            "receipt_kind": self.receipt_kind,
            "journal_bytes": self.journal_bytes,
            "cycle_budget": self.cycle_budget,
        }


class MigrationObjectClassV1(str, Enum):
    MIGRATED = "MIGRATED"
    RETAINED_FOR_DRAIN = "RETAINED_FOR_DRAIN"
    CLOSED = "CLOSED"
    TOMBSTONED = "TOMBSTONED"


@dataclass(frozen=True, slots=True, order=True)
class MigrationObjectRowV1:
    source_object_id: str
    source_release_id: str
    target_release_id: str
    classification: MigrationObjectClassV1
    source_object_root: str
    target_object_root: str
    continuity_root: str

    def __post_init__(self) -> None:
        _require_token(self.source_object_id, name="migration source object id")
        for field_name in (
            "source_release_id",
            "target_release_id",
            "source_object_root",
            "target_object_root",
            "continuity_root",
        ):
            _require_root(
                getattr(self, field_name),
                name=f"migration object {field_name}",
                allow_zero=field_name == "target_object_root",
            )
        if not isinstance(self.classification, MigrationObjectClassV1):
            raise TypeError("migration object classification is not closed")
        if (
            self.classification is MigrationObjectClassV1.MIGRATED
            and self.target_object_root == "0x" + "00" * 32
        ):
            raise ValueError("migrated object requires a nonzero target root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "source_object_id": self.source_object_id,
            "source_release_id": self.source_release_id,
            "target_release_id": self.target_release_id,
            "classification": self.classification,
            "source_object_root": self.source_object_root,
            "target_object_root": self.target_object_root,
            "continuity_root": self.continuity_root,
        }


@dataclass(frozen=True, slots=True)
class StateMigrationCertificateV1:
    source_profile_root: str
    target_profile_root: str
    predecessor_profile_root: str
    source_state_root: str
    target_state_root: str
    source_writer_epoch: int
    target_writer_epoch: int
    object_rows: tuple[MigrationObjectRowV1, ...]
    custody_continuity_root: str
    liability_continuity_root: str
    terminal_continuity_root: str
    replay_continuity_root: str
    root_image_id: str
    proof_receipt_root: str
    receipt_kind: ReceiptKindV1

    def __post_init__(self) -> None:
        for field_name in (
            "source_profile_root",
            "target_profile_root",
            "predecessor_profile_root",
            "source_state_root",
            "target_state_root",
            "custody_continuity_root",
            "liability_continuity_root",
            "terminal_continuity_root",
            "replay_continuity_root",
            "root_image_id",
            "proof_receipt_root",
        ):
            _require_root(getattr(self, field_name), name=f"migration certificate {field_name}")
        _require_nonnegative_int(self.source_writer_epoch, name="migration source writer epoch")
        _require_nonnegative_int(self.target_writer_epoch, name="migration target writer epoch")
        if self.target_writer_epoch != self.source_writer_epoch + 1:
            raise ValueError("migration must rotate the writer epoch exactly once")
        if self.source_profile_root == self.target_profile_root:
            raise ValueError("migration target profile must differ from source profile")
        if self.predecessor_profile_root != self.source_profile_root:
            raise ValueError("migration predecessor must equal the source profile")
        _require_tuple(self.object_rows, name="migration object rows")
        if any(not isinstance(item, MigrationObjectRowV1) for item in self.object_rows):
            raise TypeError("migration certificate contains an invalid object row")
        keys = tuple(item.source_object_id for item in self.object_rows)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("migration object rows must be source-object ordered and unique")
        if not isinstance(self.receipt_kind, ReceiptKindV1):
            raise TypeError("migration receipt kind is not closed")
        if self.receipt_kind is not ReceiptKindV1.SUCCINCT:
            raise ValueError("migration authority requires a succinct receipt")

    @property
    def certificate_root(self) -> str:
        return hash_global_v1("state-migration-certificate-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "source_profile_root": self.source_profile_root,
            "target_profile_root": self.target_profile_root,
            "predecessor_profile_root": self.predecessor_profile_root,
            "source_state_root": self.source_state_root,
            "target_state_root": self.target_state_root,
            "source_writer_epoch": self.source_writer_epoch,
            "target_writer_epoch": self.target_writer_epoch,
            "object_rows": self.object_rows,
            "custody_continuity_root": self.custody_continuity_root,
            "liability_continuity_root": self.liability_continuity_root,
            "terminal_continuity_root": self.terminal_continuity_root,
            "replay_continuity_root": self.replay_continuity_root,
            "root_image_id": self.root_image_id,
            "proof_receipt_root": self.proof_receipt_root,
            "receipt_kind": self.receipt_kind,
        }


class SuccinctReceiptVerifierV1(Protocol):
    """Port implemented by the release-selected cryptographic verifier."""

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


@dataclass(frozen=True, slots=True)
class EconomicEpochReceiptCandidateV1:
    """Immutable untrusted input bundle for bounded epoch verification."""

    profile: EconomicProfileSnapshotV1
    certificate: GlobalEconomicEpochCertificateV1
    command_occurrences: tuple[EconomicCommandOccurrenceV1, ...]
    route_journals: tuple[RouteCompositionJournalV1, ...]
    verified_routes: tuple[VerifiedRouteCompositionV1, ...]
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...]
    effect_plan: GlobalEconomicEffectPlanV1
    receipt_bytes: bytes
    expected_chain_id: str
    expected_deployment_root: str
    expected_pre_state_root: str
    expected_body_commitment: str

    def __post_init__(self) -> None:
        from .route_composition_receipt_verification_v1 import VerifiedRouteCompositionV1

        if not isinstance(self.profile, EconomicProfileSnapshotV1):
            raise TypeError("economic epoch profile type is not closed")
        if not isinstance(self.certificate, GlobalEconomicEpochCertificateV1):
            raise TypeError("economic epoch certificate type is not closed")
        if type(self.command_occurrences) is not tuple or any(
            not isinstance(item, EconomicCommandOccurrenceV1) for item in self.command_occurrences
        ):
            raise TypeError("economic epoch contains an invalid command occurrence")
        if type(self.route_journals) is not tuple or any(
            not isinstance(item, RouteCompositionJournalV1) for item in self.route_journals
        ):
            raise TypeError("economic epoch contains an invalid route journal")
        if type(self.verified_routes) is not tuple or any(
            not isinstance(item, VerifiedRouteCompositionV1) for item in self.verified_routes
        ):
            raise TypeError("economic epoch contains an invalid verified route")
        if type(self.route_effect_plans) is not tuple or any(
            not isinstance(item, GlobalEconomicEffectPlanV1)
            for item in self.route_effect_plans
        ):
            raise TypeError("economic epoch contains an invalid route effect plan")
        if not isinstance(self.effect_plan, GlobalEconomicEffectPlanV1):
            raise TypeError("economic epoch effect plan type is not closed")
        if type(self.receipt_bytes) is not bytes:
            raise TypeError("economic epoch receipt bytes must be exact bytes")


_VERIFIED_ECONOMIC_EPOCH_TOKEN = object()


def derive_verified_economic_epoch_commit_id_v1(
    *,
    certificate_root: str,
    ordered_route_binding_roots: tuple[str, ...],
    receipt_digest: str,
) -> str:
    """Derive the sole commit identity from the verified epoch provenance."""

    _require_root(certificate_root, name="verified epoch certificate root")
    _require_tuple(
        ordered_route_binding_roots,
        name="verified epoch route binding roots",
    )
    if not ordered_route_binding_roots:
        raise ValueError("verified epoch requires at least one route binding root")
    for index, root in enumerate(ordered_route_binding_roots):
        _require_root(root, name=f"verified epoch route binding root[{index}]")
    if len(ordered_route_binding_roots) != len(set(ordered_route_binding_roots)):
        raise ValueError("verified epoch route binding roots must be unique")
    _require_root(receipt_digest, name="verified epoch receipt digest")
    return hash_global_v1(
        "verified-economic-epoch-commit-v1",
        {
            "certificate_root": certificate_root,
            "ordered_route_binding_roots": ordered_route_binding_roots,
            "receipt_digest": receipt_digest,
        },
    )


class VerifiedEconomicEpochV1:
    """Opaque epoch witness constructible only through the verifier function."""

    __slots__ = (
        "_certificate",
        "_effect_plan",
        "_ordered_route_binding_roots",
        "_receipt_digest",
    )
    _certificate: GlobalEconomicEpochCertificateV1
    _effect_plan: GlobalEconomicEffectPlanV1
    _ordered_route_binding_roots: tuple[str, ...]
    _receipt_digest: str

    def __init__(
        self,
        token: object,
        certificate: GlobalEconomicEpochCertificateV1,
        effect_plan: GlobalEconomicEffectPlanV1,
        ordered_route_binding_roots: tuple[str, ...],
        receipt_digest: str,
    ) -> None:
        if token is not _VERIFIED_ECONOMIC_EPOCH_TOKEN:
            raise TypeError("VerifiedEconomicEpochV1 is verifier-constructed")
        _require_tuple(
            ordered_route_binding_roots,
            name="verified epoch route binding roots",
        )
        if not ordered_route_binding_roots:
            raise ValueError("verified epoch requires at least one route binding root")
        for index, root in enumerate(ordered_route_binding_roots):
            _require_root(root, name=f"verified epoch route binding root[{index}]")
        if len(ordered_route_binding_roots) != len(set(ordered_route_binding_roots)):
            raise ValueError("verified epoch route binding roots must be unique")
        object.__setattr__(self, "_certificate", certificate)
        object.__setattr__(self, "_effect_plan", effect_plan)
        object.__setattr__(
            self,
            "_ordered_route_binding_roots",
            ordered_route_binding_roots,
        )
        object.__setattr__(self, "_receipt_digest", receipt_digest)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("VerifiedEconomicEpochV1 is immutable")

    @property
    def certificate(self) -> GlobalEconomicEpochCertificateV1:
        return self._certificate

    @property
    def effect_plan(self) -> GlobalEconomicEffectPlanV1:
        return self._effect_plan

    @property
    def ordered_route_binding_roots(self) -> tuple[str, ...]:
        return self._ordered_route_binding_roots

    @property
    def receipt_digest(self) -> str:
        return self._receipt_digest

    @property
    def commit_id(self) -> str:
        return derive_verified_economic_epoch_commit_id_v1(
            certificate_root=self._certificate.certificate_root,
            ordered_route_binding_roots=self._ordered_route_binding_roots,
            receipt_digest=self._receipt_digest,
        )


def verify_economic_epoch_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    receipt_verifier: SuccinctReceiptVerifierV1,
) -> VerifiedEconomicEpochV1:
    """Verify release bindings and a succinct receipt for one epoch.

    The supplied verifier owns cryptographic acceptance.  This function owns
    profile, exact opaque route witness, journal, body, effect, count, and
    canonical-byte binding.
    """

    if not isinstance(candidate, EconomicEpochReceiptCandidateV1):
        raise TypeError("economic epoch candidate type is not closed")
    _validate_profile_and_certificate_bindings(candidate)
    _validate_route_journals(candidate)
    ordered_route_binding_roots = _validate_verified_routes(candidate)
    _validate_route_effect_plans(candidate)
    journal_bytes = candidate.certificate.canonical_journal_bytes
    if candidate.certificate.journal_bytes != len(journal_bytes):
        raise ValueError("economic epoch canonical journal byte count mismatch")
    if not isinstance(candidate.receipt_bytes, bytes) or not candidate.receipt_bytes:
        raise ValueError("economic epoch receipt bytes must be non-empty")
    receipt_digest = "0x" + hashlib.sha256(candidate.receipt_bytes).hexdigest()
    if receipt_digest != candidate.certificate.receipt_root:
        raise ValueError("economic epoch receipt root mismatch")
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt_bytes,
        expected_image_id=candidate.profile.root_image_id,
        expected_journal_bytes=journal_bytes,
    )
    return VerifiedEconomicEpochV1(
        _VERIFIED_ECONOMIC_EPOCH_TOKEN,
        candidate.certificate,
        candidate.effect_plan,
        ordered_route_binding_roots,
        receipt_digest,
    )


def _validate_profile_and_certificate_bindings(
    candidate: EconomicEpochReceiptCandidateV1,
) -> None:
    profile = candidate.profile
    certificate = candidate.certificate
    effect_plan = candidate.effect_plan
    if not isinstance(profile, EconomicProfileSnapshotV1):
        raise TypeError("economic epoch profile type is not closed")
    if not isinstance(certificate, GlobalEconomicEpochCertificateV1):
        raise TypeError("economic epoch certificate type is not closed")
    if not isinstance(effect_plan, GlobalEconomicEffectPlanV1):
        raise TypeError("economic epoch effect plan type is not closed")
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("economic profile is not ACTIVE")
    if certificate.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("economic epoch requires a succinct root receipt")
    _require_token(candidate.expected_chain_id, name="expected chain id")
    _require_root(candidate.expected_deployment_root, name="expected deployment root")
    _require_root(candidate.expected_pre_state_root, name="expected pre-state root")
    _require_root(candidate.expected_body_commitment, name="expected body commitment")
    expected_bindings = (
        (certificate.chain_id, candidate.expected_chain_id, "chain id"),
        (
            certificate.deployment_root,
            candidate.expected_deployment_root,
            "deployment root",
        ),
        (certificate.profile_root, profile.profile_id, "profile root"),
        (
            certificate.pre_state_root,
            candidate.expected_pre_state_root,
            "pre-state root",
        ),
        (
            certificate.body_commitment,
            candidate.expected_body_commitment,
            "body commitment",
        ),
        (certificate.root_image_id, profile.root_image_id, "root image id"),
    )
    for actual, expected, label in expected_bindings:
        if actual != expected:
            raise ValueError(f"economic epoch {label} mismatch")
    if certificate.writer_epoch != profile.authority_epoch:
        raise ValueError("economic epoch writer epoch mismatch")
    if certificate.effect_plan_root != effect_plan.effect_plan_root:
        raise ValueError("economic epoch effect plan root mismatch")


def _validate_route_journals(
    candidate: EconomicEpochReceiptCandidateV1,
) -> None:
    certificate = candidate.certificate
    command_occurrences = candidate.command_occurrences
    route_journals = candidate.route_journals
    _validate_command_occurrences(certificate, command_occurrences)
    _require_tuple(route_journals, name="economic epoch route journals")
    if len(route_journals) != len(certificate.ordered_occurrence_ids):
        raise ValueError("economic epoch route journal count mismatch")
    if any(not isinstance(item, RouteCompositionJournalV1) for item in route_journals):
        raise TypeError("economic epoch contains an invalid route journal")
    if (
        tuple(item.journal_root for item in route_journals)
        != certificate.ordered_route_journal_roots
    ):
        raise ValueError("economic epoch route journal order or root mismatch")
    if (
        tuple(item.command_occurrence_id for item in route_journals)
        != certificate.ordered_occurrence_ids
    ):
        raise ValueError("economic epoch occurrence order mismatch")

    current_root = certificate.pre_state_root
    for occurrence, route_journal in zip(command_occurrences, route_journals, strict=True):
        current_root = _validate_route_journal_pair(
            candidate.profile,
            certificate,
            occurrence,
            route_journal,
            expected_pre_state_root=current_root,
        )
    if current_root != certificate.post_state_root:
        raise ValueError("economic epoch route chain does not reach the certified post-state")


def _validate_command_occurrences(
    certificate: GlobalEconomicEpochCertificateV1,
    command_occurrences: tuple[EconomicCommandOccurrenceV1, ...],
) -> None:
    _require_tuple(command_occurrences, name="economic epoch command occurrences")
    if any(not isinstance(item, EconomicCommandOccurrenceV1) for item in command_occurrences):
        raise TypeError("economic epoch contains an invalid command occurrence")
    if (
        tuple(item.occurrence_id for item in command_occurrences)
        != certificate.ordered_occurrence_ids
    ):
        raise ValueError("economic epoch command occurrence order or root mismatch")
    positions = tuple((item.height, item.tx_index, item.op_index) for item in command_occurrences)
    if positions != tuple(sorted(set(positions))):
        raise ValueError(
            "economic epoch command occurrences are not canonically ordered and unique"
        )
    replay_keys = tuple((item.subject_id, item.nonce) for item in command_occurrences)
    if len(replay_keys) != len(set(replay_keys)):
        raise ValueError("economic epoch repeats a subject nonce")
    consumed: set[str] = set()
    for occurrence in command_occurrences:
        overlap = consumed.intersection(occurrence.consumed_object_ids)
        if overlap:
            raise ValueError("economic epoch consumes one object more than once")
        consumed.update(occurrence.consumed_object_ids)


def _validate_route_journal_pair(
    profile: EconomicProfileSnapshotV1,
    certificate: GlobalEconomicEpochCertificateV1,
    occurrence: EconomicCommandOccurrenceV1,
    route_journal: RouteCompositionJournalV1,
    *,
    expected_pre_state_root: str,
) -> str:
    registered = {route.route_release_id: route for route in profile.route_registry.routes}
    route = registered.get(route_journal.route_release_id)
    if route is None:
        raise ValueError("economic epoch contains an unregistered route release")
    if route.status is not ReleaseStatusV1.ACTIVE_NEW or not route.accepts_new_objects:
        raise ValueError("economic epoch contains an inactive route release")
    if occurrence.route_release_id != route.route_release_id:
        raise ValueError("command occurrence route does not match route journal")
    if occurrence.command_kind != route.command_kind:
        raise ValueError("command occurrence kind does not match governed route")
    if len(route_journal.ordered_lane_journal_roots) != len(route.ordered_lanes):
        raise ValueError("route journal lane receipt count does not match governed route")
    bindings = (
        (route_journal.chain_id, certificate.chain_id, "chain id"),
        (route_journal.deployment_root, certificate.deployment_root, "deployment root"),
        (route_journal.profile_root, certificate.profile_root, "profile root"),
        (route_journal.pre_state_root, expected_pre_state_root, "pre-state root"),
        (occurrence.chain_id, certificate.chain_id, "occurrence chain id"),
        (occurrence.deployment_root, certificate.deployment_root, "occurrence deployment root"),
        (occurrence.profile_root, certificate.profile_root, "occurrence profile root"),
        (occurrence.pre_state_root, route_journal.pre_state_root, "occurrence pre-state root"),
        (occurrence.height, certificate.height, "occurrence height"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"route journal {label} mismatch")
    if route_journal.writer_epoch != certificate.writer_epoch:
        raise ValueError("route journal writer epoch mismatch")
    return route_journal.post_state_root


def _validate_verified_routes(
    candidate: EconomicEpochReceiptCandidateV1,
) -> tuple[str, ...]:
    from .route_composition_receipt_verification_v1 import VerifiedRouteCompositionV1

    verified_routes = candidate.verified_routes
    _require_tuple(verified_routes, name="economic epoch verified routes")
    if len(verified_routes) != len(candidate.route_journals):
        raise ValueError("economic epoch route witness count mismatch")
    if any(not isinstance(item, VerifiedRouteCompositionV1) for item in verified_routes):
        raise TypeError("economic epoch contains an invalid verified route")

    roots = tuple(
        _validated_route_binding_root(candidate.profile, occurrence, route_journal, witness)
        for occurrence, route_journal, witness in zip(
            candidate.command_occurrences,
            candidate.route_journals,
            verified_routes,
            strict=True,
        )
    )
    if len(roots) != len(set(roots)):
        raise ValueError("economic epoch route witness bindings must be unique")
    assumption_roots = tuple(item.assumption_root for item in verified_routes)
    if assumption_roots != candidate.certificate.ordered_route_assumption_roots:
        raise ValueError("economic epoch route assumption root mismatch")
    return roots


def _validate_route_effect_plans(candidate: EconomicEpochReceiptCandidateV1) -> None:
    plans = candidate.route_effect_plans
    _require_tuple(plans, name="economic epoch route effect plans")
    if len(plans) != len(candidate.route_journals):
        raise ValueError("economic epoch route effect plan count mismatch")

    for occurrence, journal, plan in zip(
        candidate.command_occurrences,
        candidate.route_journals,
        plans,
        strict=True,
    ):
        route = candidate.profile.route_registry.route_for_command(
            occurrence.command_kind,
            claimed_route_release_id=occurrence.route_release_id,
        )
        if route.ordered_lanes != (LaneIdV1.ASSET_TRANSFER,):
            raise ValueError("economic epoch route effect projection is unsupported")
        if plan.effect_plan_root != journal.effect_plan_root:
            raise ValueError("economic epoch route effect plan root mismatch")
        if plan.occurrence_consumptions != (occurrence.occurrence_id,):
            raise ValueError("economic epoch route effect occurrence mismatch")
        if journal.terminal_obligations_root != ZERO_ROOT_V1:
            raise ValueError("economic epoch route terminal composition is unsupported")

    if candidate.certificate.terminal_obligations_root != ZERO_ROOT_V1:
        raise ValueError("economic epoch terminal composition is unsupported")
    composed = compose_asset_lane_epoch_effect_plans_v1(plans)
    if composed != candidate.effect_plan:
        raise ValueError("economic epoch route effect plan aggregation mismatch")


def _validated_route_binding_root(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    route_journal: RouteCompositionJournalV1,
    verified_route: VerifiedRouteCompositionV1,
) -> str:
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    route_journal_digest = (
        "0x" + hashlib.sha256(canonical_global_bytes_v1(route_journal)).hexdigest()
    )
    bindings = (
        (verified_route.profile_id, profile.profile_id, "profile"),
        (verified_route.route_release_id, route.route_release_id, "release"),
        (verified_route.command_occurrence_id, occurrence.occurrence_id, "occurrence"),
        (verified_route.ordered_lane_ids, route.ordered_lanes, "lane order"),
        (
            verified_route.ordered_lane_journal_roots,
            route_journal.ordered_lane_journal_roots,
            "lane journals",
        ),
        (verified_route.route_journal_root, route_journal.journal_root, "journal"),
        (verified_route.route_journal_digest, route_journal_digest, "journal digest"),
        (verified_route.expected_image_id, route.guest_image_id, "image"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"economic epoch route witness {label} mismatch")
    if verified_route.writer_epoch != profile.authority_epoch:
        raise ValueError("economic epoch route witness writer epoch mismatch")
    if verified_route.receipt_kind is not ReceiptKindV1.SUCCINCT:
        raise ValueError("economic epoch route witness is not succinct")
    return verified_route.binding_root


__all__ = [
    "COMMAND_AGGREGATION_JOURNAL_SCHEMA_V1",
    "EconomicCommandOccurrenceV1",
    "LaneModuleTransitionJournalV1",
    "LaneCompositionJournalV1",
    "RouteCompositionJournalV1",
    "CommandAggregationJournalV1",
    "ReceiptKindV1",
    "GlobalEconomicEpochCertificateV1",
    "MigrationObjectClassV1",
    "MigrationObjectRowV1",
    "StateMigrationCertificateV1",
    "SuccinctReceiptVerifierV1",
    "EconomicEpochReceiptCandidateV1",
    "VerifiedEconomicEpochV1",
    "derive_verified_economic_epoch_commit_id_v1",
    "verify_economic_epoch_v1",
]
