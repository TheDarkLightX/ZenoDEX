"""Structural active-profile binding for accepted lane-module outputs.

This core closes profile, route, release, occurrence, command, and domain
bindings before lane composition. It does not verify a cryptographic receipt
and grants no settlement or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final, Protocol

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
)
from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    LaneModuleTransitionJournalV1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    ProfileStatusV1,
    hash_global_v1,
)
from .managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleAcceptedV1,
    ManagedAssetLifecycleLaneModuleInputV1,
)

RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1: Final = (
    "zenodex/release-route-bound-lane-transition/v1"
)
_RELEASE_ROUTE_BOUND_TOKEN = object()


class ReleaseRouteBoundLaneTransitionV1:
    """Opaque structural witness produced only by the release-route binder."""

    _profile_id: str
    _route_release_id: str
    _lane_id: LaneIdV1
    _module_release_id: str
    _command_occurrence_id: str
    _module_journal_root: str
    _statement_root: str
    _producer_module_schema: str
    _route_lane_index: int
    _port_schema_root: str

    __slots__ = (
        "_profile_id",
        "_route_release_id",
        "_lane_id",
        "_module_release_id",
        "_command_occurrence_id",
        "_module_journal_root",
        "_statement_root",
        "_producer_module_schema",
        "_route_lane_index",
        "_port_schema_root",
    )

    def __init__(
        self,
        token: object,
        profile_id: str,
        route_release_id: str,
        lane_id: LaneIdV1,
        module_release_id: str,
        command_occurrence_id: str,
        module_journal_root: str,
        statement_root: str,
        producer_module_schema: str,
        route_lane_index: int,
        port_schema_root: str,
    ) -> None:
        if token is not _RELEASE_ROUTE_BOUND_TOKEN:
            raise TypeError("ReleaseRouteBoundLaneTransitionV1 is binder-constructed")
        object.__setattr__(self, "_profile_id", profile_id)
        object.__setattr__(self, "_route_release_id", route_release_id)
        object.__setattr__(self, "_lane_id", lane_id)
        object.__setattr__(self, "_module_release_id", module_release_id)
        object.__setattr__(self, "_command_occurrence_id", command_occurrence_id)
        object.__setattr__(self, "_module_journal_root", module_journal_root)
        object.__setattr__(self, "_statement_root", statement_root)
        object.__setattr__(self, "_producer_module_schema", producer_module_schema)
        object.__setattr__(self, "_route_lane_index", route_lane_index)
        object.__setattr__(self, "_port_schema_root", port_schema_root)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("ReleaseRouteBoundLaneTransitionV1 is immutable")

    @property
    def profile_id(self) -> str:
        return self._profile_id

    @property
    def route_release_id(self) -> str:
        return self._route_release_id

    @property
    def lane_id(self) -> LaneIdV1:
        return self._lane_id

    @property
    def module_release_id(self) -> str:
        return self._module_release_id

    @property
    def command_occurrence_id(self) -> str:
        return self._command_occurrence_id

    @property
    def module_journal_root(self) -> str:
        return self._module_journal_root

    @property
    def statement_root(self) -> str:
        return self._statement_root

    @property
    def producer_module_schema(self) -> str:
        return self._producer_module_schema

    @property
    def route_lane_index(self) -> int:
        return self._route_lane_index

    @property
    def port_schema_root(self) -> str:
        return self._port_schema_root

    @property
    def binding_root(self) -> str:
        return hash_global_v1(
            "release-route-bound-lane-transition-v1",
            {
                "schema": RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
                "profile_id": self.profile_id,
                "route_release_id": self.route_release_id,
                "lane_id": self.lane_id,
                "module_release_id": self.module_release_id,
                "command_occurrence_id": self.command_occurrence_id,
                "module_journal_root": self.module_journal_root,
                "statement_root": self.statement_root,
                "producer_module_schema": self.producer_module_schema,
                "route_lane_index": self.route_lane_index,
                "port_schema_root": self.port_schema_root,
            },
        )


@dataclass(frozen=True, slots=True)
class _BindingCandidateV1:
    actual_command_kind: str
    statement_root: str
    producer_module_schema: str
    context: _ModuleContextV1
    module_journal: LaneModuleTransitionJournalV1


class _ModuleContextV1(Protocol):
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str


def _require_exact_context_binding(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> None:
    context = candidate.context
    bindings = (
        (context.subject_id, occurrence.subject_id, "subject"),
        (context.grant_root, occurrence.grant_root, "grant root"),
        (context.chain_id, occurrence.chain_id, "chain id"),
        (context.deployment_root, occurrence.deployment_root, "deployment root"),
        (context.profile_root, profile.profile_id, "profile root"),
        (context.command_occurrence_id, occurrence.occurrence_id, "command occurrence"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"lane module release-route {label} mismatch")
    if context.writer_epoch != profile.authority_epoch:
        raise ValueError("lane module release-route writer epoch mismatch")


def _require_exact_journal_binding(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> None:
    journal = candidate.module_journal
    bindings = (
        (journal.chain_id, occurrence.chain_id, "journal chain id"),
        (journal.deployment_root, occurrence.deployment_root, "journal deployment root"),
        (journal.profile_root, profile.profile_id, "journal profile root"),
        (journal.command_occurrence_id, occurrence.occurrence_id, "journal occurrence"),
    )
    for actual, expected, label in bindings:
        if actual != expected:
            raise ValueError(f"lane module release-route {label} mismatch")
    if journal.writer_epoch != profile.authority_epoch:
        raise ValueError("lane module release-route journal writer epoch mismatch")


def _bind_candidate_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    candidate: _BindingCandidateV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("economic profile is not ACTIVE")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if candidate.actual_command_kind != occurrence.command_kind:
        raise ValueError("lane module release-route command kind mismatch")
    _require_exact_context_binding(profile, occurrence, candidate)
    _require_exact_journal_binding(profile, occurrence, candidate)

    journal = candidate.module_journal
    try:
        route_lane_index = route.ordered_lanes.index(journal.lane_id)
    except ValueError as exc:
        raise ValueError("lane module release-route lane mismatch") from exc
    release = profile.lane_registry.release_for(journal.lane_id)
    if (
        journal.module_release_id != release.release_id
        or route.module_release_ids[route_lane_index] != release.release_id
        or candidate.context.module_release_id != release.release_id
    ):
        raise ValueError("lane module release-route module release mismatch")
    if candidate.actual_command_kind not in release.command_variants:
        raise ValueError("lane module command is absent from the governed release")

    return ReleaseRouteBoundLaneTransitionV1(
        _RELEASE_ROUTE_BOUND_TOKEN,
        profile.profile_id,
        route.route_release_id,
        journal.lane_id,
        release.release_id,
        occurrence.occurrence_id,
        journal.journal_root,
        candidate.statement_root,
        candidate.producer_module_schema,
        route_lane_index,
        route.port_schema_roots[route_lane_index],
    )


def bind_asset_transfer_lane_output_to_release_route_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    """Bind one accepted transfer output to its governed active route."""

    if not isinstance(profile, EconomicProfileSnapshotV1):
        raise TypeError("economic profile must be typed")
    if not isinstance(occurrence, EconomicCommandOccurrenceV1):
        raise TypeError("economic command occurrence must be typed")
    if not isinstance(module_input, AssetTransferLaneModuleInputV1):
        raise TypeError("asset transfer lane input must be typed")
    if not isinstance(accepted, AssetTransferLaneModuleAcceptedV1):
        raise TypeError("asset transfer accepted output must be typed")
    if accepted.statement_root != module_input.statement_root:
        raise ValueError("asset transfer accepted statement mismatch")
    return _bind_candidate_v1(
        profile,
        occurrence,
        _BindingCandidateV1(
            module_input.command.command_kind,
            accepted.statement_root,
            accepted.private_port.producer_module_schema,
            module_input.context,
            accepted.module_journal,
        ),
    )


def bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> ReleaseRouteBoundLaneTransitionV1:
    """Bind one accepted ordinary-token issue or burn to its governed route."""

    if not isinstance(profile, EconomicProfileSnapshotV1):
        raise TypeError("economic profile must be typed")
    if not isinstance(occurrence, EconomicCommandOccurrenceV1):
        raise TypeError("economic command occurrence must be typed")
    if not isinstance(module_input, ManagedAssetLifecycleLaneModuleInputV1):
        raise TypeError("managed asset lifecycle lane input must be typed")
    if not isinstance(accepted, ManagedAssetLifecycleLaneModuleAcceptedV1):
        raise TypeError("managed asset lifecycle accepted output must be typed")
    if accepted.statement_root != module_input.statement_root:
        raise ValueError("managed asset lifecycle accepted statement mismatch")
    return _bind_candidate_v1(
        profile,
        occurrence,
        _BindingCandidateV1(
            module_input.command.command_kind,
            accepted.statement_root,
            accepted.private_port.producer_module_schema,
            module_input.context,
            accepted.module_journal,
        ),
    )


__all__ = [
    "RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1",
    "ReleaseRouteBoundLaneTransitionV1",
    "bind_asset_transfer_lane_output_to_release_route_v1",
    "bind_managed_asset_lifecycle_lane_output_to_release_route_v1",
]
