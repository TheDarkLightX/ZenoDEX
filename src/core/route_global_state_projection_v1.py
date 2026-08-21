"""Deterministic full-state projection for one profile-selected route.

The checker closes the structural relation between monolithic global state
roots and the lane roots named by route-composition journals. It is an
unmounted deterministic checker: it verifies no receipt, applies no economic
effects, and grants no settlement or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    RouteCompositionJournalV1,
)
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    EconomicProfileSnapshotV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    ProfileStatusV1,
    RouteReleaseV1,
    hash_global_v1,
    validate_global_state_profile_v1,
)

ROUTE_GLOBAL_STATE_PROJECTION_SCHEMA_V1: Final = (
    "zenodex/route-global-state-projection/v1"
)
_ROUTE_GLOBAL_STATE_PROJECTION_TOKEN = object()


@dataclass(frozen=True, slots=True)
class RouteGlobalStateProjectionCandidateV1:
    profile: EconomicProfileSnapshotV1
    route: RouteReleaseV1
    lane_journals: tuple[LaneCompositionJournalV1, ...]
    route_journal: RouteCompositionJournalV1
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1

    def __post_init__(self) -> None:
        typed_fields = (
            (self.profile, EconomicProfileSnapshotV1, "profile"),
            (self.route, RouteReleaseV1, "route"),
            (self.route_journal, RouteCompositionJournalV1, "route journal"),
            (self.pre_state, GlobalEconomicStateV1, "pre-state"),
            (self.post_state, GlobalEconomicStateV1, "post-state"),
        )
        for value, expected_type, name in typed_fields:
            if type(value) is not expected_type:
                raise TypeError(f"route global projection {name} must be typed")
        if type(self.lane_journals) is not tuple:
            raise TypeError("route global projection lane journals must be an exact tuple")
        if any(type(item) is not LaneCompositionJournalV1 for item in self.lane_journals):
            raise TypeError("route global projection lane journals must be typed")


@dataclass(frozen=True, slots=True)
class RouteGlobalLaneProjectionV1:
    lane_id: LaneIdV1
    module_release_id: str
    lane_journal_root: str
    pre_lane_root: str
    post_lane_root: str

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "module_release_id": self.module_release_id,
            "lane_journal_root": self.lane_journal_root,
            "pre_lane_root": self.pre_lane_root,
            "post_lane_root": self.post_lane_root,
        }


@dataclass(frozen=True, slots=True)
class _RouteGlobalStateProjectionFieldsV1:
    chain_id: str
    deployment_root: str
    profile_id: str
    writer_epoch: int
    route_release_id: str
    command_occurrence_id: str
    route_journal_root: str
    pre_state_root: str
    post_state_root: str
    ordered_lanes: tuple[RouteGlobalLaneProjectionV1, ...]
    unselected_lane_roots_root: str


class RouteGlobalStateProjectionV1:
    """Opaque witness produced only after full-state projection checks pass."""

    _fields: _RouteGlobalStateProjectionFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _RouteGlobalStateProjectionFieldsV1) -> None:
        if token is not _ROUTE_GLOBAL_STATE_PROJECTION_TOKEN:
            raise TypeError("RouteGlobalStateProjectionV1 is checker-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("RouteGlobalStateProjectionV1 is immutable")

    @property
    def ordered_lane_ids(self) -> tuple[LaneIdV1, ...]:
        return tuple(row.lane_id for row in self._fields.ordered_lanes)

    @property
    def pre_state_root(self) -> str:
        return self._fields.pre_state_root

    @property
    def post_state_root(self) -> str:
        return self._fields.post_state_root

    @property
    def projection_root(self) -> str:
        return hash_global_v1(
            "route-global-state-projection-v1",
            {
                "schema": ROUTE_GLOBAL_STATE_PROJECTION_SCHEMA_V1,
                "chain_id": self._fields.chain_id,
                "deployment_root": self._fields.deployment_root,
                "profile_id": self._fields.profile_id,
                "writer_epoch": self._fields.writer_epoch,
                "route_release_id": self._fields.route_release_id,
                "command_occurrence_id": self._fields.command_occurrence_id,
                "route_journal_root": self._fields.route_journal_root,
                "pre_state_root": self._fields.pre_state_root,
                "post_state_root": self._fields.post_state_root,
                "ordered_lanes": self._fields.ordered_lanes,
                "unselected_lane_roots_root": self._fields.unselected_lane_roots_root,
            },
        )


def _require_profile_route_v1(candidate: RouteGlobalStateProjectionCandidateV1) -> None:
    profile = candidate.profile
    if profile.profile_id != profile.derived_profile_id:
        raise ValueError("route global projection profile content-derived id mismatch")
    if profile.status is not ProfileStatusV1.ACTIVE:
        raise ValueError("route global projection profile is not ACTIVE")
    governed = profile.route_registry.route_for_command(
        candidate.route.command_kind,
        claimed_route_release_id=candidate.route.route_release_id,
    )
    if governed != candidate.route:
        raise ValueError("route global projection governed route mismatch")


def _revalidate_immutable_inputs_v1(
    candidate: RouteGlobalStateProjectionCandidateV1,
) -> None:
    """Re-run constructor invariants after possible hostile object mutation."""

    profile = candidate.profile
    replace(profile)
    replace(profile.lane_registry)
    replace(profile.lane_coordinator_registry)
    replace(profile.route_registry)
    for release in profile.lane_registry.releases:
        replace(release)
    for coordinator in profile.lane_coordinator_registry.releases:
        replace(coordinator)
    for route in profile.route_registry.routes:
        replace(route)
    replace(candidate.route)
    replace(candidate.route_journal)
    for state in (candidate.pre_state, candidate.post_state):
        replace(state)
        for lane_root in state.lane_roots:
            replace(lane_root)
        for amount in (*state.balances, *state.custody, *state.liabilities, *state.reserves):
            replace(amount)
        for supply in state.supplies:
            replace(supply)
        for occurrence in state.oracle_occurrences:
            replace(occurrence)
        for replay in state.replay_state:
            replace(replay)
        for obligation in state.terminal_obligations:
            replace(obligation)
        for outbox_row in state.outbox:
            replace(outbox_row)
    for journal in candidate.lane_journals:
        replace(journal)


def _require_global_state_context_v1(
    candidate: RouteGlobalStateProjectionCandidateV1,
) -> None:
    pre_state = candidate.pre_state
    post_state = candidate.post_state
    journal = candidate.route_journal
    validate_global_state_profile_v1(pre_state, candidate.profile)
    validate_global_state_profile_v1(post_state, candidate.profile)
    if post_state.chain_id != pre_state.chain_id:
        raise ValueError("route global projection post-state chain mismatch")
    if post_state.deployment_root != pre_state.deployment_root:
        raise ValueError("route global projection post-state deployment mismatch")
    if post_state.writer_epoch != pre_state.writer_epoch:
        raise ValueError("route global projection post-state writer epoch mismatch")
    bindings = (
        (journal.chain_id, pre_state.chain_id, "route journal chain"),
        (journal.deployment_root, pre_state.deployment_root, "route journal deployment"),
        (journal.profile_root, candidate.profile.profile_id, "route journal profile"),
        (journal.route_release_id, candidate.route.route_release_id, "route journal release"),
        (journal.pre_state_root, pre_state.state_root, "global state root"),
        (journal.post_state_root, post_state.state_root, "global state root"),
    )
    for actual, expected, name in bindings:
        if actual != expected:
            raise ValueError(f"route global projection {name} mismatch")
    if journal.writer_epoch != candidate.profile.authority_epoch:
        raise ValueError("route global projection route journal writer epoch mismatch")


def _require_lane_journal_context_v1(
    candidate: RouteGlobalStateProjectionCandidateV1,
) -> None:
    route = candidate.route
    journals = candidate.lane_journals
    route_journal = candidate.route_journal
    if len(journals) != len(route.ordered_lanes):
        raise ValueError("route global projection lane journal count mismatch")
    if tuple(journal.lane_id for journal in journals) != route.ordered_lanes:
        raise ValueError("route global projection lane journal order mismatch")
    if tuple(journal.journal_root for journal in journals) != (
        route_journal.ordered_lane_journal_roots
    ):
        raise ValueError("route global projection route lane journal roots mismatch")
    for journal in journals:
        coordinator = candidate.profile.lane_coordinator_registry.release_for(journal.lane_id)
        bindings = (
            (journal.chain_id, route_journal.chain_id, "lane journal chain"),
            (journal.deployment_root, route_journal.deployment_root, "lane journal deployment"),
            (journal.profile_root, route_journal.profile_root, "lane journal profile"),
            (
                journal.command_occurrence_id,
                route_journal.command_occurrence_id,
                "lane journal occurrence",
            ),
            (
                journal.coordinator_release_id,
                coordinator.coordinator_release_id,
                "coordinator release",
            ),
        )
        for actual, expected, name in bindings:
            if actual != expected:
                raise ValueError(f"route global projection {name} mismatch")
        if journal.writer_epoch != route_journal.writer_epoch:
            raise ValueError("route global projection lane journal writer epoch mismatch")


def _project_lane_roots_v1(
    candidate: RouteGlobalStateProjectionCandidateV1,
) -> tuple[tuple[RouteGlobalLaneProjectionV1, ...], tuple[LaneStateRootV1, ...]]:
    selected = set(candidate.route.ordered_lanes)
    rows: list[RouteGlobalLaneProjectionV1] = []
    unchanged: list[LaneStateRootV1] = []
    journals = {journal.lane_id: journal for journal in candidate.lane_journals}
    for pre_lane, post_lane in zip(
        candidate.pre_state.lane_roots,
        candidate.post_state.lane_roots,
        strict=True,
    ):
        if pre_lane.lane_id not in selected:
            if pre_lane != post_lane:
                raise ValueError("route global projection unselected lane changed")
            unchanged.append(pre_lane)
            continue
        journal = journals[pre_lane.lane_id]
        if (
            pre_lane.state_root != journal.pre_lane_root
            or post_lane.state_root != journal.post_lane_root
        ):
            raise ValueError("route global projection selected lane root mismatch")
        rows.append(
            RouteGlobalLaneProjectionV1(
                lane_id=pre_lane.lane_id,
                module_release_id=pre_lane.module_release_id,
                lane_journal_root=journal.journal_root,
                pre_lane_root=pre_lane.state_root,
                post_lane_root=post_lane.state_root,
            )
        )
    ordered_rows = tuple(
        next(row for row in rows if row.lane_id is lane_id)
        for lane_id in candidate.route.ordered_lanes
    )
    return ordered_rows, tuple(unchanged)


def project_route_global_state_v1(
    candidate: RouteGlobalStateProjectionCandidateV1,
) -> RouteGlobalStateProjectionV1:
    """Validate one full-state/lane projection and return its opaque binding."""

    if type(candidate) is not RouteGlobalStateProjectionCandidateV1:
        raise TypeError("route global state projection candidate must be typed")
    _revalidate_immutable_inputs_v1(candidate)
    _require_profile_route_v1(candidate)
    _require_global_state_context_v1(candidate)
    _require_lane_journal_context_v1(candidate)
    rows, unchanged = _project_lane_roots_v1(candidate)
    unchanged_root = hash_global_v1(
        "route-global-unselected-lane-roots-v1",
        {"schema": GLOBAL_SETTLEMENT_ABI_V1, "lane_roots": unchanged},
    )
    return RouteGlobalStateProjectionV1(
        _ROUTE_GLOBAL_STATE_PROJECTION_TOKEN,
        _RouteGlobalStateProjectionFieldsV1(
            chain_id=candidate.pre_state.chain_id,
            deployment_root=candidate.pre_state.deployment_root,
            profile_id=candidate.profile.profile_id,
            writer_epoch=candidate.profile.authority_epoch,
            route_release_id=candidate.route.route_release_id,
            command_occurrence_id=candidate.route_journal.command_occurrence_id,
            route_journal_root=candidate.route_journal.journal_root,
            pre_state_root=candidate.pre_state.state_root,
            post_state_root=candidate.post_state.state_root,
            ordered_lanes=rows,
            unselected_lane_roots_root=unchanged_root,
        ),
    )


__all__ = [
    "ROUTE_GLOBAL_STATE_PROJECTION_SCHEMA_V1",
    "RouteGlobalLaneProjectionV1",
    "RouteGlobalStateProjectionCandidateV1",
    "RouteGlobalStateProjectionV1",
    "project_route_global_state_v1",
]
