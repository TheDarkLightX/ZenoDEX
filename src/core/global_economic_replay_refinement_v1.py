"""Replay-state refinement for disclosed economic command occurrences."""

from __future__ import annotations

from typing import Protocol

from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    RouteCompositionJournalV1,
)
from .global_settlement_types_v1 import (
    MAX_EPOCH_COMMANDS_V1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    ReplayStateV1,
)


class _ReplayRefinementInputV1(Protocol):
    @property
    def pre_state(self) -> GlobalEconomicStateV1: ...

    @property
    def post_state(self) -> GlobalEconomicStateV1: ...

    @property
    def effect_plan(self) -> GlobalEconomicEffectPlanV1: ...

    @property
    def consumed_occurrences(self) -> tuple[EconomicCommandOccurrenceV1, ...]: ...

    @property
    def route_journals(self) -> tuple[RouteCompositionJournalV1, ...]: ...


def _require_disclosure_set_v1(candidate: _ReplayRefinementInputV1) -> None:
    occurrences = candidate.consumed_occurrences
    if len(occurrences) > MAX_EPOCH_COMMANDS_V1:
        raise ValueError("economic refinement occurrence count exceeds epoch bound")
    if len(candidate.route_journals) != len(occurrences):
        raise ValueError("economic refinement route-state chain count mismatch")
    disclosed_roots = tuple(sorted(item.occurrence_id for item in occurrences))
    if disclosed_roots != candidate.effect_plan.occurrence_consumptions:
        raise ValueError("economic refinement occurrence disclosure mismatch")
    positions = tuple((item.height, item.tx_index, item.op_index) for item in occurrences)
    if positions != tuple(sorted(set(positions))):
        raise ValueError("economic refinement occurrence order mismatch")


def _require_route_state_chain_v1(candidate: _ReplayRefinementInputV1) -> None:
    pre_state = candidate.pre_state
    current_root = pre_state.state_root
    for occurrence, journal in zip(
        candidate.consumed_occurrences,
        candidate.route_journals,
        strict=True,
    ):
        context_matches = (
            occurrence.chain_id == pre_state.chain_id
            and occurrence.deployment_root == pre_state.deployment_root
            and occurrence.profile_root == pre_state.profile_root
            and occurrence.height == pre_state.height
            and occurrence.pre_state_root == current_root
            and journal.chain_id == pre_state.chain_id
            and journal.deployment_root == pre_state.deployment_root
            and journal.profile_root == pre_state.profile_root
            and journal.writer_epoch == pre_state.writer_epoch
            and journal.route_release_id == occurrence.route_release_id
            and journal.command_occurrence_id == occurrence.occurrence_id
            and journal.pre_state_root == current_root
        )
        if not context_matches:
            raise ValueError("economic refinement occurrence state context mismatch")
        current_root = journal.post_state_root
    if candidate.consumed_occurrences and current_root != candidate.post_state.state_root:
        raise ValueError("economic refinement route-state chain terminal mismatch")


def _derive_replay_insertions_v1(
    candidate: _ReplayRefinementInputV1,
) -> tuple[ReplayStateV1, ...]:
    _require_disclosure_set_v1(candidate)
    _require_route_state_chain_v1(candidate)

    insertions = tuple(
        sorted(
            (
                ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
                for occurrence in candidate.consumed_occurrences
            ),
            key=lambda row: row.replay_id,
        )
    )
    replay_ids = tuple(row.replay_id for row in insertions)
    if len(replay_ids) != len(set(replay_ids)):
        raise ValueError("economic refinement duplicate replay identity")
    existing_ids = {row.replay_id for row in candidate.pre_state.replay_state}
    if existing_ids.intersection(replay_ids):
        raise ValueError("economic refinement replay identity already consumed")
    existing_occurrence_ids = {
        row.occurrence_id for row in candidate.pre_state.replay_state
    }
    insertion_occurrence_ids = tuple(row.occurrence_id for row in insertions)
    if existing_occurrence_ids.intersection(insertion_occurrence_ids):
        raise ValueError("economic refinement occurrence already consumed")
    expected_post = tuple(
        sorted(
            (*candidate.pre_state.replay_state, *insertions),
            key=lambda row: row.replay_id,
        )
    )
    if candidate.post_state.replay_state != expected_post:
        raise ValueError("economic refinement replay state delta mismatch")
    return insertions


__all__ = ["_derive_replay_insertions_v1"]
