"""Occurrence and module-journal values for GlobalSettlementABI V2.

These values are deterministic verifier inputs.  They do not verify a proof,
authenticate a profile, or authorize publication.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    ZERO_ROOT_V2,
    LaneIdV2,
    _require_nonnegative_int_v2,
    _require_root_v2,
    _require_sorted_unique_tokens_v2,
    _require_token_v2,
    hash_global_v2,
)


@dataclass(frozen=True, slots=True)
class EconomicCommandOccurrenceV2:
    chain_id: str
    deployment_root: str
    height: int
    tx_index: int
    op_index: int
    command_kind: str
    command_body_hash: str
    route_release_id: str
    subject_id: str
    grant_root: str
    nonce: int
    profile_root: str
    pre_state_root: str
    consumed_object_ids: tuple[str, ...]

    def __post_init__(self) -> None:
        _require_token_v2(self.chain_id, name="occurrence chain id")
        _require_root_v2(self.deployment_root, name="occurrence deployment root")
        _require_nonnegative_int_v2(self.height, name="occurrence height")
        _require_nonnegative_int_v2(self.tx_index, name="occurrence tx_index")
        _require_nonnegative_int_v2(self.op_index, name="occurrence op_index")
        _require_token_v2(self.command_kind, name="occurrence command kind")
        _require_root_v2(self.command_body_hash, name="occurrence command body hash")
        _require_root_v2(self.route_release_id, name="occurrence route release id")
        _require_token_v2(self.subject_id, name="occurrence subject id")
        _require_root_v2(self.grant_root, name="occurrence grant root")
        _require_nonnegative_int_v2(self.nonce, name="occurrence nonce")
        _require_root_v2(self.profile_root, name="occurrence profile root")
        _require_root_v2(self.pre_state_root, name="occurrence pre-state root")
        _require_sorted_unique_tokens_v2(
            self.consumed_object_ids,
            name="occurrence consumed object ids",
        )

    @property
    def occurrence_id(self) -> str:
        return hash_global_v2(
            "global-economic-command-occurrence-v2",
            self.to_canonical(),
        )

    @property
    def replay_id(self) -> str:
        return hash_global_v2(
            "global-economic-replay-id-v2",
            {
                "chain_id": self.chain_id,
                "deployment_root": self.deployment_root,
                "subject_id": self.subject_id,
                "nonce": self.nonce,
            },
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "height": self.height,
            "tx_index": self.tx_index,
            "op_index": self.op_index,
            "command_kind": self.command_kind,
            "command_body_hash": self.command_body_hash,
            "route_release_id": self.route_release_id,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
            "nonce": self.nonce,
            "profile_root": self.profile_root,
            "pre_state_root": self.pre_state_root,
            "consumed_object_ids": self.consumed_object_ids,
        }


@dataclass(frozen=True, slots=True)
class LaneModuleTransitionJournalV2:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    lane_id: LaneIdV2
    module_release_id: str
    command_occurrence_id: str
    pre_lane_root: str
    post_lane_root: str
    effect_plan_root: str
    private_port_root: str
    receipt_root: str
    terminal_obligations_root: str
    oracle_occurrence_plan_root: str

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_token_v2(self.chain_id, name="module journal chain id")
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
            "oracle_occurrence_plan_root",
        ):
            _require_root_v2(
                getattr(self, field_name),
                name=f"module journal {field_name}",
                allow_zero=field_name
                in {
                    "pre_lane_root",
                    "post_lane_root",
                    "private_port_root",
                    "terminal_obligations_root",
                    "oracle_occurrence_plan_root",
                },
            )
        _require_nonnegative_int_v2(
            self.writer_epoch,
            name="module journal writer epoch",
        )
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("module journal lane is not closed")

    @property
    def journal_root(self) -> str:
        self.validate()
        return hash_global_v2(
            "lane-module-transition-journal-v2",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
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
            "oracle_occurrence_plan_root": self.oracle_occurrence_plan_root,
        }


def _snapshot_occurrence_v2(
    occurrence: EconomicCommandOccurrenceV2,
) -> EconomicCommandOccurrenceV2:
    if type(occurrence) is not EconomicCommandOccurrenceV2:
        raise TypeError("economic occurrence must have the exact typed value")
    if type(occurrence.consumed_object_ids) is not tuple or any(
        type(object_id) is not str for object_id in occurrence.consumed_object_ids
    ):
        raise TypeError("occurrence consumed object ids must be exact text")
    return replace(
        occurrence,
        consumed_object_ids=tuple(occurrence.consumed_object_ids),
    )


def _snapshot_module_journal_v2(
    journal: LaneModuleTransitionJournalV2,
) -> LaneModuleTransitionJournalV2:
    if type(journal) is not LaneModuleTransitionJournalV2:
        raise TypeError("module journal must have the exact typed value")
    return replace(journal)


__all__ = [
    "EconomicCommandOccurrenceV2",
    "LaneModuleTransitionJournalV2",
    "ZERO_ROOT_V2",
    "_snapshot_occurrence_v2",
    "_snapshot_module_journal_v2",
]
