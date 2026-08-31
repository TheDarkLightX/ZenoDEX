"""Exact primitive checks used before Python economic refinement."""

from __future__ import annotations

from dataclasses import fields, replace
from enum import Enum
from typing import Any

from .global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    GlobalEconomicEpochCertificateV1,
    LaneCompositionJournalV1,
    RouteCompositionJournalV1,
)
from .global_settlement_types_v1 import (
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
    LaneWriteV1,
    OracleOccurrenceStateV1,
    OutboxStateV1,
    ReplayStateV1,
    TerminalObligationV1,
)


def _require_exact_dataclass_scalars_v1(
    value: Any,
    *,
    name: str,
    tuple_fields: frozenset[str] = frozenset(),
) -> None:
    for field in fields(value):
        item = getattr(value, field.name)
        if field.name in tuple_fields:
            if type(item) is not tuple:
                raise TypeError(f"economic refinement {name}.{field.name} must be exact tuple")
            continue
        if isinstance(item, Enum) and field.name not in {
            "kind",
            "lane_id",
            "receipt_kind",
            "status",
        }:
            raise TypeError(
                f"economic refinement {name}.{field.name} must be an exact primitive"
            )
        if isinstance(item, Enum):
            continue
        if type(item) not in {str, int, bool}:
            raise TypeError(
                f"economic refinement {name}.{field.name} must be an exact primitive"
            )


def _require_exact_tuple_items(
    values: object,
    expected_type: type[Any],
    name: str,
) -> tuple[Any, ...]:
    if type(values) is not tuple:
        raise TypeError(f"economic refinement {name} must be an exact tuple")
    if any(type(value) is not expected_type for value in values):
        raise TypeError(f"economic refinement {name} must contain exact typed values")
    return values


def _snapshot_dataclass_tuple_v1(
    values: object,
    expected_type: type[Any],
    name: str,
) -> tuple[Any, ...]:
    snapshots = []
    for value in _require_exact_tuple_items(values, expected_type, name):
        _require_exact_dataclass_scalars_v1(value, name=name)
        snapshots.append(replace(value))
    return tuple(snapshots)


def _snapshot_state_v1(state: GlobalEconomicStateV1) -> GlobalEconomicStateV1:
    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("economic refinement state must have the exact typed value")
    tuple_fields = frozenset(
        {
            "lane_roots",
            "balances",
            "supplies",
            "custody",
            "liabilities",
            "reserves",
            "oracle_occurrences",
            "replay_state",
            "terminal_obligations",
            "outbox",
        }
    )
    _require_exact_dataclass_scalars_v1(
        state,
        name="state",
        tuple_fields=tuple_fields,
    )
    return replace(
        state,
        lane_roots=_snapshot_dataclass_tuple_v1(
            state.lane_roots, LaneStateRootV1, "state lane_roots"
        ),
        balances=_snapshot_dataclass_tuple_v1(
            state.balances, EconomicAmountV1, "state balances"
        ),
        supplies=_snapshot_dataclass_tuple_v1(
            state.supplies, AssetSupplyV1, "state supplies"
        ),
        custody=_snapshot_dataclass_tuple_v1(
            state.custody, EconomicAmountV1, "state custody"
        ),
        liabilities=_snapshot_dataclass_tuple_v1(
            state.liabilities, EconomicAmountV1, "state liabilities"
        ),
        reserves=_snapshot_dataclass_tuple_v1(
            state.reserves, EconomicAmountV1, "state reserves"
        ),
        oracle_occurrences=_snapshot_dataclass_tuple_v1(
            state.oracle_occurrences,
            OracleOccurrenceStateV1,
            "state oracle_occurrences",
        ),
        replay_state=_snapshot_dataclass_tuple_v1(
            state.replay_state, ReplayStateV1, "state replay_state"
        ),
        terminal_obligations=_snapshot_dataclass_tuple_v1(
            state.terminal_obligations,
            TerminalObligationV1,
            "state terminal_obligations",
        ),
        outbox=_snapshot_dataclass_tuple_v1(
            state.outbox, OutboxStateV1, "state outbox"
        ),
    )


def _snapshot_effect_plan_v1(
    effect_plan: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    if type(effect_plan) is not GlobalEconomicEffectPlanV1:
        raise TypeError("economic refinement effect plan must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        effect_plan,
        name="effect plan",
        tuple_fields=frozenset(
            {
                "rows",
                "asset_conservation",
                "fee_conservation",
                "lane_writes",
                "occurrence_consumptions",
                "external_outbox_enqueue",
            }
        ),
    )
    consumptions = _require_exact_tuple_items(
        effect_plan.occurrence_consumptions,
        str,
        "effect plan occurrence consumptions",
    )
    return replace(
        effect_plan,
        rows=_snapshot_dataclass_tuple_v1(
            effect_plan.rows, EconomicEffectRowV1, "effect plan rows"
        ),
        asset_conservation=_snapshot_dataclass_tuple_v1(
            effect_plan.asset_conservation,
            AssetConservationRowV1,
            "effect plan asset_conservation",
        ),
        fee_conservation=_snapshot_dataclass_tuple_v1(
            effect_plan.fee_conservation,
            FeeConservationRowV1,
            "effect plan fee_conservation",
        ),
        lane_writes=_snapshot_dataclass_tuple_v1(
            effect_plan.lane_writes, LaneWriteV1, "effect plan lane_writes"
        ),
        occurrence_consumptions=tuple(consumptions),
        external_outbox_enqueue=_snapshot_dataclass_tuple_v1(
            effect_plan.external_outbox_enqueue,
            ExternalOutboxEnqueueV1,
            "effect plan external_outbox_enqueue",
        ),
    )


def _snapshot_epoch_certificate_v1(
    certificate: GlobalEconomicEpochCertificateV1,
) -> GlobalEconomicEpochCertificateV1:
    if type(certificate) is not GlobalEconomicEpochCertificateV1:
        raise TypeError("economic epoch certificate must have the exact typed value")
    tuple_fields = frozenset(
        {
            "ordered_occurrence_ids",
            "ordered_route_journal_roots",
            "ordered_route_assumption_roots",
        }
    )
    _require_exact_dataclass_scalars_v1(
        certificate,
        name="epoch certificate",
        tuple_fields=tuple_fields,
    )
    return replace(
        certificate,
        ordered_occurrence_ids=tuple(
            _require_exact_tuple_items(
                certificate.ordered_occurrence_ids,
                str,
                "epoch certificate occurrence ids",
            )
        ),
        ordered_route_journal_roots=tuple(
            _require_exact_tuple_items(
                certificate.ordered_route_journal_roots,
                str,
                "epoch certificate route journal roots",
            )
        ),
        ordered_route_assumption_roots=tuple(
            _require_exact_tuple_items(
                certificate.ordered_route_assumption_roots,
                str,
                "epoch certificate route assumption roots",
            )
        ),
    )


def _snapshot_occurrence_v1(
    occurrence: EconomicCommandOccurrenceV1,
) -> EconomicCommandOccurrenceV1:
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("economic refinement occurrence must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        occurrence,
        name="consumed occurrence",
        tuple_fields=frozenset({"consumed_object_ids"}),
    )
    return replace(
        occurrence,
        consumed_object_ids=tuple(
            _require_exact_tuple_items(
                occurrence.consumed_object_ids,
                str,
                "occurrence consumed object ids",
            )
        ),
    )


def _snapshot_lane_journal_v1(
    journal: LaneCompositionJournalV1,
) -> LaneCompositionJournalV1:
    if type(journal) is not LaneCompositionJournalV1:
        raise TypeError("economic refinement lane journal must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        journal,
        name="lane journal",
        tuple_fields=frozenset({"ordered_module_journal_roots"}),
    )
    return replace(
        journal,
        ordered_module_journal_roots=tuple(
            _require_exact_tuple_items(
                journal.ordered_module_journal_roots,
                str,
                "lane journal module roots",
            )
        ),
    )


def _snapshot_route_journal_v1(
    journal: RouteCompositionJournalV1,
) -> RouteCompositionJournalV1:
    if type(journal) is not RouteCompositionJournalV1:
        raise TypeError("economic refinement route journal must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        journal,
        name="route journal",
        tuple_fields=frozenset({"ordered_lane_journal_roots"}),
    )
    return replace(
        journal,
        ordered_lane_journal_roots=tuple(
            _require_exact_tuple_items(
                journal.ordered_lane_journal_roots,
                str,
                "route journal lane roots",
            )
        ),
    )


__all__ = [
    "_require_exact_tuple_items",
    "_snapshot_effect_plan_v1",
    "_snapshot_epoch_certificate_v1",
    "_snapshot_lane_journal_v1",
    "_snapshot_occurrence_v1",
    "_snapshot_route_journal_v1",
    "_snapshot_state_v1",
]
