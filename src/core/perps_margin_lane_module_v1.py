"""Owned guest input and recomputation boundary for perps margin accounting.

The base transition already emits the module journal and private port. This
wrapper owns and revalidates every retained value before release binding or
receipt verification. It grants no proof, route, settlement, or publication
authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, TypeAlias

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_dataclass_tuple_v1,
    _snapshot_effect_plan_v1,
)
from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    TerminalObligationV1,
    hash_global_v1,
)
from .perps_margin_module_v1 import transition_perps_margin_v1
from .perps_margin_types_v1 import (
    PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
    PerpsMarginAcceptedV1,
    PerpsMarginAccountV1,
    PerpsMarginCommandV1,
    PerpsMarginContextV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginPrivatePortV1,
    PerpsMarginRejectedV1,
    PerpsMarginStateV1,
)

PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1: Final = (
    PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1
)


@dataclass(frozen=True, slots=True)
class PerpsMarginLaneModuleInputV1:
    context: PerpsMarginContextV1
    pre_state: PerpsMarginStateV1
    command: PerpsMarginCommandV1

    def __post_init__(self) -> None:
        if type(self.context) is not PerpsMarginContextV1:
            raise TypeError("perps margin lane context must be exact typed data")
        if type(self.pre_state) is not PerpsMarginStateV1:
            raise TypeError("perps margin lane pre-state must be exact typed data")
        if type(self.command) is not PerpsMarginCommandV1:
            raise TypeError("perps margin lane command must be exact typed data")

    @property
    def statement_root(self) -> str:
        return hash_global_v1(
            "perps-margin-statement-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1,
            "context": self.context,
            "pre_state": self.pre_state,
            "command": self.command,
        }


def _snapshot_perps_margin_state_v1(
    state: PerpsMarginStateV1,
) -> PerpsMarginStateV1:
    if type(state) is not PerpsMarginStateV1:
        raise TypeError("perps margin state must have the exact typed value")
    for field_name in (
        "module_release_id",
        "market_id",
        "collateral_asset",
    ):
        if type(getattr(state, field_name)) is not str:
            raise TypeError(f"perps margin state {field_name} must be exact text")
    for field_name in (
        "index_price_e8",
        "maintenance_margin_bps",
        "depeg_buffer_bps",
        "max_position_abs",
    ):
        if type(getattr(state, field_name)) is not int:
            raise TypeError(f"perps margin state {field_name} must be an exact int")
    if type(state.market_status) is not PerpsMarginMarketStatusV1:
        raise TypeError("perps margin state market status must be exact typed data")
    if type(state.accounts) is not tuple:
        raise TypeError("perps margin state accounts must be an exact tuple")
    return replace(
        state,
        accounts=_snapshot_dataclass_tuple_v1(
            state.accounts,
            PerpsMarginAccountV1,
            "perps margin accounts",
        ),
    )


def _snapshot_perps_margin_lane_module_input_v1(
    module_input: PerpsMarginLaneModuleInputV1,
) -> PerpsMarginLaneModuleInputV1:
    if type(module_input) is not PerpsMarginLaneModuleInputV1:
        raise TypeError("perps margin lane input must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        module_input.context,
        name="perps margin context",
    )
    _require_exact_dataclass_scalars_v1(
        module_input.command,
        name="perps margin command",
    )
    return PerpsMarginLaneModuleInputV1(
        context=replace(module_input.context),
        pre_state=_snapshot_perps_margin_state_v1(module_input.pre_state),
        command=replace(module_input.command),
    )


def _snapshot_perps_margin_accepted_v1(
    accepted: PerpsMarginAcceptedV1,
) -> PerpsMarginAcceptedV1:
    if type(accepted) is not PerpsMarginAcceptedV1:
        raise TypeError("perps margin accepted output must have the exact typed value")
    if type(accepted.statement_root) is not str:
        raise TypeError("perps margin accepted statement root must be exact text")
    if type(accepted.effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("perps margin accepted effects must have the exact typed value")
    if type(accepted.module_journal) is not LaneModuleTransitionJournalV1:
        raise TypeError("perps margin accepted journal must have the exact typed value")
    if type(accepted.private_port) is not PerpsMarginPrivatePortV1:
        raise TypeError("perps margin accepted private port must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        accepted.module_journal,
        name="perps margin accepted journal",
    )
    _require_exact_dataclass_scalars_v1(
        accepted.private_port,
        name="perps margin accepted private port",
    )
    return PerpsMarginAcceptedV1(
        statement_root=accepted.statement_root,
        post_state=_snapshot_perps_margin_state_v1(accepted.post_state),
        effects=_snapshot_effect_plan_v1(accepted.effects),
        module_journal=replace(accepted.module_journal),
        private_port=replace(accepted.private_port),
        terminal_obligations=_snapshot_dataclass_tuple_v1(
            accepted.terminal_obligations,
            TerminalObligationV1,
            "perps margin terminal obligations",
        ),
    )


PerpsMarginLaneModuleResultV1: TypeAlias = (
    PerpsMarginAcceptedV1 | PerpsMarginRejectedV1
)


def transition_perps_margin_lane_module_v1(
    module_input: PerpsMarginLaneModuleInputV1,
) -> PerpsMarginLaneModuleResultV1:
    """Run one exact owned perps-margin leaf transition."""

    owned = _snapshot_perps_margin_lane_module_input_v1(module_input)
    result = transition_perps_margin_v1(
        owned.context,
        owned.pre_state,
        owned.command,
    )
    if isinstance(result, PerpsMarginAcceptedV1) and (
        result.statement_root != owned.statement_root
    ):
        raise ValueError("perps margin transition statement root drift")
    return result


def _recompute_perps_margin_accepted_v1(
    module_input: PerpsMarginLaneModuleInputV1,
    accepted: PerpsMarginAcceptedV1,
) -> tuple[PerpsMarginLaneModuleInputV1, PerpsMarginAcceptedV1]:
    owned = _snapshot_perps_margin_lane_module_input_v1(module_input)
    expected = transition_perps_margin_v1(
        owned.context,
        owned.pre_state,
        owned.command,
    )
    if type(expected) is not PerpsMarginAcceptedV1:
        raise ValueError("perps margin supplied acceptance recomputes to rejection")
    if expected.statement_root != owned.statement_root:
        raise ValueError("perps margin recomputed statement root drift")
    supplied = _snapshot_perps_margin_accepted_v1(accepted)
    if supplied != expected:
        raise ValueError("perps margin supplied acceptance differs from recomputation")
    return owned, expected


__all__ = [
    "PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1",
    "PerpsMarginLaneModuleInputV1",
    "PerpsMarginLaneModuleResultV1",
    "transition_perps_margin_lane_module_v1",
]
