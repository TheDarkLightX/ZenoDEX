"""Guest-ready bound output for the `ASSET_TRANSFER` transfer module.

The input and output are immutable deterministic values. Accepted transitions
bind the common asset-lane private port into the module journal and semantic
receipt root. Rejections are the exact base-module no-op. This module performs
no cryptographic receipt verification and grants no publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, TypeAlias

from .asset_lane_projection_v1 import (
    MAX_ASSET_LANE_CUSTODY_ROWS_V1,
    AssetLanePrivatePortV1,
    _snapshot_asset_lane_private_port_v1,
    project_asset_transfer_state_v1,
)
from .asset_transfer_module_v1 import (
    rebuild_asset_transfer_state_v1,
    transition_asset_transfer_v1,
)
from .asset_transfer_types_v1 import (
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_dataclass_tuple_v1,
    _snapshot_effect_plan_v1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    _require_ordered_objects,
    _require_root,
    hash_global_v1,
)

ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1: Final = (
    "zenodex/asset-transfer-lane-module-input/v1"
)


MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1: Final = MAX_ASSET_LANE_CUSTODY_ROWS_V1
"""The projection custody ceiling (mirrors Rust MAX_ASSET_CUSTODY_ROWS_V1; Opus P18 P3-g, P19 N2)."""


@dataclass(frozen=True, slots=True)
class AssetTransferLaneModuleInputV1:
    """Complete deterministic input for one transfer-module guest transition."""

    context: AssetTransferContextV1
    pre_state: AssetTransferStateV1
    command: AssetTransferCommandV1
    asset_policy_registry_root: str
    fee_policy_registry_root: str
    custody: tuple[EconomicAmountV1, ...]

    def __post_init__(self) -> None:
        if type(self.context) is not AssetTransferContextV1:
            raise TypeError("asset transfer lane module context must have the exact typed value")
        if type(self.pre_state) is not AssetTransferStateV1:
            raise TypeError("asset transfer lane module pre-state must have the exact typed value")
        if type(self.command) is not AssetTransferCommandV1:
            raise TypeError("asset transfer lane module command must have the exact typed value")
        _require_root(
            self.asset_policy_registry_root,
            name="asset transfer lane module asset policy registry",
        )
        _require_root(
            self.fee_policy_registry_root,
            name="asset transfer lane module fee policy registry",
        )
        _require_ordered_objects(
            self.custody,
            name="asset transfer lane module custody",
            expected_type=EconomicAmountV1,
            key="key",
            maximum=MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1,
        )
        project_asset_transfer_state_v1(
            self.pre_state,
            asset_policy_registry_root=self.asset_policy_registry_root,
            fee_policy_registry_root=self.fee_policy_registry_root,
            custody=self.custody,
        )

    @property
    def statement_root(self) -> str:
        return hash_global_v1(
            "asset-transfer-lane-module-statement-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
            "context": self.context,
            "pre_state": self.pre_state,
            "command": self.command,
            "asset_policy_registry_root": self.asset_policy_registry_root,
            "fee_policy_registry_root": self.fee_policy_registry_root,
            "custody": self.custody,
        }


def _snapshot_asset_transfer_state_v1(
    state: AssetTransferStateV1,
) -> AssetTransferStateV1:
    # Single definition of the deep rebuild (Fable P31 NEW-27); the core transition
    # entry uses the same function.
    return rebuild_asset_transfer_state_v1(state)


def _snapshot_asset_transfer_lane_module_input_v1(
    module_input: AssetTransferLaneModuleInputV1,
) -> AssetTransferLaneModuleInputV1:
    """Own one exact, revalidated input before execution or authority binding."""

    if type(module_input) is not AssetTransferLaneModuleInputV1:
        raise TypeError("asset transfer lane module input must have the exact typed value")
    if type(module_input.context) is not AssetTransferContextV1:
        raise TypeError("asset transfer lane module context must have the exact typed value")
    if type(module_input.pre_state) is not AssetTransferStateV1:
        raise TypeError("asset transfer lane module pre-state must have the exact typed value")
    if type(module_input.command) is not AssetTransferCommandV1:
        raise TypeError("asset transfer lane module command must have the exact typed value")
    if type(module_input.asset_policy_registry_root) is not str:
        raise TypeError("asset transfer asset-policy root must be an exact string")
    if type(module_input.fee_policy_registry_root) is not str:
        raise TypeError("asset transfer fee-policy root must be an exact string")

    _require_exact_dataclass_scalars_v1(
        module_input.context,
        name="asset transfer context",
    )
    _require_exact_dataclass_scalars_v1(
        module_input.command,
        name="asset transfer command",
    )
    return AssetTransferLaneModuleInputV1(
        context=replace(module_input.context),
        pre_state=_snapshot_asset_transfer_state_v1(module_input.pre_state),
        command=replace(module_input.command),
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=_snapshot_dataclass_tuple_v1(
            module_input.custody,
            EconomicAmountV1,
            "asset transfer custody",
        ),
    )


def _receipt_root(
    statement_root: str,
    module_journal: LaneModuleTransitionJournalV1,
    private_port: AssetLanePrivatePortV1,
    effects: GlobalEconomicEffectPlanV1,
) -> str:
    return hash_global_v1(
        "asset-transfer-lane-module-receipt-v1",
        {
            "statement_root": statement_root,
            "pre_state_root": module_journal.pre_lane_root,
            "post_state_root": module_journal.post_lane_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": private_port.port_root,
            "terminal_obligations_root": private_port.terminal_obligations_root,
        },
    )


@dataclass(frozen=True, slots=True)
class AssetTransferLaneModuleAcceptedV1:
    """Accepted transfer plus module-owned lane port and rebound journal."""

    statement_root: str
    post_state: AssetTransferStateV1
    effects: GlobalEconomicEffectPlanV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: AssetLanePrivatePortV1

    def __post_init__(self) -> None:
        _require_root(self.statement_root, name="asset transfer lane module statement")
        AssetTransferAcceptedV1(self.post_state, self.effects, self.module_journal)
        # Opus P28 F1: an ordinary subclass overriding port_root reported the
        # genuine root over foreign custody rows, and isinstance admitted it.
        if type(self.private_port) is not AssetLanePrivatePortV1:
            raise TypeError("asset transfer lane module private port must be the exact typed value")
        if self.private_port.producer_module_schema != ASSET_TRANSFER_MODULE_SCHEMA_V1:
            raise ValueError("asset transfer lane module producer schema mismatch")
        if self.private_port.module_release_id != self.module_journal.module_release_id:
            raise ValueError("asset transfer lane module release mismatch")
        if self.private_port.command_occurrence_id != self.module_journal.command_occurrence_id:
            raise ValueError("asset transfer lane module occurrence mismatch")
        if self.private_port.module_effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("asset transfer lane module effect-plan mismatch")
        if self.module_journal.private_port_root != self.private_port.port_root:
            raise ValueError("asset transfer lane module private-port root mismatch")
        if (
            self.module_journal.terminal_obligations_root
            != self.private_port.terminal_obligations_root
        ):
            raise ValueError("asset transfer lane module terminal obligations mismatch")
        if self.private_port.post_state.balances != self.post_state.balances:
            raise ValueError("asset transfer lane module post-balance projection mismatch")
        if self.private_port.post_state.supplies != self.post_state.supplies:
            raise ValueError("asset transfer lane module post-supply projection mismatch")
        if self.module_journal.receipt_root != _receipt_root(
            self.statement_root,
            self.module_journal,
            self.private_port,
            self.effects,
        ):
            raise ValueError("asset transfer lane module receipt root mismatch")

    @property
    def receipt_root(self) -> str:
        return self.module_journal.receipt_root


def _snapshot_asset_transfer_lane_module_accepted_v1(
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferLaneModuleAcceptedV1:
    if type(accepted) is not AssetTransferLaneModuleAcceptedV1:
        raise TypeError("asset transfer accepted output must have the exact typed value")
    if type(accepted.statement_root) is not str:
        raise TypeError("asset transfer accepted statement root must be exact text")
    if type(accepted.post_state) is not AssetTransferStateV1:
        raise TypeError("asset transfer accepted state must have the exact typed value")
    if type(accepted.effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("asset transfer accepted effects must have the exact typed value")
    if type(accepted.module_journal) is not LaneModuleTransitionJournalV1:
        raise TypeError("asset transfer accepted journal must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        accepted.module_journal,
        name="asset transfer accepted journal",
    )
    return AssetTransferLaneModuleAcceptedV1(
        statement_root=accepted.statement_root,
        post_state=_snapshot_asset_transfer_state_v1(accepted.post_state),
        effects=_snapshot_effect_plan_v1(accepted.effects),
        module_journal=replace(accepted.module_journal),
        private_port=_snapshot_asset_lane_private_port_v1(accepted.private_port),
    )


AssetTransferLaneModuleResultV1: TypeAlias = (
    AssetTransferLaneModuleAcceptedV1 | AssetTransferRejectedV1
)


def _private_port(
    module_input: AssetTransferLaneModuleInputV1,
    base_result: AssetTransferAcceptedV1,
) -> AssetLanePrivatePortV1:
    pre_projection = project_asset_transfer_state_v1(
        module_input.pre_state,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=module_input.custody,
    )
    post_projection = project_asset_transfer_state_v1(
        base_result.post_state,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=module_input.custody,
    )
    return AssetLanePrivatePortV1(
        producer_module_schema=ASSET_TRANSFER_MODULE_SCHEMA_V1,
        module_release_id=module_input.context.module_release_id,
        command_occurrence_id=module_input.context.command_occurrence_id,
        pre_state=pre_projection,
        post_state=post_projection,
        module_effect_plan_root=base_result.effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )


def _bound_journal(
    statement_root: str,
    base_result: AssetTransferAcceptedV1,
    private_port: AssetLanePrivatePortV1,
) -> LaneModuleTransitionJournalV1:
    base_journal = base_result.module_journal
    receipt_root = _receipt_root(
        statement_root,
        base_journal,
        private_port,
        base_result.effects,
    )
    return LaneModuleTransitionJournalV1(
        chain_id=base_journal.chain_id,
        deployment_root=base_journal.deployment_root,
        profile_root=base_journal.profile_root,
        writer_epoch=base_journal.writer_epoch,
        lane_id=base_journal.lane_id,
        module_release_id=base_journal.module_release_id,
        command_occurrence_id=base_journal.command_occurrence_id,
        pre_lane_root=base_journal.pre_lane_root,
        post_lane_root=base_journal.post_lane_root,
        effect_plan_root=base_journal.effect_plan_root,
        private_port_root=private_port.port_root,
        receipt_root=receipt_root,
        terminal_obligations_root=base_journal.terminal_obligations_root,
    )


def _transition_owned_asset_transfer_lane_module_v1(
    owned_input: AssetTransferLaneModuleInputV1,
) -> AssetTransferLaneModuleResultV1:
    base_result = transition_asset_transfer_v1(
        owned_input.context,
        owned_input.pre_state,
        owned_input.command,
    )
    if isinstance(base_result, AssetTransferRejectedV1):
        return base_result

    private_port = _private_port(owned_input, base_result)
    statement_root = owned_input.statement_root
    module_journal = _bound_journal(statement_root, base_result, private_port)
    return AssetTransferLaneModuleAcceptedV1(
        statement_root,
        base_result.post_state,
        base_result.effects,
        module_journal,
        private_port,
    )


def transition_asset_transfer_lane_module_v1(
    module_input: AssetTransferLaneModuleInputV1,
) -> AssetTransferLaneModuleResultV1:
    """Run one bound module transition with exact reject-as-no-op semantics."""

    return _transition_owned_asset_transfer_lane_module_v1(
        _snapshot_asset_transfer_lane_module_input_v1(module_input)
    )


def _recompute_asset_transfer_lane_module_accepted_v1(
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> tuple[AssetTransferLaneModuleInputV1, AssetTransferLaneModuleAcceptedV1]:
    owned_input = _snapshot_asset_transfer_lane_module_input_v1(module_input)
    expected = _transition_owned_asset_transfer_lane_module_v1(owned_input)
    if type(expected) is not AssetTransferLaneModuleAcceptedV1:
        raise ValueError("asset transfer supplied acceptance recomputes to rejection")
    supplied = _snapshot_asset_transfer_lane_module_accepted_v1(accepted)
    if supplied != expected:
        raise ValueError("asset transfer supplied acceptance differs from recomputation")
    return owned_input, expected


__all__ = [
    "ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1",
    "AssetTransferLaneModuleInputV1",
    "AssetTransferLaneModuleAcceptedV1",
    "AssetTransferLaneModuleResultV1",
    "transition_asset_transfer_lane_module_v1",
]
