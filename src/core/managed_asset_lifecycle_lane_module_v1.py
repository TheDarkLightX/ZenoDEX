"""Guest-ready bound output for ordinary managed-asset issue and burn.

Accepted transitions own their common asset-lane private port and rebound
module journal. Rejections are the exact lifecycle-core no-op. The deterministic
receipt root is a statement commitment and grants no proof or publication
authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final, TypeAlias

from .asset_lane_projection_v1 import (
    AssetLanePrivatePortV1,
    project_managed_asset_lifecycle_state_v1,
)
from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    _require_ordered_objects,
    _require_root,
    hash_global_v1,
)
from .managed_asset_lifecycle_module_v1 import transition_managed_asset_lifecycle_v1
from .managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)

MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1: Final = (
    "zenodex/managed-asset-lifecycle-lane-module-input/v1"
)


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleLaneModuleInputV1:
    """Complete deterministic input for one lifecycle-module guest transition."""

    context: ManagedAssetLifecycleContextV1
    pre_state: ManagedAssetLifecycleStateV1
    command: ManagedAssetLifecycleCommandV1
    asset_policy_registry_root: str
    fee_policy_registry_root: str
    custody: tuple[EconomicAmountV1, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.context, ManagedAssetLifecycleContextV1):
            raise TypeError("managed asset lane module context must be typed")
        if not isinstance(self.pre_state, ManagedAssetLifecycleStateV1):
            raise TypeError("managed asset lane module pre-state must be typed")
        if not isinstance(self.command, ManagedAssetLifecycleCommandV1):
            raise TypeError("managed asset lane module command must be typed")
        _require_root(
            self.asset_policy_registry_root,
            name="managed asset lane module asset policy registry",
        )
        _require_root(
            self.fee_policy_registry_root,
            name="managed asset lane module fee policy registry",
        )
        _require_ordered_objects(
            self.custody,
            name="managed asset lane module custody",
            expected_type=EconomicAmountV1,
            key="key",
        )
        project_managed_asset_lifecycle_state_v1(
            self.pre_state,
            asset_policy_registry_root=self.asset_policy_registry_root,
            fee_policy_registry_root=self.fee_policy_registry_root,
            custody=self.custody,
        )

    @property
    def statement_root(self) -> str:
        return hash_global_v1(
            "managed-asset-lifecycle-lane-module-statement-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1,
            "context": self.context,
            "pre_state": self.pre_state,
            "command": self.command,
            "asset_policy_registry_root": self.asset_policy_registry_root,
            "fee_policy_registry_root": self.fee_policy_registry_root,
            "custody": self.custody,
        }


def _receipt_root(
    statement_root: str,
    module_journal: LaneModuleTransitionJournalV1,
    private_port: AssetLanePrivatePortV1,
    effects: GlobalEconomicEffectPlanV1,
) -> str:
    return hash_global_v1(
        "managed-asset-lifecycle-lane-module-receipt-v1",
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
class ManagedAssetLifecycleLaneModuleAcceptedV1:
    """Accepted lifecycle transition with its module-owned lane output."""

    statement_root: str
    post_state: ManagedAssetLifecycleStateV1
    effects: GlobalEconomicEffectPlanV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: AssetLanePrivatePortV1

    def __post_init__(self) -> None:
        _require_root(self.statement_root, name="managed asset lane module statement")
        ManagedAssetLifecycleAcceptedV1(self.post_state, self.effects, self.module_journal)
        if not isinstance(self.private_port, AssetLanePrivatePortV1):
            raise TypeError("managed asset lane module private port must be typed")
        if self.private_port.producer_module_schema != MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1:
            raise ValueError("managed asset lane module producer schema mismatch")
        if self.private_port.module_release_id != self.module_journal.module_release_id:
            raise ValueError("managed asset lane module release mismatch")
        if self.private_port.command_occurrence_id != self.module_journal.command_occurrence_id:
            raise ValueError("managed asset lane module occurrence mismatch")
        if self.private_port.module_effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("managed asset lane module effect-plan mismatch")
        if self.module_journal.private_port_root != self.private_port.port_root:
            raise ValueError("managed asset lane module private-port root mismatch")
        if self.module_journal.terminal_obligations_root != self.private_port.terminal_obligations_root:
            raise ValueError("managed asset lane module terminal obligations mismatch")
        if self.private_port.post_state.balances != self.post_state.balances:
            raise ValueError("managed asset lane module post-balance projection mismatch")
        if self.private_port.post_state.supplies != self.post_state.supplies:
            raise ValueError("managed asset lane module post-supply projection mismatch")
        if self.module_journal.receipt_root != _receipt_root(
            self.statement_root,
            self.module_journal,
            self.private_port,
            self.effects,
        ):
            raise ValueError("managed asset lane module receipt root mismatch")

    @property
    def receipt_root(self) -> str:
        return self.module_journal.receipt_root


ManagedAssetLifecycleLaneModuleResultV1: TypeAlias = (
    ManagedAssetLifecycleLaneModuleAcceptedV1 | ManagedAssetLifecycleRejectedV1
)


def _private_port(
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
    base_result: ManagedAssetLifecycleAcceptedV1,
) -> AssetLanePrivatePortV1:
    project = project_managed_asset_lifecycle_state_v1
    pre_projection = project(
        module_input.pre_state,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=module_input.custody,
    )
    post_projection = project(
        base_result.post_state,
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=module_input.custody,
    )
    return AssetLanePrivatePortV1(
        producer_module_schema=MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
        module_release_id=module_input.context.module_release_id,
        command_occurrence_id=module_input.context.command_occurrence_id,
        pre_state=pre_projection,
        post_state=post_projection,
        module_effect_plan_root=base_result.effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )


def _bound_journal(
    statement_root: str,
    base_result: ManagedAssetLifecycleAcceptedV1,
    private_port: AssetLanePrivatePortV1,
) -> LaneModuleTransitionJournalV1:
    base = base_result.module_journal
    return LaneModuleTransitionJournalV1(
        chain_id=base.chain_id,
        deployment_root=base.deployment_root,
        profile_root=base.profile_root,
        writer_epoch=base.writer_epoch,
        lane_id=base.lane_id,
        module_release_id=base.module_release_id,
        command_occurrence_id=base.command_occurrence_id,
        pre_lane_root=base.pre_lane_root,
        post_lane_root=base.post_lane_root,
        effect_plan_root=base.effect_plan_root,
        private_port_root=private_port.port_root,
        receipt_root=_receipt_root(
            statement_root,
            base,
            private_port,
            base_result.effects,
        ),
        terminal_obligations_root=base.terminal_obligations_root,
    )


def transition_managed_asset_lifecycle_lane_module_v1(
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecycleLaneModuleResultV1:
    """Run one bound issue or burn transition with exact reject no-op semantics."""

    if not isinstance(module_input, ManagedAssetLifecycleLaneModuleInputV1):
        raise TypeError("managed asset lifecycle lane module input must be typed")
    base_result = transition_managed_asset_lifecycle_v1(
        module_input.context,
        module_input.pre_state,
        module_input.command,
    )
    if isinstance(base_result, ManagedAssetLifecycleRejectedV1):
        return base_result
    private_port = _private_port(module_input, base_result)
    statement_root = module_input.statement_root
    return ManagedAssetLifecycleLaneModuleAcceptedV1(
        statement_root,
        base_result.post_state,
        base_result.effects,
        _bound_journal(statement_root, base_result, private_port),
        private_port,
    )


__all__ = [
    "MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1",
    "ManagedAssetLifecycleLaneModuleAcceptedV1",
    "ManagedAssetLifecycleLaneModuleInputV1",
    "ManagedAssetLifecycleLaneModuleResultV1",
    "transition_managed_asset_lifecycle_lane_module_v1",
]
