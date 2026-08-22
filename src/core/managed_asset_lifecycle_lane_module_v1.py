"""Guest-ready bound output for ordinary managed-asset issue and burn.

Accepted transitions own their common asset-lane private port and rebound
module journal. Rejections are the exact lifecycle-core no-op. The deterministic
receipt root is a statement commitment and grants no proof or publication
authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final, TypeAlias

from .asset_lane_projection_v1 import (
    AssetLanePrivatePortV1,
    _snapshot_asset_lane_private_port_v1,
    project_managed_asset_lifecycle_state_v1,
)
from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _require_exact_tuple_items,
    _snapshot_dataclass_tuple_v1,
    _snapshot_effect_plan_v1,
)
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    _require_ordered_objects,
    _require_root,
    hash_global_v1,
)
from .managed_asset_lifecycle_module_v1 import transition_managed_asset_lifecycle_v1
from .managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
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
        if type(self.context) is not ManagedAssetLifecycleContextV1:
            raise TypeError("managed asset lane module context must have the exact typed value")
        if type(self.pre_state) is not ManagedAssetLifecycleStateV1:
            raise TypeError("managed asset lane module pre-state must have the exact typed value")
        if type(self.command) is not ManagedAssetLifecycleCommandV1:
            raise TypeError("managed asset lane module command must have the exact typed value")
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


def _snapshot_managed_policies_v1(
    policies: object,
) -> tuple[ManagedAssetLifecyclePolicyV1, ...]:
    snapshots = []
    for policy in _require_exact_tuple_items(
        policies,
        ManagedAssetLifecyclePolicyV1,
        "managed asset policies",
    ):
        if type(policy.asset) is not str:
            raise TypeError("managed asset policy asset must be an exact string")
        if type(policy.asset_class) is not ManagedAssetClassV1:
            raise TypeError("managed asset policy class must be an exact closed value")
        for field_name in (
            "issue_authority_subject",
            "issue_policy_root",
            "burn_policy_root",
        ):
            item = getattr(policy, field_name)
            if item is not None and type(item) is not str:
                raise TypeError(f"managed asset policy {field_name} must be exact text")
        if type(policy.enabled) is not bool:
            raise TypeError("managed asset policy enabled must be an exact bool")
        snapshots.append(replace(policy))
    return tuple(snapshots)


def _snapshot_managed_asset_lifecycle_state_v1(
    state: ManagedAssetLifecycleStateV1,
) -> ManagedAssetLifecycleStateV1:
    _require_exact_dataclass_scalars_v1(
        state,
        name="managed asset state",
        tuple_fields=frozenset({"policies", "balances", "supplies"}),
    )
    return replace(
        state,
        policies=_snapshot_managed_policies_v1(state.policies),
        balances=_snapshot_dataclass_tuple_v1(
            state.balances,
            EconomicAmountV1,
            "managed asset balances",
        ),
        supplies=_snapshot_dataclass_tuple_v1(
            state.supplies,
            AssetSupplyV1,
            "managed asset supplies",
        ),
    )


def _snapshot_managed_asset_lifecycle_lane_module_input_v1(
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecycleLaneModuleInputV1:
    """Own one exact, revalidated input before execution or authority binding."""

    if type(module_input) is not ManagedAssetLifecycleLaneModuleInputV1:
        raise TypeError("managed asset lifecycle lane input must have the exact typed value")
    if type(module_input.context) is not ManagedAssetLifecycleContextV1:
        raise TypeError("managed asset lane module context must have the exact typed value")
    if type(module_input.pre_state) is not ManagedAssetLifecycleStateV1:
        raise TypeError("managed asset lane module pre-state must have the exact typed value")
    if type(module_input.command) is not ManagedAssetLifecycleCommandV1:
        raise TypeError("managed asset lane module command must have the exact typed value")
    if type(module_input.asset_policy_registry_root) is not str:
        raise TypeError("managed asset asset-policy root must be an exact string")
    if type(module_input.fee_policy_registry_root) is not str:
        raise TypeError("managed asset fee-policy root must be an exact string")

    _require_exact_dataclass_scalars_v1(
        module_input.context,
        name="managed asset context",
    )
    _require_exact_dataclass_scalars_v1(
        module_input.command,
        name="managed asset command",
    )
    return ManagedAssetLifecycleLaneModuleInputV1(
        context=replace(module_input.context),
        pre_state=_snapshot_managed_asset_lifecycle_state_v1(module_input.pre_state),
        command=replace(module_input.command),
        asset_policy_registry_root=module_input.asset_policy_registry_root,
        fee_policy_registry_root=module_input.fee_policy_registry_root,
        custody=_snapshot_dataclass_tuple_v1(
            module_input.custody,
            EconomicAmountV1,
            "managed asset custody",
        ),
    )


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


def _snapshot_managed_asset_lifecycle_lane_module_accepted_v1(
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> ManagedAssetLifecycleLaneModuleAcceptedV1:
    if type(accepted) is not ManagedAssetLifecycleLaneModuleAcceptedV1:
        raise TypeError("managed lifecycle accepted output must have the exact typed value")
    if type(accepted.statement_root) is not str:
        raise TypeError("managed lifecycle accepted statement root must be exact text")
    if type(accepted.post_state) is not ManagedAssetLifecycleStateV1:
        raise TypeError("managed lifecycle accepted state must have the exact typed value")
    if type(accepted.effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("managed lifecycle accepted effects must have the exact typed value")
    if type(accepted.module_journal) is not LaneModuleTransitionJournalV1:
        raise TypeError("managed lifecycle accepted journal must have the exact typed value")
    _require_exact_dataclass_scalars_v1(
        accepted.module_journal,
        name="managed lifecycle accepted journal",
    )
    return ManagedAssetLifecycleLaneModuleAcceptedV1(
        statement_root=accepted.statement_root,
        post_state=_snapshot_managed_asset_lifecycle_state_v1(accepted.post_state),
        effects=_snapshot_effect_plan_v1(accepted.effects),
        module_journal=replace(accepted.module_journal),
        private_port=_snapshot_asset_lane_private_port_v1(accepted.private_port),
    )


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


def _transition_owned_managed_asset_lifecycle_lane_module_v1(
    owned_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecycleLaneModuleResultV1:
    base_result = transition_managed_asset_lifecycle_v1(
        owned_input.context,
        owned_input.pre_state,
        owned_input.command,
    )
    if isinstance(base_result, ManagedAssetLifecycleRejectedV1):
        return base_result
    private_port = _private_port(owned_input, base_result)
    statement_root = owned_input.statement_root
    return ManagedAssetLifecycleLaneModuleAcceptedV1(
        statement_root,
        base_result.post_state,
        base_result.effects,
        _bound_journal(statement_root, base_result, private_port),
        private_port,
    )


def transition_managed_asset_lifecycle_lane_module_v1(
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecycleLaneModuleResultV1:
    """Run one bound issue or burn transition with exact reject no-op semantics."""

    return _transition_owned_managed_asset_lifecycle_lane_module_v1(
        _snapshot_managed_asset_lifecycle_lane_module_input_v1(module_input)
    )


def _recompute_managed_asset_lifecycle_lane_module_accepted_v1(
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
    accepted: ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> tuple[
    ManagedAssetLifecycleLaneModuleInputV1,
    ManagedAssetLifecycleLaneModuleAcceptedV1,
]:
    owned_input = _snapshot_managed_asset_lifecycle_lane_module_input_v1(module_input)
    expected = _transition_owned_managed_asset_lifecycle_lane_module_v1(owned_input)
    if type(expected) is not ManagedAssetLifecycleLaneModuleAcceptedV1:
        raise ValueError("managed lifecycle supplied acceptance recomputes to rejection")
    supplied = _snapshot_managed_asset_lifecycle_lane_module_accepted_v1(accepted)
    if supplied != expected:
        raise ValueError("managed lifecycle supplied acceptance differs from recomputation")
    return owned_input, expected


__all__ = [
    "MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1",
    "ManagedAssetLifecycleLaneModuleAcceptedV1",
    "ManagedAssetLifecycleLaneModuleInputV1",
    "ManagedAssetLifecycleLaneModuleResultV1",
    "transition_managed_asset_lifecycle_lane_module_v1",
]
