"""Command and result values for the managed-asset lifecycle V2 SHADOW core."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final, cast

from .asset_transfer_types_v2 import ASSET_ATOM_DECIMALS_V2
from .global_economic_proof_v2 import (
    LaneModuleTransitionJournalV2,
    _snapshot_module_journal_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_atoms_u128_v2,
    _require_root_v2,
    _require_token_v2,
    hash_economic_command_body_v2,
)
from .managed_asset_lifecycle_state_v2 import (
    ManagedAssetClassV2,
    ManagedAssetLifecycleStateV2,
    _require_optional_root,
    _snapshot_state_v2,
)

MANAGED_ASSET_ISSUE_COMMAND_KIND_V2: Final = "managed_asset_issue"
MANAGED_ASSET_BURN_COMMAND_KIND_V2: Final = "managed_asset_burn"
MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2: Final = "NONE"


class ManagedAssetLifecycleRejectCodeV2(str, Enum):
    MISSING_OCCURRENCE = "MISSING_OCCURRENCE"
    OCCURRENCE_BINDING_MISMATCH = "OCCURRENCE_BINDING_MISMATCH"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    OCCURRENCE_COMMAND_MISMATCH = "OCCURRENCE_COMMAND_MISMATCH"
    UNKNOWN_ASSET = "UNKNOWN_ASSET"
    DISABLED_ASSET = "DISABLED_ASSET"
    ASSET_CLASS_MISMATCH = "ASSET_CLASS_MISMATCH"
    ASSET_DECIMALS_MISMATCH = "ASSET_DECIMALS_MISMATCH"
    UNREGISTERED_ASSET = "UNREGISTERED_ASSET"
    ASSET_ORIGIN_MISMATCH = "ASSET_ORIGIN_MISMATCH"
    GENERIC_AUTHORITY_FORBIDDEN = "GENERIC_AUTHORITY_FORBIDDEN"
    ISSUE_DISABLED = "ISSUE_DISABLED"
    BURN_DISABLED = "BURN_DISABLED"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    AUTHORIZATION_ROOT_MISMATCH = "AUTHORIZATION_ROOT_MISMATCH"
    ZERO_AMOUNT = "ZERO_AMOUNT"
    EFFECT_DELTA_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"
    SUPPLY_OVERFLOW = "SUPPLY_OVERFLOW"


@dataclass(frozen=True, slots=True)
class ManagedAssetLifecycleCommandV2:
    command_kind: str
    asset: str
    asset_class: ManagedAssetClassV2
    asset_origin_root: str | None
    atom_decimals: int
    authorization_root: str | None
    account_owner: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.command_kind, name="managed asset command kind")
        _require_token_v2(self.asset, name="managed asset command asset")
        if type(self.asset_class) is not ManagedAssetClassV2:
            raise TypeError("managed asset command class must be exact")
        _require_optional_root(self.asset_origin_root, name="managed asset command origin")
        if type(self.atom_decimals) is not int or self.atom_decimals != ASSET_ATOM_DECIMALS_V2:
            raise ValueError("managed asset command decimals must equal 8")
        _require_optional_root(
            self.authorization_root,
            name="managed asset command authorization root",
        )
        _require_token_v2(self.account_owner, name="managed asset command account owner")
        _require_atoms_u128_v2(self.amount_atoms, name="managed asset command amount")

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "asset": self.asset,
            "asset_class": self.asset_class,
            "asset_origin_root": self.asset_origin_root,
            "atom_decimals": self.atom_decimals,
            "authorization_root": self.authorization_root,
            "account_owner": self.account_owner,
            "amount_atoms": self.amount_atoms,
        }

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v2(self.command_kind, self)


def _snapshot_command_v2(
    command: ManagedAssetLifecycleCommandV2,
) -> ManagedAssetLifecycleCommandV2:
    if type(command) is not ManagedAssetLifecycleCommandV2:
        raise TypeError("managed asset command must be an exact typed value")
    return replace(command)


def _snapshot_effect_plan_v2(
    effect_plan: GlobalEconomicEffectPlanV2,
) -> GlobalEconomicEffectPlanV2:
    if type(effect_plan) is not GlobalEconomicEffectPlanV2:
        raise TypeError("managed asset effect plan must be an exact typed value")
    return GlobalEconomicEffectPlanV2(
        rows=effect_plan.rows,
        asset_conservation=effect_plan.asset_conservation,
        fee_conservation=effect_plan.fee_conservation,
        lane_writes=effect_plan.lane_writes,
        occurrence_consumptions=effect_plan.occurrence_consumptions,
        external_outbox_enqueue=effect_plan.external_outbox_enqueue,
    )


@dataclass(frozen=True, slots=True, init=False)
class ManagedAssetLifecycleAcceptedV2:
    _post_state: ManagedAssetLifecycleStateV2
    _effects: GlobalEconomicEffectPlanV2
    _module_journal: LaneModuleTransitionJournalV2

    def __init__(
        self,
        post_state: ManagedAssetLifecycleStateV2 | None = None,
        effects: GlobalEconomicEffectPlanV2 | None = None,
        module_journal: LaneModuleTransitionJournalV2 | None = None,
        *,
        _post_state: ManagedAssetLifecycleStateV2 | None = None,
        _effects: GlobalEconomicEffectPlanV2 | None = None,
        _module_journal: LaneModuleTransitionJournalV2 | None = None,
    ) -> None:
        selected_post_state = post_state if post_state is not None else _post_state
        selected_effects = effects if effects is not None else _effects
        selected_journal = module_journal if module_journal is not None else _module_journal
        if type(selected_post_state) is not ManagedAssetLifecycleStateV2:
            raise TypeError("managed asset accepted state is invalid")
        if type(selected_effects) is not GlobalEconomicEffectPlanV2:
            raise TypeError("managed asset accepted effects are invalid")
        if type(selected_journal) is not LaneModuleTransitionJournalV2:
            raise TypeError("managed asset accepted journal is invalid")
        object.__setattr__(
            self,
            "_post_state",
            _snapshot_state_v2(selected_post_state),
        )
        object.__setattr__(self, "_effects", _snapshot_effect_plan_v2(selected_effects))
        object.__setattr__(
            self,
            "_module_journal",
            _snapshot_module_journal_v2(selected_journal),
        )
        if self._effects.is_empty:
            raise ValueError("managed asset acceptance requires effects")
        if self._module_journal.lane_id is not LaneIdV2.ASSET_TRANSFER:
            raise ValueError("managed asset journal has the wrong lane")
        if self._module_journal.module_release_id != self._post_state.module_release_id:
            raise ValueError("managed asset journal has the wrong module release")
        if self._module_journal.post_lane_root != self._post_state.state_root:
            raise ValueError("managed asset journal has the wrong post-state root")
        if self._module_journal.effect_plan_root != self._effects.effect_plan_root:
            raise ValueError("managed asset journal has the wrong effect root")
        if self._effects.occurrence_consumptions != (self._module_journal.command_occurrence_id,):
            raise ValueError("managed asset effects have the wrong occurrence")
        if self._effects.lane_writes != (
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                self._module_journal.pre_lane_root,
                self._module_journal.post_lane_root,
            ),
        ):
            raise ValueError("managed asset effects have the wrong lane write")
        if (
            self._module_journal.private_port_root != ZERO_ROOT_V2
            or self._module_journal.terminal_obligations_root != ZERO_ROOT_V2
            or self._module_journal.oracle_occurrence_plan_root != ZERO_ROOT_V2
        ):
            raise ValueError("managed asset leaf must have zero external roots")

    @property
    def post_state(self) -> ManagedAssetLifecycleStateV2:
        return _snapshot_state_v2(self._post_state)

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effect_plan_v2(self._effects)

    @property
    def module_journal(self) -> LaneModuleTransitionJournalV2:
        return _snapshot_module_journal_v2(self._module_journal)

    @property
    def receipt_root(self) -> str:
        return self._module_journal.receipt_root

    @property
    def production_authority(self) -> str:
        return MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2


@dataclass(frozen=True, slots=True, init=False)
class ManagedAssetLifecycleRejectedV2:
    code: ManagedAssetLifecycleRejectCodeV2
    pre_state_root: str
    post_state_root: str
    _effects: GlobalEconomicEffectPlanV2

    def __init__(
        self,
        code: ManagedAssetLifecycleRejectCodeV2,
        pre_state_root: str,
        post_state_root: str,
        effects: GlobalEconomicEffectPlanV2 | None = None,
        *,
        _effects: GlobalEconomicEffectPlanV2 | None = None,
    ) -> None:
        selected_effects = effects if effects is not None else _effects
        object.__setattr__(self, "code", code)
        object.__setattr__(self, "pre_state_root", pre_state_root)
        object.__setattr__(self, "post_state_root", post_state_root)
        if type(self.code) is not ManagedAssetLifecycleRejectCodeV2:
            raise TypeError("managed asset rejection code is not closed")
        _require_root_v2(self.pre_state_root, name="managed asset rejected pre-state")
        _require_root_v2(self.post_state_root, name="managed asset rejected post-state")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("managed asset rejection changed state")
        if type(selected_effects) is not GlobalEconomicEffectPlanV2:
            raise ValueError("managed asset rejection carried effects")
        owned_effects = cast(GlobalEconomicEffectPlanV2, selected_effects)
        if not owned_effects.is_empty:
            raise ValueError("managed asset rejection carried effects")
        object.__setattr__(self, "_effects", _snapshot_effect_plan_v2(owned_effects))

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effect_plan_v2(self._effects)

    @property
    def terminal_obligations_root(self) -> str:
        return ZERO_ROOT_V2

    @property
    def oracle_occurrence_plan_root(self) -> str:
        return ZERO_ROOT_V2

    @property
    def production_authority(self) -> str:
        return MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2


ManagedAssetLifecycleResultV2 = ManagedAssetLifecycleAcceptedV2 | ManagedAssetLifecycleRejectedV2


__all__ = [
    "MANAGED_ASSET_ISSUE_COMMAND_KIND_V2",
    "MANAGED_ASSET_BURN_COMMAND_KIND_V2",
    "MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2",
    "ManagedAssetLifecycleRejectCodeV2",
    "ManagedAssetLifecycleCommandV2",
    "ManagedAssetLifecycleAcceptedV2",
    "ManagedAssetLifecycleRejectedV2",
    "ManagedAssetLifecycleResultV2",
    "_snapshot_command_v2",
]
