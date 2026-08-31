"""Closed V2 values for the research-only asset-transfer functional core."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    LaneModuleTransitionJournalV2,
    _snapshot_module_journal_v2,
    _snapshot_occurrence_v2,
)
from .global_settlement_resource_limits_v2 import (
    MAX_ASSETS_PER_ASSET_STATE_V2,
    MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
    require_raw_tuple_ceiling_v2,
    require_rootable_asset_state_bytes_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_atoms_u128_v2,
    _require_bool_v2,
    _require_nonnegative_int_v2,
    _require_ordered_objects_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    canonical_global_bytes_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)

ASSET_TRANSFER_MODULE_SCHEMA_V2: Final = "zenodex/asset-transfer-module/v2"
ASSET_TRANSFER_COMMAND_KIND_V2: Final = "asset_transfer"
ACCOUNT_CUSTODY_DOMAIN_V2: Final = "accounts"
ASSET_ATOM_DECIMALS_V2: Final = 8
ASSET_LANE_PRODUCTION_AUTHORITY_V2: Final = "NONE"
MAX_ASSET_TRANSFER_ASSETS_V2: Final = MAX_ASSETS_PER_ASSET_STATE_V2
MAX_ASSET_TRANSFER_BALANCE_ROWS_V2: Final = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
MAX_ASSET_TRANSFER_STATE_CANONICAL_BYTES_V2: Final = (
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
)
_UNSET_OWNED_VALUE_V2: Final = object()


class AssetClassV2(str, Enum):
    TAU_NATIVE_COIN = "tau_native_coin"
    CANONICAL_ZUSD = "canonical_zusd"
    LP_SHARE = "lp_share"
    ZDEX_PROTOCOL_TOKEN = "zdex_protocol_token"
    SEALED_BID_PAYMENT_OR_INVENTORY = "sealed_bid_payment_or_inventory"
    REGISTERED_ORDINARY_TOKEN = "registered_ordinary_token"


_PROTECTED_ASSET_CLASSES_BY_ID_V2: Final = {
    "TAU": AssetClassV2.TAU_NATIVE_COIN,
    "ZDEX": AssetClassV2.ZDEX_PROTOCOL_TOKEN,
    "zUSD": AssetClassV2.CANONICAL_ZUSD,
}


def require_asset_class_namespace_v2(asset: str, asset_class: AssetClassV2) -> None:
    """Reject known protocol identifiers relabelled as ordinary assets."""

    if type(asset) is not str:
        raise TypeError("asset identifier must be exact text")
    if type(asset_class) is not AssetClassV2:
        raise TypeError("asset class must be an exact closed value")
    expected = _PROTECTED_ASSET_CLASSES_BY_ID_V2.get(asset)
    if asset.startswith("LP-"):
        expected = AssetClassV2.LP_SHARE
    if expected is not None and asset_class is not expected:
        raise ValueError("protected asset identifier has the wrong asset class")


class AssetTransferRejectCodeV2(str, Enum):
    MISSING_OCCURRENCE = "MISSING_OCCURRENCE"
    OCCURRENCE_BINDING_MISMATCH = "OCCURRENCE_BINDING_MISMATCH"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    OCCURRENCE_COMMAND_MISMATCH = "OCCURRENCE_COMMAND_MISMATCH"
    UNKNOWN_ASSET = "UNKNOWN_ASSET"
    DISABLED_ASSET = "DISABLED_ASSET"
    UNREGISTERED_ASSET = "UNREGISTERED_ASSET"
    ASSET_ORIGIN_MISMATCH = "ASSET_ORIGIN_MISMATCH"
    NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED = "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    SELF_TRANSFER = "SELF_TRANSFER"
    ZERO_AMOUNT = "ZERO_AMOUNT"
    FEE_LIMIT_EXCEEDED = "FEE_LIMIT_EXCEEDED"
    EFFECT_DELTA_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
    INSUFFICIENT_BALANCE = "INSUFFICIENT_BALANCE"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"


@dataclass(frozen=True, slots=True, order=True)
class AssetTransferPolicyV2:
    asset: str
    fee_owner: str
    transfer_fee_atoms: int
    enabled: bool
    asset_class: AssetClassV2
    asset_origin_root: str | None
    atom_decimals: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="asset transfer policy asset")
        _require_token_v2(self.fee_owner, name="asset transfer policy fee owner")
        _require_atoms_u128_v2(
            self.transfer_fee_atoms,
            name="asset transfer policy fee atoms",
        )
        _require_bool_v2(self.enabled, name="asset transfer policy enabled")
        if type(self.asset_class) is not AssetClassV2:
            raise TypeError("asset transfer policy class must be exact")
        if self.asset_origin_root is not None:
            _require_root_v2(
                self.asset_origin_root,
                name="asset transfer policy origin root",
            )
        if type(self.atom_decimals) is not int or (self.atom_decimals != ASSET_ATOM_DECIMALS_V2):
            raise ValueError(f"asset transfer atom decimals must equal {ASSET_ATOM_DECIMALS_V2}")
        require_asset_class_namespace_v2(self.asset, self.asset_class)

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "fee_owner": self.fee_owner,
            "transfer_fee_atoms": self.transfer_fee_atoms,
            "enabled": self.enabled,
            "asset_class": self.asset_class,
            "asset_origin_root": self.asset_origin_root,
            "atom_decimals": self.atom_decimals,
        }


@dataclass(frozen=True, slots=True, init=False)
class AssetTransferStateV2:
    module_release_id: str
    _policies: tuple[AssetTransferPolicyV2, ...]
    _balances: tuple[EconomicAmountV2, ...]
    _supplies: tuple[AssetSupplyV2, ...]

    def __init__(
        self,
        module_release_id: str,
        policies: tuple[AssetTransferPolicyV2, ...] | None = None,
        balances: tuple[EconomicAmountV2, ...] | None = None,
        supplies: tuple[AssetSupplyV2, ...] | None = None,
        *,
        _policies: tuple[AssetTransferPolicyV2, ...] | None = None,
        _balances: tuple[EconomicAmountV2, ...] | None = None,
        _supplies: tuple[AssetSupplyV2, ...] | None = None,
    ) -> None:
        selected_policies = policies if policies is not None else _policies
        selected_balances = balances if balances is not None else _balances
        selected_supplies = supplies if supplies is not None else _supplies
        if selected_policies is None or selected_balances is None or selected_supplies is None:
            raise TypeError("asset transfer state requires all owned tables")
        require_raw_tuple_ceiling_v2(
            selected_policies,
            name="asset transfer policies",
            ceiling=MAX_ASSET_TRANSFER_ASSETS_V2,
        )
        require_raw_tuple_ceiling_v2(
            selected_balances,
            name="asset transfer balances",
            ceiling=MAX_ASSET_TRANSFER_BALANCE_ROWS_V2,
        )
        require_raw_tuple_ceiling_v2(
            selected_supplies,
            name="asset transfer supplies",
            ceiling=MAX_ASSET_TRANSFER_ASSETS_V2,
        )
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(
            self,
            "_policies",
            _snapshot_dataclass_tuple_v2(
                selected_policies,
                AssetTransferPolicyV2,
                "asset transfer policies",
            ),
        )
        object.__setattr__(
            self,
            "_balances",
            _snapshot_dataclass_tuple_v2(
                selected_balances,
                EconomicAmountV2,
                "asset transfer balances",
            ),
        )
        object.__setattr__(
            self,
            "_supplies",
            _snapshot_dataclass_tuple_v2(
                selected_supplies,
                AssetSupplyV2,
                "asset transfer supplies",
            ),
        )
        _require_root_v2(
            self.module_release_id,
            name="asset transfer module release id",
        )
        _require_ordered_objects_v2(
            self._policies,
            name="asset transfer policies",
            expected_type=AssetTransferPolicyV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self._balances,
            name="asset transfer balances",
            expected_type=EconomicAmountV2,
            key="key",
        )
        _require_ordered_objects_v2(
            self._supplies,
            name="asset transfer supplies",
            expected_type=AssetSupplyV2,
            key="asset",
        )
        policy_assets = tuple(policy.asset for policy in self._policies)
        if tuple(supply.asset for supply in self._supplies) != policy_assets:
            raise ValueError("asset transfer policies and supplies must cover the same assets")
        totals = {asset: 0 for asset in policy_assets}
        for balance in self._balances:
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2:
                raise ValueError("asset transfer balance has the wrong custody domain")
            if balance.amount_atoms == 0:
                raise ValueError("asset transfer state must omit zero balances")
            if balance.asset not in totals:
                raise ValueError("asset transfer balance references an unknown asset")
            totals[balance.asset] += balance.amount_atoms
        for supply in self._supplies:
            if totals[supply.asset] > supply.amount_atoms:
                raise ValueError("asset transfer account balances exceed supply")
        require_rootable_asset_state_bytes_v2(
            canonical_global_bytes_v2(self.to_canonical()),
            name="asset transfer state",
        )

    @property
    def policies(self) -> tuple[AssetTransferPolicyV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._policies,
            AssetTransferPolicyV2,
            "asset transfer policies",
        )

    @property
    def balances(self) -> tuple[EconomicAmountV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._balances,
            EconomicAmountV2,
            "asset transfer balances",
        )

    @property
    def supplies(self) -> tuple[AssetSupplyV2, ...]:
        return _snapshot_dataclass_tuple_v2(
            self._supplies,
            AssetSupplyV2,
            "asset transfer supplies",
        )

    @property
    def state_root(self) -> str:
        return hash_global_v2("asset-transfer-state-v2", self.to_canonical())

    def balance_atoms(self, owner: str, asset: str) -> int:
        _require_token_v2(owner, name="asset transfer balance owner")
        _require_token_v2(asset, name="asset transfer balance asset")
        for row in self._balances:
            if row.owner == owner and row.asset == asset:
                return row.amount_atoms
        return 0

    def supply_atoms(self, asset: str) -> int:
        _require_token_v2(asset, name="asset transfer supply asset")
        for row in self._supplies:
            if row.asset == asset:
                return row.amount_atoms
        raise ValueError("unknown asset transfer supply")

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_TRANSFER_MODULE_SCHEMA_V2,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
            "balances": self.balances,
            "supplies": self.supplies,
        }


@dataclass(frozen=True, slots=True, init=False)
class AssetTransferContextV2:
    writer_epoch: int
    module_release_id: str
    global_pre_state_root: str
    _occurrence: EconomicCommandOccurrenceV2 | None

    def __init__(
        self,
        writer_epoch: int,
        module_release_id: str,
        global_pre_state_root: str,
        occurrence: EconomicCommandOccurrenceV2 | None | object = _UNSET_OWNED_VALUE_V2,
        *,
        _occurrence: EconomicCommandOccurrenceV2 | None | object = _UNSET_OWNED_VALUE_V2,
    ) -> None:
        selected_occurrence = occurrence if occurrence is not _UNSET_OWNED_VALUE_V2 else _occurrence
        if selected_occurrence is _UNSET_OWNED_VALUE_V2:
            raise TypeError("asset transfer context requires an occurrence field")
        object.__setattr__(self, "writer_epoch", writer_epoch)
        object.__setattr__(self, "module_release_id", module_release_id)
        object.__setattr__(self, "global_pre_state_root", global_pre_state_root)
        _require_nonnegative_int_v2(
            self.writer_epoch,
            name="asset transfer context writer epoch",
        )
        _require_root_v2(
            self.module_release_id,
            name="asset transfer context module release",
        )
        _require_root_v2(
            self.global_pre_state_root,
            name="asset transfer context global pre-state root",
        )
        if selected_occurrence is not None:
            if type(selected_occurrence) is not EconomicCommandOccurrenceV2:
                raise TypeError("asset transfer occurrence must have the exact typed value")
            object.__setattr__(
                self,
                "_occurrence",
                _snapshot_occurrence_v2(selected_occurrence),
            )
        else:
            object.__setattr__(self, "_occurrence", None)

    @property
    def occurrence(self) -> EconomicCommandOccurrenceV2 | None:
        if self._occurrence is None:
            return None
        return _snapshot_occurrence_v2(self._occurrence)

    def to_canonical(self) -> dict[str, object]:
        return {
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "global_pre_state_root": self.global_pre_state_root,
            "occurrence": self.occurrence,
        }


@dataclass(frozen=True, slots=True)
class AssetTransferCommandV2:
    command_kind: str
    asset: str
    sender: str
    recipient: str
    amount_atoms: int
    max_fee_atoms: int
    asset_origin_root: str | None

    def __post_init__(self) -> None:
        _require_token_v2(self.command_kind, name="asset transfer command kind")
        _require_token_v2(self.asset, name="asset transfer command asset")
        _require_token_v2(self.sender, name="asset transfer command sender")
        _require_token_v2(self.recipient, name="asset transfer command recipient")
        _require_atoms_u128_v2(self.amount_atoms, name="asset transfer command amount")
        _require_atoms_u128_v2(
            self.max_fee_atoms,
            name="asset transfer command max fee",
        )
        if self.asset_origin_root is not None:
            _require_root_v2(
                self.asset_origin_root,
                name="asset transfer command origin root",
            )

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "asset": self.asset,
            "sender": self.sender,
            "recipient": self.recipient,
            "amount_atoms": self.amount_atoms,
            "max_fee_atoms": self.max_fee_atoms,
            "asset_origin_root": self.asset_origin_root,
        }

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v2(self.command_kind, self)


def _snapshot_effect_plan_v2(
    effect_plan: GlobalEconomicEffectPlanV2,
) -> GlobalEconomicEffectPlanV2:
    if type(effect_plan) is not GlobalEconomicEffectPlanV2:
        raise TypeError("effect plan must have the exact typed value")
    return GlobalEconomicEffectPlanV2(
        rows=effect_plan.rows,
        asset_conservation=effect_plan.asset_conservation,
        fee_conservation=effect_plan.fee_conservation,
        lane_writes=effect_plan.lane_writes,
        occurrence_consumptions=effect_plan.occurrence_consumptions,
        external_outbox_enqueue=effect_plan.external_outbox_enqueue,
    )


def _snapshot_asset_transfer_state_v2(
    state: AssetTransferStateV2,
) -> AssetTransferStateV2:
    if type(state) is not AssetTransferStateV2:
        raise TypeError("asset transfer state must have the exact typed value")
    return AssetTransferStateV2(
        module_release_id=state.module_release_id,
        policies=state.policies,
        balances=state.balances,
        supplies=state.supplies,
    )


def _snapshot_asset_transfer_context_v2(
    context: AssetTransferContextV2,
) -> AssetTransferContextV2:
    if type(context) is not AssetTransferContextV2:
        raise TypeError("asset transfer context must have the exact typed value")
    return AssetTransferContextV2(
        writer_epoch=context.writer_epoch,
        module_release_id=context.module_release_id,
        global_pre_state_root=context.global_pre_state_root,
        occurrence=context.occurrence,
    )


def _snapshot_asset_transfer_command_v2(
    command: AssetTransferCommandV2,
) -> AssetTransferCommandV2:
    if type(command) is not AssetTransferCommandV2:
        raise TypeError("asset transfer command must have the exact typed value")
    return replace(command)


@dataclass(frozen=True, slots=True, init=False)
class AssetTransferAcceptedV2:
    _post_state: AssetTransferStateV2
    _effects: GlobalEconomicEffectPlanV2
    _module_journal: LaneModuleTransitionJournalV2

    def __init__(
        self,
        post_state: AssetTransferStateV2 | None = None,
        effects: GlobalEconomicEffectPlanV2 | None = None,
        module_journal: LaneModuleTransitionJournalV2 | None = None,
        *,
        _post_state: AssetTransferStateV2 | None = None,
        _effects: GlobalEconomicEffectPlanV2 | None = None,
        _module_journal: LaneModuleTransitionJournalV2 | None = None,
    ) -> None:
        selected_state = post_state if post_state is not None else _post_state
        selected_effects = effects if effects is not None else _effects
        selected_journal = module_journal if module_journal is not None else _module_journal
        if type(selected_state) is not AssetTransferStateV2:
            raise TypeError("asset transfer accepted state is invalid")
        if type(selected_effects) is not GlobalEconomicEffectPlanV2:
            raise TypeError("asset transfer accepted effects are invalid")
        if type(selected_journal) is not LaneModuleTransitionJournalV2:
            raise TypeError("asset transfer module journal is invalid")
        object.__setattr__(
            self,
            "_post_state",
            _snapshot_asset_transfer_state_v2(selected_state),
        )
        object.__setattr__(self, "_effects", _snapshot_effect_plan_v2(selected_effects))
        object.__setattr__(
            self,
            "_module_journal",
            _snapshot_module_journal_v2(selected_journal),
        )
        if self._effects.is_empty:
            raise ValueError("asset transfer acceptance requires nonempty effects")
        if self._module_journal.lane_id is not LaneIdV2.ASSET_TRANSFER:
            raise ValueError("asset transfer journal has the wrong lane")
        if self._module_journal.module_release_id != self._post_state.module_release_id:
            raise ValueError("asset transfer journal has the wrong module release")
        if self._module_journal.post_lane_root != self._post_state.state_root:
            raise ValueError("asset transfer journal has the wrong post-state root")
        if self._module_journal.effect_plan_root != self._effects.effect_plan_root:
            raise ValueError("asset transfer journal has the wrong effect-plan root")
        if self._effects.occurrence_consumptions != (
            self._module_journal.command_occurrence_id,
        ):
            raise ValueError("asset transfer effects have the wrong occurrence")
        if self._effects.lane_writes != (
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                self._module_journal.pre_lane_root,
                self._module_journal.post_lane_root,
            ),
        ):
            raise ValueError("asset transfer effects have the wrong exact lane write")
        if (
            self._module_journal.private_port_root != ZERO_ROOT_V2
            or self._module_journal.terminal_obligations_root != ZERO_ROOT_V2
            or self._module_journal.oracle_occurrence_plan_root != ZERO_ROOT_V2
        ):
            raise ValueError("asset transfer leaf must have zero external roots")

    @property
    def post_state(self) -> AssetTransferStateV2:
        return _snapshot_asset_transfer_state_v2(self._post_state)

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
        return ASSET_LANE_PRODUCTION_AUTHORITY_V2

    def to_canonical(self) -> dict[str, object]:
        return {
            "post_state": self.post_state,
            "effects": self.effects,
            "module_journal": self.module_journal,
            "production_authority": self.production_authority,
        }


@dataclass(frozen=True, slots=True, init=False)
class AssetTransferRejectedV2:
    code: AssetTransferRejectCodeV2
    pre_state_root: str
    post_state_root: str
    _effects: GlobalEconomicEffectPlanV2

    def __init__(
        self,
        code: AssetTransferRejectCodeV2,
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
        if type(self.code) is not AssetTransferRejectCodeV2:
            raise TypeError("asset transfer reject code is not closed")
        if type(selected_effects) is not GlobalEconomicEffectPlanV2:
            raise TypeError("asset transfer rejected effects are invalid")
        object.__setattr__(self, "_effects", _snapshot_effect_plan_v2(selected_effects))
        _require_root_v2(self.pre_state_root, name="asset transfer rejected pre-state")
        _require_root_v2(
            self.post_state_root,
            name="asset transfer rejected post-state",
        )
        if self.pre_state_root != self.post_state_root:
            raise ValueError("asset transfer rejection changed the state root")
        if not self._effects.is_empty:
            raise ValueError("asset transfer rejection carried effects")

    @property
    def effects(self) -> GlobalEconomicEffectPlanV2:
        return _snapshot_effect_plan_v2(self._effects)

    def to_canonical(self) -> dict[str, object]:
        return {
            "code": self.code,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "effects": self.effects,
        }


AssetTransferResultV2 = AssetTransferAcceptedV2 | AssetTransferRejectedV2


__all__ = [
    "ASSET_TRANSFER_MODULE_SCHEMA_V2",
    "ASSET_TRANSFER_COMMAND_KIND_V2",
    "ACCOUNT_CUSTODY_DOMAIN_V2",
    "ASSET_ATOM_DECIMALS_V2",
    "ASSET_LANE_PRODUCTION_AUTHORITY_V2",
    "MAX_ASSET_TRANSFER_ASSETS_V2",
    "MAX_ASSET_TRANSFER_BALANCE_ROWS_V2",
    "MAX_ASSET_TRANSFER_STATE_CANONICAL_BYTES_V2",
    "AssetClassV2",
    "require_asset_class_namespace_v2",
    "AssetTransferRejectCodeV2",
    "AssetTransferPolicyV2",
    "AssetTransferStateV2",
    "AssetTransferContextV2",
    "AssetTransferCommandV2",
    "AssetTransferAcceptedV2",
    "AssetTransferRejectedV2",
    "AssetTransferResultV2",
    "_snapshot_asset_transfer_state_v2",
    "_snapshot_asset_transfer_context_v2",
    "_snapshot_asset_transfer_command_v2",
]
