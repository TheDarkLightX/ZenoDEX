"""Closed V2 values for governed asset-origin registration."""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .asset_transfer_types_v2 import (
    ASSET_ATOM_DECIMALS_V2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
    AssetClassV2,
    _snapshot_effect_plan_v2,
    require_asset_class_namespace_v2,
)
from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    LaneModuleTransitionJournalV2,
    _snapshot_module_journal_v2,
    _snapshot_occurrence_v2,
)
from .global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    GlobalEconomicEffectPlanV2,
    LaneIdV2,
    LaneWriteV2,
    _require_bool_v2,
    _require_nonnegative_int_v2,
    _require_root_v2,
    _require_token_v2,
    _snapshot_dataclass_tuple_v2,
    hash_economic_command_body_v2,
    hash_global_v2,
)

ASSET_ORIGIN_REGISTRY_SCHEMA_V2: Final = "zenodex/asset-origin-registry/v2"
ASSET_ORIGIN_REGISTRATION_COMMAND_V2: Final = "register_asset_origin"


class AssetOriginKindV2(str, Enum):
    NATIVE = "NATIVE"
    TAU_ORIGINATED = "TAU_ORIGINATED"


class AssetOriginRegistrationRejectCodeV2(str, Enum):
    MISSING_OCCURRENCE = "MISSING_OCCURRENCE"
    OCCURRENCE_BINDING_MISMATCH = "OCCURRENCE_BINDING_MISMATCH"
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    OCCURRENCE_COMMAND_MISMATCH = "OCCURRENCE_COMMAND_MISMATCH"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    GRANT_MISMATCH = "GRANT_MISMATCH"
    DECIMAL_SCALE_MISMATCH = "DECIMAL_SCALE_MISMATCH"
    DISABLED_ORIGIN_KIND = "DISABLED_ORIGIN_KIND"
    NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED = "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED"
    DUPLICATE_ASSET = "DUPLICATE_ASSET"
    DUPLICATE_ORIGIN = "DUPLICATE_ORIGIN"


@dataclass(frozen=True, slots=True, order=True)
class AssetOriginRecordV2:
    asset: str
    origin_kind: AssetOriginKindV2
    origin_root: str
    transfer_policy_root: str
    issue_policy_root: str
    decimals: int
    asset_class: AssetClassV2

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="asset origin asset")
        if type(self.origin_kind) is not AssetOriginKindV2:
            raise TypeError("asset origin kind must be exact")
        if type(self.asset_class) is not AssetClassV2:
            raise TypeError("asset origin class must be exact")
        _require_root_v2(self.origin_root, name="asset origin root")
        _require_root_v2(
            self.transfer_policy_root,
            name="asset transfer policy root",
        )
        _require_root_v2(
            self.issue_policy_root,
            name="asset issue policy root",
            allow_zero=True,
        )
        _require_nonnegative_int_v2(self.decimals, name="asset origin decimals")
        if self.decimals != ASSET_ATOM_DECIMALS_V2:
            raise ValueError("registered asset must use the ABI V2 atom scale")
        require_asset_class_namespace_v2(self.asset, self.asset_class)
        if (self.origin_kind is AssetOriginKindV2.NATIVE) != (
            self.asset_class is AssetClassV2.TAU_NATIVE_COIN
        ):
            raise ValueError("asset origin kind and native asset class disagree")

    @property
    def key(self) -> str:
        return self.asset

    @property
    def record_root(self) -> str:
        return hash_global_v2("asset-origin-record-v2", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "origin_kind": self.origin_kind,
            "origin_root": self.origin_root,
            "transfer_policy_root": self.transfer_policy_root,
            "issue_policy_root": self.issue_policy_root,
            "decimals": self.decimals,
            "asset_class": self.asset_class,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationPolicyV2:
    authority_subject: str
    authority_grant_root: str
    allow_native: bool
    allow_tau_originated: bool

    def __post_init__(self) -> None:
        _require_token_v2(
            self.authority_subject,
            name="asset registration authority",
        )
        _require_root_v2(
            self.authority_grant_root,
            name="asset registration grant",
        )
        _require_bool_v2(
            self.allow_native,
            name="allow native asset registration",
        )
        _require_bool_v2(
            self.allow_tau_originated,
            name="allow Tau asset registration",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "authority_subject": self.authority_subject,
            "authority_grant_root": self.authority_grant_root,
            "allow_native": self.allow_native,
            "allow_tau_originated": self.allow_tau_originated,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistryStateV2:
    module_release_id: str
    policy: AssetOriginRegistrationPolicyV2
    assets: tuple[AssetOriginRecordV2, ...]

    def __post_init__(self) -> None:
        _require_root_v2(
            self.module_release_id,
            name="asset origin registry module release",
        )
        if type(self.policy) is not AssetOriginRegistrationPolicyV2:
            raise TypeError("asset origin registration policy must be exact")
        object.__setattr__(self, "policy", replace(self.policy))
        object.__setattr__(
            self,
            "assets",
            _snapshot_dataclass_tuple_v2(
                self.assets,
                AssetOriginRecordV2,
                "asset origin registry rows",
            ),
        )
        assets = tuple(row.asset for row in self.assets)
        if assets != tuple(sorted(set(assets))):
            raise ValueError("asset origin registry rows must be ordered and unique")
        origins = tuple(row.origin_root for row in self.assets)
        if len(origins) != len(set(origins)):
            raise ValueError("asset origin roots must be unique")
        if sum(row.origin_kind is AssetOriginKindV2.NATIVE for row in self.assets) > 1:
            raise ValueError("only one native asset may be registered")

    @property
    def state_root(self) -> str:
        return hash_global_v2("asset-origin-registry-state-v2", self.to_canonical())

    def record_for(self, asset: str) -> AssetOriginRecordV2 | None:
        _require_token_v2(asset, name="asset origin registry lookup")
        row = next((row for row in self.assets if row.asset == asset), None)
        return None if row is None else replace(row)

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
            "module_release_id": self.module_release_id,
            "policy": self.policy,
            "assets": self.assets,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationContextV2:
    writer_epoch: int
    module_release_id: str
    global_pre_state_root: str
    occurrence: EconomicCommandOccurrenceV2 | None

    def __post_init__(self) -> None:
        _require_nonnegative_int_v2(
            self.writer_epoch,
            name="asset origin registration writer epoch",
        )
        _require_root_v2(
            self.module_release_id,
            name="asset origin registration module release",
        )
        _require_root_v2(
            self.global_pre_state_root,
            name="asset origin registration global pre-state root",
        )
        if self.occurrence is not None:
            if type(self.occurrence) is not EconomicCommandOccurrenceV2:
                raise TypeError("asset origin registration occurrence must be exact")
            object.__setattr__(
                self,
                "occurrence",
                _snapshot_occurrence_v2(self.occurrence),
            )

    def to_canonical(self) -> dict[str, object]:
        return {
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "global_pre_state_root": self.global_pre_state_root,
            "occurrence": self.occurrence,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationCommandV2:
    command_kind: str
    asset: str
    origin_kind: AssetOriginKindV2
    origin_root: str
    transfer_policy_root: str
    issue_policy_root: str
    decimals: int
    asset_class: AssetClassV2

    def __post_init__(self) -> None:
        _require_token_v2(self.command_kind, name="asset origin registration command")
        _require_token_v2(self.asset, name="asset origin registration asset")
        if type(self.origin_kind) is not AssetOriginKindV2:
            raise TypeError("asset origin registration kind must be exact")
        if type(self.asset_class) is not AssetClassV2:
            raise TypeError("asset origin registration class must be exact")
        _require_root_v2(self.origin_root, name="asset origin registration root")
        _require_root_v2(
            self.transfer_policy_root,
            name="asset origin registration transfer policy root",
        )
        _require_root_v2(
            self.issue_policy_root,
            name="asset origin registration issue policy root",
            allow_zero=True,
        )
        _require_nonnegative_int_v2(
            self.decimals,
            name="asset origin registration decimals",
        )
        require_asset_class_namespace_v2(self.asset, self.asset_class)
        if (self.origin_kind is AssetOriginKindV2.NATIVE) != (
            self.asset_class is AssetClassV2.TAU_NATIVE_COIN
        ):
            raise ValueError("asset origin kind and native asset class disagree")

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v2(self.command_kind, self)

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "asset": self.asset,
            "origin_kind": self.origin_kind,
            "origin_root": self.origin_root,
            "transfer_policy_root": self.transfer_policy_root,
            "issue_policy_root": self.issue_policy_root,
            "decimals": self.decimals,
            "asset_class": self.asset_class,
        }


def _snapshot_registry_state_v2(
    state: AssetOriginRegistryStateV2,
) -> AssetOriginRegistryStateV2:
    if type(state) is not AssetOriginRegistryStateV2:
        raise TypeError("asset origin registry state must have the exact typed value")
    return AssetOriginRegistryStateV2(
        module_release_id=state.module_release_id,
        policy=state.policy,
        assets=state.assets,
    )


def _snapshot_registration_context_v2(
    context: AssetOriginRegistrationContextV2,
) -> AssetOriginRegistrationContextV2:
    if type(context) is not AssetOriginRegistrationContextV2:
        raise TypeError("asset origin context must have the exact typed value")
    return replace(context, occurrence=context.occurrence)


def _snapshot_registration_command_v2(
    command: AssetOriginRegistrationCommandV2,
) -> AssetOriginRegistrationCommandV2:
    if type(command) is not AssetOriginRegistrationCommandV2:
        raise TypeError("asset origin command must have the exact typed value")
    return replace(command)


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationAcceptedV2:
    post_state: AssetOriginRegistryStateV2
    effects: GlobalEconomicEffectPlanV2
    module_journal: LaneModuleTransitionJournalV2

    def __post_init__(self) -> None:
        if type(self.post_state) is not AssetOriginRegistryStateV2:
            raise TypeError("asset origin accepted state must be exact")
        if type(self.effects) is not GlobalEconomicEffectPlanV2:
            raise TypeError("asset origin accepted effects must be exact")
        if type(self.module_journal) is not LaneModuleTransitionJournalV2:
            raise TypeError("asset origin accepted journal must be exact")
        object.__setattr__(
            self,
            "post_state",
            _snapshot_registry_state_v2(self.post_state),
        )
        object.__setattr__(self, "effects", _snapshot_effect_plan_v2(self.effects))
        object.__setattr__(
            self,
            "module_journal",
            _snapshot_module_journal_v2(self.module_journal),
        )
        if self.effects.rows or self.effects.asset_conservation or self.effects.fee_conservation:
            raise ValueError("asset origin registration created an economic value effect")
        if self.module_journal.lane_id is not LaneIdV2.ASSET_TRANSFER:
            raise ValueError("asset origin registration journal has the wrong lane")
        if self.module_journal.post_lane_root != self.post_state.state_root:
            raise ValueError("asset origin registration journal has the wrong post root")
        if self.module_journal.effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("asset origin registration journal has the wrong effect root")
        if self.effects.occurrence_consumptions != (self.module_journal.command_occurrence_id,):
            raise ValueError("asset origin registration effects have the wrong occurrence")
        if self.effects.lane_writes != (
            LaneWriteV2(
                LaneIdV2.ASSET_TRANSFER,
                self.module_journal.pre_lane_root,
                self.module_journal.post_lane_root,
            ),
        ):
            raise ValueError("asset origin registration effects have the wrong lane write")
        if (
            self.module_journal.terminal_obligations_root != ZERO_ROOT_V2
            or self.module_journal.oracle_occurrence_plan_root != ZERO_ROOT_V2
        ):
            raise ValueError("asset origin registration created an unrelated plan")

    @property
    def production_authority(self) -> str:
        return ASSET_LANE_PRODUCTION_AUTHORITY_V2


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationRejectedV2:
    code: AssetOriginRegistrationRejectCodeV2
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV2

    def __post_init__(self) -> None:
        if type(self.code) is not AssetOriginRegistrationRejectCodeV2:
            raise TypeError("asset origin registration reject code must be exact")
        _require_root_v2(self.pre_state_root, name="asset origin rejected pre root")
        _require_root_v2(self.post_state_root, name="asset origin rejected post root")
        object.__setattr__(self, "effects", _snapshot_effect_plan_v2(self.effects))
        if self.pre_state_root != self.post_state_root or not self.effects.is_empty:
            raise ValueError("asset origin registration rejection must be an exact no-op")


AssetOriginRegistrationResultV2 = (
    AssetOriginRegistrationAcceptedV2 | AssetOriginRegistrationRejectedV2
)


__all__ = [
    "ASSET_ORIGIN_REGISTRY_SCHEMA_V2",
    "ASSET_ORIGIN_REGISTRATION_COMMAND_V2",
    "AssetOriginKindV2",
    "AssetOriginRegistrationRejectCodeV2",
    "AssetOriginRecordV2",
    "AssetOriginRegistrationPolicyV2",
    "AssetOriginRegistryStateV2",
    "AssetOriginRegistrationContextV2",
    "AssetOriginRegistrationCommandV2",
    "AssetOriginRegistrationAcceptedV2",
    "AssetOriginRegistrationRejectedV2",
    "AssetOriginRegistrationResultV2",
    "_snapshot_registry_state_v2",
    "_snapshot_registration_context_v2",
    "_snapshot_registration_command_v2",
]
