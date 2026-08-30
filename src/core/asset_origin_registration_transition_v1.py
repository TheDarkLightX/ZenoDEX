"""Deterministic SHADOW core for profile-gated asset-origin registration.

Registration records provenance and governed policy roots. It creates no
balance, supply, custody, reserve, or issue effect. Tau-originated assets remain
an explicit testnet option until a release-selected Tau adapter proves the
corresponding origin root.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    _require_bool,
    _require_nonnegative_int,
    _require_root,
    _require_token,
    hash_economic_command_body_v1,
    hash_global_v1,
)

ASSET_ORIGIN_REGISTRATION_SCHEMA_V1: Final = (
    "zenodex/asset-origin-registration-transition/v1"
)
ASSET_ORIGIN_REGISTRATION_COMMAND_V1: Final = "register_asset_origin"
ASSET_ATOM_DECIMALS_V1: Final = 8


class AssetOriginKindV1(str, Enum):
    NATIVE = "NATIVE"
    TAU_ORIGINATED = "TAU_ORIGINATED"


class AssetOriginRegistrationRejectCodeV1(str, Enum):
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    GRANT_MISMATCH = "GRANT_MISMATCH"
    DECIMAL_SCALE_MISMATCH = "DECIMAL_SCALE_MISMATCH"
    DISABLED_ORIGIN_KIND = "DISABLED_ORIGIN_KIND"
    DUPLICATE_ASSET = "DUPLICATE_ASSET"
    DUPLICATE_ORIGIN = "DUPLICATE_ORIGIN"
    DUPLICATE_NATIVE_ASSET = "DUPLICATE_NATIVE_ASSET"


@dataclass(frozen=True, slots=True, order=True)
class AssetOriginRecordV1:
    asset: str
    origin_kind: AssetOriginKindV1
    origin_root: str
    transfer_policy_root: str
    issue_policy_root: str
    decimals: int

    def __post_init__(self) -> None:
        _require_token(self.asset, name="asset origin asset")
        if type(self.origin_kind) is not AssetOriginKindV1:
            raise TypeError("asset origin kind must be exact")
        _require_root(self.origin_root, name="asset origin root")
        _require_root(self.transfer_policy_root, name="asset transfer policy root")
        _require_root(self.issue_policy_root, name="asset issue policy root", allow_zero=True)
        _require_nonnegative_int(self.decimals, name="asset origin decimals")
        if self.decimals != ASSET_ATOM_DECIMALS_V1:
            raise ValueError("registered asset must use the ABI V1 atom scale")

    @property
    def key(self) -> str:
        return self.asset

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "origin_kind": self.origin_kind,
            "origin_root": self.origin_root,
            "transfer_policy_root": self.transfer_policy_root,
            "issue_policy_root": self.issue_policy_root,
            "decimals": self.decimals,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationPolicyV1:
    authority_subject: str
    authority_grant_root: str
    allow_native: bool
    allow_tau_originated: bool

    def __post_init__(self) -> None:
        _require_token(self.authority_subject, name="asset registration authority")
        _require_root(self.authority_grant_root, name="asset registration grant")
        _require_bool(self.allow_native, name="allow native asset registration")
        _require_bool(self.allow_tau_originated, name="allow Tau asset registration")

    def to_canonical(self) -> dict[str, object]:
        return {
            "authority_subject": self.authority_subject,
            "authority_grant_root": self.authority_grant_root,
            "allow_native": self.allow_native,
            "allow_tau_originated": self.allow_tau_originated,
        }


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationStateV1:
    module_release_id: str
    policy: AssetOriginRegistrationPolicyV1
    assets: tuple[AssetOriginRecordV1, ...]

    def __post_init__(self) -> None:
        _require_root(self.module_release_id, name="asset registration module release")
        if type(self.policy) is not AssetOriginRegistrationPolicyV1:
            raise TypeError("asset registration policy must be exact")
        if type(self.assets) is not tuple or any(
            type(row) is not AssetOriginRecordV1 for row in self.assets
        ):
            raise TypeError("asset registration rows must be an exact tuple")
        assets = tuple(row.asset for row in self.assets)
        if assets != tuple(sorted(set(assets))):
            raise ValueError("asset registration rows must be asset-ordered and unique")
        origins = tuple(row.origin_root for row in self.assets)
        if len(origins) != len(set(origins)):
            raise ValueError("asset origin roots must be unique")
        if sum(row.origin_kind is AssetOriginKindV1.NATIVE for row in self.assets) > 1:
            raise ValueError("only one native asset may be registered")

    @property
    def state_root(self) -> str:
        return hash_global_v1(
            "asset-origin-registration-state-v1",
            {
                "schema": ASSET_ORIGIN_REGISTRATION_SCHEMA_V1,
                "module_release_id": self.module_release_id,
                "policy": self.policy,
                "assets": self.assets,
            },
        )


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str

    def __post_init__(self) -> None:
        _require_token(self.chain_id, name="asset registration chain")
        for name in (
            "deployment_root",
            "profile_root",
            "module_release_id",
            "command_occurrence_id",
            "grant_root",
        ):
            _require_root(getattr(self, name), name=f"asset registration {name}")
        _require_nonnegative_int(self.writer_epoch, name="asset registration writer epoch")
        _require_token(self.subject_id, name="asset registration subject")


@dataclass(frozen=True, slots=True)
class RegisterAssetOriginV1:
    command_kind: str
    asset: str
    origin_kind: AssetOriginKindV1
    origin_root: str
    transfer_policy_root: str
    issue_policy_root: str
    decimals: int

    def __post_init__(self) -> None:
        _require_token(self.command_kind, name="asset registration command")
        _require_token(self.asset, name="asset registration asset")
        if type(self.origin_kind) is not AssetOriginKindV1:
            raise TypeError("asset registration origin kind must be exact")
        _require_root(self.origin_root, name="asset registration origin root")
        _require_root(self.transfer_policy_root, name="asset registration transfer policy")
        _require_root(
            self.issue_policy_root,
            name="asset registration issue policy",
            allow_zero=True,
        )
        _require_nonnegative_int(self.decimals, name="asset registration decimals")

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v1(
            self.command_kind,
            {
                "asset": self.asset,
                "origin_kind": self.origin_kind,
                "origin_root": self.origin_root,
                "transfer_policy_root": self.transfer_policy_root,
                "issue_policy_root": self.issue_policy_root,
                "decimals": self.decimals,
            },
        )


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationAcceptedV1:
    post_state: AssetOriginRegistrationStateV1
    effects: GlobalEconomicEffectPlanV1


@dataclass(frozen=True, slots=True)
class AssetOriginRegistrationRejectedV1:
    code: AssetOriginRegistrationRejectCodeV1
    pre_state: AssetOriginRegistrationStateV1
    post_state: AssetOriginRegistrationStateV1
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if self.pre_state != self.post_state or not self.effects.is_empty:
            raise ValueError("asset registration rejection must be an exact no-op")


AssetOriginRegistrationResultV1 = (
    AssetOriginRegistrationAcceptedV1 | AssetOriginRegistrationRejectedV1
)


def _reject(
    code: AssetOriginRegistrationRejectCodeV1,
    state: AssetOriginRegistrationStateV1,
) -> AssetOriginRegistrationRejectedV1:
    return AssetOriginRegistrationRejectedV1(
        code,
        state,
        state,
        GlobalEconomicEffectPlanV1.empty(),
    )


def transition_asset_origin_registration_v1(
    context: AssetOriginRegistrationContextV1,
    pre_state: AssetOriginRegistrationStateV1,
    command: RegisterAssetOriginV1,
) -> AssetOriginRegistrationResultV1:
    """Register one provenance-bound asset without issuing any value."""

    if context.module_release_id != pre_state.module_release_id:
        return _reject(AssetOriginRegistrationRejectCodeV1.RELEASE_MISMATCH, pre_state)
    if command.command_kind != ASSET_ORIGIN_REGISTRATION_COMMAND_V1:
        return _reject(AssetOriginRegistrationRejectCodeV1.UNKNOWN_COMMAND, pre_state)
    if context.subject_id != pre_state.policy.authority_subject:
        return _reject(AssetOriginRegistrationRejectCodeV1.UNAUTHORIZED_SUBJECT, pre_state)
    if context.grant_root != pre_state.policy.authority_grant_root:
        return _reject(AssetOriginRegistrationRejectCodeV1.GRANT_MISMATCH, pre_state)
    if command.decimals != ASSET_ATOM_DECIMALS_V1:
        return _reject(AssetOriginRegistrationRejectCodeV1.DECIMAL_SCALE_MISMATCH, pre_state)
    enabled = {
        AssetOriginKindV1.NATIVE: pre_state.policy.allow_native,
        AssetOriginKindV1.TAU_ORIGINATED: pre_state.policy.allow_tau_originated,
    }[command.origin_kind]
    if not enabled:
        return _reject(AssetOriginRegistrationRejectCodeV1.DISABLED_ORIGIN_KIND, pre_state)
    if any(row.asset == command.asset for row in pre_state.assets):
        return _reject(AssetOriginRegistrationRejectCodeV1.DUPLICATE_ASSET, pre_state)
    if any(row.origin_root == command.origin_root for row in pre_state.assets):
        return _reject(AssetOriginRegistrationRejectCodeV1.DUPLICATE_ORIGIN, pre_state)
    if command.origin_kind is AssetOriginKindV1.NATIVE and any(
        row.origin_kind is AssetOriginKindV1.NATIVE for row in pre_state.assets
    ):
        return _reject(AssetOriginRegistrationRejectCodeV1.DUPLICATE_NATIVE_ASSET, pre_state)

    record = AssetOriginRecordV1(
        command.asset,
        command.origin_kind,
        command.origin_root,
        command.transfer_policy_root,
        command.issue_policy_root,
        command.decimals,
    )
    post_state = replace(
        pre_state,
        assets=tuple(sorted((*pre_state.assets, record), key=lambda row: row.asset)),
    )
    effects = GlobalEconomicEffectPlanV1(
        rows=(),
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(LaneIdV1.ASSET_TRANSFER, pre_state.state_root, post_state.state_root),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )
    return AssetOriginRegistrationAcceptedV1(post_state, effects)


__all__ = [
    "ASSET_ATOM_DECIMALS_V1",
    "ASSET_ORIGIN_REGISTRATION_COMMAND_V1",
    "ASSET_ORIGIN_REGISTRATION_SCHEMA_V1",
    "AssetOriginKindV1",
    "AssetOriginRecordV1",
    "AssetOriginRegistrationAcceptedV1",
    "AssetOriginRegistrationContextV1",
    "AssetOriginRegistrationPolicyV1",
    "AssetOriginRegistrationRejectCodeV1",
    "AssetOriginRegistrationRejectedV1",
    "AssetOriginRegistrationResultV1",
    "AssetOriginRegistrationStateV1",
    "RegisterAssetOriginV1",
    "transition_asset_origin_registration_v1",
]
