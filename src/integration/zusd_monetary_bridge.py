"""Live zUSD monetary bridge for Tau app-state transactions.

This adapter binds the pure single-vault zUSD kernel to Tau app-state balances:

- collateral deposits and withdrawals move native balance entries;
- zUSD mint/repay/redeem moves transferable zUSD balance entries;
- stability-pool deposits are held in a deterministic zUSD escrow account;
- liquidation burns escrowed zUSD and assigns collateral gains to SP accounts.

The pure kernel uses E8 monetary amounts. The existing token/perps transport uses
whole quote units, so this bridge only exposes whole-zUSD balance movements and
rejects non-whole zUSD amounts at the app boundary.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from types import MappingProxyType
from typing import Any, Mapping, Optional, cast

from ..core.consensus_time import VerifiedExecutionClockV1
from ..core.dex import DexState
from ..core.perps import (
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpMarketState,
    PerpMarketState,
)
from ..core.zusd import (
    BPS_SCALE,
    E8,
    ZUSDCommand,
    ZUSDCommandTag,
    ZUSDRedemptionAdmissionProfile,
    ZUSDState,
    ZUSDStepResult,
    ZUSDWithShutdownExtension,
    check_invariants,
    init_state,
    step,
    step_with_shutdown_extension,
)
from ..core.zusd_liability_cover import (
    ZUSDFreeDebtLiabilityBreakdown,
    evaluate_zusd_free_debt_liability_cover,
)
from ..core.zusd_oracle_ingress_admission import (
    ZUSDOracleEvidenceProfile,
    ZUSDOracleIngressAction,
    ZUSDOracleIngressEvidence,
    evaluate_zusd_oracle_ingress_admission,
)
from ..core.zusd_redemption_guard import MAX_TCR_BPS
from ..core.zusd_shutdown import (
    ZUSDShutdownExtensionProfile,
    ZUSDShutdownExtensionState,
    ZUSDShutdownPhase,
)
from ..state.balances import NATIVE_ASSET, BalanceTable
from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
)
from ..state.nonces import NonceTable
from .dex_snapshot import snapshot_from_state
from .zeno_oracle_authorization import (
    ZUSD_COLLATERAL_QUERY_ID,
    ZUSD_LIQUIDATE_VAULT_PROFILE_ID,
    ZUSD_MINT_PROFILE_ID,
    RuntimeActionFacts,
    check_critical_consumer_authorization,
    semantic_hash,
)
from .zusd_tau_token import derive_zusd_tau_asset_id

ZUSD_MONETARY_SCHEMA = "zenodex/zusd_monetary_state/v1"
ZUSD_AUTHORITY_BINDING_SCHEMA = "zenodex/zusd_authority_binding/v1"
ZUSD_RUNTIME_POLICY_BINDING_SCHEMA = "zenodex/zusd_runtime_policy_binding/v3"
_LEGACY_ZUSD_RUNTIME_POLICY_BINDING_SCHEMA_V2 = (
    "zenodex/zusd_runtime_policy_binding/v2"
)
_LEGACY_ZUSD_RUNTIME_POLICY_BINDING_SCHEMA = (
    "zenodex/zusd_runtime_policy_binding/v1"
)
ZUSD_MONETARY_MODULE = "ZUSDFinance"
ZUSD_MONETARY_VERSION = "0.1"

_U32_MAX = 0xFFFFFFFF
_MAX_OPS = 128
_MAX_OP_BYTES = 64_000
_MAX_TOTAL_OPS_BYTES = 512_000
_FEE_ACC_SCALE = 1_000_000


def _canonical_sha256_ref(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if len(value) != 71 or not value.startswith("sha256:"):
        raise ValueError(f"{name} must be a sha256 reference")
    digest = value.removeprefix("sha256:")
    if digest != digest.lower():
        raise ValueError(f"{name} must use lowercase hex")
    try:
        int(digest, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a sha256 reference") from exc
    return value


@dataclass(frozen=True)
class ZUSDMonetaryConfig:
    chain_id: str = "tau-local"
    oracle_pubkey: Optional[str] = None
    epoch_operator_pubkey: Optional[str] = None
    protocol_fee_recipient_pubkey: Optional[str] = None
    asset_id: Optional[str] = None
    liquidation_gas_comp_fixed_collateral_e8: int = 0
    liquidation_gas_comp_bps: int = 0
    borrow_fee_floor_bps: int = 0
    borrow_fee_max_bps: int = 1_000
    host_protocol_fee_share_bps: int = 0
    fee_stake_asset_id: Optional[str] = None
    staking_activation_delay_epochs: int = 1
    oracle_evidence_profile: ZUSDOracleEvidenceProfile = (
        ZUSDOracleEvidenceProfile.FINALIZED_O3_V1
    )
    # None is a state-committed disabled sentinel for the strict profile. The
    # O3 checker rejects every authorization until a canonical trusted root is
    # provisioned and committed; it never trusts a root from the operation.
    oracle_authorization_receipt_graph_root: Optional[str] = None
    # terminal-freeze-v1 is a quarantined, refuted experiment. Callers must
    # opt in explicitly for bounded replay; production constructors leave it
    # unmounted.
    shutdown_extension_profile: ZUSDShutdownExtensionProfile | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "chain_id",
            _canonical_chain_id(self.chain_id, name="chain_id"),
        )
        if self.asset_id is not None:
            object.__setattr__(
                self,
                "asset_id",
                _canonical_asset(self.asset_id, name="asset_id"),
            )
        _require_int(self.borrow_fee_floor_bps, name="borrow_fee_floor_bps", minimum=0, maximum=BPS_SCALE)
        _require_int(self.borrow_fee_max_bps, name="borrow_fee_max_bps", minimum=0, maximum=BPS_SCALE)
        if int(self.borrow_fee_floor_bps) > int(self.borrow_fee_max_bps):
            raise ValueError("borrow_fee bps bounds invalid")
        _require_int(
            self.host_protocol_fee_share_bps,
            name="host_protocol_fee_share_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        _require_int(
            self.staking_activation_delay_epochs,
            name="staking_activation_delay_epochs",
            minimum=1,
            maximum=_U32_MAX,
        )
        if (
            self.shutdown_extension_profile is not None
            and type(self.shutdown_extension_profile)
            is not ZUSDShutdownExtensionProfile
        ):
            raise TypeError(
                "shutdown_extension_profile must be exactly typed or None"
            )
        if type(self.oracle_evidence_profile) is not ZUSDOracleEvidenceProfile:
            raise TypeError(
                "oracle_evidence_profile must be exactly ZUSDOracleEvidenceProfile"
            )
        if self.oracle_authorization_receipt_graph_root is not None:
            object.__setattr__(
                self,
                "oracle_authorization_receipt_graph_root",
                _canonical_sha256_ref(
                    self.oracle_authorization_receipt_graph_root,
                    name="oracle_authorization_receipt_graph_root",
                ),
            )
        if self.epoch_operator_pubkey is not None:
            _canonical_pubkey(
                self.epoch_operator_pubkey,
                name="epoch_operator_pubkey",
            )
        if self.oracle_pubkey is not None:
            _canonical_pubkey(
                self.oracle_pubkey,
                name="oracle_pubkey",
            )
        if self.protocol_fee_recipient_pubkey is not None:
            fee_recipient = _canonical_pubkey(
                self.protocol_fee_recipient_pubkey,
                name="protocol_fee_recipient_pubkey",
            )
            if fee_recipient == stability_pool_pubkey(chain_id=self.chain_id):
                raise ValueError(
                    "protocol_fee_recipient_pubkey must differ from Stability Pool custody"
                )
        if self.fee_stake_asset_id is not None:
            object.__setattr__(
                self,
                "fee_stake_asset_id",
                _canonical_asset(
                    self.fee_stake_asset_id,
                    name="fee_stake_asset_id",
                ),
            )
            if self.fee_stake_asset_id == self.zusd_asset:
                raise ValueError("fee_stake_asset_id must differ from canonical zUSD")

    @property
    def zusd_asset(self) -> str:
        if self.asset_id is not None:
            return _canonical_asset(self.asset_id, name="asset_id")
        return derive_zusd_tau_asset_id(chain_id=self.chain_id)

    @property
    def fee_stake_asset(self) -> str | None:
        if self.fee_stake_asset_id is None:
            return None
        return _canonical_asset(self.fee_stake_asset_id, name="fee_stake_asset_id")

    @property
    def redemption_admission_profile(self) -> ZUSDRedemptionAdmissionProfile:
        """Return the only redemption profile representable by this config."""

        return ZUSDRedemptionAdmissionProfile.LIQUITY_V1_MINIMUM


@dataclass(frozen=True)
class ZUSDAuthorityBinding:
    """State-committed identities that may authorize or receive zUSD value."""

    oracle_pubkey: Optional[str] = None
    epoch_operator_pubkey: Optional[str] = None
    protocol_fee_recipient_pubkey: Optional[str] = None

    def __post_init__(self) -> None:
        for field_name in (
            "oracle_pubkey",
            "epoch_operator_pubkey",
            "protocol_fee_recipient_pubkey",
        ):
            raw = getattr(self, field_name)
            canonical = (
                None
                if raw is None
                else _canonical_pubkey(raw, name=f"authority_binding.{field_name}")
            )
            object.__setattr__(self, field_name, canonical)

    @classmethod
    def from_config(cls, config: ZUSDMonetaryConfig) -> ZUSDAuthorityBinding:
        if not isinstance(config, ZUSDMonetaryConfig):
            raise TypeError("config must be a ZUSDMonetaryConfig")
        return cls(
            oracle_pubkey=config.oracle_pubkey,
            epoch_operator_pubkey=config.epoch_operator_pubkey,
            protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
        )

    def to_obj(self) -> dict[str, Any]:
        return {
            "schema": ZUSD_AUTHORITY_BINDING_SCHEMA,
            "oracle_pubkey": self.oracle_pubkey,
            "epoch_operator_pubkey": self.epoch_operator_pubkey,
            "protocol_fee_recipient_pubkey": self.protocol_fee_recipient_pubkey,
        }

    @classmethod
    def from_obj(cls, obj: Any) -> ZUSDAuthorityBinding:
        if not isinstance(obj, Mapping):
            raise TypeError("zusd_monetary.authority_binding must be an object")
        expected_fields = {
            "schema",
            "oracle_pubkey",
            "epoch_operator_pubkey",
            "protocol_fee_recipient_pubkey",
        }
        extra = set(obj) - expected_fields
        if extra:
            raise ValueError(
                "zusd_monetary.authority_binding unknown fields: "
                f"{sorted(extra)}"
            )
        missing = expected_fields - set(obj)
        if missing:
            raise ValueError(
                "zusd_monetary.authority_binding missing fields: "
                f"{sorted(missing)}"
            )
        schema = _require_str(
            obj.get("schema"),
            name="zusd_monetary.authority_binding.schema",
        )
        if schema != ZUSD_AUTHORITY_BINDING_SCHEMA:
            raise ValueError(f"unsupported zUSD authority binding schema: {schema!r}")
        return cls(
            oracle_pubkey=obj.get("oracle_pubkey"),
            epoch_operator_pubkey=obj.get("epoch_operator_pubkey"),
            protocol_fee_recipient_pubkey=obj.get(
                "protocol_fee_recipient_pubkey"
            ),
        )


@dataclass(frozen=True)
class ZUSDRuntimePolicyBinding:
    """State-committed policy that fixes the meaning of monetary transitions."""

    chain_id: str
    zusd_asset_id: str
    stability_pool_pubkey: str
    fee_stake_asset_id: Optional[str]
    liquidation_gas_comp_fixed_collateral_e8: int
    liquidation_gas_comp_bps: int
    borrow_fee_floor_bps: int
    borrow_fee_max_bps: int
    host_protocol_fee_share_bps: int
    staking_activation_delay_epochs: int
    oracle_evidence_profile: ZUSDOracleEvidenceProfile
    oracle_authorization_receipt_graph_root: Optional[str]
    shutdown_extension_profile: ZUSDShutdownExtensionProfile | None

    def __post_init__(self) -> None:
        chain_id = _canonical_chain_id(
            self.chain_id,
            name="runtime_policy_binding.chain_id",
        )
        zusd_asset_id = _canonical_asset(
            self.zusd_asset_id,
            name="runtime_policy_binding.zusd_asset_id",
        )
        pool_pubkey = _canonical_pubkey(
            self.stability_pool_pubkey,
            name="runtime_policy_binding.stability_pool_pubkey",
        )
        expected_pool = stability_pool_pubkey(chain_id=chain_id)
        if pool_pubkey != expected_pool:
            raise ValueError(
                "runtime_policy_binding.stability_pool_pubkey does not match chain_id"
            )
        fee_stake_asset_id = (
            None
            if self.fee_stake_asset_id is None
            else _canonical_asset(
                self.fee_stake_asset_id,
                name="runtime_policy_binding.fee_stake_asset_id",
            )
        )
        if fee_stake_asset_id == zusd_asset_id:
            raise ValueError(
                "runtime_policy_binding.fee_stake_asset_id must differ from canonical zUSD"
            )
        fixed_comp = _require_nonnegative_int(
            self.liquidation_gas_comp_fixed_collateral_e8,
            name="runtime_policy_binding.liquidation_gas_comp_fixed_collateral_e8",
        )
        liquidation_comp_bps = _require_int(
            self.liquidation_gas_comp_bps,
            name="runtime_policy_binding.liquidation_gas_comp_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        borrow_floor_bps = _require_int(
            self.borrow_fee_floor_bps,
            name="runtime_policy_binding.borrow_fee_floor_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        borrow_max_bps = _require_int(
            self.borrow_fee_max_bps,
            name="runtime_policy_binding.borrow_fee_max_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        if borrow_floor_bps > borrow_max_bps:
            raise ValueError("runtime_policy_binding borrow fee bps bounds invalid")
        host_share_bps = _require_int(
            self.host_protocol_fee_share_bps,
            name="runtime_policy_binding.host_protocol_fee_share_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        activation_delay = _require_int(
            self.staking_activation_delay_epochs,
            name="runtime_policy_binding.staking_activation_delay_epochs",
            minimum=1,
            maximum=_U32_MAX,
        )
        if type(self.oracle_evidence_profile) is not ZUSDOracleEvidenceProfile:
            raise TypeError(
                "runtime_policy_binding.oracle_evidence_profile must be "
                "exactly ZUSDOracleEvidenceProfile"
            )
        oracle_authorization_root = (
            None
            if self.oracle_authorization_receipt_graph_root is None
            else _canonical_sha256_ref(
                self.oracle_authorization_receipt_graph_root,
                name=(
                    "runtime_policy_binding."
                    "oracle_authorization_receipt_graph_root"
                ),
            )
        )
        if (
            self.shutdown_extension_profile is not None
            and type(self.shutdown_extension_profile)
            is not ZUSDShutdownExtensionProfile
        ):
            raise TypeError(
                "runtime_policy_binding.shutdown_extension_profile "
                "must be exactly typed or None"
            )
        object.__setattr__(self, "chain_id", chain_id)
        object.__setattr__(self, "zusd_asset_id", zusd_asset_id)
        object.__setattr__(self, "stability_pool_pubkey", pool_pubkey)
        object.__setattr__(self, "fee_stake_asset_id", fee_stake_asset_id)
        object.__setattr__(
            self,
            "liquidation_gas_comp_fixed_collateral_e8",
            fixed_comp,
        )
        object.__setattr__(self, "liquidation_gas_comp_bps", liquidation_comp_bps)
        object.__setattr__(self, "borrow_fee_floor_bps", borrow_floor_bps)
        object.__setattr__(self, "borrow_fee_max_bps", borrow_max_bps)
        object.__setattr__(self, "host_protocol_fee_share_bps", host_share_bps)
        object.__setattr__(
            self,
            "staking_activation_delay_epochs",
            activation_delay,
        )
        object.__setattr__(
            self,
            "oracle_authorization_receipt_graph_root",
            oracle_authorization_root,
        )

    @property
    def redemption_admission_profile(self) -> ZUSDRedemptionAdmissionProfile:
        """Bind runtime-policy schema v3 to the closed baseline profile."""

        return ZUSDRedemptionAdmissionProfile.LIQUITY_V1_MINIMUM

    @classmethod
    def from_config(
        cls,
        config: ZUSDMonetaryConfig,
    ) -> ZUSDRuntimePolicyBinding:
        if not isinstance(config, ZUSDMonetaryConfig):
            raise TypeError("config must be a ZUSDMonetaryConfig")
        return cls(
            chain_id=config.chain_id,
            zusd_asset_id=config.zusd_asset,
            stability_pool_pubkey=stability_pool_pubkey(
                chain_id=config.chain_id
            ),
            fee_stake_asset_id=config.fee_stake_asset,
            liquidation_gas_comp_fixed_collateral_e8=(
                config.liquidation_gas_comp_fixed_collateral_e8
            ),
            liquidation_gas_comp_bps=config.liquidation_gas_comp_bps,
            borrow_fee_floor_bps=config.borrow_fee_floor_bps,
            borrow_fee_max_bps=config.borrow_fee_max_bps,
            host_protocol_fee_share_bps=config.host_protocol_fee_share_bps,
            staking_activation_delay_epochs=(
                config.staking_activation_delay_epochs
            ),
            oracle_evidence_profile=config.oracle_evidence_profile,
            oracle_authorization_receipt_graph_root=(
                config.oracle_authorization_receipt_graph_root
            ),
            shutdown_extension_profile=config.shutdown_extension_profile,
        )

    def to_obj(self) -> dict[str, Any]:
        return {
            "schema": ZUSD_RUNTIME_POLICY_BINDING_SCHEMA,
            "chain_id": self.chain_id,
            "zusd_asset_id": self.zusd_asset_id,
            "stability_pool_pubkey": self.stability_pool_pubkey,
            "fee_stake_asset_id": self.fee_stake_asset_id,
            "liquidation_gas_comp_fixed_collateral_e8": (
                self.liquidation_gas_comp_fixed_collateral_e8
            ),
            "liquidation_gas_comp_bps": self.liquidation_gas_comp_bps,
            "borrow_fee_floor_bps": self.borrow_fee_floor_bps,
            "borrow_fee_max_bps": self.borrow_fee_max_bps,
            "host_protocol_fee_share_bps": self.host_protocol_fee_share_bps,
            "staking_activation_delay_epochs": (
                self.staking_activation_delay_epochs
            ),
            "oracle_evidence_profile": self.oracle_evidence_profile.value,
            "oracle_authorization_receipt_graph_root": (
                self.oracle_authorization_receipt_graph_root
            ),
            "redemption_admission_profile": self.redemption_admission_profile.value,
            "shutdown_extension_profile": (
                None
                if self.shutdown_extension_profile is None
                else self.shutdown_extension_profile.value
            ),
        }

    @classmethod
    def from_obj(cls, obj: Any) -> ZUSDRuntimePolicyBinding:
        if not isinstance(obj, Mapping):
            raise TypeError(
                "zusd_monetary.runtime_policy_binding must be an object"
            )
        if obj.get("schema") == _LEGACY_ZUSD_RUNTIME_POLICY_BINDING_SCHEMA_V2:
            legacy_fields = {
                "schema",
                "chain_id",
                "zusd_asset_id",
                "stability_pool_pubkey",
                "fee_stake_asset_id",
                "liquidation_gas_comp_fixed_collateral_e8",
                "liquidation_gas_comp_bps",
                "borrow_fee_floor_bps",
                "borrow_fee_max_bps",
                "host_protocol_fee_share_bps",
                "staking_activation_delay_epochs",
                "redemption_admission_profile",
                "shutdown_extension_profile",
            }
            if set(obj) != legacy_fields:
                raise ValueError(
                    "legacy zUSD runtime policy binding v2 fields must match exactly"
                )
            upgraded = dict(obj)
            upgraded["schema"] = ZUSD_RUNTIME_POLICY_BINDING_SCHEMA
            upgraded["oracle_evidence_profile"] = (
                ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0.value
            )
            upgraded["oracle_authorization_receipt_graph_root"] = None
            return cls.from_obj(upgraded)
        fields = {
            "schema",
            "chain_id",
            "zusd_asset_id",
            "stability_pool_pubkey",
            "fee_stake_asset_id",
            "liquidation_gas_comp_fixed_collateral_e8",
            "liquidation_gas_comp_bps",
            "borrow_fee_floor_bps",
            "borrow_fee_max_bps",
            "host_protocol_fee_share_bps",
            "staking_activation_delay_epochs",
            "oracle_evidence_profile",
            "oracle_authorization_receipt_graph_root",
            "redemption_admission_profile",
            "shutdown_extension_profile",
        }
        extra = set(obj) - fields
        if extra:
            raise ValueError(
                "zusd_monetary.runtime_policy_binding unknown fields: "
                f"{sorted(extra)}"
            )
        missing = fields - set(obj)
        if missing:
            raise ValueError(
                "zusd_monetary.runtime_policy_binding missing fields: "
                f"{sorted(missing)}"
            )
        schema = _require_str(
            obj.get("schema"),
            name="zusd_monetary.runtime_policy_binding.schema",
        )
        if schema != ZUSD_RUNTIME_POLICY_BINDING_SCHEMA:
            raise ValueError(
                f"unsupported zUSD runtime policy binding schema: {schema!r}"
            )
        profile = _require_str(
            obj.get("redemption_admission_profile"),
            name="zusd_monetary.runtime_policy_binding.redemption_admission_profile",
        )
        if profile != ZUSDRedemptionAdmissionProfile.LIQUITY_V1_MINIMUM.value:
            raise ValueError(
                "unsupported zUSD redemption admission profile: "
                f"{profile!r}"
            )
        shutdown_profile_raw = obj.get("shutdown_extension_profile")
        if shutdown_profile_raw is None:
            shutdown_profile = None
        else:
            try:
                shutdown_profile = ZUSDShutdownExtensionProfile(
                    shutdown_profile_raw
                )
            except (TypeError, ValueError) as exc:
                raise ValueError(
                    "unsupported zUSD shutdown extension profile"
                ) from exc
        fee_stake_asset_raw = obj.get("fee_stake_asset_id")
        fee_stake_asset_id = (
            None
            if fee_stake_asset_raw is None
            else _require_str(
                fee_stake_asset_raw,
                name="zusd_monetary.runtime_policy_binding.fee_stake_asset_id",
            )
        )
        try:
            oracle_evidence_profile = ZUSDOracleEvidenceProfile(
                _require_str(
                    obj.get("oracle_evidence_profile"),
                    name=(
                        "zusd_monetary.runtime_policy_binding."
                        "oracle_evidence_profile"
                    ),
                )
            )
        except (TypeError, ValueError) as exc:
            raise ValueError(
                "unsupported zUSD oracle evidence profile"
            ) from exc
        oracle_authorization_root_raw = obj.get(
            "oracle_authorization_receipt_graph_root"
        )
        oracle_authorization_root = (
            None
            if oracle_authorization_root_raw is None
            else _canonical_sha256_ref(
                oracle_authorization_root_raw,
                name=(
                    "zusd_monetary.runtime_policy_binding."
                    "oracle_authorization_receipt_graph_root"
                ),
            )
        )
        return cls(
            chain_id=_require_str(
                obj.get("chain_id"),
                name="zusd_monetary.runtime_policy_binding.chain_id",
            ),
            zusd_asset_id=_require_str(
                obj.get("zusd_asset_id"),
                name="zusd_monetary.runtime_policy_binding.zusd_asset_id",
            ),
            stability_pool_pubkey=_require_str(
                obj.get("stability_pool_pubkey"),
                name="zusd_monetary.runtime_policy_binding.stability_pool_pubkey",
            ),
            fee_stake_asset_id=fee_stake_asset_id,
            liquidation_gas_comp_fixed_collateral_e8=_require_int(
                obj.get("liquidation_gas_comp_fixed_collateral_e8"),
                name="runtime_policy_binding.liquidation_gas_comp_fixed_collateral_e8",
                minimum=0,
            ),
            liquidation_gas_comp_bps=_require_int(
                obj.get("liquidation_gas_comp_bps"),
                name="runtime_policy_binding.liquidation_gas_comp_bps",
                minimum=0,
                maximum=BPS_SCALE,
            ),
            borrow_fee_floor_bps=_require_int(
                obj.get("borrow_fee_floor_bps"),
                name="runtime_policy_binding.borrow_fee_floor_bps",
                minimum=0,
                maximum=BPS_SCALE,
            ),
            borrow_fee_max_bps=_require_int(
                obj.get("borrow_fee_max_bps"),
                name="runtime_policy_binding.borrow_fee_max_bps",
                minimum=0,
                maximum=BPS_SCALE,
            ),
            host_protocol_fee_share_bps=_require_int(
                obj.get("host_protocol_fee_share_bps"),
                name="runtime_policy_binding.host_protocol_fee_share_bps",
                minimum=0,
                maximum=BPS_SCALE,
            ),
            staking_activation_delay_epochs=_require_int(
                obj.get("staking_activation_delay_epochs"),
                name="runtime_policy_binding.staking_activation_delay_epochs",
                minimum=0,
                maximum=_U32_MAX,
            ),
            oracle_evidence_profile=oracle_evidence_profile,
            oracle_authorization_receipt_graph_root=(
                oracle_authorization_root
            ),
            shutdown_extension_profile=shutdown_profile,
        )


def _freeze_account_amounts(
    values: Mapping[str, int],
    *,
    drop_zero: bool = False,
) -> Mapping[str, int]:
    """Own and canonically freeze a scalar account map."""

    ordered = {
        pubkey: amount
        for pubkey, amount in sorted(values.items())
        if not drop_zero or amount > 0
    }
    return MappingProxyType(ordered)


@dataclass(frozen=True)
class ZUSDMonetaryState:
    core: ZUSDState
    shutdown_extension: ZUSDShutdownExtensionState | None = None
    vault_owner_pubkey: Optional[str] = None
    sp_deposits_e8: Mapping[str, int] | None = None
    sp_collateral_claims_e8: Mapping[str, int] | None = None
    protocol_zusd_fee_reserve_e8: int = 0
    staking_zusd_fee_pool_e8: int = 0
    staking_zusd_fee_acc_per_share_e8: int = 0
    host_zusd_fee_pool_e8: int = 0
    host_zusd_fee_cum_e8: int = 0
    host_zusd_fees_e8: Mapping[str, int] | None = None
    active_fee_stakes: Mapping[str, int] | None = None
    pending_fee_stakes: Mapping[str, int] | None = None
    pending_fee_stake_activation_epochs: Mapping[str, int] | None = None
    fee_stake_reward_debt_e8: Mapping[str, int] | None = None
    authority_binding: ZUSDAuthorityBinding | None = None
    runtime_policy_binding: ZUSDRuntimePolicyBinding | None = None

    def __post_init__(self) -> None:
        if type(self.core) is not ZUSDState:
            raise TypeError("core must be exactly ZUSDState")
        if (
            self.shutdown_extension is not None
            and type(self.shutdown_extension) is not ZUSDShutdownExtensionState
        ):
            raise TypeError(
                "shutdown_extension must be exactly typed or None"
            )
        if self.shutdown_extension is not None:
            ZUSDWithShutdownExtension(
                baseline=self.core,
                extension=self.shutdown_extension,
            )
        if self.authority_binding is not None and not isinstance(
            self.authority_binding,
            ZUSDAuthorityBinding,
        ):
            raise TypeError("authority_binding must be a ZUSDAuthorityBinding")
        if self.runtime_policy_binding is not None and not isinstance(
            self.runtime_policy_binding,
            ZUSDRuntimePolicyBinding,
        ):
            raise TypeError(
                "runtime_policy_binding must be a ZUSDRuntimePolicyBinding"
            )
        if (
            self.runtime_policy_binding is not None
            and self.authority_binding is None
        ):
            raise ValueError(
                "runtime_policy_binding requires authority_binding"
            )
        if (
            self.runtime_policy_binding is not None
            and self.authority_binding is not None
            and self.authority_binding.protocol_fee_recipient_pubkey
            == self.runtime_policy_binding.stability_pool_pubkey
        ):
            raise ValueError(
                "protocol fee recipient must differ from Stability Pool custody"
            )
        if self.vault_owner_pubkey is not None:
            _canonical_pubkey(self.vault_owner_pubkey, name="vault_owner_pubkey")
        deposits = dict(self.sp_deposits_e8 or {})
        claims = dict(self.sp_collateral_claims_e8 or {})
        host_fees = dict(self.host_zusd_fees_e8 or {})
        active_stakes = dict(self.active_fee_stakes or {})
        pending_stakes = dict(self.pending_fee_stakes or {})
        pending_epochs = dict(self.pending_fee_stake_activation_epochs or {})
        reward_debt = dict(self.fee_stake_reward_debt_e8 or {})
        for field_name in (
            "protocol_zusd_fee_reserve_e8",
            "staking_zusd_fee_pool_e8",
            "staking_zusd_fee_acc_per_share_e8",
            "host_zusd_fee_pool_e8",
            "host_zusd_fee_cum_e8",
        ):
            _require_nonnegative_int(getattr(self, field_name), name=field_name)
        for table_name, table in (
            ("sp_deposits_e8", deposits),
            ("sp_collateral_claims_e8", claims),
            ("host_zusd_fees_e8", host_fees),
            ("active_fee_stakes", active_stakes),
            ("pending_fee_stakes", pending_stakes),
            ("fee_stake_reward_debt_e8", reward_debt),
        ):
            for pk, amount in table.items():
                _canonical_pubkey(pk, name=f"{table_name}.pubkey")
                _require_nonnegative_int(amount, name=f"{table_name}[{pk}]")
        for pk, epoch in pending_epochs.items():
            _canonical_pubkey(pk, name="pending_fee_stake_activation_epochs.pubkey")
            _require_nonnegative_int(epoch, name=f"pending_fee_stake_activation_epochs[{pk}]")
        if set(pending_epochs) != set(pending_stakes):
            raise ValueError("pending fee stake activation keys mismatch")
        object.__setattr__(
            self,
            "sp_deposits_e8",
            _freeze_account_amounts(deposits),
        )
        object.__setattr__(
            self,
            "sp_collateral_claims_e8",
            _freeze_account_amounts(claims),
        )
        object.__setattr__(
            self,
            "host_zusd_fees_e8",
            _freeze_account_amounts(host_fees, drop_zero=True),
        )
        object.__setattr__(
            self,
            "active_fee_stakes",
            _freeze_account_amounts(active_stakes, drop_zero=True),
        )
        object.__setattr__(
            self,
            "pending_fee_stakes",
            _freeze_account_amounts(pending_stakes, drop_zero=True),
        )
        object.__setattr__(
            self,
            "pending_fee_stake_activation_epochs",
            _freeze_account_amounts(pending_epochs),
        )
        object.__setattr__(
            self,
            "fee_stake_reward_debt_e8",
            _freeze_account_amounts(reward_debt, drop_zero=True),
        )
        # This record is a committed value object, not a partially validated
        # builder. Cross-field accounting must hold at construction time.
        _raise_if_bad_state(self)


@dataclass(frozen=True)
class ZUSDMonetaryTxResult:
    ok: bool
    state: Optional[DexState] = None
    zusd_state: Optional[ZUSDMonetaryState] = None
    effects: Optional[list[dict[str, Any]]] = None
    error: Optional[str] = None


def init_monetary_state(config: ZUSDMonetaryConfig | None = None) -> ZUSDMonetaryState:
    core = init_state()
    if config is not None:
        core = ZUSDState(
            **{
                **core.__dict__,
                "liquidation_gas_comp_fixed_collateral_e8": _require_nonnegative_int(
                    config.liquidation_gas_comp_fixed_collateral_e8,
                    name="liquidation_gas_comp_fixed_collateral_e8",
                ),
                "liquidation_gas_comp_bps": _require_int(
                    config.liquidation_gas_comp_bps,
                    name="liquidation_gas_comp_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
                "borrow_fee_floor_bps": _require_int(
                    config.borrow_fee_floor_bps,
                    name="borrow_fee_floor_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
                "borrow_fee_max_bps": _require_int(
                    config.borrow_fee_max_bps,
                    name="borrow_fee_max_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
            }
        )
    return ZUSDMonetaryState(
        core=core,
        shutdown_extension=(
            None
            if config is None or config.shutdown_extension_profile is None
            else ZUSDShutdownExtensionState(
                profile=config.shutdown_extension_profile
            )
        ),
        authority_binding=(
            None if config is None else ZUSDAuthorityBinding.from_config(config)
        ),
        runtime_policy_binding=(
            None
            if config is None
            else ZUSDRuntimePolicyBinding.from_config(config)
        ),
        sp_deposits_e8={},
        sp_collateral_claims_e8={},
        host_zusd_fees_e8={},
        active_fee_stakes={},
        pending_fee_stakes={},
        pending_fee_stake_activation_epochs={},
        fee_stake_reward_debt_e8={},
    )


def stability_pool_pubkey(*, chain_id: str) -> str:
    canonical_chain_id = _canonical_chain_id(chain_id, name="chain_id")
    payload = (
        b"zenodex:zusd:stability_pool:v1\x00"
        + canonical_chain_id.encode("ascii")
    )
    return "0x" + hashlib.sha384(payload).hexdigest()


def zusd_monetary_sender_nonce_key(sender_pubkey: str) -> str:
    sender = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
    payload = b"zenodex:zusd_monetary_nonce:v1\x00" + sender.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


_LEGACY_CE067_CORE_FIELDS = frozenset(
    {
        "epoch_redemption_used_e8",
        "redemption_shutdown_tcr_bps",
        "redemption_min_post_tcr_bps",
        "max_epoch_redemption_fraction_bps",
    }
)
_LEGACY_SHUTDOWN_SNAPSHOT_FIELDS = frozenset(
    {
        "shutdown_phase",
        "shutdown_epoch",
        "shutdown_oracle_observed_epoch",
        "shutdown_price_e8",
        "shutdown_collateral_e8",
        "shutdown_debt_e8",
        "shutdown_source_state_root",
    }
)


def _ce067_migration_required(field_name: str) -> ValueError:
    return ValueError(
        "CE067 explicit profile migration required for non-neutral legacy "
        f"field: {field_name}"
    )


def _core_state_to_obj(core: ZUSDState) -> dict[str, Any]:
    out = dict(core.__dict__)
    forbidden = (
        _LEGACY_CE067_CORE_FIELDS
        | _LEGACY_SHUTDOWN_SNAPSHOT_FIELDS
        | {"shutdown_extension"}
    ) & set(out)
    if forbidden:
        raise ValueError(
            "baseline zUSD core contains CE067 extension fields: "
            f"{sorted(forbidden)}"
        )
    return out


def _decode_current_core(core_obj: Mapping[str, Any]) -> ZUSDState:
    fields = dict(core_obj)
    forbidden = (_LEGACY_CE067_CORE_FIELDS | _LEGACY_SHUTDOWN_SNAPSHOT_FIELDS) & set(
        fields
    )
    if forbidden:
        raise ValueError(
            "zUSD v4 core contains legacy CE067 fields: "
            f"{sorted(forbidden)}"
        )
    if "shutdown_extension" in fields:
        raise ValueError(
            "zUSD v4 baseline core cannot contain shutdown_extension"
        )
    return ZUSDState(**fields)


def _decode_legacy_core(
    core_obj: Mapping[str, Any],
) -> tuple[ZUSDState, ZUSDShutdownExtensionState | None]:
    fields = dict(core_obj)
    if "shutdown_extension" in fields:
        raise ValueError(
            "legacy zUSD core cannot contain shutdown_extension"
        )
    epoch_used = _require_nonnegative_int(
        fields.pop("epoch_redemption_used_e8", 0),
        name="zusd_monetary.core.epoch_redemption_used_e8",
    )
    post_floor = _require_int(
        fields.pop("redemption_min_post_tcr_bps", 0),
        name="zusd_monetary.core.redemption_min_post_tcr_bps",
        minimum=0,
        maximum=MAX_TCR_BPS,
    )
    epoch_cap = _require_int(
        fields.pop("max_epoch_redemption_fraction_bps", BPS_SCALE),
        name="zusd_monetary.core.max_epoch_redemption_fraction_bps",
        minimum=0,
        maximum=BPS_SCALE,
    )
    if epoch_used != 0:
        raise _ce067_migration_required("epoch_redemption_used_e8")
    if post_floor != 0:
        raise _ce067_migration_required("redemption_min_post_tcr_bps")
    if epoch_cap != BPS_SCALE:
        raise _ce067_migration_required("max_epoch_redemption_fraction_bps")

    mcr_bps = _require_int(
        fields.get("mcr_bps", 11_000),
        name="zusd_monetary.core.mcr_bps",
        minimum=1,
        maximum=MAX_TCR_BPS,
    )
    has_shutdown_extension = bool(
        ({"redemption_shutdown_tcr_bps"} | _LEGACY_SHUTDOWN_SNAPSHOT_FIELDS)
        & set(core_obj)
    )
    legacy_threshold = _require_int(
        fields.pop("redemption_shutdown_tcr_bps", mcr_bps),
        name="zusd_monetary.core.redemption_shutdown_tcr_bps",
        minimum=0,
        maximum=MAX_TCR_BPS,
    )
    if legacy_threshold != mcr_bps:
        raise _ce067_migration_required("redemption_shutdown_tcr_bps")

    phase_raw = fields.pop("shutdown_phase", ZUSDShutdownPhase.OPEN)
    try:
        phase = ZUSDShutdownPhase(phase_raw)
    except (TypeError, ValueError) as exc:
        raise ValueError("invalid legacy shutdown_phase") from exc
    extension = None
    if has_shutdown_extension:
        extension = ZUSDShutdownExtensionState(
            phase=phase,
            epoch=fields.pop("shutdown_epoch", 0),
            oracle_observed_epoch=fields.pop(
                "shutdown_oracle_observed_epoch", 0
            ),
            price_e8=fields.pop("shutdown_price_e8", 0),
            collateral_e8=fields.pop("shutdown_collateral_e8", 0),
            debt_e8=fields.pop("shutdown_debt_e8", 0),
            source_state_root=fields.pop("shutdown_source_state_root", ""),
        )
    else:
        for field_name in _LEGACY_SHUTDOWN_SNAPSHOT_FIELDS:
            fields.pop(field_name, None)
    return ZUSDState(**fields), extension


def _migrate_legacy_runtime_policy_binding_v1(
    obj: object,
    *,
    mcr_bps: int,
) -> ZUSDRuntimePolicyBinding:
    if not isinstance(obj, Mapping):
        raise TypeError("zusd_monetary.runtime_policy_binding must be an object")
    legacy_fields = {
        "schema",
        "chain_id",
        "zusd_asset_id",
        "stability_pool_pubkey",
        "fee_stake_asset_id",
        "liquidation_gas_comp_fixed_collateral_e8",
        "liquidation_gas_comp_bps",
        "borrow_fee_floor_bps",
        "borrow_fee_max_bps",
        "host_protocol_fee_share_bps",
        "staking_activation_delay_epochs",
        "redemption_shutdown_tcr_bps",
        "redemption_min_post_tcr_bps",
        "max_epoch_redemption_fraction_bps",
    }
    if set(obj) != legacy_fields:
        raise ValueError(
            "legacy zUSD runtime policy binding fields must match v1 exactly"
        )
    if obj.get("schema") != _LEGACY_ZUSD_RUNTIME_POLICY_BINDING_SCHEMA:
        raise ValueError("legacy zUSD runtime policy binding schema mismatch")
    threshold = _require_int(
        obj.get("redemption_shutdown_tcr_bps"),
        name="runtime_policy_binding.redemption_shutdown_tcr_bps",
        minimum=0,
        maximum=MAX_TCR_BPS,
    )
    post_floor = _require_int(
        obj.get("redemption_min_post_tcr_bps"),
        name="runtime_policy_binding.redemption_min_post_tcr_bps",
        minimum=0,
        maximum=MAX_TCR_BPS,
    )
    epoch_cap = _require_int(
        obj.get("max_epoch_redemption_fraction_bps"),
        name="runtime_policy_binding.max_epoch_redemption_fraction_bps",
        minimum=0,
        maximum=BPS_SCALE,
    )
    if threshold != mcr_bps:
        raise _ce067_migration_required("redemption_shutdown_tcr_bps")
    if post_floor != 0:
        raise _ce067_migration_required("redemption_min_post_tcr_bps")
    if epoch_cap != BPS_SCALE:
        raise _ce067_migration_required("max_epoch_redemption_fraction_bps")

    upgraded = {
        key: value
        for key, value in obj.items()
        if key
        not in {
            "redemption_shutdown_tcr_bps",
            "redemption_min_post_tcr_bps",
            "max_epoch_redemption_fraction_bps",
        }
    }
    upgraded["schema"] = ZUSD_RUNTIME_POLICY_BINDING_SCHEMA
    upgraded["redemption_admission_profile"] = (
        ZUSDRedemptionAdmissionProfile.LIQUITY_V1_MINIMUM.value
    )
    upgraded["oracle_evidence_profile"] = (
        ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0.value
    )
    upgraded["oracle_authorization_receipt_graph_root"] = None
    upgraded["shutdown_extension_profile"] = None
    return ZUSDRuntimePolicyBinding.from_obj(upgraded)


def zusd_monetary_state_to_obj(state: ZUSDMonetaryState) -> dict[str, Any]:
    _raise_if_bad_state(state)
    if (
        state.runtime_policy_binding is not None
        and state.authority_binding is None
    ):
        raise ValueError("runtime_policy_binding requires authority_binding")
    if (
        state.shutdown_extension is not None
        and state.runtime_policy_binding is None
    ):
        raise ValueError(
            "shutdown_extension requires runtime_policy_binding"
        )
    deposits = [
        {"pubkey": pk, "amount_e8": int(amount)}
        for pk, amount in sorted(dict(state.sp_deposits_e8 or {}).items())
        if int(amount) > 0
    ]
    claims = [
        {"pubkey": pk, "amount_e8": int(amount)}
        for pk, amount in sorted(dict(state.sp_collateral_claims_e8 or {}).items())
        if int(amount) > 0
    ]
    host_fees = _account_amount_entries(state.host_zusd_fees_e8, amount_key="amount_e8")
    active_stakes = _account_amount_entries(state.active_fee_stakes, amount_key="amount")
    pending_stakes = [
        {
            "pubkey": pk,
            "amount": int(amount),
            "activation_epoch": int(dict(state.pending_fee_stake_activation_epochs or {}).get(pk, 0)),
        }
        for pk, amount in sorted(dict(state.pending_fee_stakes or {}).items())
        if int(amount) > 0
    ]
    reward_debt = _account_amount_entries(state.fee_stake_reward_debt_e8, amount_key="amount_e8")
    out = {
        "schema": ZUSD_MONETARY_SCHEMA,
        "version": (
            4
            if state.runtime_policy_binding is not None
            else 2
            if state.authority_binding is not None
            else 1
        ),
        "core": _core_state_to_obj(state.core),
        "vault_owner_pubkey": state.vault_owner_pubkey,
        "sp_deposits": deposits,
        "sp_collateral_claims": claims,
        "protocol_zusd_fee_reserve_e8": int(state.protocol_zusd_fee_reserve_e8),
        "staking_zusd_fee_pool_e8": int(state.staking_zusd_fee_pool_e8),
        "staking_zusd_fee_acc_per_share_e8": int(state.staking_zusd_fee_acc_per_share_e8),
        "host_zusd_fee_pool_e8": int(state.host_zusd_fee_pool_e8),
        "host_zusd_fee_cum_e8": int(state.host_zusd_fee_cum_e8),
        "host_zusd_fees": host_fees,
        "active_fee_stakes": active_stakes,
        "pending_fee_stakes": pending_stakes,
        "fee_stake_reward_debt": reward_debt,
    }
    if state.authority_binding is not None:
        out["authority_binding"] = state.authority_binding.to_obj()
    if state.runtime_policy_binding is not None:
        out["runtime_policy_binding"] = state.runtime_policy_binding.to_obj()
        out["shutdown_extension"] = (
            None
            if state.shutdown_extension is None
            else state.shutdown_extension.to_obj()
        )
    return out


def zusd_monetary_state_from_obj(obj: Mapping[str, Any]) -> ZUSDMonetaryState:
    if not isinstance(obj, Mapping):
        raise TypeError("zusd_monetary must be an object")
    schema = _require_str(obj.get("schema"), name="zusd_monetary.schema")
    if schema != ZUSD_MONETARY_SCHEMA:
        raise ValueError(f"unsupported zusd_monetary schema: {schema!r}")
    version = _require_int(
        obj.get("version"),
        name="zusd_monetary.version",
        minimum=1,
        maximum=4,
    )
    if version not in {1, 2, 3, 4}:
        raise ValueError(f"unsupported zusd_monetary version: {version}")
    authority_binding = None
    if version >= 2:
        if "authority_binding" not in obj:
            raise ValueError(
                "zusd_monetary.authority_binding is required for "
                f"version {version}"
            )
        authority_binding = ZUSDAuthorityBinding.from_obj(
            obj.get("authority_binding")
        )
    elif "authority_binding" in obj:
        raise ValueError(
            "zusd_monetary.authority_binding requires version 2, 3, or 4"
        )

    core_obj = obj.get("core")
    if not isinstance(core_obj, Mapping):
        raise TypeError("zusd_monetary.core must be an object")
    shutdown_extension: ZUSDShutdownExtensionState | None
    if version == 4:
        core = _decode_current_core(core_obj)
        if "shutdown_extension" not in obj:
            raise ValueError(
                "zusd_monetary.shutdown_extension is required for version 4"
            )
        extension_obj = obj.get("shutdown_extension")
        shutdown_extension = (
            None
            if extension_obj is None
            else ZUSDShutdownExtensionState.from_obj(extension_obj)
        )
    else:
        if "shutdown_extension" in obj:
            raise ValueError(
                "zusd_monetary.shutdown_extension requires version 4"
            )
        core, legacy_extension = _decode_legacy_core(core_obj)
        if (
            legacy_extension is not None
            and legacy_extension.phase is ZUSDShutdownPhase.FROZEN
        ):
            raise _ce067_migration_required("shutdown_phase")
        else:
            shutdown_extension = None

    runtime_policy_binding = None
    if version in {3, 4}:
        if "runtime_policy_binding" not in obj:
            raise ValueError(
                "zusd_monetary.runtime_policy_binding is required for "
                f"version {version}"
            )
        runtime_policy_binding = (
            ZUSDRuntimePolicyBinding.from_obj(
                obj.get("runtime_policy_binding")
            )
            if version == 4
            else _migrate_legacy_runtime_policy_binding_v1(
                obj.get("runtime_policy_binding"),
                mcr_bps=core.mcr_bps,
            )
        )
    elif "runtime_policy_binding" in obj:
        raise ValueError(
            "zusd_monetary.runtime_policy_binding requires version 3 or 4"
        )
    owner_raw = obj.get("vault_owner_pubkey")
    owner = None if owner_raw is None else _canonical_pubkey(owner_raw, name="zusd_monetary.vault_owner_pubkey")
    deposits = _parse_account_amount_entries(obj.get("sp_deposits"), name="zusd_monetary.sp_deposits")
    claims = _parse_account_amount_entries(obj.get("sp_collateral_claims"), name="zusd_monetary.sp_collateral_claims")
    pending_stakes, pending_epochs = _parse_pending_fee_stake_entries(obj.get("pending_fee_stakes"))
    state = ZUSDMonetaryState(
        core=core,
        shutdown_extension=shutdown_extension,
        authority_binding=authority_binding,
        runtime_policy_binding=runtime_policy_binding,
        vault_owner_pubkey=owner,
        sp_deposits_e8=deposits,
        sp_collateral_claims_e8=claims,
        protocol_zusd_fee_reserve_e8=_require_nonnegative_int(
            obj.get("protocol_zusd_fee_reserve_e8", 0),
            name="zusd_monetary.protocol_zusd_fee_reserve_e8",
        ),
        staking_zusd_fee_pool_e8=_require_nonnegative_int(
            obj.get("staking_zusd_fee_pool_e8", 0),
            name="zusd_monetary.staking_zusd_fee_pool_e8",
        ),
        staking_zusd_fee_acc_per_share_e8=_require_nonnegative_int(
            obj.get("staking_zusd_fee_acc_per_share_e8", 0),
            name="zusd_monetary.staking_zusd_fee_acc_per_share_e8",
        ),
        host_zusd_fee_pool_e8=_require_nonnegative_int(
            obj.get("host_zusd_fee_pool_e8", 0),
            name="zusd_monetary.host_zusd_fee_pool_e8",
        ),
        host_zusd_fee_cum_e8=_require_nonnegative_int(
            obj.get("host_zusd_fee_cum_e8", 0),
            name="zusd_monetary.host_zusd_fee_cum_e8",
        ),
        host_zusd_fees_e8=_parse_account_amount_entries(
            obj.get("host_zusd_fees"),
            name="zusd_monetary.host_zusd_fees",
        ),
        active_fee_stakes=_parse_account_amount_entries(
            obj.get("active_fee_stakes"),
            name="zusd_monetary.active_fee_stakes",
            amount_key="amount",
        ),
        pending_fee_stakes=pending_stakes,
        pending_fee_stake_activation_epochs=pending_epochs,
        fee_stake_reward_debt_e8=_parse_account_amount_entries(
            obj.get("fee_stake_reward_debt"),
            name="zusd_monetary.fee_stake_reward_debt",
        ),
    )
    err = _state_invariant_error(state)
    if err is not None:
        raise ValueError(err)
    return state


@dataclass(frozen=True, slots=True)
class _PreviewExecutionClockV1:
    chain_id: str
    height: int
    derived_epoch: int


def _admit_consensus_epoch(
    *,
    monetary_state: ZUSDMonetaryState,
    execution_clock: VerifiedExecutionClockV1 | _PreviewExecutionClockV1,
) -> tuple[ZUSDMonetaryState, dict[str, Any] | None]:
    """Advance the internal epoch from an authenticated candidate height."""

    current_epoch = int(monetary_state.core.now_epoch)
    target_epoch = int(execution_clock.derived_epoch)
    if target_epoch < current_epoch:
        raise ValueError("verified consensus epoch regressed")
    if target_epoch == current_epoch:
        return monetary_state, None
    result, next_extension = _step_monetary_core(
        monetary_state=monetary_state,
        command=_core_command(
            action="advance_epoch",
            args={"delta": target_epoch - current_epoch},
        ),
    )
    if not result.ok or result.state is None:
        raise ValueError(result.error or "consensus epoch admission rejected")
    next_state = replace(
        monetary_state,
        core=result.state,
        shutdown_extension=next_extension,
    )
    _raise_if_bad_state(next_state)
    return next_state, dict(result.effects or {})


def apply_zusd_monetary_ops(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState,
    zusd_state: ZUSDMonetaryState | None,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
    execution_clock: VerifiedExecutionClockV1 | None = None,
) -> ZUSDMonetaryTxResult:
    """Apply authoritative operations under a consensus-verified clock."""

    if type(execution_clock) is not VerifiedExecutionClockV1:
        return ZUSDMonetaryTxResult(
            ok=False,
            error="verified execution clock is required",
        )
    return _apply_zusd_monetary_ops_with_clock(
        config=config,
        state=state,
        zusd_state=zusd_state,
        operations=operations,
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=block_timestamp,
        execution_clock=execution_clock,
    )


def preview_zusd_monetary_ops(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState,
    zusd_state: ZUSDMonetaryState | None,
    operations: Any,
    tx_sender_pubkey: str,
    preview_height: int,
    preview_epoch: int,
) -> ZUSDMonetaryTxResult:
    """Advisory wallet simulation with no execution-authority claim."""

    try:
        height = _require_int(
            preview_height,
            name="preview_height",
            minimum=0,
            maximum=_U32_MAX,
        )
        epoch = _require_int(
            preview_epoch,
            name="preview_epoch",
            minimum=0,
            maximum=_U32_MAX,
        )
    except (TypeError, ValueError) as exc:
        return ZUSDMonetaryTxResult(ok=False, error=_safe_error_str(exc))
    return _apply_zusd_monetary_ops_with_clock(
        config=config,
        state=state,
        zusd_state=zusd_state,
        operations=operations,
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=height,
        execution_clock=_PreviewExecutionClockV1(
            chain_id=config.chain_id,
            height=height,
            derived_epoch=epoch,
        ),
    )


def _apply_zusd_monetary_ops_with_clock(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState,
    zusd_state: ZUSDMonetaryState | None,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
    execution_clock: VerifiedExecutionClockV1 | _PreviewExecutionClockV1 | None,
) -> ZUSDMonetaryTxResult:
    try:
        if type(execution_clock) not in {
            VerifiedExecutionClockV1,
            _PreviewExecutionClockV1,
        }:
            raise ValueError("verified execution clock is required")
        if execution_clock.chain_id != config.chain_id:
            raise ValueError("execution clock chain_id mismatch")
        legacy_height = _require_int(
            block_timestamp,
            name="block_timestamp",
            minimum=0,
        )
        if legacy_height != execution_clock.height:
            raise ValueError("block_timestamp must equal verified consensus height")
        ops = _parse_ops(operations)
        actions = tuple(
            _require_action(op, index=index)
            for index, op in enumerate(ops)
        )

        balances = _copy_balance_table(state.balances)
        nonces = _copy_nonce_table(state.nonces)
        working = zusd_state or init_monetary_state(config)
        working = _bind_or_validate_authority_config(
            state=working,
            config=config,
        )
        working = _bind_or_validate_runtime_policy_config(
            state=working,
            config=config,
        )
        runtime_policy = _require_committed_runtime_policy_binding(working)
        effects: list[dict[str, Any]] = []
        working, epoch_effect = _admit_consensus_epoch(
            monetary_state=working,
            execution_clock=execution_clock,
        )
        if epoch_effect is not None:
            effects.append(
                {
                    "action": "admit_consensus_epoch",
                    "effects": epoch_effect,
                }
            )
        zusd_asset = runtime_policy.zusd_asset_id
        sp_pubkey = runtime_policy.stability_pool_pubkey
        perps_zusd_liability_e8 = _perps_quote_liability_e8(state, zusd_asset=zusd_asset)
        dex_pool_zusd_liability_e8 = _dex_pool_liability_e8(
            state,
            asset_id=zusd_asset,
        )
        if not ops:
            _assert_sp_escrow_matches(
                balances,
                working,
                zusd_asset=zusd_asset,
                sp_pubkey=sp_pubkey,
            )
            _assert_free_debt_liability_cover(
                balances,
                working,
                zusd_asset=zusd_asset,
                sp_pubkey=sp_pubkey,
                perps_zusd_liability_e8=perps_zusd_liability_e8,
                dex_pool_zusd_liability_e8=dex_pool_zusd_liability_e8,
            )
            next_state = replace(state, balances=balances, nonces=nonces)
            return ZUSDMonetaryTxResult(
                ok=True,
                state=next_state,
                zusd_state=working,
                effects=effects,
            )

        raw_sender, sender_had_0x = _raw_pubkey_key(tx_sender_pubkey)
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
        native_sender = _native_sender_key(
            balances,
            sender=sender,
            raw_sender=raw_sender,
            sender_had_0x=sender_had_0x,
        )

        _assert_sp_escrow_matches(balances, working, zusd_asset=zusd_asset, sp_pubkey=sp_pubkey)
        _assert_free_debt_liability_cover(
            balances,
            working,
            zusd_asset=zusd_asset,
            sp_pubkey=sp_pubkey,
            perps_zusd_liability_e8=perps_zusd_liability_e8,
            dex_pool_zusd_liability_e8=dex_pool_zusd_liability_e8,
        )

        nonce_key = zusd_monetary_sender_nonce_key(sender)
        for i, op in enumerate(ops):
            action = actions[i]
            nonce = _require_int(op.get("nonce"), name=f"zusd op[{i}].nonce", minimum=1, maximum=_U32_MAX)
            expected = int(nonces.get_last(nonce_key)) + 1
            if nonce != expected:
                return ZUSDMonetaryTxResult(
                    ok=False,
                    error=f"zusd op[{i}] nonce invalid (expected {expected}, got {nonce})",
                )
            deadline_err = _deadline_error(op=op, block_timestamp=block_timestamp, index=i)
            if deadline_err is not None:
                return ZUSDMonetaryTxResult(ok=False, error=deadline_err)

            allowed = _allowed_fields_for_action(action)
            extra = set(op.keys()) - allowed
            if extra:
                return ZUSDMonetaryTxResult(ok=False, error=f"zusd op[{i}] unknown fields: {sorted(extra)}")

            ingress_error = _zusd_oracle_ingress_error(
                runtime_policy=runtime_policy,
                staged_state=replace(
                    state,
                    balances=balances,
                    nonces=nonces,
                ),
                monetary_state=working,
                op=op,
                action=action,
                sender=sender,
            )
            if ingress_error is not None:
                return ZUSDMonetaryTxResult(
                    ok=False,
                    error=f"zusd op[{i}] {ingress_error}",
                )

            try:
                working, balance_effect = _apply_one(
                    runtime_policy=runtime_policy,
                    balances=balances,
                    monetary_state=working,
                    op=op,
                    action=action,
                    sender=sender,
                    native_sender=native_sender,
                    zusd_asset=zusd_asset,
                    sp_pubkey=sp_pubkey,
                )
            except Exception as exc:
                return ZUSDMonetaryTxResult(ok=False, error=f"zusd op[{i}] {exc}")

            nonces.set_last(nonce_key, nonce)
            effect = {"i": i, "action": action, "effects": balance_effect}
            effects.append(effect)
            _assert_sp_escrow_matches(balances, working, zusd_asset=zusd_asset, sp_pubkey=sp_pubkey)
            _assert_free_debt_liability_cover(
                balances,
                working,
                zusd_asset=zusd_asset,
                sp_pubkey=sp_pubkey,
                perps_zusd_liability_e8=perps_zusd_liability_e8,
                dex_pool_zusd_liability_e8=dex_pool_zusd_liability_e8,
            )

        next_state = replace(state, balances=balances, nonces=nonces)
        return ZUSDMonetaryTxResult(ok=True, state=next_state, zusd_state=working, effects=effects)
    except Exception as exc:
        return ZUSDMonetaryTxResult(ok=False, error=_safe_error_str(exc))


_CORE_COMMAND_TAGS = frozenset(
    {
        "advance_epoch",
        "bootstrap_oracle",
        "oracle_report",
        "oracle_commit",
        "deposit_collateral",
        "withdraw_collateral",
        "mint_zusd",
        "repay_zusd",
        "deposit_sp",
        "withdraw_sp",
        "redeem_zusd",
        "liquidate",
    }
)


def _core_command(*, action: str, args: Mapping[str, Any]) -> ZUSDCommand:
    if action not in _CORE_COMMAND_TAGS:
        raise ValueError(f"action is not a zUSD core command: {action!r}")
    return ZUSDCommand(tag=cast(ZUSDCommandTag, action), args=args)


def _shutdown_source_state_root(state: ZUSDMonetaryState) -> str:
    """Bind a shutdown snapshot to the complete pre-step monetary state."""

    payload = canonical_json_bytes(zusd_monetary_state_to_obj(state))
    return hashlib.sha256(
        b"zenodex:zusd:shutdown_source_state:v1\x00" + payload
    ).hexdigest()


def _step_monetary_core(
    *,
    monetary_state: ZUSDMonetaryState,
    command: ZUSDCommand,
) -> tuple[ZUSDStepResult, ZUSDShutdownExtensionState | None]:
    """Run one baseline command through the explicitly mounted extension."""

    extension = monetary_state.shutdown_extension
    if extension is None:
        return step(monetary_state.core, command), None

    mounted_command = command
    if command.tag == "oracle_commit":
        mounted_command = ZUSDCommand(
            tag=command.tag,
            args={
                **dict(command.args),
                "shutdown_source_state_root": _shutdown_source_state_root(
                    monetary_state
                ),
            },
        )
    mounted_result = step_with_shutdown_extension(
        ZUSDWithShutdownExtension(
            baseline=monetary_state.core,
            extension=extension,
        ),
        mounted_command,
    )
    if not mounted_result.ok or mounted_result.state is None:
        return (
            ZUSDStepResult(ok=False, error=mounted_result.error),
            extension,
        )
    return (
        ZUSDStepResult(
            ok=True,
            state=mounted_result.state.baseline,
            effects=mounted_result.effects,
        ),
        mounted_result.state.extension,
    )


def _apply_one(
    *,
    runtime_policy: ZUSDRuntimePolicyBinding,
    balances: BalanceTable,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
    sender: str,
    native_sender: str,
    zusd_asset: str,
    sp_pubkey: str,
) -> tuple[ZUSDMonetaryState, dict[str, Any]]:
    core = monetary_state.core
    owner = monetary_state.vault_owner_pubkey
    deposits = dict(monetary_state.sp_deposits_e8 or {})
    claims = dict(monetary_state.sp_collateral_claims_e8 or {})
    fee_fields = _fee_state_fields(monetary_state)
    authority_binding = _require_committed_authority_binding(monetary_state)

    if (
        monetary_state.shutdown_extension is not None
        and monetary_state.shutdown_extension.phase is ZUSDShutdownPhase.FROZEN
    ):
        raise ValueError(f"shutdown phase FROZEN blocks {action}")

    def run_core(command: ZUSDCommand) -> ZUSDStepResult:
        result, next_extension = _step_monetary_core(
            monetary_state=monetary_state,
            command=command,
        )
        fee_fields["shutdown_extension"] = next_extension
        return result

    if action in {"bootstrap_oracle", "oracle_report", "oracle_commit"}:
        if (
            runtime_policy.oracle_evidence_profile
            is ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0
        ):
            _require_oracle_sender(authority_binding, sender=sender)
        args: dict[str, Any] = {"auth_ok": True}
        if action in {"bootstrap_oracle", "oracle_report"}:
            args["price_e8"] = _require_int(op.get("price_e8"), name=f"{action}.price_e8", minimum=1)
            args["oracle_observed_epoch"] = _require_live_oracle_observed_epoch(
                core=core,
                op=op,
                action=action,
            )
        result = run_core(_core_command(action=action, args=args))
        if not result.ok or result.state is None:
            raise ValueError(result.error or f"{action} rejected")
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, dict(result.effects or {})

    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"}:
        op_owner = _canonical_pubkey(op.get("owner_pubkey", sender), name=f"{action}.owner_pubkey")
        if op_owner != sender:
            raise ValueError("owner_pubkey mismatch")
        if owner is None:
            if action not in {"deposit_collateral"}:
                raise ValueError("vault owner not initialized")
            owner = sender
        elif owner != sender:
            raise ValueError("vault owner mismatch")

    if action == "deposit_collateral":
        amount_e8 = _require_int(op.get("amount_e8"), name="deposit_collateral.amount_e8", minimum=1)
        if balances.get(native_sender, NATIVE_ASSET) < amount_e8:
            raise ValueError("insufficient native collateral balance")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "deposit_collateral rejected")
        balances.subtract(native_sender, NATIVE_ASSET, amount_e8)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": -amount_e8}

    if action == "withdraw_collateral":
        amount_e8 = _require_int(op.get("amount_e8"), name="withdraw_collateral.amount_e8", minimum=1)
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "withdraw_collateral rejected")
        balances.add(native_sender, NATIVE_ASSET, amount_e8)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": amount_e8}

    if action == "mint_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="mint_zusd.amount_e8")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "mint_zusd rejected")
        effects = dict(result.effects or {})
        minted_units = _e8_to_whole_units(int(effects.get("principal_e8", amount_e8)), name="mint_zusd.principal_e8")
        balances.add(sender, zusd_asset, minted_units)
        fee_fields, fee_effects = _route_mint_fee(
            runtime_policy=runtime_policy,
            fee_fields=fee_fields,
            mint_fee_e8=int(effects.get("mint_fee_e8", 0)),
            host_pubkey=op.get("host_pubkey"),
        )
        _require_fee_routes_transport_exact(
            authority_binding=authority_binding,
            fee_fields=fee_fields,
            fee_effects=fee_effects,
        )
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**effects, **fee_effects, "zusd_balance_delta": minted_units}

    if action == "repay_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="repay_zusd.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="repay_zusd.amount_e8")
        if balances.get(sender, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "repay_zusd rejected")
        balances.subtract(sender, zusd_asset, units)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units}

    if action == "deposit_sp":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="deposit_sp.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="deposit_sp.amount_e8")
        if balances.get(account, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "deposit_sp rejected")
        balances.subtract(account, zusd_asset, units)
        balances.add(sp_pubkey, zusd_asset, units)
        deposits[account] = int(deposits.get(account, 0)) + amount_e8
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units, "sp_escrow_delta": units}

    if action == "withdraw_sp":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="withdraw_sp.amount_e8")
        current = int(deposits.get(account, 0))
        if amount_e8 > current:
            raise ValueError("withdraw_sp exceeds account deposit")
        units = _e8_to_whole_units(amount_e8, name="withdraw_sp.amount_e8")
        if balances.get(sp_pubkey, zusd_asset) < units:
            raise ValueError("stability pool escrow balance too low")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None:
            raise ValueError(result.error or "withdraw_sp rejected")
        balances.subtract(sp_pubkey, zusd_asset, units)
        balances.add(account, zusd_asset, units)
        deposits = _set_or_drop(deposits, account, current - amount_e8)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": units, "sp_escrow_delta": -units}

    if action == "redeem_zusd":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="redeem_zusd.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="redeem_zusd.amount_e8")
        if balances.get(account, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = run_core(
            _core_command(action=action, args={"amount_e8": amount_e8})
        )
        if not result.ok or result.state is None or result.effects is None:
            raise ValueError(result.error or "redeem_zusd rejected")
        collateral_out = _require_int(result.effects.get("redeemed_collateral_out_e8"), name="redeemed_collateral_out_e8", minimum=0)
        balances.subtract(account, zusd_asset, units)
        native_account = native_sender if account == sender else account
        balances.add(native_account, NATIVE_ASSET, collateral_out)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units, "native_balance_delta_e8": collateral_out}

    if action == "liquidate":
        pre_deposits = dict(deposits)
        result = run_core(_core_command(action=action, args={}))
        if not result.ok or result.state is None or result.effects is None:
            raise ValueError(result.error or "liquidate rejected")
        liquidated_debt = _require_whole_zusd_amount(result.effects.get("liquidated_debt_e8"), name="liquidated_debt_e8")
        liquidated_coll = _require_int(
            result.effects.get("sp_collateral_gain_e8", result.effects.get("liquidated_collateral_e8")),
            name="sp_collateral_gain_e8",
            minimum=0,
        )
        liquidator_comp = _require_int(
            result.effects.get("liquidator_compensation_collateral_e8", 0),
            name="liquidator_compensation_collateral_e8",
            minimum=0,
        )
        debt_units = _e8_to_whole_units(liquidated_debt, name="liquidated_debt_e8")
        if balances.get(sp_pubkey, zusd_asset) < debt_units:
            raise ValueError("stability pool escrow balance too low")
        balances.subtract(sp_pubkey, zusd_asset, debt_units)
        if liquidator_comp > 0:
            balances.add(native_sender, NATIVE_ASSET, liquidator_comp)
        deposits, coll_gains = _allocate_stability_pool_liquidation(
            pre_deposits,
            debt_e8=liquidated_debt,
            collateral_e8=liquidated_coll,
        )
        for pk, gain in coll_gains.items():
            claims[pk] = int(claims.get(pk, 0)) + int(gain)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            **dict(result.effects or {}),
            "sp_escrow_delta": -debt_units,
            "native_balance_delta_e8": liquidator_comp,
            "sp_collateral_claims_e8": coll_gains,
        }

    if action == "claim_sp_collateral":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_int(op.get("amount_e8"), name="claim_sp_collateral.amount_e8", minimum=1)
        current = int(claims.get(account, 0))
        if amount_e8 > current:
            raise ValueError("claim exceeds account collateral gain")
        if amount_e8 > core.sp_coll_e8:
            raise ValueError("claim exceeds stability-pool collateral")
        next_core = ZUSDState(**{**core.__dict__, "sp_coll_e8": int(core.sp_coll_e8) - amount_e8})
        failures = check_invariants(next_core)
        if failures:
            raise ValueError(f"invariant violation: {','.join(failures)}")
        native_account = native_sender if account == sender else account
        balances.add(native_account, NATIVE_ASSET, amount_e8)
        claims = _set_or_drop(claims, account, current - amount_e8)
        next_state = ZUSDMonetaryState(
            core=next_core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "sp_collateral_claimed", "amount_e8": amount_e8, "native_balance_delta_e8": amount_e8}

    if action == "stake_fee_shares":
        account = _sender_account(op, sender=sender, action=action)
        stake_asset = runtime_policy.fee_stake_asset_id
        if stake_asset is None:
            raise ValueError("fee staking asset not configured")
        amount = _require_int(op.get("amount"), name="stake_fee_shares.amount", minimum=1)
        if balances.get(account, stake_asset) < amount:
            raise ValueError("insufficient fee stake balance")
        balances.subtract(account, stake_asset, amount)
        pending = dict(fee_fields["pending_fee_stakes"])
        pending_epochs = dict(fee_fields["pending_fee_stake_activation_epochs"])
        activation_epoch = (
            int(core.now_epoch)
            + int(runtime_policy.staking_activation_delay_epochs)
        )
        pending[account] = int(pending.get(account, 0)) + amount
        pending_epochs[account] = max(
            int(pending_epochs.get(account, 0)), activation_epoch
        )
        fee_fields = {**fee_fields, "pending_fee_stakes": pending, "pending_fee_stake_activation_epochs": pending_epochs}
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "fee_shares_staked_pending",
            "account_pubkey": account,
            "amount": amount,
            "activation_epoch": activation_epoch,
        }

    if action == "activate_fee_stake":
        account = _sender_account(op, sender=sender, action=action)
        fee_fields, amount, activation_epoch = _activate_fee_stake_for_account(
            fee_fields,
            account=account,
            now_epoch=int(core.now_epoch),
        )
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "fee_stake_activated",
            "account_pubkey": account,
            "amount": amount,
            "activation_epoch": activation_epoch,
        }

    if action == "unstake_fee_shares":
        account = _sender_account(op, sender=sender, action=action)
        stake_asset = runtime_policy.fee_stake_asset_id
        if stake_asset is None:
            raise ValueError("fee staking asset not configured")
        amount = _require_int(op.get("amount"), name="unstake_fee_shares.amount", minimum=1)
        active = dict(fee_fields["active_fee_stakes"])
        current = int(active.get(account, 0))
        if amount > current:
            raise ValueError("unstake_fee_shares exceeds active stake")
        if _fee_stake_claimable_e8(fee_fields, account) > 0:
            raise ValueError("claim staking fees before unstake")
        active = _set_or_drop(active, account, current - amount)
        reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
        if account in active:
            reward_debt[account] = _fee_stake_debt_for(
                active[account],
                int(fee_fields["staking_zusd_fee_acc_per_share_e8"]),
            )
        else:
            reward_debt.pop(account, None)
        balances.add(account, stake_asset, amount)
        fee_fields = {**fee_fields, "active_fee_stakes": active, "fee_stake_reward_debt_e8": reward_debt}
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "fee_shares_unstaked",
            "account_pubkey": account,
            "amount": amount,
        }

    if action == "claim_protocol_fees":
        recipient = _require_protocol_fee_recipient(authority_binding)
        if sender != recipient:
            raise ValueError("claim_protocol_fees recipient only")
        current = int(fee_fields["protocol_zusd_fee_reserve_e8"])
        requested_e8 = _optional_whole_zusd_amount(
            op.get("amount_e8"),
            name="claim_protocol_fees.amount_e8",
        )
        claim_e8 = current if requested_e8 is None else requested_e8
        if claim_e8 <= 0:
            raise ValueError("no protocol fees claimable")
        if claim_e8 > current:
            raise ValueError("claim_protocol_fees exceeds reserve")
        units = _e8_to_whole_units(
            claim_e8,
            name="claim_protocol_fees.amount_e8",
        )
        balances.add(sender, zusd_asset, units)
        fee_fields = {
            **fee_fields,
            "protocol_zusd_fee_reserve_e8": current - claim_e8,
        }
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "protocol_zusd_fees_claimed",
            "amount_e8": claim_e8,
            "zusd_balance_delta": units,
        }

    if action == "claim_host_fees":
        requested_e8 = _optional_whole_zusd_amount(op.get("amount_e8"), name="claim_host_fees.amount_e8")
        host_fees = dict(fee_fields["host_zusd_fees_e8"])
        current = int(host_fees.get(sender, 0))
        claim_e8 = current if requested_e8 is None else requested_e8
        if claim_e8 <= 0:
            raise ValueError("no host fees claimable")
        if claim_e8 > current:
            raise ValueError("claim_host_fees exceeds host claim")
        units = _e8_to_whole_units(claim_e8, name="claim_host_fees.amount_e8")
        balances.add(sender, zusd_asset, units)
        fee_fields = {
            **fee_fields,
            "host_zusd_fee_pool_e8": int(fee_fields["host_zusd_fee_pool_e8"]) - claim_e8,
            "host_zusd_fees_e8": _set_or_drop(host_fees, sender, current - claim_e8),
        }
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "host_zusd_fees_claimed", "amount_e8": claim_e8, "zusd_balance_delta": units}

    if action in {"claim_staking_fees", "claim_fee_rewards"}:
        account = _sender_account(op, sender=sender, action=action)
        claimable_e8 = _fee_stake_claimable_e8(fee_fields, account)
        requested_e8 = _optional_whole_zusd_amount(
            op.get("amount_e8"), name=f"{action}.amount_e8"
        )
        claim_e8 = claimable_e8 if requested_e8 is None else requested_e8
        if claim_e8 <= 0:
            raise ValueError("no staking fees claimable")
        if claim_e8 > claimable_e8:
            raise ValueError(f"{action} exceeds claimable fees")
        units = _e8_to_whole_units(claim_e8, name=f"{action}.amount_e8")
        balances.add(account, zusd_asset, units)
        reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
        reward_debt[account] = int(reward_debt.get(account, 0)) + claim_e8
        fee_fields = {
            **fee_fields,
            "staking_zusd_fee_pool_e8": int(fee_fields["staking_zusd_fee_pool_e8"]) - claim_e8,
            "fee_stake_reward_debt_e8": reward_debt,
        }
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "staking_zusd_fees_claimed",
            "account_pubkey": account,
            "amount_e8": claim_e8,
            "zusd_balance_delta": units,
        }

    raise ValueError(f"unknown action: {action}")


def _parse_ops(raw_ops: Any) -> list[Mapping[str, Any]]:
    if raw_ops is None:
        return []
    if not isinstance(raw_ops, list):
        raise TypeError("zusd monetary op stream must be a list")
    if len(raw_ops) > _MAX_OPS:
        raise ValueError(f"too many zusd ops: {len(raw_ops)} > {_MAX_OPS}")
    total_bytes = 0
    out: list[Mapping[str, Any]] = []
    for i, raw in enumerate(raw_ops):
        if not isinstance(raw, Mapping):
            raise TypeError(f"zusd op[{i}] must be an object")
        op = dict(raw)
        size = bounded_json_utf8_size(op, max_bytes=_MAX_OP_BYTES)
        total_bytes += size
        if total_bytes > _MAX_TOTAL_OPS_BYTES:
            raise ValueError("zusd op stream too large")
        out.append(op)
    return out


def _require_action(op: Mapping[str, Any], *, index: int) -> str:
    module = str(op.get("module", ZUSD_MONETARY_MODULE))
    if module != ZUSD_MONETARY_MODULE:
        raise ValueError(f"zusd op[{index}] module must be {ZUSD_MONETARY_MODULE}")
    version = str(op.get("version", ZUSD_MONETARY_VERSION))
    if version != ZUSD_MONETARY_VERSION:
        raise ValueError(f"zusd op[{index}] version unsupported: {version!r}")
    action = str(op.get("action", "")).strip().lower()
    if action not in {
        "bootstrap_oracle",
        "oracle_report",
        "oracle_commit",
        "deposit_collateral",
        "withdraw_collateral",
        "mint_zusd",
        "repay_zusd",
        "deposit_sp",
        "withdraw_sp",
        "redeem_zusd",
        "liquidate",
        "claim_sp_collateral",
        "stake_fee_shares",
        "activate_fee_stake",
        "unstake_fee_shares",
        "claim_protocol_fees",
        "claim_host_fees",
        "claim_staking_fees",
        "claim_fee_rewards",
    }:
        raise ValueError(f"zusd op[{index}] action unsupported: {action!r}")
    return action


def _allowed_fields_for_action(action: str) -> set[str]:
    base = {"module", "version", "action", "nonce", "deadline"}
    if action in {"bootstrap_oracle", "oracle_report"}:
        return base | {
            "price_e8",
            "oracle_observed_epoch",
            "oracle_authorization",
        }
    if action == "oracle_commit":
        return base
    if action == "mint_zusd":
        return base | {
            "owner_pubkey",
            "amount_e8",
            "host_pubkey",
            "oracle_authorization",
        }
    if action in {"deposit_collateral", "withdraw_collateral", "repay_zusd"}:
        return base | {"owner_pubkey", "amount_e8"}
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"}:
        return base | {"account_pubkey", "amount_e8"}
    if action in {"stake_fee_shares", "unstake_fee_shares"}:
        return base | {"account_pubkey", "amount"}
    if action == "activate_fee_stake":
        return base | {"account_pubkey"}
    if action in {
        "claim_protocol_fees",
        "claim_host_fees",
        "claim_staking_fees",
        "claim_fee_rewards",
    }:
        fields = base | {"amount_e8"}
        if action == "claim_fee_rewards":
            fields.add("account_pubkey")
        return fields
    if action == "liquidate":
        return base | {"oracle_authorization"}
    return base


_STRICT_ORACLE_AUTHORIZATION_ACTIONS = frozenset(
    {"liquidate", "mint_zusd"}
)


def _zusd_oracle_runtime_value_e8(
    *,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
) -> int:
    if action in {"bootstrap_oracle", "oracle_report"}:
        return _require_int(
            op.get("price_e8"),
            name=f"{action}.price_e8",
            minimum=1,
        )
    if action == "oracle_commit":
        return _require_int(
            monetary_state.core.price_pending_e8,
            name="oracle_commit.pending_price_e8",
            minimum=1,
        )
    if action in {"liquidate", "mint_zusd"}:
        return _require_int(
            monetary_state.core.price_e8,
            name=f"{action}.active_price_e8",
            minimum=1,
        )
    raise ValueError(f"{action} has no oracle authorization value")


def zusd_monetary_oracle_runtime_facts(
    *,
    runtime_policy: ZUSDRuntimePolicyBinding,
    staged_state: DexState,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
    sender: str,
) -> RuntimeActionFacts:
    """Derive exact stream-11 facts for the shared O3 authorization checker."""

    if action not in _STRICT_ORACLE_AUTHORIZATION_ACTIONS:
        raise ValueError(f"{action} has no strict oracle authorization profile")
    runtime_value_e8 = _zusd_oracle_runtime_value_e8(
        monetary_state=monetary_state,
        op=op,
        action=action,
    )
    monetary_prestate = zusd_monetary_state_to_obj(monetary_state)
    policy_prestate = monetary_prestate.get("runtime_policy_binding")
    if isinstance(policy_prestate, Mapping):
        policy_without_action_root = dict(policy_prestate)
        # The action receipt root is checked independently as the trusted
        # anchor below.  Excluding that one dynamic value avoids a hash
        # self-reference: the receipt itself binds this pre-state hash.
        policy_without_action_root.pop(
            "oracle_authorization_receipt_graph_root",
            None,
        )
        monetary_prestate["runtime_policy_binding"] = policy_without_action_root
    pre_state_hash = semantic_hash(
        "zenodex.zusd.stream11.pre_state.v1",
        {
            "dex_snapshot_commitment": snapshot_from_state(
                staged_state
            ).commitment_hex(),
            "monetary_state": monetary_prestate,
        },
    )
    if action == "liquidate":
        action_kind = "liquidate_vault"
        profile_id = ZUSD_LIQUIDATE_VAULT_PROFILE_ID
    elif action == "mint_zusd":
        action_kind = "mint"
        profile_id = ZUSD_MINT_PROFILE_ID
    else:
        action_kind = action
        profile_id = "critical-zusd-v1"
    bound_operation = {
        str(key): value
        for key, value in op.items()
        if key != "oracle_authorization"
    }
    action_facts_hash = semantic_hash(
        "zenodex.zusd.stream11.action_facts.v1",
        {
            "action": action,
            "action_kind": action_kind,
            "chain_id": runtime_policy.chain_id,
            "operation": bound_operation,
            "pre_state_hash": pre_state_hash,
            "query_id": ZUSD_COLLATERAL_QUERY_ID,
            "runtime_value_e8": runtime_value_e8,
            "sender": sender,
        },
    )
    action_id = semantic_hash(
        "zenodex.zusd.stream11.action_id.v1",
        {
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "profile_id": profile_id,
            "query_id": ZUSD_COLLATERAL_QUERY_ID,
            "runtime_value_e8": runtime_value_e8,
        },
    )
    runtime_notional_value_e8 = None
    if action == "liquidate":
        collateral_value_e8 = (
            int(monetary_state.core.collateral_e8) * runtime_value_e8
        ) // E8
        runtime_notional_value_e8 = max(
            int(monetary_state.core.debt_e8),
            collateral_value_e8,
        )
    elif action == "mint_zusd":
        principal_e8 = _require_whole_zusd_amount(
            op.get("amount_e8"),
            name="mint_zusd.amount_e8",
        )
        max_fee_e8 = (
            principal_e8 * int(runtime_policy.borrow_fee_max_bps)
            + BPS_SCALE
            - 1
        ) // BPS_SCALE
        runtime_notional_value_e8 = principal_e8 + max_fee_e8
    return RuntimeActionFacts(
        consumer_module="zenodex.zusd",
        action_kind=action_kind,
        action_id=action_id,
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id=profile_id,
        query_id=ZUSD_COLLATERAL_QUERY_ID,
        runtime_value_e8=runtime_value_e8,
        now_epoch=int(monetary_state.core.now_epoch),
        runtime_notional_value_e8=runtime_notional_value_e8,
    )


def _strict_oracle_authorization_check(
    *,
    runtime_policy: ZUSDRuntimePolicyBinding,
    staged_state: DexState,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
    sender: str,
) -> tuple[bool, tuple[str, ...]]:
    if action not in _STRICT_ORACLE_AUTHORIZATION_ACTIONS:
        return False, ()
    authorization = op.get("oracle_authorization")
    if not isinstance(authorization, Mapping):
        return False, ("oracle_authorization_required",)
    try:
        runtime = zusd_monetary_oracle_runtime_facts(
            runtime_policy=runtime_policy,
            staged_state=staged_state,
            monetary_state=monetary_state,
            op=op,
            action=action,
            sender=sender,
        )
        result = check_critical_consumer_authorization(
            authorization,
            consumer_module=runtime.consumer_module,
            action_kind=runtime.action_kind,
            action_id=runtime.action_id,
            action_facts_hash=runtime.action_facts_hash,
            pre_state_hash=runtime.pre_state_hash,
            profile_id=runtime.profile_id,
            query_id=runtime.query_id,
            runtime_value_e8=runtime.runtime_value_e8,
            now_epoch=runtime.now_epoch,
            runtime_notional_value_e8=runtime.runtime_notional_value_e8,
            expected_receipt_graph_root=(
                runtime_policy.oracle_authorization_receipt_graph_root
            ),
        )
    except (TypeError, ValueError) as exc:
        return False, (str(exc),)
    errors = result.get("typed_errors") or result.get("opaque_errors") or ()
    return bool(result.get("typed_ok") is True), tuple(str(error) for error in errors)


def _zusd_oracle_ingress_error(
    *,
    runtime_policy: ZUSDRuntimePolicyBinding,
    staged_state: DexState,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
    sender: str,
) -> str | None:
    if action not in {item.value for item in ZUSDOracleIngressAction}:
        return None
    profile = runtime_policy.oracle_evidence_profile
    if profile is ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0:
        # The legacy checks remain in _apply_one so their stable rejection
        # classes and configured-identity semantics are preserved exactly.
        return None

    authorization_bound, authorization_errors = (
        _strict_oracle_authorization_check(
            runtime_policy=runtime_policy,
            staged_state=staged_state,
            monetary_state=monetary_state,
            op=op,
            action=action,
            sender=sender,
        )
        if action in _STRICT_ORACLE_AUTHORIZATION_ACTIONS
        else (False, ())
    )
    # F02 finalized context, full F03 snapshot provenance, and pending-root
    # bindings do not exist in the current stream-11 shell.  Keeping these
    # facts false is the fail-closed nonclaim; neither block_timestamp nor a
    # configured operator is promoted into consensus evidence.
    decision = evaluate_zusd_oracle_ingress_admission(
        profile=profile,
        action=ZUSDOracleIngressAction(action),
        evidence=ZUSDOracleIngressEvidence(
            critical_action_authorization_bound=authorization_bound,
        ),
    )
    if decision.admitted:
        return None
    violations = ",".join(item.value for item in decision.violations)
    details = ""
    if authorization_errors and not authorization_bound:
        details = "; oracle_authorization=" + ";".join(
            authorization_errors[:3]
        )
    return (
        f"oracle ingress profile {profile.value} rejects: "
        f"{violations}{details}"
    )


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _canonical_chain_id(value: Any, *, name: str) -> str:
    chain_id = _require_str(value, name=name, max_len=128).strip()
    if not chain_id:
        raise ValueError(f"{name} must be non-empty")
    try:
        chain_id.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain only ASCII characters") from exc
    allowed_punctuation = frozenset("-._:/")
    if any(
        not (character.isalnum() or character in allowed_punctuation)
        for character in chain_id
    ):
        raise ValueError(f"{name} contains unsupported characters")
    return chain_id


def _require_int(value: Any, *, name: str, minimum: int = 0, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    out = int(value)
    if out < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if maximum is not None and out > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return out


def _require_nonnegative_int(value: Any, *, name: str) -> int:
    return _require_int(value, name=name, minimum=0)


def _raw_pubkey_key(value: Any) -> tuple[str, bool]:
    if not isinstance(value, str):
        return "", False
    raw = value.strip().lower()
    had_0x = raw.startswith("0x")
    return (raw[2:] if had_0x else raw), had_0x


def _native_sender_key(
    balances: BalanceTable,
    *,
    sender: str,
    raw_sender: str,
    sender_had_0x: bool,
) -> str:
    if raw_sender and raw_sender != sender and (not sender_had_0x or balances.get(raw_sender, NATIVE_ASSET) > 0):
        return raw_sender
    return sender


def _require_whole_zusd_amount(value: Any, *, name: str) -> int:
    amount = _require_int(value, name=name, minimum=1)
    if amount % E8 != 0:
        raise ValueError(f"{name} must be a whole zUSD amount in E8")
    return amount


def _optional_whole_zusd_amount(value: Any, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_whole_zusd_amount(value, name=name)


def _e8_to_whole_units(amount_e8: int, *, name: str) -> int:
    amount = _require_whole_zusd_amount(amount_e8, name=name)
    return amount // E8


def _canonical_pubkey(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a 48-byte hex pubkey string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a 32-byte hex asset string")
    asset = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if asset == NATIVE_ASSET:
        raise ValueError("zUSD asset cannot be native asset")
    return asset


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def _copy_nonce_table(nonces: NonceTable) -> NonceTable:
    copied = NonceTable()
    for pk, last in nonces.get_all().items():
        copied.set_last(pk, int(last))
    return copied


def _account_amount_entries(value: Mapping[str, int] | None, *, amount_key: str) -> list[dict[str, Any]]:
    return [
        {"pubkey": pk, amount_key: int(amount)}
        for pk, amount in sorted(dict(value or {}).items())
        if int(amount) > 0
    ]


def _parse_account_amount_entries(value: Any, *, name: str, amount_key: str = "amount_e8") -> dict[str, int]:
    if value is None:
        return {}
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: dict[str, int] = {}
    for i, entry in enumerate(value):
        if not isinstance(entry, Mapping):
            raise TypeError(f"{name}[{i}] must be an object")
        pk = _canonical_pubkey(entry.get("pubkey"), name=f"{name}[{i}].pubkey")
        amount = _require_nonnegative_int(entry.get(amount_key), name=f"{name}[{i}].{amount_key}")
        if amount == 0:
            continue
        if pk in out:
            raise ValueError(f"{name}[{i}] duplicate pubkey")
        out[pk] = int(amount)
    return out


def _parse_pending_fee_stake_entries(value: Any) -> tuple[dict[str, int], dict[str, int]]:
    if value is None:
        return {}, {}
    if not isinstance(value, list):
        raise TypeError("zusd_monetary.pending_fee_stakes must be a list")
    stakes: dict[str, int] = {}
    epochs: dict[str, int] = {}
    for i, entry in enumerate(value):
        if not isinstance(entry, Mapping):
            raise TypeError(f"zusd_monetary.pending_fee_stakes[{i}] must be an object")
        pk = _canonical_pubkey(entry.get("pubkey"), name=f"zusd_monetary.pending_fee_stakes[{i}].pubkey")
        amount = _require_nonnegative_int(
            entry.get("amount"),
            name=f"zusd_monetary.pending_fee_stakes[{i}].amount",
        )
        activation_epoch = _require_nonnegative_int(
            entry.get("activation_epoch"),
            name=f"zusd_monetary.pending_fee_stakes[{i}].activation_epoch",
        )
        if amount == 0:
            continue
        if pk in stakes:
            raise ValueError(f"zusd_monetary.pending_fee_stakes[{i}] duplicate pubkey")
        stakes[pk] = amount
        epochs[pk] = activation_epoch
    return stakes, epochs


def _deadline_error(*, op: Mapping[str, Any], block_timestamp: int, index: int) -> str | None:
    raw = op.get("deadline")
    if raw is None:
        return None
    deadline = _require_int(raw, name=f"zusd op[{index}].deadline", minimum=1, maximum=_U32_MAX)
    if int(block_timestamp) > int(deadline):
        return f"zusd op[{index}].deadline expired"
    return None


def _require_committed_authority_binding(
    state: ZUSDMonetaryState,
) -> ZUSDAuthorityBinding:
    binding = state.authority_binding
    if binding is None:
        raise ValueError("zUSD authority binding is missing")
    return binding


def _require_committed_runtime_policy_binding(
    state: ZUSDMonetaryState,
) -> ZUSDRuntimePolicyBinding:
    binding = state.runtime_policy_binding
    if binding is None:
        raise ValueError("zUSD runtime policy binding is missing")
    return binding


def _legacy_state_is_pristine_for_authority_binding(
    state: ZUSDMonetaryState,
) -> bool:
    """Return whether binding current config cannot redirect prior authority.

    Version-1 snapshots did not commit authority identities. Automatic binding
    is safe only before an authority-sensitive or value-moving transition has
    occurred. Policy parameters may differ from defaults, so this predicate
    inspects operational state and cumulative history rather than comparing the
    complete core object with ``init_state()``.
    """

    core = state.core
    core_history = (
        int(core.now_epoch),
        int(core.oracle_last_update_epoch),
        int(core.oracle_pending_update_epoch),
        int(core.price_e8),
        int(core.price_pending_e8),
        int(core.collateral_e8),
        int(core.debt_e8),
        int(core.free_debt_e8),
        int(core.sp_debt_e8),
        int(core.sp_coll_e8),
        int(core.protocol_collateral_e8),
        int(core.protocol_revenue_zusd_cum_e8),
        int(core.liquidator_compensation_collateral_cum_e8),
        int(core.base_rate_bps),
        int(core.base_rate_last_epoch),
    )
    monetary_history = (
        int(state.protocol_zusd_fee_reserve_e8),
        int(state.staking_zusd_fee_pool_e8),
        int(state.staking_zusd_fee_acc_per_share_e8),
        int(state.host_zusd_fee_pool_e8),
        int(state.host_zusd_fee_cum_e8),
    )
    tables = (
        state.sp_deposits_e8,
        state.sp_collateral_claims_e8,
        state.host_zusd_fees_e8,
        state.active_fee_stakes,
        state.pending_fee_stakes,
        state.pending_fee_stake_activation_epochs,
        state.fee_stake_reward_debt_e8,
    )
    return (
        core.oracle_seen is False
        and state.vault_owner_pubkey is None
        and (
            state.shutdown_extension is None
            or state.shutdown_extension.phase is ZUSDShutdownPhase.OPEN
        )
        and all(value == 0 for value in core_history)
        and all(value == 0 for value in monetary_history)
        and all(not dict(table or {}) for table in tables)
    )


def _bind_or_validate_authority_config(
    *,
    state: ZUSDMonetaryState,
    config: ZUSDMonetaryConfig,
) -> ZUSDMonetaryState:
    configured = ZUSDAuthorityBinding.from_config(config)
    committed = state.authority_binding
    if committed is None:
        if not _legacy_state_is_pristine_for_authority_binding(state):
            raise ValueError(
                "zUSD authority binding missing for non-pristine legacy state"
            )
        return replace(state, authority_binding=configured)

    for field_name in (
        "oracle_pubkey",
        "epoch_operator_pubkey",
        "protocol_fee_recipient_pubkey",
    ):
        if getattr(committed, field_name) != getattr(configured, field_name):
            raise ValueError(f"zUSD authority config drift: {field_name}")
    return state


def _bind_or_validate_runtime_policy_config(
    *,
    state: ZUSDMonetaryState,
    config: ZUSDMonetaryConfig,
) -> ZUSDMonetaryState:
    configured = ZUSDRuntimePolicyBinding.from_config(config)
    committed = state.runtime_policy_binding
    if committed is None:
        if not _legacy_state_is_pristine_for_authority_binding(state):
            raise ValueError(
                "zUSD runtime policy binding missing for non-pristine legacy state"
            )
        return replace(
            state,
            runtime_policy_binding=configured,
            shutdown_extension=(
                None
                if configured.shutdown_extension_profile is None
                else ZUSDShutdownExtensionState(
                    profile=configured.shutdown_extension_profile
                )
            ),
        )

    for field_name in (
        "chain_id",
        "zusd_asset_id",
        "stability_pool_pubkey",
        "fee_stake_asset_id",
        "liquidation_gas_comp_fixed_collateral_e8",
        "liquidation_gas_comp_bps",
        "borrow_fee_floor_bps",
        "borrow_fee_max_bps",
        "host_protocol_fee_share_bps",
        "staking_activation_delay_epochs",
        "oracle_evidence_profile",
        "oracle_authorization_receipt_graph_root",
        "shutdown_extension_profile",
    ):
        if getattr(committed, field_name) != getattr(configured, field_name):
            raise ValueError(
                f"zUSD runtime policy config drift: {field_name}"
            )
    return state


def _require_oracle_sender(
    authority_binding: ZUSDAuthorityBinding,
    *,
    sender: str,
) -> None:
    oracle = (authority_binding.oracle_pubkey or "").strip()
    if not oracle:
        raise ValueError("zUSD oracle signer not configured")
    if sender != oracle:
        raise ValueError("zUSD oracle action requires oracle sender")


def _require_epoch_operator(
    authority_binding: ZUSDAuthorityBinding,
    *,
    sender: str,
) -> None:
    operator = (authority_binding.epoch_operator_pubkey or "").strip()
    if not operator:
        raise ValueError("advance_epoch operator not configured")
    if sender != operator:
        raise ValueError("advance_epoch operator only")


def _require_protocol_fee_recipient(
    authority_binding: ZUSDAuthorityBinding,
) -> str:
    recipient = (
        authority_binding.protocol_fee_recipient_pubkey or ""
    ).strip()
    if not recipient:
        raise ValueError("protocol fee recipient not configured")
    return recipient


def _require_live_oracle_observed_epoch(
    *,
    core: ZUSDState,
    op: Mapping[str, Any],
    action: str,
) -> int:
    """Project the signed stream-11 observation epoch into the core command.

    The outer Tau transaction authenticates the complete operation object. Live
    ingress therefore requires this field explicitly and accepts it only when
    it is ordered and fresh relative to the deterministic zUSD epoch state.
    """

    field_name = f"{action}.oracle_observed_epoch"
    if "oracle_observed_epoch" not in op:
        raise ValueError(f"{field_name} is required")
    observed_epoch = _require_int(
        op.get("oracle_observed_epoch"),
        name=field_name,
        minimum=0,
    )
    now_epoch = int(core.now_epoch)
    if observed_epoch > now_epoch:
        raise ValueError(f"{field_name} cannot be in the future")
    if action == "oracle_report" and observed_epoch < int(core.oracle_pending_update_epoch):
        raise ValueError(f"{field_name} regressed")
    if now_epoch - observed_epoch > int(core.max_oracle_staleness_epochs):
        raise ValueError(f"{field_name} is stale")
    return observed_epoch


def _sender_account(op: Mapping[str, Any], *, sender: str, action: str) -> str:
    account = _canonical_pubkey(op.get("account_pubkey", sender), name=f"{action}.account_pubkey")
    if account != sender:
        raise ValueError("account_pubkey mismatch")
    return account


def _set_or_drop(table: dict[str, int], key: str, value: int) -> dict[str, int]:
    out = dict(table)
    if value <= 0:
        out.pop(key, None)
    else:
        out[key] = int(value)
    return out


def _fee_state_fields(state: ZUSDMonetaryState) -> dict[str, Any]:
    return {
        "shutdown_extension": state.shutdown_extension,
        "authority_binding": state.authority_binding,
        "runtime_policy_binding": state.runtime_policy_binding,
        "protocol_zusd_fee_reserve_e8": int(state.protocol_zusd_fee_reserve_e8),
        "staking_zusd_fee_pool_e8": int(state.staking_zusd_fee_pool_e8),
        "staking_zusd_fee_acc_per_share_e8": int(state.staking_zusd_fee_acc_per_share_e8),
        "host_zusd_fee_pool_e8": int(state.host_zusd_fee_pool_e8),
        "host_zusd_fee_cum_e8": int(state.host_zusd_fee_cum_e8),
        "host_zusd_fees_e8": dict(state.host_zusd_fees_e8 or {}),
        "active_fee_stakes": dict(state.active_fee_stakes or {}),
        "pending_fee_stakes": dict(state.pending_fee_stakes or {}),
        "pending_fee_stake_activation_epochs": dict(state.pending_fee_stake_activation_epochs or {}),
        "fee_stake_reward_debt_e8": dict(state.fee_stake_reward_debt_e8 or {}),
    }


def _fee_stake_debt_for(shares: int, acc_per_share_e8: int) -> int:
    return (int(shares) * int(acc_per_share_e8)) // _FEE_ACC_SCALE


def _fee_stake_claimable_e8(fee_fields: Mapping[str, Any], account: str) -> int:
    active = dict(fee_fields["active_fee_stakes"])
    reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
    shares = int(active.get(account, 0))
    if shares <= 0:
        return 0
    accrued = _fee_stake_debt_for(shares, int(fee_fields["staking_zusd_fee_acc_per_share_e8"]))
    return max(0, accrued - int(reward_debt.get(account, 0)))


def _require_fee_routes_transport_exact(
    *,
    authority_binding: ZUSDAuthorityBinding,
    fee_fields: Mapping[str, Any],
    fee_effects: Mapping[str, Any],
) -> None:
    """Reject fee liabilities that the v0.1 whole-zUSD transport cannot pay.

    The core accounts in E8 while the live Tau asset uses whole zUSD units.
    A mint may therefore commit only when every newly routed fee and every
    resulting claimant balance is representable by that transport. Exact
    equality between the staking pool and its claimants also rules out
    accumulator dust that could otherwise leave debt with no reachable token.
    """

    routed: dict[str, int] = {}
    for field_name in (
        "mint_fee_host_e8",
        "mint_fee_staking_e8",
        "mint_fee_protocol_e8",
    ):
        amount_e8 = _require_nonnegative_int(
            fee_effects.get(field_name),
            name=field_name,
        )
        if amount_e8 % E8 != 0:
            raise ValueError(
                "mint fee routes must be whole zUSD at v0.1 transport"
            )
        routed[field_name] = amount_e8

    if routed["mint_fee_protocol_e8"] > 0:
        _require_protocol_fee_recipient(authority_binding)

    host_fees = dict(fee_fields["host_zusd_fees_e8"])
    if any(int(amount_e8) % E8 != 0 for amount_e8 in host_fees.values()):
        raise ValueError(
            "host fee claims must be whole zUSD at v0.1 transport"
        )

    active_stakes = dict(fee_fields["active_fee_stakes"])
    claimables = tuple(
        _fee_stake_claimable_e8(fee_fields, pubkey)
        for pubkey in sorted(active_stakes)
    )
    if any(claimable_e8 % E8 != 0 for claimable_e8 in claimables):
        raise ValueError(
            "staking fee claims must be whole zUSD at v0.1 transport"
        )
    if sum(claimables) != int(fee_fields["staking_zusd_fee_pool_e8"]):
        raise ValueError(
            "staking fee pool must equal exactly claimable fees at v0.1 transport"
        )


def _activate_fee_stake_for_account(
    fee_fields: Mapping[str, Any],
    *,
    account: str,
    now_epoch: int,
) -> tuple[dict[str, Any], int, int]:
    out = dict(fee_fields)
    active = dict(out["active_fee_stakes"])
    pending = dict(out["pending_fee_stakes"])
    pending_epochs = dict(out["pending_fee_stake_activation_epochs"])
    reward_debt = dict(out["fee_stake_reward_debt_e8"])
    acc = int(out["staking_zusd_fee_acc_per_share_e8"])
    amount = int(pending.get(account, 0))
    if amount <= 0:
        raise ValueError("no pending fee stake")
    activation_epoch = int(pending_epochs.get(account, 0))
    if activation_epoch > now_epoch:
        raise ValueError("fee stake not mature")
    active[account] = int(active.get(account, 0)) + amount
    reward_debt[account] = int(reward_debt.get(account, 0)) + _fee_stake_debt_for(
        amount, acc
    )
    pending.pop(account, None)
    pending_epochs.pop(account, None)
    out["active_fee_stakes"] = active
    out["pending_fee_stakes"] = pending
    out["pending_fee_stake_activation_epochs"] = pending_epochs
    out["fee_stake_reward_debt_e8"] = reward_debt
    return out, amount, activation_epoch


def _route_mint_fee(
    *,
    runtime_policy: ZUSDRuntimePolicyBinding,
    fee_fields: Mapping[str, Any],
    mint_fee_e8: int,
    host_pubkey: Any,
) -> tuple[dict[str, Any], dict[str, Any]]:
    fee_e8 = _require_nonnegative_int(mint_fee_e8, name="mint_fee_e8")
    out = dict(fee_fields)
    if fee_e8 == 0:
        return out, {"mint_fee_host_e8": 0, "mint_fee_staking_e8": 0, "mint_fee_protocol_e8": 0}

    host_fee_e8 = 0
    host: str | None = None
    if host_pubkey is not None:
        host = _canonical_pubkey(host_pubkey, name="mint_zusd.host_pubkey")
        host_fee_e8 = (
            fee_e8 * int(runtime_policy.host_protocol_fee_share_bps)
        ) // BPS_SCALE
    non_host_fee_e8 = fee_e8 - host_fee_e8

    if host is not None and host_fee_e8 > 0:
        host_fees = dict(out["host_zusd_fees_e8"])
        host_fees[host] = int(host_fees.get(host, 0)) + host_fee_e8
        out["host_zusd_fees_e8"] = host_fees
        out["host_zusd_fee_pool_e8"] = int(out["host_zusd_fee_pool_e8"]) + host_fee_e8
        out["host_zusd_fee_cum_e8"] = int(out["host_zusd_fee_cum_e8"]) + host_fee_e8

    active_total = sum(int(v) for v in dict(out["active_fee_stakes"]).values())
    staking_fee_e8 = 0
    protocol_fee_e8 = 0
    if active_total > 0 and non_host_fee_e8 > 0:
        staking_fee_e8 = non_host_fee_e8
        out["staking_zusd_fee_pool_e8"] = int(out["staking_zusd_fee_pool_e8"]) + staking_fee_e8
        out["staking_zusd_fee_acc_per_share_e8"] = int(out["staking_zusd_fee_acc_per_share_e8"]) + (
            staking_fee_e8 * _FEE_ACC_SCALE
        ) // active_total
    else:
        protocol_fee_e8 = non_host_fee_e8
        out["protocol_zusd_fee_reserve_e8"] = int(out["protocol_zusd_fee_reserve_e8"]) + protocol_fee_e8

    return out, {
        "mint_fee_host_e8": host_fee_e8,
        "mint_fee_staking_e8": staking_fee_e8,
        "mint_fee_protocol_e8": protocol_fee_e8,
    }


def _state_invariant_error(state: ZUSDMonetaryState) -> str | None:
    failed = check_invariants(state.core)
    if failed:
        return f"invariant violation: {','.join(failed)}"
    runtime_policy = state.runtime_policy_binding
    if runtime_policy is not None:
        for field_name in (
            "liquidation_gas_comp_fixed_collateral_e8",
            "liquidation_gas_comp_bps",
            "borrow_fee_floor_bps",
            "borrow_fee_max_bps",
        ):
            if int(getattr(state.core, field_name)) != int(
                getattr(runtime_policy, field_name)
            ):
                return f"runtime policy/core mismatch: {field_name}"
        mounted_shutdown_profile = (
            None
            if state.shutdown_extension is None
            else state.shutdown_extension.profile
        )
        if mounted_shutdown_profile is not runtime_policy.shutdown_extension_profile:
            return "runtime policy/core mismatch: shutdown_extension_profile"
    deposits = {pk: int(amount) for pk, amount in dict(state.sp_deposits_e8 or {}).items() if int(amount) > 0}
    claims = {pk: int(amount) for pk, amount in dict(state.sp_collateral_claims_e8 or {}).items() if int(amount) > 0}
    host_fees = {pk: int(amount) for pk, amount in dict(state.host_zusd_fees_e8 or {}).items() if int(amount) > 0}
    active_stakes = {pk: int(amount) for pk, amount in dict(state.active_fee_stakes or {}).items() if int(amount) > 0}
    pending_stakes = {pk: int(amount) for pk, amount in dict(state.pending_fee_stakes or {}).items() if int(amount) > 0}
    pending_epochs = dict(state.pending_fee_stake_activation_epochs or {})
    if sum(deposits.values()) != int(state.core.sp_debt_e8):
        return "stability pool account deposits do not match core sp_debt_e8"
    if sum(claims.values()) > int(state.core.sp_coll_e8):
        return "stability pool collateral claims exceed core sp_coll_e8"
    if sum(host_fees.values()) != int(state.host_zusd_fee_pool_e8):
        return "host zUSD fee claims do not match host_zusd_fee_pool_e8"
    for field_name, amount_e8 in (
        (
            "protocol_zusd_fee_reserve_e8",
            int(state.protocol_zusd_fee_reserve_e8),
        ),
        ("staking_zusd_fee_pool_e8", int(state.staking_zusd_fee_pool_e8)),
        ("host_zusd_fee_pool_e8", int(state.host_zusd_fee_pool_e8)),
    ):
        if amount_e8 % E8 != 0:
            return f"{field_name} must be whole zUSD at v0.1 transport"
    if any(amount_e8 % E8 != 0 for amount_e8 in host_fees.values()):
        return "host fee claims must be whole zUSD at v0.1 transport"
    if int(state.host_zusd_fee_pool_e8) > int(state.host_zusd_fee_cum_e8):
        return "host_zusd_fee_pool_e8 exceeds host_zusd_fee_cum_e8"
    if set(pending_epochs) != set(pending_stakes):
        return "pending fee stake activation keys mismatch"
    fee_fields = _fee_state_fields(state)
    claimables = tuple(
        _fee_stake_claimable_e8(fee_fields, pk)
        for pk in sorted(active_stakes)
    )
    if any(claimable_e8 % E8 != 0 for claimable_e8 in claimables):
        return "staking fee claims must be whole zUSD at v0.1 transport"
    if sum(claimables) != int(state.staking_zusd_fee_pool_e8):
        return "staking zUSD fee claimables do not match staking_zusd_fee_pool_e8"
    if state.vault_owner_pubkey is None and (state.core.collateral_e8 > 0 or state.core.debt_e8 > 0):
        return "non-empty vault requires vault_owner_pubkey"
    return None


def _raise_if_bad_state(state: ZUSDMonetaryState) -> None:
    err = _state_invariant_error(state)
    if err is not None:
        raise ValueError(err)


def _asset_identity(value: object, *, name: str) -> str:
    """Canonicalize fixed 32-byte asset ids while preserving symbolic ids."""

    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    stripped = value.strip()
    body = stripped[2:] if stripped.lower().startswith("0x") else stripped
    if len(body) != 64 or any(character not in "0123456789abcdefABCDEF" for character in body):
        return value
    return canonical_hex_fixed_allow_0x(stripped, nbytes=32, name=name)


def _asset_matches(value: object, *, asset_id: str, name: str) -> bool:
    return _asset_identity(value, name=name) == _asset_identity(
        asset_id,
        name="asset_id",
    )


def _perps_quote_liability_e8(state: DexState, *, zusd_asset: str) -> int:
    perps = state.perps
    if perps is None:
        return 0

    total = 0
    for market_id in sorted(perps.markets):
        market = perps.markets[market_id]
        if not _asset_matches(
            market.quote_asset,
            asset_id=zusd_asset,
            name=f"perps[{market_id}].quote_asset",
        ):
            continue
        if type(market) is PerpMarketState:
            account_collateral = sum(
                _require_int(
                    account.collateral_quote,
                    name=f"perps[{market_id}].account[{account_id}].collateral_quote",
                )
                for account_id, account in sorted(market.accounts.items())
            )
            insurance_balance = _require_int(
                market.global_state["insurance_balance"],
                name=f"perps[{market_id}].insurance_balance",
            )
            # fee_pool_quote is a subledger of fee_income already included in
            # insurance_balance; counting it again would create phantom custody.
            total += (account_collateral + insurance_balance) * E8
        elif type(market) in (
            PerpClearinghouse2pMarketState,
            PerpClearinghouse3pTransferMarketState,
        ):
            total += _require_int(
                market.state["net_deposited_e8"],
                name=f"perps[{market_id}].net_deposited_e8",
            )
        elif type(market) is PerpClearinghouseNpMarketState:
            net_deposited_e8 = market.global_state["net_deposited_e8"]
            insurance_ext_e8 = market.global_state["insurance_ext_e8"]
            if type(net_deposited_e8) is not int or type(insurance_ext_e8) is not int:
                raise TypeError(f"perps[{market_id}] source liabilities must be ints")
            market_total = net_deposited_e8 + insurance_ext_e8
            if market_total < 0:
                raise ValueError(f"perps[{market_id}] source liability must be non-negative")
            total += market_total
        else:
            raise TypeError(
                f"perps[{market_id}] has unsupported liability semantics: "
                f"{type(market).__name__}"
            )
    return total


def _dex_pool_liability_e8(state: DexState, *, asset_id: str) -> int:
    """Return an asset's complete DEX-pool custody liability in E8 units.

    Pool reserves and wallet balances share whole-token units.  Iterating by
    canonical pool id makes the extraction deterministic even if the backing
    mapping was assembled in a different insertion order.
    """

    total_whole = 0
    for pool_id in sorted(state.pools):
        pool = state.pools[pool_id]
        if _asset_matches(
            pool.asset0,
            asset_id=asset_id,
            name=f"pool[{pool_id}].asset0",
        ):
            total_whole += _require_int(
                pool.reserve0,
                name=f"pool[{pool_id}].reserve0",
            )
        if _asset_matches(
            pool.asset1,
            asset_id=asset_id,
            name=f"pool[{pool_id}].asset1",
        ):
            total_whole += _require_int(
                pool.reserve1,
                name=f"pool[{pool_id}].reserve1",
            )
    return total_whole * E8


def _assert_sp_escrow_matches(
    balances: BalanceTable,
    state: ZUSDMonetaryState,
    *,
    zusd_asset: str,
    sp_pubkey: str,
) -> None:
    expected = _e8_to_whole_units(int(state.core.sp_debt_e8), name="sp_debt_e8") if state.core.sp_debt_e8 else 0
    actual = 0
    for (pubkey, asset), amount in sorted(
        balances.get_all_balances().items(),
    ):
        if pubkey != sp_pubkey:
            continue
        if _asset_matches(
            asset,
            asset_id=zusd_asset,
            name=f"stability_pool[{pubkey}].asset",
        ):
            actual += _require_int(
                amount,
                name=f"stability_pool[{pubkey}].amount",
            )
    if actual != expected:
        raise ValueError(f"stability pool escrow mismatch (expected {expected}, got {actual})")


def _assert_free_debt_liability_cover(
    balances: BalanceTable,
    state: ZUSDMonetaryState,
    *,
    zusd_asset: str,
    sp_pubkey: str,
    perps_zusd_liability_e8: int,
    dex_pool_zusd_liability_e8: int,
) -> None:
    external_free_e8 = _wallet_asset_liability_e8(
        balances,
        asset_id=zusd_asset,
        excluded_pubkey=sp_pubkey,
    )
    decision = evaluate_zusd_free_debt_liability_cover(
        breakdown=ZUSDFreeDebtLiabilityBreakdown(
            wallet_e8=external_free_e8,
            dex_pool_e8=dex_pool_zusd_liability_e8,
            perps_e8=perps_zusd_liability_e8,
            protocol_fee_reserve_e8=int(state.protocol_zusd_fee_reserve_e8),
            staking_fee_pool_e8=int(state.staking_zusd_fee_pool_e8),
            host_fee_pool_e8=int(state.host_zusd_fee_pool_e8),
        ),
        actual_free_debt_e8=int(state.core.free_debt_e8),
    )
    if not decision.covered:
        raise ValueError(
            "free debt liability cover mismatch "
            f"(expected {decision.expected_free_debt_e8}, "
            f"got {decision.actual_free_debt_e8})"
        )


def _wallet_asset_liability_e8(
    balances: BalanceTable,
    *,
    asset_id: str,
    excluded_pubkey: str | None = None,
) -> int:
    total_whole = 0
    for (pubkey, asset), amount in sorted(
        balances.get_all_balances().items(),
    ):
        if pubkey == excluded_pubkey:
            continue
        if _asset_matches(
            asset,
            asset_id=asset_id,
            name=f"balance[{pubkey}].asset",
        ):
            total_whole += _require_int(
                amount,
                name=f"balance[{pubkey}].amount",
            )
    return total_whole * E8


def assert_zusd_global_liability_cover(
    *,
    state: DexState,
    zusd_state: ZUSDMonetaryState | None,
    expected_zusd_asset_id: str,
) -> None:
    """Fail closed unless all canonical zUSD custody matches core liabilities.

    This is the authoritative cross-module composition check.  It derives the
    canonical asset and Stability Pool principal from the policy committed in
    ``zusd_state``; callers cannot substitute an alternate asset or escrow.
    """

    expected_asset = _asset_identity(
        expected_zusd_asset_id,
        name="expected_zusd_asset_id",
    )
    if state.vault is not None and (
        state.vault.reward_balance != 0 or state.vault.pending_rewards != 0
    ):
        raise ValueError(
            "untyped legacy vault reward custody is unsupported with canonical zUSD"
        )
    if zusd_state is None:
        inventory_e8 = (
            _wallet_asset_liability_e8(
                state.balances,
                asset_id=expected_asset,
            )
            + _dex_pool_liability_e8(
                state,
                asset_id=expected_asset,
            )
            + _perps_quote_liability_e8(
                state,
                zusd_asset=expected_asset,
            )
        )
        if inventory_e8:
            raise ValueError(
                "canonical zUSD inventory requires committed monetary state "
                f"(found {inventory_e8})"
            )
        return
    runtime_policy = _require_committed_runtime_policy_binding(zusd_state)
    zusd_asset = runtime_policy.zusd_asset_id
    if _asset_identity(zusd_asset, name="runtime_policy.zusd_asset_id") != expected_asset:
        raise ValueError("committed zUSD asset does not match the active chain")
    sp_pubkey = runtime_policy.stability_pool_pubkey
    _assert_sp_escrow_matches(
        state.balances,
        zusd_state,
        zusd_asset=zusd_asset,
        sp_pubkey=sp_pubkey,
    )
    _assert_free_debt_liability_cover(
        state.balances,
        zusd_state,
        zusd_asset=zusd_asset,
        sp_pubkey=sp_pubkey,
        perps_zusd_liability_e8=_perps_quote_liability_e8(
            state,
            zusd_asset=zusd_asset,
        ),
        dex_pool_zusd_liability_e8=_dex_pool_liability_e8(
            state,
            asset_id=zusd_asset,
        ),
    )


def _allocate_stability_pool_liquidation(
    deposits: Mapping[str, int],
    *,
    debt_e8: int,
    collateral_e8: int,
) -> tuple[dict[str, int], dict[str, int]]:
    total = sum(int(v) for v in deposits.values())
    if total <= 0:
        raise ValueError("stability pool has no account deposits")
    if debt_e8 > total:
        raise ValueError("liquidation debt exceeds account deposits")

    rows = [(pk, int(amount)) for pk, amount in sorted(deposits.items()) if int(amount) > 0]
    debt_losses: dict[str, int] = {}
    coll_gains: dict[str, int] = {}
    assigned_debt = 0
    assigned_coll = 0
    for pk, amount in rows:
        loss = (debt_e8 * amount) // total
        gain = (collateral_e8 * amount) // total if collateral_e8 > 0 else 0
        debt_losses[pk] = int(loss)
        coll_gains[pk] = int(gain)
        assigned_debt += int(loss)
        assigned_coll += int(gain)

    debt_rem = int(debt_e8) - assigned_debt
    for pk, _amount in sorted(rows, key=lambda item: (-item[1], item[0])):
        if debt_rem <= 0:
            break
        available = int(deposits[pk]) - int(debt_losses.get(pk, 0))
        if available <= 0:
            continue
        take = min(available, debt_rem)
        debt_losses[pk] = int(debt_losses.get(pk, 0)) + take
        debt_rem -= take
    if debt_rem != 0:
        raise ValueError("failed to allocate liquidation debt exactly")

    coll_rem = int(collateral_e8) - assigned_coll
    for pk, _amount in sorted(rows, key=lambda item: (-item[1], item[0])):
        if coll_rem <= 0:
            break
        coll_gains[pk] = int(coll_gains.get(pk, 0)) + 1
        coll_rem -= 1
    if coll_rem != 0:
        raise ValueError("failed to allocate liquidation collateral exactly")

    next_deposits: dict[str, int] = {}
    for pk, amount in rows:
        remaining = amount - int(debt_losses.get(pk, 0))
        if remaining > 0:
            next_deposits[pk] = int(remaining)
    coll_gains = {pk: int(amount) for pk, amount in coll_gains.items() if int(amount) > 0}
    return next_deposits, coll_gains


def _safe_error_str(exc: Exception) -> str:
    if isinstance(exc, (ValueError, TypeError, KeyError)):
        msg = str(exc)
    else:
        msg = f"internal error: {type(exc).__name__}"
    msg = " ".join((msg or "").split())
    if not msg:
        msg = "internal error"
    if len(msg) > 512:
        msg = msg[:512]
    return msg
