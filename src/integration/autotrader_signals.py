from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING, Any, Mapping

from ..agents.strategy_ir import StrategyAction, StrategyIR
from ..core.quote_receipts import verify_route_quote_receipt
from ..kernels.python.strategy_external_signal_contract_v1_adapter import (
    ADVISORY_EXTERNAL_SOURCE_CODE,
    ADVISORY_TRUST_TIER_CODE,
    ATTESTED_EXTERNAL_SOURCE_CODE,
    ATTESTED_TRUST_TIER_CODE,
    VERIFIED_TRUST_TIER_CODE,
    check_strategy_external_signal_contract,
)
from ..state.pools import PoolState

if TYPE_CHECKING:
    from .autotrader_signal_registry import ExternalSignalSourceRegistry

_SAFE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")
_U32_MAX = 0xFFFFFFFF
SIGNAL_PACKET_SCHEMA = "zenodex/autotrader-signal-packet/v1"
OBSERVATION_PACKET_SCHEMA = "zenodex/autotrader-observation-packet/v1"
EXTERNAL_SIGNAL_SCHEMA = "zenodex/autotrader-external-signal/v1"
WALLET_CAPABILITY_SCHEMA = "zenodex/autotrader-wallet-capability/v1"


class SignalSourceKind(Enum):
    ROUTE_QUOTE_RECEIPT = "route_quote_receipt"
    LOCAL_PROTOCOL_STATE = "local_protocol_state"
    ATTESTED_EXTERNAL = "attested_external"
    ADVISORY_EXTERNAL = "advisory_external"


class SignalTrustTier(Enum):
    ADVISORY = "advisory"
    ATTESTED = "attested"
    VERIFIED = "verified"
    PROTOCOL = "protocol"


def _external_signal_source_kind_code(value: SignalSourceKind) -> int:
    if not isinstance(value, SignalSourceKind):
        raise TypeError("value must be a SignalSourceKind")
    if value is SignalSourceKind.ADVISORY_EXTERNAL:
        return ADVISORY_EXTERNAL_SOURCE_CODE
    if value is SignalSourceKind.ATTESTED_EXTERNAL:
        return ATTESTED_EXTERNAL_SOURCE_CODE
    return 0


def _external_signal_trust_tier_code(value: SignalTrustTier) -> int:
    if not isinstance(value, SignalTrustTier):
        raise TypeError("value must be a SignalTrustTier")
    if value is SignalTrustTier.ADVISORY:
        return ADVISORY_TRUST_TIER_CODE
    if value is SignalTrustTier.ATTESTED:
        return ATTESTED_TRUST_TIER_CODE
    if value is SignalTrustTier.VERIFIED:
        return VERIFIED_TRUST_TIER_CODE
    return 0xFF


@dataclass(frozen=True)
class ExternalSignalObservation:
    signal_id: str
    source_id: str
    source_kind: SignalSourceKind
    trust_tier: SignalTrustTier
    freshness_ok: bool
    auth_ok: bool
    advisory_only: bool = True
    tags: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "signal_id", _require_safe_token("signal_id", self.signal_id))
        object.__setattr__(self, "source_id", _require_safe_token("source_id", self.source_id))
        if not isinstance(self.source_kind, SignalSourceKind):
            raise TypeError("source_kind must be a SignalSourceKind")
        if not isinstance(self.trust_tier, SignalTrustTier):
            raise TypeError("trust_tier must be a SignalTrustTier")
        if not isinstance(self.freshness_ok, bool):
            raise TypeError("freshness_ok must be a bool")
        if not isinstance(self.auth_ok, bool):
            raise TypeError("auth_ok must be a bool")
        if not isinstance(self.advisory_only, bool):
            raise TypeError("advisory_only must be a bool")
        normalized_tags: list[str] = []
        seen_tags: set[str] = set()
        for raw_tag in self.tags:
            tag = _require_safe_token("tags", raw_tag)
            if tag in seen_tags:
                continue
            seen_tags.add(tag)
            normalized_tags.append(tag)
        object.__setattr__(self, "tags", tuple(normalized_tags))
        contract = check_strategy_external_signal_contract(
            source_kind_code=_external_signal_source_kind_code(self.source_kind),
            trust_tier_code=_external_signal_trust_tier_code(self.trust_tier),
            freshness_ok=self.freshness_ok,
            auth_ok=self.auth_ok,
            advisory_only=self.advisory_only,
        )
        if not contract.ok:
            raise ValueError(f"external signal contract rejected: {contract.error}")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": EXTERNAL_SIGNAL_SCHEMA,
            "signal_id": self.signal_id,
            "source_id": self.source_id,
            "source_kind": self.source_kind.value,
            "trust_tier": self.trust_tier.value,
            "freshness_ok": bool(self.freshness_ok),
            "auth_ok": bool(self.auth_ok),
            "advisory_only": bool(self.advisory_only),
            "tags": list(self.tags),
        }


def external_signal_observation_from_dict(data: Mapping[str, Any]) -> ExternalSignalObservation:
    if not isinstance(data, Mapping):
        raise TypeError("external signal entry must be an object")
    signal_id_raw = data.get("signal_id")
    source_id_raw = data.get("source_id")
    source_kind_raw = data.get("source_kind")
    trust_tier_raw = data.get("trust_tier")
    if not isinstance(signal_id_raw, str):
        raise TypeError("external signal signal_id must be a string")
    if not isinstance(source_id_raw, str):
        raise TypeError("external signal source_id must be a string")
    if not isinstance(source_kind_raw, str):
        raise TypeError("external signal source_kind must be a string")
    if not isinstance(trust_tier_raw, str):
        raise TypeError("external signal trust_tier must be a string")
    tags_raw = data.get("tags", ())
    if not isinstance(tags_raw, (list, tuple)):
        raise ValueError("external signal tags must be a list")
    return ExternalSignalObservation(
        signal_id=signal_id_raw,
        source_id=source_id_raw,
        source_kind=SignalSourceKind(source_kind_raw),
        trust_tier=SignalTrustTier(trust_tier_raw),
        freshness_ok=data.get("freshness_ok", False),
        auth_ok=data.get("auth_ok", False),
        advisory_only=data.get("advisory_only", True),
        tags=tuple(tags_raw),
    )


def external_signal_observations_from_object(data: object) -> tuple[ExternalSignalObservation, ...]:
    if data is None:
        return ()
    if isinstance(data, Mapping):
        if "external_signals" in data:
            data = data["external_signals"]
        else:
            data = [data]
    if not isinstance(data, list):
        raise ValueError("external signals file must be a list or an object with external_signals")
    out: list[ExternalSignalObservation] = []
    for row in data:
        out.append(external_signal_observation_from_dict(row))
    return tuple(out)


def _require_safe_token(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    if not _SAFE_TOKEN_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


@dataclass(frozen=True)
class QuoteReceiptSignalPacket:
    current_epoch: int
    quote_epoch: int
    asset_in: str
    asset_out: str
    amount_in: int
    amount_out: int
    receipt_hash: str
    source_id: str = "route_quote_receipt"
    source_kind: SignalSourceKind = SignalSourceKind.ROUTE_QUOTE_RECEIPT
    trust_tier: SignalTrustTier = SignalTrustTier.VERIFIED
    quote_receipt_present: bool = True
    quote_receipt_verified: bool = True
    quote_epoch_present: bool = True
    source_available: bool = True
    auth_ok: bool = True
    binding_ok: bool = True
    verify_error: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "current_epoch", _require_u32("current_epoch", self.current_epoch))
        object.__setattr__(self, "quote_epoch", _require_u32("quote_epoch", self.quote_epoch))
        object.__setattr__(self, "amount_in", _require_u32("amount_in", self.amount_in, minimum=1))
        object.__setattr__(self, "amount_out", _require_u32("amount_out", self.amount_out, minimum=1))
        object.__setattr__(self, "asset_in", _require_safe_token("asset_in", self.asset_in))
        object.__setattr__(self, "asset_out", _require_safe_token("asset_out", self.asset_out))
        object.__setattr__(self, "receipt_hash", _require_safe_token("receipt_hash", self.receipt_hash))
        object.__setattr__(self, "source_id", _require_safe_token("source_id", self.source_id))
        if self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must differ")
        if not isinstance(self.source_kind, SignalSourceKind):
            raise TypeError("source_kind must be a SignalSourceKind")
        if not isinstance(self.trust_tier, SignalTrustTier):
            raise TypeError("trust_tier must be a SignalTrustTier")
        for field_name in (
            "quote_receipt_present",
            "quote_receipt_verified",
            "quote_epoch_present",
            "source_available",
            "auth_ok",
            "binding_ok",
        ):
            if not isinstance(getattr(self, field_name), bool):
                raise TypeError(f"{field_name} must be a bool")
        if self.verify_error is not None and not isinstance(self.verify_error, str):
            raise TypeError("verify_error must be a string or None")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": SIGNAL_PACKET_SCHEMA,
            "current_epoch": int(self.current_epoch),
            "quote_epoch": int(self.quote_epoch),
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
            "amount_in": int(self.amount_in),
            "amount_out": int(self.amount_out),
            "receipt_hash": self.receipt_hash,
            "source_id": self.source_id,
            "source_kind": self.source_kind.value,
            "trust_tier": self.trust_tier.value,
            "quote_receipt_present": bool(self.quote_receipt_present),
            "quote_receipt_verified": bool(self.quote_receipt_verified),
            "quote_epoch_present": bool(self.quote_epoch_present),
            "source_available": bool(self.source_available),
            "auth_ok": bool(self.auth_ok),
            "binding_ok": bool(self.binding_ok),
            "verify_error": self.verify_error,
        }


@dataclass(frozen=True)
class AutoTraderWalletCapability:
    session_id: str
    owner_pubkey: str
    chain_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    notional_remaining: int
    allowed_assets: tuple[str, ...]
    allowed_actions: tuple[StrategyAction, ...]
    enabled: bool = True

    def __post_init__(self) -> None:
        object.__setattr__(self, "session_id", _require_safe_token("session_id", self.session_id))
        object.__setattr__(self, "owner_pubkey", _require_safe_token("owner_pubkey", self.owner_pubkey))
        object.__setattr__(self, "chain_id", _require_safe_token("chain_id", self.chain_id))
        valid_from_epoch = _require_u32("valid_from_epoch", self.valid_from_epoch)
        valid_until_epoch = _require_u32("valid_until_epoch", self.valid_until_epoch)
        notional_remaining = _require_u32("notional_remaining", self.notional_remaining)
        if valid_from_epoch > valid_until_epoch:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        object.__setattr__(self, "valid_from_epoch", valid_from_epoch)
        object.__setattr__(self, "valid_until_epoch", valid_until_epoch)
        object.__setattr__(self, "notional_remaining", notional_remaining)
        if not isinstance(self.enabled, bool):
            raise TypeError("enabled must be a bool")
        normalized_assets: list[str] = []
        seen_assets: set[str] = set()
        for raw in self.allowed_assets:
            asset = _require_safe_token("allowed_assets", raw)
            if asset in seen_assets:
                continue
            seen_assets.add(asset)
            normalized_assets.append(asset)
        if not normalized_assets:
            raise ValueError("allowed_assets must be non-empty")
        object.__setattr__(self, "allowed_assets", tuple(normalized_assets))
        normalized_actions: list[StrategyAction] = []
        seen_actions: set[StrategyAction] = set()
        for raw_action in self.allowed_actions:
            if not isinstance(raw_action, StrategyAction):
                raise TypeError("allowed_actions must contain StrategyAction members")
            if raw_action in seen_actions:
                continue
            seen_actions.add(raw_action)
            normalized_actions.append(raw_action)
        if not normalized_actions:
            raise ValueError("allowed_actions must be non-empty")
        object.__setattr__(self, "allowed_actions", tuple(normalized_actions))

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": WALLET_CAPABILITY_SCHEMA,
            "session_id": self.session_id,
            "owner_pubkey": self.owner_pubkey,
            "chain_id": self.chain_id,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
            "notional_remaining": int(self.notional_remaining),
            "allowed_assets": list(self.allowed_assets),
            "allowed_actions": [action.value for action in self.allowed_actions],
            "enabled": bool(self.enabled),
        }


@dataclass(frozen=True)
class AutoTraderSessionState:
    session_id: str
    owner_pubkey: str
    chain_id: str
    enabled: bool = True
    revoked_at_epoch: int | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "session_id", _require_safe_token("session_id", self.session_id))
        object.__setattr__(self, "owner_pubkey", _require_safe_token("owner_pubkey", self.owner_pubkey))
        object.__setattr__(self, "chain_id", _require_safe_token("chain_id", self.chain_id))
        if not isinstance(self.enabled, bool):
            raise TypeError("enabled must be a bool")
        if self.revoked_at_epoch is not None:
            object.__setattr__(
                self,
                "revoked_at_epoch",
                _require_u32("revoked_at_epoch", self.revoked_at_epoch),
            )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "zenodex/autotrader-session-state/v1",
            "session_id": self.session_id,
            "owner_pubkey": self.owner_pubkey,
            "chain_id": self.chain_id,
            "enabled": bool(self.enabled),
            "revoked_at_epoch": self.revoked_at_epoch,
        }


@dataclass(frozen=True)
class AutoTraderObservationPacket:
    current_epoch: int
    primary_signal: QuoteReceiptSignalPacket
    external_signals: tuple[ExternalSignalObservation, ...] = ()
    wallet_capability: AutoTraderWalletCapability | None = None
    signal_source_registry: ExternalSignalSourceRegistry | None = None
    tau_enabled: bool = False

    def __post_init__(self) -> None:
        object.__setattr__(self, "current_epoch", _require_u32("current_epoch", self.current_epoch))
        if not isinstance(self.primary_signal, QuoteReceiptSignalPacket):
            raise TypeError("primary_signal must be a QuoteReceiptSignalPacket")
        if self.primary_signal.current_epoch != self.current_epoch:
            raise ValueError("primary_signal.current_epoch must equal current_epoch")
        normalized_signals: list[ExternalSignalObservation] = []
        seen_signal_ids: set[str] = set()
        for signal in self.external_signals:
            if not isinstance(signal, ExternalSignalObservation):
                raise TypeError("external_signals must contain ExternalSignalObservation items")
            if signal.signal_id in seen_signal_ids:
                continue
            seen_signal_ids.add(signal.signal_id)
            normalized_signals.append(signal)
        object.__setattr__(self, "external_signals", tuple(normalized_signals))
        if self.wallet_capability is not None and not isinstance(
            self.wallet_capability,
            AutoTraderWalletCapability,
        ):
            raise TypeError("wallet_capability must be an AutoTraderWalletCapability or None")
        if self.signal_source_registry is not None:
            from .autotrader_signal_registry import ExternalSignalSourceRegistry

            if not isinstance(self.signal_source_registry, ExternalSignalSourceRegistry):
                raise TypeError(
                    "signal_source_registry must be an ExternalSignalSourceRegistry or None"
                )
            for signal in self.external_signals:
                binding = self.signal_source_registry.validate(signal)
                if not binding.ok:
                    raise ValueError(
                        "signal source registry rejected "
                        f"{signal.signal_id}: {binding.error}"
                    )
        elif any(
            signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL
            and signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
            and not signal.advisory_only
            for signal in self.external_signals
        ):
            raise ValueError("trusted external signals require a signal source registry")
        if not isinstance(self.tau_enabled, bool):
            raise TypeError("tau_enabled must be a bool")
        from ..kernels.python.strategy_observation_packet_contract_v1_adapter import (
            check_strategy_observation_packet_contract,
        )

        contract = check_strategy_observation_packet_contract(packet=self)
        if not contract.ok:
            raise ValueError(f"observation packet contract rejected: {contract.error}")

    def advisory_external_count(self) -> int:
        return sum(
            1
            for signal in self.external_signals
            if signal.source_kind is SignalSourceKind.ADVISORY_EXTERNAL
            and signal.trust_tier is SignalTrustTier.ADVISORY
            and signal.advisory_only
        )

    def trusted_external_count(self) -> int:
        return sum(
            1
            for signal in self.external_signals
            if signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL
            and signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
            and signal.auth_ok
            and signal.freshness_ok
            and not signal.advisory_only
        )

    def trusted_primary(self) -> bool:
        signal = self.primary_signal
        if signal.source_kind is SignalSourceKind.ROUTE_QUOTE_RECEIPT:
            return signal.trust_tier in (SignalTrustTier.VERIFIED, SignalTrustTier.PROTOCOL)
        if signal.source_kind is SignalSourceKind.LOCAL_PROTOCOL_STATE:
            return signal.trust_tier is SignalTrustTier.PROTOCOL
        if signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL:
            return signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
        return False

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": OBSERVATION_PACKET_SCHEMA,
            "current_epoch": int(self.current_epoch),
            "primary_signal": self.primary_signal.to_dict(),
            "external_signals": [signal.to_dict() for signal in self.external_signals],
            "wallet_capability": (
                None if self.wallet_capability is None else self.wallet_capability.to_dict()
            ),
            "signal_source_registry_present": bool(self.signal_source_registry is not None),
            "registered_external_count": (
                len(self.external_signals) if self.signal_source_registry is not None else 0
            ),
            "external_signal_count": len(self.external_signals),
            "advisory_external_count": self.advisory_external_count(),
            "trusted_external_count": self.trusted_external_count(),
            "trusted_primary": self.trusted_primary(),
            "observation_packet_ok": True,
            "tau_enabled": bool(self.tau_enabled),
        }


def build_quote_receipt_signal_packet(
    *,
    receipt: Mapping[str, object],
    pools_by_id: Mapping[str, PoolState],
    current_epoch: int,
    source_id: str = "route_quote_receipt",
    source_kind: SignalSourceKind = SignalSourceKind.ROUTE_QUOTE_RECEIPT,
    trust_tier: SignalTrustTier = SignalTrustTier.VERIFIED,
) -> QuoteReceiptSignalPacket:
    if not isinstance(receipt, Mapping):
        raise TypeError("receipt must be a mapping")
    if not isinstance(pools_by_id, Mapping):
        raise TypeError("pools_by_id must be a mapping")
    current_epoch = _require_u32("current_epoch", current_epoch)
    source_id = _require_safe_token("source_id", source_id)

    body_raw = receipt.get("body")
    if not isinstance(body_raw, Mapping):
        raise ValueError("missing receipt.body")

    asset_in = _require_safe_token("receipt.body.asset_in", body_raw.get("asset_in"))
    asset_out = _require_safe_token("receipt.body.asset_out", body_raw.get("asset_out"))
    amount_in = _require_u32("receipt.body.amount_in", body_raw.get("amount_in"), minimum=1)
    amount_out = _require_u32("receipt.body.amount_out", body_raw.get("amount_out"), minimum=1)
    receipt_hash = _require_safe_token("receipt.receipt_hash", receipt.get("receipt_hash"))
    quote_epoch_present = "quote_epoch" in body_raw
    quote_epoch = 0
    if quote_epoch_present:
        quote_epoch = _require_u32("receipt.body.quote_epoch", body_raw.get("quote_epoch"))

    verify_ok, verify_error = verify_route_quote_receipt(dict(receipt), pools_by_id=dict(pools_by_id))
    return QuoteReceiptSignalPacket(
        current_epoch=current_epoch,
        quote_epoch=quote_epoch,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        amount_out=amount_out,
        receipt_hash=receipt_hash,
        source_id=source_id,
        source_kind=source_kind,
        trust_tier=trust_tier,
        quote_receipt_present=True,
        quote_receipt_verified=bool(verify_ok),
        quote_epoch_present=bool(quote_epoch_present),
        source_available=True,
        auth_ok=bool(verify_ok),
        binding_ok=bool(verify_ok),
        verify_error=None if verify_ok else str(verify_error),
    )


def build_wallet_capability_from_strategy(
    *,
    strategy: StrategyIR,
    chain_id: str,
    lifetime_spent: int = 0,
    session_id: str | None = None,
) -> AutoTraderWalletCapability:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    lifetime_spent = _require_u32("lifetime_spent", lifetime_spent)
    remaining = strategy.notional_caps.lifetime_max - lifetime_spent
    if remaining < 0:
        remaining = 0
    return AutoTraderWalletCapability(
        session_id=session_id or f"{strategy.strategy_id}.session",
        owner_pubkey=strategy.owner_pubkey,
        chain_id=chain_id,
        valid_from_epoch=strategy.strategy_window.valid_from_epoch,
        valid_until_epoch=strategy.strategy_window.valid_until_epoch,
        notional_remaining=remaining,
        allowed_assets=tuple(strategy.asset_universe),
        allowed_actions=tuple(strategy.allowed_actions),
        enabled=True,
    )


def build_session_state_from_capability(
    *,
    capability: AutoTraderWalletCapability,
    revoked_at_epoch: int | None = None,
    enabled: bool = True,
) -> AutoTraderSessionState:
    if not isinstance(capability, AutoTraderWalletCapability):
        raise TypeError("capability must be an AutoTraderWalletCapability")
    return AutoTraderSessionState(
        session_id=capability.session_id,
        owner_pubkey=capability.owner_pubkey,
        chain_id=capability.chain_id,
        enabled=enabled,
        revoked_at_epoch=revoked_at_epoch,
    )


def build_autotrader_observation_packet(
    *,
    primary_signal: QuoteReceiptSignalPacket,
    wallet_capability: AutoTraderWalletCapability | None = None,
    external_signals: tuple[ExternalSignalObservation, ...] = (),
    signal_source_registry: ExternalSignalSourceRegistry | None = None,
    tau_enabled: bool = False,
) -> AutoTraderObservationPacket:
    return AutoTraderObservationPacket(
        current_epoch=primary_signal.current_epoch,
        primary_signal=primary_signal,
        external_signals=tuple(external_signals),
        wallet_capability=wallet_capability,
        signal_source_registry=signal_source_registry,
        tau_enabled=tau_enabled,
    )
