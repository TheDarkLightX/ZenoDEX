from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping

from ..kernels.python.strategy_external_signal_source_registry_guard_v1_adapter import (
    ADVISORY_TRUST_TIER_CODE,
    ATTESTED_TRUST_TIER_CODE,
    PROTOCOL_TRUST_TIER_CODE,
    VERIFIED_TRUST_TIER_CODE,
    StrategyExternalSignalSourceRegistryGuardResult,
    check_strategy_external_signal_source_registry_guard,
)
from .autotrader_signals import ExternalSignalObservation, SignalSourceKind, SignalTrustTier

_SAFE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")

EXTERNAL_SIGNAL_SOURCE_REGISTRY_SCHEMA = "zenodex/autotrader-external-signal-source-registry/v1"
EXTERNAL_SIGNAL_SOURCE_REGISTRY_ENTRY_SCHEMA = (
    "zenodex/autotrader-external-signal-source-registry-entry/v1"
)


def _require_safe_token(name: str, value: object) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    if not _SAFE_TOKEN_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _source_kind_code(value: SignalSourceKind) -> int:
    if not isinstance(value, SignalSourceKind):
        raise TypeError("value must be a SignalSourceKind")
    mapping = {
        SignalSourceKind.ROUTE_QUOTE_RECEIPT: 1,
        SignalSourceKind.LOCAL_PROTOCOL_STATE: 2,
        SignalSourceKind.ATTESTED_EXTERNAL: 3,
        SignalSourceKind.ADVISORY_EXTERNAL: 4,
    }
    return mapping[value]


def _trust_tier_code(value: SignalTrustTier) -> int:
    if not isinstance(value, SignalTrustTier):
        raise TypeError("value must be a SignalTrustTier")
    mapping = {
        SignalTrustTier.ADVISORY: ADVISORY_TRUST_TIER_CODE,
        SignalTrustTier.ATTESTED: ATTESTED_TRUST_TIER_CODE,
        SignalTrustTier.VERIFIED: VERIFIED_TRUST_TIER_CODE,
        SignalTrustTier.PROTOCOL: PROTOCOL_TRUST_TIER_CODE,
    }
    return mapping[value]


@dataclass(frozen=True)
class ExternalSignalSourceRegistryEntry:
    source_id: str
    source_kind: SignalSourceKind
    allowed_trust_tiers: tuple[SignalTrustTier, ...]
    require_advisory_only: bool = False
    require_auth: bool = False
    require_freshness: bool = False
    enabled: bool = True
    tags: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "source_id", _require_safe_token("source_id", self.source_id))
        if not isinstance(self.source_kind, SignalSourceKind):
            raise TypeError("source_kind must be a SignalSourceKind")
        if not isinstance(self.require_advisory_only, bool):
            raise TypeError("require_advisory_only must be a bool")
        if not isinstance(self.require_auth, bool):
            raise TypeError("require_auth must be a bool")
        if not isinstance(self.require_freshness, bool):
            raise TypeError("require_freshness must be a bool")
        if not isinstance(self.enabled, bool):
            raise TypeError("enabled must be a bool")
        normalized_tiers: list[SignalTrustTier] = []
        seen_tiers: set[SignalTrustTier] = set()
        for raw in self.allowed_trust_tiers:
            if not isinstance(raw, SignalTrustTier):
                raise TypeError("allowed_trust_tiers must contain SignalTrustTier members")
            if raw in seen_tiers:
                continue
            seen_tiers.add(raw)
            normalized_tiers.append(raw)
        if self.enabled and not normalized_tiers:
            raise ValueError("allowed_trust_tiers must be non-empty when enabled")
        object.__setattr__(self, "allowed_trust_tiers", tuple(normalized_tiers))
        normalized_tags: list[str] = []
        seen_tags: set[str] = set()
        for raw_tag in self.tags:
            tag = _require_safe_token("tags", raw_tag)
            if tag in seen_tags:
                continue
            seen_tags.add(tag)
            normalized_tags.append(tag)
        object.__setattr__(self, "tags", tuple(normalized_tags))

    @property
    def allow_advisory(self) -> bool:
        return SignalTrustTier.ADVISORY in self.allowed_trust_tiers

    @property
    def allow_attested(self) -> bool:
        return SignalTrustTier.ATTESTED in self.allowed_trust_tiers

    @property
    def allow_verified(self) -> bool:
        return SignalTrustTier.VERIFIED in self.allowed_trust_tiers

    @property
    def allow_protocol(self) -> bool:
        return SignalTrustTier.PROTOCOL in self.allowed_trust_tiers

    def validate(
        self,
        signal: ExternalSignalObservation,
    ) -> StrategyExternalSignalSourceRegistryGuardResult:
        if not isinstance(signal, ExternalSignalObservation):
            raise TypeError("signal must be an ExternalSignalObservation")
        return check_strategy_external_signal_source_registry_guard(
            registry_entry_present=True,
            registry_entry_enabled=self.enabled,
            observed_source_kind_code=_source_kind_code(signal.source_kind),
            observed_trust_tier_code=_trust_tier_code(signal.trust_tier),
            advisory_only=bool(signal.advisory_only),
            auth_ok=bool(signal.auth_ok),
            freshness_ok=bool(signal.freshness_ok),
            registered_source_kind_code=_source_kind_code(self.source_kind),
            allow_advisory=self.allow_advisory,
            allow_attested=self.allow_attested,
            allow_verified=self.allow_verified,
            allow_protocol=self.allow_protocol,
            require_advisory_only=self.require_advisory_only,
            require_auth=self.require_auth,
            require_freshness=self.require_freshness,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": EXTERNAL_SIGNAL_SOURCE_REGISTRY_ENTRY_SCHEMA,
            "source_id": self.source_id,
            "source_kind": self.source_kind.value,
            "allowed_trust_tiers": [tier.value for tier in self.allowed_trust_tiers],
            "require_advisory_only": bool(self.require_advisory_only),
            "require_auth": bool(self.require_auth),
            "require_freshness": bool(self.require_freshness),
            "enabled": bool(self.enabled),
            "tags": list(self.tags),
        }


@dataclass(frozen=True)
class ExternalSignalSourceRegistry:
    entries: tuple[ExternalSignalSourceRegistryEntry, ...]

    def __post_init__(self) -> None:
        normalized_entries: list[ExternalSignalSourceRegistryEntry] = []
        seen_source_ids: set[str] = set()
        for entry in self.entries:
            if not isinstance(entry, ExternalSignalSourceRegistryEntry):
                raise TypeError("entries must contain ExternalSignalSourceRegistryEntry items")
            if entry.source_id in seen_source_ids:
                raise ValueError(f"duplicate source registry entry: {entry.source_id}")
            seen_source_ids.add(entry.source_id)
            normalized_entries.append(entry)
        object.__setattr__(self, "entries", tuple(normalized_entries))

    def get(self, source_id: str) -> ExternalSignalSourceRegistryEntry | None:
        source_id = _require_safe_token("source_id", source_id)
        for entry in self.entries:
            if entry.source_id == source_id:
                return entry
        return None

    def validate(self, signal: ExternalSignalObservation) -> StrategyExternalSignalSourceRegistryGuardResult:
        if not isinstance(signal, ExternalSignalObservation):
            raise TypeError("signal must be an ExternalSignalObservation")
        entry = self.get(signal.source_id)
        if entry is None:
            return check_strategy_external_signal_source_registry_guard(
                registry_entry_present=False,
                registry_entry_enabled=False,
                observed_source_kind_code=_source_kind_code(signal.source_kind),
                observed_trust_tier_code=_trust_tier_code(signal.trust_tier),
                advisory_only=bool(signal.advisory_only),
                auth_ok=bool(signal.auth_ok),
                freshness_ok=bool(signal.freshness_ok),
                registered_source_kind_code=0,
                allow_advisory=False,
                allow_attested=False,
                allow_verified=False,
                allow_protocol=False,
                require_advisory_only=False,
                require_auth=False,
                require_freshness=False,
            )
        return entry.validate(signal)

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": EXTERNAL_SIGNAL_SOURCE_REGISTRY_SCHEMA,
            "entry_count": len(self.entries),
            "entries": [entry.to_dict() for entry in self.entries],
        }


def external_signal_source_registry_entry_from_dict(
    data: Mapping[str, Any],
) -> ExternalSignalSourceRegistryEntry:
    if not isinstance(data, Mapping):
        raise TypeError("external signal source registry entry must be an object")
    source_id_raw = data.get("source_id")
    source_kind_raw = data.get("source_kind")
    trust_tiers_raw = data.get("allowed_trust_tiers")
    if not isinstance(source_id_raw, str):
        raise TypeError("external signal source registry entry source_id must be a string")
    if not isinstance(source_kind_raw, str):
        raise TypeError("external signal source registry entry source_kind must be a string")
    if not isinstance(trust_tiers_raw, (list, tuple)):
        raise TypeError("external signal source registry entry allowed_trust_tiers must be a list")
    tags_raw = data.get("tags", ())
    if not isinstance(tags_raw, (list, tuple)):
        raise TypeError("external signal source registry entry tags must be a list")
    return ExternalSignalSourceRegistryEntry(
        source_id=source_id_raw,
        source_kind=SignalSourceKind(source_kind_raw),
        allowed_trust_tiers=tuple(SignalTrustTier(str(raw)) for raw in trust_tiers_raw),
        require_advisory_only=_require_bool(
            "external signal source registry entry require_advisory_only",
            data.get("require_advisory_only", False),
        ),
        require_auth=_require_bool(
            "external signal source registry entry require_auth",
            data.get("require_auth", False),
        ),
        require_freshness=_require_bool(
            "external signal source registry entry require_freshness",
            data.get("require_freshness", False),
        ),
        enabled=_require_bool(
            "external signal source registry entry enabled",
            data.get("enabled", True),
        ),
        tags=tuple(str(raw) for raw in tags_raw),
    )


def external_signal_source_registry_from_object(data: object) -> ExternalSignalSourceRegistry:
    if isinstance(data, Mapping):
        if "entries" in data:
            data = data["entries"]
        else:
            data = [data]
    if not isinstance(data, list):
        raise ValueError(
            "external signal source registry file must be a list or an object with entries"
        )
    entries = [external_signal_source_registry_entry_from_dict(row) for row in data]
    return ExternalSignalSourceRegistry(entries=tuple(entries))


__all__ = [
    "EXTERNAL_SIGNAL_SOURCE_REGISTRY_ENTRY_SCHEMA",
    "EXTERNAL_SIGNAL_SOURCE_REGISTRY_SCHEMA",
    "ExternalSignalSourceRegistry",
    "ExternalSignalSourceRegistryEntry",
    "external_signal_source_registry_entry_from_dict",
    "external_signal_source_registry_from_object",
]
