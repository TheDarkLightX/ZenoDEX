from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping

_SAFE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")


class ZGEntityKind(Enum):
    USER = "user"
    ACCOUNT = "account"
    WALLET = "wallet"
    ASSET = "asset"
    POOL = "pool"
    PROTOCOL = "protocol"
    POSITION = "position"
    STRATEGY_TEMPLATE = "strategy_template"
    TACTIC = "tactic"
    REGIME = "regime"
    SIGNAL = "signal"
    EVENT = "event"
    SOURCE = "source"
    EVIDENCE = "evidence"
    CONSTRAINT = "constraint"
    RISK_STATE = "risk_state"
    THEME = "theme"
    SECTOR = "sector"
    COUNTERPARTY = "counterparty"
    TAX_LOT = "tax_lot"
    OUTCOME = "outcome"


class ZGFactStatus(Enum):
    OBSERVED = "observed"
    DERIVED = "derived"
    INFERRED = "inferred"
    PROPOSED = "proposed"
    REJECTED = "rejected"
    ACCEPTED = "accepted"


class ZGSourceKind(Enum):
    ONCHAIN = "onchain"
    EXCHANGE = "exchange"
    NEWS = "news"
    RESEARCH = "research"
    USER = "user"
    MODEL = "model"
    SYSTEM = "system"


def _require_safe_token(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    text = value.strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    if not _SAFE_TOKEN_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _require_optional_safe_token(value: object | None, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_safe_token(value, name=name)


def _require_optional_epoch(value: object | None, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_epoch(value, name=name)


def _require_epoch(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0:
        raise ValueError(f"{name} must be >= 0: {out}")
    return out


def _require_confidence_bps(value: object, *, name: str) -> int:
    out = _require_epoch(value, name=name)
    if out > 10_000:
        raise ValueError(f"{name} must be <= 10000: {out}")
    return out


def _normalize_json_value(value: object, *, name: str) -> object:
    try:
        encoded = json.dumps(value, sort_keys=True, separators=(",", ":"))
        return json.loads(encoded)
    except TypeError as exc:
        raise TypeError(f"{name} must be JSON-serializable") from exc


def _normalize_string_tuple(values: tuple[str, ...] | list[str], *, name: str) -> tuple[str, ...]:
    out: list[str] = []
    seen: set[str] = set()
    for idx, raw in enumerate(values):
        value = _require_safe_token(raw, name=f"{name}[{idx}]")
        if value in seen:
            continue
        seen.add(value)
        out.append(value)
    return tuple(out)


@dataclass(frozen=True)
class ZGEntity:
    entity_id: str
    kind: ZGEntityKind
    attrs: Mapping[str, object] = field(default_factory=dict)

    def __post_init__(self) -> None:
        object.__setattr__(self, "entity_id", _require_safe_token(self.entity_id, name="entity_id"))
        if not isinstance(self.kind, ZGEntityKind):
            raise TypeError("kind must be a ZGEntityKind")
        normalized_attrs = _normalize_json_value(dict(self.attrs), name="attrs")
        if not isinstance(normalized_attrs, dict):
            raise TypeError("attrs must normalize to a JSON object")
        object.__setattr__(self, "attrs", normalized_attrs)

    def to_dict(self) -> dict[str, object]:
        return {
            "entity_id": self.entity_id,
            "kind": self.kind.value,
            "attrs": dict(self.attrs),
        }


@dataclass(frozen=True)
class ZGFact:
    fact_id: str
    status: ZGFactStatus
    subject_id: str
    predicate: str
    object_id: str | None = None
    value: object | None = None
    microtheory: str = "OnChainFacts"
    source_id: str = "system.default"
    source_kind: ZGSourceKind = ZGSourceKind.SYSTEM
    observed_at: int | None = None
    effective_at: int | None = None
    expires_at: int | None = None
    confidence_bps: int = 10_000
    extraction_method: str = "manual"
    validator_status: str = "unchecked"
    validation_receipt_ids: tuple[str, ...] = ()
    proposed_by: str | None = None
    accepted_by: str | None = None
    notes: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "fact_id", _require_safe_token(self.fact_id, name="fact_id"))
        if not isinstance(self.status, ZGFactStatus):
            raise TypeError("status must be a ZGFactStatus")
        object.__setattr__(self, "subject_id", _require_safe_token(self.subject_id, name="subject_id"))
        object.__setattr__(self, "predicate", _require_safe_token(self.predicate, name="predicate"))
        object.__setattr__(self, "object_id", _require_optional_safe_token(self.object_id, name="object_id"))
        object.__setattr__(self, "value", _normalize_json_value(self.value, name="value"))
        object.__setattr__(self, "microtheory", _require_safe_token(self.microtheory, name="microtheory"))
        object.__setattr__(self, "source_id", _require_safe_token(self.source_id, name="source_id"))
        if not isinstance(self.source_kind, ZGSourceKind):
            raise TypeError("source_kind must be a ZGSourceKind")
        object.__setattr__(self, "observed_at", _require_optional_epoch(self.observed_at, name="observed_at"))
        object.__setattr__(self, "effective_at", _require_optional_epoch(self.effective_at, name="effective_at"))
        object.__setattr__(self, "expires_at", _require_optional_epoch(self.expires_at, name="expires_at"))
        if self.effective_at is not None and self.observed_at is not None and self.effective_at < self.observed_at:
            raise ValueError("effective_at must be >= observed_at when both are present")
        if self.expires_at is not None and self.effective_at is not None and self.expires_at < self.effective_at:
            raise ValueError("expires_at must be >= effective_at when both are present")
        object.__setattr__(self, "confidence_bps", _require_confidence_bps(self.confidence_bps, name="confidence_bps"))
        object.__setattr__(self, "extraction_method", _require_safe_token(self.extraction_method, name="extraction_method"))
        object.__setattr__(self, "validator_status", _require_safe_token(self.validator_status, name="validator_status"))
        receipt_ids = _normalize_string_tuple(self.validation_receipt_ids, name="validation_receipt_ids")
        object.__setattr__(self, "validation_receipt_ids", receipt_ids)
        object.__setattr__(self, "proposed_by", _require_optional_safe_token(self.proposed_by, name="proposed_by"))
        object.__setattr__(self, "accepted_by", _require_optional_safe_token(self.accepted_by, name="accepted_by"))
        if self.notes is not None and not isinstance(self.notes, str):
            raise TypeError("notes must be a string when present")
        if self.status is ZGFactStatus.ACCEPTED and not receipt_ids:
            raise ValueError("accepted facts require validation_receipt_ids")
        if self.status is ZGFactStatus.ACCEPTED and self.accepted_by is None:
            raise ValueError("accepted facts require accepted_by")
        if self.status is not ZGFactStatus.ACCEPTED and self.accepted_by is not None:
            raise ValueError("accepted_by is only allowed for accepted facts")
        if self.status is ZGFactStatus.PROPOSED and self.validator_status == "validated":
            raise ValueError("proposed facts cannot be validator_status=validated")
        if self.object_id is None and self.value is None:
            raise ValueError("fact must have object_id or value")

    def to_dict(self) -> dict[str, object]:
        return {
            "fact_id": self.fact_id,
            "status": self.status.value,
            "subject_id": self.subject_id,
            "predicate": self.predicate,
            "object_id": self.object_id,
            "value": self.value,
            "microtheory": self.microtheory,
            "source_id": self.source_id,
            "source_kind": self.source_kind.value,
            "observed_at": self.observed_at,
            "effective_at": self.effective_at,
            "expires_at": self.expires_at,
            "confidence_bps": self.confidence_bps,
            "extraction_method": self.extraction_method,
            "validator_status": self.validator_status,
            "validation_receipt_ids": list(self.validation_receipt_ids),
            "proposed_by": self.proposed_by,
            "accepted_by": self.accepted_by,
            "notes": self.notes,
        }


def zg_entity_from_dict(obj: Mapping[str, object]) -> ZGEntity:
    return ZGEntity(
        entity_id=obj["entity_id"],
        kind=ZGEntityKind(str(obj["kind"])),
        attrs=obj.get("attrs", {}),
    )


def zg_fact_from_dict(obj: Mapping[str, object]) -> ZGFact:
    return ZGFact(
        fact_id=obj["fact_id"],
        status=ZGFactStatus(str(obj["status"])),
        subject_id=obj["subject_id"],
        predicate=obj["predicate"],
        object_id=obj.get("object_id"),
        value=obj.get("value"),
        microtheory=str(obj.get("microtheory", "OnChainFacts")),
        source_id=str(obj.get("source_id", "system.default")),
        source_kind=ZGSourceKind(str(obj.get("source_kind", ZGSourceKind.SYSTEM.value))),
        observed_at=obj.get("observed_at"),
        effective_at=obj.get("effective_at"),
        expires_at=obj.get("expires_at"),
        confidence_bps=obj.get("confidence_bps", 10_000),
        extraction_method=str(obj.get("extraction_method", "manual")),
        validator_status=str(obj.get("validator_status", "unchecked")),
        validation_receipt_ids=tuple(obj.get("validation_receipt_ids", ())),
        proposed_by=obj.get("proposed_by"),
        accepted_by=obj.get("accepted_by"),
        notes=obj.get("notes"),
    )
