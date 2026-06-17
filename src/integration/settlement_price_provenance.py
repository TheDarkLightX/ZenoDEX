from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from .zusd_oracle_contracts import verify_zusd_cross_module_oracle_sync_contract_payload

SETTLEMENT_SPOT_PRICE_PACKET_SCHEMA = "zenodex/settlement-spot-price-packet/v1"
_PRICE_PACKET_DOMAIN_ERRORS = (TypeError, ValueError, ArithmeticError)
_PRICE_PACKET_VERIFY_CACHE: dict[tuple[object, ...], tuple[bool, str | None]] = {}


@dataclass(frozen=True)
class SettlementSpotPriceEntry:
    asset: str
    price: int
    observed_epoch: int
    age_epochs: int
    source_id: str

    def __post_init__(self) -> None:
        if not isinstance(self.asset, str) or not self.asset:
            raise ValueError("asset must be a non-empty string")
        if not isinstance(self.price, int) or isinstance(self.price, bool) or self.price < 0:
            raise ValueError("price must be a non-negative int")
        if not isinstance(self.observed_epoch, int) or isinstance(self.observed_epoch, bool) or self.observed_epoch < 0:
            raise ValueError("observed_epoch must be a non-negative int")
        if not isinstance(self.age_epochs, int) or isinstance(self.age_epochs, bool) or self.age_epochs < 0:
            raise ValueError("age_epochs must be a non-negative int")
        if not isinstance(self.source_id, str) or not self.source_id:
            raise ValueError("source_id must be a non-empty string")

    def to_dict(self) -> dict[str, Any]:
        return {
            "asset": self.asset,
            "price": int(self.price),
            "observed_epoch": int(self.observed_epoch),
            "age_epochs": int(self.age_epochs),
            "source_id": self.source_id,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSpotPriceEntry":
        if not isinstance(payload, Mapping):
            raise ValueError("price entry must be an object")
        return cls(
            asset=str(payload.get("asset", "")),
            price=_require_non_negative_int(payload.get("price", -1), name="price"),
            observed_epoch=_require_non_negative_int(payload.get("observed_epoch", -1), name="observed_epoch"),
            age_epochs=_require_non_negative_int(payload.get("age_epochs", -1), name="age_epochs"),
            source_id=str(payload.get("source_id", "")),
        )


@dataclass(frozen=True)
class SettlementSpotPricePacket:
    entries: tuple[SettlementSpotPriceEntry, ...]
    now_epoch: int
    max_staleness_epochs: int
    cross_module_sync_required: bool
    cross_module_sync_ok: bool
    price_vector_sha256: str
    provenance_vector_sha256: str
    unique_assets: bool
    all_positive: bool
    all_fresh: bool
    provenance_ok: bool
    cross_module_sync_contract: dict[str, Any] | None = None
    schema: str = SETTLEMENT_SPOT_PRICE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_SPOT_PRICE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not self.entries:
            raise ValueError("entries must be non-empty")
        if not isinstance(self.now_epoch, int) or isinstance(self.now_epoch, bool) or self.now_epoch < 0:
            raise ValueError("now_epoch must be a non-negative int")
        if (
            not isinstance(self.max_staleness_epochs, int)
            or isinstance(self.max_staleness_epochs, bool)
            or self.max_staleness_epochs < 0
        ):
            raise ValueError("max_staleness_epochs must be a non-negative int")
        for name in (
            "cross_module_sync_required",
            "cross_module_sync_ok",
            "unique_assets",
            "all_positive",
            "all_fresh",
            "provenance_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise ValueError(f"{name} must be a bool")
        _require_hex_digest(self.price_vector_sha256, name="price_vector_sha256")
        _require_hex_digest(self.provenance_vector_sha256, name="provenance_vector_sha256")
        if self.cross_module_sync_contract is not None and not isinstance(self.cross_module_sync_contract, dict):
            raise ValueError("cross_module_sync_contract must be an object when present")

    def to_dict(self) -> dict[str, Any]:
        out = {
            "schema": self.schema,
            "entries": [entry.to_dict() for entry in self.entries],
            "now_epoch": int(self.now_epoch),
            "max_staleness_epochs": int(self.max_staleness_epochs),
            "cross_module_sync_required": bool(self.cross_module_sync_required),
            "cross_module_sync_ok": bool(self.cross_module_sync_ok),
            "price_vector_sha256": self.price_vector_sha256,
            "provenance_vector_sha256": self.provenance_vector_sha256,
            "unique_assets": bool(self.unique_assets),
            "all_positive": bool(self.all_positive),
            "all_fresh": bool(self.all_fresh),
            "provenance_ok": bool(self.provenance_ok),
        }
        if self.cross_module_sync_contract is not None:
            out["cross_module_sync_contract"] = dict(self.cross_module_sync_contract)
        return out

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSpotPricePacket":
        if not isinstance(payload, Mapping):
            raise ValueError("packet must be an object")
        raw_entries = payload.get("entries", [])
        if not isinstance(raw_entries, list):
            raise ValueError("packet.entries must be a list")
        cross_module_sync_required = payload.get("cross_module_sync_required", False)
        if not isinstance(cross_module_sync_required, bool):
            raise ValueError("packet.cross_module_sync_required must be a bool")
        cross_module_sync_ok = payload.get("cross_module_sync_ok", False)
        if not isinstance(cross_module_sync_ok, bool):
            raise ValueError("packet.cross_module_sync_ok must be a bool")
        unique_assets = payload.get("unique_assets", False)
        if not isinstance(unique_assets, bool):
            raise ValueError("packet.unique_assets must be a bool")
        all_positive = payload.get("all_positive", False)
        if not isinstance(all_positive, bool):
            raise ValueError("packet.all_positive must be a bool")
        all_fresh = payload.get("all_fresh", False)
        if not isinstance(all_fresh, bool):
            raise ValueError("packet.all_fresh must be a bool")
        provenance_ok = payload.get("provenance_ok", False)
        if not isinstance(provenance_ok, bool):
            raise ValueError("packet.provenance_ok must be a bool")
        sync_contract = payload.get("cross_module_sync_contract")
        if sync_contract is not None and not isinstance(sync_contract, dict):
            raise ValueError("packet.cross_module_sync_contract must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            entries=tuple(SettlementSpotPriceEntry.from_dict(entry) for entry in raw_entries),
            now_epoch=_require_non_negative_int(payload.get("now_epoch", -1), name="now_epoch"),
            max_staleness_epochs=_require_non_negative_int(
                payload.get("max_staleness_epochs", -1),
                name="max_staleness_epochs",
            ),
            cross_module_sync_required=cross_module_sync_required,
            cross_module_sync_ok=cross_module_sync_ok,
            price_vector_sha256=str(payload.get("price_vector_sha256", "")),
            provenance_vector_sha256=str(payload.get("provenance_vector_sha256", "")),
            unique_assets=unique_assets,
            all_positive=all_positive,
            all_fresh=all_fresh,
            provenance_ok=provenance_ok,
            cross_module_sync_contract=sync_contract,
        )


def build_settlement_spot_price_packet(
    *,
    entries: Sequence[SettlementSpotPriceEntry],
    now_epoch: int,
    max_staleness_epochs: int,
    cross_module_sync_required: bool = False,
    cross_module_sync_contract: Mapping[str, Any] | None = None,
) -> SettlementSpotPricePacket:
    if not isinstance(now_epoch, int) or isinstance(now_epoch, bool) or now_epoch < 0:
        raise ValueError("now_epoch must be a non-negative int")
    if not isinstance(max_staleness_epochs, int) or isinstance(max_staleness_epochs, bool) or max_staleness_epochs < 0:
        raise ValueError("max_staleness_epochs must be a non-negative int")
    if not isinstance(cross_module_sync_required, bool):
        raise ValueError("cross_module_sync_required must be a bool")
    canonical_entries = tuple(
        sorted(
            (
                SettlementSpotPriceEntry(
                    asset=entry.asset,
                    price=entry.price,
                    observed_epoch=entry.observed_epoch,
                    age_epochs=abs(int(now_epoch) - int(entry.observed_epoch)),
                    source_id=entry.source_id,
                )
                for entry in entries
            ),
            key=lambda e: e.asset,
        )
    )
    if not canonical_entries:
        raise ValueError("entries must be non-empty")

    unique_assets = len({entry.asset for entry in canonical_entries}) == len(canonical_entries)
    all_positive = all(entry.price > 0 for entry in canonical_entries)
    all_fresh = all(abs(int(now_epoch) - int(entry.observed_epoch)) <= int(max_staleness_epochs) for entry in canonical_entries)

    sync_contract_payload: dict[str, Any] | None = None
    cross_module_sync_ok = False
    if cross_module_sync_contract is not None:
        sync_contract_payload = _canonical_json_obj(cross_module_sync_contract)
        ok, err = verify_zusd_cross_module_oracle_sync_contract_payload(sync_contract_payload)
        if not ok:
            raise ValueError(f"cross_module_sync_contract invalid: {err}")
        cross_module_sync_ok = _require_bool(
            sync_contract_payload.get("sync_gate_ok"),
            name="cross_module_sync_contract.sync_gate_ok",
        )

    provenance_ok = bool(unique_assets) and bool(all_positive) and bool(all_fresh) and (
        (not bool(cross_module_sync_required))
        or (bool(cross_module_sync_ok) and sync_contract_payload is not None)
    )

    return SettlementSpotPricePacket(
        entries=canonical_entries,
        now_epoch=int(now_epoch),
        max_staleness_epochs=int(max_staleness_epochs),
        cross_module_sync_required=bool(cross_module_sync_required),
        cross_module_sync_ok=bool(cross_module_sync_ok),
        price_vector_sha256=_sha256_json({"entries": [{"asset": entry.asset, "price": entry.price} for entry in canonical_entries]}),
        provenance_vector_sha256=_sha256_json(
            {
                "entries": [entry.to_dict() for entry in canonical_entries],
                "now_epoch": int(now_epoch),
                "max_staleness_epochs": int(max_staleness_epochs),
                "cross_module_sync_required": bool(cross_module_sync_required),
                "cross_module_sync_contract": sync_contract_payload,
            }
        ),
        unique_assets=bool(unique_assets),
        all_positive=bool(all_positive),
        all_fresh=bool(all_fresh),
        provenance_ok=bool(provenance_ok),
        cross_module_sync_contract=sync_contract_payload,
    )


def verify_settlement_spot_price_packet(
    *,
    packet: SettlementSpotPricePacket,
) -> tuple[bool, str | None]:
    if not isinstance(packet, SettlementSpotPricePacket):
        return False, "packet must be a SettlementSpotPricePacket"
    key = _price_packet_verify_cache_key(packet)
    cached = _PRICE_PACKET_VERIFY_CACHE.get(key)
    if cached is not None:
        return cached
    try:
        expected = build_settlement_spot_price_packet(
            entries=packet.entries,
            now_epoch=packet.now_epoch,
            max_staleness_epochs=packet.max_staleness_epochs,
            cross_module_sync_required=packet.cross_module_sync_required,
            cross_module_sync_contract=packet.cross_module_sync_contract,
        )
    except _PRICE_PACKET_DOMAIN_ERRORS as exc:
        result = (False, str(exc))
        _cache_verify_result(_PRICE_PACKET_VERIFY_CACHE, key, result)
        return result
    if packet != expected:
        result = (False, "settlement spot price packet mismatch")
        _cache_verify_result(_PRICE_PACKET_VERIFY_CACHE, key, result)
        return result
    result = (True, None)
    _cache_verify_result(_PRICE_PACKET_VERIFY_CACHE, key, result)
    return result


def verify_settlement_spot_price_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, Mapping):
        return False, "packet payload must be a dict"
    try:
        packet = SettlementSpotPricePacket.from_dict(payload)
    except _PRICE_PACKET_DOMAIN_ERRORS as exc:
        return False, str(exc)
    return verify_settlement_spot_price_packet(packet=packet)


def asset_prices_from_spot_price_packet(packet: SettlementSpotPricePacket) -> dict[str, int]:
    return {entry.asset: int(entry.price) for entry in packet.entries}


def _require_non_negative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be a bool")
    return value


def _canonical_json_obj(payload: Mapping[str, Any]) -> dict[str, Any]:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    return json.loads(encoded)


def _sha256_json(value: object) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def _price_packet_verify_cache_key(packet: SettlementSpotPricePacket) -> tuple[object, ...]:
    sync_key = None if packet.cross_module_sync_contract is None else json.dumps(
        packet.cross_module_sync_contract,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    return (
        tuple(
            (entry.asset, int(entry.price), int(entry.observed_epoch), int(entry.age_epochs), entry.source_id)
            for entry in packet.entries
        ),
        int(packet.now_epoch),
        int(packet.max_staleness_epochs),
        bool(packet.cross_module_sync_required),
        bool(packet.cross_module_sync_ok),
        bool(packet.unique_assets),
        bool(packet.all_positive),
        bool(packet.all_fresh),
        bool(packet.provenance_ok),
        packet.price_vector_sha256,
        packet.provenance_vector_sha256,
        sync_key,
    )


def _cache_verify_result(
    cache: dict[tuple[object, ...], tuple[bool, str | None]],
    key: tuple[object, ...],
    result: tuple[bool, str | None],
) -> None:
    if len(cache) >= 512:
        cache.clear()
    cache[key] = result


def _require_hex_digest(value: str, *, name: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest")
    try:
        int(value, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest") from exc
