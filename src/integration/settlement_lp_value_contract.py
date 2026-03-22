from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Mapping

from src.core.settlement import Settlement
from src.core.settlement_normal_form import normalize_settlement_op_for_commitment

from .operations import create_settlement_operation
from .settlement_price_provenance import (
    SettlementSpotPricePacket,
    asset_prices_from_spot_price_packet,
    verify_settlement_spot_price_packet,
)
from .settlement_value_contract import AssetNetValueEntry, AssetPriceEntry

if TYPE_CHECKING:
    from .settlement_attestation_policy import SettlementAttestationPolicy
    from .settlement_price_attestation import SettlementSpotPriceAttestation


SETTLEMENT_LP_VALUE_CONTRACT_SCHEMA = "zenodex/settlement-lp-value-contract/v1"


@dataclass(frozen=True)
class LPUnitValueEntry:
    pool_id: str
    unit_value: int

    def __post_init__(self) -> None:
        if not isinstance(self.pool_id, str) or not self.pool_id:
            raise ValueError("pool_id must be a non-empty string")
        if not isinstance(self.unit_value, int) or isinstance(self.unit_value, bool) or self.unit_value < 0:
            raise ValueError("unit_value must be a non-negative int")

    def to_dict(self) -> dict[str, Any]:
        return {
            "pool_id": self.pool_id,
            "unit_value": int(self.unit_value),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "LPUnitValueEntry":
        if not isinstance(payload, Mapping):
            raise ValueError("lp unit value entry must be an object")
        return cls(
            pool_id=str(payload.get("pool_id", "")),
            unit_value=int(payload.get("unit_value", -1)),
        )


@dataclass(frozen=True)
class LPNetValueEntry:
    pool_id: str
    net_delta: int
    unit_value: int
    user_value: int
    protocol_liability_value: int

    def __post_init__(self) -> None:
        if not isinstance(self.pool_id, str) or not self.pool_id:
            raise ValueError("pool_id must be a non-empty string")
        for name in ("net_delta", "user_value", "protocol_liability_value"):
            if not isinstance(getattr(self, name), int) or isinstance(getattr(self, name), bool):
                raise ValueError(f"{name} must be an int")
        if not isinstance(self.unit_value, int) or isinstance(self.unit_value, bool) or self.unit_value < 0:
            raise ValueError("unit_value must be a non-negative int")

    def to_dict(self) -> dict[str, Any]:
        return {
            "pool_id": self.pool_id,
            "net_delta": int(self.net_delta),
            "unit_value": int(self.unit_value),
            "user_value": int(self.user_value),
            "protocol_liability_value": int(self.protocol_liability_value),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "LPNetValueEntry":
        if not isinstance(payload, Mapping):
            raise ValueError("lp net entry must be an object")
        return cls(
            pool_id=str(payload.get("pool_id", "")),
            net_delta=int(payload.get("net_delta", 0)),
            unit_value=int(payload.get("unit_value", -1)),
            user_value=int(payload.get("user_value", 0)),
            protocol_liability_value=int(payload.get("protocol_liability_value", 0)),
        )


@dataclass(frozen=True)
class SettlementLPValueContract:
    settlement_commitment_sha256: str
    delta_commitment_sha256: str
    price_vector_sha256: str
    lp_value_vector_sha256: str
    asset_prices: tuple[AssetPriceEntry, ...]
    lp_unit_values: tuple[LPUnitValueEntry, ...]
    asset_nets: tuple[AssetNetValueEntry, ...]
    lp_nets: tuple[LPNetValueEntry, ...]
    balance_value_sum: int
    reserve_value_sum: int
    lp_user_value_sum: int
    lp_protocol_liability_value_sum: int
    net_value_sum: int
    asset_conservation_ok: bool
    lp_liability_balanced_ok: bool
    value_conservation_ok: bool
    schema: str = SETTLEMENT_LP_VALUE_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        _require_hex_digest(self.settlement_commitment_sha256, name="settlement_commitment_sha256")
        _require_hex_digest(self.delta_commitment_sha256, name="delta_commitment_sha256")
        _require_hex_digest(self.price_vector_sha256, name="price_vector_sha256")
        _require_hex_digest(self.lp_value_vector_sha256, name="lp_value_vector_sha256")
        if not self.asset_prices:
            raise ValueError("asset_prices must be non-empty")
        if not self.lp_unit_values:
            raise ValueError("lp_unit_values must be non-empty")
        for name in (
            "balance_value_sum",
            "reserve_value_sum",
            "lp_user_value_sum",
            "lp_protocol_liability_value_sum",
            "net_value_sum",
        ):
            if not isinstance(getattr(self, name), int) or isinstance(getattr(self, name), bool):
                raise ValueError(f"{name} must be an int")
        for name in ("asset_conservation_ok", "lp_liability_balanced_ok", "value_conservation_ok"):
            if not isinstance(getattr(self, name), bool):
                raise ValueError(f"{name} must be a bool")
        if self.schema != SETTLEMENT_LP_VALUE_CONTRACT_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "settlement_commitment_sha256": self.settlement_commitment_sha256,
            "delta_commitment_sha256": self.delta_commitment_sha256,
            "price_vector_sha256": self.price_vector_sha256,
            "lp_value_vector_sha256": self.lp_value_vector_sha256,
            "asset_prices": [entry.to_dict() for entry in self.asset_prices],
            "lp_unit_values": [entry.to_dict() for entry in self.lp_unit_values],
            "asset_nets": [entry.to_dict() for entry in self.asset_nets],
            "lp_nets": [entry.to_dict() for entry in self.lp_nets],
            "balance_value_sum": int(self.balance_value_sum),
            "reserve_value_sum": int(self.reserve_value_sum),
            "lp_user_value_sum": int(self.lp_user_value_sum),
            "lp_protocol_liability_value_sum": int(self.lp_protocol_liability_value_sum),
            "net_value_sum": int(self.net_value_sum),
            "asset_conservation_ok": bool(self.asset_conservation_ok),
            "lp_liability_balanced_ok": bool(self.lp_liability_balanced_ok),
            "value_conservation_ok": bool(self.value_conservation_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementLPValueContract":
        if not isinstance(payload, Mapping):
            raise ValueError("contract must be an object")
        asset_prices_payload = payload.get("asset_prices", [])
        lp_values_payload = payload.get("lp_unit_values", [])
        asset_nets_payload = payload.get("asset_nets", [])
        lp_nets_payload = payload.get("lp_nets", [])
        if not isinstance(asset_prices_payload, list):
            raise ValueError("contract.asset_prices must be a list")
        if not isinstance(lp_values_payload, list):
            raise ValueError("contract.lp_unit_values must be a list")
        if not isinstance(asset_nets_payload, list):
            raise ValueError("contract.asset_nets must be a list")
        if not isinstance(lp_nets_payload, list):
            raise ValueError("contract.lp_nets must be a list")
        asset_conservation_ok = payload.get("asset_conservation_ok", False)
        lp_liability_balanced_ok = payload.get("lp_liability_balanced_ok", False)
        value_conservation_ok = payload.get("value_conservation_ok", False)
        if not isinstance(asset_conservation_ok, bool):
            raise ValueError("contract.asset_conservation_ok must be a bool")
        if not isinstance(lp_liability_balanced_ok, bool):
            raise ValueError("contract.lp_liability_balanced_ok must be a bool")
        if not isinstance(value_conservation_ok, bool):
            raise ValueError("contract.value_conservation_ok must be a bool")
        return cls(
            schema=str(payload.get("schema", "")),
            settlement_commitment_sha256=str(payload.get("settlement_commitment_sha256", "")),
            delta_commitment_sha256=str(payload.get("delta_commitment_sha256", "")),
            price_vector_sha256=str(payload.get("price_vector_sha256", "")),
            lp_value_vector_sha256=str(payload.get("lp_value_vector_sha256", "")),
            asset_prices=tuple(AssetPriceEntry.from_dict(entry) for entry in asset_prices_payload),
            lp_unit_values=tuple(LPUnitValueEntry.from_dict(entry) for entry in lp_values_payload),
            asset_nets=tuple(AssetNetValueEntry.from_dict(entry) for entry in asset_nets_payload),
            lp_nets=tuple(LPNetValueEntry.from_dict(entry) for entry in lp_nets_payload),
            balance_value_sum=int(payload.get("balance_value_sum", 0)),
            reserve_value_sum=int(payload.get("reserve_value_sum", 0)),
            lp_user_value_sum=int(payload.get("lp_user_value_sum", 0)),
            lp_protocol_liability_value_sum=int(payload.get("lp_protocol_liability_value_sum", 0)),
            net_value_sum=int(payload.get("net_value_sum", 0)),
            asset_conservation_ok=asset_conservation_ok,
            lp_liability_balanced_ok=lp_liability_balanced_ok,
            value_conservation_ok=value_conservation_ok,
        )


def build_settlement_lp_value_contract(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
    lp_unit_values: Mapping[str, int],
) -> SettlementLPValueContract:
    normalized = _normalized_settlement_dict(settlement)
    price_entries = _canonical_price_entries(asset_prices)
    lp_value_entries = _canonical_lp_value_entries(lp_unit_values)
    price_map = {entry.asset: entry.price for entry in price_entries}
    lp_value_map = {entry.pool_id: entry.unit_value for entry in lp_value_entries}

    balance_value_sum = 0
    reserve_value_sum = 0
    asset_nets: dict[str, int] = {}

    for delta in normalized.get("balance_deltas", []):
        asset = str(delta["asset"])
        price = _require_priced_asset(price_map, asset)
        net_delta = int(delta["delta_add"]) - int(delta["delta_sub"])
        asset_nets[asset] = int(asset_nets.get(asset, 0)) + int(net_delta)
        balance_value_sum += int(net_delta) * int(price)

    for delta in normalized.get("reserve_deltas", []):
        asset = str(delta["asset"])
        price = _require_priced_asset(price_map, asset)
        net_delta = int(delta["delta_add"]) - int(delta["delta_sub"])
        asset_nets[asset] = int(asset_nets.get(asset, 0)) + int(net_delta)
        reserve_value_sum += int(net_delta) * int(price)

    asset_net_entries = tuple(
        AssetNetValueEntry(
            asset=asset,
            net_delta=int(net_delta),
            unit_price=int(price_map[asset]),
            value=int(net_delta) * int(price_map[asset]),
        )
        for asset, net_delta in sorted(asset_nets.items())
    )

    lp_nets_by_pool: dict[str, int] = {}
    for delta in normalized.get("lp_deltas", []):
        pool_id = str(delta["pool_id"])
        _require_lp_unit_value(lp_value_map, pool_id)
        net_delta = int(delta["delta_add"]) - int(delta["delta_sub"])
        lp_nets_by_pool[pool_id] = int(lp_nets_by_pool.get(pool_id, 0)) + int(net_delta)

    lp_net_entries = tuple(
        LPNetValueEntry(
            pool_id=pool_id,
            net_delta=int(net_delta),
            unit_value=int(lp_value_map[pool_id]),
            user_value=int(net_delta) * int(lp_value_map[pool_id]),
            protocol_liability_value=-(int(net_delta) * int(lp_value_map[pool_id])),
        )
        for pool_id, net_delta in sorted(lp_nets_by_pool.items())
    )

    lp_user_value_sum = sum(entry.user_value for entry in lp_net_entries)
    lp_protocol_liability_value_sum = sum(entry.protocol_liability_value for entry in lp_net_entries)
    net_value_sum = int(balance_value_sum) + int(reserve_value_sum) + int(lp_user_value_sum) + int(lp_protocol_liability_value_sum)

    return SettlementLPValueContract(
        settlement_commitment_sha256=_sha256_json(normalized),
        delta_commitment_sha256=_sha256_json(
            {
                "balance_deltas": normalized.get("balance_deltas", []),
                "reserve_deltas": normalized.get("reserve_deltas", []),
                "lp_deltas": normalized.get("lp_deltas", []),
            }
        ),
        price_vector_sha256=_sha256_json({"asset_prices": [entry.to_dict() for entry in price_entries]}),
        lp_value_vector_sha256=_sha256_json({"lp_unit_values": [entry.to_dict() for entry in lp_value_entries]}),
        asset_prices=price_entries,
        lp_unit_values=lp_value_entries,
        asset_nets=asset_net_entries,
        lp_nets=lp_net_entries,
        balance_value_sum=int(balance_value_sum),
        reserve_value_sum=int(reserve_value_sum),
        lp_user_value_sum=int(lp_user_value_sum),
        lp_protocol_liability_value_sum=int(lp_protocol_liability_value_sum),
        net_value_sum=int(net_value_sum),
        asset_conservation_ok=all(entry.net_delta == 0 for entry in asset_net_entries),
        lp_liability_balanced_ok=all((entry.user_value + entry.protocol_liability_value) == 0 for entry in lp_net_entries),
        value_conservation_ok=(int(net_value_sum) == 0),
    )


def verify_settlement_lp_value_contract(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
    lp_unit_values: Mapping[str, int],
    contract: SettlementLPValueContract,
) -> tuple[bool, str | None]:
    if not isinstance(contract, SettlementLPValueContract):
        return False, "contract must be a SettlementLPValueContract"
    expected = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices,
        lp_unit_values=lp_unit_values,
    )
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement lp value contract mismatch"
    return True, None


def build_settlement_lp_value_contract_from_price_packet(
    *,
    settlement: Settlement,
    price_packet: SettlementSpotPricePacket,
    lp_unit_values: Mapping[str, int],
) -> SettlementLPValueContract:
    ok, err = verify_settlement_spot_price_packet(packet=price_packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not price_packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    return build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_packet),
        lp_unit_values=lp_unit_values,
    )


def build_settlement_lp_value_contract_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    lp_unit_values: Mapping[str, int],
    attestation_policy: SettlementAttestationPolicy | None = None,
) -> SettlementLPValueContract:
    from .settlement_attestation_policy import coerce_settlement_attestation_policy
    from .settlement_price_attestation import verify_settlement_spot_price_attestation

    attestation_policy = coerce_settlement_attestation_policy(attestation_policy)

    ok, err = verify_settlement_spot_price_attestation(
        attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        attestation_policy=attestation_policy,
    )
    if not ok:
        raise ValueError(f"invalid settlement spot price attestation: {err}")
    return build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
        lp_unit_values=lp_unit_values,
    )


def verify_settlement_lp_value_contract_payload(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
    lp_unit_values: Mapping[str, int],
    contract_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        contract = SettlementLPValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices,
        lp_unit_values=lp_unit_values,
        contract=contract,
    )


def verify_settlement_lp_value_contract_payload_from_price_packet(
    *,
    settlement: Settlement,
    price_packet_payload: Mapping[str, Any],
    lp_unit_values: Mapping[str, int],
    contract_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        price_packet = SettlementSpotPricePacket.from_dict(price_packet_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        contract = SettlementLPValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    expected = build_settlement_lp_value_contract_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        lp_unit_values=lp_unit_values,
    )
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement lp value contract mismatch"
    return True, None


def verify_settlement_lp_value_contract_payload_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation_payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    lp_unit_values: Mapping[str, int],
    contract_payload: Mapping[str, Any],
    attestation_policy: SettlementAttestationPolicy | None = None,
) -> tuple[bool, str | None]:
    from .settlement_price_attestation import SettlementSpotPriceAttestation

    try:
        price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        contract = SettlementLPValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    expected = build_settlement_lp_value_contract_from_price_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        lp_unit_values=lp_unit_values,
        attestation_policy=attestation_policy,
    )
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement lp value contract mismatch"
    return True, None


def _canonical_price_entries(asset_prices: Mapping[str, int]) -> tuple[AssetPriceEntry, ...]:
    if not isinstance(asset_prices, Mapping) or not asset_prices:
        raise ValueError("asset_prices must be a non-empty mapping")
    entries = [AssetPriceEntry(asset=str(asset), price=int(price)) for asset, price in asset_prices.items()]
    entries.sort(key=lambda entry: entry.asset)
    return tuple(entries)


def _canonical_lp_value_entries(lp_unit_values: Mapping[str, int]) -> tuple[LPUnitValueEntry, ...]:
    if not isinstance(lp_unit_values, Mapping) or not lp_unit_values:
        raise ValueError("lp_unit_values must be a non-empty mapping")
    entries = [LPUnitValueEntry(pool_id=str(pool_id), unit_value=int(unit_value)) for pool_id, unit_value in lp_unit_values.items()]
    entries.sort(key=lambda entry: entry.pool_id)
    return tuple(entries)


def _normalized_settlement_dict(settlement: Settlement) -> dict[str, Any]:
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("internal error: settlement operation must be a dict")
    return normalize_settlement_op_for_commitment(op)


def _sha256_json(value: Mapping[str, Any]) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def _require_priced_asset(price_map: Mapping[str, int], asset: str) -> int:
    if asset not in price_map:
        raise ValueError(f"missing asset price for settlement lp value contract: {asset}")
    return int(price_map[asset])


def _require_lp_unit_value(lp_value_map: Mapping[str, int], pool_id: str) -> int:
    if pool_id not in lp_value_map:
        raise ValueError(f"missing lp unit value for settlement lp value contract: {pool_id}")
    return int(lp_value_map[pool_id])


def _require_hex_digest(value: str, *, name: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest")
    try:
        int(value, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest") from exc
