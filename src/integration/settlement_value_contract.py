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

if TYPE_CHECKING:
    from .settlement_attestation_policy import SettlementAttestationPolicy
    from .settlement_price_attestation import SettlementSpotPriceAttestation
    from .settlement_signer_registry import SettlementSignerRegistrySnapshot


SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA = "zenodex/settlement-spot-value-contract/v1"


@dataclass(frozen=True)
class AssetPriceEntry:
    asset: str
    price: int

    def __post_init__(self) -> None:
        if not isinstance(self.asset, str) or not self.asset:
            raise ValueError("asset must be a non-empty string")
        if not isinstance(self.price, int) or isinstance(self.price, bool) or self.price < 0:
            raise ValueError("price must be a non-negative int")

    def to_dict(self) -> dict[str, Any]:
        return {
            "asset": self.asset,
            "price": int(self.price),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "AssetPriceEntry":
        if not isinstance(payload, Mapping):
            raise ValueError("asset price entry must be an object")
        return cls(
            asset=str(payload.get("asset", "")),
            price=int(payload.get("price", -1)),
        )


@dataclass(frozen=True)
class AssetNetValueEntry:
    asset: str
    net_delta: int
    unit_price: int
    value: int

    def __post_init__(self) -> None:
        if not isinstance(self.asset, str) or not self.asset:
            raise ValueError("asset must be a non-empty string")
        if not isinstance(self.net_delta, int) or isinstance(self.net_delta, bool):
            raise ValueError("net_delta must be an int")
        if not isinstance(self.unit_price, int) or isinstance(self.unit_price, bool) or self.unit_price < 0:
            raise ValueError("unit_price must be a non-negative int")
        if not isinstance(self.value, int) or isinstance(self.value, bool):
            raise ValueError("value must be an int")

    def to_dict(self) -> dict[str, Any]:
        return {
            "asset": self.asset,
            "net_delta": int(self.net_delta),
            "unit_price": int(self.unit_price),
            "value": int(self.value),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "AssetNetValueEntry":
        if not isinstance(payload, Mapping):
            raise ValueError("asset net entry must be an object")
        return cls(
            asset=str(payload.get("asset", "")),
            net_delta=int(payload.get("net_delta", 0)),
            unit_price=int(payload.get("unit_price", -1)),
            value=int(payload.get("value", 0)),
        )


@dataclass(frozen=True)
class SettlementSpotValueContract:
    settlement_commitment_sha256: str
    delta_commitment_sha256: str
    price_vector_sha256: str
    asset_prices: tuple[AssetPriceEntry, ...]
    asset_nets: tuple[AssetNetValueEntry, ...]
    balance_value_sum: int
    reserve_value_sum: int
    net_value_sum: int
    asset_conservation_ok: bool
    value_conservation_ok: bool
    schema: str = SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        _require_hex_digest(self.settlement_commitment_sha256, name="settlement_commitment_sha256")
        _require_hex_digest(self.delta_commitment_sha256, name="delta_commitment_sha256")
        _require_hex_digest(self.price_vector_sha256, name="price_vector_sha256")
        if not self.asset_prices:
            raise ValueError("asset_prices must be non-empty")
        if not isinstance(self.balance_value_sum, int) or isinstance(self.balance_value_sum, bool):
            raise ValueError("balance_value_sum must be an int")
        if not isinstance(self.reserve_value_sum, int) or isinstance(self.reserve_value_sum, bool):
            raise ValueError("reserve_value_sum must be an int")
        if not isinstance(self.net_value_sum, int) or isinstance(self.net_value_sum, bool):
            raise ValueError("net_value_sum must be an int")
        if not isinstance(self.asset_conservation_ok, bool):
            raise ValueError("asset_conservation_ok must be a bool")
        if not isinstance(self.value_conservation_ok, bool):
            raise ValueError("value_conservation_ok must be a bool")
        if self.schema != SETTLEMENT_SPOT_VALUE_CONTRACT_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "settlement_commitment_sha256": self.settlement_commitment_sha256,
            "delta_commitment_sha256": self.delta_commitment_sha256,
            "price_vector_sha256": self.price_vector_sha256,
            "asset_prices": [entry.to_dict() for entry in self.asset_prices],
            "asset_nets": [entry.to_dict() for entry in self.asset_nets],
            "balance_value_sum": int(self.balance_value_sum),
            "reserve_value_sum": int(self.reserve_value_sum),
            "net_value_sum": int(self.net_value_sum),
            "asset_conservation_ok": bool(self.asset_conservation_ok),
            "value_conservation_ok": bool(self.value_conservation_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementSpotValueContract":
        if not isinstance(payload, Mapping):
            raise ValueError("contract must be an object")
        asset_prices_payload = payload.get("asset_prices", [])
        if not isinstance(asset_prices_payload, list):
            raise ValueError("contract.asset_prices must be a list")
        asset_nets_payload = payload.get("asset_nets", [])
        if not isinstance(asset_nets_payload, list):
            raise ValueError("contract.asset_nets must be a list")
        asset_conservation_ok = payload.get("asset_conservation_ok", False)
        if not isinstance(asset_conservation_ok, bool):
            raise ValueError("contract.asset_conservation_ok must be a bool")
        value_conservation_ok = payload.get("value_conservation_ok", False)
        if not isinstance(value_conservation_ok, bool):
            raise ValueError("contract.value_conservation_ok must be a bool")
        return cls(
            schema=str(payload.get("schema", "")),
            settlement_commitment_sha256=str(payload.get("settlement_commitment_sha256", "")),
            delta_commitment_sha256=str(payload.get("delta_commitment_sha256", "")),
            price_vector_sha256=str(payload.get("price_vector_sha256", "")),
            asset_prices=tuple(AssetPriceEntry.from_dict(entry) for entry in asset_prices_payload),
            asset_nets=tuple(AssetNetValueEntry.from_dict(entry) for entry in asset_nets_payload),
            balance_value_sum=int(payload.get("balance_value_sum", 0)),
            reserve_value_sum=int(payload.get("reserve_value_sum", 0)),
            net_value_sum=int(payload.get("net_value_sum", 0)),
            asset_conservation_ok=asset_conservation_ok,
            value_conservation_ok=value_conservation_ok,
        )


def build_settlement_spot_value_contract(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
) -> SettlementSpotValueContract:
    normalized = _normalized_settlement_dict(settlement)
    if normalized.get("lp_deltas"):
        raise ValueError("spot value contract requires settlement with empty lp_deltas")

    price_entries = _canonical_price_entries(asset_prices)
    price_map = {entry.asset: entry.price for entry in price_entries}

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
    net_value_sum = int(balance_value_sum) + int(reserve_value_sum)

    return SettlementSpotValueContract(
        settlement_commitment_sha256=_sha256_json(normalized),
        delta_commitment_sha256=_sha256_json(
            {
                "balance_deltas": normalized.get("balance_deltas", []),
                "reserve_deltas": normalized.get("reserve_deltas", []),
                "lp_deltas": normalized.get("lp_deltas", []),
            }
        ),
        price_vector_sha256=_sha256_json({"asset_prices": [entry.to_dict() for entry in price_entries]}),
        asset_prices=price_entries,
        asset_nets=asset_net_entries,
        balance_value_sum=int(balance_value_sum),
        reserve_value_sum=int(reserve_value_sum),
        net_value_sum=int(net_value_sum),
        asset_conservation_ok=all(entry.net_delta == 0 for entry in asset_net_entries),
        value_conservation_ok=(int(net_value_sum) == 0),
    )


def verify_settlement_spot_value_contract(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
    contract: SettlementSpotValueContract,
) -> tuple[bool, str | None]:
    if not isinstance(contract, SettlementSpotValueContract):
        return False, "contract must be a SettlementSpotValueContract"
    expected = build_settlement_spot_value_contract(settlement=settlement, asset_prices=asset_prices)
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement spot value contract mismatch"
    return True, None


def build_settlement_spot_value_contract_from_price_packet(
    *,
    settlement: Settlement,
    price_packet: SettlementSpotPricePacket,
) -> SettlementSpotValueContract:
    ok, err = verify_settlement_spot_price_packet(packet=price_packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not price_packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    return build_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_packet),
    )


def verify_settlement_spot_value_contract_from_price_packet(
    *,
    settlement: Settlement,
    price_packet: SettlementSpotPricePacket,
    contract: SettlementSpotValueContract,
) -> tuple[bool, str | None]:
    try:
        expected = build_settlement_spot_value_contract_from_price_packet(
            settlement=settlement,
            price_packet=price_packet,
        )
    except Exception as exc:
        return False, str(exc)
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement spot value contract mismatch"
    return True, None


def build_settlement_spot_value_contract_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
) -> SettlementSpotValueContract:
    from .settlement_price_attestation import verify_settlement_spot_price_attestation
    from .settlement_signer_registry import load_attestation_policy_and_registry_snapshot

    attestation_policy, attestation_registry_snapshot = load_attestation_policy_and_registry_snapshot(
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
        consumer_now_epoch=int(consumer_now_epoch),
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
    )
    if not ok:
        raise ValueError(f"invalid settlement spot price attestation: {err}")
    return build_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
    )


def verify_settlement_spot_value_contract_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    contract: SettlementSpotValueContract,
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
) -> tuple[bool, str | None]:
    try:
        expected = build_settlement_spot_value_contract_from_price_attestation(
            settlement=settlement,
            price_attestation=price_attestation,
            consumer_now_epoch=consumer_now_epoch,
            max_attestation_age_epochs=max_attestation_age_epochs,
            attestation_policy=attestation_policy,
            attestation_registry_snapshot=attestation_registry_snapshot,
            attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
        )
    except Exception as exc:
        return False, str(exc)
    if contract.schema != expected.schema:
        return False, "schema mismatch"
    if contract != expected:
        return False, "settlement spot value contract mismatch"
    return True, None


def verify_settlement_spot_value_contract_payload(
    *,
    settlement: Settlement,
    asset_prices: Mapping[str, int],
    contract_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        contract = SettlementSpotValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=asset_prices,
        contract=contract,
    )


def verify_settlement_spot_value_contract_payload_from_price_packet(
    *,
    settlement: Settlement,
    price_packet_payload: Mapping[str, Any],
    contract_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        price_packet = SettlementSpotPricePacket.from_dict(price_packet_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        contract = SettlementSpotValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_spot_value_contract_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
        contract=contract,
    )


def verify_settlement_spot_value_contract_payload_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation_payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    contract_payload: Mapping[str, Any],
    attestation_policy: SettlementAttestationPolicy | None = None,
    attestation_registry_snapshot: SettlementSignerRegistrySnapshot | None = None,
    attestation_registry_snapshot_loader: object | None = None,
) -> tuple[bool, str | None]:
    from .settlement_price_attestation import SettlementSpotPriceAttestation

    try:
        price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        contract = SettlementSpotValueContract.from_dict(contract_payload)
    except Exception as exc:
        return False, str(exc)
    return verify_settlement_spot_value_contract_from_price_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        contract=contract,
        attestation_policy=attestation_policy,
        attestation_registry_snapshot=attestation_registry_snapshot,
        attestation_registry_snapshot_loader=attestation_registry_snapshot_loader,
    )


def _canonical_price_entries(asset_prices: Mapping[str, int]) -> tuple[AssetPriceEntry, ...]:
    if not isinstance(asset_prices, Mapping) or not asset_prices:
        raise ValueError("asset_prices must be a non-empty mapping")
    entries: list[AssetPriceEntry] = []
    for asset, price in asset_prices.items():
        entries.append(AssetPriceEntry(asset=str(asset), price=int(price)))
    entries.sort(key=lambda entry: entry.asset)
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
        raise ValueError(f"missing asset price for settlement value contract: {asset}")
    return int(price_map[asset])


def _require_hex_digest(value: str, *, name: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest")
    try:
        int(value, 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest") from exc
