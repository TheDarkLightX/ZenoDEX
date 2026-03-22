from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Mapping, Sequence

from src.core.settlement import Settlement
from src.state.canonical import canonical_hex_fixed_allow_0x
from src.state.pools import PoolState, PoolStatus

from .settlement_lp_value_contract import SettlementLPValueContract, build_settlement_lp_value_contract
from .settlement_price_provenance import (
    SettlementSpotPricePacket,
    asset_prices_from_spot_price_packet,
    verify_settlement_spot_price_packet,
)

if TYPE_CHECKING:
    from .settlement_attestation_policy import SettlementAttestationPolicy
    from .settlement_price_attestation import SettlementSpotPriceAttestation


SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA = "zenodex/settlement-endogenous-lp-value-packet/v1"


@dataclass(frozen=True)
class SettlementEndogenousLPValuePacket:
    price_input_kind: str
    price_packet: SettlementSpotPricePacket
    price_attestation: SettlementSpotPriceAttestation | None
    attestation_policy_id: str | None
    attestation_policy_epoch: int | None
    attestation_policy_root: str | None
    attestation_policy_hash: str | None
    pool_snapshots: tuple[dict[str, Any], ...]
    pool_snapshot_vector_sha256: str
    lp_value_contract: SettlementLPValueContract
    price_provenance_ok: bool
    attestation_ok: bool
    unique_pool_ids_ok: bool
    all_positive_lp_supply_ok: bool
    all_assets_priced_ok: bool
    asset_conservation_ok: bool
    lp_liability_balanced_ok: bool
    value_conservation_ok: bool
    packet_ok: bool
    schema: str = SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_ENDOGENOUS_LP_VALUE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.price_input_kind not in {"packet", "attestation"}:
            raise ValueError("price_input_kind must be 'packet' or 'attestation'")
        if not isinstance(self.price_packet, SettlementSpotPricePacket):
            raise TypeError("price_packet must be a SettlementSpotPricePacket")
        if self.price_input_kind == "packet":
            if self.price_attestation is not None:
                raise ValueError("price_attestation must be None for packet mode")
            if any(
                value is not None
                for value in (
                    self.attestation_policy_id,
                    self.attestation_policy_epoch,
                    self.attestation_policy_root,
                    self.attestation_policy_hash,
                )
            ):
                raise ValueError("attestation policy fields must be None for packet mode")
        else:
            if self.price_attestation is None:
                raise ValueError("price_attestation must be present for attestation mode")
            if not isinstance(self.attestation_policy_id, str) or not self.attestation_policy_id:
                raise ValueError("attestation_policy_id must be present for attestation mode")
            if (
                not isinstance(self.attestation_policy_epoch, int)
                or isinstance(self.attestation_policy_epoch, bool)
                or self.attestation_policy_epoch < 0
            ):
                raise ValueError("attestation_policy_epoch must be a non-negative int")
            if not isinstance(self.attestation_policy_root, str):
                raise ValueError("attestation_policy_root must be present for attestation mode")
            if not isinstance(self.attestation_policy_hash, str):
                raise ValueError("attestation_policy_hash must be present for attestation mode")
            object.__setattr__(
                self,
                "attestation_policy_root",
                canonical_hex_fixed_allow_0x(
                    self.attestation_policy_root,
                    nbytes=32,
                    name="attestation_policy_root",
                ),
            )
            object.__setattr__(
                self,
                "attestation_policy_hash",
                canonical_hex_fixed_allow_0x(
                    self.attestation_policy_hash,
                    nbytes=32,
                    name="attestation_policy_hash",
                ),
            )
        if not self.pool_snapshots:
            raise ValueError("pool_snapshots must be non-empty")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        _require_hex_digest(self.pool_snapshot_vector_sha256, name="pool_snapshot_vector_sha256")
        if not isinstance(self.lp_value_contract, SettlementLPValueContract):
            raise TypeError("lp_value_contract must be a SettlementLPValueContract")
        for name in (
            "price_provenance_ok",
            "attestation_ok",
            "unique_pool_ids_ok",
            "all_positive_lp_supply_ok",
            "all_assets_priced_ok",
            "asset_conservation_ok",
            "lp_liability_balanced_ok",
            "value_conservation_ok",
            "packet_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "price_input_kind": self.price_input_kind,
            "price_packet": self.price_packet.to_dict(),
            "price_attestation": None if self.price_attestation is None else self.price_attestation.to_dict(),
            "attestation_policy_id": self.attestation_policy_id,
            "attestation_policy_epoch": self.attestation_policy_epoch,
            "attestation_policy_root": self.attestation_policy_root,
            "attestation_policy_hash": self.attestation_policy_hash,
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "pool_snapshot_vector_sha256": self.pool_snapshot_vector_sha256,
            "lp_value_contract": self.lp_value_contract.to_dict(),
            "price_provenance_ok": bool(self.price_provenance_ok),
            "attestation_ok": bool(self.attestation_ok),
            "unique_pool_ids_ok": bool(self.unique_pool_ids_ok),
            "all_positive_lp_supply_ok": bool(self.all_positive_lp_supply_ok),
            "all_assets_priced_ok": bool(self.all_assets_priced_ok),
            "asset_conservation_ok": bool(self.asset_conservation_ok),
            "lp_liability_balanced_ok": bool(self.lp_liability_balanced_ok),
            "value_conservation_ok": bool(self.value_conservation_ok),
            "packet_ok": bool(self.packet_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementEndogenousLPValuePacket":
        if not isinstance(payload, Mapping):
            raise ValueError("packet must be an object")
        from .settlement_price_attestation import SettlementSpotPriceAttestation

        price_packet_payload = payload.get("price_packet")
        if not isinstance(price_packet_payload, Mapping):
            raise ValueError("packet.price_packet must be an object")
        price_attestation_payload = payload.get("price_attestation")
        pool_snapshots_payload = payload.get("pool_snapshots")
        if not isinstance(pool_snapshots_payload, list) or not pool_snapshots_payload:
            raise ValueError("packet.pool_snapshots must be a non-empty list")
        lp_value_contract_payload = payload.get("lp_value_contract")
        if not isinstance(lp_value_contract_payload, Mapping):
            raise ValueError("packet.lp_value_contract must be an object")
        return cls(
            schema=str(payload.get("schema", "")),
            price_input_kind=str(payload.get("price_input_kind", "")),
            price_packet=SettlementSpotPricePacket.from_dict(price_packet_payload),
            price_attestation=(
                None
                if price_attestation_payload is None
                else SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
            ),
            attestation_policy_id=payload.get("attestation_policy_id"),
            attestation_policy_epoch=payload.get("attestation_policy_epoch"),
            attestation_policy_root=payload.get("attestation_policy_root"),
            attestation_policy_hash=payload.get("attestation_policy_hash"),
            pool_snapshots=tuple(dict(snapshot) for snapshot in pool_snapshots_payload),
            pool_snapshot_vector_sha256=str(payload.get("pool_snapshot_vector_sha256", "")),
            lp_value_contract=SettlementLPValueContract.from_dict(lp_value_contract_payload),
            price_provenance_ok=bool(payload.get("price_provenance_ok", False)),
            attestation_ok=bool(payload.get("attestation_ok", False)),
            unique_pool_ids_ok=bool(payload.get("unique_pool_ids_ok", False)),
            all_positive_lp_supply_ok=bool(payload.get("all_positive_lp_supply_ok", False)),
            all_assets_priced_ok=bool(payload.get("all_assets_priced_ok", False)),
            asset_conservation_ok=bool(payload.get("asset_conservation_ok", False)),
            lp_liability_balanced_ok=bool(payload.get("lp_liability_balanced_ok", False)),
            value_conservation_ok=bool(payload.get("value_conservation_ok", False)),
            packet_ok=bool(payload.get("packet_ok", False)),
        )


def build_settlement_endogenous_lp_value_packet_from_price_packet(
    *,
    settlement: Settlement,
    price_packet: SettlementSpotPricePacket,
    pool_snapshots: Sequence[PoolState],
) -> SettlementEndogenousLPValuePacket:
    ok, err = verify_settlement_spot_price_packet(packet=price_packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not price_packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    canonical_snapshots = _canonical_pool_snapshots(pool_snapshots)
    unit_values = _derive_lp_unit_values(
        canonical_snapshots=canonical_snapshots,
        asset_prices=asset_prices_from_spot_price_packet(price_packet),
    )
    contract = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_packet),
        lp_unit_values=unit_values,
    )
    return SettlementEndogenousLPValuePacket(
        price_input_kind="packet",
        price_packet=price_packet,
        price_attestation=None,
        attestation_policy_id=None,
        attestation_policy_epoch=None,
        attestation_policy_root=None,
        attestation_policy_hash=None,
        pool_snapshots=canonical_snapshots,
        pool_snapshot_vector_sha256=_sha256_json({"pool_snapshots": list(canonical_snapshots)}),
        lp_value_contract=contract,
        price_provenance_ok=bool(price_packet.provenance_ok),
        attestation_ok=True,
        unique_pool_ids_ok=True,
        all_positive_lp_supply_ok=True,
        all_assets_priced_ok=True,
        asset_conservation_ok=bool(contract.asset_conservation_ok),
        lp_liability_balanced_ok=bool(contract.lp_liability_balanced_ok),
        value_conservation_ok=bool(contract.value_conservation_ok),
        packet_ok=bool(
            price_packet.provenance_ok
            and contract.asset_conservation_ok
            and contract.lp_liability_balanced_ok
            and contract.value_conservation_ok
        ),
    )


def build_settlement_endogenous_lp_value_packet_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    pool_snapshots: Sequence[PoolState],
    attestation_policy: SettlementAttestationPolicy | None = None,
) -> SettlementEndogenousLPValuePacket:
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
    if attestation_policy is None:
        raise ValueError("attestation mode requires attestation_policy")
    canonical_snapshots = _canonical_pool_snapshots(pool_snapshots)
    unit_values = _derive_lp_unit_values(
        canonical_snapshots=canonical_snapshots,
        asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
    )
    contract = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
        lp_unit_values=unit_values,
    )
    return SettlementEndogenousLPValuePacket(
        price_input_kind="attestation",
        price_packet=price_attestation.packet,
        price_attestation=price_attestation,
        attestation_policy_id=attestation_policy.policy_id,
        attestation_policy_epoch=int(attestation_policy.policy_epoch),
        attestation_policy_root=attestation_policy.registry_root,
        attestation_policy_hash=attestation_policy.policy_hash_hex(),
        pool_snapshots=canonical_snapshots,
        pool_snapshot_vector_sha256=_sha256_json({"pool_snapshots": list(canonical_snapshots)}),
        lp_value_contract=contract,
        price_provenance_ok=bool(price_attestation.packet.provenance_ok),
        attestation_ok=True,
        unique_pool_ids_ok=True,
        all_positive_lp_supply_ok=True,
        all_assets_priced_ok=True,
        asset_conservation_ok=bool(contract.asset_conservation_ok),
        lp_liability_balanced_ok=bool(contract.lp_liability_balanced_ok),
        value_conservation_ok=bool(contract.value_conservation_ok),
        packet_ok=bool(
            price_attestation.packet.provenance_ok
            and contract.asset_conservation_ok
            and contract.lp_liability_balanced_ok
            and contract.value_conservation_ok
        ),
    )


def verify_settlement_endogenous_lp_value_packet_payload_from_price_packet(
    *,
    settlement: Settlement,
    price_packet_payload: Mapping[str, Any],
    pool_snapshots_payload: Sequence[Mapping[str, Any]],
    packet_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        price_packet = SettlementSpotPricePacket.from_dict(price_packet_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        pool_snapshots = tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        expected = build_settlement_endogenous_lp_value_packet_from_price_packet(
            settlement=settlement,
            price_packet=price_packet,
            pool_snapshots=pool_snapshots,
        )
    except Exception as exc:
        return False, str(exc)
    try:
        packet = SettlementEndogenousLPValuePacket.from_dict(packet_payload)
    except Exception as exc:
        return False, str(exc)
    if packet.schema != expected.schema:
        return False, "schema mismatch"
    if packet != expected:
        return False, "settlement endogenous lp value packet mismatch"
    return True, None


def verify_settlement_endogenous_lp_value_packet_payload_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation_payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    pool_snapshots_payload: Sequence[Mapping[str, Any]],
    packet_payload: Mapping[str, Any],
    attestation_policy: SettlementAttestationPolicy | None = None,
) -> tuple[bool, str | None]:
    from .settlement_price_attestation import SettlementSpotPriceAttestation

    try:
        price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        pool_snapshots = tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_payload)
    except Exception as exc:
        return False, str(exc)
    try:
        expected = build_settlement_endogenous_lp_value_packet_from_price_attestation(
            settlement=settlement,
            price_attestation=price_attestation,
            consumer_now_epoch=consumer_now_epoch,
            max_attestation_age_epochs=max_attestation_age_epochs,
            pool_snapshots=pool_snapshots,
            attestation_policy=attestation_policy,
        )
    except Exception as exc:
        return False, str(exc)
    try:
        packet = SettlementEndogenousLPValuePacket.from_dict(packet_payload)
    except Exception as exc:
        return False, str(exc)
    if packet.schema != expected.schema:
        return False, "schema mismatch"
    if packet != expected:
        return False, "settlement endogenous lp value packet mismatch"
    return True, None


def _canonical_pool_snapshots(pool_snapshots: Sequence[PoolState]) -> tuple[dict[str, Any], ...]:
    canonical = tuple(sorted((_pool_to_dict(pool) for pool in pool_snapshots), key=lambda snapshot: snapshot["pool_id"]))
    if not canonical:
        raise ValueError("pool_snapshots must be non-empty")
    pool_ids = [str(snapshot["pool_id"]) for snapshot in canonical]
    if len(set(pool_ids)) != len(pool_ids):
        raise ValueError("pool_snapshots must have unique pool_id values")
    for snapshot in canonical:
        if int(snapshot["lp_supply"]) <= 0:
            raise ValueError(f"pool snapshot lp_supply must be positive for {snapshot['pool_id']}")
    return canonical


def _derive_lp_unit_values(
    *,
    canonical_snapshots: Sequence[Mapping[str, Any]],
    asset_prices: Mapping[str, int],
) -> dict[str, int]:
    unit_values: dict[str, int] = {}
    for snapshot in canonical_snapshots:
        asset0 = str(snapshot["asset0"])
        asset1 = str(snapshot["asset1"])
        if asset0 not in asset_prices:
            raise ValueError(f"missing price for asset0: {asset0}")
        if asset1 not in asset_prices:
            raise ValueError(f"missing price for asset1: {asset1}")
        reserve0 = int(snapshot["reserve0"])
        reserve1 = int(snapshot["reserve1"])
        lp_supply = int(snapshot["lp_supply"])
        gross_value = reserve0 * int(asset_prices[asset0]) + reserve1 * int(asset_prices[asset1])
        unit_values[str(snapshot["pool_id"])] = gross_value // lp_supply
    return unit_values


def _pool_to_dict(pool: PoolState) -> dict[str, Any]:
    return {
        "pool_id": str(pool.pool_id),
        "asset0": str(pool.asset0),
        "asset1": str(pool.asset1),
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "lp_supply": int(pool.lp_supply),
        "status": str(pool.status.name),
        "created_at": int(pool.created_at),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
    }


def _pool_from_dict(payload: Mapping[str, Any]) -> PoolState:
    if not isinstance(payload, Mapping):
        raise TypeError("pool snapshot payload must be an object")
    status_raw = payload.get("status")
    if not isinstance(status_raw, str) or status_raw not in PoolStatus.__members__:
        raise ValueError("pool snapshot status must be a valid PoolStatus string")
    return PoolState(
        pool_id=str(payload.get("pool_id", "")),
        asset0=str(payload.get("asset0", "")),
        asset1=str(payload.get("asset1", "")),
        reserve0=int(payload.get("reserve0", 0)),
        reserve1=int(payload.get("reserve1", 0)),
        fee_bps=int(payload.get("fee_bps", 0)),
        lp_supply=int(payload.get("lp_supply", 0)),
        status=PoolStatus[status_raw],
        created_at=int(payload.get("created_at", 0)),
        curve_tag=str(payload.get("curve_tag", "CPMM")),
        curve_params=str(payload.get("curve_params", "")),
    )


def _sha256_json(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def _require_hex_digest(value: str, *, name: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise ValueError(f"{name} must be a 64-char sha256 hex digest")
    try:
        int(value, 16)
    except Exception as exc:  # pragma: no cover
        raise ValueError(f"{name} must be hex") from exc
