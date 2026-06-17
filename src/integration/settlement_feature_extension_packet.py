from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from .tau_witness import (
    build_settlement_feature_extension_bundle_v1_step,
    build_tdex_buyback_floor_fixedpoint_v2_step,
    build_tdex_buyback_floor_v2_step,
    build_tdex_fee_rebate_v1_step,
    build_tdex_lock_weight_v1_step,
)

SETTLEMENT_FEATURE_EXTENSION_PACKET_SCHEMA = "zenodex/settlement-feature-extension-packet/v1"
_PACKET_DOMAIN_ERRORS = (TypeError, ValueError, ArithmeticError)


def _require_u16(value: int, *, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > 0xFFFF:
        raise ValueError(f"{name} out of u16 range: {value!r}")


def _require_u32(value: int, *, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > 0xFFFFFFFF:
        raise ValueError(f"{name} out of u32 range: {value!r}")


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return value


def _require_int_field(payload: Mapping[str, Any], name: str) -> int:
    try:
        value = payload[name]
    except KeyError as exc:
        raise ValueError(f"missing feature extension input field: {name}") from exc
    return _require_int(value, name=name)


def _require_step_dict(value: object, *, name: str) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return {str(key): _require_int(step_value, name=f"{name}.{key}") for key, step_value in value.items()}


@dataclass(frozen=True)
class SettlementFeatureExtensionInputs:
    trade_amount: int
    fee_charged: int
    buyback_amount: int
    burned_amount: int
    supply_before: int
    supply_after: int
    supply_floor: int
    unit_scale: int
    rebate_rate_bps: int
    rebate_amount: int
    rebate_cap: int
    lock_days: int
    stake_amount: int
    tier1_days: int
    tier2_days: int
    weight_t1: int
    weight_t2: int
    weight_t3: int
    weight_claimed: int
    weighted_stake: int

    def __post_init__(self) -> None:
        for name in (
            "trade_amount",
            "fee_charged",
            "buyback_amount",
            "burned_amount",
            "unit_scale",
            "rebate_rate_bps",
            "rebate_amount",
            "rebate_cap",
            "lock_days",
            "stake_amount",
            "tier1_days",
            "tier2_days",
            "weight_t1",
            "weight_t2",
            "weight_t3",
            "weight_claimed",
            "weighted_stake",
        ):
            _require_u16(getattr(self, name), name=name)
        for name in ("supply_before", "supply_after", "supply_floor"):
            _require_u32(getattr(self, name), name=name)

    def to_dict(self) -> dict[str, int]:
        return {
            "trade_amount": int(self.trade_amount),
            "fee_charged": int(self.fee_charged),
            "buyback_amount": int(self.buyback_amount),
            "burned_amount": int(self.burned_amount),
            "supply_before": int(self.supply_before),
            "supply_after": int(self.supply_after),
            "supply_floor": int(self.supply_floor),
            "unit_scale": int(self.unit_scale),
            "rebate_rate_bps": int(self.rebate_rate_bps),
            "rebate_amount": int(self.rebate_amount),
            "rebate_cap": int(self.rebate_cap),
            "lock_days": int(self.lock_days),
            "stake_amount": int(self.stake_amount),
            "tier1_days": int(self.tier1_days),
            "tier2_days": int(self.tier2_days),
            "weight_t1": int(self.weight_t1),
            "weight_t2": int(self.weight_t2),
            "weight_t3": int(self.weight_t3),
            "weight_claimed": int(self.weight_claimed),
            "weighted_stake": int(self.weighted_stake),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementFeatureExtensionInputs":
        if not isinstance(payload, Mapping):
            raise TypeError("feature extension inputs must be an object")
        return cls(
            trade_amount=_require_int_field(payload, "trade_amount"),
            fee_charged=_require_int_field(payload, "fee_charged"),
            buyback_amount=_require_int_field(payload, "buyback_amount"),
            burned_amount=_require_int_field(payload, "burned_amount"),
            supply_before=_require_int_field(payload, "supply_before"),
            supply_after=_require_int_field(payload, "supply_after"),
            supply_floor=_require_int_field(payload, "supply_floor"),
            unit_scale=_require_int_field(payload, "unit_scale"),
            rebate_rate_bps=_require_int_field(payload, "rebate_rate_bps"),
            rebate_amount=_require_int_field(payload, "rebate_amount"),
            rebate_cap=_require_int_field(payload, "rebate_cap"),
            lock_days=_require_int_field(payload, "lock_days"),
            stake_amount=_require_int_field(payload, "stake_amount"),
            tier1_days=_require_int_field(payload, "tier1_days"),
            tier2_days=_require_int_field(payload, "tier2_days"),
            weight_t1=_require_int_field(payload, "weight_t1"),
            weight_t2=_require_int_field(payload, "weight_t2"),
            weight_t3=_require_int_field(payload, "weight_t3"),
            weight_claimed=_require_int_field(payload, "weight_claimed"),
            weighted_stake=_require_int_field(payload, "weighted_stake"),
        )


@dataclass(frozen=True)
class SettlementFeatureExtensionPacket:
    inputs: SettlementFeatureExtensionInputs
    buyback_floor_step: dict[str, int]
    buyback_floor_fixedpoint_step: dict[str, int]
    rebate_step: dict[str, int]
    lock_weight_step: dict[str, int]
    feature_extension_step: dict[str, int]
    buyback_floor_ok: bool
    buyback_floor_fixedpoint_ok: bool
    rebate_ok: bool
    lock_weight_ok: bool
    feature_extension_ok: bool
    packet_ok: bool
    schema: str = SETTLEMENT_FEATURE_EXTENSION_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_FEATURE_EXTENSION_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.inputs, SettlementFeatureExtensionInputs):
            raise TypeError("inputs must be a SettlementFeatureExtensionInputs")
        for name in (
            "buyback_floor_ok",
            "buyback_floor_fixedpoint_ok",
            "rebate_ok",
            "lock_weight_ok",
            "feature_extension_ok",
            "packet_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "inputs": self.inputs.to_dict(),
            "buyback_floor_step": dict(self.buyback_floor_step),
            "buyback_floor_fixedpoint_step": dict(self.buyback_floor_fixedpoint_step),
            "rebate_step": dict(self.rebate_step),
            "lock_weight_step": dict(self.lock_weight_step),
            "feature_extension_step": dict(self.feature_extension_step),
            "buyback_floor_ok": bool(self.buyback_floor_ok),
            "buyback_floor_fixedpoint_ok": bool(self.buyback_floor_fixedpoint_ok),
            "rebate_ok": bool(self.rebate_ok),
            "lock_weight_ok": bool(self.lock_weight_ok),
            "feature_extension_ok": bool(self.feature_extension_ok),
            "packet_ok": bool(self.packet_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementFeatureExtensionPacket":
        if not isinstance(payload, Mapping):
            raise TypeError("feature extension packet must be an object")
        if str(payload.get("schema", "")) != SETTLEMENT_FEATURE_EXTENSION_PACKET_SCHEMA:
            raise ValueError("feature extension packet schema mismatch")
        try:
            inputs = SettlementFeatureExtensionInputs.from_dict(payload["inputs"])
            return cls(
                inputs=inputs,
                buyback_floor_step=_require_step_dict(
                    payload["buyback_floor_step"],
                    name="buyback_floor_step",
                ),
                buyback_floor_fixedpoint_step=_require_step_dict(
                    payload["buyback_floor_fixedpoint_step"],
                    name="buyback_floor_fixedpoint_step",
                ),
                rebate_step=_require_step_dict(payload["rebate_step"], name="rebate_step"),
                lock_weight_step=_require_step_dict(payload["lock_weight_step"], name="lock_weight_step"),
                feature_extension_step=_require_step_dict(
                    payload["feature_extension_step"],
                    name="feature_extension_step",
                ),
                buyback_floor_ok=_require_bool(payload["buyback_floor_ok"], name="buyback_floor_ok"),
                buyback_floor_fixedpoint_ok=_require_bool(
                    payload["buyback_floor_fixedpoint_ok"],
                    name="buyback_floor_fixedpoint_ok",
                ),
                rebate_ok=_require_bool(payload["rebate_ok"], name="rebate_ok"),
                lock_weight_ok=_require_bool(payload["lock_weight_ok"], name="lock_weight_ok"),
                feature_extension_ok=_require_bool(payload["feature_extension_ok"], name="feature_extension_ok"),
                packet_ok=_require_bool(payload["packet_ok"], name="packet_ok"),
            )
        except KeyError as exc:
            raise ValueError(f"missing feature extension packet field: {exc.args[0]}") from exc


def build_settlement_feature_extension_packet(
    inputs: SettlementFeatureExtensionInputs,
) -> SettlementFeatureExtensionPacket:
    if not isinstance(inputs, SettlementFeatureExtensionInputs):
        raise TypeError("inputs must be a SettlementFeatureExtensionInputs")
    buyback_floor_ok = _buyback_floor_ok(inputs)
    buyback_floor_fixedpoint_ok = buyback_floor_ok and _unit_ok(
        scale=inputs.unit_scale,
        trade_amount=inputs.trade_amount,
        fee_charged=inputs.fee_charged,
        buyback_amount=inputs.buyback_amount,
        burned_amount=inputs.burned_amount,
    )
    rebate_ok = _rebate_ok(inputs)
    lock_weight_ok = _lock_weight_ok(inputs)
    feature_extension_ok = (
        buyback_floor_ok
        and buyback_floor_fixedpoint_ok
        and rebate_ok
        and lock_weight_ok
    )
    buyback_floor_step = build_tdex_buyback_floor_v2_step(
        trade_amount=inputs.trade_amount,
        fee_charged=inputs.fee_charged,
        buyback_amount=inputs.buyback_amount,
        burned_amount=inputs.burned_amount,
        supply_before=inputs.supply_before,
        supply_after=inputs.supply_after,
        supply_floor=inputs.supply_floor,
        fee_rate_ok=int(_fee_rate_ok(inputs.trade_amount, inputs.fee_charged)),
        buyback_share_ok=int(_buyback_share_ok(inputs.fee_charged, inputs.buyback_amount)),
    )
    buyback_floor_fixedpoint_step = build_tdex_buyback_floor_fixedpoint_v2_step(
        trade_amount=inputs.trade_amount,
        fee_charged=inputs.fee_charged,
        buyback_amount=inputs.buyback_amount,
        burned_amount=inputs.burned_amount,
        supply_before=inputs.supply_before,
        supply_after=inputs.supply_after,
        supply_floor=inputs.supply_floor,
        unit_scale=inputs.unit_scale,
        fee_rate_ok=int(_fee_rate_ok(inputs.trade_amount, inputs.fee_charged)),
        buyback_share_ok=int(_buyback_share_ok(inputs.fee_charged, inputs.buyback_amount)),
        unit_ok=int(
            _unit_ok(
                scale=inputs.unit_scale,
                trade_amount=inputs.trade_amount,
                fee_charged=inputs.fee_charged,
                buyback_amount=inputs.buyback_amount,
                burned_amount=inputs.burned_amount,
            )
        ),
    )
    rebate_step = build_tdex_fee_rebate_v1_step(
        trade_fee=inputs.fee_charged,
        rebate_rate_bps=inputs.rebate_rate_bps,
        rebate_amount=inputs.rebate_amount,
        rebate_cap=inputs.rebate_cap,
    )
    lock_weight_step = build_tdex_lock_weight_v1_step(
        lock_days=inputs.lock_days,
        stake_amount=inputs.stake_amount,
        tier1_days=inputs.tier1_days,
        tier2_days=inputs.tier2_days,
        weight_t1=inputs.weight_t1,
        weight_t2=inputs.weight_t2,
        weight_t3=inputs.weight_t3,
        weight_claimed=inputs.weight_claimed,
        weighted_stake=inputs.weighted_stake,
    )
    feature_extension_step = build_settlement_feature_extension_bundle_v1_step(
        buyback_floor_ok=int(buyback_floor_ok),
        buyback_floor_fixedpoint_ok=int(buyback_floor_fixedpoint_ok),
        rebate_ok=int(rebate_ok),
        lock_weight_ok=int(lock_weight_ok),
    )
    return SettlementFeatureExtensionPacket(
        inputs=inputs,
        buyback_floor_step=buyback_floor_step,
        buyback_floor_fixedpoint_step=buyback_floor_fixedpoint_step,
        rebate_step=rebate_step,
        lock_weight_step=lock_weight_step,
        feature_extension_step=feature_extension_step,
        buyback_floor_ok=bool(buyback_floor_ok),
        buyback_floor_fixedpoint_ok=bool(buyback_floor_fixedpoint_ok),
        rebate_ok=bool(rebate_ok),
        lock_weight_ok=bool(lock_weight_ok),
        feature_extension_ok=bool(feature_extension_ok),
        packet_ok=bool(feature_extension_ok),
    )


def verify_settlement_feature_extension_packet_payload(
    *,
    inputs_payload: Mapping[str, Any],
    packet_payload: Mapping[str, Any],
) -> tuple[bool, str | None]:
    try:
        inputs = SettlementFeatureExtensionInputs.from_dict(inputs_payload)
    except _PACKET_DOMAIN_ERRORS as exc:
        return False, str(exc)
    try:
        expected = build_settlement_feature_extension_packet(inputs)
    except _PACKET_DOMAIN_ERRORS as exc:
        return False, str(exc)
    if not isinstance(packet_payload, Mapping):
        return False, "packet must be an object"
    if str(packet_payload.get("schema", "")) != expected.schema:
        return False, "schema mismatch"
    try:
        observed = SettlementFeatureExtensionPacket.from_dict(packet_payload)
    except _PACKET_DOMAIN_ERRORS as exc:
        return False, str(exc)
    if observed.to_dict() != expected.to_dict():
        return False, "settlement feature extension packet mismatch"
    return True, None


def _fee_rate_ok(trade_amount: int, fee_charged: int) -> bool:
    return fee_charged * 10_000 >= trade_amount * 29 and fee_charged * 10_000 <= (trade_amount * 29) + 9_999


def _buyback_share_ok(fee_charged: int, buyback_amount: int) -> bool:
    return buyback_amount * 100 >= fee_charged * 21 and buyback_amount * 100 <= (fee_charged * 21) + 99


def _buyback_floor_ok(inputs: SettlementFeatureExtensionInputs) -> bool:
    return (
        _fee_rate_ok(inputs.trade_amount, inputs.fee_charged)
        and _buyback_share_ok(inputs.fee_charged, inputs.buyback_amount)
        and _burn_floor_ok(
            supply_before=inputs.supply_before,
            supply_after=inputs.supply_after,
            supply_floor=inputs.supply_floor,
            buyback_amount=inputs.buyback_amount,
            burned_amount=inputs.burned_amount,
        )
    )


def _burn_floor_ok(
    *,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    buyback_amount: int,
    burned_amount: int,
) -> bool:
    if supply_before <= supply_floor:
        return burned_amount == 0 and supply_after == supply_before
    return (
        burned_amount == buyback_amount
        and supply_after == supply_before - burned_amount
        and supply_after >= supply_floor
    )


def _unit_ok(
    *,
    scale: int,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
) -> bool:
    return (
        scale != 0
        and trade_amount % scale == 0
        and fee_charged % scale == 0
        and buyback_amount % scale == 0
        and burned_amount % scale == 0
    )


def _rebate_ok(inputs: SettlementFeatureExtensionInputs) -> bool:
    return (
        inputs.rebate_amount * 10_000 >= inputs.fee_charged * inputs.rebate_rate_bps
        and inputs.rebate_amount * 10_000 <= (inputs.fee_charged * inputs.rebate_rate_bps) + 9_999
        and inputs.rebate_amount <= inputs.rebate_cap
        and inputs.rebate_amount <= inputs.fee_charged
    )


def _lock_weight_ok(inputs: SettlementFeatureExtensionInputs) -> bool:
    if not inputs.tier1_days < inputs.tier2_days:
        return False
    if inputs.lock_days < inputs.tier1_days:
        expected_weight = inputs.weight_t1
    elif inputs.lock_days < inputs.tier2_days:
        expected_weight = inputs.weight_t2
    else:
        expected_weight = inputs.weight_t3
    return (
        inputs.weight_claimed == expected_weight
        and inputs.weighted_stake == inputs.stake_amount * inputs.weight_claimed
    )
