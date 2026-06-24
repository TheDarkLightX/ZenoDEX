from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Mapping

from src.core.settlement import Settlement

from .settlement_lp_value_contract import (
    SettlementLPValueContract,
    build_settlement_lp_value_contract,
)
from .settlement_price_provenance import (
    SettlementSpotPricePacket,
    asset_prices_from_spot_price_packet,
    verify_settlement_spot_price_packet,
)
from .settlement_value_contract import (
    SettlementSpotValueContract,
    build_settlement_spot_value_contract,
)

if TYPE_CHECKING:
    from .settlement_price_attestation import SettlementSpotPriceAttestation


SETTLEMENT_VALUE_PACKET_SCHEMA = "zenodex/settlement-value-packet/v1"


def _safe_payload_validation_error(exc: Exception) -> str:
    detail = " ".join(str(exc).split())
    return detail[:200] or type(exc).__name__


@dataclass(frozen=True)
class SettlementValuePacket:
    mode: str
    price_input_kind: str
    price_packet: SettlementSpotPricePacket
    price_attestation: SettlementSpotPriceAttestation | None
    spot_value_contract: SettlementSpotValueContract | None
    lp_value_contract: SettlementLPValueContract | None
    price_provenance_ok: bool
    attestation_ok: bool
    asset_conservation_ok: bool
    lp_liability_balanced_ok: bool
    value_conservation_ok: bool
    packet_ok: bool
    schema: str = SETTLEMENT_VALUE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != SETTLEMENT_VALUE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.mode not in {"spot_only", "lp_aware"}:
            raise ValueError("mode must be 'spot_only' or 'lp_aware'")
        if self.price_input_kind not in {"packet", "attestation"}:
            raise ValueError("price_input_kind must be 'packet' or 'attestation'")
        if not isinstance(self.price_packet, SettlementSpotPricePacket):
            raise TypeError("price_packet must be a SettlementSpotPricePacket")
        if self.price_input_kind == "packet":
            if self.price_attestation is not None:
                raise ValueError("price_attestation must be None for packet mode")
        else:
            if self.price_attestation is None:
                raise ValueError("price_attestation must be present for attestation mode")
        if self.mode == "spot_only":
            if self.spot_value_contract is None or self.lp_value_contract is not None:
                raise ValueError("spot_only mode requires only spot_value_contract")
        else:
            if self.lp_value_contract is None or self.spot_value_contract is not None:
                raise ValueError("lp_aware mode requires only lp_value_contract")
        for name in (
            "price_provenance_ok",
            "attestation_ok",
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
            "mode": self.mode,
            "price_input_kind": self.price_input_kind,
            "price_packet": self.price_packet.to_dict(),
            "price_attestation": None if self.price_attestation is None else self.price_attestation.to_dict(),
            "spot_value_contract": None if self.spot_value_contract is None else self.spot_value_contract.to_dict(),
            "lp_value_contract": None if self.lp_value_contract is None else self.lp_value_contract.to_dict(),
            "price_provenance_ok": bool(self.price_provenance_ok),
            "attestation_ok": bool(self.attestation_ok),
            "asset_conservation_ok": bool(self.asset_conservation_ok),
            "lp_liability_balanced_ok": bool(self.lp_liability_balanced_ok),
            "value_conservation_ok": bool(self.value_conservation_ok),
            "packet_ok": bool(self.packet_ok),
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "SettlementValuePacket":
        if not isinstance(payload, Mapping):
            raise ValueError("packet must be an object")
        from .settlement_price_attestation import SettlementSpotPriceAttestation

        price_packet_payload = payload.get("price_packet")
        if not isinstance(price_packet_payload, Mapping):
            raise ValueError("packet.price_packet must be an object")
        price_attestation_payload = payload.get("price_attestation")
        spot_contract_payload = payload.get("spot_value_contract")
        lp_contract_payload = payload.get("lp_value_contract")
        return cls(
            schema=str(payload.get("schema", "")),
            mode=str(payload.get("mode", "")),
            price_input_kind=str(payload.get("price_input_kind", "")),
            price_packet=SettlementSpotPricePacket.from_dict(price_packet_payload),
            price_attestation=(
                None
                if price_attestation_payload is None
                else SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
            ),
            spot_value_contract=(
                None if spot_contract_payload is None else SettlementSpotValueContract.from_dict(spot_contract_payload)
            ),
            lp_value_contract=(
                None if lp_contract_payload is None else SettlementLPValueContract.from_dict(lp_contract_payload)
            ),
            price_provenance_ok=bool(payload.get("price_provenance_ok", False)),
            attestation_ok=bool(payload.get("attestation_ok", False)),
            asset_conservation_ok=bool(payload.get("asset_conservation_ok", False)),
            lp_liability_balanced_ok=bool(payload.get("lp_liability_balanced_ok", False)),
            value_conservation_ok=bool(payload.get("value_conservation_ok", False)),
            packet_ok=bool(payload.get("packet_ok", False)),
        )


def build_settlement_value_packet_from_price_packet(
    *,
    settlement: Settlement,
    price_packet: SettlementSpotPricePacket,
    lp_unit_values: Mapping[str, int] | None = None,
) -> SettlementValuePacket:
    ok, err = verify_settlement_spot_price_packet(packet=price_packet)
    if not ok:
        raise ValueError(f"invalid settlement spot price packet: {err}")
    if not price_packet.provenance_ok:
        raise ValueError("settlement spot price packet is not provenance_ok")
    if lp_unit_values is None:
        contract = build_settlement_spot_value_contract(
            settlement=settlement,
            asset_prices=asset_prices_from_spot_price_packet(price_packet),
        )
        return SettlementValuePacket(
            mode="spot_only",
            price_input_kind="packet",
            price_packet=price_packet,
            price_attestation=None,
            spot_value_contract=contract,
            lp_value_contract=None,
            price_provenance_ok=bool(price_packet.provenance_ok),
            attestation_ok=True,
            asset_conservation_ok=bool(contract.asset_conservation_ok),
            lp_liability_balanced_ok=True,
            value_conservation_ok=bool(contract.value_conservation_ok),
            packet_ok=bool(price_packet.provenance_ok and contract.asset_conservation_ok and contract.value_conservation_ok),
        )
    contract_lp = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_packet),
        lp_unit_values=lp_unit_values,
    )
    return SettlementValuePacket(
        mode="lp_aware",
        price_input_kind="packet",
        price_packet=price_packet,
        price_attestation=None,
        spot_value_contract=None,
        lp_value_contract=contract_lp,
        price_provenance_ok=bool(price_packet.provenance_ok),
        attestation_ok=True,
        asset_conservation_ok=bool(contract_lp.asset_conservation_ok),
        lp_liability_balanced_ok=bool(contract_lp.lp_liability_balanced_ok),
        value_conservation_ok=bool(contract_lp.value_conservation_ok),
        packet_ok=bool(
            price_packet.provenance_ok
            and contract_lp.asset_conservation_ok
            and contract_lp.lp_liability_balanced_ok
            and contract_lp.value_conservation_ok
        ),
    )


def build_settlement_value_packet_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation: SettlementSpotPriceAttestation,
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    lp_unit_values: Mapping[str, int] | None = None,
    allowed_signers: Mapping[str, tuple[str, ...] | list[str]] | None = None,
) -> SettlementValuePacket:
    from .settlement_price_attestation import verify_settlement_spot_price_attestation

    ok, err = verify_settlement_spot_price_attestation(
        attestation=price_attestation,
        consumer_now_epoch=consumer_now_epoch,
        max_attestation_age_epochs=max_attestation_age_epochs,
        allowed_signers=allowed_signers,
    )
    if not ok:
        raise ValueError(f"invalid settlement spot price attestation: {err}")
    if lp_unit_values is None:
        contract = build_settlement_spot_value_contract(
            settlement=settlement,
            asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
        )
        return SettlementValuePacket(
            mode="spot_only",
            price_input_kind="attestation",
            price_packet=price_attestation.packet,
            price_attestation=price_attestation,
            spot_value_contract=contract,
            lp_value_contract=None,
            price_provenance_ok=bool(price_attestation.packet.provenance_ok),
            attestation_ok=True,
            asset_conservation_ok=bool(contract.asset_conservation_ok),
            lp_liability_balanced_ok=True,
            value_conservation_ok=bool(contract.value_conservation_ok),
            packet_ok=bool(
                price_attestation.packet.provenance_ok
                and contract.asset_conservation_ok
                and contract.value_conservation_ok
            ),
        )
    contract_lp = build_settlement_lp_value_contract(
        settlement=settlement,
        asset_prices=asset_prices_from_spot_price_packet(price_attestation.packet),
        lp_unit_values=lp_unit_values,
    )
    return SettlementValuePacket(
        mode="lp_aware",
        price_input_kind="attestation",
        price_packet=price_attestation.packet,
        price_attestation=price_attestation,
        spot_value_contract=None,
        lp_value_contract=contract_lp,
        price_provenance_ok=bool(price_attestation.packet.provenance_ok),
        attestation_ok=True,
        asset_conservation_ok=bool(contract_lp.asset_conservation_ok),
        lp_liability_balanced_ok=bool(contract_lp.lp_liability_balanced_ok),
        value_conservation_ok=bool(contract_lp.value_conservation_ok),
        packet_ok=bool(
            price_attestation.packet.provenance_ok
            and contract_lp.asset_conservation_ok
            and contract_lp.lp_liability_balanced_ok
            and contract_lp.value_conservation_ok
        ),
    )


def verify_settlement_value_packet_payload_from_price_packet(
    *,
    settlement: Settlement,
    price_packet_payload: Mapping[str, Any],
    packet_payload: Mapping[str, Any],
    lp_unit_values: Mapping[str, int] | None = None,
) -> tuple[bool, str | None]:
    try:
        price_packet = SettlementSpotPricePacket.from_dict(price_packet_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    try:
        expected = build_settlement_value_packet_from_price_packet(
            settlement=settlement,
            price_packet=price_packet,
            lp_unit_values=lp_unit_values,
        )
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    try:
        packet = SettlementValuePacket.from_dict(packet_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    if packet.schema != expected.schema:
        return False, "schema mismatch"
    if packet != expected:
        return False, "settlement value packet mismatch"
    return True, None


def verify_settlement_value_packet_payload_from_price_attestation(
    *,
    settlement: Settlement,
    price_attestation_payload: Mapping[str, Any],
    consumer_now_epoch: int,
    max_attestation_age_epochs: int,
    packet_payload: Mapping[str, Any],
    lp_unit_values: Mapping[str, int] | None = None,
    allowed_signers: Mapping[str, tuple[str, ...] | list[str]] | None = None,
) -> tuple[bool, str | None]:
    from .settlement_price_attestation import SettlementSpotPriceAttestation

    try:
        price_attestation = SettlementSpotPriceAttestation.from_dict(price_attestation_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    try:
        expected = build_settlement_value_packet_from_price_attestation(
            settlement=settlement,
            price_attestation=price_attestation,
            consumer_now_epoch=consumer_now_epoch,
            max_attestation_age_epochs=max_attestation_age_epochs,
            lp_unit_values=lp_unit_values,
            allowed_signers=allowed_signers,
        )
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    try:
        packet = SettlementValuePacket.from_dict(packet_payload)
    except (TypeError, ValueError, KeyError) as exc:
        return False, _safe_payload_validation_error(exc)
    if packet.schema != expected.schema:
        return False, "schema mismatch"
    if packet != expected:
        return False, "settlement value packet mismatch"
    return True, None
