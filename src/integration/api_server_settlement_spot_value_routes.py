from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


WriteJson = Callable[[int, object], None]

_BUILD_SPOT_VALUE_CONTRACT_ENDPOINT = "/api/dex/build_settlement_spot_value_contract"
_VERIFY_SPOT_VALUE_CONTRACT_ENDPOINT = "/api/dex/verify_settlement_spot_value_contract"


@dataclass(frozen=True)
class SpotValueRequest:
    settlement: dict[str, object]
    asset_prices: dict[str, object] | None
    price_packet: dict[str, object] | None
    price_attestation: dict[str, object] | None
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers: dict[str, object] | None


class BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _parse_spot_value_request(obj: dict[str, object]) -> SpotValueRequest:
    settlement = _required_dict(obj.get("settlement"), "bad_settlement")
    asset_prices = _optional_dict(obj.get("asset_prices"), "bad_asset_prices", non_empty=True)
    price_packet = _optional_dict(obj.get("price_packet"), "bad_price_packet")
    price_attestation = _optional_dict(obj.get("price_attestation"), "bad_price_attestation")
    _require_price_input(asset_prices, price_packet, price_attestation)
    parsed_consumer_epoch, parsed_max_age, parsed_allowed_signers = _parse_attestation_options(
        obj=obj,
        has_price_attestation=price_attestation is not None,
    )

    return SpotValueRequest(
        settlement=settlement,
        asset_prices=asset_prices,
        price_packet=price_packet,
        price_attestation=price_attestation,
        consumer_now_epoch=parsed_consumer_epoch,
        max_attestation_age_epochs=parsed_max_age,
        allowed_signers=parsed_allowed_signers,
    )


def _required_dict(value: object, error: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise BadRequest(error)
    return value


def _optional_dict(value: object, error: str, *, non_empty: bool = False) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise BadRequest(error)
    if non_empty and not value:
        raise BadRequest(error)
    return value


def _require_price_input(
    asset_prices: dict[str, object] | None,
    price_packet: dict[str, object] | None,
    price_attestation: dict[str, object] | None,
) -> None:
    if asset_prices is None and price_packet is None and price_attestation is None:
        raise BadRequest("missing_price_input")


def _parse_attestation_options(
    *,
    obj: dict[str, object],
    has_price_attestation: bool,
) -> tuple[int | None, int | None, dict[str, object] | None]:
    if not has_price_attestation:
        return None, None, None
    allowed_signers = obj.get("allowed_signers")
    return (
        _non_negative_int(obj.get("consumer_now_epoch"), "bad_consumer_now_epoch"),
        _non_negative_int(obj.get("max_attestation_age_epochs"), "bad_max_attestation_age_epochs"),
        _allowed_signers(allowed_signers),
    )


def _non_negative_int(value: object, error: str) -> int:
    if isinstance(value, bool):
        raise BadRequest(error)
    if not isinstance(value, int):
        raise BadRequest(error)
    if value < 0:
        raise BadRequest(error)
    return int(value)


def _allowed_signers(value: object) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise BadRequest("bad_allowed_signers")
    return value


def _parse_asset_prices(asset_prices_obj: dict[str, object]) -> dict[str, int]:
    asset_prices: dict[str, int] = {}
    for raw_asset, raw_price in asset_prices_obj.items():
        asset = _asset_name(raw_asset)
        asset_prices[asset] = _asset_price(asset, raw_price)
    return asset_prices


def _asset_name(raw_asset: object) -> str:
    asset = str(raw_asset).strip()
    if not asset:
        raise ValueError("asset_prices keys must be non-empty strings")
    return asset


def _asset_price(asset: str, raw_price: object) -> int:
    if isinstance(raw_price, bool):
        raise ValueError(f"asset price must be a non-negative int for {asset}")
    if not isinstance(raw_price, int):
        raise ValueError(f"asset price must be a non-negative int for {asset}")
    if raw_price < 0:
        raise ValueError(f"asset price must be a non-negative int for {asset}")
    return int(raw_price)


def _handle_build_spot_value_contract(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        req = _parse_spot_value_request(obj)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return

    try:
        from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

        settlement = _parse_settlement(req.settlement)
        contract = _build_contract(req, settlement)
        write_json(200, {"ok": True, "contract": contract.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_settlement_spot_value_contract_error", "details": "request failed"},
        )


def _build_contract(req: SpotValueRequest, settlement: object) -> object:
    if req.price_attestation is not None:
        return _build_contract_from_attestation(req, settlement)
    if req.price_packet is not None:
        return _build_contract_from_packet(req, settlement)
    return _build_contract_from_prices(req, settlement)


def _build_contract_from_attestation(req: SpotValueRequest, settlement: object) -> object:
    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPriceAttestation,
    )
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        build_settlement_spot_value_contract_from_price_attestation,
    )

    price_attestation = SettlementSpotPriceAttestation.from_dict(req.price_attestation)
    return build_settlement_spot_value_contract_from_price_attestation(
        settlement=settlement,
        price_attestation=price_attestation,
        consumer_now_epoch=int(req.consumer_now_epoch),
        max_attestation_age_epochs=int(req.max_attestation_age_epochs),
        allowed_signers=req.allowed_signers,
    )


def _build_contract_from_packet(req: SpotValueRequest, settlement: object) -> object:
    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        build_settlement_spot_value_contract_from_price_packet,
    )

    price_packet = SettlementSpotPricePacket.from_dict(req.price_packet)
    return build_settlement_spot_value_contract_from_price_packet(
        settlement=settlement,
        price_packet=price_packet,
    )


def _build_contract_from_prices(req: SpotValueRequest, settlement: object) -> object:
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        build_settlement_spot_value_contract,
    )

    return build_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=_parse_asset_prices(req.asset_prices or {}),
    )


def _handle_verify_spot_value_contract(obj: dict[str, object], write_json: WriteJson) -> None:
    try:
        req = _parse_spot_value_request(obj)
        contract = obj.get("contract")
        if not isinstance(contract, dict):
            raise BadRequest("bad_contract")
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return

    try:
        from src.integration.operations import _parse_settlement  # pylint: disable=import-outside-toplevel

        settlement = _parse_settlement(req.settlement)
        ok, err = _verify_contract(req, settlement, contract)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_settlement_spot_value_contract_error", "details": "request failed"},
        )


def _verify_contract(
    req: SpotValueRequest,
    settlement: object,
    contract: dict[str, object],
) -> tuple[bool, str | None]:
    if req.price_attestation is not None:
        return _verify_contract_from_attestation(req, settlement, contract)
    if req.price_packet is not None:
        return _verify_contract_from_packet(req, settlement, contract)
    return _verify_contract_from_prices(req, settlement, contract)


def _verify_contract_from_attestation(
    req: SpotValueRequest,
    settlement: object,
    contract: dict[str, object],
) -> tuple[bool, str | None]:
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        verify_settlement_spot_value_contract_payload_from_price_attestation,
    )

    return verify_settlement_spot_value_contract_payload_from_price_attestation(
        settlement=settlement,
        price_attestation_payload=req.price_attestation,
        consumer_now_epoch=int(req.consumer_now_epoch),
        max_attestation_age_epochs=int(req.max_attestation_age_epochs),
        contract_payload=contract,
        allowed_signers=req.allowed_signers,
    )


def _verify_contract_from_packet(
    req: SpotValueRequest,
    settlement: object,
    contract: dict[str, object],
) -> tuple[bool, str | None]:
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        verify_settlement_spot_value_contract_payload_from_price_packet,
    )

    return verify_settlement_spot_value_contract_payload_from_price_packet(
        settlement=settlement,
        price_packet_payload=req.price_packet,
        contract_payload=contract,
    )


def _verify_contract_from_prices(
    req: SpotValueRequest,
    settlement: object,
    contract: dict[str, object],
) -> tuple[bool, str | None]:
    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        verify_settlement_spot_value_contract_payload,
    )

    return verify_settlement_spot_value_contract_payload(
        settlement=settlement,
        asset_prices=_parse_asset_prices(req.asset_prices or {}),
        contract_payload=contract,
    )


def maybe_handle_settlement_spot_value_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_SPOT_VALUE_CONTRACT_ENDPOINT:
        _handle_build_spot_value_contract(obj, write_json)
        return True
    if path == _VERIFY_SPOT_VALUE_CONTRACT_ENDPOINT:
        _handle_verify_spot_value_contract(obj, write_json)
        return True
    return False
