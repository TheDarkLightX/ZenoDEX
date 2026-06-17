"""Settlement value-contract handlers for the DEX dispatch registry."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.api_server_dex_dispatch import DexRequestContext, DexResponse, _register

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (ImportError, TypeError, ValueError, ArithmeticError)
"""Expected parse, import, and arithmetic failures at the value-contract boundary."""


@dataclass(frozen=True)
class _SpotValueInputs:
    settlement_obj: dict[str, Any]
    asset_prices_obj: dict[str, Any] | None
    price_packet_obj: dict[str, Any] | None
    price_attestation_obj: dict[str, Any] | None
    consumer_now_epoch: int | None
    max_attestation_age_epochs: int | None
    allowed_signers_obj: dict[str, Any] | None
    contract_obj: dict[str, Any] | None = None


def _bad_request(error: str) -> DexResponse:
    return 400, {"ok": False, "error": error}


def _parse_nonnegative_int(value: object, *, error: str) -> DexResponse | int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        return _bad_request(error)
    return int(value)


def _parse_spot_value_inputs(
    obj: Mapping[str, Any],
    *,
    require_contract: bool,
) -> DexResponse | _SpotValueInputs:
    settlement_obj = obj.get("settlement")
    asset_prices_obj = obj.get("asset_prices")
    price_packet_obj = obj.get("price_packet")
    price_attestation_obj = obj.get("price_attestation")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    contract_obj = obj.get("contract")

    if not isinstance(settlement_obj, dict):
        return _bad_request("bad_settlement")
    if asset_prices_obj is None and price_packet_obj is None and price_attestation_obj is None:
        return _bad_request("missing_price_input")
    if asset_prices_obj is not None and (not isinstance(asset_prices_obj, dict) or not asset_prices_obj):
        return _bad_request("bad_asset_prices")
    if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
        return _bad_request("bad_price_packet")
    if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
        return _bad_request("bad_price_attestation")

    parsed_consumer_now_epoch: int | None = None
    parsed_max_attestation_age_epochs: int | None = None
    if price_attestation_obj is not None:
        parsed_consumer_now_epoch = _parse_nonnegative_int(
            consumer_now_epoch,
            error="bad_consumer_now_epoch",
        )
        if isinstance(parsed_consumer_now_epoch, tuple):
            return parsed_consumer_now_epoch

        parsed_max_attestation_age_epochs = _parse_nonnegative_int(
            max_attestation_age_epochs,
            error="bad_max_attestation_age_epochs",
        )
        if isinstance(parsed_max_attestation_age_epochs, tuple):
            return parsed_max_attestation_age_epochs

        if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
            return _bad_request("bad_allowed_signers")

    if require_contract and not isinstance(contract_obj, dict):
        return _bad_request("bad_contract")

    return _SpotValueInputs(
        settlement_obj=settlement_obj,
        asset_prices_obj=asset_prices_obj if isinstance(asset_prices_obj, dict) else None,
        price_packet_obj=price_packet_obj if isinstance(price_packet_obj, dict) else None,
        price_attestation_obj=price_attestation_obj if isinstance(price_attestation_obj, dict) else None,
        consumer_now_epoch=parsed_consumer_now_epoch,
        max_attestation_age_epochs=parsed_max_attestation_age_epochs,
        allowed_signers_obj=allowed_signers_obj if isinstance(allowed_signers_obj, dict) else None,
        contract_obj=contract_obj if isinstance(contract_obj, dict) else None,
    )


def _parse_asset_prices(asset_prices_obj: Mapping[str, Any] | None) -> dict[str, int]:
    if asset_prices_obj is None:
        raise ValueError("missing asset_prices")
    asset_prices: dict[str, int] = {}
    for raw_asset, raw_price in asset_prices_obj.items():
        asset = str(raw_asset).strip()
        if not asset:
            raise ValueError("asset_prices keys must be non-empty strings")
        if not isinstance(raw_price, int) or isinstance(raw_price, bool) or raw_price < 0:
            raise ValueError(f"asset price must be a non-negative int for {asset}")
        asset_prices[asset] = int(raw_price)
    return asset_prices


def _parse_settlement(settlement_obj: Mapping[str, Any]) -> Any:
    from src.integration.operations import (  # pylint: disable=import-outside-toplevel
        _parse_settlement as parse_settlement,
    )

    return parse_settlement(settlement_obj)


def _build_spot_value_contract(inputs: _SpotValueInputs) -> Any:
    settlement = _parse_settlement(inputs.settlement_obj)
    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceAttestation,
        )
        from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
            build_settlement_spot_value_contract_from_price_attestation,
        )

        return build_settlement_spot_value_contract_from_price_attestation(
            settlement=settlement,
            price_attestation=SettlementSpotPriceAttestation.from_dict(inputs.price_attestation_obj),
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            allowed_signers=inputs.allowed_signers_obj,
        )

    if inputs.price_packet_obj is not None:
        from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPricePacket,
        )
        from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
            build_settlement_spot_value_contract_from_price_packet,
        )

        return build_settlement_spot_value_contract_from_price_packet(
            settlement=settlement,
            price_packet=SettlementSpotPricePacket.from_dict(inputs.price_packet_obj),
        )

    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        build_settlement_spot_value_contract,
    )

    return build_settlement_spot_value_contract(
        settlement=settlement,
        asset_prices=_parse_asset_prices(inputs.asset_prices_obj),
    )


def _verify_spot_value_contract(inputs: _SpotValueInputs) -> tuple[bool, str | None]:
    settlement = _parse_settlement(inputs.settlement_obj)
    if inputs.contract_obj is None:
        raise ValueError("missing contract")

    if inputs.price_attestation_obj is not None:
        from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
            verify_settlement_spot_value_contract_payload_from_price_attestation,
        )

        return verify_settlement_spot_value_contract_payload_from_price_attestation(
            settlement=settlement,
            price_attestation_payload=inputs.price_attestation_obj,
            consumer_now_epoch=int(inputs.consumer_now_epoch),
            max_attestation_age_epochs=int(inputs.max_attestation_age_epochs),
            contract_payload=inputs.contract_obj,
            allowed_signers=inputs.allowed_signers_obj,
        )

    if inputs.price_packet_obj is not None:
        from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
            verify_settlement_spot_value_contract_payload_from_price_packet,
        )

        return verify_settlement_spot_value_contract_payload_from_price_packet(
            settlement=settlement,
            price_packet_payload=inputs.price_packet_obj,
            contract_payload=inputs.contract_obj,
        )

    from src.integration.settlement_value_contract import (  # pylint: disable=import-outside-toplevel
        verify_settlement_spot_value_contract_payload,
    )

    return verify_settlement_spot_value_contract_payload(
        settlement=settlement,
        asset_prices=_parse_asset_prices(inputs.asset_prices_obj),
        contract_payload=inputs.contract_obj,
    )


def _handle_build_settlement_spot_value_contract(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_spot_value_inputs(obj, require_contract=False)
    if isinstance(inputs, tuple):
        return inputs
    try:
        contract = _build_spot_value_contract(inputs)
        return 200, {"ok": True, "contract": contract.to_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "build_settlement_spot_value_contract_error",
            "details": "request failed",
        }


def _handle_verify_settlement_spot_value_contract(
    obj: Mapping[str, Any],
    ctx: DexRequestContext,
) -> DexResponse:
    del ctx
    inputs = _parse_spot_value_inputs(obj, require_contract=True)
    if isinstance(inputs, tuple):
        return inputs
    try:
        ok, err = _verify_spot_value_contract(inputs)
        return 200, {"ok": bool(ok), "error": err}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {
            "ok": False,
            "error": "verify_settlement_spot_value_contract_error",
            "details": "request failed",
        }


_register("/api/dex/build_settlement_spot_value_contract", _handle_build_settlement_spot_value_contract)
_register("/api/dex/verify_settlement_spot_value_contract", _handle_verify_settlement_spot_value_contract)
