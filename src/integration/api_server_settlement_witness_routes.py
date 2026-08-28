from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

from src.integration.api_server_settlement_parsers import (
    _parse_balance_table_payload,
    _parse_lp_balances_payload,
    _parse_lp_unit_values_payload,
)


@dataclass(frozen=True)
class _SettlementWitnessRequest:
    intents_obj: object
    balances_obj: object
    lp_balances_obj: object
    block_timestamp: object
    settlement_obj: object
    proof_flags_obj: object
    price_history_obj: object
    feature_extension_inputs_obj: object
    price_packet_obj: object
    price_attestation_obj: object
    pool_snapshots_obj: object
    lp_unit_values_obj: object
    consumer_now_epoch: object
    max_attestation_age_epochs: object
    allowed_signers_obj: object
    settlement_validation: str
    swap_ordering: str
    quote_bindings_validated: object
    protocol_fee_share_bps: object
    protocol_fee_recipient_pubkey: object
    packet_obj: object


@dataclass(frozen=True)
class _SettlementWitnessContext:
    intents: Any
    balances: Any
    lp_balances: Any
    pools_by_id: dict[str, Any]
    settlement: Any
    certificate_inputs: Any


def _bad_request(write_json: Callable[[int, object], None], error: str) -> None:
    write_json(400, {"ok": False, "error": error})


def _extract_request(obj: dict[str, object]) -> _SettlementWitnessRequest:
    return _SettlementWitnessRequest(
        intents_obj=obj.get("intents"),
        balances_obj=obj.get("balances"),
        lp_balances_obj=obj.get("lp_balances"),
        block_timestamp=obj.get("block_timestamp"),
        settlement_obj=obj.get("settlement"),
        proof_flags_obj=obj.get("proof_flags"),
        price_history_obj=obj.get("price_history"),
        feature_extension_inputs_obj=obj.get("feature_extension_inputs"),
        price_packet_obj=obj.get("price_packet"),
        price_attestation_obj=obj.get("price_attestation"),
        pool_snapshots_obj=obj.get("pool_snapshots"),
        lp_unit_values_obj=obj.get("lp_unit_values"),
        consumer_now_epoch=obj.get("consumer_now_epoch"),
        max_attestation_age_epochs=obj.get("max_attestation_age_epochs"),
        allowed_signers_obj=obj.get("allowed_signers"),
        settlement_validation=str(obj.get("settlement_validation", "strong_replay")),
        swap_ordering=str(obj.get("swap_ordering", "greedy_ab_refined")),
        quote_bindings_validated=obj.get("quote_bindings_validated", False),
        protocol_fee_share_bps=obj.get("protocol_fee_share_bps", 0),
        protocol_fee_recipient_pubkey=obj.get("protocol_fee_recipient_pubkey"),
        packet_obj=obj.get("packet"),
    )


def _validate_core_inputs(
    request: _SettlementWitnessRequest,
    write_json: Callable[[int, object], None],
) -> bool:
    if not isinstance(request.intents_obj, list) or not request.intents_obj:
        _bad_request(write_json, "bad_intents")
        return False
    if not isinstance(request.balances_obj, list):
        _bad_request(write_json, "bad_balances")
        return False
    if request.lp_balances_obj is not None and not isinstance(request.lp_balances_obj, list):
        _bad_request(write_json, "bad_lp_balances")
        return False
    if not isinstance(request.block_timestamp, int) or isinstance(request.block_timestamp, bool) or request.block_timestamp < 0:
        _bad_request(write_json, "bad_block_timestamp")
        return False
    if not isinstance(request.settlement_obj, dict):
        _bad_request(write_json, "bad_settlement")
        return False
    if not isinstance(request.quote_bindings_validated, bool):
        _bad_request(write_json, "bad_quote_bindings_validated")
        return False
    if (
        not isinstance(request.protocol_fee_share_bps, int)
        or isinstance(request.protocol_fee_share_bps, bool)
        or not 0 <= request.protocol_fee_share_bps <= 10_000
    ):
        _bad_request(write_json, "bad_protocol_fee_share_bps")
        return False
    if request.protocol_fee_recipient_pubkey is not None and (
        not isinstance(request.protocol_fee_recipient_pubkey, str)
        or not request.protocol_fee_recipient_pubkey
    ):
        _bad_request(write_json, "bad_protocol_fee_recipient_pubkey")
        return False
    if request.protocol_fee_share_bps > 0 and request.protocol_fee_recipient_pubkey is None:
        _bad_request(write_json, "missing_protocol_fee_recipient_pubkey")
        return False
    return True


def _require_protocol_fee_policy(
    request: _SettlementWitnessRequest,
) -> tuple[int, str | None]:
    share = request.protocol_fee_share_bps
    recipient = request.protocol_fee_recipient_pubkey
    if (
        not isinstance(share, int)
        or isinstance(share, bool)
        or not 0 <= share <= 10_000
    ):
        raise ValueError("bad_protocol_fee_share_bps")
    if recipient is not None and (
        not isinstance(recipient, str) or not recipient
    ):
        raise ValueError("bad_protocol_fee_recipient_pubkey")
    if share > 0 and recipient is None:
        raise ValueError("missing_protocol_fee_recipient_pubkey")
    return share, recipient


def _validate_price_inputs(
    request: _SettlementWitnessRequest,
    write_json: Callable[[int, object], None],
) -> bool:
    if request.price_packet_obj is None and request.price_attestation_obj is None:
        _bad_request(write_json, "missing_price_input")
        return False
    if request.price_packet_obj is not None and not isinstance(request.price_packet_obj, dict):
        _bad_request(write_json, "bad_price_packet")
        return False
    if request.price_attestation_obj is not None and not isinstance(request.price_attestation_obj, dict):
        _bad_request(write_json, "bad_price_attestation")
        return False
    if request.pool_snapshots_obj is not None and (
        not isinstance(request.pool_snapshots_obj, list) or not request.pool_snapshots_obj
    ):
        _bad_request(write_json, "bad_pool_snapshots")
        return False
    if request.lp_unit_values_obj is not None and (
        not isinstance(request.lp_unit_values_obj, dict) or not request.lp_unit_values_obj
    ):
        _bad_request(write_json, "bad_lp_unit_values")
        return False
    if request.pool_snapshots_obj is not None and request.lp_unit_values_obj is not None:
        _bad_request(write_json, "conflicting_value_mode_inputs")
        return False
    return True


def _validate_attestation_inputs(
    request: _SettlementWitnessRequest,
    write_json: Callable[[int, object], None],
    *,
    require_packet: bool,
) -> bool:
    if require_packet and not isinstance(request.packet_obj, dict):
        _bad_request(write_json, "bad_packet")
        return False
    if request.price_attestation_obj is None:
        return True
    if (
        not isinstance(request.consumer_now_epoch, int)
        or isinstance(request.consumer_now_epoch, bool)
        or request.consumer_now_epoch < 0
    ):
        _bad_request(write_json, "bad_consumer_now_epoch")
        return False
    if (
        not isinstance(request.max_attestation_age_epochs, int)
        or isinstance(request.max_attestation_age_epochs, bool)
        or request.max_attestation_age_epochs < 0
    ):
        _bad_request(write_json, "bad_max_attestation_age_epochs")
        return False
    if request.allowed_signers_obj is not None and not isinstance(request.allowed_signers_obj, dict):
        _bad_request(write_json, "bad_allowed_signers")
        return False
    return True


def _build_attested_certificate_inputs(
    *,
    request: _SettlementWitnessRequest,
    proof_flags: Any,
    price_history: tuple[int, int, int],
    feature_extension_inputs: Any,
    lp_unit_values: dict[str, int] | None,
    pool_snapshots: tuple[Any, ...] | None,
) -> Any:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        SettlementEndToEndCertificateInputs,
    )
    from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPriceAttestation,
    )

    return SettlementEndToEndCertificateInputs(
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_extension_inputs,
        price_attestation=SettlementSpotPriceAttestation.from_dict(request.price_attestation_obj),
        consumer_now_epoch=int(request.consumer_now_epoch),
        max_attestation_age_epochs=int(request.max_attestation_age_epochs),
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
        allowed_signers=request.allowed_signers_obj,
    )


def _build_packet_certificate_inputs(
    *,
    request: _SettlementWitnessRequest,
    proof_flags: Any,
    price_history: tuple[int, int, int],
    feature_extension_inputs: Any,
    lp_unit_values: dict[str, int] | None,
    pool_snapshots: tuple[Any, ...] | None,
) -> Any:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        SettlementEndToEndCertificateInputs,
    )
    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )

    return SettlementEndToEndCertificateInputs(
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_extension_inputs,
        price_packet=SettlementSpotPricePacket.from_dict(request.price_packet_obj),
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
    )


def _build_certificate_inputs(
    *,
    request: _SettlementWitnessRequest,
    parse_settlement_proof_flags_payload: Callable[[object], Any],
    parse_price_history_payload: Callable[[object], tuple[int, int, int]],
    parse_settlement_feature_extension_inputs_payload: Callable[[object], Any],
) -> Any:
    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        _pool_from_dict,
    )

    proof_flags = parse_settlement_proof_flags_payload(request.proof_flags_obj)
    price_history = parse_price_history_payload(request.price_history_obj)
    feature_extension_inputs = parse_settlement_feature_extension_inputs_payload(request.feature_extension_inputs_obj)
    pool_snapshots = (
        None
        if request.pool_snapshots_obj is None
        else tuple(_pool_from_dict(snapshot) for snapshot in request.pool_snapshots_obj)
    )
    lp_unit_values = _parse_lp_unit_values_payload(request.lp_unit_values_obj)
    builder = _build_attested_certificate_inputs if request.price_attestation_obj is not None else _build_packet_certificate_inputs
    return builder(
        request=request,
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_extension_inputs,
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
    )


def _load_request_context(
    *,
    request: _SettlementWitnessRequest,
    parse_pools: Callable[[], dict[str, Any]],
    parse_settlement_proof_flags_payload: Callable[[object], Any],
    parse_price_history_payload: Callable[[object], tuple[int, int, int]],
    parse_settlement_feature_extension_inputs_payload: Callable[[object], Any],
) -> _SettlementWitnessContext:
    from src.integration.operations import (  # pylint: disable=import-outside-toplevel
        _parse_settlement,
        parse_intents,
    )

    return _SettlementWitnessContext(
        intents=parse_intents({"2": request.intents_obj}),
        balances=_parse_balance_table_payload(request.balances_obj),
        lp_balances=_parse_lp_balances_payload(request.lp_balances_obj),
        pools_by_id=parse_pools(),
        settlement=_parse_settlement(request.settlement_obj),
        certificate_inputs=_build_certificate_inputs(
            request=request,
            parse_settlement_proof_flags_payload=parse_settlement_proof_flags_payload,
            parse_price_history_payload=parse_price_history_payload,
            parse_settlement_feature_extension_inputs_payload=parse_settlement_feature_extension_inputs_payload,
        ),
    )


def _handle_build_request(
    *,
    request: _SettlementWitnessRequest,
    context: _SettlementWitnessContext,
    write_json: Callable[[int, object], None],
) -> None:
    from src.integration.settlement_witness_lifecycle import (  # pylint: disable=import-outside-toplevel
        build_settlement_witness_lifecycle_packet,
    )

    protocol_fee_share_bps, protocol_fee_recipient = _require_protocol_fee_policy(request)
    packet = build_settlement_witness_lifecycle_packet(
        intents=context.intents,
        settlement=context.settlement,
        balances=context.balances,
        pools=context.pools_by_id,
        lp_balances=context.lp_balances,
        block_timestamp=int(request.block_timestamp),
        settlement_end_to_end_certificate_inputs=context.certificate_inputs,
        settlement_validation=request.settlement_validation,
        swap_ordering=request.swap_ordering,
        quote_bindings_validated=bool(request.quote_bindings_validated),
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient,
    )
    write_json(200, {"ok": True, "packet": packet.to_dict()})


def _handle_verify_request(
    *,
    request: _SettlementWitnessRequest,
    context: _SettlementWitnessContext,
    write_json: Callable[[int, object], None],
) -> None:
    from src.integration.settlement_witness_lifecycle import (  # pylint: disable=import-outside-toplevel
        verify_settlement_witness_lifecycle_packet_payload,
    )

    protocol_fee_share_bps, protocol_fee_recipient = _require_protocol_fee_policy(request)
    ok, err = verify_settlement_witness_lifecycle_packet_payload(
        intents=context.intents,
        settlement=context.settlement,
        balances=context.balances,
        pools=context.pools_by_id,
        lp_balances=context.lp_balances,
        block_timestamp=int(request.block_timestamp),
        settlement_end_to_end_certificate_inputs=context.certificate_inputs,
        packet_payload=request.packet_obj,
        settlement_validation=request.settlement_validation,
        swap_ordering=request.swap_ordering,
        quote_bindings_validated=bool(request.quote_bindings_validated),
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient,
    )
    write_json(200, {"ok": bool(ok), "error": err})


def maybe_handle_settlement_witness_lifecycle_route(
    *,
    path: str,
    obj: dict[str, object],
    write_json: Callable[[int, object], None],
    parse_pools: Callable[[], dict[str, Any]],
    parse_settlement_proof_flags_payload: Callable[[object], Any],
    parse_price_history_payload: Callable[[object], tuple[int, int, int]],
    parse_settlement_feature_extension_inputs_payload: Callable[[object], Any],
) -> bool:
    if path not in {
        "/api/dex/build_settlement_witness_lifecycle_packet",
        "/api/dex/verify_settlement_witness_lifecycle_packet",
    }:
        return False

    require_packet = path == "/api/dex/verify_settlement_witness_lifecycle_packet"
    request = _extract_request(obj)
    if not _validate_core_inputs(request, write_json):
        return True
    if not _validate_price_inputs(request, write_json):
        return True
    if not _validate_attestation_inputs(request, write_json, require_packet=require_packet):
        return True

    try:
        context = _load_request_context(
            request=request,
            parse_pools=parse_pools,
            parse_settlement_proof_flags_payload=parse_settlement_proof_flags_payload,
            parse_price_history_payload=parse_price_history_payload,
            parse_settlement_feature_extension_inputs_payload=parse_settlement_feature_extension_inputs_payload,
        )
        handler = _handle_verify_request if require_packet else _handle_build_request
        handler(request=request, context=context, write_json=write_json)
        return True
    except Exception as exc:
        error = (
            "verify_settlement_witness_lifecycle_packet_error"
            if require_packet
            else "build_settlement_witness_lifecycle_packet_error"
        )
        write_json(400, {"ok": False, "error": error, "details": str(exc)[:200]})
        return True
