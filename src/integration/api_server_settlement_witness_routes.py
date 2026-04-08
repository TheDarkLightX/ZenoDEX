from __future__ import annotations

from typing import Any, Callable


def _parse_balance_table_payload(payload: object) -> Any:
    from src.state import BalanceTable  # pylint: disable=import-outside-toplevel

    if not isinstance(payload, list):
        raise ValueError("balances must be a list")
    balances = BalanceTable()
    seen: set[tuple[str, str]] = set()
    for entry in payload:
        if not isinstance(entry, dict):
            raise ValueError("balances entries must be objects")
        pubkey = str(entry.get("pubkey", "")).strip()
        asset = str(entry.get("asset", "")).strip()
        amount = entry.get("amount")
        if not pubkey:
            raise ValueError("balance pubkey must be a non-empty string")
        if not asset:
            raise ValueError("balance asset must be a non-empty string")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("balance amount must be a non-negative int")
        key = (pubkey, asset)
        if key in seen:
            raise ValueError("duplicate balance entry")
        seen.add(key)
        balances.set(pubkey, asset, int(amount))
    return balances


def _parse_lp_balances_payload(payload: object) -> Any:
    from src.state import LPTable  # pylint: disable=import-outside-toplevel

    if payload is None:
        return LPTable()
    if not isinstance(payload, list):
        raise ValueError("lp_balances must be a list")
    lp_balances = LPTable()
    seen: set[tuple[str, str]] = set()
    for entry in payload:
        if not isinstance(entry, dict):
            raise ValueError("lp_balances entries must be objects")
        pubkey = str(entry.get("pubkey", "")).strip()
        pool_id = str(entry.get("pool_id", "")).strip()
        amount = entry.get("amount")
        if not pubkey:
            raise ValueError("lp balance pubkey must be a non-empty string")
        if not pool_id:
            raise ValueError("lp balance pool_id must be a non-empty string")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("lp balance amount must be a non-negative int")
        key = (pubkey, pool_id)
        if key in seen:
            raise ValueError("duplicate lp balance entry")
        seen.add(key)
        lp_balances.set(pubkey, pool_id, int(amount))
    return lp_balances


def _parse_lp_unit_values_payload(payload: object) -> dict[str, int] | None:
    if payload is None:
        return None
    if not isinstance(payload, dict) or not payload:
        raise ValueError("bad_lp_unit_values")
    lp_unit_values: dict[str, int] = {}
    for raw_pool_id, raw_unit_value in payload.items():
        pool_id = str(raw_pool_id).strip()
        if not pool_id:
            raise ValueError("lp_unit_values keys must be non-empty strings")
        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
        lp_unit_values[pool_id] = int(raw_unit_value)
    return lp_unit_values


def _build_certificate_inputs(
    *,
    proof_flags_obj: object,
    price_history_obj: object,
    feature_extension_inputs_obj: object,
    price_packet_obj: object,
    price_attestation_obj: object,
    pool_snapshots_obj: object,
    lp_unit_values_obj: object,
    consumer_now_epoch: object,
    max_attestation_age_epochs: object,
    allowed_signers_obj: object,
    parse_settlement_proof_flags_payload: Callable[[object], Any],
    parse_price_history_payload: Callable[[object], tuple[int, int, int]],
    parse_settlement_feature_extension_inputs_payload: Callable[[object], Any],
) -> Any:
    from src.integration.settlement_end_to_end_certificate_packet import (  # pylint: disable=import-outside-toplevel
        SettlementEndToEndCertificateInputs,
    )
    from src.integration.settlement_endogenous_lp_value_packet import (  # pylint: disable=import-outside-toplevel
        _pool_from_dict,
    )

    proof_flags = parse_settlement_proof_flags_payload(proof_flags_obj)
    price_history = parse_price_history_payload(price_history_obj)
    feature_extension_inputs = parse_settlement_feature_extension_inputs_payload(feature_extension_inputs_obj)
    pool_snapshots = None if pool_snapshots_obj is None else tuple(_pool_from_dict(snapshot) for snapshot in pool_snapshots_obj)
    lp_unit_values = _parse_lp_unit_values_payload(lp_unit_values_obj)

    if price_attestation_obj is not None:
        from src.integration.settlement_price_attestation import (  # pylint: disable=import-outside-toplevel
            SettlementSpotPriceAttestation,
        )

        return SettlementEndToEndCertificateInputs(
            proof_flags=proof_flags,
            price_history=price_history,
            feature_extension_inputs=feature_extension_inputs,
            price_attestation=SettlementSpotPriceAttestation.from_dict(price_attestation_obj),
            consumer_now_epoch=int(consumer_now_epoch),
            max_attestation_age_epochs=int(max_attestation_age_epochs),
            lp_unit_values=lp_unit_values,
            pool_snapshots=pool_snapshots,
            allowed_signers=allowed_signers_obj,
        )

    from src.integration.settlement_price_provenance import (  # pylint: disable=import-outside-toplevel
        SettlementSpotPricePacket,
    )

    return SettlementEndToEndCertificateInputs(
        proof_flags=proof_flags,
        price_history=price_history,
        feature_extension_inputs=feature_extension_inputs,
        price_packet=SettlementSpotPricePacket.from_dict(price_packet_obj),
        lp_unit_values=lp_unit_values,
        pool_snapshots=pool_snapshots,
    )


def _validate_common_request(
    *,
    obj: dict[str, object],
    write_json: Callable[[int, object], None],
    require_packet: bool,
) -> dict[str, object] | None:
    intents_obj = obj.get("intents")
    balances_obj = obj.get("balances")
    lp_balances_obj = obj.get("lp_balances")
    block_timestamp = obj.get("block_timestamp")
    settlement_obj = obj.get("settlement")
    proof_flags_obj = obj.get("proof_flags")
    price_history_obj = obj.get("price_history")
    feature_extension_inputs_obj = obj.get("feature_extension_inputs")
    price_packet_obj = obj.get("price_packet")
    price_attestation_obj = obj.get("price_attestation")
    pool_snapshots_obj = obj.get("pool_snapshots")
    lp_unit_values_obj = obj.get("lp_unit_values")
    consumer_now_epoch = obj.get("consumer_now_epoch")
    max_attestation_age_epochs = obj.get("max_attestation_age_epochs")
    allowed_signers_obj = obj.get("allowed_signers")
    settlement_validation = obj.get("settlement_validation", "strong_replay")
    swap_ordering = obj.get("swap_ordering", "greedy_ab_refined")
    quote_bindings_validated = obj.get("quote_bindings_validated", False)
    packet_obj = obj.get("packet")

    if not isinstance(intents_obj, list) or not intents_obj:
        write_json(400, {"ok": False, "error": "bad_intents"})
        return None
    if not isinstance(balances_obj, list):
        write_json(400, {"ok": False, "error": "bad_balances"})
        return None
    if lp_balances_obj is not None and not isinstance(lp_balances_obj, list):
        write_json(400, {"ok": False, "error": "bad_lp_balances"})
        return None
    if not isinstance(block_timestamp, int) or isinstance(block_timestamp, bool) or block_timestamp < 0:
        write_json(400, {"ok": False, "error": "bad_block_timestamp"})
        return None
    if not isinstance(settlement_obj, dict):
        write_json(400, {"ok": False, "error": "bad_settlement"})
        return None
    if price_packet_obj is None and price_attestation_obj is None:
        write_json(400, {"ok": False, "error": "missing_price_input"})
        return None
    if price_packet_obj is not None and not isinstance(price_packet_obj, dict):
        write_json(400, {"ok": False, "error": "bad_price_packet"})
        return None
    if price_attestation_obj is not None and not isinstance(price_attestation_obj, dict):
        write_json(400, {"ok": False, "error": "bad_price_attestation"})
        return None
    if pool_snapshots_obj is not None and (not isinstance(pool_snapshots_obj, list) or not pool_snapshots_obj):
        write_json(400, {"ok": False, "error": "bad_pool_snapshots"})
        return None
    if lp_unit_values_obj is not None and (not isinstance(lp_unit_values_obj, dict) or not lp_unit_values_obj):
        write_json(400, {"ok": False, "error": "bad_lp_unit_values"})
        return None
    if pool_snapshots_obj is not None and lp_unit_values_obj is not None:
        write_json(400, {"ok": False, "error": "conflicting_value_mode_inputs"})
        return None
    if not isinstance(quote_bindings_validated, bool):
        write_json(400, {"ok": False, "error": "bad_quote_bindings_validated"})
        return None
    if require_packet and not isinstance(packet_obj, dict):
        write_json(400, {"ok": False, "error": "bad_packet"})
        return None
    if price_attestation_obj is not None:
        if not isinstance(consumer_now_epoch, int) or isinstance(consumer_now_epoch, bool) or consumer_now_epoch < 0:
            write_json(400, {"ok": False, "error": "bad_consumer_now_epoch"})
            return None
        if (
            not isinstance(max_attestation_age_epochs, int)
            or isinstance(max_attestation_age_epochs, bool)
            or max_attestation_age_epochs < 0
        ):
            write_json(400, {"ok": False, "error": "bad_max_attestation_age_epochs"})
            return None
        if allowed_signers_obj is not None and not isinstance(allowed_signers_obj, dict):
            write_json(400, {"ok": False, "error": "bad_allowed_signers"})
            return None

    return {
        "intents_obj": intents_obj,
        "balances_obj": balances_obj,
        "lp_balances_obj": lp_balances_obj,
        "block_timestamp": block_timestamp,
        "settlement_obj": settlement_obj,
        "proof_flags_obj": proof_flags_obj,
        "price_history_obj": price_history_obj,
        "feature_extension_inputs_obj": feature_extension_inputs_obj,
        "price_packet_obj": price_packet_obj,
        "price_attestation_obj": price_attestation_obj,
        "pool_snapshots_obj": pool_snapshots_obj,
        "lp_unit_values_obj": lp_unit_values_obj,
        "consumer_now_epoch": consumer_now_epoch,
        "max_attestation_age_epochs": max_attestation_age_epochs,
        "allowed_signers_obj": allowed_signers_obj,
        "settlement_validation": settlement_validation,
        "swap_ordering": swap_ordering,
        "quote_bindings_validated": quote_bindings_validated,
        "packet_obj": packet_obj,
    }


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
    payload = _validate_common_request(obj=obj, write_json=write_json, require_packet=require_packet)
    if payload is None:
        return True

    try:
        from src.integration.operations import (  # pylint: disable=import-outside-toplevel
            _parse_settlement,
            parse_intents,
        )
        from src.integration.settlement_witness_lifecycle import (  # pylint: disable=import-outside-toplevel
            build_settlement_witness_lifecycle_packet,
            verify_settlement_witness_lifecycle_packet_payload,
        )

        intents = parse_intents({"2": payload["intents_obj"]})
        balances = _parse_balance_table_payload(payload["balances_obj"])
        lp_balances = _parse_lp_balances_payload(payload["lp_balances_obj"])
        pools_by_id = parse_pools()
        settlement = _parse_settlement(payload["settlement_obj"])
        certificate_inputs = _build_certificate_inputs(
            proof_flags_obj=payload["proof_flags_obj"],
            price_history_obj=payload["price_history_obj"],
            feature_extension_inputs_obj=payload["feature_extension_inputs_obj"],
            price_packet_obj=payload["price_packet_obj"],
            price_attestation_obj=payload["price_attestation_obj"],
            pool_snapshots_obj=payload["pool_snapshots_obj"],
            lp_unit_values_obj=payload["lp_unit_values_obj"],
            consumer_now_epoch=payload["consumer_now_epoch"],
            max_attestation_age_epochs=payload["max_attestation_age_epochs"],
            allowed_signers_obj=payload["allowed_signers_obj"],
            parse_settlement_proof_flags_payload=parse_settlement_proof_flags_payload,
            parse_price_history_payload=parse_price_history_payload,
            parse_settlement_feature_extension_inputs_payload=parse_settlement_feature_extension_inputs_payload,
        )

        if not require_packet:
            packet = build_settlement_witness_lifecycle_packet(
                intents=intents,
                settlement=settlement,
                balances=balances,
                pools=pools_by_id,
                lp_balances=lp_balances,
                block_timestamp=int(payload["block_timestamp"]),
                settlement_end_to_end_certificate_inputs=certificate_inputs,
                settlement_validation=str(payload["settlement_validation"]),
                swap_ordering=str(payload["swap_ordering"]),
                quote_bindings_validated=bool(payload["quote_bindings_validated"]),
            )
            write_json(200, {"ok": True, "packet": packet.to_dict()})
            return True

        ok, err = verify_settlement_witness_lifecycle_packet_payload(
            intents=intents,
            settlement=settlement,
            balances=balances,
            pools=pools_by_id,
            lp_balances=lp_balances,
            block_timestamp=int(payload["block_timestamp"]),
            settlement_end_to_end_certificate_inputs=certificate_inputs,
            packet_payload=payload["packet_obj"],
            settlement_validation=str(payload["settlement_validation"]),
            swap_ordering=str(payload["swap_ordering"]),
            quote_bindings_validated=bool(payload["quote_bindings_validated"]),
        )
        write_json(200, {"ok": bool(ok), "error": err})
        return True
    except Exception as exc:
        error = "verify_settlement_witness_lifecycle_packet_error" if require_packet else "build_settlement_witness_lifecycle_packet_error"
        write_json(400, {"ok": False, "error": error, "details": str(exc)[:200]})
        return True
