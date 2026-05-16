from __future__ import annotations

import pytest

from src.core.settlement import Settlement
from src.integration.operations import (
    SignedIntentEnvelope,
    _parse_intent,
    create_intent_operation,
    create_signed_intent_operation,
    create_settlement_operation,
    parse_intents,
    parse_settlement,
    parse_settlement_envelope,
    parse_signed_intents,
)
from src.state.intents import Intent, IntentKind


def _min_intent_dict(*, intent_id: str = "0x" + "11" * 32) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id,
        "sender_pubkey": "pk",
        "deadline": 1,
        "pool_id": "0x" + "22" * 32,
        "asset_in": "asset-a",
        "asset_out": "asset-b",
        "amount_in": 5,
        "min_amount_out": 0,
    }


def test_parse_signed_intents_accepts_signature_field() -> None:
    ops = {"2": [{**_min_intent_dict(), "signature": "0xsig"}]}
    envs = parse_signed_intents(ops)
    assert len(envs) == 1
    assert envs[0].signature == "0xsig"
    assert "signature" not in (envs[0].intent.fields or {})


def test_parse_signed_intents_accepts_envelope_format() -> None:
    ops = {"2": [[_min_intent_dict(), "0xsig2"]]}
    envs = parse_signed_intents(ops)
    assert len(envs) == 1
    assert envs[0].signature == "0xsig2"


def test_parse_signed_intents_accepts_quote_receipt_field() -> None:
    receipt = {"body": {"schema": "zenodex/route_quote_receipt/v1"}, "receipt_hash": "0xabc"}
    ops = {"2": [{**_min_intent_dict(), "quote_receipt": receipt}]}
    envs = parse_signed_intents(ops)
    assert len(envs) == 1
    assert envs[0].quote_receipt == receipt
    assert "quote_receipt" not in (envs[0].intent.fields or {})


def test_parse_signed_intents_accepts_envelope_format_with_quote_receipt() -> None:
    receipt = {"body": {"schema": "zenodex/route_quote_receipt/v1"}, "receipt_hash": "0xabc"}
    ops = {"2": [[_min_intent_dict(), "0xsig2", receipt]]}
    envs = parse_signed_intents(ops)
    assert len(envs) == 1
    assert envs[0].signature == "0xsig2"
    assert envs[0].quote_receipt == receipt


def test_parse_signed_intents_rejects_double_signature() -> None:
    ops = {"2": [[{**_min_intent_dict(), "signature": "0xsig"}, "0xsig"]]}
    with pytest.raises(ValueError, match="signature provided twice"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_differing_double_signature() -> None:
    ops = {"2": [[{**_min_intent_dict(), "signature": "0xsig-a"}, "0xsig-b"]]}
    with pytest.raises(ValueError, match="signature provided twice \\(envelope \\+ field\\) and differs"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_double_quote_receipt() -> None:
    receipt = {"body": {"schema": "zenodex/route_quote_receipt/v1"}, "receipt_hash": "0xabc"}
    ops = {"2": [[{**_min_intent_dict(), "quote_receipt": receipt}, "0xsig", receipt]]}
    with pytest.raises(ValueError, match="quote_receipt provided twice"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_malformed_quote_receipt_envelope() -> None:
    ops = {"2": [[_min_intent_dict(), {"not": "a receipt"}]]}
    with pytest.raises(ValueError, match=r"quote_receipt\.body must be an object"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_quote_receipt_without_hash() -> None:
    ops = {"2": [[_min_intent_dict(), {"body": {"schema": "zenodex/route_quote_receipt/v1"}, "receipt_hash": ""}]]}
    with pytest.raises(ValueError, match=r"quote_receipt\.receipt_hash must be a non-empty string"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_bad_deadline_type() -> None:
    ops = {"2": [{**_min_intent_dict(), "deadline": True}]}
    with pytest.raises(ValueError, match="intent\\.deadline must be an int"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_non_string_signature() -> None:
    ops = {"2": [{**_min_intent_dict(), "signature": 123}]}
    with pytest.raises(ValueError, match="signature must be a string"):
        parse_signed_intents(ops)


def test_parse_signed_intents_rejects_oversized_signature() -> None:
    ops = {"2": [{**_min_intent_dict(), "signature": "x" * 4097}]}
    with pytest.raises(ValueError, match="signature too large"):
        parse_signed_intents(ops)


def test_create_signed_intent_operation_roundtrips_transport_metadata() -> None:
    receipt = {"body": {"schema": "zenodex/route_quote_receipt/v1"}, "receipt_hash": "0xabc"}
    env = parse_signed_intents({"2": [{**_min_intent_dict(), "signature": "0xsig", "quote_receipt": receipt}]})[0]
    ops = create_signed_intent_operation([env])
    assert ops["2"][0]["signature"] == "0xsig"
    assert ops["2"][0]["quote_receipt"] == receipt

    reparsed = parse_signed_intents(ops)
    assert len(reparsed) == 1
    assert reparsed[0].signature == "0xsig"
    assert reparsed[0].quote_receipt == receipt


def test_create_intent_operation_rejects_quote_receipt_reserved_key() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "33" * 32,
        sender_pubkey="pk",
        deadline=1,
        fields={"quote_receipt": {"receipt_hash": "0xabc"}},
    )
    with pytest.raises(ValueError, match="reserved key: quote_receipt"):
        create_intent_operation([intent])


def test_parse_settlement_envelope_extracts_proof() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "proof": {"pi": 1}}}
    env = parse_settlement_envelope(ops)
    assert env is not None
    assert env.proof == {"pi": 1}


def test_parse_settlement_envelope_extracts_legacy_zk_proof() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "zk_proof": {"pi": 2}}}
    env = parse_settlement_envelope(ops)
    assert env is not None
    assert env.proof == {"pi": 2}


def test_parse_settlement_envelope_rejects_invalid_top_level_shapes() -> None:
    with pytest.raises(ValueError, match="operations must be an object"):
        parse_settlement_envelope([])  # type: ignore[arg-type]

    assert parse_settlement_envelope({}) is None

    with pytest.raises(ValueError, match=r"operations\['3'\] must be a dict"):
        parse_settlement_envelope({"3": []})


def test_parse_settlement_envelope_rejects_double_proof() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "proof": {}, "zk_proof": {}}}
    with pytest.raises(ValueError, match="provided twice"):
        parse_settlement_envelope(ops)


def test_parse_settlement_envelope_rejects_non_object_proof() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "proof": "nope"}}
    with pytest.raises(ValueError, match="proof must be an object"):
        parse_settlement_envelope(ops)


def test_parse_settlement_envelope_rejects_non_string_batch_ref() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "batch_ref": 123}}
    with pytest.raises(ValueError, match="batch_ref must be a string"):
        parse_settlement_envelope(ops)


def test_parse_settlement_treats_none_lists_as_empty() -> None:
    settlement = parse_settlement(
        {
            "3": {
                "module": "TauSwap",
                "version": "0.1",
                "included_intents": None,
                "fills": None,
                "balance_deltas": None,
                "reserve_deltas": None,
                "lp_deltas": None,
            }
        }
    )
    assert settlement is not None
    assert settlement.included_intents == []
    assert settlement.fills == []
    assert settlement.balance_deltas == []
    assert settlement.reserve_deltas == []
    assert settlement.lp_deltas == []


def test_parse_intents_handles_missing_group_and_rejects_invalid_shapes() -> None:
    assert parse_intents({}) == []

    with pytest.raises(ValueError, match="operations must be an object"):
        parse_intents([])  # type: ignore[arg-type]

    with pytest.raises(ValueError, match=r"operations\['2'\] must be a list"):
        parse_intents({"2": {}})

    with pytest.raises(ValueError, match="Failed to parse intent 0: Missing required field: module"):
        parse_intents({"2": [{"version": "0.1"}]})


def test_parse_signed_intents_rejects_invalid_operations_shapes() -> None:
    with pytest.raises(ValueError, match="operations must be an object"):
        parse_signed_intents([])  # type: ignore[arg-type]

    with pytest.raises(ValueError, match=r"operations\['2'\] must be a list"):
        parse_signed_intents({"2": {}})

    with pytest.raises(ValueError, match="intent list entry must have length 1, 2, or 3"):
        parse_signed_intents({"2": [[_min_intent_dict(), "a", "b", "c"]]})

    with pytest.raises(ValueError, match="intent entry must be a dict"):
        parse_signed_intents({"2": [[123]]})


def test_parse_signed_intents_rejects_invalid_intent_envelope_fields() -> None:
    with pytest.raises(ValueError, match="intent.salt must be non-empty"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "salt": ""}]})

    with pytest.raises(ValueError, match="intent.deadline must be non-negative"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "deadline": -1}]})

    with pytest.raises(ValueError, match="Invalid module: NopeSwap"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "module": "NopeSwap"}]})

    with pytest.raises(ValueError, match="Invalid version: 9.9"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "version": "9.9"}]})

    with pytest.raises(ValueError, match="Invalid intent kind: NOPE"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "kind": "NOPE"}]})

    with pytest.raises(ValueError, match="intent keys must be strings"):
        parse_signed_intents({"2": [{**_min_intent_dict(), 1: "bad-key"}]})  # type: ignore[dict-item]


def test_parse_signed_intents_validates_swap_exact_in_fields() -> None:
    with pytest.raises(ValueError, match="Missing required field for SWAP_EXACT_IN: amount_in"):
        parse_signed_intents({"2": [{k: v for k, v in _min_intent_dict().items() if k != "amount_in"}]})

    with pytest.raises(ValueError, match="intent.amount_in must be an int"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "amount_in": True}]})

    with pytest.raises(ValueError, match="intent.asset_in and intent.asset_out must differ"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "asset_out": "asset-a"}]})


def test_parse_signed_intents_validates_swap_exact_out_fields() -> None:
    exact_out = {
        **_min_intent_dict(),
        "kind": "SWAP_EXACT_OUT",
        "amount_out": 4,
        "max_amount_in": 9,
    }
    exact_out.pop("amount_in")
    exact_out.pop("min_amount_out")
    envs = parse_signed_intents({"2": [exact_out]})
    assert envs[0].intent.kind == IntentKind.SWAP_EXACT_OUT

    with pytest.raises(ValueError, match="intent.max_amount_in must be >= 1"):
        parse_signed_intents({"2": [{**exact_out, "max_amount_in": 0}]})


def test_parse_signed_intents_validates_create_pool_fields() -> None:
    create_pool = {
        **_min_intent_dict(),
        "kind": "CREATE_POOL",
        "asset0": "asset-a",
        "asset1": "asset-b",
        "fee_bps": 30,
        "amount0": 10,
        "amount1": 20,
        "created_at": 1,
    }
    for key in ("pool_id", "asset_in", "asset_out", "amount_in", "min_amount_out"):
        create_pool.pop(key)
    envs = parse_signed_intents({"2": [create_pool]})
    assert envs[0].intent.kind == IntentKind.CREATE_POOL

    with pytest.raises(ValueError, match="intent assets must be in canonical order"):
        parse_signed_intents({"2": [{**create_pool, "asset0": "asset-b", "asset1": "asset-a"}]})

    with pytest.raises(ValueError, match="intent.fee_bps must be <= 9999"):
        parse_signed_intents({"2": [{**create_pool, "fee_bps": 10_000}]})

    with pytest.raises(ValueError, match="invalid curve configuration"):
        parse_signed_intents({"2": [{**create_pool, "curve_tag": "CPMM", "curve_params": {"p": 1}}]})


def test_parse_signed_intents_validates_liquidity_fields() -> None:
    add_liquidity = {
        **_min_intent_dict(),
        "kind": "ADD_LIQUIDITY",
        "amount0_desired": 10,
        "amount1_desired": 20,
        "amount0_min": 0,
        "amount1_min": 0,
    }
    for key in ("asset_in", "asset_out", "amount_in", "min_amount_out"):
        add_liquidity.pop(key)
    assert parse_signed_intents({"2": [add_liquidity]})[0].intent.kind == IntentKind.ADD_LIQUIDITY

    with pytest.raises(ValueError, match="Missing required field for ADD_LIQUIDITY: amount1_min"):
        parse_signed_intents({"2": [{k: v for k, v in add_liquidity.items() if k != "amount1_min"}]})

    remove_liquidity = {
        **_min_intent_dict(),
        "kind": "REMOVE_LIQUIDITY",
        "lp_amount": 1,
        "amount0_min": 0,
        "amount1_min": 0,
    }
    for key in ("asset_in", "asset_out", "amount_in", "min_amount_out"):
        remove_liquidity.pop(key)
    assert parse_signed_intents({"2": [remove_liquidity]})[0].intent.kind == IntentKind.REMOVE_LIQUIDITY

    with pytest.raises(ValueError, match="intent.lp_amount must be >= 1"):
        parse_signed_intents({"2": [{**remove_liquidity, "lp_amount": 0}]})


def test_parse_settlement_rejects_invalid_included_intent_action() -> None:
    ops = {
        "3": {
            "module": "TauSwap",
            "version": "0.1",
            "included_intents": [["id-1", "UNKNOWN"]],
        }
    }
    with pytest.raises(ValueError, match="Invalid action: UNKNOWN"):
        parse_settlement(ops)

    with pytest.raises(ValueError, match="included_intents entries must be \\[intent_id, action\\]"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "included_intents": [["id-only"]]}})


def test_parse_settlement_rejects_non_object_fill_entry() -> None:
    ops = {
        "3": {
            "module": "TauSwap",
            "version": "0.1",
            "fills": ["bad"],
        }
    }
    with pytest.raises(ValueError, match="fills entries must be objects"):
        parse_settlement(ops)


def test_parse_settlement_rejects_non_object_event_entry() -> None:
    ops = {
        "3": {
            "module": "TauSwap",
            "version": "0.1",
            "events": ["bad"],
        }
    }
    with pytest.raises(ValueError, match="settlement.events entries must be objects"):
        parse_settlement(ops)


def test_parse_settlement_rejects_invalid_top_level_shapes_and_scalars() -> None:
    with pytest.raises(ValueError, match="operations must be an object"):
        parse_settlement([])  # type: ignore[arg-type]

    assert parse_settlement({}) is None

    with pytest.raises(ValueError, match=r"operations\['3'\] must be a dict"):
        parse_settlement({"3": []})

    with pytest.raises(ValueError, match="settlement.included_intents must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "included_intents": {}}})

    with pytest.raises(ValueError, match="settlement.fills must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "fills": {}}})

    with pytest.raises(ValueError, match="settlement.balance_deltas must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "balance_deltas": {}}})

    with pytest.raises(ValueError, match="settlement.reserve_deltas must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "reserve_deltas": {}}})

    with pytest.raises(ValueError, match="settlement.lp_deltas must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "lp_deltas": {}}})

    with pytest.raises(ValueError, match="settlement.events must be a list"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "events": {}}})


def test_parse_settlement_rejects_invalid_delta_entries_and_batch_ref_types() -> None:
    with pytest.raises(ValueError, match="balance_deltas entries must be objects"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "balance_deltas": [1]}})

    with pytest.raises(ValueError, match="reserve_deltas entries must be objects"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "reserve_deltas": [1]}})

    with pytest.raises(ValueError, match="lp_deltas entries must be objects"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "lp_deltas": [1]}})

    with pytest.raises(ValueError, match="settlement.batch_ref must be a string"):
        parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "batch_ref": 123}})


def test_parse_settlement_rejects_invalid_module_version_and_constructor_failures() -> None:
    with pytest.raises(ValueError, match="Invalid module: NopeSwap"):
        parse_settlement({"3": {"module": "NopeSwap", "version": "0.1"}})

    with pytest.raises(ValueError, match="Invalid version: 9.9"):
        parse_settlement({"3": {"module": "TauSwap", "version": "9.9"}})

    with pytest.raises(ValueError, match="Invalid settlement: included_intents contains duplicate intent_id entries"):
        parse_settlement(
            {
                "3": {
                    "module": "TauSwap",
                    "version": "0.1",
                    "included_intents": [["id-1", "REJECT"], ["id-1", "REJECT"]],
                }
            }
        )


def test_parse_settlement_accepts_none_batch_ref_and_create_omits_empty_events() -> None:
    settlement = parse_settlement({"3": {"module": "TauSwap", "version": "0.1", "batch_ref": None}})
    assert settlement is not None
    assert settlement.batch_ref == ""

    created = create_settlement_operation(
        Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=[],
        )
    )
    assert "events" not in created["3"]


def test_create_intent_operation_includes_salt_and_accepts_empty_fields() -> None:
    salted = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "44" * 32,
        sender_pubkey="pk",
        deadline=1,
        salt="pepper",
        fields={},
    )
    plain = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "55" * 32,
        sender_pubkey="pk",
        deadline=1,
        fields=None,
    )

    ops = create_intent_operation([salted, plain])
    assert ops["2"][0]["salt"] == "pepper"
    assert "salt" not in ops["2"][1]


def test_parse_intent_rejects_non_object_input() -> None:
    with pytest.raises(ValueError, match="intent must be an object"):
        _parse_intent([])  # type: ignore[arg-type]
