from __future__ import annotations

import pytest

from src.integration.operations import (
    SignedIntentEnvelope,
    create_intent_operation,
    create_signed_intent_operation,
    create_settlement_operation,
    parse_intents,
    parse_settlement,
    parse_settlement_envelope,
    parse_signed_intents,
)
from src.core.settlement import Settlement
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

    with pytest.raises(ValueError, match="Invalid intent kind: NOPE"):
        parse_signed_intents({"2": [{**_min_intent_dict(), "kind": "NOPE"}]})

    with pytest.raises(ValueError, match="intent keys must be strings"):
        parse_signed_intents({"2": [{**_min_intent_dict(), 1: "bad-key"}]})  # type: ignore[dict-item]


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
