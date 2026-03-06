from __future__ import annotations

import pytest

from src.integration.operations import parse_settlement, parse_settlement_envelope, parse_signed_intents


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


def test_parse_signed_intents_rejects_double_signature() -> None:
    ops = {"2": [[{**_min_intent_dict(), "signature": "0xsig"}, "0xsig"]]}
    with pytest.raises(ValueError, match="signature provided twice"):
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


def test_parse_settlement_envelope_extracts_proof() -> None:
    ops = {"3": {"module": "TauSwap", "version": "0.1", "proof": {"pi": 1}}}
    env = parse_settlement_envelope(ops)
    assert env is not None
    assert env.proof == {"pi": 1}


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
