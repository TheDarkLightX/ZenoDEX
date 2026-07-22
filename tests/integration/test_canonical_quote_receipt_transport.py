from __future__ import annotations

import pytest

from src.integration.dex_engine import (
    make_strict_upba_engine_config,
    strict_upba_engine_config_facts_v0,
)
from src.integration.operations import parse_signed_intents
from src.state.canonical import canonical_json_bytes
from src.state.immutable_json import FrozenDict


def _intent(**extra: object) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "11" * 32,
        "sender_pubkey": "0x" + "22" * 48,
        "deadline": 1,
        "pool_id": "0x" + "33" * 32,
        **extra,
    }


def _receipt() -> dict[str, object]:
    body = {
        "amount_in": 10,
        "amount_out": 9,
        "asset_in": "A",
        "asset_out": "B",
        "kind": "exact_in",
        "legs": [],
        "pools": {},
        "schema": "zenodex/route_quote_receipt/v1",
    }
    return {"body": body, "receipt_hash": "0x" + "44" * 32}


def _canonical_receipt_text() -> str:
    return canonical_json_bytes(_receipt()).decode("utf-8")


def test_strict_parser_accepts_only_canonical_receipt_text() -> None:
    env = parse_signed_intents(
        {
            "2": [
                _intent(
                    signature="0xsig",
                    quote_receipt_canonical_json=_canonical_receipt_text(),
                )
            ]
        },
        require_canonical_quote_receipt_transport=True,
    )[0]

    assert isinstance(env.quote_receipt, FrozenDict)
    assert env.quote_receipt == _receipt()
    assert "quote_receipt_canonical_json" not in (env.intent.fields or {})
    with pytest.raises(TypeError):
        env.quote_receipt["receipt_hash"] = "0xforged"


def test_strict_parser_rejects_legacy_decoded_receipt_object() -> None:
    with pytest.raises(ValueError, match="canonical quote receipt transport required"):
        parse_signed_intents(
            {"2": [_intent(quote_receipt=_receipt())]},
            require_canonical_quote_receipt_transport=True,
        )


def test_legacy_parser_retains_builder_compatibility() -> None:
    env = parse_signed_intents({"2": [_intent(quote_receipt=_receipt())]})[0]
    assert env.quote_receipt == _receipt()


@pytest.mark.parametrize(
    "transport",
    [
        '{ "body":{},"receipt_hash":"0x' + "44" * 32 + '"}',
        '{"receipt_hash":"0x' + "44" * 32 + '","body":{}}',
        '{"body":{},"body":{},"receipt_hash":"0x' + "44" * 32 + '"}',
        _canonical_receipt_text() + "\n",
    ],
)
def test_strict_parser_rejects_noncanonical_inner_json(transport: str) -> None:
    with pytest.raises(ValueError, match="canonical JSON"):
        parse_signed_intents(
            {
                "2": [
                    _intent(
                        quote_receipt_canonical_json=transport,
                    )
                ]
            },
            require_canonical_quote_receipt_transport=True,
        )


def test_receipt_cannot_be_supplied_in_both_carriers() -> None:
    with pytest.raises(ValueError, match="provided twice"):
        parse_signed_intents(
            {
                "2": [
                    _intent(
                        quote_receipt=_receipt(),
                        quote_receipt_canonical_json=_canonical_receipt_text(),
                    )
                ]
            }
        )


def test_strict_upba_profile_requires_canonical_receipt_transport() -> None:
    config = make_strict_upba_engine_config()
    facts = strict_upba_engine_config_facts_v0(config)

    assert config.require_canonical_quote_receipt_transport is True
    assert facts["require_canonical_quote_receipt_transport"] is True
