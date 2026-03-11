from __future__ import annotations

import importlib.util
from typing import Any

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from src.integration.operations import (
    SettlementEnvelope,
    create_settlement_operation,
    create_signed_intent_operation,
    parse_settlement,
    parse_settlement_envelope,
    parse_signed_intents,
)
from src.state.intents import IntentKind

ALPHABET = "abcdefghijklmnopqrstuvwxyz0123456789_-"
TEXT = st.text(ALPHABET, min_size=0, max_size=16)
NON_EMPTY_TEXT = st.text(ALPHABET, min_size=1, max_size=16)
HEX_32 = st.binary(min_size=32, max_size=32).map(lambda raw: "0x" + raw.hex())
RESERVED_INTENT_KEYS = {
    "module",
    "version",
    "kind",
    "intent_id",
    "sender_pubkey",
    "deadline",
    "salt",
    "signature",
    "quote_receipt",
}


JSON_VALUE: st.SearchStrategy[Any] = st.recursive(
    st.none() | st.booleans() | st.integers(min_value=-10_000, max_value=10_000) | TEXT,
    lambda child: st.lists(child, max_size=3) | st.dictionaries(NON_EMPTY_TEXT, child, max_size=3),
    max_leaves=12,
)


@st.composite
def _quote_receipt_transport(draw: st.DrawFn) -> dict[str, Any]:
    body = draw(st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=4))
    return {
        "body": body,
        "receipt_hash": draw(NON_EMPTY_TEXT),
    }


@st.composite
def _intent_fields(draw: st.DrawFn) -> dict[str, Any]:
    keys = draw(
        st.lists(
            NON_EMPTY_TEXT.filter(lambda value: value not in RESERVED_INTENT_KEYS),
            min_size=0,
            max_size=4,
            unique=True,
        )
    )
    return {key: draw(JSON_VALUE) for key in keys}


@st.composite
def _valid_intent_dict(draw: st.DrawFn) -> dict[str, Any]:
    intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": draw(st.sampled_from([kind.value for kind in IntentKind])),
        "intent_id": draw(HEX_32),
        "sender_pubkey": draw(NON_EMPTY_TEXT),
        "deadline": draw(st.integers(min_value=0, max_value=2**31)),
    }
    salt = draw(st.one_of(st.none(), NON_EMPTY_TEXT))
    if salt is not None:
        intent["salt"] = salt
    intent.update(draw(_intent_fields()))
    return intent


@st.composite
def _valid_signed_intent_entry(draw: st.DrawFn) -> dict[str, Any] | list[Any]:
    intent = draw(_valid_intent_dict())
    signature = draw(st.one_of(st.none(), NON_EMPTY_TEXT))
    quote_receipt = draw(st.one_of(st.none(), _quote_receipt_transport()))
    carrier = draw(st.sampled_from(["dict", "envelope"]))
    if carrier == "dict":
        entry = dict(intent)
        if signature is not None:
            entry["signature"] = signature
        if quote_receipt is not None:
            entry["quote_receipt"] = quote_receipt
        return entry

    options: list[list[Any]] = [[dict(intent)]]
    if signature is not None:
        options.append([dict(intent), signature])
    if quote_receipt is not None:
        options.append([dict(intent), quote_receipt])
    if signature is not None and quote_receipt is not None:
        options.append([dict(intent), signature, quote_receipt])
    return draw(st.sampled_from(options))


@st.composite
def _valid_settlement(draw: st.DrawFn) -> Settlement:
    base_ids = draw(st.lists(st.integers(min_value=0, max_value=10_000), min_size=0, max_size=4, unique=True))
    included_intents: list[tuple[str, FillAction]] = []
    fills: list[Fill] = []
    for idx in base_ids:
        intent_id = "0x" + f"{idx:064x}"
        action = draw(st.sampled_from([FillAction.FILL, FillAction.REJECT]))
        included_intents.append((intent_id, action))
        if action == FillAction.FILL:
            fills.append(
                Fill(
                    intent_id=intent_id,
                    action=FillAction.FILL,
                    amount_in_filled=draw(st.integers(min_value=0, max_value=10_000)),
                    amount_out_filled=draw(st.integers(min_value=0, max_value=10_000)),
                    fee_paid=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=1000))),
                    amount0_used=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    amount1_used=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    lp_minted=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    amount0_out=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    amount1_out=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    lp_burned=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    reserve_in_before=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                    reserve_out_before=draw(st.one_of(st.none(), st.integers(min_value=0, max_value=10_000))),
                )
            )

    balance_deltas = [
        BalanceDelta(
            pubkey=draw(NON_EMPTY_TEXT),
            asset=draw(NON_EMPTY_TEXT),
            delta_add=draw(st.integers(min_value=0, max_value=10_000)),
            delta_sub=draw(st.integers(min_value=0, max_value=10_000)),
        )
        for _ in range(draw(st.integers(min_value=0, max_value=3)))
    ]
    reserve_deltas = [
        ReserveDelta(
            pool_id=draw(NON_EMPTY_TEXT),
            asset=draw(NON_EMPTY_TEXT),
            delta_add=draw(st.integers(min_value=0, max_value=10_000)),
            delta_sub=draw(st.integers(min_value=0, max_value=10_000)),
        )
        for _ in range(draw(st.integers(min_value=0, max_value=3)))
    ]
    lp_deltas = [
        LPDelta(
            pubkey=draw(NON_EMPTY_TEXT),
            pool_id=draw(NON_EMPTY_TEXT),
            delta_add=draw(st.integers(min_value=0, max_value=10_000)),
            delta_sub=draw(st.integers(min_value=0, max_value=10_000)),
        )
        for _ in range(draw(st.integers(min_value=0, max_value=3)))
    ]
    events = draw(
        st.one_of(
            st.none(),
            st.lists(st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=3), min_size=1, max_size=3),
        )
    )
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref=draw(TEXT),
        included_intents=included_intents,
        fills=fills,
        balance_deltas=balance_deltas,
        reserve_deltas=reserve_deltas,
        lp_deltas=lp_deltas,
        events=events,
    )


SIGNED_INTENT_OPERATION = st.one_of(
    JSON_VALUE,
    st.fixed_dictionaries({"2": JSON_VALUE}),
    st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=4),
)

SETTLEMENT_OPERATION = st.one_of(
    JSON_VALUE,
    st.fixed_dictionaries({"3": JSON_VALUE}),
    st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=4),
)


@given(entries=st.lists(_valid_signed_intent_entry(), max_size=5))
@settings(max_examples=50, deadline=None, derandomize=True)
def test_parse_signed_intents_roundtrips_generated_valid_entries(entries: list[dict[str, Any] | list[Any]]) -> None:
    ops = {"2": entries}
    envs = parse_signed_intents(ops)
    reparsed = parse_signed_intents(create_signed_intent_operation(envs))
    assert reparsed == envs


@given(ops=SIGNED_INTENT_OPERATION)
@settings(max_examples=80, deadline=None, derandomize=True)
def test_parse_signed_intents_fuzz_fails_closed_with_value_error_only(ops: Any) -> None:
    try:
        envs = parse_signed_intents(ops)  # type: ignore[arg-type]
    except Exception as exc:  # noqa: BLE001
        assert isinstance(exc, ValueError)
    else:
        assert parse_signed_intents(create_signed_intent_operation(envs)) == envs


@given(settlement=_valid_settlement(), proof=st.one_of(st.none(), st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=4)), legacy_key=st.booleans())
@settings(max_examples=40, deadline=None, derandomize=True)
def test_parse_settlement_envelope_roundtrips_generated_valid_settlements(
    settlement: Settlement,
    proof: dict[str, Any] | None,
    legacy_key: bool,
) -> None:
    ops = create_settlement_operation(settlement)
    if proof is not None:
        ops["3"]["zk_proof" if legacy_key else "proof"] = proof
    env = parse_settlement_envelope(ops)
    assert env == SettlementEnvelope(settlement=settlement, proof=proof)
    assert parse_settlement(create_settlement_operation(settlement)) == settlement


@given(ops=SETTLEMENT_OPERATION)
@settings(max_examples=80, deadline=None, derandomize=True)
def test_parse_settlement_envelope_fuzz_fails_closed_with_value_error_only(ops: Any) -> None:
    try:
        env = parse_settlement_envelope(ops)  # type: ignore[arg-type]
    except Exception as exc:  # noqa: BLE001
        assert isinstance(exc, ValueError)
    else:
        if env is not None:
            assert parse_settlement(create_settlement_operation(env.settlement)) == env.settlement


def test_parse_signed_intents_rejects_empty_signature() -> None:
    ops = {"2": [{"module": "TauSwap", "version": "0.1", "kind": "SWAP_EXACT_IN", "intent_id": "0x" + "11" * 32, "sender_pubkey": "pk", "deadline": 1, "signature": ""}]}
    with pytest.raises(ValueError, match="signature must be non-empty"):
        parse_signed_intents(ops)
