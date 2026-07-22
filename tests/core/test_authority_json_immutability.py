from __future__ import annotations

import copy

import pytest

from src.core.quote_receipts import make_route_quote_receipt, receipt_hash
from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.core.zusd import E8, ZUSDMultiCommand, ZUSDMultiState, ZUSDVault, step_multi
from src.integration.operations import SignedIntentEnvelope
from src.state.canonical import canonical_json_bytes
from src.state.immutable_json import FrozenDict, FrozenList
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus


def _pool() -> PoolState:
    return PoolState(
        pool_id="pool-ab",
        asset0="A",
        asset1="B",
        reserve0=1_000_000,
        reserve1=500_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=1,
    )


def _quote() -> RouteQuote:
    hop = RouteHop(
        pool_id="pool-ab",
        asset_in="A",
        asset_out="B",
        amount_in=10,
        amount_out=9,
    )
    return RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=10,
        amount_out=9,
        legs=(RouteLeg(hops=(hop,), amount_in=10, amount_out=9),),
    )


def test_quote_receipt_body_is_owned_and_recursively_immutable() -> None:
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=_quote(),
        pools_by_id={"pool-ab": _pool()},
    )
    body = receipt["body"]
    before = receipt_hash(body)

    assert isinstance(receipt, FrozenDict)
    assert isinstance(body, FrozenDict)
    assert isinstance(body["legs"], FrozenList)
    assert receipt["receipt_hash"] == before

    with pytest.raises(TypeError):
        body["legs"][0]["hops"][0]["amount_out"] = 8
    with pytest.raises(TypeError):
        body["legs"].append({})
    with pytest.raises(TypeError):
        receipt["receipt_hash"] = "0x00"

    assert body["legs"][0]["hops"][0]["amount_out"] == 9
    assert receipt_hash(body) == before


def test_signed_intent_envelope_owns_raw_quote_receipt_builder() -> None:
    receipt_builder = copy.deepcopy(
        make_route_quote_receipt(
            kind="exact_in",
            quote=_quote(),
            pools_by_id={"pool-ab": _pool()},
        )
    )
    envelope = SignedIntentEnvelope(
        intent=Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id="0x" + "11" * 32,
            sender_pubkey="0x" + "22" * 48,
            deadline=10,
            fields={},
        ),
        quote_receipt=receipt_builder,
    )
    assert envelope.quote_receipt is not None
    before = receipt_hash(envelope.quote_receipt["body"])

    receipt_builder["body"]["amount_out"] = 1
    receipt_builder["body"]["legs"][0]["hops"][0]["amount_out"] = 1

    assert envelope.quote_receipt["body"]["amount_out"] == 9
    assert envelope.quote_receipt["body"]["legs"][0]["hops"][0]["amount_out"] == 9
    assert receipt_hash(envelope.quote_receipt["body"]) == before

    with pytest.raises(TypeError):
        envelope.quote_receipt["body"]["amount_out"] = 1


def test_zusd_command_owns_constructor_arguments_before_hash_and_execution() -> None:
    builder = {
        "vault": "a",
        "amount_e8": 10 * E8,
        "metadata": {"route": ["first", "second"]},
    }
    command = ZUSDMultiCommand(tag="repay_zusd", args=builder)
    command_bytes = canonical_json_bytes({"tag": command.tag, "args": command.args})
    state = ZUSDMultiState(
        vault_a=ZUSDVault(collateral_e8=500 * E8, debt_e8=200 * E8),
        free_debt_e8=200 * E8,
    )

    builder["amount_e8"] = 20 * E8
    builder["metadata"]["route"][0] = "mutated"

    assert command.args["amount_e8"] == 10 * E8
    assert command.args["metadata"]["route"] == ["first", "second"]
    assert canonical_json_bytes({"tag": command.tag, "args": command.args}) == command_bytes

    with pytest.raises(TypeError):
        command.args["amount_e8"] = 20 * E8
    with pytest.raises(TypeError):
        command.args["metadata"]["route"].append("third")

    first = step_multi(state, command)
    second = step_multi(state, command)
    assert first == second
    assert first.ok is True
    assert first.state is not None
    assert first.effects is not None
    assert first.state.vault_a.debt_e8 == 190 * E8
    assert first.effects["amount_e8"] == 10 * E8
