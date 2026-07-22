from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.agents.intent_signer import _create_canonical_message
from src.core.dex import DexEffects
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.core.settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    LPDelta,
    ReserveDelta,
    Settlement,
)
from src.core.settlement_snapshots import snapshot_settlement
from src.core.uniform_batch_admission import (
    uniform_batch_admission_intent_set_hash_v1,
)
from src.core.uniform_batch_clearing import uniform_batch_intent_set_hash
from src.integration.operations import SignedIntentEnvelope
from src.state.intents import Intent, IntentKind, SignedIntent
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch


def _intent_id(byte: str) -> str:
    return "0x" + byte * 64


def _pubkey(byte: str) -> str:
    return "0x" + byte * 96


def test_signed_intent_owns_and_seals_the_authenticated_payload() -> None:
    caller_fields = {
        "pool_id": "pool",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "min_amount_out": 1,
        "route": {"hops": ["pool"]},
    }
    caller_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_intent_id("1"),
        sender_pubkey=_pubkey("a"),
        deadline=123,
        fields=caller_fields,
    )
    signed = SignedIntent(
        intent=caller_intent,
        signature="0x" + "ab" * 96,
    )
    mounted = SignedIntentEnvelope(intent=caller_intent)
    authenticated_before = _create_canonical_message(signed.intent)
    mounted_before = _create_canonical_message(mounted.intent)

    signing_dict_before = build_dex_intent_signing_dict_v1(signed.intent)

    nonce_ok, nonce_error, next_nonces = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[signed.intent],
        require_all_nonces=False,
    )
    assert nonce_ok is True
    assert nonce_error is None
    assert next_nonces is not None
    assert not hasattr(signed, "__dict__")
    assert not hasattr(signed.intent, "__dict__")
    assert not hasattr(mounted, "__dict__")
    assert not hasattr(mounted.intent, "__dict__")
    assert uniform_batch_intent_set_hash([signed.intent]) == uniform_batch_intent_set_hash(
        [caller_intent]
    )
    assert uniform_batch_admission_intent_set_hash_v1(
        [signed.intent]
    ) == uniform_batch_admission_intent_set_hash_v1([caller_intent])
    caller_fields["amount_in"] = 999
    caller_fields["route"]["hops"].append("attacker")
    caller_intent.deadline = 999
    caller_intent.set_field("min_amount_out", 0)

    assert _create_canonical_message(signed.intent) == authenticated_before
    assert signed.intent.deadline == 123
    assert _create_canonical_message(mounted.intent) == mounted_before
    assert build_dex_intent_signing_dict_v1(signed.intent) == signing_dict_before
    assert signed.intent.get_field("amount_in") == 10
    assert signed.intent.get_field("min_amount_out") == 1
    assert signed.intent.get_field("route") == {"hops": ["pool"]}

    with pytest.raises(TypeError, match="immutable"):
        signed.intent.set_field("amount_in", 11)
    with pytest.raises(TypeError, match="immutable"):
        mounted.intent.set_field("amount_in", 11)
    with pytest.raises(TypeError, match="immutable"):
        signed.intent.deadline = 124
    with pytest.raises(TypeError, match="immutable"):
        signed.intent.fields["amount_in"] = 11  # type: ignore[index]
    route = signed.intent.get_field("route")
    with pytest.raises(TypeError, match="immutable"):
        route["hops"].append("other")
    with pytest.raises(FrozenInstanceError):
        signed.signature = "0x" + "cd" * 96


def test_dex_effects_owns_and_recursively_seals_settlement_meaning() -> None:
    fill = Fill(
        intent_id="i1",
        action=FillAction.FILL,
        amount_in_filled=10,
        amount_out_filled=9,
        fee_paid=1,
        reserve_in_before=100,
        reserve_out_before=100,
    )
    balance_delta = BalanceDelta(pubkey="pk", asset="A", delta_add=0, delta_sub=10)
    reserve_delta = ReserveDelta(pool_id="pool", asset="A", delta_add=10, delta_sub=0)
    lp_delta = LPDelta(pubkey="pk", pool_id="pool", delta_add=0, delta_sub=0)
    event = {"type": "SWAP", "payload": {"amounts": [10, 9]}}
    proposal = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[("i1", FillAction.FILL)],
        fills=[fill],
        balance_deltas=[balance_delta],
        reserve_deltas=[reserve_delta],
        lp_deltas=[lp_delta],
        events=[event],
    )
    effects = DexEffects(settlement=proposal, total_swap_fees=1)
    owned_candidate = snapshot_settlement(proposal)

    proposal.batch_ref = "changed"
    proposal.included_intents.append(("i2", FillAction.REJECT))
    fill.fee_paid = 999
    balance_delta.delta_sub = 999
    reserve_delta.delta_add = 999
    lp_delta.delta_add = 999
    event["payload"]["amounts"].append(999)

    assert type(owned_candidate) is Settlement
    assert type(owned_candidate.fills[0]) is Fill
    assert type(owned_candidate.balance_deltas[0]) is BalanceDelta
    assert type(owned_candidate.reserve_deltas[0]) is ReserveDelta
    assert type(owned_candidate.lp_deltas[0]) is LPDelta
    assert owned_candidate.batch_ref == "batch-1"
    assert owned_candidate.fills[0].fee_paid == 1
    assert owned_candidate.events == [{"type": "SWAP", "payload": {"amounts": [10, 9]}}]

    accepted = effects.settlement
    assert accepted.batch_ref == "batch-1"
    assert accepted.included_intents == [("i1", FillAction.FILL)]
    assert accepted.fills[0].fee_paid == 1
    assert accepted.balance_deltas[0].delta_sub == 10
    assert accepted.reserve_deltas[0].delta_add == 10
    assert accepted.lp_deltas[0].delta_add == 0
    assert accepted.events == [{"type": "SWAP", "payload": {"amounts": [10, 9]}}]

    with pytest.raises(TypeError, match="immutable"):
        accepted.batch_ref = "other"
    with pytest.raises(TypeError, match="immutable"):
        accepted.included_intents.append(("i2", FillAction.REJECT))
    with pytest.raises(TypeError, match="immutable"):
        accepted.fills[0].fee_paid = 2
    with pytest.raises(TypeError, match="immutable"):
        accepted.balance_deltas[0].delta_sub = 2
    assert accepted.events is not None
    with pytest.raises(TypeError, match="immutable"):
        accepted.events[0]["payload"]["amounts"].append(11)
    with pytest.raises(TypeError, match="immutable"):
        accepted.events[0]["payload"] = {}
