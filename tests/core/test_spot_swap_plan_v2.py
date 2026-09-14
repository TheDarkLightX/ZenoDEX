"""Actual intents, immutable plans and independently checked CPMM amounts."""

import sys
import types
from dataclasses import FrozenInstanceError, replace
from pathlib import Path

import pytest

from src.core.global_settlement_types_v2 import MAX_ATOMS_V2
from src.core.spot_swap_plan_v2 import (
    SpotSwapContextV2,
    SpotSwapPlanV2,
    SpotSwapRejectedV2,
    plan_spot_swap_v2,
)
from src.core.spot_swap_plan_v2 import (
    SpotSwapRejectCodeV2 as Code,
)
from src.state.intents import IntentKind, SwapIntent
from src.state.pools import PoolState, PoolStatus


def pool(**changes):
    return PoolState(**{
        "pool_id": "pool", "asset0": "A", "asset1": "B", "reserve0": 1000,
        "reserve1": 1000, "fee_bps": 30, "lp_supply": 1000,
        "status": PoolStatus.ACTIVE, "created_at": 0, **changes,
    })


def intent(*, exact_out=True, reverse=False, **fields):
    amounts = {"amount_out": 7, "max_amount_in": 10} if exact_out else {
        "amount_in": 10, "min_amount_out": 7,
    }
    return SwapIntent(
        "TauSwap", "0.1", IntentKind.SWAP_EXACT_OUT if exact_out else IntentKind.SWAP_EXACT_IN,
        "0x" + "11" * 32, "alice", 100,
        fields={"pool_id": "pool", "asset_in": "B" if reverse else "A",
                "asset_out": "A" if reverse else "B", "nonce": 1, **amounts, **fields},
    )


def context(**changes):
    return SpotSwapContextV2(**{
        "subject_id": "alice", "block_timestamp": 100,
        "sender_input_atoms": 100, "recipient_output_atoms": 5, **changes,
    })


@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("exact_out", [False, True])
def test_given_real_intent_when_planned_then_complete_conserving_owned_result(reverse, exact_out):
    pre = pool(reserve0=1000, reserve1=2000)
    command = intent(exact_out=exact_out, reverse=reverse, recipient="bob",
                     **({"amount_out": 7, "max_amount_in": 20} if exact_out else {"min_amount_out": 1}))
    ctx = context()
    result = plan_spot_swap_v2(ctx, pre, command)
    assert isinstance(result, SpotSwapPlanV2)
    assert result.intent == command and result.intent is not command
    assert result.sender == "alice" and result.recipient == "bob"
    assert result.post_sender_input_atoms == 100 - result.amount_in_atoms
    assert result.post_recipient_output_atoms == 5 + result.amount_out_atoms
    assert result.post_pool.lp_supply == pre.lp_supply
    assert result.post_pool.created_at == pre.created_at
    assert result.post_pool.reserve0 * result.post_pool.reserve1 >= pre.reserve0 * pre.reserve1
    deltas = result.pool_deltas
    assert deltas == ((-result.amount_out_atoms, result.amount_in_atoms) if reverse else
                      (result.amount_in_atoms, -result.amount_out_atoms))
    assert result.account_deltas == (-result.amount_in_atoms, result.amount_out_atoms)
    before = result.pre_pool
    pre.reserve0 = 999
    assert result.pre_pool == before and result.pre_pool.reserve0 == 1000
    with pytest.raises(FrozenInstanceError):
        result.post_pool.reserve0 = 0  # type: ignore[misc]  # Deliberate immutable-value attack.


def test_given_maximum_ten_when_exact_output_seven_then_actual_debit_is_nine():
    result = plan_spot_swap_v2(context(), pool(), intent())
    assert isinstance(result, SpotSwapPlanV2)
    assert (result.amount_in_atoms, result.amount_out_atoms, result.fee_atoms) == (9, 7, 1)
    assert result.post_pool.reserve0 == 1009  # Entire rounded fee stays with LP reserves.
    assert result.post_sender_input_atoms == 91


@pytest.mark.parametrize("ctx,pre,command,code", [
    (context(subject_id="mallory"), pool(), intent(), Code.SUBJECT_MISMATCH),
    (context(block_timestamp=101), pool(), intent(), Code.EXPIRED),
    (context(), pool(), intent(pool_id="other"), Code.POOL_MISMATCH),
    (context(), pool(), intent(asset_out="C"), Code.ASSET_MISMATCH),
    (context(), pool(), intent(asset_out="A"), Code.ASSET_MISMATCH),
    (context(), pool(status=PoolStatus.DISABLED), intent(), Code.POOL_INACTIVE),
    (context(), pool(), intent(max_amount_in=8), Code.SLIPPAGE_LIMIT),
    (context(), pool(), intent(exact_out=False, min_amount_out=99), Code.SLIPPAGE_LIMIT),
    (context(sender_input_atoms=8), pool(), intent(), Code.INSUFFICIENT_BALANCE),
    (context(recipient_output_atoms=MAX_ATOMS_V2), pool(), intent(), Code.BALANCE_OVERFLOW),
    (context(), pool(), intent(quote_receipt_hash="foreign"), Code.UNSUPPORTED_FIELDS),
    (context(), pool(), intent(nonce=0), Code.INVALID_NONCE),
    (context(), pool(), intent(nonce=2**32), Code.INVALID_NONCE),
])
def test_given_failed_guard_when_planned_then_typed_reject_has_no_plan_or_mutation(ctx, pre, command, code):
    before = dict(vars(pre))
    assert plan_spot_swap_v2(ctx, pre, command) == SpotSwapRejectedV2(code)
    assert vars(pre) == before


def test_independent_small_domain_exact_out_minimum_and_rounding():
    accepted = rejected = 0
    for reserve_in in (9, 17, 31):
        for reserve_out in (11, 29, 53):
            for fee_bps in (0, 30, 1000):
                for wanted in range(1, 6):
                    gross = next(n for n in range(1, 100) if
                        reserve_out * (n - (n * fee_bps + 9999) // 10000) //
                        (reserve_in + n - (n * fee_bps + 9999) // 10000) >= wanted)
                    fee = (gross * fee_bps + 9999) // 10000
                    quote_out = reserve_out * (gross - fee) // (reserve_in + gross - fee)
                    gap_bps = ((quote_out - wanted) * 10000 + wanted - 1) // wanted
                    result = plan_spot_swap_v2(context(), pool(reserve0=reserve_in,
                        reserve1=reserve_out, fee_bps=fee_bps), intent(amount_out=wanted, max_amount_in=99))
                    if gap_bps > 200:
                        assert result == SpotSwapRejectedV2(Code.QUOTE_REJECTED)
                        rejected += 1
                    else:
                        assert isinstance(result, SpotSwapPlanV2)
                        assert (result.amount_in_atoms, result.amount_out_atoms, result.fee_atoms) == (gross, wanted, fee)
                        assert result.pool_deltas == (gross, -wanted)
                        accepted += 1
    assert accepted > 0 and rejected > 0


def test_successor_reserve_domain_and_u128_balance_neighbors():
    assert plan_spot_swap_v2(context(sender_input_atoms=MAX_ATOMS_V2), pool(reserve0=3_000_000_000),
        intent(amount_out=1, max_amount_in=3_000_000_000)) == SpotSwapRejectedV2(Code.QUOTE_REJECTED)
    result = plan_spot_swap_v2(context(recipient_output_atoms=MAX_ATOMS_V2 - 7), pool(), intent())
    assert isinstance(result, SpotSwapPlanV2)
    assert result.post_recipient_output_atoms == MAX_ATOMS_V2


def test_hostile_subclass_is_rejected_before_getter_runs():
    class HostilePool(PoolState):
        def __getattribute__(self, name):
            raise AssertionError("foreign getter executed")

    hostile = object.__new__(HostilePool)
    with pytest.raises(TypeError, match="exact"):
        plan_spot_swap_v2(context(), hostile, intent())


@pytest.mark.parametrize("location", ["backing", "pair", "key", "value", "module", "intent_id"])
def test_forged_exact_intent_rejects_without_executing_foreign_hooks(location):
    calls = []

    class Foreign:
        def hook(self, *args):
            calls.append(location)
            raise RuntimeError("foreign protocol executed")

        __iter__ = __len__ = __str__ = __hash__ = __eq__ = hook

    foreign = Foreign()
    command = intent()
    if location in {"module", "intent_id"}:
        object.__setattr__(command, location, foreign)
    else:
        raw = {"backing": foreign, "pair": (foreign,), "key": ((foreign, 1),),
               "value": (("amount_out", foreign),)}[location]
        object.__setattr__(command.fields, "_items", raw)
    pre = pool()
    before = dict(vars(pre))
    with pytest.raises((TypeError, ValueError)):
        plan_spot_swap_v2(context(), pre, command)
    assert calls == [] and vars(pre) == before


@pytest.mark.parametrize("location", ["context", "pool", "intent", "fields"])
def test_uninitialized_exact_values_have_structural_rejections(location):
    ctx, pre, command = context(), pool(), intent()
    if location == "context":
        ctx = object.__new__(type(ctx))
    elif location == "pool":
        pre = object.__new__(type(pre))
    elif location == "intent":
        command = object.__new__(type(command))
    else:
        object.__setattr__(command, "fields", object.__new__(type(command.fields)))
    with pytest.raises((TypeError, ValueError)):
        plan_spot_swap_v2(ctx, pre, command)


@pytest.mark.parametrize("raw", [(("nonce", 1), ("nonce", 2)), (("nonce", 1), ("asset_in", "A"))])
def test_forged_field_order_or_duplicates_reject_without_normalizing(raw):
    command = intent()
    object.__setattr__(command.fields, "_items", raw)
    with pytest.raises(ValueError, match="unique, ordered"):
        plan_spot_swap_v2(context(), pool(), command)


def test_complete_intent_metadata_and_unsupported_nested_fields():
    command = replace(intent(), salt="s" * 4096)
    result = plan_spot_swap_v2(context(), pool(), command)
    assert isinstance(result, SpotSwapPlanV2) and result.intent == command
    assert result.intent.salt == "s" * 4096
    assert plan_spot_swap_v2(context(), pool(), intent(route={"steps": [1, 2]})) == SpotSwapRejectedV2(
        Code.UNSUPPORTED_FIELDS)


@pytest.mark.parametrize("field,value", [("sender_input_atoms", True), ("recipient_output_atoms", -1),
                                        ("block_timestamp", 2**64)])
def test_structural_context_edges_reject(field, value):
    with pytest.raises((TypeError, ValueError)):
        context(**{field: value})


def test_intent_field_alias_and_unsupported_curve():
    command = intent()
    exported = command.to_wire_fields()
    candidate = plan_spot_swap_v2(context(), pool(), command)
    assert isinstance(candidate, SpotSwapPlanV2)
    exported["max_amount_in"] = 1
    assert candidate.intent.get_field("max_amount_in") == 10
    other_curve = pool()
    other_curve.curve_tag = "CUBIC_SUM_V1"
    assert plan_spot_swap_v2(context(), other_curve, command) == SpotSwapRejectedV2(Code.UNSUPPORTED_CURVE)


@pytest.mark.parametrize("name,old,new", [
    ("wrong_subject", "if context.subject_id != intent.sender_pubkey:",
     "if False and context.subject_id != intent.sender_pubkey:"),
    ("wrong_direction", "pre.asset0 else (\n        quote.reserve_out_after, quote.reserve_in_after)",
     "pre.asset1 else (\n        quote.reserve_out_after, quote.reserve_in_after)"),
    ("sender_credited", "context.sender_input_atoms - quote.amount_in, context.recipient_output_atoms",
     "context.sender_input_atoms + quote.amount_in, context.recipient_output_atoms"),
    ("lp_fee_omitted", 'amount_in=intent.get_field("amount_in"), fee_bps=pool.fee_bps, protocol_fee_share_bps=0)',
     'amount_in=intent.get_field("amount_in"), fee_bps=0, protocol_fee_share_bps=0)'),
])
def test_named_source_mutants_change_the_independent_economic_observation(name, old, new, monkeypatch):
    source = Path(__file__).resolve().parents[2] / "src/core/spot_swap_plan_v2.py"
    text = source.read_text()
    assert text.count(old) == 1
    module = types.ModuleType(f"src.core._spot_mutant_{name}")
    monkeypatch.setitem(sys.modules, module.__name__, module)
    exec(compile(text.replace(old, new, 1), str(source), "exec"), module.__dict__)
    ctx = module.SpotSwapContextV2("mallory" if name == "wrong_subject" else "alice", 100, 100, 5)
    command = intent(exact_out=name != "lp_fee_omitted")
    control = plan_spot_swap_v2(context(subject_id=ctx.subject_id), pool(reserve1=2000), command)
    outcome = module.plan_spot_swap_v2(ctx, pool(reserve1=2000), command)
    # Fixed independent outcomes for the exact-out and exact-in specimens.
    if name == "wrong_subject":
        assert control == SpotSwapRejectedV2(Code.SUBJECT_MISMATCH)
        assert type(outcome).__name__ != "SpotSwapRejectedV2"
    else:
        expected = (1005, 1993, 95, 12, 1) if name != "lp_fee_omitted" else (1010, 1983, 90, 22, 1)
        assert isinstance(control, SpotSwapPlanV2)
        assert (control.post_pool.reserve0, control.post_pool.reserve1,
                control.post_sender_input_atoms, control.post_recipient_output_atoms, control.fee_atoms) == expected
        observed = (outcome.post_pool.reserve0, outcome.post_pool.reserve1,
                    outcome.post_sender_input_atoms, outcome.post_recipient_output_atoms, outcome.fee_atoms)
        assert observed != expected
