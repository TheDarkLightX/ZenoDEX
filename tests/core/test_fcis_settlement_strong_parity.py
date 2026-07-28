"""Direct exact-to-mixed parity tests for the unmounted P4B4 validator."""

from __future__ import annotations

from dataclasses import replace

from src.core.fcis_settlement_strong_validator import (
    evaluate_settlement_strong_exact_v1,
)
from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
    ExactStrongSettlementRejectV1,
    StrongSettlementContextV1,
)
from src.core.settlement_snapshots import (
    OwnedSettlementV1,
    snapshot_settlement,
)
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    _evaluate_settlement_strong_admitted_observed_v5,
)
from src.state.fcis_execution_context_values import settlement_mode_label_v1
from src.state.intent_snapshots import OwnedIntentV1
from src.state.intents import IntentKind
from src.state.owned_json import snapshot_owned_json_object
from tests.core.test_fcis_settlement_strong_routes import (
    _cow_context,
    _cow_pre_state,
    _cow_settlement,
    _route_context,
    _route_fixture,
    route_pools,
)
from tests.core.test_fcis_settlement_strong_validator import (
    SWAP_AMOUNT_OUT,
    _add_liquidity_intent,
    _add_liquidity_settlement,
    _context,
    _create_pool_intent,
    _create_pool_pre_state,
    _create_pool_settlement,
    _empty_pre_state,
    _exact_out_intent,
    _exact_out_settlement,
    _liquidity_pre_state,
    _ordinary_reject_settlement,
    _proof_carrying_context,
    _protocol_fee_context,
    _protocol_fee_exact_out_settlement,
    _protocol_fee_settlement,
    _recipient_swap_intent,
    _recipient_swap_settlement,
    _remove_liquidity_intent,
    _remove_liquidity_settlement,
    _swap_intent,
    _swap_pre_state,
    _swap_settlement,
)


def _empty_settlement() -> OwnedSettlementV1:
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="empty",
            included_intents=(),
            fills=(),
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
            events=None,
        )
    )


def _assert_direct_trace_parity(exact_trace, mixed_trace) -> None:
    """Compare every retained field without normalization or projection."""

    assert exact_trace.balance_keys == mixed_trace.balance_keys
    assert exact_trace.pool_ids == mixed_trace.pool_ids
    assert exact_trace.lp_keys == mixed_trace.lp_keys
    assert exact_trace.nonce_keys == mixed_trace.nonce_keys
    assert exact_trace.reads_fee_accumulator == mixed_trace.reads_fee_accumulator
    assert exact_trace == mixed_trace


def _assert_direct_result_parity(exact_result, mixed_result) -> None:
    """Require kind, public reason, successor, and patch parity.

    There is deliberately no expected-difference registry. A REJECT-detail or
    fill-order difference remains a failing parity blocker.
    """

    if type(exact_result) is ExactStrongSettlementCandidateV1:
        assert type(mixed_result) is StrongSettlementStateCandidateV1
        assert exact_result.balances == mixed_result.balances
        assert exact_result.pools == mixed_result.pools
        assert exact_result.lp_balances == mixed_result.lp_balances
        assert exact_result.balance_patch == mixed_result.balance_patch
        assert exact_result.pool_patch == mixed_result.pool_patch
        assert exact_result.lp_patch == mixed_result.lp_patch
        return

    assert type(exact_result) is ExactStrongSettlementRejectV1
    assert type(mixed_result) is StrongSettlementRejectV1
    assert exact_result.reason == mixed_result.reason
    assert not hasattr(exact_result, "balances")
    assert not hasattr(exact_result, "balance_patch")


def _assert_parity(
    *,
    settlement: OwnedSettlementV1,
    intents: tuple[OwnedIntentV1, ...],
    pre_state: ExactSpotPreStateV1,
    context: StrongSettlementContextV1 | None = None,
) -> None:
    # This differential relation starts after exact graph admission. Corrupt
    # graphs rejected by public recursive revalidation are outside its domain.
    exact_context = _context() if context is None else context
    exact = evaluate_settlement_strong_exact_v1(
        settlement=settlement,
        intents=intents,
        pre_state=pre_state,
        context=exact_context,
    )
    settlement_context = exact_context.settlement
    mixed = _evaluate_settlement_strong_admitted_observed_v5(
        settlement=settlement,
        intents=intents,
        pre_balances=pre_state.balances,
        pre_pools=pre_state.pools,
        pre_lp_balances=pre_state.lp_balances,
        now=settlement_context.now,
        min_lp_position_age_seconds=settlement_context.min_lp_position_age_seconds,
        lp_duration_policy=exact_context.lp_duration_policy,
        mode=settlement_mode_label_v1(settlement_context.mode),
        allow_cow_netting=settlement_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(
            settlement_context.allow_snapshot_bound_quote_bindings
        ),
        protocol_fee_share_bps=settlement_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=(settlement_context.protocol_fee_recipient_pubkey),
    )

    _assert_direct_result_parity(exact.result, mixed.result)
    _assert_direct_trace_parity(exact.state_read_trace, mixed.state_read_trace)


def test_empty_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_empty_settlement(),
        intents=(),
        pre_state=_empty_pre_state(),
    )


def test_exact_in_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_swap_settlement(),
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_create_pool_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_create_pool_settlement(),
        intents=(_create_pool_intent(),),
        pre_state=_create_pool_pre_state(),
    )


def test_malformed_fill_reject_has_exact_reason_and_trace_parity() -> None:
    settlement = _swap_settlement()
    malformed = replace(
        settlement,
        fills=(
            replace(
                settlement.fills[0],
                amount_out_filled=SWAP_AMOUNT_OUT + 1,
            ),
        ),
    )

    _assert_parity(
        settlement=malformed,
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_delta_mismatch_reject_has_exact_reason_and_trace_parity() -> None:
    settlement = _swap_settlement()
    malformed_output = replace(
        settlement.balance_deltas[1],
        delta_add=SWAP_AMOUNT_OUT - 1,
    )
    malformed = replace(
        settlement,
        balance_deltas=(settlement.balance_deltas[0], malformed_output),
    )

    _assert_parity(
        settlement=malformed,
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_event_mismatch_reject_has_exact_reason_and_trace_parity() -> None:
    malformed = replace(
        _swap_settlement(),
        events=(snapshot_owned_json_object({"type": "UNEXPECTED"}),),
    )

    _assert_parity(
        settlement=malformed,
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_exact_out_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_exact_out_settlement(),
        intents=(_exact_out_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_add_liquidity_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_add_liquidity_settlement(),
        intents=(_add_liquidity_intent(),),
        pre_state=_liquidity_pre_state(),
    )


def test_remove_liquidity_accept_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_remove_liquidity_settlement(),
        intents=(_remove_liquidity_intent(),),
        pre_state=_liquidity_pre_state(),
    )


def test_ordinary_reject_without_fill_has_direct_result_and_trace_parity() -> None:
    _assert_parity(
        settlement=_ordinary_reject_settlement(),
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
    )


def test_proof_carrying_reserve_witness_has_direct_parity() -> None:
    _assert_parity(
        settlement=_exact_out_settlement(reserve_witnesses=True),
        intents=(_exact_out_intent(),),
        pre_state=_swap_pre_state(),
        context=_proof_carrying_context(),
    )


def test_protocol_fee_enabled_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_protocol_fee_settlement(),
        intents=(_swap_intent(),),
        pre_state=_swap_pre_state(),
        context=_protocol_fee_context(),
    )


def test_exact_out_protocol_fee_has_direct_result_patch_and_trace_parity() -> None:
    _assert_parity(
        settlement=_protocol_fee_exact_out_settlement(),
        intents=(_exact_out_intent(),),
        pre_state=_swap_pre_state(),
        context=_protocol_fee_context(),
    )


def test_route_exact_in_and_out_have_direct_result_patch_and_trace_parity() -> None:
    for kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
        settlement, intent, pre_state, _replay = _route_fixture(kind, route_pools())
        _assert_parity(
            settlement=settlement,
            intents=(intent,),
            pre_state=pre_state,
            context=_route_context(),
        )


def test_cow_accept_and_reject_have_direct_result_patch_and_trace_parity() -> None:
    for symmetric in (True, False):
        settlement, intents = _cow_settlement(symmetric=symmetric)
        _assert_parity(
            settlement=settlement,
            intents=intents,
            pre_state=_cow_pre_state(),
            context=_cow_context(enabled=True),
        )


def test_sender_distinct_from_recipient_has_direct_parity() -> None:
    _assert_parity(
        settlement=_recipient_swap_settlement(),
        intents=(_recipient_swap_intent(),),
        pre_state=_swap_pre_state(),
    )
