from __future__ import annotations

import pytest

from src.agents.autotrader_local_guard_evaluator import (
    AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA,
    AutoTraderLocalGuardInputs,
    autotrader_local_guard_evaluation_from_dict,
    evaluate_autotrader_local_guards,
)
from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)


def _strategy(*, require_quote_receipts: bool = True) -> StrategyIR:
    return StrategyIR(
        strategy_id="autotrader.local.guard.1",
        owner_pubkey="owner.pubkey.guard.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(
            max_slippage_bps=75,
            max_oracle_staleness_epochs=3,
            require_quote_receipts=require_quote_receipts,
        ),
        strategy_window=StrategyWindow(valid_from_epoch=10, valid_until_epoch=100, min_order_spacing_epochs=2),
        controls=StrategyControls(kill_switch_enabled=True, max_live_orders=3),
        template_params={"fixed_order_size": 100, "cadence_epochs": 4, "asset_in": "zUSD", "asset_out": "BTC"},
    )


def _packet(**overrides: object) -> QuoteReceiptSignalPacket:
    data = {
        "current_epoch": 12,
        "quote_epoch": 12,
        "asset_in": "zUSD",
        "asset_out": "BTC",
        "amount_in": 100,
        "amount_out": 181,
        "receipt_hash": "receipt.hash.1",
        "source_id": "route_quote_receipt",
        "source_kind": SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        "trust_tier": SignalTrustTier.VERIFIED,
        "quote_receipt_present": True,
        "quote_receipt_verified": True,
        "quote_epoch_present": True,
        "source_available": True,
        "auth_ok": True,
        "binding_ok": True,
    }
    data.update(overrides)
    return QuoteReceiptSignalPacket(**data)


def test_evaluate_autotrader_local_guards_accepts_healthy_inputs() -> None:
    strategy = _strategy()
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=200,
            spent_in_window=100,
            budget_window_id=12,
            kill_switch_active=False,
            last_action_epoch=8,
            slippage_bps=50,
            signal_packet=_packet(),
        ),
    )

    assert evaluation.ok is True
    assert evaluation.blocking_families == ()
    assert evaluation.to_dict()["schema"] == AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA
    assert evaluation.family("controls").ok is True
    assert evaluation.family("provenance").ok is True
    assert evaluation.family("oracle_freshness").ok is True
    assert evaluation.family("execution").ok is True
    assert evaluation.family("notional_budget").ok is True


def test_evaluate_autotrader_local_guards_reports_multiple_blockers() -> None:
    strategy = _strategy()
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=4,
            lifetime_spent=200,
            spent_in_window=100,
            budget_window_id=12,
            kill_switch_active=True,
            last_action_epoch=8,
            slippage_bps=80,
            signal_packet=_packet(quote_epoch=7),
        ),
    )

    assert evaluation.ok is False
    assert evaluation.blocking_families == ("controls", "slippage", "oracle_freshness", "execution")
    assert evaluation.blocking_reason_codes == (
        "kill_switch_active",
        "slippage_limit_exceeded",
        "quote_receipt_stale",
        "max_live_orders_reached",
    )
    assert evaluation.first_blocking_reason == "kill_switch_active"


def test_evaluate_autotrader_local_guards_rejects_missing_signal_packet_when_required() -> None:
    strategy = _strategy(require_quote_receipts=True)
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=0,
            spent_in_window=0,
            budget_window_id=12,
            quote_epoch=12,
        ),
    )

    provenance = evaluation.family("provenance")
    assert provenance.blocking is True
    assert provenance.reason == "signal_packet_missing"


def test_evaluate_autotrader_local_guards_separates_controls_from_budget_failures() -> None:
    strategy = _strategy()
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=101,
            projected_live_orders=1,
            lifetime_spent=0,
            spent_in_window=0,
            budget_window_id=12,
            kill_switch_active=True,
            last_action_epoch=8,
            signal_packet=_packet(amount_in=101),
        ),
    )

    assert evaluation.family("controls").reason == "kill_switch_active"
    assert evaluation.family("notional_budget").reason == "per_order_limit_exceeded"


def test_evaluate_autotrader_local_guards_leaves_optional_provenance_unchecked() -> None:
    strategy = _strategy(require_quote_receipts=False)
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=0,
            spent_in_window=0,
            budget_window_id=12,
            quote_epoch=12,
        ),
    )

    provenance = evaluation.family("provenance")
    assert provenance.checked is False
    assert provenance.blocking is False
    assert evaluation.ok is True


def test_autotrader_local_guard_inputs_to_dict_rejects_unresolved_budget_window_without_assert() -> None:
    inputs = AutoTraderLocalGuardInputs(current_epoch=12, order_amount=100)
    object.__setattr__(inputs, "budget_window_id", None)

    with pytest.raises(ValueError, match="budget_window_id must be resolved"):
        inputs.to_dict()


def test_evaluate_autotrader_local_guards_rejects_unresolved_budget_window_without_assert() -> None:
    inputs = AutoTraderLocalGuardInputs(
        current_epoch=12,
        order_amount=100,
        projected_live_orders=1,
        lifetime_spent=0,
        spent_in_window=0,
        budget_window_id=12,
        signal_packet=_packet(),
    )
    object.__setattr__(inputs, "budget_window_id", None)

    with pytest.raises(ValueError, match="budget_window_id must be resolved"):
        evaluate_autotrader_local_guards(strategy=_strategy(), inputs=inputs)


def test_evaluate_autotrader_local_guards_roundtrips_from_dict() -> None:
    strategy = _strategy()
    evaluation = evaluate_autotrader_local_guards(
        strategy=strategy,
        inputs=AutoTraderLocalGuardInputs(
            current_epoch=12,
            order_amount=100,
            projected_live_orders=1,
            lifetime_spent=200,
            spent_in_window=100,
            budget_window_id=12,
            kill_switch_active=False,
            last_action_epoch=8,
            slippage_bps=50,
            signal_packet=_packet(),
        ),
    )

    roundtrip = autotrader_local_guard_evaluation_from_dict(evaluation.to_dict())
    assert roundtrip.to_dict() == evaluation.to_dict()


def test_autotrader_local_guard_evaluation_from_dict_rejects_bad_input_types() -> None:
    payload = {
        "schema": AUTOTRADER_LOCAL_GUARD_EVALUATION_SCHEMA,
        "strategy_id": "autotrader.local.guard.1",
        "ok": False,
        "blocking_families": ["provenance"],
        "blocking_reason_codes": ["signal_packet_missing"],
        "first_blocking_reason": "signal_packet_missing",
        "inputs": {
            "current_epoch": "12",
            "order_amount": 100,
            "projected_live_orders": 1,
            "lifetime_spent": 0,
            "spent_in_window": 0,
            "budget_window_id": 12,
            "kill_switch_active": False,
            "signal_packet": _packet().to_dict(),
        },
        "family_results": [
            {
                "family": "provenance",
                "checked": True,
                "ok": False,
                "blocking": True,
                "reason": "signal_packet_missing",
                "reason_code": "signal_packet_missing",
            }
        ],
    }

    with pytest.raises(TypeError, match="current_epoch must be an int"):
        autotrader_local_guard_evaluation_from_dict(payload)
