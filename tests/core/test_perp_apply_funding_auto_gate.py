from __future__ import annotations

from src.core.perp_apply_funding_auto_gate import (
    evaluate_perp_apply_funding_auto_gate,
    perp_apply_funding_auto_gate_error,
)


def _base_kwargs() -> dict[str, object]:
    return {
        "now_epoch": 3,
        "mark_price_source_kind": 1,
        "clearing_price_seen": True,
        "clearing_price_epoch": 3,
        "oracle_last_update_epoch": 2,
        "oracle_seen": True,
        "index_price_e8": 100_000_000,
        "max_oracle_staleness_epochs": 2,
        "clearing_price_e8": 102_000_000,
        "max_oracle_move_bps": 1_000,
        "funding_cap_bps": 100,
        "projected_net_funding_quote": 0,
        "fee_pool_quote": 0,
        "fee_income_quote": 0,
        "insurance_balance_quote": 0,
        "max_fee_pool_quote": 1_000_000_000_000_000,
        "any_funding_applied_this_epoch": False,
    }


def test_perp_apply_funding_auto_gate_accepts_happy_path() -> None:
    outcome = evaluate_perp_apply_funding_auto_gate(**_base_kwargs())

    assert outcome.funding_auto_allowed is True
    assert outcome.oracle_fresh is True
    assert outcome.mark_price_e8 == 102_000_000
    assert outcome.funding_rate_bps == 100
    assert perp_apply_funding_auto_gate_error(outcome) is None


def test_perp_apply_funding_auto_gate_rejects_stale_oracle() -> None:
    kwargs = _base_kwargs()
    kwargs["now_epoch"] = 6
    kwargs["clearing_price_epoch"] = 6
    kwargs["max_oracle_staleness_epochs"] = 1
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.oracle_fresh is False
    assert outcome.funding_auto_allowed is False
    assert perp_apply_funding_auto_gate_error(outcome) == "cannot apply funding: oracle is stale"


def test_perp_apply_funding_auto_gate_rejects_invalid_control_fields() -> None:
    kwargs = _base_kwargs()
    kwargs["funding_cap_bps"] = 0
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.funding_cap_ok is False
    assert outcome.funding_auto_allowed is False
    assert perp_apply_funding_auto_gate_error(outcome) == "cannot apply funding: invalid funding_cap_bps"


def test_perp_apply_funding_auto_gate_allows_positive_net_flow_to_sink() -> None:
    kwargs = _base_kwargs()
    kwargs["projected_net_funding_quote"] = 11
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.net_funding_balanced is False
    assert outcome.fee_pool_bounds_ok is True
    assert outcome.fee_pool_after_funding_quote == 11
    assert outcome.fee_income_after_funding_quote == 11
    assert outcome.insurance_after_funding_quote == 11
    assert outcome.funding_auto_allowed is True
    assert perp_apply_funding_auto_gate_error(outcome) is None


def test_perp_apply_funding_auto_gate_rejects_negative_sink_underflow() -> None:
    kwargs = _base_kwargs()
    kwargs["projected_net_funding_quote"] = -11
    kwargs["fee_pool_quote"] = 10
    kwargs["fee_income_quote"] = 10
    kwargs["insurance_balance_quote"] = 10
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.net_funding_balanced is False
    assert outcome.funding_auto_allowed is False
    assert perp_apply_funding_auto_gate_error(outcome) == (
        "apply_funding_auto would violate funding sink bounds (net=-11)"
    )


def test_perp_apply_funding_auto_gate_accepts_prefunded_negative_net_flow() -> None:
    kwargs = _base_kwargs()
    kwargs["projected_net_funding_quote"] = -11
    kwargs["fee_pool_quote"] = 11
    kwargs["fee_income_quote"] = 11
    kwargs["insurance_balance_quote"] = 11
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.fee_pool_after_funding_quote == 0
    assert outcome.fee_income_after_funding_quote == 0
    assert outcome.insurance_after_funding_quote == 0
    assert outcome.funding_auto_allowed is True
    assert perp_apply_funding_auto_gate_error(outcome) is None


def test_perp_apply_funding_auto_gate_rejects_unsafe_mark_source() -> None:
    kwargs = _base_kwargs()
    kwargs["mark_price_source_kind"] = 4
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.mark_price_source_ok is False
    assert outcome.funding_auto_allowed is False
    assert (
        perp_apply_funding_auto_gate_error(outcome)
        == "cannot apply funding: mark price source is not derivatives-safe"
    )


def test_perp_apply_funding_auto_gate_rejects_double_apply() -> None:
    kwargs = _base_kwargs()
    kwargs["any_funding_applied_this_epoch"] = True
    outcome = evaluate_perp_apply_funding_auto_gate(**kwargs)

    assert outcome.funding_not_applied is False
    assert outcome.funding_auto_allowed is False
    assert perp_apply_funding_auto_gate_error(outcome) == "funding already applied this epoch"


def test_perp_apply_funding_auto_gate_allows_empty_open_interest_projection() -> None:
    outcome = evaluate_perp_apply_funding_auto_gate(**_base_kwargs())

    assert outcome.projected_net_funding_quote == 0
    assert outcome.funding_auto_allowed is True
