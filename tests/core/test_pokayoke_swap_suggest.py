from __future__ import annotations

import pytest

import src.core.pokayoke_swap_suggest as suggest_module
from src.core.pokayoke_swap_suggest import (
    suggest_amount_in_exact_in_cpmm,
    suggest_amount_in_for_impact_lt_bps,
    suggest_amount_in_for_required_slippage_le_bps,
)
from src.core.price_impact_preview import price_impact_preview


def _required_slippage_bps(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int,
    confidence_bps: int,
) -> int:
    pv = price_impact_preview(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        fee_bps=int(fee_bps),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
    )
    best = int(pv.amount_out_best_case)
    out_conf = int(pv.amount_out_at_confidence)
    if best <= 0:
        return 10_000
    gap = max(0, best - out_conf)
    return (gap * 10_000 + best - 1) // best if gap > 0 else 0


def test_suggest_amount_in_for_impact_lt_5pct_finds_integer_rounding_boundary() -> None:
    # Setup: large trade against small reserves triggers high impact.
    # We ask for an amount that gets below the typed-confirm threshold (impact < 500 bps).
    s = suggest_amount_in_for_impact_lt_bps(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=1000,
        target_impact_bps=500,
        window=256,
    )
    assert s.kind == "impact_lt_bps"
    assert s.status == "ok"
    assert s.suggested_amount_in is not None

    # Empirically (under integer floor rounding), 45 is the largest amount with impact < 5%.
    assert s.suggested_amount_in == 45
    assert s.suggested_value_bps is not None
    assert int(s.suggested_value_bps) < 500


@pytest.mark.parametrize(
    "pending_volume_same_direction,target_required_slip,expected_status,expected_amount,reason",
    [
        (20, 300, "ok", 49, "reduce amount until required_slippage <= 3%"),
        (20, 218, "ok", 49, "exactly at the boundary (amount_in=49 yields required_slippage_bps=218)"),
        (20, 217, "ok", 18, "just-below boundary: due to rounding, required_slippage can drop to 0 at a much smaller size"),
    ],
    ids=lambda x: str(x),
)
def test_suggest_amount_in_for_required_slippage_bps_bva(
    pending_volume_same_direction: int,
    target_required_slip: int,
    expected_status: str,
    expected_amount: int | None,
    reason: str,
) -> None:
    _ = reason
    s = suggest_amount_in_for_required_slippage_le_bps(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        amount_in=50,
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=9500,
        target_required_slippage_bps=int(target_required_slip),
        window=64,
    )
    assert s.kind == "required_slippage_le_bps"
    assert s.status == str(expected_status)
    assert s.suggested_amount_in == expected_amount
    if expected_amount is not None:
        req = _required_slippage_bps(
            reserve_in=1000,
            reserve_out=1000,
            fee_bps=0,
            amount_in=int(expected_amount),
            pending_volume_same_direction=int(pending_volume_same_direction),
            confidence_bps=9500,
        )
        assert req <= int(target_required_slip)


def test_suggest_amount_in_exact_in_cpmm_bva_max_evals_boundary() -> None:
    # Boundary Value Analysis (BVA) for max_evals:
    # - just below valid range (0): error
    # - exactly at boundary (1): only baseline eval -> cannot find an improving candidate
    # - just above boundary (2): can evaluate 1 candidate -> should find a safer amount
    #
    # Reproducer: reserves=20_000, amount_in=101 yields action=typed_confirm due solely to mev_conflict
    # under the bounded sandwich model. amount_in=50 reduces interlock severity to confirm.
    with pytest.raises(ValueError):
        suggest_amount_in_exact_in_cpmm(
            reserve_in=20_000,
            reserve_out=20_000,
            fee_bps=0,
            amount_in=101,
            pending_volume_same_direction=0,
            confidence_bps=9500,
            slippage_options_bps=[10, 50, 100, 300],
            max_attacker_amount_in=500,
            user_slippage_bps=10,
            max_evals=0,
            target_actions=("confirm",),
        )

    s1 = suggest_amount_in_exact_in_cpmm(
        reserve_in=20_000,
        reserve_out=20_000,
        fee_bps=0,
        amount_in=101,
        pending_volume_same_direction=0,
        confidence_bps=9500,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=500,
        user_slippage_bps=10,
        max_evals=1,
        target_actions=("confirm",),
    )
    assert len(s1) == 1
    assert s1[0].baseline_action == "typed_confirm"
    assert s1[0].baseline_reasons == ("mev_conflict",)
    assert s1[0].status == "not_found"
    assert s1[0].eval_count == 1

    s2 = suggest_amount_in_exact_in_cpmm(
        reserve_in=20_000,
        reserve_out=20_000,
        fee_bps=0,
        amount_in=101,
        pending_volume_same_direction=0,
        confidence_bps=9500,
        slippage_options_bps=[10, 50, 100, 300],
        max_attacker_amount_in=500,
        user_slippage_bps=10,
        max_evals=2,
        target_actions=("confirm",),
    )
    assert len(s2) == 1
    assert s2[0].status == "ok"
    assert s2[0].suggested_amount_in == 50
    assert s2[0].suggested_action == "confirm"
    assert s2[0].suggested_reasons is not None
    assert "mev_conflict" not in set(s2[0].suggested_reasons)


def test_exact_in_candidate_eval_internal_fault_is_not_silently_suppressed(monkeypatch: pytest.MonkeyPatch) -> None:
    original_eval = suggest_module._eval_amount

    def eval_once_then_fault(**kwargs):
        if int(kwargs["amount_in"]) == 101:
            return original_eval(**kwargs)
        raise RuntimeError("candidate evaluation fault")

    monkeypatch.setattr(suggest_module, "_eval_amount", eval_once_then_fault)

    with pytest.raises(RuntimeError, match="candidate evaluation fault"):
        suggest_amount_in_exact_in_cpmm(
            reserve_in=20_000,
            reserve_out=20_000,
            fee_bps=0,
            amount_in=101,
            pending_volume_same_direction=0,
            confidence_bps=9500,
            slippage_options_bps=[10, 50, 100, 300],
            max_attacker_amount_in=500,
            user_slippage_bps=10,
            max_evals=2,
            target_actions=("confirm",),
        )
