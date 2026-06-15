from __future__ import annotations

from types import SimpleNamespace

import pytest

from src.core import pokayoke_swap_suggest as suggest_module
from src.core.pokayoke_swap_suggest import suggest_amount_in_exact_in_cpmm


def _suggest_confirm() -> list[suggest_module.SwapAmountSuggestion]:
    return suggest_amount_in_exact_in_cpmm(
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


def _amount_in(kwargs: dict[str, object]) -> int:
    value = kwargs["amount_in"]
    if not isinstance(value, int) or isinstance(value, bool):
        raise AssertionError("test fake expected strict int amount_in")
    return value


def test_candidate_domain_errors_are_skipped(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[int] = []

    def fake_eval_amount(**kwargs: object) -> tuple[object, SimpleNamespace]:
        calls.append(_amount_in(kwargs))
        if len(calls) == 1:
            return object(), SimpleNamespace(action="typed_confirm", reasons=("mev_conflict",))
        raise ValueError("candidate outside deterministic domain")

    monkeypatch.setattr(suggest_module, "_eval_amount", fake_eval_amount)

    suggestions = _suggest_confirm()

    assert calls == [101, 50]
    assert len(suggestions) == 1
    assert suggestions[0].status == "not_found"
    assert suggestions[0].eval_count == 2
    assert suggestions[0].baseline_action == "typed_confirm"
    assert suggestions[0].baseline_reasons == ("mev_conflict",)


def test_candidate_helper_bugs_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[int] = []

    def fake_eval_amount(**kwargs: object) -> tuple[object, SimpleNamespace]:
        calls.append(_amount_in(kwargs))
        if len(calls) == 1:
            return object(), SimpleNamespace(action="typed_confirm", reasons=("mev_conflict",))
        raise RuntimeError("unexpected candidate helper bug")

    monkeypatch.setattr(suggest_module, "_eval_amount", fake_eval_amount)

    with pytest.raises(RuntimeError, match="unexpected candidate helper bug"):
        _suggest_confirm()
