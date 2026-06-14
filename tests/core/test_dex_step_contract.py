from __future__ import annotations

import pytest

import src.core.dex as dex
from src.core.dex import DexConfig, DexState
from src.state import BalanceTable, LPTable


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def test_step_converts_expected_domain_failure_to_result(monkeypatch: pytest.MonkeyPatch) -> None:
    def invalid_settlement(**_kwargs):
        raise ValueError("expected domain failure")

    monkeypatch.setattr(dex, "compute_settlement", invalid_settlement)

    result = dex.step(DexConfig(), _empty_state(), [])

    assert not result.ok
    assert result.error == "expected domain failure"


def test_step_propagates_unexpected_implementation_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_settlement(**_kwargs):
        raise RuntimeError("unexpected settlement computation fault")

    monkeypatch.setattr(dex, "compute_settlement", broken_settlement)

    with pytest.raises(RuntimeError, match="unexpected settlement computation fault"):
        dex.step(DexConfig(), _empty_state(), [])


def test_candidate_step_propagates_unexpected_apply_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_apply(*_args, **_kwargs):
        raise RuntimeError("unexpected candidate apply fault")

    monkeypatch.setattr(dex, "_validate_and_apply_settlement", broken_apply)

    with pytest.raises(RuntimeError, match="unexpected candidate apply fault"):
        dex.step_with_candidate_settlement(
            DexConfig(),
            _empty_state(),
            [],
            candidate_settlement=object(),  # type: ignore[arg-type]
        )
