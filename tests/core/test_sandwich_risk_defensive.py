from __future__ import annotations

import pytest

from src.core import sandwich_risk


def test_cpmm_domain_errors_still_return_none(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_swap(**_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("bad CPMM domain")

    monkeypatch.setattr(sandwich_risk, "swap_exact_in", reject_swap)

    assert (
        sandwich_risk.sandwich_profit_exact_in_cpmm(
            reserve_in=1_000,
            reserve_out=1_000,
            fee_bps=0,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )
        is None
    )


def test_cpmm_helper_bugs_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_swap(**_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("swap helper bug")

    monkeypatch.setattr(sandwich_risk, "swap_exact_in", broken_swap)

    with pytest.raises(RuntimeError, match="swap helper bug"):
        sandwich_risk.sandwich_profit_exact_in_cpmm(
            reserve_in=1_000,
            reserve_out=1_000,
            fee_bps=0,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )


def test_dynamic_fee_domain_errors_still_return_none() -> None:
    def reject_fee(_reserve_in: int, _reserve_out: int, _amount_in: int) -> int:
        raise ValueError("bad fee domain")

    assert (
        sandwich_risk.sandwich_profit_exact_in_cpmm_dynamic_fee(
            reserve_in=1_000,
            reserve_out=1_000,
            fee_bps_fn=reject_fee,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )
        is None
    )


def test_dynamic_fee_helper_bugs_propagate() -> None:
    def broken_fee(_reserve_in: int, _reserve_out: int, _amount_in: int) -> int:
        raise RuntimeError("fee helper bug")

    with pytest.raises(RuntimeError, match="fee helper bug"):
        sandwich_risk.sandwich_profit_exact_in_cpmm_dynamic_fee(
            reserve_in=1_000,
            reserve_out=1_000,
            fee_bps_fn=broken_fee,
            victim_amount_in=50,
            victim_min_out=1,
            attacker_amount_in=1,
        )


def test_bounded_dynamic_fee_scan_helper_bugs_propagate() -> None:
    def fee_bps(_reserve_in: int, _reserve_out: int, amount_in: int) -> int:
        if amount_in == 0:
            raise RuntimeError("scan fee helper bug")
        return 0

    with pytest.raises(RuntimeError, match="scan fee helper bug"):
        sandwich_risk.max_sandwich_profit_exact_in_cpmm_bounded_dynamic_fee(
            reserve_in=1_000,
            reserve_out=1_000,
            fee_bps_fn=fee_bps,
            victim_amount_in=50,
            victim_min_out=1,
            max_attacker_amount_in=1,
        )
