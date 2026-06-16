from __future__ import annotations

import pytest

from src.integration import fast_quote_router_v1 as router_mod
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool() -> PoolState:
    return PoolState(
        pool_id="P0",
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=0,
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params="",
    )


def test_fast_quote_candidate_domain_errors_are_skipped(monkeypatch: pytest.MonkeyPatch) -> None:
    def reject_domain(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("candidate outside deterministic quote domain")

    monkeypatch.setattr(router_mod, "swap_exact_in_for_pool", reject_domain)

    assert (
        router_mod._quote_exact_in_onehop(
            _pool(),
            asset_in="A",
            asset_out="B",
            amount_in=1,
        )
        is None
    )


def test_fast_quote_candidate_programmer_errors_propagate(monkeypatch: pytest.MonkeyPatch) -> None:
    def broken_quote_helper(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("unexpected quote helper bug")

    monkeypatch.setattr(router_mod, "swap_exact_in_for_pool", broken_quote_helper)

    with pytest.raises(RuntimeError, match="unexpected quote helper bug"):
        router_mod._quote_exact_in_onehop(
            _pool(),
            asset_in="A",
            asset_out="B",
            amount_in=1,
        )
