from __future__ import annotations

from src.state.perps_funding_transitions import apply_isolated_funding_auto_v1
from src.state.perps_state_transitions import (
    IsolatedPerpTransitionCodeV1,
    IsolatedPerpTransitionRejectV1,
)
from tests.state.test_perps_epoch_transitions import (
    _ALICE,
    _BOB,
    _account,
    _exact_market,
)


def test_funding_reject_code_and_path_ignore_source_account_insertion_order() -> None:
    accounts = {
        _ALICE: _account(position_base=1_000_000, collateral_quote=0),
        _BOB: _account(position_base=1_000_000, collateral_quote=0),
    }
    forward = _exact_market(accounts)
    reverse = _exact_market(dict(reversed(tuple(accounts.items()))))

    forward_result = apply_isolated_funding_auto_v1(
        forward,
        operator_authorized=True,
    )
    reverse_result = apply_isolated_funding_auto_v1(
        reverse,
        operator_authorized=True,
    )

    expected = IsolatedPerpTransitionRejectV1(
        IsolatedPerpTransitionCodeV1.KERNEL_REJECT,
        ("kernel", "accounts", _ALICE),
        "guard",
    )
    assert forward_result == expected
    assert reverse_result == expected
    assert not hasattr(forward_result, "market")
    assert not hasattr(reverse_result, "market")
