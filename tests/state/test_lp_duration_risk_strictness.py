import pytest

from src.state import BalanceTable, LPTable
from src.state.state_root import compute_state_root


def test_state_root_rejects_corrupt_internal_lp_churn_tier_before_encoding() -> None:
    pk = "0x" + "aa" * 48
    pool_id = "0x" + "11" * 32
    lp = LPTable()
    lp._churn_tiers[(pk, pool_id)] = True  # type: ignore[assignment]

    with pytest.raises(TypeError, match="LP churn tier must be an int"):
        compute_state_root(balances=BalanceTable(), pools={}, lp_balances=lp)
