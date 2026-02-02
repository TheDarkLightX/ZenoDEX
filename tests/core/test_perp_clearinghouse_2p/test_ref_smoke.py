"""Smoke tests for the generated reference model of the 2-party clearinghouse perp kernel."""

from __future__ import annotations

import sys
from pathlib import Path


# Import the generated reference oracle (produced from the YAML kernel spec).
# We load it by path so the test does not depend on any packaging/install step.
_REF_DIR = Path(__file__).resolve().parents[3] / "generated" / "perp_python"
if str(_REF_DIR) not in sys.path:
    sys.path.insert(0, str(_REF_DIR))

import perp_epoch_clearinghouse_2p_v0_1_ref as ref  # type: ignore  # noqa: E402


def _apply(state: ref.State, tag: str, **kwargs):  # type: ignore[name-defined]
    cmd = ref.Command(tag=tag, args=kwargs)
    res = ref.step(state, cmd)
    assert res.ok, res.error
    assert res.state is not None
    ok, failed = ref.check_invariants(res.state)
    assert ok, f"post-invariant violated: {failed}"
    assert res.effects is not None
    return res.state, dict(res.effects)


def test_settlement_can_trigger_deterministic_liquidation_and_penalty():
    s = ref.init_state()

    # Initialize oracle (first settlement sets oracle_seen + index price).
    s, _ = _apply(s, "advance_epoch", delta=1)
    s, _ = _apply(s, "publish_clearing_price", price_e8=100_000_000)
    s, eff = _apply(s, "settle_epoch")
    assert eff["liquidated"] is False
    assert s.index_price_e8 == 100_000_000

    # Fund both accounts (quote-e8 collateral).
    s, _ = _apply(s, "deposit_collateral_a", amount_e8=10_000_000_000, auth_ok=True)
    s, _ = _apply(s, "deposit_collateral_b", amount_e8=10_000_000_000, auth_ok=True)
    assert s.net_deposited_e8 == 20_000_000_000
    assert s.collateral_e8_a + s.collateral_e8_b + s.fee_pool_e8 == s.net_deposited_e8

    # Open a matched position pair.
    s, _ = _apply(s, "set_position_pair", new_position_base_a=1000, auth_ok=True)
    assert s.position_base_b == -s.position_base_a
    assert s.entry_price_e8_a == s.index_price_e8
    assert s.entry_price_e8_b == s.index_price_e8

    # Move the clearing price up by +5%: the short side drops below maintenance and is liquidated.
    s, _ = _apply(s, "advance_epoch", delta=1)
    s, _ = _apply(s, "publish_clearing_price", price_e8=105_000_000)
    s, eff = _apply(s, "settle_epoch")

    assert eff["liquidated"] is True
    assert s.position_base_a == 0
    assert s.position_base_b == 0
    assert s.entry_price_e8_a == 0
    assert s.entry_price_e8_b == 0

    # Exact quote-e8 accounting for this scenario:
    # - long gains: 1000 * (105_000_000 - 100_000_000) = +5_000_000_000
    # - short loses: -5_000_000_000 (but stays nonnegative)
    # - liquidation penalty: ceil(|pos| * price * 50bps / 10_000) = 525_000_000
    assert s.collateral_e8_a == 15_000_000_000
    assert s.collateral_e8_b == 4_475_000_000
    assert s.fee_pool_e8 == 525_000_000
    assert s.collateral_e8_a + s.collateral_e8_b + s.fee_pool_e8 == s.net_deposited_e8
