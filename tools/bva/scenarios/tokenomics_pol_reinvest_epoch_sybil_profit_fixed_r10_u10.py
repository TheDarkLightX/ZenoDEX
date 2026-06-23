from __future__ import annotations

"""BMSE-style tokenomics scenario: fixed reward/usage; mine boundaries in POL+fee params.

Fixed:
- base_reward_per_identity_quote = 10
- min_usage_quote = 10

Variable:
- fee_bps
- protocol_fee_share_bps
- reinvest_bps
- epochs

Label:
  1 if profit_per_identity > 0 else 0, where profit is computed using attacker
  best-response wash-farming cost after POL has compounded for N epochs.
"""

from functools import lru_cache
from fractions import Fraction

from tools.bva.spec import IntDomain, Scenario
from tools.tokenomics.pol_reinvest_sim import simulate_pol_reinvest
from tools.tokenomics.wash_trade import min_cost_to_reach_usage_fee_gated


@lru_cache(maxsize=4096)
def _pol_state_after_epochs(
    *,
    initial_reserve: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    gross_in: int,
    epochs: int,
    reinvest_bps: int,
) -> tuple[int, int, int]:
    rows = simulate_pol_reinvest(
        initial_reserve=int(initial_reserve),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        gross_in=int(gross_in),
        epochs=int(epochs),
        reinvest_bps=int(reinvest_bps),
    )
    last = rows[-1]
    return (int(last.reserve0), int(last.reserve1), int(last.protocol_lp_bps))


def _profit_per_identity(
    *,
    fee_bps: int,
    protocol_fee_share_bps: int,
    reinvest_bps: int,
    epochs: int,
) -> Fraction:
    base_reward_per_identity_quote = 10
    min_usage_quote = 10

    initial_reserve = 10_000
    gross_in = 1_000
    if int(epochs) <= 0:
        return Fraction(0, 1)

    r0, r1, protocol_lp_bps = _pol_state_after_epochs(
        initial_reserve=int(initial_reserve),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        gross_in=int(gross_in),
        epochs=int(epochs),
        reinvest_bps=int(reinvest_bps),
    )

    attacker_lp_share_bps = 10_000 - int(protocol_lp_bps)
    if attacker_lp_share_bps < 0:
        attacker_lp_share_bps = 0
    if attacker_lp_share_bps > 10_000:
        attacker_lp_share_bps = 10_000

    res = min_cost_to_reach_usage_fee_gated(
        reserve_base=int(r0),
        reserve_quote=int(r1),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        min_usage_quote=int(min_usage_quote),
        attacker_lp_share_bps=int(attacker_lp_share_bps),
        max_trade_in_quote=8_000,
        local_search_window=32,
    )
    if not res.found or res.best_cost_quote_at_p0 is None:
        return Fraction(0, 1)
    return Fraction(int(base_reward_per_identity_quote), 1) - res.best_cost_quote_at_p0


SCENARIO = Scenario(
    name="tokenomics_pol_reinvest_epoch_sybil_profit_fixed_r10_u10_v1",
    fn=_profit_per_identity,
    domains={
        "fee_bps": IntDomain(min_value=0, max_value=100, specials=(0, 1, 10, 30, 100)),
        "protocol_fee_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 2_000, 5_000, 9_999, 10_000)),
        "reinvest_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 2_500, 5_000, 10_000)),
        "epochs": IntDomain(min_value=1, max_value=50, specials=(1, 2, 5, 10, 20, 50)),
    },
    label_fn=lambda profit: 1 if profit > 0 else 0,
    seed=0,
    max_contexts=12,
    samples_per_context=96,
    exhaustive_threshold=8192,
    random_contexts=12,
    random_context_budget=256,
)

