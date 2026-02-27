from __future__ import annotations

"""BMSE-style tokenomics scenario: POL share vs Sybil profitability (wash-farming).

Purpose:
- Mine boundary cases where a per-identity mining reward becomes Sybil-profitable.
- Explicitly include protocol-owned liquidity (POL) as a parameter that reduces
  attacker LP share (worst case: attacker controls all non-protocol LP).

Model (bounded, explicit):
- Eligibility requires usage_score >= min_usage_quote, where usage_score is the
  total protocol fees paid (quote-equivalent at p0) by a deterministic 2-leg
  wash trade under CPMM v8.
- Per identity reward is fixed: base_reward_per_identity_quote.
- POL is modelled as a fixed LP share pol_share_bps (0..10000). Attacker LP share:
    attacker_lp_share_bps = 10000 - pol_share_bps
- Attacker best response: choose minimum-cost wash trade (bounded by max_trade_in_quote)
  that reaches the usage threshold.

Label:
  1 if profit_per_identity > 0 else 0.

Notes:
- This is a stress-test mechanism (fixed per-identity rewards). The goal is to
  surface counterexamples and quantify how POL shifts the boundary.
"""

from fractions import Fraction

from tools.bva.spec import IntDomain, Scenario
from tools.tokenomics.wash_trade import min_cost_to_reach_usage_fee_gated


def _profit_per_identity(
    *,
    base_reward_per_identity_quote: int,
    min_usage_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    pol_share_bps: int,
) -> Fraction:
    attacker_lp_share_bps = 10_000 - int(pol_share_bps)
    if attacker_lp_share_bps < 0:
        attacker_lp_share_bps = 0
    if attacker_lp_share_bps > 10_000:
        attacker_lp_share_bps = 10_000

    r = min_cost_to_reach_usage_fee_gated(
        reserve_base=10_000,
        reserve_quote=10_000,
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        min_usage_quote=int(min_usage_quote),
        attacker_lp_share_bps=int(attacker_lp_share_bps),
        max_trade_in_quote=8_000,  # bounded for mining speed
        local_search_window=32,
    )
    if not r.found or r.best_cost_quote_at_p0 is None:
        # If the identity cannot meet the threshold within bounds, it cannot claim.
        return Fraction(0, 1)
    return Fraction(int(base_reward_per_identity_quote), 1) - r.best_cost_quote_at_p0


SCENARIO = Scenario(
    name="tokenomics_pol_share_sybil_profit_v1",
    fn=_profit_per_identity,
    domains={
        "base_reward_per_identity_quote": IntDomain(min_value=0, max_value=20, specials=(0, 1, 2, 5, 10, 20)),
        "min_usage_quote": IntDomain(min_value=0, max_value=20, specials=(0, 1, 2, 5, 10, 20)),
        "fee_bps": IntDomain(min_value=0, max_value=30, specials=(0, 1, 10, 30)),
        "protocol_fee_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 5_000, 9_999, 10_000)),
        "pol_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 10, 100, 1_000, 5_000, 9_000, 9_999, 10_000)),
    },
    label_fn=lambda profit: 1 if profit > 0 else 0,
    seed=0,
    max_contexts=8,
    samples_per_context=48,
    exhaustive_threshold=8192,
)

