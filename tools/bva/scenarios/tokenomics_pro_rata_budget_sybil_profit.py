from __future__ import annotations

"""BMSE-style tokenomics exploration scenario: pro-rata epoch budgets.

We mine parameter boundaries where a Sybil attacker can profit from a pro-rata
budgeted mining program by wash trading.

Model:
- Mining budget B is distributed pro-rata by usage share.
- Usage is protocol fees paid (quote-equivalent at p0) by a deterministic 2-leg
  wash trade (quote->base->quote) under CPMM v8 semantics.
- Other usage U_other is exogenous (honest activity).
- POL reduces attacker LP share: attacker_lp_share_bps = 10_000 - pol_share_bps.
- Attacker best response is a bounded scan over trade sizes; label is 1 if
  max_profit > 0 else 0.
"""

from tools.bva.spec import IntDomain, Scenario
from tools.tokenomics.pro_rata_budget import max_sybil_profit_pro_rata_budget


def _label(
    *,
    budget_quote: int,
    other_usage_quote: int,
    pol_share_bps: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    max_trade_in_quote: int,
    scan_step: int,
    max_cycles: int,
) -> int:
    res = max_sybil_profit_pro_rata_budget(
        reserve_base=10_000,
        reserve_quote=10_000,
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        pol_share_bps=int(pol_share_bps),
        other_usage_quote=int(other_usage_quote),
        budget_quote=int(budget_quote),
        max_trade_in_quote=int(max_trade_in_quote),
        scan_step=int(scan_step),
        max_cycles=int(max_cycles),
    )
    if not res.found or res.best_profit_quote_at_p0 is None:
        return 0
    return 1 if res.best_profit_quote_at_p0 > 0 else 0


SCENARIO = Scenario(
    name="tokenomics_pro_rata_budget_sybil_profit_v1",
    fn=_label,
    fixed_kwargs={
        # Keep boundary mining fast; refine later with stricter bounds if needed.
        "max_trade_in_quote": 5_000,
        "scan_step": 16,
        "max_cycles": 5,
    },
    domains={
        # Keep bounded for fast boundary mining.
        "budget_quote": IntDomain(min_value=0, max_value=200, specials=(0, 1, 2, 5, 10, 50, 100, 200)),
        "other_usage_quote": IntDomain(min_value=0, max_value=500, specials=(0, 1, 2, 10, 50, 100, 500)),
        "pol_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 500, 2_000, 5_000, 10_000)),
        "fee_bps": IntDomain(min_value=0, max_value=100, specials=(0, 1, 10, 30, 100)),
        "protocol_fee_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 500, 2_000, 5_000, 10_000)),
    },
    label_fn=lambda x: int(x),
    seed=0,
    max_contexts=8,
    samples_per_context=48,
    # A bit of cross-field sampling since profit can be sensitive to other_usage and budget.
    random_contexts=8,
    random_context_budget=64,
)
