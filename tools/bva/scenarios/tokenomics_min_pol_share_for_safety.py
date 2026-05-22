from __future__ import annotations

"""BMSE-style scenario: compute minimal POL share required for mining safety.

Function output:
  min_pol_share_bps (0..9999) if possible, else 10000 to denote "impossible".

Label (optional):
  Not used here; we mine boundary values in the scalar output itself via repr/labeling.
"""

from tools.bva.spec import IntDomain, Scenario
from tools.tokenomics.pol_share_required_for_safety import min_pol_share_bps_for_safety


def _min_pol_share_for_safety(
    *,
    base_reward_quote: int,
    min_usage_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
) -> int:
    pol_min, _, _ = min_pol_share_bps_for_safety(
        reserve_base=10_000,
        reserve_quote=10_000,
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        min_usage_quote=int(min_usage_quote),
        base_reward_per_identity_quote=int(base_reward_quote),
        max_trade_in_quote=20_000,
    )
    return 10_000 if pol_min is None else int(pol_min)


SCENARIO = Scenario(
    name="tokenomics_min_pol_share_for_safety_v1",
    fn=_min_pol_share_for_safety,
    domains={
        "base_reward_quote": IntDomain(min_value=0, max_value=20, specials=(0, 1, 2, 5, 10, 11, 15, 20)),
        "min_usage_quote": IntDomain(min_value=0, max_value=20, specials=(0, 1, 2, 5, 10, 20)),
        "fee_bps": IntDomain(min_value=0, max_value=30, specials=(0, 1, 10, 30)),
        "protocol_fee_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 2_000, 5_000, 9_999, 10_000)),
    },
    seed=0,
    max_contexts=12,
    samples_per_context=64,
)

