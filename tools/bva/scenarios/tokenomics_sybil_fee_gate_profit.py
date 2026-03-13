from __future__ import annotations

"""BMSE-style tokenomics exploration scenario.

We reuse the repo's BVA+MCMC boundary miner to find parameter boundaries where a
Sybil attacker can profit from a fee-gated reward scheme via wash trading.

Game-theoretic model (explicit):
- Each identity gets a fixed reward `reward_amount` if it meets a minimum
  `min_usage_protocol_fee` threshold.
- Usage is defined as protocol fees paid (quote-equivalent).
- Worst case for the protocol: attacker owns 100% LP, so LP fees are fully
  recaptured; irrecoverable cost is protocol fees only.
- Attacker chooses the *minimum* gross swap size that yields protocol_fee >=
  min_usage_protocol_fee under the swap fee arithmetic.

Label:
  1 if profit_per_identity > 0 else 0.
"""

from tools.bva.spec import IntDomain, Scenario
from tools.tokenomics.wash_math import sybil_profit_per_identity_fee_gated


def _profit_per_identity(
    *,
    reward_amount: int,
    min_usage_protocol_fee: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
) -> int:
    return sybil_profit_per_identity_fee_gated(
        reward_amount=int(reward_amount),
        min_usage_protocol_fee=int(min_usage_protocol_fee),
        fee_bps=int(fee_bps),
        protocol_fee_share_bps=int(protocol_fee_share_bps),
    )


SCENARIO = Scenario(
    name="tokenomics_sybil_fee_gate_profit_v1",
    fn=_profit_per_identity,
    domains={
        # Keep the ranges bounded so MCMC mining stays fast.
        "reward_amount": IntDomain(min_value=0, max_value=50, specials=(0, 1, 2, 10, 25, 50)),
        "min_usage_protocol_fee": IntDomain(min_value=0, max_value=50, specials=(0, 1, 2, 10, 25, 50)),
        "fee_bps": IntDomain(min_value=0, max_value=100, specials=(0, 1, 10, 30, 100)),
        "protocol_fee_share_bps": IntDomain(min_value=0, max_value=10_000, specials=(0, 1, 500, 2_000, 5_000, 10_000)),
    },
    label_fn=lambda profit: 1 if int(profit) > 0 else 0,
    seed=0,
)

