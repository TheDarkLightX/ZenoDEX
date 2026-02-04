from __future__ import annotations

from src.kernels.python.cpmm_swap_v8 import swap_exact_in


E8 = 100_000_000
BPS_DENOM = 10_000


def _spot_price_e8(*, reserve_base: int, reserve_quote: int) -> int:
    return (reserve_quote * E8) // reserve_base


def _clamp_price_e8(*, price0_e8: int, price1_e8: int, max_move_bps: int) -> int:
    delta = (max_move_bps * price0_e8) // BPS_DENOM
    lo = price0_e8 - delta
    hi = price0_e8 + delta
    if price1_e8 < lo:
        return lo
    if price1_e8 > hi:
        return hi
    return price1_e8


def _reward_quote(*, notional_quote: int, reward_bps: int) -> int:
    return (notional_quote * reward_bps) // BPS_DENOM


def test_volume_rewards_can_subsidize_oracle_manipulation_witness() -> None:
    # Concrete witness (captured by counterexample search):
    # - Attack PnL in quote is 0 due to integer quantization,
    # - but a naive per-leg volume reward pays enough to make net profit positive.
    reserve_base = 10_000
    reserve_quote = 10_000
    fee_bps = 10
    protocol_fee_share_bps = 0
    reward_bps = 10
    max_move_bps = 500
    pos_base = -1
    trade_in_base = 6674

    price0_e8 = _spot_price_e8(reserve_base=reserve_base, reserve_quote=reserve_quote)

    # Manipulate price down: base->quote, observe, unwind quote->base.
    t1 = swap_exact_in(
        reserve_in=reserve_base,
        reserve_out=reserve_quote,
        amount_in=trade_in_base,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    quote_out = int(t1.amount_out)
    b1 = int(t1.new_reserve_in)
    q1 = int(t1.new_reserve_out)
    price1_e8 = _spot_price_e8(reserve_base=b1, reserve_quote=q1)

    t2 = swap_exact_in(
        reserve_in=q1,
        reserve_out=b1,
        amount_in=quote_out,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    base_back = int(t2.amount_out)

    base_loss = trade_in_base - base_back
    spot_cost_quote = (base_loss * price0_e8) // E8

    leg1_notional = (trade_in_base * price0_e8) // E8
    leg2_notional = quote_out
    reward_quote = _reward_quote(notional_quote=leg1_notional, reward_bps=reward_bps) + _reward_quote(
        notional_quote=leg2_notional, reward_bps=reward_bps
    )

    settle_price_e8 = _clamp_price_e8(price0_e8=price0_e8, price1_e8=price1_e8, max_move_bps=max_move_bps)
    perp_pnl_quote = (pos_base * (settle_price_e8 - price0_e8)) // E8
    net_profit_quote = perp_pnl_quote - spot_cost_quote + reward_quote

    assert price0_e8 == 100_000_000
    assert price1_e8 == 35_984_166
    assert settle_price_e8 == 95_000_000
    assert spot_cost_quote == 9
    assert reward_quote == 10
    assert perp_pnl_quote == 0
    assert net_profit_quote == 1
