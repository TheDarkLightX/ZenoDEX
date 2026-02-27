from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.core.perp_epoch import perp_epoch_isolated_v1_1_apply, perp_epoch_isolated_v1_1_initial_state
from src.kernels.python.cpmm_swap_v8 import swap_exact_in as swap_exact_in_floor
from src.kernels.python.cpmm_swap_v9 import swap_exact_in as swap_exact_in_ceil

BPS_DENOM = 10_000
E8 = 100_000_000


def _spot_price_e8(*, reserve_base: int, reserve_quote: int) -> int:
    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("empty reserves")
    return int((reserve_quote * E8) // reserve_base)


def _abs_i(x: int) -> int:
    return x if x >= 0 else -x


def _ceil_div_nonneg(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    if n < 0:
        raise ValueError("numerator must be non-negative")
    return (n + d - 1) // d


def _clamp_price_e8(*, price0_e8: int, price1_e8: int, max_move_bps: int) -> int:
    if price0_e8 < 0 or price1_e8 < 0:
        raise ValueError("negative price")
    if not (0 <= max_move_bps <= BPS_DENOM):
        raise ValueError("bad max_move_bps")
    if price0_e8 == 0:
        return int(price1_e8)

    violated = (_abs_i(price1_e8 - price0_e8) * BPS_DENOM) > (max_move_bps * price0_e8)
    if not violated:
        return int(price1_e8)

    delta = (max_move_bps * price0_e8) // BPS_DENOM
    if price1_e8 >= price0_e8:
        return int(price0_e8 + delta)
    return int(price0_e8 - delta)


def _pool_value_quote_at_price(*, reserve_base: int, reserve_quote: int, price_e8: int) -> int:
    if reserve_base < 0 or reserve_quote < 0 or price_e8 < 0:
        raise ValueError("negative inputs")
    return int(reserve_quote + ((reserve_base * price_e8) // E8))


@dataclass(frozen=True)
class OracleManipLPWitness:
    protocol_fee_share_bps: int
    lp_share_bps: int
    fee_bps: int
    max_move_bps: int
    max_pos_abs: int
    max_r: int
    reserve_base: int
    reserve_quote: int
    pos_base: int
    trade_in: int
    price0_e8: int
    price1_e8: int
    settle_price_e8: int
    spot_cost_quote: int
    lp_delta_quote: int
    perp_pnl_quote: int
    net_profit_quote: int


def _kernel_perp_settle_pnl(*, price0_e8: int, price1_e8: int, pos_base: int, max_move_bps: int, max_pos_abs: int) -> tuple[int, int]:
    st = perp_epoch_isolated_v1_1_initial_state()
    st2 = dict(st)
    st2["now_epoch"] = 1
    st2["oracle_seen"] = True
    st2["oracle_last_update_epoch"] = 0
    st2["index_price_e8"] = int(price0_e8)
    st2["clearing_price_seen"] = True
    st2["clearing_price_epoch"] = 1
    st2["clearing_price_e8"] = int(price1_e8)
    st2["max_oracle_staleness_epochs"] = 1_000_000
    st2["max_oracle_move_bps"] = int(max_move_bps)
    st2["maintenance_margin_bps"] = int(max_move_bps)
    st2["initial_margin_bps"] = int(max_move_bps)
    st2["liquidation_penalty_bps"] = 0
    st2["max_position_abs"] = int(max_pos_abs)
    st2["breaker_active"] = False
    st2["breaker_last_trigger_epoch"] = 0
    st2["position_base"] = int(pos_base)
    st2["entry_price_e8"] = int(price0_e8) if pos_base != 0 else 0
    st2["collateral_quote"] = 1_000_000_000

    res = perp_epoch_isolated_v1_1_apply(state=st2, action="settle_epoch", params={})
    if not res.ok or res.state is None:
        raise ValueError(f"perp settle failed: {res.error or res.code or ''}".strip())
    post = res.state
    settle_price = int(post.get("index_price_e8", 0))
    pnl = int(post.get("collateral_quote", 0)) - int(st2.get("collateral_quote", 0))
    return settle_price, pnl


def _eval_attack(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    lp_share_bps: int,
    pos_base: int,
    trade_in: int,
    max_move_bps: int,
    max_pos_abs: int,
    max_r: int,
    confirm_with_kernel: bool,
    protocol_fee_rounding: str,
) -> OracleManipLPWitness:
    if not (0 <= protocol_fee_share_bps <= BPS_DENOM):
        raise ValueError("bad protocol_fee_share_bps")
    if not (0 <= lp_share_bps <= BPS_DENOM):
        raise ValueError("bad lp_share_bps")
    pfr = str(protocol_fee_rounding).strip().lower()
    if pfr not in {"floor", "ceil"}:
        raise ValueError("bad protocol_fee_rounding")
    swap_exact_in = swap_exact_in_floor if pfr == "floor" else swap_exact_in_ceil

    price0 = _spot_price_e8(reserve_base=reserve_base, reserve_quote=reserve_quote)
    pool_v0 = _pool_value_quote_at_price(reserve_base=reserve_base, reserve_quote=reserve_quote, price_e8=price0)

    if pos_base > 0:
        t1 = swap_exact_in(
            reserve_in=int(reserve_quote),
            reserve_out=int(reserve_base),
            amount_in=int(trade_in),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        base_out = int(t1.amount_out)
        q1 = int(t1.new_reserve_in)
        b1 = int(t1.new_reserve_out)
        price1 = _spot_price_e8(reserve_base=b1, reserve_quote=q1)

        t2 = swap_exact_in(
            reserve_in=int(b1),
            reserve_out=int(q1),
            amount_in=int(base_out),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        quote_back = int(t2.amount_out)
        b2 = int(t2.new_reserve_in)
        q2 = int(t2.new_reserve_out)
        spot_cost_quote = int(trade_in - quote_back)
        if spot_cost_quote < 0:
            raise ValueError("negative roundtrip cost (unexpected)")
    else:
        t1 = swap_exact_in(
            reserve_in=int(reserve_base),
            reserve_out=int(reserve_quote),
            amount_in=int(trade_in),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        quote_out = int(t1.amount_out)
        b1 = int(t1.new_reserve_in)
        q1 = int(t1.new_reserve_out)
        price1 = _spot_price_e8(reserve_base=b1, reserve_quote=q1)

        t2 = swap_exact_in(
            reserve_in=int(q1),
            reserve_out=int(b1),
            amount_in=int(quote_out),
            fee_bps=int(fee_bps),
            protocol_fee_share_bps=int(protocol_fee_share_bps),
        )
        base_back = int(t2.amount_out)
        q2 = int(t2.new_reserve_in)
        b2 = int(t2.new_reserve_out)
        base_loss = int(trade_in - base_back)
        if base_loss < 0:
            raise ValueError("negative base_loss (unexpected)")
        spot_cost_quote = int((base_loss * price0) // E8)

    pool_v2 = _pool_value_quote_at_price(reserve_base=b2, reserve_quote=q2, price_e8=price0)
    pool_delta = int(pool_v2 - pool_v0)
    lp_delta = int((pool_delta * lp_share_bps) // BPS_DENOM)

    settle_fast = _clamp_price_e8(price0_e8=price0, price1_e8=price1, max_move_bps=max_move_bps)
    pnl_fast = int((pos_base * (settle_fast - price0)) // E8)
    settle, pnl = (settle_fast, pnl_fast)
    if confirm_with_kernel:
        settle, pnl = _kernel_perp_settle_pnl(
            price0_e8=price0, price1_e8=price1, pos_base=pos_base, max_move_bps=max_move_bps, max_pos_abs=max_pos_abs
        )

    net = int(pnl - spot_cost_quote + lp_delta)
    return OracleManipLPWitness(
        protocol_fee_share_bps=int(protocol_fee_share_bps),
        lp_share_bps=int(lp_share_bps),
        fee_bps=int(fee_bps),
        max_move_bps=int(max_move_bps),
        max_pos_abs=int(max_pos_abs),
        max_r=int(max_r),
        reserve_base=int(reserve_base),
        reserve_quote=int(reserve_quote),
        pos_base=int(pos_base),
        trade_in=int(trade_in),
        price0_e8=int(price0),
        price1_e8=int(price1),
        settle_price_e8=int(settle),
        spot_cost_quote=int(spot_cost_quote),
        lp_delta_quote=int(lp_delta),
        perp_pnl_quote=int(pnl),
        net_profit_quote=int(net),
    )


def _min_trade_in_for_fee(*, fee_bps: int) -> int:
    if fee_bps <= 0:
        return 1
    # Require net_in > 0:
    #   amount_in > ceil(amount_in * fee_bps / 10_000)
    return _ceil_div_nonneg(BPS_DENOM, BPS_DENOM - fee_bps)


def find_profitable_attack(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
    lp_share_bps: int,
    max_r: int,
    max_pos_abs: int,
    max_move_bps: int,
    target_profit_quote: int,
    protocol_fee_rounding: str = "floor",
) -> OracleManipLPWitness | None:
    if not (0 <= fee_bps < BPS_DENOM):
        raise ValueError("fee_bps out of range")
    if not (1 <= max_r):
        raise ValueError("bad max_r")
    if max_pos_abs < 1:
        raise ValueError("bad max_pos_abs")

    min_trade_in = _min_trade_in_for_fee(fee_bps=fee_bps)

    for abs_pos in range(1, max_pos_abs + 1):
        for sign in (-1, 1):
            pos = int(sign * abs_pos)
            for trade_in in range(min_trade_in, max_r + 1):
                try:
                    w = _eval_attack(
                        reserve_base=reserve_base,
                        reserve_quote=reserve_quote,
                        fee_bps=fee_bps,
                        protocol_fee_share_bps=protocol_fee_share_bps,
                        lp_share_bps=lp_share_bps,
                        pos_base=pos,
                        trade_in=trade_in,
                        max_move_bps=max_move_bps,
                        max_pos_abs=max_pos_abs,
                        max_r=max_r,
                        confirm_with_kernel=False,
                        protocol_fee_rounding=protocol_fee_rounding,
                    )
                except Exception:
                    continue
                if w.net_profit_quote < target_profit_quote:
                    continue
                # Confirm only when potentially profitable.
                try:
                    w2 = _eval_attack(
                        reserve_base=reserve_base,
                        reserve_quote=reserve_quote,
                        fee_bps=fee_bps,
                        protocol_fee_share_bps=protocol_fee_share_bps,
                        lp_share_bps=lp_share_bps,
                        pos_base=pos,
                        trade_in=trade_in,
                        max_move_bps=max_move_bps,
                        max_pos_abs=max_pos_abs,
                        max_r=max_r,
                        confirm_with_kernel=True,
                        protocol_fee_rounding=protocol_fee_rounding,
                    )
                except Exception:
                    continue
                if w2.net_profit_quote >= target_profit_quote:
                    return w2
    return None


def parse_int_list(spec: str) -> list[int]:
    out: list[int] = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    return out


def main() -> int:
    p = argparse.ArgumentParser(description="Sweep LP-assisted oracle manipulation over protocol_fee_share_bps.")
    p.add_argument("--reserve-base", type=int, default=10_000)
    p.add_argument("--reserve-quote", type=int, default=10_000)
    p.add_argument("--fee-bps", type=int, default=10)
    p.add_argument("--lp-share-bps", type=int, default=10_000)
    p.add_argument("--max-r", type=int, default=20_000)
    p.add_argument("--max-pos-abs", type=int, default=50)
    p.add_argument("--max-move-bps", type=int, default=500)
    p.add_argument("--target-profit-quote", type=int, default=1)
    p.add_argument("--protocol-fee-rounding", choices=("floor", "ceil"), default="floor")
    p.add_argument(
        "--protocol-fee-share-bps",
        default="0,5000,9999,10000",
        help="Comma-separated list of protocol_fee_share_bps to test (default: 0,5000,9999,10000).",
    )
    args = p.parse_args()

    shares = parse_int_list(args.protocol_fee_share_bps)
    rows: list[dict[str, Any]] = []
    for s in shares:
        w = find_profitable_attack(
            reserve_base=args.reserve_base,
            reserve_quote=args.reserve_quote,
            fee_bps=args.fee_bps,
            protocol_fee_share_bps=s,
            lp_share_bps=args.lp_share_bps,
            max_r=args.max_r,
            max_pos_abs=args.max_pos_abs,
            max_move_bps=args.max_move_bps,
            target_profit_quote=args.target_profit_quote,
            protocol_fee_rounding=str(args.protocol_fee_rounding),
        )
        rows.append(
            {
                "protocol_fee_share_bps": int(s),
                "attack_found": w is not None,
                "witness": None if w is None else w.__dict__,
            }
        )

    print(json.dumps({"ok": True, "rows": rows}, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
