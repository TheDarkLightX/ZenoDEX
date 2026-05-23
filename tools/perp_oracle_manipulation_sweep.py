from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


E8 = 100_000_000
BPS_DENOM = 10_000


@dataclass(frozen=True)
class BestAttack:
    ok: bool
    net_profit_quote: int
    spot_cost_quote: int
    perp_pnl_quote: int
    reserve_base: int
    reserve_quote: int
    fee_bps: int
    max_move_bps: int
    max_pos_abs: int
    pos_base: int
    trade_in: int
    price0_e8: int
    price1_e8: int
    settle_price_e8: int


def _abs_i(x: int) -> int:
    return x if x >= 0 else -x


def _ceil_div_nonneg(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    if n < 0:
        raise ValueError("numerator must be non-negative")
    return (n + d - 1) // d


def _cpmm_fee_total(*, gross_in: int, fee_bps: int) -> int:
    return _ceil_div_nonneg(gross_in * fee_bps, BPS_DENOM)


def _cpmm_swap_exact_in_inlined(*, reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int) -> tuple[int, int, int]:
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError("empty reserves")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if not (0 <= fee_bps < BPS_DENOM):
        raise ValueError("bad fee_bps")

    fee_total = _cpmm_fee_total(gross_in=amount_in, fee_bps=fee_bps)
    net_in = amount_in - fee_total
    if net_in <= 0:
        raise ValueError("net_in must be positive after fees")

    amount_out = (reserve_out * net_in) // (reserve_in + net_in)
    if amount_out < 0 or amount_out >= reserve_out:
        raise ValueError("invalid amount_out")

    new_reserve_in = reserve_in + amount_in  # fee stays in the pool (protocol fee share ignored)
    new_reserve_out = reserve_out - amount_out
    if new_reserve_in <= 0 or new_reserve_out <= 0:
        raise ValueError("invalid post reserves")
    return int(amount_out), int(new_reserve_in), int(new_reserve_out)


def _spot_price_e8(*, reserve_base: int, reserve_quote: int) -> int:
    if reserve_base <= 0 or reserve_quote <= 0:
        raise ValueError("empty reserves")
    return int((reserve_quote * E8) // reserve_base)


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


@dataclass(frozen=True)
class AttackEval:
    price0_e8: int
    price1_e8: int
    settle_price_e8: int
    spot_cost_quote: int
    perp_pnl_quote: int
    net_profit_quote: int


def _eval_attack_inlined(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    pos_base: int,
    trade_in: int,
    max_move_bps: int,
) -> AttackEval:
    price0 = _spot_price_e8(reserve_base=reserve_base, reserve_quote=reserve_quote)

    if pos_base > 0:
        # Manipulate price UP: swap quote->base, observe price, then unwind base->quote.
        base_out, q1, b1 = _cpmm_swap_exact_in_inlined(
            reserve_in=reserve_quote, reserve_out=reserve_base, amount_in=trade_in, fee_bps=fee_bps
        )
        price1 = _spot_price_e8(reserve_base=b1, reserve_quote=q1)

        quote_back, _b2, _q2 = _cpmm_swap_exact_in_inlined(
            reserve_in=b1, reserve_out=q1, amount_in=base_out, fee_bps=fee_bps
        )
        cost_quote = int(trade_in - quote_back)
        if cost_quote < 0:
            raise ValueError("negative roundtrip cost (unexpected)")
    else:
        # Manipulate price DOWN: swap base->quote, observe price, then unwind quote->base.
        quote_out, b1, q1 = _cpmm_swap_exact_in_inlined(
            reserve_in=reserve_base, reserve_out=reserve_quote, amount_in=trade_in, fee_bps=fee_bps
        )
        price1 = _spot_price_e8(reserve_base=b1, reserve_quote=q1)

        base_back, _q2, _b2 = _cpmm_swap_exact_in_inlined(
            reserve_in=q1, reserve_out=b1, amount_in=quote_out, fee_bps=fee_bps
        )
        base_loss = int(trade_in - base_back)
        if base_loss < 0:
            raise ValueError("negative base_loss (unexpected)")
        cost_quote = int((base_loss * price0) // E8)

    settle = _clamp_price_e8(price0_e8=price0, price1_e8=price1, max_move_bps=max_move_bps)
    pnl = int((pos_base * (settle - price0)) // E8)
    net = int(pnl - cost_quote)
    return AttackEval(
        price0_e8=int(price0),
        price1_e8=int(price1),
        settle_price_e8=int(settle),
        spot_cost_quote=int(cost_quote),
        perp_pnl_quote=int(pnl),
        net_profit_quote=int(net),
    )


def _parse_int_list(csv: str) -> list[int]:
    out: list[int] = []
    for part in str(csv).split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty list")
    return out


def _best_attack_key(a: BestAttack) -> tuple[int, int, int, int, int]:
    # Primary: maximize net profit.
    # Ties: minimize abs(pos), then prefer short (-) before long (+), then minimize trade_in, then minimize price1.
    sign_rank = 0 if a.pos_base < 0 else 1
    return (int(a.net_profit_quote), -int(_abs_i(a.pos_base)), -int(sign_rank), -int(a.trade_in), -int(a.price1_e8))


def _find_best_attack(
    *,
    reserve_base: int,
    reserve_quote: int,
    fee_bps: int,
    max_move_bps: int,
    max_pos_abs: int,
    max_trade_in: int,
) -> BestAttack:
    price0_e8 = int((reserve_quote * E8) // reserve_base)

    if fee_bps >= BPS_DENOM:
        return BestAttack(
            ok=False,
            net_profit_quote=0,
            spot_cost_quote=0,
            perp_pnl_quote=0,
            reserve_base=reserve_base,
            reserve_quote=reserve_quote,
            fee_bps=fee_bps,
            max_move_bps=max_move_bps,
            max_pos_abs=max_pos_abs,
            pos_base=0,
            trade_in=0,
            price0_e8=price0_e8,
            price1_e8=0,
            settle_price_e8=0,
        )

    min_trade_in = _ceil_div_nonneg(BPS_DENOM, BPS_DENOM - int(fee_bps)) if fee_bps > 0 else 1

    best: BestAttack | None = None
    for abs_pos in range(1, int(max_pos_abs) + 1):
        for sign in (-1, 1):
            pos = int(sign * abs_pos)
            for trade_in in range(int(min_trade_in), int(max_trade_in) + 1):
                try:
                    ev = _eval_attack_inlined(
                        reserve_base=int(reserve_base),
                        reserve_quote=int(reserve_quote),
                        fee_bps=int(fee_bps),
                        pos_base=int(pos),
                        trade_in=int(trade_in),
                        max_move_bps=int(max_move_bps),
                    )
                except Exception:
                    continue
                cand = BestAttack(
                    ok=True,
                    net_profit_quote=int(ev.net_profit_quote),
                    spot_cost_quote=int(ev.spot_cost_quote),
                    perp_pnl_quote=int(ev.perp_pnl_quote),
                    reserve_base=int(reserve_base),
                    reserve_quote=int(reserve_quote),
                    fee_bps=int(fee_bps),
                    max_move_bps=int(max_move_bps),
                    max_pos_abs=int(max_pos_abs),
                    pos_base=int(pos),
                    trade_in=int(trade_in),
                    price0_e8=int(ev.price0_e8),
                    price1_e8=int(ev.price1_e8),
                    settle_price_e8=int(ev.settle_price_e8),
                )
                if best is None or _best_attack_key(cand) > _best_attack_key(best):
                    best = cand

    if best is None:
        return BestAttack(
            ok=False,
            net_profit_quote=0,
            spot_cost_quote=0,
            perp_pnl_quote=0,
            reserve_base=int(reserve_base),
            reserve_quote=int(reserve_quote),
            fee_bps=int(fee_bps),
            max_move_bps=int(max_move_bps),
            max_pos_abs=int(max_pos_abs),
            pos_base=0,
            trade_in=0,
            price0_e8=int(price0_e8),
            price1_e8=0,
            settle_price_e8=0,
        )
    return best


def main() -> int:
    ap = argparse.ArgumentParser(description="Deterministic sweep: oracle manipulation profitability (bounded)")
    ap.add_argument("--reserves", type=str, default="80,100,150,200", help="comma-separated reserve values (base=quote=r)")
    ap.add_argument("--fee-bps", type=str, default="0,5,10,20,30,40,50", help="comma-separated fee bps values")
    ap.add_argument("--max-move-bps", type=str, default="50,100,200,500", help="comma-separated clamp max oracle move bps")
    ap.add_argument("--max-pos-abs", type=str, default="10,25,50", help="comma-separated max abs position values")
    ap.add_argument("--max-trade-in", type=int, default=200, help="upper bound for the attacker trade_in search")
    ap.add_argument("--progress-every", type=int, default=200, help="print progress to stderr every N combos (0 disables)")
    ap.add_argument("--out", type=str, default="", help="write JSON report to this path")
    args = ap.parse_args()

    reserves = _parse_int_list(args.reserves)
    fee_bps_list = _parse_int_list(args.fee_bps)
    max_move_list = _parse_int_list(args.max_move_bps)
    max_pos_list = _parse_int_list(args.max_pos_abs)
    max_trade_in = int(args.max_trade_in)

    if max_trade_in <= 0:
        raise SystemExit("--max-trade-in must be positive")

    combos = 0
    results: list[dict[str, int | bool]] = []
    start = time.perf_counter()
    for r in reserves:
        if r < 2:
            continue
        for fee_bps in fee_bps_list:
            if fee_bps < 0 or fee_bps > 10_000:
                continue
            for max_move_bps in max_move_list:
                if max_move_bps < 0 or max_move_bps > 10_000:
                    continue
                for max_pos_abs in max_pos_list:
                    if max_pos_abs < 1:
                        continue
                    combos += 1
                    if args.progress_every and (combos % int(args.progress_every) == 0):
                        print(
                            f"[oracle_sweep] combos={combos} r={r} fee={fee_bps} max_move={max_move_bps} max_pos={max_pos_abs}",
                            file=sys.stderr,
                            flush=True,
                        )

                    best = _find_best_attack(
                        reserve_base=int(r),
                        reserve_quote=int(r),
                        fee_bps=int(fee_bps),
                        max_move_bps=int(max_move_bps),
                        max_pos_abs=int(max_pos_abs),
                        max_trade_in=int(max_trade_in),
                    )
                    results.append(
                        {
                            "ok": bool(best.ok),
                            "reserve": int(r),
                            "fee_bps": int(fee_bps),
                            "max_move_bps": int(max_move_bps),
                            "max_pos_abs": int(max_pos_abs),
                            "trade_in": int(best.trade_in),
                            "pos_base": int(best.pos_base),
                            "price0_e8": int(best.price0_e8),
                            "price1_e8": int(best.price1_e8),
                            "settle_price_e8": int(best.settle_price_e8),
                            "spot_cost_quote": int(best.spot_cost_quote),
                            "perp_pnl_quote": int(best.perp_pnl_quote),
                            "net_profit_quote": int(best.net_profit_quote),
                        }
                    )

    runtime_s = time.perf_counter() - start
    report = {
        "schema": "zenodex/perp-oracle-manipulation-sweep/v1",
        "timestamp_unix": int(time.time()),
        "runtime_s": runtime_s,
        "params": {
            "reserves": reserves,
            "fee_bps": fee_bps_list,
            "max_move_bps": max_move_list,
            "max_pos_abs": max_pos_list,
            "max_trade_in": max_trade_in,
        },
        "results": results,
    }

    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(payload + "\n", encoding="utf-8")
        print(f"Wrote {out_path}")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
