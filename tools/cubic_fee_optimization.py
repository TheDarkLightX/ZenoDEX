from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import cpmm
from src.core import cubic_sum_amm


@dataclass(frozen=True)
class Sample:
    reserve: int
    dx: int


def _parse_int_list(csv: str) -> list[int]:
    out: list[int] = []
    for part in csv.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise ValueError("empty list")
    return out


def _parse_float_list(csv: str) -> list[float]:
    out: list[float] = []
    for part in csv.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(float(part))
    if not out:
        raise ValueError("empty list")
    return out


def _cost_bps(*, dx: int, out: int) -> int:
    """
    Effective trader cost in basis points, using dx as the ideal out at price=1.
    """
    if dx <= 0:
        raise ValueError("dx must be positive")
    if out < 0:
        raise ValueError("out must be non-negative")
    if out > dx:
        return 0
    # ceil to avoid zero-cost infinities in isoelastic demand models.
    lost = dx - out
    return max(1, int(math.ceil(lost * 10_000 / dx)))


def _sample_set(*, reserves: list[int], trade_fracs: list[float], min_dx: int) -> list[Sample]:
    samples: list[Sample] = []
    for r in reserves:
        if r <= 0:
            raise ValueError("reserve must be positive")
        for frac in trade_fracs:
            if frac <= 0:
                raise ValueError("trade fraction must be positive")
            dx = max(int(round(r * frac)), int(min_dx))
            if dx <= 0:
                dx = 1
            samples.append(Sample(reserve=int(r), dx=int(dx)))
    if not samples:
        raise ValueError("no samples")
    return samples


def _avg_cost_bps_curve(
    *,
    curve: str,
    samples: list[Sample],
    fee_bps: int,
    p: int,
    q: int,
    cost_model: str,
) -> float | None:
    costs: list[int] = []
    for s in samples:
        x = s.reserve
        y = s.reserve
        dx = s.dx
        try:
            if cost_model == "explicit_fee_plus_slippage":
                # Avoid integer fee-quantization artifacts by making fee explicit in the cost model.
                if curve == "cpmm":
                    out0, _ = cpmm.swap_exact_in(x, y, dx, fee_bps=0)
                elif curve == "cubic_sum":
                    out0, _ = cubic_sum_amm.swap_exact_in_cubic_sum(x, y, dx, p=p, q=q, fee_bps=0)
                else:
                    raise ValueError(f"unknown curve: {curve}")
                slippage_bps = _cost_bps(dx=int(dx), out=int(out0))
                total_cost = int(slippage_bps) + int(fee_bps)
                costs.append(max(1, int(total_cost)))
            elif cost_model == "output_loss":
                if curve == "cpmm":
                    out, _ = cpmm.swap_exact_in(x, y, dx, fee_bps=int(fee_bps))
                elif curve == "cubic_sum":
                    out, _ = cubic_sum_amm.swap_exact_in_cubic_sum(x, y, dx, p=p, q=q, fee_bps=int(fee_bps))
                else:
                    raise ValueError(f"unknown curve: {curve}")
                costs.append(_cost_bps(dx=int(dx), out=int(out)))
            else:
                raise ValueError(f"unknown cost model: {cost_model}")
        except Exception:
            continue
    if not costs:
        return None
    return float(sum(costs)) / float(len(costs))


def _opt_fee_bps_isoelastic(
    *,
    curve: str,
    samples: list[Sample],
    epsilon: float,
    fee_bps_min: int,
    fee_bps_max: int,
    fee_bps_step: int,
    p: int,
    q: int,
    cost_model: str,
) -> dict[str, object]:
    """
    Optimize fee_bps for revenue proxy:
      revenue ∝ fee_rate * (avg_cost_bps)^(-epsilon)

    Deterministic tie-break: lowest fee_bps.
    """
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    if fee_bps_step <= 0:
        raise ValueError("fee_bps_step must be positive")
    if fee_bps_min < 0 or fee_bps_max > 10_000 or fee_bps_min > fee_bps_max:
        raise ValueError("invalid fee_bps range")

    best_fee: int | None = None
    best_score: float | None = None
    best_cost: float | None = None
    table: list[dict[str, object]] = []

    for fee_bps in range(int(fee_bps_min), int(fee_bps_max) + 1, int(fee_bps_step)):
        cost = _avg_cost_bps_curve(
            curve=curve,
            samples=samples,
            fee_bps=fee_bps,
            p=p,
            q=q,
            cost_model=str(cost_model),
        )
        if cost is None:
            continue
        fee_rate = float(fee_bps) / 10_000.0
        score = fee_rate * (float(cost) ** (-float(epsilon)))
        row = {"fee_bps": int(fee_bps), "avg_cost_bps": float(cost), "revenue_proxy": float(score)}
        table.append(row)

        if best_score is None or score > best_score or (score == best_score and fee_bps < int(best_fee)):
            best_fee = int(fee_bps)
            best_score = float(score)
            best_cost = float(cost)

    return {
        "curve": curve,
        "epsilon": float(epsilon),
        "cost_model": str(cost_model),
        "fee_bps_range": {"min": int(fee_bps_min), "max": int(fee_bps_max), "step": int(fee_bps_step)},
        "best": {"fee_bps": best_fee, "avg_cost_bps": best_cost, "revenue_proxy": best_score},
        "table": table,
    }


def _group_samples_by_reserve(samples: list[Sample]) -> dict[int, list[Sample]]:
    grouped: dict[int, list[Sample]] = {}
    for s in samples:
        grouped.setdefault(int(s.reserve), []).append(s)
    return grouped


def main() -> int:
    ap = argparse.ArgumentParser(description="Cubic-sum fee optimization (isoelastic volume vs total cost proxy)")
    ap.add_argument("--reserves", type=str, default="1000,10000,1000000")
    ap.add_argument("--trade-fracs", type=str, default="0.001,0.005,0.01")
    ap.add_argument("--min-dx", type=int, default=10)
    ap.add_argument("--epsilon", type=float, default=1.5)
    ap.add_argument("--fee-bps-min", type=int, default=1)
    ap.add_argument("--fee-bps-max", type=int, default=300)
    ap.add_argument("--fee-bps-step", type=int, default=1)
    ap.add_argument("--p", type=int, default=1)
    ap.add_argument("--q", type=int, default=1)
    ap.add_argument(
        "--cost-model",
        type=str,
        default="explicit_fee_plus_slippage",
        choices=["explicit_fee_plus_slippage", "output_loss"],
        help="How to convert (fee, slippage) into a single total-cost proxy for the isoelastic demand model.",
    )
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()

    reserves = _parse_int_list(args.reserves)
    trade_fracs = _parse_float_list(args.trade_fracs)
    samples = _sample_set(reserves=reserves, trade_fracs=trade_fracs, min_dx=int(args.min_dx))

    start = time.perf_counter()
    report = {
        "schema": "zenodex/cubic-fee-opt/v1",
        "timestamp_unix": int(time.time()),
        "params": {
            "reserves": reserves,
            "trade_fracs": trade_fracs,
            "min_dx": int(args.min_dx),
            "epsilon": float(args.epsilon),
            "p": int(args.p),
            "q": int(args.q),
            "cost_model": str(args.cost_model),
        },
        "samples": [{"reserve": s.reserve, "dx": s.dx} for s in samples],
        "results": {
            "overall": {
                "cpmm": _opt_fee_bps_isoelastic(
                    curve="cpmm",
                    samples=samples,
                    epsilon=float(args.epsilon),
                    fee_bps_min=int(args.fee_bps_min),
                fee_bps_max=int(args.fee_bps_max),
                fee_bps_step=int(args.fee_bps_step),
                p=int(args.p),
                q=int(args.q),
                cost_model=str(args.cost_model),
            ),
                "cubic_sum": _opt_fee_bps_isoelastic(
                    curve="cubic_sum",
                    samples=samples,
                    epsilon=float(args.epsilon),
                    fee_bps_min=int(args.fee_bps_min),
                    fee_bps_max=int(args.fee_bps_max),
                    fee_bps_step=int(args.fee_bps_step),
                    p=int(args.p),
                    q=int(args.q),
                    cost_model=str(args.cost_model),
                ),
            },
            "by_reserve": {},
        },
        "runtime_s": None,
    }

    by_reserve: dict[int, list[Sample]] = _group_samples_by_reserve(samples)
    for reserve, rsamples in sorted(by_reserve.items(), key=lambda kv: kv[0]):
        report["results"]["by_reserve"][str(reserve)] = {
            "cpmm": _opt_fee_bps_isoelastic(
                curve="cpmm",
                samples=rsamples,
                epsilon=float(args.epsilon),
                fee_bps_min=int(args.fee_bps_min),
                fee_bps_max=int(args.fee_bps_max),
                fee_bps_step=int(args.fee_bps_step),
                p=int(args.p),
                q=int(args.q),
                cost_model=str(args.cost_model),
            ),
            "cubic_sum": _opt_fee_bps_isoelastic(
                curve="cubic_sum",
                samples=rsamples,
                epsilon=float(args.epsilon),
                fee_bps_min=int(args.fee_bps_min),
                fee_bps_max=int(args.fee_bps_max),
                fee_bps_step=int(args.fee_bps_step),
                p=int(args.p),
                q=int(args.q),
                cost_model=str(args.cost_model),
            ),
        }

    report["runtime_s"] = time.perf_counter() - start

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
