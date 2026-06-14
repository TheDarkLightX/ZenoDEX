#!/usr/bin/env python3
from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.cpmm import swap_exact_out  # noqa: E402


@dataclass(frozen=True)
class Route2HopValueCase:
    x_ab: int
    y_ab: int
    fee_ab: int
    x_ac: int
    y_ac: int
    fee_ac: int
    x_cb: int
    y_cb: int
    fee_cb: int
    amount_out: int


def _ceil_div(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _exact_out_gross_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
) -> int:
    if amount_out <= 0:
        raise ValueError("amount_out must be positive")
    if amount_out >= reserve_out:
        raise ValueError("amount_out must be below reserve_out")
    if not 0 <= fee_bps < 10_000:
        raise ValueError("fee_bps must be in [0, 10000)")
    net_in = _ceil_div(reserve_in * amount_out, reserve_out - amount_out)
    return _ceil_div(net_in * 10_000, 10_000 - fee_bps)


def eval_route_exact_out_2hop_value_python(case: Route2HopValueCase) -> tuple[bool, dict[str, Any]]:
    """Replay the witness through the production CPMM exact-out kernel."""

    direct_in, _ = swap_exact_out(
        reserve_in=int(case.x_ab),
        reserve_out=int(case.y_ab),
        amount_out=int(case.amount_out),
        fee_bps=int(case.fee_ab),
    )
    intermediate_in, _ = swap_exact_out(
        reserve_in=int(case.x_cb),
        reserve_out=int(case.y_cb),
        amount_out=int(case.amount_out),
        fee_bps=int(case.fee_cb),
    )
    twohop_in, _ = swap_exact_out(
        reserve_in=int(case.x_ac),
        reserve_out=int(case.y_ac),
        amount_out=int(intermediate_in),
        fee_bps=int(case.fee_ac),
    )
    ok = int(twohop_in) < int(direct_in)
    return ok, {
        "direct_in": int(direct_in),
        "intermediate_in": int(intermediate_in),
        "twohop_in": int(twohop_in),
        "amount_out": int(case.amount_out),
    }


def eval_route_exact_out_2hop_value_z3(case: Route2HopValueCase) -> tuple[bool, dict[str, Any]]:
    """Check the same concrete witness with an independent Z3 integer encoding."""

    import z3  # pylint: disable=import-outside-toplevel

    def zceil(numerator: int | z3.ArithRef, denominator: int) -> z3.ArithRef:
        if isinstance(numerator, int):
            numerator = z3.IntVal(int(numerator))
        return z3.simplify((numerator + z3.IntVal(int(denominator)) - 1) / z3.IntVal(int(denominator)))

    direct_in = _exact_out_gross_in(
        reserve_in=int(case.x_ab),
        reserve_out=int(case.y_ab),
        amount_out=int(case.amount_out),
        fee_bps=int(case.fee_ab),
    )
    intermediate_in = _exact_out_gross_in(
        reserve_in=int(case.x_cb),
        reserve_out=int(case.y_cb),
        amount_out=int(case.amount_out),
        fee_bps=int(case.fee_cb),
    )
    twohop_in = _exact_out_gross_in(
        reserve_in=int(case.x_ac),
        reserve_out=int(case.y_ac),
        amount_out=int(intermediate_in),
        fee_bps=int(case.fee_ac),
    )

    direct_net = zceil(case.x_ab * case.amount_out, case.y_ab - case.amount_out)
    direct_expr = zceil(direct_net * 10_000, 10_000 - case.fee_ab)
    second_net = zceil(case.x_cb * case.amount_out, case.y_cb - case.amount_out)
    second_expr = zceil(second_net * 10_000, 10_000 - case.fee_cb)
    first_net = zceil(case.x_ac * intermediate_in, case.y_ac - intermediate_in)
    first_expr = zceil(first_net * 10_000, 10_000 - case.fee_ac)

    solver = z3.Solver()
    solver.add(
        z3.Not(
            z3.And(
                direct_expr == int(direct_in),
                second_expr == int(intermediate_in),
                first_expr == int(twohop_in),
                first_expr < direct_expr,
            )
        )
    )
    ok = solver.check() == z3.unsat
    return bool(ok), {
        "direct_in": int(direct_in),
        "intermediate_in": int(intermediate_in),
        "twohop_in": int(twohop_in),
        "z3_refutation_check": str(solver.check()),
    }


def main() -> int:
    case = Route2HopValueCase(
        x_ab=2,
        y_ab=2,
        fee_ab=0,
        x_ac=1,
        y_ac=2,
        fee_ac=0,
        x_cb=1,
        y_cb=2,
        fee_cb=0,
        amount_out=1,
    )
    ok_py, py_details = eval_route_exact_out_2hop_value_python(case)
    ok_z3, z3_details = eval_route_exact_out_2hop_value_z3(case)
    import json

    print(
        json.dumps(
            {
                "ok": bool(ok_py and ok_z3),
                "python": py_details,
                "z3": z3_details,
            },
            sort_keys=True,
        )
    )
    return 0 if ok_py and ok_z3 else 1


if __name__ == "__main__":
    raise SystemExit(main())
