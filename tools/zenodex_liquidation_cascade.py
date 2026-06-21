#!/usr/bin/env python3
"""ZenoDEX Liquidation Cascade Termination Verifier.

Validates that a partial liquidation cascade terminates in bounded steps
under the ZenoDEX perp model. Uses exact BPS-scaled integer arithmetic.

Model (matching Lean ZenoProofLiquidationCascade):
  closed = pos * fraction // BPS
  remaining = pos - closed
  maint_margin_req = pos * price * (maint_bps + depeg_bps) // BPS
  penalty = min(collateral, closed * price * penalty_bps // BPS)
  post_collateral = collateral - penalty
  Guard: post_collateral >= maint_margin_req(remaining, price, maint_bps + depeg_bps)

Termination bound:
  - Each liquidation with fraction >= 1 and pos >= BPS reduces pos by >= 1
  - Cascade terminates in at most pos steps for a single position

Funded liquidation condition:
  penalty_bps * (BPS + max_oracle_move) <= BPS * (maint_eff - max_oracle_move)
  ensures penalty is funded by collateral, not insurance.

Usage:
    python3 tools/zenodex_liquidation_cascade.py sample > envelope.json
    python3 tools/zenodex_liquidation_cascade.py verify envelope.json
    python3 tools/zenodex_liquidation_cascade.py verify envelope.json --output result.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

BPS_SCALE = 10_000
MAX_AMOUNT = 10**18
MAX_POSITION = 10**18
MAX_PRICE = 10**18
MAX_BPS = 30_000

REQUIRED_FIELDS = (
    "position_id",
    "position_base",
    "collateral_quote",
    "index_price_e8",
    "maint_bps",
    "depeg_buffer_bps",
    "penalty_bps",
    "max_oracle_move_bps",
    "liquidation_fraction_bps",
)


@dataclass(frozen=True)
class LiquidationCascadeResult:
    status: str
    errors: list[str] = field(default_factory=list)
    position_id: str = ""
    position_base: int = 0
    collateral_quote: int = 0
    index_price_e8: int = 0
    maint_bps: int = 0
    depeg_buffer_bps: int = 0
    penalty_bps: int = 0
    max_oracle_move_bps: int = 0
    liquidation_fraction_bps: int = 0
    closed_portion: int = 0
    remaining_position: int = 0
    maint_margin_req: int = 0
    raw_penalty: int = 0
    capped_penalty: int = 0
    post_collateral: int = 0
    is_liquidatable: bool | None = None
    position_decreases: bool | None = None
    post_liquidation_safe: bool | None = None
    cascade_terminates: bool | None = None
    max_cascade_steps: int | None = None
    funded_liquidation_ok: bool | None = None


def _load_json(path: Path) -> dict[str, Any]:
    text = path.read_text()
    if len(text) > 1_000_000:
        raise ValueError("file_too_large")
    obj = json.loads(text)
    if not isinstance(obj, dict):
        raise ValueError("top_level_must_be_object")
    return obj


def _int_between(obj: dict[str, Any], key: str, *, minimum: int, maximum: int) -> int:
    val = obj.get(key)
    if not isinstance(val, int) or isinstance(val, bool):
        raise ValueError(f"{key}_must_be_int")
    if val < minimum:
        raise ValueError(f"{key}_must_be_gte_{minimum}")
    if val > maximum:
        raise ValueError(f"{key}_must_be_lte_{maximum}")
    return val


def _token(obj: dict[str, Any], key: str) -> str:
    val = obj.get(key)
    if not isinstance(val, str):
        raise ValueError(f"{key}_must_be_token")
    if not val.replace(".", "").replace("_", "").replace("-", "").isalnum():
        raise ValueError(f"{key}_must_be_token")
    if len(val) < 1 or len(val) > 128:
        raise ValueError(f"{key}_must_be_token")
    return val


def notional_quote(pos_abs: int, price: int) -> int:
    return pos_abs * price


def maint_margin_req(pos_abs: int, price: int, maint_bps: int, depeg_bps: int) -> int:
    return notional_quote(pos_abs, price) * (maint_bps + depeg_bps) // BPS_SCALE


def liq_penalty(closed: int, price: int, penalty_bps: int) -> int:
    return closed * price * penalty_bps // BPS_SCALE


def capped_penalty(collateral: int, closed: int, price: int, penalty_bps: int) -> int:
    return min(collateral, liq_penalty(closed, price, penalty_bps))


def is_liquidatable(pos_abs: int, collateral: int, price: int,
                    maint_bps: int, depeg_bps: int) -> bool:
    if pos_abs == 0:
        return False
    return collateral < maint_margin_req(pos_abs, price, maint_bps, depeg_bps)


def closed_portion(pos_abs: int, fraction: int) -> int:
    return pos_abs * fraction // BPS_SCALE


def remaining_position(pos_abs: int, fraction: int) -> int:
    return pos_abs - closed_portion(pos_abs, fraction)


def funded_liquidation_ok(penalty_bps: int, max_oracle_move: int,
                          maint_bps: int, depeg_bps: int) -> bool:
    eff_maint = maint_bps + depeg_bps
    return penalty_bps * (BPS_SCALE + max_oracle_move) <= (
        BPS_SCALE * (eff_maint - max_oracle_move)
    )


def sample_envelope() -> dict[str, Any]:
    return {
        "position_id": "zenodex.perp-position-001",
        "position_base": 10_000,
        "collateral_quote": 100_000_000_000,
        "index_price_e8": 100_000_000,
        "maint_bps": 500,
        "depeg_buffer_bps": 100,
        "penalty_bps": 200,
        "max_oracle_move_bps": 300,
        "liquidation_fraction_bps": 5_000,
    }


def verify_liquidation_cascade_envelope(obj: dict[str, Any]) -> LiquidationCascadeResult:
    if not isinstance(obj, dict):
        return LiquidationCascadeResult(
            status="rejected",
            errors=["top_level_must_be_object"],
        )

    errors: list[str] = []

    for field_name in REQUIRED_FIELDS:
        if field_name not in obj:
            errors.append(f"missing_required_field:{field_name}")

    if errors:
        return LiquidationCascadeResult(status="rejected", errors=errors)

    try:
        position_id = _token(obj, "position_id")
        pos = _int_between(obj, "position_base", minimum=0, maximum=MAX_POSITION)
        collateral = _int_between(obj, "collateral_quote", minimum=0, maximum=MAX_AMOUNT)
        price = _int_between(obj, "index_price_e8", minimum=1, maximum=MAX_PRICE)
        maint_bps = _int_between(obj, "maint_bps", minimum=1, maximum=MAX_BPS)
        depeg_bps = _int_between(obj, "depeg_buffer_bps", minimum=0, maximum=MAX_BPS)
        penalty_bps = _int_between(obj, "penalty_bps", minimum=0, maximum=BPS_SCALE)
        max_oracle_move = _int_between(obj, "max_oracle_move_bps", minimum=0, maximum=MAX_BPS)
        fraction = _int_between(obj, "liquidation_fraction_bps", minimum=0, maximum=BPS_SCALE)
    except ValueError as exc:
        return LiquidationCascadeResult(status="rejected", errors=[str(exc)])

    eff_maint = maint_bps + depeg_bps
    closed = closed_portion(pos, fraction)
    remaining = remaining_position(pos, fraction)
    mreq = maint_margin_req(pos, price, maint_bps, depeg_bps)
    raw_pen = liq_penalty(closed, price, penalty_bps)
    capped_pen = capped_penalty(collateral, closed, price, penalty_bps)
    post_collat = collateral - capped_pen

    liq = is_liquidatable(pos, collateral, price, maint_bps, depeg_bps)
    pos_decreases = fraction >= 1 and pos >= BPS_SCALE and remaining < pos
    rem_mreq = maint_margin_req(remaining, price, maint_bps, depeg_bps) if remaining > 0 else 0
    post_safe = post_collat >= rem_mreq
    cascade_term = remaining <= pos - 1 if pos > 0 else True
    max_steps = pos if pos > 0 else 0
    funded_ok = funded_liquidation_ok(penalty_bps, max_oracle_move, maint_bps, depeg_bps)

    if fraction < 1 and pos > 0:
        errors.append("fraction_must_be_at_least_1_bps")
    if pos < BPS_SCALE and pos > 0 and fraction < BPS_SCALE:
        errors.append("position_must_be_at_least_bps_for_termination")
    if not pos_decreases and pos > 0 and fraction >= 1 and pos >= BPS_SCALE:
        errors.append("position_does_not_decrease")
    if not post_safe and remaining > 0:
        errors.append("post_liquidation_unsafe")
    if penalty_bps >= eff_maint:
        errors.append("penalty_exceeds_eff_maint_margin")
    if max_oracle_move > eff_maint:
        errors.append("oracle_move_exceeds_eff_maint")
    if not funded_ok:
        errors.append("funded_liquidation_violated")
    if raw_pen > collateral and capped_pen < raw_pen:
        errors.append("raw_penalty_exceeds_collateral")

    status = "accepted" if not errors else "rejected"

    return LiquidationCascadeResult(
        status=status,
        errors=errors,
        position_id=position_id,
        position_base=pos,
        collateral_quote=collateral,
        index_price_e8=price,
        maint_bps=maint_bps,
        depeg_buffer_bps=depeg_bps,
        penalty_bps=penalty_bps,
        max_oracle_move_bps=max_oracle_move,
        liquidation_fraction_bps=fraction,
        closed_portion=closed,
        remaining_position=remaining,
        maint_margin_req=mreq,
        raw_penalty=raw_pen,
        capped_penalty=capped_pen,
        post_collateral=post_collat,
        is_liquidatable=liq,
        position_decreases=pos_decreases,
        post_liquidation_safe=post_safe,
        cascade_terminates=cascade_term,
        max_cascade_steps=max_steps,
        funded_liquidation_ok=funded_ok,
    )


def _write_result(result: LiquidationCascadeResult, output: Path | None) -> None:
    data = asdict(result)
    text = json.dumps(data, indent=2, sort_keys=True)
    if output is not None:
        output.write_text(text)
    else:
        print(text)


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_envelope(), indent=2)
    if args.output:
        Path(args.output).write_text(text)
    else:
        print(text)
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        obj = _load_json(Path(args.input))
    except Exception as exc:
        result = LiquidationCascadeResult(
            status="inconclusive",
            errors=[f"cascade_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_liquidation_cascade_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Liquidation Cascade Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a liquidation cascade envelope")
    p_verify.add_argument("input", type=str, help="Path to JSON envelope")
    p_verify.add_argument("--output", type=str, default="")

    args = parser.parse_args(argv)

    if args.command == "sample":
        return cmd_sample(args)
    elif args.command == "verify":
        return cmd_verify(args)
    return 1


if __name__ == "__main__":
    sys.exit(main())
