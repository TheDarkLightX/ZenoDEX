#!/usr/bin/env python3
"""ZenoDEX Liquidation Cascade Termination Verifier.

Verifies that the liquidation cascade terminates in bounded steps. Each
partial liquidation with fraction >= 1 BPS strictly reduces the position
size by at least 1 unit when pos >= BPS. A position of size n requires
at most n partial liquidations to reach zero.

Mathematical model (integer arithmetic, no floats):
  closed = pos * fraction / BPS (integer division)
  remaining = pos - closed
  maint_margin_req = pos * price * maint_bps / BPS
  penalty = min(collateral, closed * price * penalty_bps / BPS)
  post_collateral = collateral - penalty

Key invariants:
  - position_strictly_decreases: fraction >= 1 and pos >= BPS => remaining < pos
  - cascade_terminates: remaining <= pos - 1 (at most pos steps to zero)
  - post_liquidation_safe: guard ensures post_collateral >= maint_margin_req(remaining)

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
MAX_POSITION = 10**18
MAX_PRICE = 10**18
MAX_BPS = 30_000

REQUIRED_FIELDS = (
    "position_id",
    "position_base",
    "collateral_quote",
    "index_price_e8",
    "maint_bps",
    "penalty_bps",
    "liquidation_fraction_bps",
)


@dataclass(frozen=True)
class LiquidationCascadeResult:
    status: str  # "accepted" | "rejected" | "inconclusive"
    errors: list[str] = field(default_factory=list)
    position_id: str = ""
    position_base: int = 0
    collateral_quote: int = 0
    index_price_e8: int = 0
    maint_bps: int = 0
    penalty_bps: int = 0
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


def sample_envelope() -> dict[str, Any]:
    return {
        "position_id": "zenodex.perp-position-001",
        "position_base": 10_000,
        "collateral_quote": 2_000_000_000,
        "index_price_e8": 100_000_000,
        "maint_bps": 6_000,
        "penalty_bps": 500,
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
        collateral = _int_between(obj, "collateral_quote", minimum=0, maximum=MAX_POSITION)
        price = _int_between(obj, "index_price_e8", minimum=1, maximum=MAX_PRICE)
        maint_bps = _int_between(obj, "maint_bps", minimum=1, maximum=MAX_BPS)
        penalty_bps = _int_between(obj, "penalty_bps", minimum=0, maximum=BPS_SCALE)
        fraction = _int_between(obj, "liquidation_fraction_bps", minimum=0, maximum=BPS_SCALE)
    except ValueError as exc:
        return LiquidationCascadeResult(status="rejected", errors=[str(exc)])

    closed = (pos * fraction) // BPS_SCALE
    remaining = pos - closed
    maint_margin = (pos * price * maint_bps) // (BPS_SCALE * 100_000_000) if price > 0 else 0
    raw_penalty = (closed * price * penalty_bps) // (BPS_SCALE * 100_000_000) if price > 0 else 0
    capped_penalty = min(collateral, raw_penalty)
    post_collateral = collateral - capped_penalty

    is_liquidatable = pos > 0 and collateral < maint_margin
    position_decreases = fraction >= 1 and pos >= BPS_SCALE and remaining < pos
    post_liquidation_safe = post_collateral >= (remaining * price * maint_bps) // (BPS_SCALE * 100_000_000) if price > 0 else True
    cascade_terminates = remaining <= pos - 1 if pos > 0 else True

    if fraction < 1:
        errors.append("fraction_must_be_at_least_1_bps")
    if pos < BPS_SCALE and pos > 0:
        errors.append("position_must_be_at_least_bps_for_termination")
    if not position_decreases and pos > 0 and fraction >= 1:
        errors.append("position_does_not_decrease")
    if not post_liquidation_safe:
        errors.append("post_liquidation_unsafe")
    if penalty_bps > maint_bps:
        errors.append("penalty_exceeds_maint_margin")

    status = "accepted" if not errors else "rejected"

    return LiquidationCascadeResult(
        status=status,
        errors=errors,
        position_id=position_id,
        position_base=pos,
        collateral_quote=collateral,
        index_price_e8=price,
        maint_bps=maint_bps,
        penalty_bps=penalty_bps,
        liquidation_fraction_bps=fraction,
        closed_portion=closed,
        remaining_position=remaining,
        maint_margin_req=maint_margin,
        raw_penalty=raw_penalty,
        capped_penalty=capped_penalty,
        post_collateral=post_collateral,
        is_liquidatable=is_liquidatable,
        position_decreases=position_decreases,
        post_liquidation_safe=post_liquidation_safe,
        cascade_terminates=cascade_terminates,
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
