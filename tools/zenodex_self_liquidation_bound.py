#!/usr/bin/env python3
"""ZenoDEX Self-Liquidation Bound Verifier.

Verifies that the liquidator gas compensation parameter does not enable
self-liquidation attacks. A self-liquidation attack occurs when a borrower
liquidates their own vault to capture the liquidator compensation. If the
compensation exceeds the collateral the borrower would have kept by repaying
the debt at fair market price, the attack is profitable.

Mathematical model (integer arithmetic, no floats):
  At the MCR boundary (C*P*BPS = D*mcr*E8), self-liquidation is unprofitable iff:
    gas_comp_bps * mcr_bps <= BPS * (mcr_bps - BPS)

  This is independent of C, D, and P: the bound is purely a function of the
  protocol parameters gas_comp_bps and mcr_bps.

  Max safe gas_comp = BPS * (mcr_bps - BPS) / mcr_bps (integer floor).

Usage:
    python3 tools/zenodex_self_liquidation_bound.py sample > envelope.json
    python3 tools/zenodex_self_liquidation_bound.py verify envelope.json
    python3 tools/zenodex_self_liquidation_bound.py verify envelope.json --output result.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

BPS_SCALE = 10_000
MAX_BPS = 30_000  # max MCR = 300%

REQUIRED_FIELDS = (
    "vault_id",
    "mcr_bps",
    "gas_comp_bps",
)


@dataclass(frozen=True)
class SelfLiquidationResult:
    status: str  # "accepted" | "rejected" | "inconclusive"
    errors: list[str] = field(default_factory=list)
    vault_id: str = ""
    mcr_bps: int = 0
    gas_comp_bps: int = 0
    lhs: int = 0  # gas_comp_bps * mcr_bps
    rhs: int = 0  # BPS * (mcr_bps - BPS)
    self_liquidation_unprofitable: bool | None = None
    max_safe_gas_comp_bps: int = 0
    mcr_exceeds_100pct: bool | None = None


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
        "vault_id": "zenodex.zusd-vault-001",
        "mcr_bps": 13000,
        "gas_comp_bps": 2307,
    }


def verify_self_liquidation_envelope(obj: dict[str, Any]) -> SelfLiquidationResult:
    if not isinstance(obj, dict):
        return SelfLiquidationResult(
            status="rejected",
            errors=["top_level_must_be_object"],
        )

    errors: list[str] = []

    for field_name in REQUIRED_FIELDS:
        if field_name not in obj:
            errors.append(f"missing_required_field:{field_name}")

    if errors:
        return SelfLiquidationResult(status="rejected", errors=errors)

    try:
        vault_id = _token(obj, "vault_id")
        mcr_bps = _int_between(obj, "mcr_bps", minimum=1, maximum=MAX_BPS)
        gas_comp_bps = _int_between(obj, "gas_comp_bps", minimum=0, maximum=BPS_SCALE)
    except ValueError as exc:
        return SelfLiquidationResult(status="rejected", errors=[str(exc)])

    mcr_exceeds_100pct = mcr_bps > BPS_SCALE

    lhs = gas_comp_bps * mcr_bps
    rhs = BPS_SCALE * (mcr_bps - BPS_SCALE) if mcr_exceeds_100pct else 0
    self_liquidation_unprofitable = lhs <= rhs

    max_safe = (BPS_SCALE * (mcr_bps - BPS_SCALE)) // mcr_bps if mcr_exceeds_100pct else 0

    if not mcr_exceeds_100pct:
        errors.append("mcr_must_exceed_100pct")

    if not self_liquidation_unprofitable:
        errors.append("self_liquidation_profitable")

    status = "accepted" if not errors else "rejected"

    return SelfLiquidationResult(
        status=status,
        errors=errors,
        vault_id=vault_id,
        mcr_bps=mcr_bps,
        gas_comp_bps=gas_comp_bps,
        lhs=lhs,
        rhs=rhs,
        self_liquidation_unprofitable=self_liquidation_unprofitable,
        max_safe_gas_comp_bps=max_safe,
        mcr_exceeds_100pct=mcr_exceeds_100pct,
    )


def _write_result(result: SelfLiquidationResult, output: Path | None) -> None:
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
        result = SelfLiquidationResult(
            status="inconclusive",
            errors=[f"self_liquidation_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_self_liquidation_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Self-Liquidation Bound Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a self-liquidation envelope")
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
