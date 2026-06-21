#!/usr/bin/env python3
"""ZenoDEX Linked Assurance Threshold Verifier.

Verifies the Linked Assurance mechanism for escaping Myerson-Satterthwaite
impossibility in public-good provision (e.g., Lean proof receipts). The
mechanism links pledge participation to *early access* rather than access
itself: pledgers receive the receipt at T_0, non-pledgers at T_1 > T_0.

Mathematical model (integer arithmetic, no floats):
  Buyer valuation: v
  Pledge bond: B
  Delay discount: delta = deltaNum / deltaDen (0 < deltaNum < deltaDen)

  Pledge payoff:  v - B        (receive at T_0, pay bond)
  Abstain payoff: delta * v    (receive at T_1, discounted)

  Pledge dominates iff v * (1 - delta) >= B
  Cross-multiplied: v * (deltaDen - deltaNum) >= B * deltaDen

Aggregate: n pledgers each posting B reach production cost C iff n * B >= C.

Usage:
    python3 tools/zenodex_linked_assurance.py sample > envelope.json
    python3 tools/zenodex_linked_assurance.py verify envelope.json
    python3 tools/zenodex_linked_assurance.py verify envelope.json --output result.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

MAX_AMOUNT = 10**18
MAX_N = 10_000

REQUIRED_FIELDS = (
    "campaign_id",
    "buyer_valuation_e8",
    "pledge_bond_e8",
    "delta_num",
    "delta_den",
    "participant_count",
    "production_cost_e8",
)


@dataclass(frozen=True)
class LinkedAssuranceResult:
    status: str  # "accepted" | "rejected" | "inconclusive"
    errors: list[str] = field(default_factory=list)
    campaign_id: str = ""
    buyer_valuation_e8: int = 0
    pledge_bond_e8: int = 0
    delta_num: int = 0
    delta_den: int = 0
    participant_count: int = 0
    production_cost_e8: int = 0
    lhs: int = 0  # v * (deltaDen - deltaNum)
    rhs: int = 0  # B * deltaDen
    pledge_dominates: bool | None = None
    aggregate_meets_cost: bool | None = None
    total_pledged_e8: int = 0
    required_bond_e8: int | None = None


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
        "campaign_id": "zenoproof.proof-receipt-001",
        "buyer_valuation_e8": 100_000_000,
        "pledge_bond_e8": 30_000_000,
        "delta_num": 1,
        "delta_den": 2,
        "participant_count": 5,
        "production_cost_e8": 100_000_000,
    }


def verify_linked_assurance_envelope(obj: dict[str, Any]) -> LinkedAssuranceResult:
    if not isinstance(obj, dict):
        return LinkedAssuranceResult(
            status="rejected",
            errors=["top_level_must_be_object"],
        )

    errors: list[str] = []

    for field_name in REQUIRED_FIELDS:
        if field_name not in obj:
            errors.append(f"missing_required_field:{field_name}")

    if errors:
        return LinkedAssuranceResult(status="rejected", errors=errors)

    try:
        campaign_id = _token(obj, "campaign_id")
        v = _int_between(obj, "buyer_valuation_e8", minimum=1, maximum=MAX_AMOUNT)
        B = _int_between(obj, "pledge_bond_e8", minimum=0, maximum=MAX_AMOUNT)
        delta_num = _int_between(obj, "delta_num", minimum=1, maximum=MAX_AMOUNT)
        delta_den = _int_between(obj, "delta_den", minimum=2, maximum=MAX_AMOUNT)
        n = _int_between(obj, "participant_count", minimum=1, maximum=MAX_N)
        C = _int_between(obj, "production_cost_e8", minimum=1, maximum=MAX_AMOUNT)
    except ValueError as exc:
        return LinkedAssuranceResult(status="rejected", errors=[str(exc)])

    if delta_num >= delta_den:
        errors.append("delta_must_be_strictly_less_than_one")

    lhs = v * (delta_den - delta_num)
    rhs = B * delta_den
    pledge_dominates = lhs >= rhs

    total_pledged = n * B
    aggregate_meets_cost = total_pledged >= C

    required_bond = None
    if not pledge_dominates and delta_den > 0:
        required_bond = (lhs + delta_den - 1) // delta_den

    if not pledge_dominates:
        errors.append("pledge_does_not_dominate")

    if not aggregate_meets_cost:
        errors.append("aggregate_insufficient")

    status = "accepted" if not errors else "rejected"

    return LinkedAssuranceResult(
        status=status,
        errors=errors,
        campaign_id=campaign_id,
        buyer_valuation_e8=v,
        pledge_bond_e8=B,
        delta_num=delta_num,
        delta_den=delta_den,
        participant_count=n,
        production_cost_e8=C,
        lhs=lhs,
        rhs=rhs,
        pledge_dominates=pledge_dominates,
        aggregate_meets_cost=aggregate_meets_cost,
        total_pledged_e8=total_pledged,
        required_bond_e8=required_bond,
    )


def _write_result(result: LinkedAssuranceResult, output: Path | None) -> None:
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
        result = LinkedAssuranceResult(
            status="inconclusive",
            errors=[f"linked_assurance_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_linked_assurance_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Linked Assurance Threshold Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a linked assurance envelope")
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
