#!/usr/bin/env python3
"""ZenoDEX Mechanism Composition Verifier.

Verifies parallel and series composition of bounty mechanisms. A bounty
mechanism has an eligibility predicate and a payout function bounded by a
cap. Parallel composition fires both mechanisms (total bounded by sum of
caps). Series composition fires the first eligible mechanism (bounded by
shared cap).

Mathematical model (integer arithmetic, no floats):
  Parallel: payout = payout1(cap1, sub1) + payout2(cap2, sub2) <= cap1 + cap2
  Series: payout = if eligible(sub1) then payout1(cap, sub1) else payout2(cap, sub2) <= cap

  Counterexample beats proof: if proof ineligible and counterexample eligible,
  series pays counterexample. Positivity requires cap > 0.

Usage:
    python3 tools/zenodex_mechanism_composition.py sample > envelope.json
    python3 tools/zenodex_mechanism_composition.py verify envelope.json
    python3 tools/zenodex_mechanism_composition.py verify envelope.json --output result.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

MAX_CAP = 10**18


@dataclass(frozen=True)
class Submission:
    eligible: bool
    claimed: int


@dataclass(frozen=True)
class CompositionResult:
    status: str
    errors: list[str] = field(default_factory=list)
    composition_type: str = ""
    cap1: int = 0
    cap2: int = 0
    sub1_eligible: bool | None = None
    sub2_eligible: bool | None = None
    sub1_claimed: int = 0
    sub2_claimed: int = 0
    sub1_payout: int = 0
    sub2_payout: int = 0
    total_payout: int = 0
    bound: int = 0
    within_bound: bool | None = None


def _safe_int(obj: dict[str, Any], key: str, *, minimum: int, maximum: int) -> int:
    val = obj.get(key)
    if isinstance(val, bool) or not isinstance(val, int):
        raise ValueError(f"{key}_must_be_int")
    if val < minimum:
        raise ValueError(f"{key}_must_be_gte_{minimum}")
    if val > maximum:
        raise ValueError(f"{key}_must_be_lte_{maximum}")
    return val


def _safe_bool(obj: dict[str, Any], key: str) -> bool:
    val = obj.get(key)
    if not isinstance(val, bool):
        raise ValueError(f"{key}_must_be_bool")
    return val


def _payout(cap: int, sub: Submission) -> int:
    if sub.eligible:
        return min(sub.claimed, cap)
    return 0


def parallel_payout(cap1: int, cap2: int, sub1: Submission, sub2: Submission) -> int:
    return _payout(cap1, sub1) + _payout(cap2, sub2)


def series_payout(cap: int, sub1: Submission, sub2: Submission) -> int:
    if sub1.eligible:
        return _payout(cap, sub1)
    return _payout(cap, sub2)


def sample_envelope() -> dict[str, Any]:
    return {
        "composition_type": "parallel",
        "cap1": 100,
        "cap2": 200,
        "sub1": {"eligible": True, "claimed": 50},
        "sub2": {"eligible": True, "claimed": 150},
    }


def _parse_submission(obj: dict[str, Any], prefix: str) -> Submission:
    sub_obj = obj.get(prefix)
    if not isinstance(sub_obj, dict):
        raise ValueError(f"{prefix}_must_be_object")
    eligible = _safe_bool(sub_obj, "eligible")
    claimed = _safe_int(sub_obj, "claimed", minimum=0, maximum=MAX_CAP)
    return Submission(eligible=eligible, claimed=claimed)


def verify_composition_envelope(obj: dict[str, Any]) -> CompositionResult:
    if not isinstance(obj, dict):
        return CompositionResult(status="rejected", errors=["top_level_must_be_object"])

    errors: list[str] = []

    comp_type = obj.get("composition_type")
    if comp_type not in ("parallel", "series"):
        errors.append("composition_type_must_be_parallel_or_series")

    if errors:
        return CompositionResult(status="rejected", errors=errors)

    try:
        cap1 = _safe_int(obj, "cap1", minimum=0, maximum=MAX_CAP)
        cap2 = _safe_int(obj, "cap2", minimum=0, maximum=MAX_CAP)
        sub1 = _parse_submission(obj, "sub1")
        sub2 = _parse_submission(obj, "sub2")
    except ValueError as exc:
        return CompositionResult(status="rejected", errors=[str(exc)])

    if comp_type == "parallel":
        p1 = _payout(cap1, sub1)
        p2 = _payout(cap2, sub2)
        total = p1 + p2
        bound = cap1 + cap2
    else:
        if sub1.eligible:
            p1 = _payout(cap1, sub1)
            p2 = 0
        else:
            p1 = 0
            p2 = _payout(cap1, sub2)
        total = p1 + p2
        bound = cap1
        if cap2 != 0:
            errors.append("series_cap2_should_be_zero")

    within = total <= bound

    if not within:
        errors.append("payout_exceeds_bound")

    status = "accepted" if not errors else "rejected"

    return CompositionResult(
        status=status,
        errors=errors,
        composition_type=comp_type,
        cap1=cap1,
        cap2=cap2,
        sub1_eligible=sub1.eligible,
        sub2_eligible=sub2.eligible,
        sub1_claimed=sub1.claimed,
        sub2_claimed=sub2.claimed,
        sub1_payout=p1,
        sub2_payout=p2,
        total_payout=total,
        bound=bound,
        within_bound=within,
    )


def _write_result(result: CompositionResult, output: Path | None) -> None:
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
        text = Path(args.input).read_text()
        if len(text) > 1_000_000:
            raise ValueError("file_too_large")
        obj = json.loads(text)
        if not isinstance(obj, dict):
            raise ValueError("top_level_must_be_object")
    except Exception as exc:
        result = CompositionResult(
            status="inconclusive",
            errors=[f"load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_composition_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Mechanism Composition Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a composition envelope")
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
