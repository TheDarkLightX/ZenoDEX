#!/usr/bin/env python3
"""ZenoDEX Sybil Bond Bound Verifier (k-atom generalization).

Verifies Sybil resistance of equal-split reward allocation under a per-identity
bond. The key result: the bond B sized for the 2-atom binding case covers all
k-atom splits for k >= 2, because the post-split denominator n + k - 1 grows
in k, making the RHS B * n * (n + k - 1) larger.

Mathematical model (integer arithmetic, no floats):
  Pre-split payment:   V / n
  Post-split payment:  k * V / (n + k - 1)
  Bond cost:           (k - 1) * B
  Gross gain:          V * (k - 1) * (n - 1) / (n * (n + k - 1))
  Net unprofitable iff V * (n - 1) <= B * n * (n + k - 1)

The k=2 case is binding: n + 2 - 1 = n + 1 is the smallest denominator for
k >= 2. If the bond deters k=2, it deters all k >= 2.

Usage:
    python3 tools/zenodex_sybil_bond_bound.py sample > envelope.json
    python3 tools/zenodex_sybil_bond_bound.py verify envelope.json
    python3 tools/zenodex_sybil_bond_bound.py verify envelope.json --output result.json
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
MAX_K = 10_000

REQUIRED_FIELDS = (
    "pool_id",
    "total_reward_e8",
    "identity_bond_e8",
    "cohort_size",
    "split_atoms",
)


@dataclass(frozen=True)
class SybilBondResult:
    status: str  # "accepted" | "rejected" | "inconclusive"
    errors: list[str] = field(default_factory=list)
    pool_id: str = ""
    total_reward_e8: int = 0
    identity_bond_e8: int = 0
    cohort_size: int = 0
    split_atoms: int = 0
    lhs: int = 0  # V * (n - 1)
    rhs: int = 0  # B * n * (n + k - 1)
    sybil_unprofitable: bool | None = None
    k2_binding: bool | None = None
    covers_all_k: bool | None = None
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
        "pool_id": "zenoproof.bounty-pool-001",
        "total_reward_e8": 100_000_000,
        "identity_bond_e8": 15_000_000,
        "cohort_size": 4,
        "split_atoms": 2,
    }


def verify_sybil_bond_envelope(obj: dict[str, Any]) -> SybilBondResult:
    if not isinstance(obj, dict):
        return SybilBondResult(
            status="rejected",
            errors=["top_level_must_be_object"],
        )

    errors: list[str] = []

    for field_name in REQUIRED_FIELDS:
        if field_name not in obj:
            errors.append(f"missing_required_field:{field_name}")

    if errors:
        return SybilBondResult(status="rejected", errors=errors)

    try:
        pool_id = _token(obj, "pool_id")
        V = _int_between(obj, "total_reward_e8", minimum=1, maximum=MAX_AMOUNT)
        B = _int_between(obj, "identity_bond_e8", minimum=0, maximum=MAX_AMOUNT)
        n = _int_between(obj, "cohort_size", minimum=1, maximum=MAX_N)
        k = _int_between(obj, "split_atoms", minimum=2, maximum=MAX_K)
    except ValueError as exc:
        return SybilBondResult(status="rejected", errors=[str(exc)])

    lhs = V * (n - 1)
    rhs = B * n * (n + k - 1)
    sybil_unprofitable = lhs <= rhs

    k2_lhs = V * (n - 1)
    k2_rhs = B * n * (n + 2 - 1)
    k2_binding = k2_lhs <= k2_rhs

    covers_all_k = k2_binding

    k2_denom = n * (n + 2 - 1)
    k2_required_bond = (k2_lhs + k2_denom - 1) // k2_denom if k2_denom > 0 else 0

    required_bond = None
    if not sybil_unprofitable:
        required_bond = (lhs + n * (n + k - 1) - 1) // (n * (n + k - 1))
    elif not k2_binding:
        required_bond = k2_required_bond

    if not sybil_unprofitable:
        errors.append("sybil_profitable")

    if not k2_binding:
        errors.append("k2_binding_violated")

    status = "accepted" if not errors else "rejected"

    return SybilBondResult(
        status=status,
        errors=errors,
        pool_id=pool_id,
        total_reward_e8=V,
        identity_bond_e8=B,
        cohort_size=n,
        split_atoms=k,
        lhs=lhs,
        rhs=rhs,
        sybil_unprofitable=sybil_unprofitable,
        k2_binding=k2_binding,
        covers_all_k=covers_all_k,
        required_bond_e8=required_bond,
    )


def _write_result(result: SybilBondResult, output: Path | None) -> None:
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
        result = SybilBondResult(
            status="inconclusive",
            errors=[f"sybil_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_sybil_bond_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Sybil Bond Bound Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a Sybil bond envelope")
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
