#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle economic security envelopes."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.oracle_economic_security import (  # noqa: E402
    BPS_SCALE,
    ENVELOPE_KEYS,
    ENVELOPE_SCHEMA,
    MAX_AMOUNT,
    MAX_COUNT,
    MAX_MARGIN_BPS,
    SHA256_RE,
    TOKEN_RE,
    EconomicSecurityResult,
    verify_economic_security_envelope,
)

__all__ = [
    "BPS_SCALE",
    "ENVELOPE_KEYS",
    "ENVELOPE_SCHEMA",
    "MAX_AMOUNT",
    "MAX_COUNT",
    "MAX_MARGIN_BPS",
    "SHA256_RE",
    "TOKEN_RE",
    "EconomicSecurityResult",
    "sample_envelope",
    "verify_economic_security_envelope",
]


MAX_ENVELOPE_BYTES = 250_000


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_envelope() -> dict[str, Any]:
    return {
        "schema": ENVELOPE_SCHEMA,
        "query_id": sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "notional_value_e8": 1_000_000_000_000,
        "max_extractable_value_e8": 50_000_000_000,
        "attack_cost_floor_e8": 75_000_000_000,
        "required_attack_margin_bps": 2_000,
        "reporter_count": 3,
        "reporter_reward_budget_e8": 120_000_000,
        "reporter_reward_per_report_e8": 30_000_000,
        "honest_reporter_cost_e8": 20_000_000,
        "honest_reporter_risk_premium_e8": 5_000_000,
        "reporter_bond_required_e8": 250_000_000_000,
        "slash_fraction_bps": 5_000,
        "expected_cheat_gain_e8": 50_000_000_000,
        "deterrence_margin_bps": 2_000,
        "dispute_reward_e8": 10_000_000,
        "dispute_budget_e8": 20_000_000,
        "fee_paid_e8": 100_000_000,
        "reporter_fee_share_e8": 30_000_000,
        "treasury_fee_share_e8": 40_000_000,
        "burn_fee_share_e8": 30_000_000,
    }


def _load_json(path: Path) -> dict[str, Any]:
    size = path.stat().st_size
    if size > MAX_ENVELOPE_BYTES:
        raise ValueError(
            f"economic_security_file_too_large:{size}>{MAX_ENVELOPE_BYTES}"
        )
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if type(obj) is not dict:
        raise ValueError("economic security root must be an exact JSON object")
    return obj


def _write_result(result: EconomicSecurityResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        envelope = _load_json(Path(args.envelope))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = EconomicSecurityResult(
            status="inconclusive",
            errors=(f"economic_security_load_failed:{exc}",),
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_economic_security_envelope(envelope)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_envelope(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser(
        "verify",
        help="verify an Oracle economic security envelope",
    )
    verify.add_argument(
        "envelope",
        help="path to an economic security envelope JSON file",
    )
    verify.add_argument(
        "--output",
        help="optional output path for the verifier result JSON",
    )
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser(
        "sample",
        help="emit a minimal accepted economic security envelope",
    )
    sample.add_argument(
        "--output",
        help="optional output path for the sample envelope JSON",
    )
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
