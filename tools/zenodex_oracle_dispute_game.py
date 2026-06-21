#!/usr/bin/env python3
"""Verify ZenoOracle dispute game incentive compatibility.

The dispute game has two strategic constraints:

1. HONEST CHALLENGE PROFITABILITY:
   A challenger who disputes a genuinely wrong report must expect positive
   profit.  Otherwise honest reports go unchallenged and bad values persist.

   profit_honest = p_w * (R_c + MEV_uphold) - D

   Required: profit_honest > 0, i.e. p_w * (R_c + MEV_uphold) > D

2. FRIVOLOUS DISPUTE DETERRENCE:
   A challenger who disputes a correct report must expect negative profit.
   Otherwise the dispute mechanism is weaponized to grief honest reporters.

   profit_frivolous = p_f * (R_c + MEV_uphold) + (1 - p_f) * MEV_reject - D

   Required: profit_frivolous < 0, i.e.
   p_f * (R_c + MEV_uphold) + (1 - p_f) * MEV_reject < D

Combined feasibility (p_w = 1, p_f = 0 simplification):

   R_c + MEV_uphold > D > MEV_reject

which requires R_c + MEV_uphold > MEV_reject as a necessary condition.

Symbols:
  D           = dispute_bond_e8           (challenger upfront cost)
  R_c         = dispute_reward_e8         (challenger reward if upheld)
  MEV_uphold  = mev_uphold_dispute_e8     (extractable value from upheld dispute)
  MEV_reject  = mev_reject_dispute_e8     (extractable value from rejected dispute)
  p_w         = prob_upheld_when_wrong    (in bps, 0..10000)
  p_f         = prob_upheld_when_correct  (in bps, 0..10000)
  slash_amount = reporter_bond * slash_fraction_bps // BPS_SCALE
  required_slash = ceil_div(expected_cheat_gain * (BPS_SCALE + deterrence_margin_bps), BPS_SCALE)

All profit comparisons use exact scaled integer arithmetic (no intermediate flooring):
  honest_profit > 0  iff  p_w * (R_c + MEV_uphold) > D * BPS_SCALE
  frivolous_profit < 0 iff  p_f * (R_c + MEV_uphold) + (BPS_SCALE - p_f) * MEV_reject < D * BPS_SCALE
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

ENVELOPE_SCHEMA = "zenodex.oracle.dispute_game_envelope.v1"
RESULT_SCHEMA = "zenodex.oracle.dispute_game_verify_result.v1"
MAX_ENVELOPE_BYTES = 250_000
MAX_AMOUNT = 10**30
BPS_SCALE = 10_000
MAX_BPS = 10_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")

ENVELOPE_KEYS = {
    "schema",
    "query_id",
    "consumer_module",
    "action_kind",
    "dispute_bond_e8",
    "dispute_reward_e8",
    "dispute_budget_e8",
    "mev_uphold_dispute_e8",
    "mev_reject_dispute_e8",
    "prob_upheld_when_wrong_bps",
    "prob_upheld_when_correct_bps",
    "reporter_bond_required_e8",
    "slash_fraction_bps",
    "expected_cheat_gain_e8",
    "deterrence_margin_bps",
}

NOT_CLAIMED = [
    "does_not_claim_verification_infallibility",
    "does_not_claim_mev_estimate_is_exact",
    "does_not_claim_production_dispute_parameters_live",
    "does_not_claim_reporter_honesty",
]


@dataclass(frozen=True)
class DisputeGameResult:
    status: str
    errors: list[str]
    query_id: str | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    honest_challenge_profit_e8: int | None = None  # rounded summary; feasibility uses exact scaled comparison
    frivolous_dispute_profit_e8: int | None = None  # rounded summary; feasibility uses exact scaled comparison
    slash_amount_e8: int | None = None
    required_deterrence_slash_e8: int | None = None
    profit_feasible: bool | None = None  # True means profit inequalities pass, not full envelope validity

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_id": self.query_id,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "honest_challenge_profit_e8": self.honest_challenge_profit_e8,
            "frivolous_dispute_profit_e8": self.frivolous_dispute_profit_e8,
            "slash_amount_e8": self.slash_amount_e8,
            "required_deterrence_slash_e8": self.required_deterrence_slash_e8,
            "profit_feasible": self.profit_feasible,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def _sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_envelope() -> dict[str, Any]:
    return {
        "schema": ENVELOPE_SCHEMA,
        "query_id": _sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "dispute_bond_e8": 10_000_000,
        "dispute_reward_e8": 15_000_000,
        "dispute_budget_e8": 20_000_000,
        "mev_uphold_dispute_e8": 0,
        "mev_reject_dispute_e8": 0,
        "prob_upheld_when_wrong_bps": 10_000,
        "prob_upheld_when_correct_bps": 0,
        "reporter_bond_required_e8": 250_000_000_000,
        "slash_fraction_bps": 5_000,
        "expected_cheat_gain_e8": 50_000_000_000,
        "deterrence_margin_bps": 2_000,
    }


def _ceil_div(numer: int, denom: int) -> int:
    return (numer + denom - 1) // denom


def _scaled_profit(scaled_gain: int, scaled_bond: int) -> int:
    if scaled_gain > scaled_bond:
        return (scaled_gain - scaled_bond) // BPS_SCALE
    return -_ceil_div(scaled_bond - scaled_gain, BPS_SCALE)


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(obj: Mapping[str, Any], errors: list[str]) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append("dispute_game_field_must_be_string")
        elif key not in ENVELOPE_KEYS:
            errors.append(f"unknown_dispute_game_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int = 0,
    maximum: int = MAX_AMOUNT,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _bps(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    return _int_between(obj, key, errors, minimum=0, maximum=MAX_BPS)


def verify_dispute_game_envelope(obj: Mapping[str, Any]) -> DisputeGameResult:
    errors: list[str] = []
    _unknown_fields(obj, errors)
    if obj.get("schema") != ENVELOPE_SCHEMA:
        errors.append("dispute_game_schema_mismatch")

    query_id = _hash(obj, "query_id", errors)
    consumer_module = _token(obj, "consumer_module", errors)
    action_kind = _token(obj, "action_kind", errors)

    dispute_bond = _int_between(obj, "dispute_bond_e8", errors)
    dispute_reward = _int_between(obj, "dispute_reward_e8", errors)
    dispute_budget = _int_between(obj, "dispute_budget_e8", errors)
    mev_uphold = _int_between(obj, "mev_uphold_dispute_e8", errors)
    mev_reject = _int_between(obj, "mev_reject_dispute_e8", errors)
    p_w_bps = _bps(obj, "prob_upheld_when_wrong_bps", errors)
    p_f_bps = _bps(obj, "prob_upheld_when_correct_bps", errors)
    reporter_bond = _int_between(obj, "reporter_bond_required_e8", errors)
    slash_fraction = _bps(obj, "slash_fraction_bps", errors)
    expected_cheat_gain = _int_between(obj, "expected_cheat_gain_e8", errors)
    deterrence_margin = _bps(obj, "deterrence_margin_bps", errors)

    if dispute_bond is not None and dispute_bond == 0:
        errors.append("dispute_bond_must_be_positive")

    if p_w_bps is not None and p_f_bps is not None and p_w_bps < p_f_bps:
        errors.append("prob_upheld_when_wrong_below_prob_upheld_when_correct")

    if dispute_reward is not None and dispute_budget is not None and dispute_reward > dispute_budget:
        errors.append("dispute_reward_budget_exceeded")

    slash_amount: int | None = None
    required_deterrence_slash: int | None = None
    if reporter_bond is not None and slash_fraction is not None:
        slash_amount = (reporter_bond * slash_fraction) // BPS_SCALE
    if expected_cheat_gain is not None and deterrence_margin is not None:
        required_deterrence_slash = _ceil_div(
            expected_cheat_gain * (BPS_SCALE + deterrence_margin),
            BPS_SCALE,
        )
    if (
        slash_amount is not None
        and required_deterrence_slash is not None
        and slash_amount < required_deterrence_slash
    ):
        errors.append("slash_deterrence_below_required_margin")

    honest_profit: int | None = None
    frivolous_profit: int | None = None
    profit_feasible: bool | None = None

    if (
        dispute_bond is not None
        and dispute_reward is not None
        and mev_uphold is not None
        and mev_reject is not None
        and p_w_bps is not None
        and p_f_bps is not None
    ):
        p_w = p_w_bps
        p_f = p_f_bps
        one_minus_p_f = BPS_SCALE - p_f
        honest_gain = dispute_reward + mev_uphold

        honest_scaled = p_w * honest_gain
        frivolous_scaled = p_f * honest_gain + one_minus_p_f * mev_reject
        bond_scaled = dispute_bond * BPS_SCALE

        honest_profit = _scaled_profit(honest_scaled, bond_scaled)
        frivolous_profit = _scaled_profit(frivolous_scaled, bond_scaled)

        if honest_scaled <= bond_scaled:
            errors.append("honest_challenge_not_profitable")

        if frivolous_scaled >= bond_scaled:
            errors.append("frivolous_dispute_not_deterred")

        profit_feasible = honest_scaled > bond_scaled and frivolous_scaled < bond_scaled

        if p_w == BPS_SCALE and p_f == 0:
            if honest_gain < mev_reject:
                errors.append("dispute_game_infeasible_mev_reject_exceeds_honest_gain")
            elif honest_gain == mev_reject:
                errors.append("dispute_game_infeasible_mev_reject_equals_honest_gain")
            elif honest_gain == mev_reject + 1:
                errors.append("dispute_game_infeasible_adjacent_gap")

    return DisputeGameResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_id=query_id,
        consumer_module=consumer_module,
        action_kind=action_kind,
        honest_challenge_profit_e8=honest_profit,
        frivolous_dispute_profit_e8=frivolous_profit,
        slash_amount_e8=slash_amount,
        required_deterrence_slash_e8=required_deterrence_slash,
        profit_feasible=profit_feasible,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_ENVELOPE_BYTES:
        raise ValueError(f"dispute_game_file_too_large:{size}>{MAX_ENVELOPE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("dispute game root must be a JSON object")
    return obj


def _write_result(result: DisputeGameResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        obj = _load_json(Path(args.input))
    except Exception as exc:
        result = DisputeGameResult(
            status="inconclusive",
            errors=[f"dispute_game_load_failed:{exc}"],
        )
        output_path = Path(args.output) if args.output else None
        _write_result(result, output_path)
        return 3

    result = verify_dispute_game_envelope(obj)
    output_path = Path(args.output) if args.output else None
    _write_result(result, output_path)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    envelope = sample_envelope()
    text = json.dumps(envelope, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(text)
    else:
        Path(args.output).write_text(text, encoding="utf-8")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="ZenoOracle dispute game verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify a dispute game envelope")
    verify.add_argument("input", help="path to the dispute game envelope JSON")
    verify.add_argument("--output", help="optional output path for the result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted dispute game envelope")
    sample.add_argument("--output", help="optional output path for the sample envelope JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
