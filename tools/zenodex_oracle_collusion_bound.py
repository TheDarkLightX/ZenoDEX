#!/usr/bin/env python3
"""ZenoDEX Oracle Collusion Bound Verifier.

Verifies collusion resistance of oracle dispute game bonds under three
bonding models:
  1. Per-identity bond, per-head reward (collusion-invariant)
  2. Per-identity bond, split reward (deterrence-amplifying)
  3. Shared bond, per-head reward (collusion-vulnerable, bond must scale with k)

Mathematical model (BPS-scaled integer arithmetic, no floats):
  BPS = 10000
  frivolous_scaled = p_f * G + (BPS - p_f) * M_rej
  bond_scaled = D * BPS

  Single reporter deterred:    frivolous_scaled < bond_scaled
  Per-head collusion deterred:  frivolous_scaled < bond_scaled  (invariant)
  Split collusion deterred:     frivolous_scaled < k * bond_scaled  (amplified)
  Shared bond deterred:         k * frivolous_scaled < bond_scaled  (requires scaling)

Critical median_3 value-at-risk gate:
  median_control_threshold = reporter_count // 2 + 1
  median_control_possible = controlled_reporter_count >= median_control_threshold
  slash_amount = reporter_bond_required_e8 * slash_fraction_bps // BPS
  expected_downside_scaled = detection_probability_bps * slash_amount
                           + future_value_lost_e8 * BPS
  required_downside_scaled = critical_value_at_risk_e8
                            * (BPS + deterrence_margin_bps)
  max_critical_value_at_risk_e8 = expected_downside_scaled
                                  // (BPS + deterrence_margin_bps)

  If median_control_possible, require:
    expected_downside_scaled >= required_downside_scaled

Usage:
    python3 tools/zenodex_oracle_collusion_bound.py sample > envelope.json
    python3 tools/zenodex_oracle_collusion_bound.py verify envelope.json
    python3 tools/zenodex_oracle_collusion_bound.py verify envelope.json --output result.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

BPS_SCALE = 10_000
MAX_BPS = 10_000
MAX_AMOUNT = 10**30
MAX_COALITION = 10_000

REQUIRED_FIELDS = (
    "query_id",
    "consumer_module",
    "action_kind",
    "reporter_count",
    "controlled_reporter_count",
    "critical_value_at_risk_e8",
    "dispute_reward_e8",
    "mev_uphold_dispute_e8",
    "mev_reject_dispute_e8",
    "dispute_bond_e8",
    "reporter_bond_required_e8",
    "slash_fraction_bps",
    "detection_probability_bps",
    "future_value_lost_e8",
    "deterrence_margin_bps",
    "prob_upheld_when_wrong_bps",
    "prob_upheld_when_correct_bps",
    "coalition_size",
    "bond_model",
    "reward_model",
)
ALLOWED_FIELDS = set(REQUIRED_FIELDS)


@dataclass(frozen=True)
class CollusionResult:
    status: str  # "accepted" | "rejected" | "inconclusive"
    errors: list[str] = field(default_factory=list)
    query_id: str = ""
    consumer_module: str = ""
    action_kind: str = ""
    reporter_count: int = 0
    controlled_reporter_count: int = 0
    median_control_threshold: int = 0
    critical_value_at_risk_e8: int = 0
    coalition_size: int = 0
    bond_model: str = ""
    reward_model: str = ""
    frivolous_scaled: int = 0
    bond_scaled: int = 0
    slash_amount_e8: int = 0
    expected_downside_scaled: int = 0
    required_downside_scaled: int = 0
    max_critical_value_at_risk_e8: int = 0
    single_deterred: bool | None = None
    collusion_deterred: bool | None = None
    collusion_invariant: bool | None = None
    median_control_possible: bool | None = None
    value_at_risk_downside_ok: bool | None = None
    required_shared_bond_e8: int | None = None


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


def _bps(obj: dict[str, Any], key: str) -> int:
    return _int_between(obj, key, minimum=0, maximum=MAX_BPS)


def _hash(obj: dict[str, Any], key: str) -> str:
    val = obj.get(key)
    if not isinstance(val, str):
        raise ValueError(f"{key}_must_be_sha256")
    if not val.startswith("sha256:"):
        raise ValueError(f"{key}_must_be_sha256")
    hex_part = val[len("sha256:"):]
    if len(hex_part) != 64:
        raise ValueError(f"{key}_must_be_sha256")
    try:
        int(hex_part, 16)
    except ValueError:
        raise ValueError(f"{key}_must_be_sha256") from None
    return val


def _token(obj: dict[str, Any], key: str) -> str:
    val = obj.get(key)
    if not isinstance(val, str):
        raise ValueError(f"{key}_must_be_token")
    if not val.replace(".", "").replace("_", "").isalnum():
        raise ValueError(f"{key}_must_be_token")
    if len(val) < 3 or len(val) > 128:
        raise ValueError(f"{key}_must_be_token")
    return val


def _bond_model(val: Any) -> str:
    if val not in ("per_identity", "shared"):
        raise ValueError("bond_model_must_be_per_identity_or_shared")
    return val


def _reward_model(val: Any) -> str:
    if val not in ("per_head", "split"):
        raise ValueError("reward_model_must_be_per_head_or_split")
    return val


def sample_envelope() -> dict[str, Any]:
    return {
        "query_id": "sha256:011d8c85737df1769f83f0562a682c6dc6b53e8a607e717beb899bf901512b56",
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "reporter_count": 3,
        "controlled_reporter_count": 1,
        "critical_value_at_risk_e8": 50_000_000_000,
        "dispute_reward_e8": 100_000_000,
        "mev_uphold_dispute_e8": 0,
        "mev_reject_dispute_e8": 10_000_000,
        "dispute_bond_e8": 20_000_000,
        "reporter_bond_required_e8": 250_000_000_000,
        "slash_fraction_bps": 5_000,
        "detection_probability_bps": 10_000,
        "future_value_lost_e8": 0,
        "deterrence_margin_bps": 2_000,
        "prob_upheld_when_wrong_bps": 1000,
        "prob_upheld_when_correct_bps": 9000,
        "coalition_size": 5,
        "bond_model": "per_identity",
        "reward_model": "per_head",
    }


def verify_collusion_envelope(obj: dict[str, Any]) -> CollusionResult:
    if not isinstance(obj, dict):
        return CollusionResult(
            status="rejected",
            errors=["top_level_must_be_object"],
        )

    errors: list[str] = []
    for key in obj:
        if not isinstance(key, str):
            errors.append("collusion_field_must_be_string")
        elif key not in ALLOWED_FIELDS:
            errors.append(f"unknown_collusion_field:{key}")

    for field_name in REQUIRED_FIELDS:
        if field_name not in obj:
            errors.append(f"missing_required_field:{field_name}")

    if errors:
        return CollusionResult(status="rejected", errors=errors)

    try:
        query_id = _hash(obj, "query_id")
        consumer_module = _token(obj, "consumer_module")
        action_kind = _token(obj, "action_kind")
        reporter_count = _int_between(obj, "reporter_count", minimum=3, maximum=MAX_COALITION)
        controlled_reporters = _int_between(
            obj,
            "controlled_reporter_count",
            minimum=0,
            maximum=MAX_COALITION,
        )
        value_at_risk = _int_between(obj, "critical_value_at_risk_e8", minimum=0, maximum=MAX_AMOUNT)
        reward = _int_between(obj, "dispute_reward_e8", minimum=1, maximum=MAX_AMOUNT)
        mev_uphold = _int_between(obj, "mev_uphold_dispute_e8", minimum=0, maximum=MAX_AMOUNT)
        mev_reject = _int_between(obj, "mev_reject_dispute_e8", minimum=0, maximum=MAX_AMOUNT)
        bond = _int_between(obj, "dispute_bond_e8", minimum=1, maximum=MAX_AMOUNT)
        reporter_bond = _int_between(obj, "reporter_bond_required_e8", minimum=1, maximum=MAX_AMOUNT)
        slash_fraction = _bps(obj, "slash_fraction_bps")
        detection_probability = _bps(obj, "detection_probability_bps")
        future_value_lost = _int_between(obj, "future_value_lost_e8", minimum=0, maximum=MAX_AMOUNT)
        deterrence_margin = _bps(obj, "deterrence_margin_bps")
        p_f = _bps(obj, "prob_upheld_when_wrong_bps")
        p_w = _bps(obj, "prob_upheld_when_correct_bps")
        coalition = _int_between(obj, "coalition_size", minimum=1, maximum=MAX_COALITION)
        bond_model = _bond_model(obj["bond_model"])
        reward_model = _reward_model(obj["reward_model"])
    except ValueError as exc:
        return CollusionResult(status="rejected", errors=[str(exc)])

    if p_w < p_f:
        errors.append("prob_inversion")
    if controlled_reporters > reporter_count:
        errors.append("controlled_reporter_count_exceeds_reporter_count")

    G = reward + mev_uphold
    honest_gain_scaled = p_w * G
    honest_bond_scaled = bond * BPS_SCALE
    if honest_gain_scaled <= honest_bond_scaled:
        errors.append("honest_challenge_not_profitable")

    one_minus_p_f = BPS_SCALE - p_f
    frivolous_scaled = p_f * G + one_minus_p_f * mev_reject
    bond_scaled = bond * BPS_SCALE

    single_deterred = frivolous_scaled < bond_scaled
    median_control_threshold = (reporter_count // 2) + 1
    median_control_possible = controlled_reporters >= median_control_threshold
    slash_amount = (reporter_bond * slash_fraction) // BPS_SCALE
    expected_downside_scaled = detection_probability * slash_amount + future_value_lost * BPS_SCALE
    required_downside_scaled = value_at_risk * (BPS_SCALE + deterrence_margin)
    max_critical_value_at_risk = expected_downside_scaled // (BPS_SCALE + deterrence_margin)

    value_at_risk_downside_ok = expected_downside_scaled >= required_downside_scaled
    if median_control_possible and not value_at_risk_downside_ok:
        errors.append("median3_control_budget_reaches_threshold")
        errors.append("value_at_risk_downside_below_required_margin")

    if bond_model == "per_identity" and reward_model == "per_head":
        collusion_deterred = single_deterred
        collusion_invariant = True
    elif bond_model == "per_identity" and reward_model == "split":
        collusion_deterred = frivolous_scaled < coalition * bond_scaled
        collusion_invariant = False
    elif bond_model == "shared" and reward_model == "per_head":
        collusion_deterred = coalition * frivolous_scaled < bond_scaled
        collusion_invariant = False
        if not collusion_deterred and single_deterred:
            errors.append("shared_bond_insufficient")
    else:
        return CollusionResult(
            status="rejected",
            errors=["unsupported_bond_reward_combination"],
            query_id=query_id,
            consumer_module=consumer_module,
            action_kind=action_kind,
            coalition_size=coalition,
            bond_model=bond_model,
            reward_model=reward_model,
        )

    if not single_deterred:
        errors.append("single_reporter_not_deterred")

    if not collusion_deterred:
        errors.append("collusion_not_deterred")

    required_shared_bond = None
    if bond_model == "shared" and reward_model == "per_head" and not collusion_deterred:
        required_shared_bond = ((coalition * frivolous_scaled) // BPS_SCALE) + 1

    status = "accepted" if not errors else "rejected"

    return CollusionResult(
        status=status,
        errors=errors,
        query_id=query_id,
        consumer_module=consumer_module,
        action_kind=action_kind,
        reporter_count=reporter_count,
        controlled_reporter_count=controlled_reporters,
        median_control_threshold=median_control_threshold,
        critical_value_at_risk_e8=value_at_risk,
        coalition_size=coalition,
        bond_model=bond_model,
        reward_model=reward_model,
        frivolous_scaled=frivolous_scaled,
        bond_scaled=bond_scaled,
        slash_amount_e8=slash_amount,
        expected_downside_scaled=expected_downside_scaled,
        required_downside_scaled=required_downside_scaled,
        max_critical_value_at_risk_e8=max_critical_value_at_risk,
        single_deterred=single_deterred,
        collusion_deterred=collusion_deterred,
        collusion_invariant=collusion_invariant,
        median_control_possible=median_control_possible,
        value_at_risk_downside_ok=value_at_risk_downside_ok,
        required_shared_bond_e8=required_shared_bond,
    )


def _write_result(result: CollusionResult, output: Path | None) -> None:
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
        result = CollusionResult(
            status="inconclusive",
            errors=[f"collusion_load_failed:{exc}"],
        )
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_collusion_envelope(obj)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX Oracle Collusion Bound Verifier")
    subparsers = parser.add_subparsers(dest="command", required=True)

    p_sample = subparsers.add_parser("sample", help="Print sample envelope")
    p_sample.add_argument("--output", type=str, default="")

    p_verify = subparsers.add_parser("verify", help="Verify a collusion envelope")
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
