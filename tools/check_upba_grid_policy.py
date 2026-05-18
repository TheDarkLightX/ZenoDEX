#!/usr/bin/env python3
"""Check a production-candidate UPBA bounded-grid economic sufficiency policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX  # noqa: E402
from src.core.uniform_batch_clearing import UNIFORM_BATCH_POLICY_V1_ID  # noqa: E402
from src.core.uniform_batch_price_grid_table import (  # noqa: E402
    UPBA_PRICE_GRID_MAX_ROWS,
    UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
)
from src.state.pools import POOL_FEE_BPS_MAX, POOL_FEE_BPS_MIN  # noqa: E402

POLICY_SCHEMA = "zenodex.upba.grid_economic_sufficiency_policy.v1"
REPORT_SCHEMA = "zenodex.upba.grid_economic_sufficiency_check.v1"
BPS_DENOM = 10_000
PPM_DENOM = 1_000_000
DECIMAL_MAX = 36

REQUIRED_NOT_CLAIMS = {
    "does_not_claim_unbounded_rational_optimality",
    "does_not_claim_all_market_conditions",
    "does_not_claim_upba_v2_partial_fill_economic_sufficiency",
    "does_not_claim_multi_hop_or_exact_out",
    "does_not_claim_oracle_fairness_or_inclusion",
}

TOP_LEVEL_KEYS = {
    "schema",
    "policy_id",
    "pool_id",
    "upba_policy_id",
    "score_function_id",
    "base_decimals",
    "quote_decimals",
    "reserve_base_atoms",
    "reserve_quote_atoms",
    "fee_bps",
    "max_trade_input_atoms",
    "max_trade_fraction_bps",
    "grid_max_price_num",
    "grid_max_price_den",
    "economic_price_scale",
    "economic_min_price_scaled",
    "economic_max_price_scaled",
    "economic_tick_size_scaled",
    "rounding_loss_atoms",
    "max_absolute_loss_atoms",
    "min_notional_output_atoms",
    "max_relative_loss_ppm",
    "not_claimed",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _ceil_div(num: int, den: int) -> int:
    if den <= 0:
        raise ValueError("ceil_div denominator must be positive")
    return (num + den - 1) // den


def _int_field(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int | None = None,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    valid = True
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
        valid = False
    if maximum is not None and value > maximum:
        errors.append(f"{key}_above_max:{maximum}")
        valid = False
    return int(value) if valid else None


def _str_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not value:
        errors.append(f"{key}_must_be_nonempty_string")
        return None
    return value


def _unknown_fields(obj: Mapping[str, Any], errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append("policy_field_must_be_string")
        elif key not in TOP_LEVEL_KEYS:
            errors.append(f"unknown_policy_field:{key}")


def _not_claimed(policy: Mapping[str, Any], errors: list[str]) -> list[str]:
    value = policy.get("not_claimed")
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        errors.append("not_claimed_must_be_nonempty_string_list")
        return []
    out = list(value)
    for required in sorted(REQUIRED_NOT_CLAIMS):
        if required not in out:
            errors.append(f"missing_not_claim:{required}")
    return out


def sample_policy() -> dict[str, Any]:
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_id": "",
        "pool_id": "pool_ab",
        "upba_policy_id": UNIFORM_BATCH_POLICY_V1_ID,
        "score_function_id": UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        "base_decimals": 6,
        "quote_decimals": 6,
        "reserve_base_atoms": 1_000_000,
        "reserve_quote_atoms": 1_000_000,
        "fee_bps": 30,
        "max_trade_input_atoms": 1_000,
        "max_trade_fraction_bps": 25,
        "grid_max_price_num": 60,
        "grid_max_price_den": 50,
        "economic_price_scale": 50,
        "economic_min_price_scaled": 40,
        "economic_max_price_scaled": 60,
        "economic_tick_size_scaled": 1,
        "rounding_loss_atoms": 1,
        "max_absolute_loss_atoms": 25,
        "min_notional_output_atoms": 790,
        "max_relative_loss_ppm": 30_000,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def check_policy(policy: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    _unknown_fields(policy, errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("schema_mismatch")

    policy_id = _str_field(policy, "policy_id", errors)
    pool_id = _str_field(policy, "pool_id", errors)
    upba_policy_id = _str_field(policy, "upba_policy_id", errors)
    score_function_id = _str_field(policy, "score_function_id", errors)
    not_claimed = _not_claimed(policy, errors)

    if policy_id is not None and policy_id != policy_content_hash(policy):
        errors.append("policy_id_mismatch")
    if upba_policy_id is not None and upba_policy_id != UNIFORM_BATCH_POLICY_V1_ID:
        errors.append("unsupported_upba_policy_id")
    if score_function_id is not None and score_function_id != UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1:
        errors.append("unsupported_score_function_id")

    base_decimals = _int_field(policy, "base_decimals", errors, minimum=0, maximum=DECIMAL_MAX)
    quote_decimals = _int_field(policy, "quote_decimals", errors, minimum=0, maximum=DECIMAL_MAX)
    reserve_base_atoms = _int_field(
        policy,
        "reserve_base_atoms",
        errors,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    reserve_quote_atoms = _int_field(
        policy,
        "reserve_quote_atoms",
        errors,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    fee_bps = _int_field(policy, "fee_bps", errors, minimum=POOL_FEE_BPS_MIN, maximum=POOL_FEE_BPS_MAX)
    max_trade_input_atoms = _int_field(
        policy,
        "max_trade_input_atoms",
        errors,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    max_trade_fraction_bps = _int_field(
        policy,
        "max_trade_fraction_bps",
        errors,
        minimum=1,
        maximum=BPS_DENOM,
    )
    grid_max_price_num = _int_field(policy, "grid_max_price_num", errors, minimum=1)
    grid_max_price_den = _int_field(policy, "grid_max_price_den", errors, minimum=1)
    economic_price_scale = _int_field(policy, "economic_price_scale", errors, minimum=1)
    economic_min_price_scaled = _int_field(policy, "economic_min_price_scaled", errors, minimum=1)
    economic_max_price_scaled = _int_field(policy, "economic_max_price_scaled", errors, minimum=1)
    economic_tick_size_scaled = _int_field(policy, "economic_tick_size_scaled", errors, minimum=1)
    rounding_loss_atoms = _int_field(policy, "rounding_loss_atoms", errors, minimum=0)
    max_absolute_loss_atoms = _int_field(policy, "max_absolute_loss_atoms", errors, minimum=0)
    min_notional_output_atoms = _int_field(policy, "min_notional_output_atoms", errors, minimum=1)
    max_relative_loss_ppm = _int_field(
        policy,
        "max_relative_loss_ppm",
        errors,
        minimum=0,
        maximum=PPM_DENOM,
    )

    derived: dict[str, Any] = {
        "pool_id": pool_id,
        "policy_id": policy_id,
        "upba_policy_id": upba_policy_id,
        "score_function_id": score_function_id,
    }

    if grid_max_price_num is not None and grid_max_price_den is not None:
        row_count = (grid_max_price_num + 1) * (grid_max_price_den + 1)
        derived["raw_grid_row_count"] = row_count
        if row_count > UPBA_PRICE_GRID_MAX_ROWS:
            errors.append(f"raw_grid_row_count_above_max:{UPBA_PRICE_GRID_MAX_ROWS}")

    if (
        economic_min_price_scaled is not None
        and economic_max_price_scaled is not None
        and economic_tick_size_scaled is not None
    ):
        if economic_min_price_scaled > economic_max_price_scaled:
            errors.append("economic_price_interval_inverted")
        if economic_min_price_scaled % economic_tick_size_scaled != 0:
            errors.append("economic_min_price_not_tick_aligned")
        if economic_max_price_scaled % economic_tick_size_scaled != 0:
            errors.append("economic_max_price_not_tick_aligned")

    if (
        grid_max_price_num is not None
        and economic_max_price_scaled is not None
        and grid_max_price_num < economic_max_price_scaled
    ):
        errors.append("grid_max_price_num_does_not_cover_economic_max_price")
    if (
        grid_max_price_den is not None
        and economic_price_scale is not None
        and grid_max_price_den < economic_price_scale
    ):
        errors.append("grid_max_price_den_does_not_cover_economic_price_scale")

    if (
        max_trade_input_atoms is not None
        and reserve_base_atoms is not None
        and reserve_quote_atoms is not None
        and max_trade_fraction_bps is not None
    ):
        min_reserve = min(reserve_base_atoms, reserve_quote_atoms)
        trade_fraction_bps = _ceil_div(max_trade_input_atoms * BPS_DENOM, min_reserve)
        derived["max_trade_fraction_bps_computed"] = trade_fraction_bps
        if trade_fraction_bps > max_trade_fraction_bps:
            errors.append("max_trade_fraction_bps_exceeded")

    if (
        max_trade_input_atoms is not None
        and fee_bps is not None
        and economic_min_price_scaled is not None
        and economic_tick_size_scaled is not None
        and economic_price_scale is not None
        and rounding_loss_atoms is not None
        and max_absolute_loss_atoms is not None
        and min_notional_output_atoms is not None
        and max_relative_loss_ppm is not None
    ):
        post_fee_input_atoms = max_trade_input_atoms * (BPS_DENOM - fee_bps) // BPS_DENOM
        min_fee_adjusted_notional_output_atoms = (
            post_fee_input_atoms * economic_min_price_scaled // economic_price_scale
        )
        half_tick_error_scaled = _ceil_div(economic_tick_size_scaled, 2)
        raw_grid_loss_atoms = _ceil_div(
            max_trade_input_atoms * half_tick_error_scaled,
            economic_price_scale,
        )
        absolute_loss_bound_atoms = raw_grid_loss_atoms + rounding_loss_atoms
        relative_loss_ppm = _ceil_div(absolute_loss_bound_atoms * PPM_DENOM, min_notional_output_atoms)
        derived.update(
            {
                "post_fee_input_atoms": post_fee_input_atoms,
                "min_fee_adjusted_notional_output_atoms": min_fee_adjusted_notional_output_atoms,
                "half_tick_error_scaled": half_tick_error_scaled,
                "raw_grid_loss_atoms": raw_grid_loss_atoms,
                "absolute_loss_bound_atoms": absolute_loss_bound_atoms,
                "relative_loss_ppm": relative_loss_ppm,
            }
        )
        if min_notional_output_atoms > min_fee_adjusted_notional_output_atoms:
            errors.append("min_notional_output_atoms_above_conservative_fee_adjusted_floor")
        if absolute_loss_bound_atoms > max_absolute_loss_atoms:
            errors.append("absolute_loss_bound_exceeds_policy")
        if relative_loss_ppm > max_relative_loss_ppm:
            errors.append("relative_loss_bound_exceeds_policy")

    # Keep these names in the report so review can see that the economic inputs
    # were parsed and included in the policy commitment.
    derived["base_decimals"] = base_decimals
    derived["quote_decimals"] = quote_decimals
    derived["fee_bps"] = fee_bps

    return {
        "schema": REPORT_SCHEMA,
        "status": "accepted" if not errors else "rejected",
        "ok": not errors,
        "error_count": len(errors),
        "errors": errors,
        "derived": derived,
        "not_claimed": not_claimed,
    }


def _load_policy(path: Path) -> Mapping[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, Mapping):
        raise TypeError("policy must decode to a JSON object")
    return value


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _print_text(report: Mapping[str, Any]) -> None:
    if report["ok"]:
        derived = report["derived"]
        assert isinstance(derived, Mapping)
        print(
            "ok "
            f"absolute_loss_bound_atoms={derived.get('absolute_loss_bound_atoms')} "
            f"relative_loss_ppm={derived.get('relative_loss_ppm')} "
            f"raw_grid_row_count={derived.get('raw_grid_row_count')}"
        )
        return
    print("error: UPBA grid economic sufficiency policy rejected", file=sys.stderr)
    for error in report["errors"]:
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command")

    sample_parser = subparsers.add_parser("sample", help="write a sample accepted policy")
    sample_parser.add_argument("--output", type=Path)

    verify_parser = subparsers.add_parser("verify", help="verify a policy JSON file")
    verify_parser.add_argument("policy", type=Path)
    verify_parser.add_argument("--format", choices=("json", "text"), default="text")

    parser.add_argument("--format", choices=("json", "text"), default="text")
    args = parser.parse_args(argv)

    if args.command == "sample":
        policy = sample_policy()
        if args.output is None:
            print(json.dumps(policy, indent=2, sort_keys=True))
        else:
            _write_json(args.output, policy)
        return 0

    if args.command == "verify":
        report = check_policy(_load_policy(args.policy))
        if args.format == "json":
            print(json.dumps(report, indent=2, sort_keys=True))
        else:
            _print_text(report)
        return 0 if report["ok"] else 1

    report = check_policy(sample_policy())
    if args.format == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_text(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
