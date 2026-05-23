#!/usr/bin/env python3
"""Evaluate UPBA v1 price-grid economic sufficiency profiles."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, replace
from fractions import Fraction
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.uniform_batch_clearing import UNIFORM_BATCH_PRICE_RATIO_MAX  # noqa: E402
from src.state.canonical import canonical_json_bytes, sha256_hex  # noqa: E402


@dataclass(frozen=True)
class UPBAV1GridEconomicProfile:
    profile_id: str
    max_grid_num: int
    max_grid_den: int
    min_supported_price_num: int
    min_supported_price_den: int
    max_supported_price_num: int
    max_supported_price_den: int
    max_gross_input_per_fill: int
    negligible_relative_error_bps: int
    negligible_output_error_units: int


PROFILES: dict[str, UPBAV1GridEconomicProfile] = {
    "production_deep_v1": UPBAV1GridEconomicProfile(
        profile_id="production_deep_v1",
        max_grid_num=100_000_000,
        max_grid_den=10_000_000,
        min_supported_price_num=1,
        min_supported_price_den=1_000,
        max_supported_price_num=10,
        max_supported_price_den=1,
        max_gross_input_per_fill=1_000_000,
        negligible_relative_error_bps=1,
        negligible_output_error_units=2,
    ),
    "production_wide_v1": UPBAV1GridEconomicProfile(
        profile_id="production_wide_v1",
        max_grid_num=1_000_000_000,
        max_grid_den=100_000_000,
        min_supported_price_num=1,
        min_supported_price_den=100_000,
        max_supported_price_num=10,
        max_supported_price_den=1,
        max_gross_input_per_fill=10_000_000,
        negligible_relative_error_bps=5,
        negligible_output_error_units=2,
    ),
}


def evaluate_profile(profile: UPBAV1GridEconomicProfile) -> dict[str, Any]:
    _validate_positive_profile(profile)
    min_price = Fraction(profile.min_supported_price_num, profile.min_supported_price_den)
    max_price = Fraction(profile.max_supported_price_num, profile.max_supported_price_den)
    mid_price = (min_price + max_price) / 2
    grid_step = Fraction(1, profile.max_grid_den)
    abs_price_error_upper = Fraction(1, 2 * profile.max_grid_den)
    relative_error_bps_upper = _ceil_fraction(abs_price_error_upper * 10_000 / min_price)
    output_error_units_upper = (
        _ceil_fraction(profile.max_gross_input_per_fill * abs_price_error_upper) + 1
    )
    min_price_scaled = min_price * profile.max_grid_den
    min_grid_num_at_min_price = _ceil_fraction(min_price_scaled)
    required_num_at_max_price = _ceil_fraction(max_price * profile.max_grid_den)
    supported_price_band_ordered = min_price <= max_price
    grid_domain_covers_supported_band = (
        supported_price_band_ordered
        and min_price_scaled >= 1
        and required_num_at_max_price <= profile.max_grid_num
    )
    universal_bound = _universal_rational_price_bound(
        profile=profile,
        min_price=min_price,
        max_price=max_price,
        min_price_scaled=min_price_scaled,
        required_num_at_max_price=required_num_at_max_price,
        abs_price_error_upper=abs_price_error_upper,
    )
    rounding_witnesses = {
        "min_supported_price": _nearest_grid_witness(profile, min_price),
        "mid_supported_price": _nearest_grid_witness(profile, mid_price),
        "max_supported_price": _nearest_grid_witness(profile, max_price),
    }
    checks = {
        "grid_num_within_runtime_domain": profile.max_grid_num <= UNIFORM_BATCH_PRICE_RATIO_MAX,
        "grid_den_within_runtime_domain": profile.max_grid_den <= UNIFORM_BATCH_PRICE_RATIO_MAX,
        "supported_price_band_ordered": supported_price_band_ordered,
        "min_price_has_positive_grid_candidate": min_price_scaled >= 1,
        "max_price_representable_at_grid_den": required_num_at_max_price <= profile.max_grid_num,
        "grid_domain_covers_supported_price_band": grid_domain_covers_supported_band,
        "all_supported_rational_prices_within_epsilon": universal_bound["accepted"],
        "representative_rational_prices_within_epsilon": all(
            _fraction_from_obj(witness["abs_error"]) <= abs_price_error_upper
            and int(witness["grid_num"]) <= profile.max_grid_num
            for witness in rounding_witnesses.values()
        ),
        "relative_error_negligible": (
            relative_error_bps_upper <= profile.negligible_relative_error_bps
        ),
        "output_error_negligible": (
            output_error_units_upper <= profile.negligible_output_error_units
        ),
    }
    report: dict[str, Any] = {
        "schema": "zenodex/upba_v1_grid_economic_profile_report/v1",
        "profile": asdict(profile),
        "bounds": {
            "grid_step": _fraction_obj(grid_step),
            "rational_price_epsilon": _fraction_obj(abs_price_error_upper),
            "absolute_price_error_upper": _fraction_obj(abs_price_error_upper),
            "relative_error_bps_upper": relative_error_bps_upper,
            "output_error_units_upper": output_error_units_upper,
            "min_price_scaled_by_grid_den": _fraction_obj(min_price_scaled),
            "min_grid_num_at_min_price": min_grid_num_at_min_price,
            "required_num_at_max_price": required_num_at_max_price,
            "relative_error_margin_bps": (
                profile.negligible_relative_error_bps - relative_error_bps_upper
            ),
            "output_error_margin_units": (
                profile.negligible_output_error_units - output_error_units_upper
            ),
        },
        "universal_rational_price_bound": universal_bound,
        "rounding_witnesses": rounding_witnesses,
        "checks": checks,
        "accepted": all(checks.values()),
    }
    report["profile_hash"] = sha256_hex(canonical_json_bytes(report))
    return report


def profile_by_id(profile_id: str) -> UPBAV1GridEconomicProfile:
    try:
        return PROFILES[profile_id]
    except KeyError as exc:
        known = ", ".join(sorted(PROFILES))
        raise ValueError(f"unknown UPBA v1 grid profile {profile_id!r}; known profiles: {known}") from exc


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES),
        help="Evaluate one built-in profile. Defaults to all profiles.",
    )
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = parser.parse_args()

    profiles = [profile_by_id(args.profile)] if args.profile else [PROFILES[key] for key in sorted(PROFILES)]
    reports = [evaluate_profile(profile) for profile in profiles]
    accepted = all(report["accepted"] for report in reports)
    if args.json:
        print(
            json.dumps(
                {
                    "schema": "zenodex/upba_v1_grid_economic_profile_collection/v1",
                    "accepted": accepted,
                    "reports": reports,
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        for report in reports:
            profile = report["profile"]
            bounds = report["bounds"]
            status = "accepted" if report["accepted"] else "rejected"
            print(
                f"{profile['profile_id']}: {status}; "
                f"relative_error_bps_upper={bounds['relative_error_bps_upper']}; "
                f"output_error_units_upper={bounds['output_error_units_upper']}"
            )
    return 0 if accepted else 1


def _validate_positive_profile(profile: UPBAV1GridEconomicProfile) -> None:
    for field_name, value in asdict(profile).items():
        if field_name == "profile_id":
            if not isinstance(value, str) or not value:
                raise ValueError("profile_id must be a non-empty string")
            continue
        if isinstance(value, bool) or not isinstance(value, int):
            raise TypeError(f"{field_name} must be an integer")
        if value <= 0:
            raise ValueError(f"{field_name} must be positive")


def _ceil_fraction(value: Fraction) -> int:
    return (value.numerator + value.denominator - 1) // value.denominator


def _floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def _nearest_grid_witness(
    profile: UPBAV1GridEconomicProfile,
    price: Fraction,
) -> dict[str, Any]:
    scaled = price * profile.max_grid_den
    lower = max(1, _floor_fraction(scaled))
    upper = min(profile.max_grid_num, lower + 1)
    candidates = (lower, upper)
    best_num = min(
        candidates,
        key=lambda num: (
            abs(Fraction(num, profile.max_grid_den) - price),
            num,
        ),
    )
    grid_price = Fraction(best_num, profile.max_grid_den)
    return {
        "target_price": _fraction_obj(price),
        "grid_num": best_num,
        "grid_den": profile.max_grid_den,
        "grid_price": _fraction_obj(grid_price),
        "abs_error": _fraction_obj(abs(grid_price - price)),
    }


def _universal_rational_price_bound(
    *,
    profile: UPBAV1GridEconomicProfile,
    min_price: Fraction,
    max_price: Fraction,
    min_price_scaled: Fraction,
    required_num_at_max_price: int,
    abs_price_error_upper: Fraction,
) -> dict[str, Any]:
    assumptions = {
        "grid_den_positive": profile.max_grid_den > 0,
        "grid_num_positive": profile.max_grid_num > 0,
        "supported_price_band_ordered": min_price <= max_price,
        "min_scaled_price_at_least_first_grid_num": min_price_scaled >= 1,
        "ceil_max_scaled_price_within_grid_num": (
            required_num_at_max_price <= profile.max_grid_num
        ),
    }
    accepted = all(assumptions.values())
    return {
        "kind": "nearest_integer_grid_interval_cover_v1",
        "statement": (
            "for every rational price p in the supported band, nearest-integer "
            "rounding of p * grid_den gives a bounded grid numerator n with "
            "abs(p - n / grid_den) <= 1 / (2 * grid_den)"
        ),
        "supported_price_min": _fraction_obj(min_price),
        "supported_price_max": _fraction_obj(max_price),
        "grid_num_min": 1,
        "grid_num_max": profile.max_grid_num,
        "grid_den": profile.max_grid_den,
        "epsilon": _fraction_obj(abs_price_error_upper),
        "rounding_rule": "nearest integer to p * grid_den, lower numerator wins exact ties",
        "assumptions": assumptions,
        "accepted": accepted,
    }


def _fraction_obj(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": int(value.numerator),
        "denominator": int(value.denominator),
        "decimal": str(float(value)),
    }


def _fraction_from_obj(value: dict[str, Any]) -> Fraction:
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def weakened_for_test(
    profile: UPBAV1GridEconomicProfile,
    **changes: Any,
) -> UPBAV1GridEconomicProfile:
    return replace(profile, **changes)


if __name__ == "__main__":
    raise SystemExit(main())
