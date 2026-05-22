from __future__ import annotations

from tools.upba_v1_grid_economic_profile import (
    PROFILES,
    evaluate_profile,
    profile_by_id,
    weakened_for_test,
)


def test_builtin_upba_v1_grid_profiles_are_accepted() -> None:
    for profile in PROFILES.values():
        report = evaluate_profile(profile)

        assert report["accepted"] is True
        assert report["checks"] == {
            "grid_num_within_runtime_domain": True,
            "grid_den_within_runtime_domain": True,
            "supported_price_band_ordered": True,
            "min_price_has_positive_grid_candidate": True,
            "max_price_representable_at_grid_den": True,
            "grid_domain_covers_supported_price_band": True,
            "all_supported_rational_prices_within_epsilon": True,
            "representative_rational_prices_within_epsilon": True,
            "relative_error_negligible": True,
            "output_error_negligible": True,
        }
        assert report["bounds"]["grid_step"]["numerator"] == 1
        assert report["bounds"]["rational_price_epsilon"]["denominator"] == (
            2 * profile.max_grid_den
        )
        assert report["bounds"]["relative_error_margin_bps"] >= 0
        assert report["bounds"]["output_error_margin_units"] >= 0
        universal_bound = report["universal_rational_price_bound"]
        assert universal_bound["accepted"] is True
        assert universal_bound["kind"] == "nearest_integer_grid_interval_cover_v1"
        assert universal_bound["grid_num_min"] == 1
        assert universal_bound["grid_num_max"] == profile.max_grid_num
        assert universal_bound["grid_den"] == profile.max_grid_den
        assert universal_bound["epsilon"] == report["bounds"]["rational_price_epsilon"]
        assert all(universal_bound["assumptions"].values())
        assert set(report["rounding_witnesses"]) == {
            "min_supported_price",
            "mid_supported_price",
            "max_supported_price",
        }
        assert report["profile_hash"].startswith("0x")
        assert len(report["profile_hash"]) == 66


def test_upba_v1_grid_profile_rejects_coarse_denominator() -> None:
    profile = weakened_for_test(
        profile_by_id("production_deep_v1"),
        max_grid_den=100,
        max_grid_num=1_000,
    )

    report = evaluate_profile(profile)

    assert report["accepted"] is False
    assert report["checks"]["relative_error_negligible"] is False
    assert report["checks"]["output_error_negligible"] is False


def test_upba_v1_grid_profile_rejects_unrepresentable_max_price() -> None:
    profile = weakened_for_test(
        profile_by_id("production_wide_v1"),
        max_grid_num=100,
    )

    report = evaluate_profile(profile)

    assert report["accepted"] is False
    assert report["checks"]["max_price_representable_at_grid_den"] is False


def test_upba_v1_grid_profile_witnesses_non_grid_rational_prices() -> None:
    profile = weakened_for_test(
        profile_by_id("production_deep_v1"),
        max_grid_num=10,
        max_grid_den=10,
        min_supported_price_num=1,
        min_supported_price_den=3,
        max_supported_price_num=2,
        max_supported_price_den=3,
        max_gross_input_per_fill=1,
        negligible_relative_error_bps=2_000,
        negligible_output_error_units=2,
    )

    report = evaluate_profile(profile)

    assert report["accepted"] is True
    assert report["bounds"]["rational_price_epsilon"] == {
        "numerator": 1,
        "denominator": 20,
        "decimal": "0.05",
    }
    assert report["rounding_witnesses"]["min_supported_price"]["grid_num"] == 3
    assert report["rounding_witnesses"]["min_supported_price"]["abs_error"] == {
        "numerator": 1,
        "denominator": 30,
        "decimal": "0.03333333333333333",
    }


def test_upba_v1_grid_profile_rejects_min_price_without_positive_grid_candidate() -> None:
    profile = weakened_for_test(
        profile_by_id("production_deep_v1"),
        min_supported_price_num=1,
        min_supported_price_den=100_000_000,
        max_grid_den=10,
        max_grid_num=100,
    )

    report = evaluate_profile(profile)

    assert report["accepted"] is False
    assert report["bounds"]["min_grid_num_at_min_price"] == 1
    assert report["checks"]["min_price_has_positive_grid_candidate"] is False
    assert report["checks"]["grid_domain_covers_supported_price_band"] is False
    assert report["checks"]["all_supported_rational_prices_within_epsilon"] is False
    assert report["universal_rational_price_bound"]["accepted"] is False
    assert (
        report["universal_rational_price_bound"]["assumptions"][
            "min_scaled_price_at_least_first_grid_num"
        ]
        is False
    )
    assert report["checks"]["relative_error_negligible"] is False


def test_upba_v1_grid_profile_rejects_inverted_supported_price_band() -> None:
    profile = weakened_for_test(
        profile_by_id("production_deep_v1"),
        min_supported_price_num=2,
        min_supported_price_den=1,
        max_supported_price_num=1,
        max_supported_price_den=1,
    )

    report = evaluate_profile(profile)

    assert report["accepted"] is False
    assert report["checks"]["supported_price_band_ordered"] is False
    assert report["checks"]["grid_domain_covers_supported_price_band"] is False
    assert report["checks"]["all_supported_rational_prices_within_epsilon"] is False
