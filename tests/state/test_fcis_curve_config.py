from __future__ import annotations

import pytest

import src.state.fcis_curve_config as exact_curve_config
from src.state.fcis_curve_config import (
    CURVE_TAG_CPMM,
    CURVE_TAG_CUBIC_SUM_V1,
    CURVE_TAG_QUARTIC_BLEND_V1,
    CURVE_TAG_QUINTIC_BLEND_V1,
    CURVE_TAG_SUM_BOOST_V1,
    CPMMCurveConfigV1,
    CubicSumCurveConfigV1,
    QuarticBlendCurveConfigV1,
    QuinticBlendCurveConfigV1,
    SumBoostCurveConfigV1,
    canonical_curve_config_fields_v1,
    decode_canonical_curve_config_v1,
)
from src.state.pools import (
    normalize_curve_config,
    parse_cubic_sum_params,
    parse_quartic_blend_params,
    parse_quintic_blend_params,
    parse_sum_boost_params,
)

CANONICAL_CASES = (
    (CPMMCurveConfigV1(), (CURVE_TAG_CPMM, "")),
    (
        CubicSumCurveConfigV1(p=3, q=5),
        (CURVE_TAG_CUBIC_SUM_V1, '{"p":3,"q":5}'),
    ),
    (
        SumBoostCurveConfigV1(mu_num=200, mu_den=10_000),
        (CURVE_TAG_SUM_BOOST_V1, '{"mu_den":10000,"mu_num":200}'),
    ),
    (
        QuarticBlendCurveConfigV1(c_num=2, c_den=3),
        (CURVE_TAG_QUARTIC_BLEND_V1, '{"c_den":3,"c_num":2}'),
    ),
    (
        QuinticBlendCurveConfigV1(c_num=3, c_den=5),
        (CURVE_TAG_QUINTIC_BLEND_V1, '{"c_den":5,"c_num":3}'),
    ),
)


@pytest.mark.parametrize(("value", "fields"), CANONICAL_CASES)
def test_exact_curve_codec_has_one_round_trip(value: object, fields: tuple[str, str]) -> None:
    assert canonical_curve_config_fields_v1(value) == fields  # type: ignore[arg-type]
    assert decode_canonical_curve_config_v1(*fields) == value


@pytest.mark.parametrize(
    ("tag", "params"),
    (
        ("cpmm", ""),
        (CURVE_TAG_CPMM, "{}"),
        (CURVE_TAG_CUBIC_SUM_V1, '{"q":5,"p":3}'),
        (CURVE_TAG_CUBIC_SUM_V1, '{"p":3, "q":5}'),
        (CURVE_TAG_CUBIC_SUM_V1, '{"p":03,"q":5}'),
        (CURVE_TAG_CUBIC_SUM_V1, '{"p":3,"q":5,"x":1}'),
        (CURVE_TAG_CUBIC_SUM_V1, '{"p":3,"p":3,"q":5}'),
        (CURVE_TAG_SUM_BOOST_V1, '{"mu_den":10000,"mu_num":-1}'),
        (CURVE_TAG_QUARTIC_BLEND_V1, '{"c_den":4,"c_num":2}'),
        (CURVE_TAG_QUINTIC_BLEND_V1, '{"c_den":2,"c_num":0}'),
    ),
)
def test_exact_curve_codec_rejects_noncanonical_spelling(tag: str, params: str) -> None:
    with pytest.raises((TypeError, ValueError)):
        decode_canonical_curve_config_v1(tag, params)


@pytest.mark.parametrize(
    ("raw_tag", "raw_params", "expected"),
    (
        ("cpmm", {}, (CURVE_TAG_CPMM, "")),
        (
            " cubic_sum_v1 ",
            {"p": 3, "q": 5},
            (CURVE_TAG_CUBIC_SUM_V1, '{"p":3,"q":5}'),
        ),
        (
            CURVE_TAG_SUM_BOOST_V1,
            '{"mu_num":200,"mu_den":10000}',
            (CURVE_TAG_SUM_BOOST_V1, '{"mu_den":10000,"mu_num":200}'),
        ),
        (
            CURVE_TAG_QUARTIC_BLEND_V1,
            {"c_num": 2, "c_den": 4},
            (CURVE_TAG_QUARTIC_BLEND_V1, '{"c_den":2,"c_num":1}'),
        ),
        (
            CURVE_TAG_QUINTIC_BLEND_V1,
            {"c_num": 0, "c_den": 99},
            (CURVE_TAG_QUINTIC_BLEND_V1, '{"c_den":1,"c_num":0}'),
        ),
    ),
)
def test_legacy_builder_normalization_retains_public_behavior(
    raw_tag: object,
    raw_params: object,
    expected: tuple[str, str],
) -> None:
    assert normalize_curve_config(curve_tag=raw_tag, curve_params=raw_params) == expected
    assert decode_canonical_curve_config_v1(*expected) == decode_canonical_curve_config_v1(
        *normalize_curve_config(curve_tag=raw_tag, curve_params=raw_params)
    )


@pytest.mark.parametrize(
    ("legacy", "payload", "expected"),
    (
        (parse_cubic_sum_params, '{"q":5,"p":3,"x":1}', (3, 5)),
        (
            parse_sum_boost_params,
            '{"mu_num":200,"mu_den":10000,"x":1}',
            (200, 10_000),
        ),
        (
            parse_quartic_blend_params,
            '{"c_num":2,"c_den":3,"x":1}',
            (2, 3),
        ),
        (
            parse_quintic_blend_params,
            '{"c_num":3,"c_den":5,"x":1}',
            (3, 5),
        ),
    ),
)
def test_legacy_parsers_retain_public_result(
    legacy: object,
    payload: str,
    expected: tuple[int, int],
) -> None:
    assert callable(legacy)
    assert legacy(payload) == expected


def test_exact_curve_module_exposes_no_legacy_json_parser() -> None:
    assert "json" not in exact_curve_config.__dict__
    assert not any(name.endswith("_legacy_v1") for name in exact_curve_config.__dict__)
