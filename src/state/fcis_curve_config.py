"""Closed curve-configuration values for exact FCIS pool evaluation.

The legacy pool builder accepts convenient raw spellings.  This module owns the
canonical parameter representation consumed by committed-state code.  Exact
decoding accepts one spelling per value and returns one closed variant.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass
from typing import TypeAlias, final

CURVE_TAG_CPMM = "CPMM"
CURVE_TAG_CUBIC_SUM_V1 = "CUBIC_SUM_V1"
CURVE_TAG_SUM_BOOST_V1 = "SUM_BOOST_V1"
CURVE_TAG_QUARTIC_BLEND_V1 = "QUARTIC_BLEND_V1"
CURVE_TAG_QUINTIC_BLEND_V1 = "QUINTIC_BLEND_V1"

MAX_CURVE_PARAMS_CHARACTERS_V1 = 4_096

_POSITIVE_INT_TEXT = r"(?:[1-9][0-9]*)"
_NONNEGATIVE_INT_TEXT = r"(?:0|[1-9][0-9]*)"
_CUBIC_CANONICAL_RE = re.compile(
    rf'^\{{"p":(?P<p>{_POSITIVE_INT_TEXT}),"q":(?P<q>{_POSITIVE_INT_TEXT})\}}$'
)
_SUM_BOOST_CANONICAL_RE = re.compile(
    rf'^\{{"mu_den":(?P<den>{_POSITIVE_INT_TEXT}),'
    rf'"mu_num":(?P<num>{_NONNEGATIVE_INT_TEXT})\}}$'
)
_BLEND_CANONICAL_RE = re.compile(
    rf'^\{{"c_den":(?P<den>{_POSITIVE_INT_TEXT}),'
    rf'"c_num":(?P<num>{_NONNEGATIVE_INT_TEXT})\}}$'
)


def _require_exact_int(value: object, *, minimum: int) -> int:
    if type(value) is not int:
        raise TypeError("curve parameter must be an exact int")
    if value < minimum:
        raise ValueError("curve parameter violates its exact domain")
    return value


def _canonical_decimal_to_int_v1(value: str) -> int:
    """Decode the regex-validated canonical decimal without host coercion."""

    if type(value) is not str or not value:
        raise TypeError("canonical curve integer must be a nonempty string")
    result = 0
    for character in value:
        if character < "0" or character > "9":
            raise ValueError("canonical curve integer contains a nondigit")
        result = result * 10 + (ord(character) - ord("0"))
    return result


@final
@dataclass(frozen=True, slots=True)
class CPMMCurveConfigV1:
    """The parameter-free constant-product curve."""


@final
@dataclass(frozen=True, slots=True)
class CubicSumCurveConfigV1:
    p: int
    q: int

    def __post_init__(self) -> None:
        _require_exact_int(self.p, minimum=1)
        _require_exact_int(self.q, minimum=1)


@final
@dataclass(frozen=True, slots=True)
class SumBoostCurveConfigV1:
    mu_num: int
    mu_den: int

    def __post_init__(self) -> None:
        _require_exact_int(self.mu_num, minimum=0)
        _require_exact_int(self.mu_den, minimum=1)


@final
@dataclass(frozen=True, slots=True)
class QuarticBlendCurveConfigV1:
    c_num: int
    c_den: int

    def __post_init__(self) -> None:
        _require_canonical_rational(self.c_num, self.c_den)


@final
@dataclass(frozen=True, slots=True)
class QuinticBlendCurveConfigV1:
    c_num: int
    c_den: int

    def __post_init__(self) -> None:
        _require_canonical_rational(self.c_num, self.c_den)


ExactCurveConfigV1: TypeAlias = (
    CPMMCurveConfigV1
    | CubicSumCurveConfigV1
    | SumBoostCurveConfigV1
    | QuarticBlendCurveConfigV1
    | QuinticBlendCurveConfigV1
)


def create_pool_curve_config_v1(
    curve_tag: str | None,
    curve_params: str | None,
) -> ExactCurveConfigV1:
    """Resolve the source-owned CREATE_POOL defaults into one exact variant."""

    if curve_tag is None:
        if curve_params is not None and curve_params != "":
            raise ValueError("CPMM pools must not specify curve_params")
        return CPMMCurveConfigV1()
    if type(curve_tag) is not str:
        raise TypeError("curve_tag must be an exact string or None")
    if curve_params is not None and type(curve_params) is not str:
        raise TypeError("curve_params must be an exact string or None")
    if curve_params is not None:
        return decode_canonical_curve_config_v1(curve_tag, curve_params)
    if curve_tag == CURVE_TAG_CPMM:
        return CPMMCurveConfigV1()
    if curve_tag == CURVE_TAG_CUBIC_SUM_V1:
        return CubicSumCurveConfigV1(p=1, q=1)
    if curve_tag == CURVE_TAG_SUM_BOOST_V1:
        return SumBoostCurveConfigV1(mu_num=200, mu_den=10_000)
    if curve_tag == CURVE_TAG_QUARTIC_BLEND_V1:
        return QuarticBlendCurveConfigV1(c_num=8, c_den=1)
    if curve_tag == CURVE_TAG_QUINTIC_BLEND_V1:
        return QuinticBlendCurveConfigV1(c_num=2, c_den=1)
    raise ValueError(f"unsupported curve_tag: {curve_tag!r}")


def _require_canonical_rational(numerator: object, denominator: object) -> None:
    num = _require_exact_int(numerator, minimum=0)
    den = _require_exact_int(denominator, minimum=1)
    if (num == 0 and den != 1) or (num > 0 and math.gcd(num, den) != 1):
        raise ValueError("curve rational parameter is not canonical")


def canonicalize_curve_rational_v1(numerator: int, denominator: int) -> tuple[int, int]:
    """Return the unique non-negative lowest-terms rational pair."""

    num = _require_exact_int(numerator, minimum=0)
    den = _require_exact_int(denominator, minimum=1)
    if num == 0:
        return 0, 1
    divisor = math.gcd(num, den)
    return num // divisor, den // divisor


def encode_cubic_sum_params_v1(p: int, q: int) -> str:
    value = CubicSumCurveConfigV1(p=p, q=q)
    return f'{{"p":{value.p},"q":{value.q}}}'


def encode_sum_boost_params_v1(mu_num: int, mu_den: int) -> str:
    value = SumBoostCurveConfigV1(mu_num=mu_num, mu_den=mu_den)
    return f'{{"mu_den":{value.mu_den},"mu_num":{value.mu_num}}}'


def encode_blend_params_v1(c_num: int, c_den: int) -> str:
    canonical_num, canonical_den = canonicalize_curve_rational_v1(c_num, c_den)
    return f'{{"c_den":{canonical_den},"c_num":{canonical_num}}}'


def canonical_curve_config_fields_v1(value: ExactCurveConfigV1) -> tuple[str, str]:
    """Encode one closed curve value into its unique committed fields."""

    if type(value) is CPMMCurveConfigV1:
        return CURVE_TAG_CPMM, ""
    if type(value) is CubicSumCurveConfigV1:
        return CURVE_TAG_CUBIC_SUM_V1, encode_cubic_sum_params_v1(value.p, value.q)
    if type(value) is SumBoostCurveConfigV1:
        return CURVE_TAG_SUM_BOOST_V1, encode_sum_boost_params_v1(
            value.mu_num,
            value.mu_den,
        )
    if type(value) is QuarticBlendCurveConfigV1:
        return CURVE_TAG_QUARTIC_BLEND_V1, encode_blend_params_v1(
            value.c_num,
            value.c_den,
        )
    if type(value) is QuinticBlendCurveConfigV1:
        return CURVE_TAG_QUINTIC_BLEND_V1, encode_blend_params_v1(
            value.c_num,
            value.c_den,
        )
    raise TypeError("curve configuration must be an exact closed variant")


def _require_exact_curve_fields(curve_tag: object, curve_params: object) -> tuple[str, str]:
    if type(curve_tag) is not str or not curve_tag:
        raise TypeError("curve_tag must be an exact non-empty string")
    if type(curve_params) is not str:
        raise TypeError("curve_params must be an exact string")
    if len(curve_params) > MAX_CURVE_PARAMS_CHARACTERS_V1:
        raise ValueError("curve_params exceeds its character bound")
    return curve_tag, curve_params


def decode_canonical_curve_config_v1(
    curve_tag: str,
    curve_params: str,
) -> ExactCurveConfigV1:
    """Decode an already-canonical committed curve configuration."""

    tag, params = _require_exact_curve_fields(curve_tag, curve_params)
    if tag == CURVE_TAG_CPMM:
        if params:
            raise ValueError("CPMM pools must not specify curve_params")
        return CPMMCurveConfigV1()
    if tag == CURVE_TAG_CUBIC_SUM_V1:
        match = _CUBIC_CANONICAL_RE.fullmatch(params)
        if match is None:
            raise ValueError("curve_params is not canonical CUBIC_SUM_V1 JSON")
        return CubicSumCurveConfigV1(
            p=_canonical_decimal_to_int_v1(match.group("p")),
            q=_canonical_decimal_to_int_v1(match.group("q")),
        )
    if tag == CURVE_TAG_SUM_BOOST_V1:
        match = _SUM_BOOST_CANONICAL_RE.fullmatch(params)
        if match is None:
            raise ValueError("curve_params is not canonical SUM_BOOST_V1 JSON")
        return SumBoostCurveConfigV1(
            mu_num=_canonical_decimal_to_int_v1(match.group("num")),
            mu_den=_canonical_decimal_to_int_v1(match.group("den")),
        )
    if tag == CURVE_TAG_QUARTIC_BLEND_V1:
        match = _BLEND_CANONICAL_RE.fullmatch(params)
        if match is None:
            raise ValueError("curve_params is not canonical QUARTIC_BLEND_V1 JSON")
        value = QuarticBlendCurveConfigV1(
            c_num=_canonical_decimal_to_int_v1(match.group("num")),
            c_den=_canonical_decimal_to_int_v1(match.group("den")),
        )
        return value
    if tag == CURVE_TAG_QUINTIC_BLEND_V1:
        match = _BLEND_CANONICAL_RE.fullmatch(params)
        if match is None:
            raise ValueError("curve_params is not canonical QUINTIC_BLEND_V1 JSON")
        return QuinticBlendCurveConfigV1(
            c_num=_canonical_decimal_to_int_v1(match.group("num")),
            c_den=_canonical_decimal_to_int_v1(match.group("den")),
        )
    raise ValueError(f"unsupported curve_tag: {tag!r}")
