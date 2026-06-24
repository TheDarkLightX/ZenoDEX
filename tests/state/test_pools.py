from __future__ import annotations

import re
from collections.abc import Callable

import pytest

from src.state import pools
from src.state.pools import (
    CURVE_TAG_CUBIC_SUM_V1,
    CURVE_TAG_QUARTIC_BLEND_V1,
    CURVE_TAG_QUINTIC_BLEND_V1,
    CURVE_TAG_SUM_BOOST_V1,
    normalize_curve_config,
    parse_cubic_sum_params,
    parse_quartic_blend_params,
    parse_quintic_blend_params,
    parse_sum_boost_params,
)


@pytest.mark.parametrize(
    "curve_tag",
    [
        CURVE_TAG_CUBIC_SUM_V1,
        CURVE_TAG_SUM_BOOST_V1,
        CURVE_TAG_QUARTIC_BLEND_V1,
        CURVE_TAG_QUINTIC_BLEND_V1,
    ],
)
def test_normalize_curve_config_rejects_malformed_json(curve_tag: str) -> None:
    with pytest.raises(ValueError, match=re.escape(f"invalid curve_params JSON for {curve_tag}:")):
        normalize_curve_config(curve_tag=curve_tag, curve_params="{")


@pytest.mark.parametrize(
    "parser",
    [
        parse_cubic_sum_params,
        parse_sum_boost_params,
        parse_quartic_blend_params,
        parse_quintic_blend_params,
    ],
)
def test_curve_param_parsers_reject_malformed_json(parser: Callable[[str], tuple[int, int]]) -> None:
    with pytest.raises(ValueError, match="invalid curve_params JSON:"):
        parser("{")


def test_curve_param_parser_unexpected_loader_error_propagates(monkeypatch: pytest.MonkeyPatch) -> None:
    def boom(_raw: str) -> object:
        raise RuntimeError("json loader unavailable")

    monkeypatch.setattr(pools.json, "loads", boom)

    with pytest.raises(RuntimeError, match="json loader unavailable"):
        parse_cubic_sum_params('{"p":1,"q":1}')


def test_normalize_curve_config_unexpected_loader_error_propagates(monkeypatch: pytest.MonkeyPatch) -> None:
    def boom(_raw: str) -> object:
        raise RuntimeError("json loader unavailable")

    monkeypatch.setattr(pools.json, "loads", boom)

    with pytest.raises(RuntimeError, match="json loader unavailable"):
        normalize_curve_config(curve_tag=CURVE_TAG_CUBIC_SUM_V1, curve_params='{"p":1,"q":1}')
