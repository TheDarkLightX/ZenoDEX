from __future__ import annotations

import json
from typing import NoReturn

import pytest

from src.state.pools import CURVE_TAG_CUBIC_SUM_V1, normalize_curve_config, parse_cubic_sum_params


def _raise_runtime_error(_payload: str) -> NoReturn:
    raise RuntimeError("json helper bug")


def test_parse_curve_params_rejects_malformed_json() -> None:
    with pytest.raises(ValueError, match="invalid curve_params JSON"):
        parse_cubic_sum_params("{")


def test_normalize_curve_config_rejects_malformed_json() -> None:
    with pytest.raises(ValueError, match=f"invalid curve_params JSON for {CURVE_TAG_CUBIC_SUM_V1}"):
        normalize_curve_config(curve_tag=CURVE_TAG_CUBIC_SUM_V1, curve_params="{")


def test_parse_curve_params_does_not_swallow_json_helper_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(json, "loads", _raise_runtime_error)

    with pytest.raises(RuntimeError, match="json helper bug"):
        parse_cubic_sum_params('{"p":1,"q":1}')


def test_normalize_curve_config_does_not_swallow_json_helper_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(json, "loads", _raise_runtime_error)

    with pytest.raises(RuntimeError, match="json helper bug"):
        normalize_curve_config(curve_tag=CURVE_TAG_CUBIC_SUM_V1, curve_params='{"p":1,"q":1}')
