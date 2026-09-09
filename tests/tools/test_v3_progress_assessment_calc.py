from __future__ import annotations

import copy
import json
import math
from pathlib import Path

import pytest

from tools import v3_progress_assessment_calc as calculator

REPO_ROOT = Path(__file__).resolve().parents[2]
ASSESSMENT_PATH = REPO_ROOT / "docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json"


def _assessment() -> dict[str, object]:
    return calculator.load_assessment(ASSESSMENT_PATH)


def _rejects(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    contents: str,
    expected_code: str,
) -> None:
    path = tmp_path / "assessment.json"
    path.write_text(contents, encoding="utf-8")

    assert calculator.main([str(path)]) == 2

    report = json.loads(capsys.readouterr().out)
    assert report == {
        "advisory": calculator.ADVISORY,
        "findings": [{"code": expected_code}],
        "ok": False,
    }


def _rejects_data(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    data: dict[str, object],
    expected_code: str,
) -> None:
    _rejects(tmp_path, capsys, json.dumps(data, ensure_ascii=True), expected_code)


def test_given_frozen_assessment_when_calculated_then_matches_independent_weighted_rollup() -> None:
    data = _assessment()
    report = calculator.assess(data)

    for name, expected in (("full_v3", 23.369), ("formal_core", 20.981)):
        section = data[name]
        rows = section["rows"]  # type: ignore[index]
        total_weight = math.fsum(float(row["weight"]) for row in rows)
        central_percent = round(
            100.0
            * math.fsum(float(row["weight"]) * float(row["central"]) for row in rows)
            / total_weight,
            3,
        )
        assert central_percent == expected
        assert report["sections"][name]["central_percent"] == central_percent  # type: ignore[index]

    full_lane = data["full_v3"]["rows"][7]  # type: ignore[index]
    formal_lane = data["formal_core"]["rows"][0]  # type: ignore[index]
    assert (
        abs(
            full_lane["central"]
            - math.fsum(float(capability["c"]) for capability in full_lane["capabilities"])
            / len(full_lane["capabilities"])
        )
        <= calculator.ROW_SCORE_TOLERANCE
    )
    assert (
        abs(
            formal_lane["central"]
            - math.fsum(
                0.3 * float(capability["sem"])
                + 0.4 * float(capability["prf"])
                + 0.3 * float(capability["ref"])
                for capability in formal_lane["capabilities"]
            )
            / len(formal_lane["capabilities"])
        )
        <= calculator.ROW_SCORE_TOLERANCE
    )
    assert report["release_authority"] == data["release_authority"]
    assert report["advisory"] == calculator.ADVISORY


def test_given_malformed_or_nonfinite_json_when_loaded_then_no_score_is_emitted(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _rejects(tmp_path, capsys, "{", "MALFORMED_JSON")
    _rejects(tmp_path, capsys, "[" * 2_000 + "0" + "]" * 2_000, "MALFORMED_JSON")
    for token in ("NaN", "Infinity", "-Infinity", "1e400"):
        _rejects(tmp_path, capsys, '{"value":' + token + "}", "NONFINITE_JSON")


def test_given_duplicate_json_key_when_loaded_then_no_score_is_emitted(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _rejects(
        tmp_path,
        capsys,
        '{"schema":"first","schema":"second"}',
        "DUPLICATE_JSON_KEY",
    )


def test_given_method_denominator_drift_when_calculated_then_it_rejects(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    data = copy.deepcopy(_assessment())
    data["method"]["denominators"]["full_v3"]["weight_points"] = 99  # type: ignore[index]

    _rejects_data(tmp_path, capsys, data, "METHOD_DRIFT")


def test_given_duplicate_workstream_or_changed_capability_order_when_calculated_then_it_rejects(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    duplicated = copy.deepcopy(_assessment())
    duplicated["full_v3"]["rows"][0]["id"] = "W01"  # type: ignore[index]
    _rejects_data(tmp_path, capsys, duplicated, "ROW_LAYOUT")

    reordered = copy.deepcopy(_assessment())
    reordered["full_v3"]["rows"][7]["capabilities"].reverse()  # type: ignore[index]
    _rejects_data(tmp_path, capsys, reordered, "CAPABILITY_IDS")

    dropped = copy.deepcopy(_assessment())
    dropped["formal_core"]["rows"][0]["capabilities"].pop()  # type: ignore[index]
    _rejects_data(tmp_path, capsys, dropped, "CAPABILITY_IDS")

    redistributed = copy.deepcopy(_assessment())
    redistributed["full_v3"]["rows"][7]["weight"] += 0.00001  # type: ignore[index]
    _rejects_data(tmp_path, capsys, redistributed, "ROW_WEIGHT")


def test_given_invalid_numeric_component_or_uncertainty_when_calculated_then_it_rejects(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    boolean_weight = copy.deepcopy(_assessment())
    boolean_weight["full_v3"]["rows"][0]["weight"] = True  # type: ignore[index]
    _rejects_data(tmp_path, capsys, boolean_weight, "NUMERIC")

    inverted_interval = copy.deepcopy(_assessment())
    inverted_interval["full_v3"]["rows"][0]["low"] = 1.0  # type: ignore[index]
    _rejects_data(tmp_path, capsys, inverted_interval, "ROW_ORDER")

    component = copy.deepcopy(_assessment())
    component["formal_core"]["rows"][0]["capabilities"][0]["sem"] = 1.1  # type: ignore[index]
    _rejects_data(tmp_path, capsys, component, "NUMERIC")

    uncertainty = copy.deepcopy(_assessment())
    uncertainty["full_v3"]["rows"][7]["capabilities"][0]["unc"] = "X"  # type: ignore[index]
    _rejects_data(tmp_path, capsys, uncertainty, "UNCERTAINTY")


def test_given_missing_score_field_or_nonfalse_authority_when_calculated_then_it_rejects(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    missing = copy.deepcopy(_assessment())
    del missing["full_v3"]["rows"][0]["low"]  # type: ignore[index]
    _rejects_data(tmp_path, capsys, missing, "ROW_SHAPE")

    authority = copy.deepcopy(_assessment())
    authority["release_authority"]["formal_core_complete"] = 0  # type: ignore[index]
    _rejects_data(tmp_path, capsys, authority, "AUTHORITY_VALUE")
