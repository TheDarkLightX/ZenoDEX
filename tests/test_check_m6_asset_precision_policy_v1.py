from __future__ import annotations

import json
from pathlib import Path

from tools.check_m6_asset_precision_policy_v1 import (
    POLICY_PATH,
    check_m6_asset_precision_policy_v1,
)


def test_current_eight_decimal_policy_is_exact_and_content_derived() -> None:
    report = check_m6_asset_precision_policy_v1()

    assert report["ok"] is True
    assert report["findings"] == []
    assert report["decimal_places"] == 8
    assert report["atoms_per_display_unit"] == 100_000_000
    assert report["production_authority"] is False


def test_checker_kills_decimal_and_rescale_semantic_mutants(tmp_path: Path) -> None:
    policy = json.loads(POLICY_PATH.read_text(encoding="utf-8"))
    policy["decimal_places"] = 18
    policy["rescale_rule"] = "automatic"
    path = tmp_path / "policy.json"
    path.write_text(json.dumps(policy), encoding="utf-8")

    report = check_m6_asset_precision_policy_v1(path)

    assert report["ok"] is False
    assert report["findings"] == ["precision policy content drift"]


def test_checker_rejects_duplicate_policy_fields(tmp_path: Path) -> None:
    path = tmp_path / "policy.json"
    path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")

    report = check_m6_asset_precision_policy_v1(path)

    assert report["ok"] is False
    assert "duplicate JSON key: schema" in report["findings"][0]
