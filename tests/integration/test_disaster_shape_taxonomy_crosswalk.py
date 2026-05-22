from __future__ import annotations

import json
from pathlib import Path

from tools.check_disaster_shape_taxonomy_crosswalk import (
    DEFAULT_CROSSWALK,
    check_crosswalk,
)


def test_disaster_shape_taxonomy_crosswalk_covers_current_axes() -> None:
    result = check_crosswalk(DEFAULT_CROSSWALK)

    assert result["ok"] is True
    assert result["known_axis_count"] == 125
    assert result["mapped_axis_count"] == result["known_axis_count"]
    assert result["unmapped_axis_count"] == 0
    assert result["orphan_mapping_count"] == 0


def test_disaster_shape_taxonomy_crosswalk_rejects_unknown_axis(tmp_path: Path) -> None:
    payload = json.loads(DEFAULT_CROSSWALK.read_text(encoding="utf-8"))
    payload["entries"][0]["mapped_axis_ids"].append("not_a_real_disaster_axis")
    candidate = tmp_path / "bad_crosswalk.json"
    candidate.write_text(json.dumps(payload), encoding="utf-8")

    result = check_crosswalk(candidate)

    assert result["ok"] is False
    assert any("not_a_real_disaster_axis" in error for error in result["errors"])
