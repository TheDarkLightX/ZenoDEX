from __future__ import annotations

import json
from pathlib import Path

from tools.check_cantor_shapeforge_promotion import (
    check_cantor_shapeforge_promotion,
    main,
)


def test_check_cantor_shapeforge_promotion_returns_current_counts(tmp_path: Path) -> None:
    report_path = tmp_path / "bridge.json"

    result = check_cantor_shapeforge_promotion(output_report=report_path)

    assert result["ok"] is True
    assert result["world_model_id"] == "zenodex_shape_reference_v3"
    assert result["mapped_surface_count"] == 4
    assert result["unmapped_surface_count"] == 0
    payload = json.loads(report_path.read_text(encoding="utf-8"))
    assert payload["backend_invariance"]["payload_equal"] is True


def test_check_cantor_shapeforge_promotion_cli_rejects_invalid_world_model(tmp_path: Path) -> None:
    source = Path("docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json")
    payload = json.loads(source.read_text(encoding="utf-8"))
    payload["schema"] = "bad/schema"
    world_model_path = tmp_path / "bad-world-model.json"
    world_model_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    assert main(["--world-model", str(world_model_path)]) == 1
