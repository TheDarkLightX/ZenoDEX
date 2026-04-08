from __future__ import annotations

import json
from pathlib import Path

from tools.build_cantor_shapeforge_bridge_report import main


def test_build_cantor_shapeforge_bridge_report_cli(tmp_path: Path) -> None:
    out_path = tmp_path / "cantor-shapeforge-bridge.json"

    assert main(["--output", str(out_path)]) == 0
    payload = json.loads(out_path.read_text(encoding="utf-8"))

    assert payload["world_model_id"] == "zenodex_shape_reference_v3"
    assert payload["mapped_surface_count"] == 3
    assert payload["backend_invariance"]["payload_equal"] is True
