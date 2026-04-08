from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.cantor_region_assurance_bundle import CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA


def test_build_cantor_region_assurance_bundle_writes_expected_json(tmp_path: Path) -> None:
    out_path = tmp_path / "cantor_region_assurance_bundle.json"

    subprocess.run(
        [
            sys.executable,
            "tools/build_cantor_region_assurance_bundle.py",
            "--output",
            str(out_path),
        ],
        check=True,
    )

    payload = json.loads(out_path.read_text(encoding="utf-8"))
    assert payload["schema"] == CANTOR_REGION_ASSURANCE_BUNDLE_SCHEMA
    assert payload["surface_count"] == 4
    assert payload["product_receipt_count"] == 1
    assert payload["product_receipts"][0]["product_cube_count_matches_factor_counts"] is True
