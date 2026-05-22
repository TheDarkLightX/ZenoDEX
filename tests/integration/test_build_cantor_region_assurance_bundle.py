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

def test_build_cantor_region_assurance_bundle_bdd_backend_matches_prefix_payload(tmp_path: Path) -> None:
    prefix_path = tmp_path / "prefix_bundle.json"
    bdd_path = tmp_path / "bdd_bundle.json"

    subprocess.run(
        [
            sys.executable,
            "tools/build_cantor_region_assurance_bundle.py",
            "--output",
            str(prefix_path),
            "--backend",
            "prefix",
        ],
        check=True,
    )
    subprocess.run(
        [
            sys.executable,
            "tools/build_cantor_region_assurance_bundle.py",
            "--output",
            str(bdd_path),
            "--backend",
            "bdd",
        ],
        check=True,
    )

    assert json.loads(prefix_path.read_text(encoding="utf-8")) == json.loads(bdd_path.read_text(encoding="utf-8"))
