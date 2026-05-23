from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.cantor_region_backend_invariance_receipt import (
    build_cantor_region_backend_invariance_receipt,
)


def test_build_cantor_region_backend_invariance_receipt_cli_writes_expected_json(tmp_path: Path) -> None:
    out_path = tmp_path / "backend_invariance_receipt.json"

    subprocess.run(
        [
            sys.executable,
            "tools/build_cantor_region_backend_invariance_receipt.py",
            "--left",
            "prefix",
            "--right",
            "bdd",
            "--output",
            str(out_path),
            "--require-equal",
        ],
        check=True,
    )

    assert json.loads(out_path.read_text(encoding="utf-8")) == build_cantor_region_backend_invariance_receipt(
        left_backend="prefix",
        right_backend="bdd",
    ).to_dict()


def test_build_cantor_region_backend_invariance_receipt_cli_rejects_unknown_backend(tmp_path: Path) -> None:
    out_path = tmp_path / "backend_invariance_receipt.json"

    proc = subprocess.run(
        [
            sys.executable,
            "tools/build_cantor_region_backend_invariance_receipt.py",
            "--left",
            "unknown",
            "--output",
            str(out_path),
        ],
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "unsupported RegionBA backend" in proc.stderr
