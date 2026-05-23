from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.cantor_region_assurance_bundle import build_default_cantor_region_assurance_bundle


def test_check_cantor_region_backend_invariance_cli_accepts_prefix_vs_bdd(tmp_path: Path) -> None:
    out_path = tmp_path / "invariant_bundle.json"

    subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_backend_invariance.py",
            "--left",
            "prefix",
            "--right",
            "bdd",
            "--output",
            str(out_path),
        ],
        check=True,
    )

    assert json.loads(out_path.read_text(encoding="utf-8")) == build_default_cantor_region_assurance_bundle().to_dict()


def test_check_cantor_region_backend_invariance_cli_rejects_unknown_backend() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_cantor_region_backend_invariance.py",
            "--left",
            "unknown",
        ],
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    assert "unsupported RegionBA backend" in proc.stderr
