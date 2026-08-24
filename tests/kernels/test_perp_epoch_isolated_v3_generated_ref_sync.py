from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
ESSO_ROOT = ROOT / "external" / "ESSO"
MODEL = ROOT / "src" / "kernels" / "dex" / "perp_epoch_isolated_v3.yaml"
CHECKED_IN_REF = ROOT / "generated" / "perp_python" / "perp_epoch_isolated_v3_ref.py"


def _esso_env() -> dict[str, str]:
    env = os.environ.copy()
    if ESSO_ROOT.is_dir():
        current = env.get("PYTHONPATH", "")
        env["PYTHONPATH"] = str(ESSO_ROOT) if not current else f"{ESSO_ROOT}:{current}"
    return env


def test_generated_reference_is_exact_export_of_normative_model(tmp_path: Path) -> None:
    """A model edit cannot leave the checked-in parity oracle stale."""
    env = _esso_env()
    availability = subprocess.run(
        [sys.executable, "-c", "import ESSO"],
        env=env,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    if availability.returncode != 0:
        pytest.skip("ESSO is required to check generated-reference synchronization")

    subprocess.run(
        [
            sys.executable,
            "-m",
            "ESSO",
            "export-python",
            str(MODEL),
            "--output",
            str(tmp_path),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )

    regenerated = tmp_path / CHECKED_IN_REF.name
    assert regenerated.read_bytes() == CHECKED_IN_REF.read_bytes()
