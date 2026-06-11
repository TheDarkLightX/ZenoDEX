"""Wave 0 charter grounding checks."""

from __future__ import annotations

import subprocess
import sys


def test_h_md_xd_001_charter_paths_are_grounded() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "experiments/mechanism_design_math_v1/tools/check_charter_grounding.py",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_h_md_xd_002_crosswalk_covers_charter_obligations() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "experiments/mechanism_design_math_v1/tools/check_crosswalk.py",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
