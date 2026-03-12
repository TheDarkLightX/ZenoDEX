from __future__ import annotations

import subprocess

from src.integration.tau_runner import ROOT


def test_check_tau_recommended_semantic_view() -> None:
    proc = subprocess.run(
        [
            "python3",
            "tools/check_tau_recommended_semantic_view.py",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "recommended semantic view specs:" in proc.stdout
    assert "equation-surface extractable:" in proc.stdout
