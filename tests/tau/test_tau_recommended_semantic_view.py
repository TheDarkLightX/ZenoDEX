from __future__ import annotations

import subprocess

from src.integration.tau_runner import ROOT
from tools.check_tau_recommended_semantic_view import validate_tau_recommended_semantic_view


def test_check_tau_recommended_semantic_view() -> None:
    result = validate_tau_recommended_semantic_view()
    assert result.errors == []
    assert result.spec_count == len(list((ROOT / "src" / "tau_specs" / "recommended").glob("*.tau")))
    assert result.extractable_count == result.spec_count

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
