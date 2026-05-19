from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]


def test_julia_negative_curriculum_receipt_has_epiplexity_proxy(
    tmp_path: Path,
) -> None:
    julia = shutil.which("julia")
    if julia is None:
        pytest.skip("julia executable is not available")

    output_json = tmp_path / "negative_curriculum.json"
    output_markdown = tmp_path / "negative_curriculum.md"
    subprocess.run(
        [
            julia,
            "tools/zenoenergy_negative_curriculum.jl",
            "--input",
            "data/upba_energy/upba_v2_suffix_bound_adversarial_family_stress_seed20260545.json",
            "--output-json",
            str(output_json),
            "--output-markdown",
            str(output_markdown),
        ],
        cwd=ROOT,
        check=True,
    )

    receipt = json.loads(output_json.read_text(encoding="utf-8"))
    markdown = output_markdown.read_text(encoding="utf-8")

    assert receipt["schema"] == "zenodex/energy/negative_curriculum/v1"
    assert receipt["evaluated_batches"] == 118
    assert receipt["family_count"] == 8
    assert receipt["total_cases"] == 944
    assert (
        receipt["recommended_disqualifier_sample_weights"]["output_mismatch_count"]
        > 1.0
    )

    proxy = receipt["bounded_epiplexity_proxy"]
    assert proxy["schema"] == "zenodex/energy/bounded_epiplexity_proxy/v1"
    assert proxy["classification"] == "measurable_bounded_structure"
    assert proxy["score"] > 0.0
    assert proxy["policy_separation"] == pytest.approx(0.375)
    assert "correctness certificate" in proxy["boundary"]

    assert "Bounded Epiplexity Proxy" in markdown
    assert "Academic Hooks" in markdown
    assert "LeCun" in markdown
