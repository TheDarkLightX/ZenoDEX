from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT_JSON = ROOT / "generated" / "zenodex_ab_cow_algorithm_breakthrough_20260627" / "report.json"


def test_zenodex_ab_cow_algorithm_breakthrough_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_ab_cow_algorithm_breakthrough_20260627.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["authority_boundary"] == (
        "The Tau spec admits certificates only. It has no settlement-authorizing output."
    )
    assert report["tau_envelope"]["ok"] is True
    assert {case["case_id"] for case in report["tau_envelope"]["cases"]} == {
        "ab_item_1_pass",
        "cow_item_2_pass",
        "coupled_capacity_reject",
        "two_modes_reject",
    }

    ab = report["ab_ordering"]
    assert ab["ok"] is True
    assert all(case["ok"] for case in ab["exactness_cases"])
    assert ab["measured_n8"]["same_order"] is True
    assert ab["n12_permutation_vs_compressed_proxy"]["permutations"] == 479_001_600
    assert ab["n12_permutation_vs_compressed_proxy"]["n_squared_times_2_to_n"] == 589_824
    assert "not claimed as a universal runtime bound" in ab["n12_permutation_vs_compressed_proxy"]["scope_note"]

    cow = report["cow_matching"]
    assert cow["ok"] is True
    assert all(case["ok"] for case in cow["exactness_cases"])
    assert all(case["uncoupled_balance_safe"] for case in cow["exactness_cases"])
    assert cow["measured_6x6"]["same_economic_key"] is True
    assert "not claimed byte-identical" in cow["current_core_policy"]["tie_scope"]
    assert cow["n20_perfect_matching_vs_hungarian_proxy"]["n_cubed"] == 8_000
