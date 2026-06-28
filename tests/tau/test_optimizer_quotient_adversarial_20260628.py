from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.check_optimizer_quotient_adversarial import (
    REPORT_JSON,
    adversarial_route_cases,
    build_report,
)


ROOT = Path(__file__).resolve().parents[2]


def test_optimizer_quotient_adversarial_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["case_count"] == len(adversarial_route_cases())
    assert report["case_count"] >= 15
    assert report["max_label_count"] > 200
    assert report["min_label_count"] < 10
    assert report["min_compression_ratio"] > 5.0
    assert report["max_compression_ratio"] > 150.0
    assert report["tau"]["ok"] is True
    assert {"direct", "twohop"}.issubset(set(report["selected_route_prefixes"]))
    assert all(row["ok"] for row in report["cases"])
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_optimizer_quotient_adversarial_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/check_optimizer_quotient_adversarial.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["case_count"] == len(adversarial_route_cases())
