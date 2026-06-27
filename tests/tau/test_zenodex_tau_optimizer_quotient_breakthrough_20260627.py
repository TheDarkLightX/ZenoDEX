from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tau_optimizer_quotient_breakthrough_20260627 import (
    ASSET_A,
    ASSET_B,
    build_quotient_certificate,
    enumerate_route_labels,
    route_cases,
    verify_quotient_certificate,
)


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_optimizer_quotient_breakthrough_20260627" / "report.json"


def test_optimizer_quotient_breakthrough_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_optimizer_quotient_breakthrough_20260627.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["breakthrough"]["spec_id"] == "optimizer_quotient_certificate_v1"
    assert report["tau"]["ok"] is True
    assert report["route_quotient"]["case_count"] == 3
    assert report["route_quotient"]["max_label_count"] > 40
    assert report["route_quotient"]["min_compression_ratio"] > 5.0
    assert {case["case_id"] for case in report["tau"]["cases"]} >= {
        "route_quotient_pass",
        "ab_work_item_1_pass",
        "cow_work_item_2_pass",
        "authority_reject",
    }
    assert all(not row["accepted"] for row in report["mutation_checks"])


def test_quotient_certificate_mutations_fail_closed() -> None:
    case = route_cases()[0]
    labels = enumerate_route_labels(case.pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=case.amount_out)
    certificate = build_quotient_certificate(labels)

    assert verify_quotient_certificate(certificate, labels)["ok"] is True

    bad_hash = dict(certificate)
    bad_hash["domain_hash"] = "0" * 64
    assert verify_quotient_certificate(bad_hash, labels)["ok"] is False

    bad_selected = dict(certificate)
    bad_selected["selected_route_id"] = labels[-1].route_id
    assert verify_quotient_certificate(bad_selected, labels)["ok"] is False

    bad_count = dict(certificate)
    bad_count["label_count"] = int(certificate["label_count"]) - 1
    assert verify_quotient_certificate(bad_count, labels)["ok"] is False
