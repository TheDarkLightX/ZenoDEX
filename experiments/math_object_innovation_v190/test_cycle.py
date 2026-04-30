#!/usr/bin/env python3
from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"
_REPORT_CACHE: dict | None = None


def load_report() -> dict:
    global _REPORT_CACHE
    if _REPORT_CACHE is None:
        subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
        _REPORT_CACHE = json.loads(REPORT.read_text(encoding="utf-8"))
    return _REPORT_CACHE


def test_report_has_survivors() -> None:
    report = load_report()
    assert report["candidate_policy_count"] > 100_000
    assert report["survivor_count"] > 0
    assert report["best_survivor"]["survivor"] is True
    assert report["best_survivor"]["net_protocol_revenue"] > 0
    assert report["model_audit"]["total_model_invariant_failures"] == 0


def test_best_survivor_is_not_penalty_dependent() -> None:
    report = load_report()
    best = report["best_survivor"]
    assert best["recurring_revenue_bps"] >= 9000
    assert best["primary_recurring_revenue_bps"] >= 8500
    assert best["penalty_dependency_bps"] <= 1000


def test_zero_fee_is_not_revenue_generating() -> None:
    report = load_report()
    zero_fee = report["named_policies"]["zero_fee"]
    assert zero_fee["gross_protocol_revenue"] == 0
    assert zero_fee["survivor"] is False


def test_extractive_notional_rejected() -> None:
    report = load_report()
    extractive = report["named_policies"]["extractive_notional"]
    assert extractive["survivor"] is False
    assert extractive["negative_user_surface_count"] > 0


def test_wash_rebate_farm_rejected() -> None:
    report = load_report()
    farm = report["named_policies"]["wash_rebate_farm"]
    assert farm["survivor"] is False
    assert farm["wash_profit_max"] > 0 or farm["rail_violation_count"] > 0


def test_subsidized_passive_yield_rejected() -> None:
    report = load_report()
    passive = report["named_policies"]["subsidized_passive_yield"]
    assert passive["survivor"] is False
    assert passive["rail_violation_count"] > 0 or passive["deflation_margin"] <= 0


def test_optional_julia_probe_matches_python_named_accounting() -> None:
    if shutil.which("julia") is None:
        import pytest

        pytest.skip("Julia is not installed")
    report = load_report()
    subprocess.run(["julia", str(ROOT / "run_julia_probe.jl")], check=True)
    rows = {}
    for line in (ROOT / "generated" / "julia_probe.tsv").read_text(encoding="utf-8").splitlines()[1:]:
        policy, gross, net, user_fee, _user_net = line.split("\t")
        rows[policy] = {
            "gross_protocol_revenue": int(gross),
            "net_protocol_revenue": int(net),
            "total_user_fee_paid": int(user_fee),
        }
    for policy in ("zero_fee", "fee_surface_launch", "surplus_bot_heavy", "extractive_notional", "penalty_dependency"):
        assert rows[policy]["gross_protocol_revenue"] == report["named_policies"][policy]["gross_protocol_revenue"]
        assert rows[policy]["net_protocol_revenue"] == report["named_policies"][policy]["net_protocol_revenue"]
        assert rows[policy]["total_user_fee_paid"] == report["named_policies"][policy]["total_user_fee_paid"]
