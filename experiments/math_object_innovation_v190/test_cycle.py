#!/usr/bin/env python3
from __future__ import annotations

import json
import shutil
import subprocess
import sys
from dataclasses import replace
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"
_REPORT_CACHE: dict | None = None
_CYCLE_MODULE = None


def cycle_module():
    global _CYCLE_MODULE
    if _CYCLE_MODULE is None:
        spec = spec_from_file_location("v190_run_cycle", ROOT / "run_cycle.py")
        assert spec is not None
        assert spec.loader is not None
        module = module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _CYCLE_MODULE = module
    return _CYCLE_MODULE


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


def _named_policy(name: str):
    cycle = cycle_module()
    for policy in cycle.NAMED_POLICIES:
        if policy.name == name:
            return policy
    raise AssertionError(f"missing policy {name}")


def _mutate_surface(score, surface_name: str, **changes: int):
    surfaces = list(score.surfaces)
    for idx, surface in enumerate(surfaces):
        if surface.surface == surface_name:
            surfaces[idx] = replace(surface, **changes)
            return replace(score, surfaces=tuple(surfaces))
    raise AssertionError(f"missing surface {surface_name}")


def test_model_audit_detects_known_bug_classes() -> None:
    cycle = cycle_module()
    zero = cycle.evaluate_policy(_named_policy("zero_fee"))
    launch = cycle.evaluate_policy(_named_policy("fee_surface_launch"))
    extractive = cycle.evaluate_policy(_named_policy("extractive_notional"))

    mutants = {
        "negative_gross_revenue": _mutate_surface(
            zero,
            "lp_loss_cover_premium",
            protocol_revenue_gross=-250,
        ),
        "wrong_user_net_identity": _mutate_surface(
            launch,
            "route_surplus_capture",
            user_net_value=999_999,
        ),
        "wrong_net_revenue_identity": _mutate_surface(
            launch,
            "lp_loss_cover_premium",
            protocol_revenue_net=999_999,
        ),
        "sink_budget_overallocation": replace(
            launch,
            burn_budget=launch.net_protocol_revenue + 1,
            treasury_budget=launch.net_protocol_revenue + 1,
        ),
        "false_survivor_flag": replace(extractive, survivor=True),
    }

    for mutant in mutants.values():
        audit = cycle.audit_scores([mutant])
        assert audit["total_model_invariant_failures"] > 0


def test_mutation_receipt_all_detected() -> None:
    subprocess.run([sys.executable, str(ROOT / "run_mutation_checks.py")], check=True)
    receipt = json.loads((ROOT / "generated" / "model_mutation_receipt.json").read_text(encoding="utf-8"))
    assert receipt["mutant_count"] == 5
    assert receipt["detected_count"] == 5
    assert receipt["all_detected"] is True
