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


def test_report_integrity_replay_all_passed() -> None:
    subprocess.run([sys.executable, str(ROOT / "check_report_integrity.py")], check=True)
    receipt = json.loads((ROOT / "generated" / "report_integrity_receipt.json").read_text(encoding="utf-8"))
    assert receipt["check_count"] >= 10
    assert receipt["passed_count"] == receipt["check_count"]
    assert receipt["all_passed"] is True


def test_fee_monotonicity_metamorphic_laws() -> None:
    cycle = cycle_module()
    base = _named_policy("fee_surface_launch")

    higher_base = replace(base, base_notional_fee_bps=base.base_notional_fee_bps + 1)
    higher_value = replace(base, value_capture_bps=base.value_capture_bps + 1)
    higher_pro = replace(base, pro_notional_fee_bps=base.pro_notional_fee_bps + 1)

    base_score = cycle.evaluate_policy(base)
    higher_base_score = cycle.evaluate_policy(higher_base)
    higher_value_score = cycle.evaluate_policy(higher_value)
    higher_pro_score = cycle.evaluate_policy(higher_pro)

    assert higher_base_score.gross_protocol_revenue >= base_score.gross_protocol_revenue
    assert higher_base_score.total_user_fee_paid >= base_score.total_user_fee_paid
    assert higher_base_score.total_user_net_value <= base_score.total_user_net_value

    assert higher_value_score.gross_protocol_revenue >= base_score.gross_protocol_revenue
    assert higher_value_score.total_user_fee_paid >= base_score.total_user_fee_paid
    assert higher_value_score.total_user_net_value <= base_score.total_user_net_value

    assert higher_pro_score.gross_protocol_revenue >= base_score.gross_protocol_revenue
    assert higher_pro_score.total_user_fee_paid >= base_score.total_user_fee_paid
    assert higher_pro_score.total_user_net_value <= base_score.total_user_net_value


def test_reward_wash_pressure_metamorphic_law() -> None:
    cycle = cycle_module()
    base = _named_policy("fee_surface_launch")
    higher_rewards = replace(
        base,
        fee_rebate_bps=base.fee_rebate_bps + 1000,
        usage_reward_bps=base.usage_reward_bps + 1000,
    )
    base_score = cycle.evaluate_policy(base)
    higher_score = cycle.evaluate_policy(higher_rewards)

    assert higher_score.gross_protocol_revenue == base_score.gross_protocol_revenue
    assert higher_score.total_user_fee_paid == base_score.total_user_fee_paid
    assert higher_score.wash_profit_max >= base_score.wash_profit_max


def test_sink_split_metamorphic_law() -> None:
    cycle = cycle_module()
    base = _named_policy("fee_surface_launch")
    higher_burn_sink = replace(
        base.sink,
        burn_bps=base.sink.burn_bps + 500,
        user_rebate_bps=base.sink.user_rebate_bps - 500,
    )
    higher_burn = replace(base, sink=higher_burn_sink)

    base_score = cycle.evaluate_policy(base)
    higher_score = cycle.evaluate_policy(higher_burn)

    assert cycle.sink_sum(higher_burn_sink) == cycle.BPS
    assert higher_score.net_protocol_revenue == base_score.net_protocol_revenue
    assert higher_score.burn_budget >= base_score.burn_budget
    assert higher_score.user_rebate_budget <= base_score.user_rebate_budget


def test_floor_bps_boundary_laws() -> None:
    cycle = cycle_module()
    for amount in (0, 1, 7, 10_000, 123_456_789):
        assert cycle.floor_bps(amount, 0) == 0
        assert cycle.floor_bps(amount, cycle.BPS) == amount
        prev = -1
        for bps in (0, 1, 2, 9999, 10_000):
            current = cycle.floor_bps(amount, bps)
            assert current >= prev
            prev = current


def test_receipt_calibration_fixture() -> None:
    subprocess.run([sys.executable, str(ROOT / "calibrate_receipts.py")], check=True)
    report = json.loads((ROOT / "generated" / "receipt_calibration_report.json").read_text(encoding="utf-8"))
    assert report["receipt_count"] == 11
    assert report["accepted_count"] == 9
    assert report["rejected_count"] == 2
    assert report["model_audit"]["total_calibration_invariant_failures"] == 0
    assert report["reject_reason_counts"]["user_fee_exceeds_measured_value"] == 1
    assert report["reject_reason_counts"]["wash_score_rejected"] == 1
    assert report["penalty_revenue_bps"] < 1000
    assert report["primary_recurring_revenue_bps"] > 9000
    assert report["surface_summaries"]["route_surplus_capture"]["suggested_review_cap_bps_of_value"] == 2500


def test_receipt_calibration_rejects_malformed_rows(tmp_path: Path) -> None:
    bad = tmp_path / "bad.jsonl"
    out = tmp_path / "out.json"
    bad.write_text(
        "\n".join(
            [
                '{"schema":"zenodex/fire-revenue-surface-receipt/v1","event_id":"ok","surface":"route_surplus_capture","fee_source":"user","asset":"OUT","notional_units":1000,"measured_value_units":100,"user_fee_paid_units":10,"protocol_revenue_units":10,"direct_cost_units":1,"recurring":true,"primary_revenue":true,"wash_score_bps":0,"eligible_for_retail":true}',
                '{"schema":"bad","event_id":"bad"}',
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    proc = subprocess.run(
        [sys.executable, str(ROOT / "calibrate_receipts.py"), str(bad), "--output", str(out)],
        check=False,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 1
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["accepted_count"] == 1
    assert report["malformed_count"] == 1
    assert report["model_audit"]["total_calibration_invariant_failures"] == 1


def test_fee_cap_recommendations_are_guarded() -> None:
    subprocess.run([sys.executable, str(ROOT / "calibrate_receipts.py")], check=True)
    subprocess.run([sys.executable, str(ROOT / "build_fee_cap_recommendations.py")], check=True)
    report = json.loads((ROOT / "generated" / "fee_cap_recommendations.json").read_text(encoding="utf-8"))
    recs = {row["surface"]: row for row in report["recommendations"]}

    assert report["schema"] == "zenodex/fire-revenue-fee-cap-recommendations/v1"
    assert report["surface_count"] == 11
    assert report["candidate_review_cap_count"] == 6
    assert report["launch_parameter_claim_count"] == 0
    assert report["model_audit"]["total_recommendation_invariant_failures"] == 0

    assert recs["route_surplus_capture"]["status"] == "candidate_review_cap"
    assert recs["route_surplus_capture"]["recommended_user_value_cap_bps"] == 2500
    assert recs["route_surplus_capture"]["hard_value_cap_bps"] == 2500

    assert recs["cow_batch_solver_surplus"]["status"] == "candidate_review_cap"
    assert recs["cow_batch_solver_surplus"]["recommended_user_value_cap_bps"] == 5000
    assert recs["lp_loss_cover_premium"]["recommended_user_value_cap_bps"] == 5000

    assert recs["treasury_market_maker_bot"]["status"] == "protocol_surplus_internal_capture"
    assert recs["treasury_market_maker_bot"]["recommended_user_value_cap_bps"] is None
    assert recs["staking_early_exit_penalty"]["status"] == "penalty_not_primary_revenue"
    assert recs["staking_early_exit_penalty"]["launch_parameter_claim"] is False
    assert recs["extractive_notional_bad"]["status"] == "rejected_only"


def test_fee_cap_recommendations_fail_closed_on_thin_samples(tmp_path: Path) -> None:
    subprocess.run([sys.executable, str(ROOT / "calibrate_receipts.py")], check=True)
    out = tmp_path / "fee_caps.json"
    subprocess.run(
        [
            sys.executable,
            str(ROOT / "build_fee_cap_recommendations.py"),
            "--min-user-fee-samples",
            "2",
            "--output",
            str(out),
        ],
        check=True,
    )
    report = json.loads(out.read_text(encoding="utf-8"))
    recs = {row["surface"]: row for row in report["recommendations"]}

    assert report["candidate_review_cap_count"] == 0
    assert report["status_counts"]["insufficient_user_fee_evidence"] == 6
    assert recs["route_surplus_capture"]["recommended_user_value_cap_bps"] is None
    assert recs["route_surplus_capture"]["status"] == "insufficient_user_fee_evidence"
    assert report["model_audit"]["total_recommendation_invariant_failures"] == 0
