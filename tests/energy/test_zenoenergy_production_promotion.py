from __future__ import annotations

import json
from pathlib import Path

from tools.check_zenoenergy_production_promotion import (
    build_production_gate_report,
    main,
)


ROOT = Path(__file__).resolve().parents[2]


def test_production_gate_blocks_current_research_without_real_replay() -> None:
    research_replay = json.loads(
        (ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json").read_text(
            encoding="utf-8"
        )
    )

    report = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=None,
        autotrader_real_shadow=None,
        operator_release_enabled=False,
    )

    assert report["schema"] == "zenodex/energy/production_promotion_gate/v1"
    assert report["decision"] == "blocked"
    assert report["promotion_allowed"] is False
    assert "missing real UPBA replay report" in report["blocked_reasons"]
    assert "missing real AutoTrader shadow report" in report["blocked_reasons"]
    assert "operator must explicitly enable advisory ranking-only promotion" in report[
        "blocked_reasons"
    ]
    assert _obligation(report, "research_replay_clean")["passed"] is True


def test_production_gate_allows_ranking_only_when_real_reports_pass() -> None:
    research_replay = json.loads(
        (ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json").read_text(
            encoding="utf-8"
        )
    )

    report = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=_passing_upba_real_replay(),
        autotrader_real_shadow=_passing_autotrader_real_shadow(),
        operator_release_enabled=True,
    )

    assert report["decision"] == "allow_ranking_only"
    assert report["promotion_allowed"] is True
    assert report["blocked_reasons"] == []
    assert all(obligation["passed"] is True for obligation in report["obligations"])
    assert report["safety_contract"]["scorer_authorizes_settlement_or_trade"] is False
    assert report["safety_contract"]["deterministic_fallback_required"] is True


def test_production_gate_blocks_real_report_without_source_manifest() -> None:
    research_replay = json.loads(
        (ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json").read_text(
            encoding="utf-8"
        )
    )
    upba = _passing_upba_real_replay()
    upba.pop("source_manifest")

    report = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=upba,
        autotrader_real_shadow=_passing_autotrader_real_shadow(),
        operator_release_enabled=True,
    )

    assert report["decision"] == "blocked"
    observed = _obligation(report, "upba_real_replay_coverage")["observed"]
    assert isinstance(observed, dict)
    assert observed["source_manifest_ok"] is False


def test_production_gate_blocks_real_report_without_coverage_profile() -> None:
    research_replay = json.loads(
        (ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json").read_text(
            encoding="utf-8"
        )
    )
    upba = _passing_upba_real_replay()
    upba.pop("coverage_profile")

    report = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=upba,
        autotrader_real_shadow=_passing_autotrader_real_shadow(),
        operator_release_enabled=True,
    )

    assert report["decision"] == "blocked"
    observed = _obligation(report, "upba_real_replay_coverage")["observed"]
    assert isinstance(observed, dict)
    assert observed["coverage_profile_ok"] is False


def test_production_gate_cli_writes_blocked_receipt(tmp_path: Path) -> None:
    output_json = tmp_path / "gate.json"
    output_markdown = tmp_path / "gate.md"

    rc = main(
        [
            "--research-replay",
            str(ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json"),
            "--output-json",
            str(output_json),
            "--output-markdown",
            str(output_markdown),
        ]
    )

    assert rc == 0
    report = json.loads(output_json.read_text(encoding="utf-8"))
    assert report["decision"] == "blocked"
    assert report["promotion_allowed"] is False
    assert "missing real UPBA replay report" in report["blocked_reasons"]
    assert "decision: blocked" in output_markdown.read_text(encoding="utf-8")


def _obligation(report: dict[str, object], obligation_id: str) -> dict[str, object]:
    obligations = report["obligations"]
    assert isinstance(obligations, list)
    for obligation in obligations:
        assert isinstance(obligation, dict)
        if obligation["id"] == obligation_id:
            return obligation
    raise AssertionError(f"missing obligation {obligation_id}")


def _passing_upba_real_replay() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_real_replay_report/v1",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "batch_count": 1_250,
        "candidate_count": 25_000,
        "market_day_count": 9,
        "invalid_accept_count": 0,
        "permutation_violation_count": 0,
        "top_25_recall": 0.995,
        "learned_mean_verifier_calls": 1.8,
        "hand_mean_verifier_calls": 2.5,
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "source_manifest": _passing_source_manifest_check(),
        "coverage_profile": _passing_coverage_profile(
            "upba",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        ),
    }


def _passing_autotrader_real_shadow() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/autotrader_real_shadow_report/v1",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:autotrader:2026-05-01..2026-05-09",
        "context_count": 700,
        "row_count": 7_500,
        "market_day_count": 9,
        "invalid_accept_count_total": 0,
        "top_25_recall": 0.996,
        "learned_mean_guard_calls": 1.4,
        "hand_mean_guard_calls": 2.0,
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "policy_guards_authoritative": True,
        "scorer_authorizes_trade": False,
        "model_output_in_state_root": False,
        "source_manifest": _passing_source_manifest_check(),
        "coverage_profile": _passing_coverage_profile(
            "autotrader",
            source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
        ),
    }


def _passing_source_manifest_check() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_source_manifest_check/v1",
        "ok": True,
        "manifest_id": "prod-shadow-20260501-20260509",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "source_report_count": 1,
        "source_report_match_count": 1,
        "failed_count": 0,
    }


def _passing_coverage_profile(
    profile_type: str,
    *,
    source_descriptor: str,
) -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile_check/v1",
        "ok": True,
        "profile_type": profile_type,
        "source_kind": "production-shadow",
        "source_descriptor": source_descriptor,
        "market_day_count": 9,
        "source_report_count": 1,
        "failed_count": 0,
        "coverage": {
            "pool_count": 4,
            "intent_size_bucket_count": 3,
            "candidate_family_count": 5,
            "hard_negative_family_count": 4,
            "strategy_family_count": 3,
            "guard_family_count": 4,
            "decision_family_count": 3,
        },
    }
