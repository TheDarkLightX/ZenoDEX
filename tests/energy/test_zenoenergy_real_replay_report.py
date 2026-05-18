from __future__ import annotations

import json
from pathlib import Path

from tools.build_zenoenergy_real_replay_report import (
    build_autotrader_real_shadow_report,
    build_upba_real_replay_report,
    main,
)
from tools.check_zenoenergy_replay_source_manifest import (
    canonical_sha256,
    validate_replay_source_manifest,
)
from tools.check_zenoenergy_production_promotion import build_production_gate_report


ROOT = Path(__file__).resolve().parents[2]


def test_builds_upba_real_replay_report_from_benchmark_modes() -> None:
    report = build_upba_real_replay_report(
        benchmark_report=_upba_benchmark_report(),
        source_kind="production-shadow",
        source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
    )

    assert report["schema"] == "zenodex/energy/upba_real_replay_report/v1"
    assert report["batch_count"] == 1_250
    assert report["candidate_count"] == 25_000
    assert report["top_25_recall"] == 0.995
    assert report["top_25_objective_recall"] == 0.998
    assert report["learned_mean_verifier_calls"] == 1.7
    assert report["hand_mean_verifier_calls"] == 2.4
    assert report["deterministic_replay_ok"] is True
    assert report["no_live_secrets"] is True


def test_builds_upba_real_replay_report_from_evaluation_reports() -> None:
    learned = _upba_evaluation_report(mode="learned", mean_calls=1.6)
    hand = _upba_evaluation_report(mode="hand", mean_calls=2.2)

    report = build_upba_real_replay_report(
        learned_report=learned,
        hand_report=hand,
        source_kind="historical-replay",
        source_descriptor="historical-replay:2026-04-20..2026-04-27",
        market_day_count=7,
        deterministic_replay_ok=True,
        no_live_secrets=True,
    )

    assert report["batch_count"] == 1_000
    assert report["candidate_count"] == 20_000
    assert report["top_25_recall"] == 0.992
    assert report["learned_mean_verifier_calls"] == 1.6
    assert report["hand_mean_verifier_calls"] == 2.2


def test_builds_autotrader_real_shadow_report_from_bridge() -> None:
    report = build_autotrader_real_shadow_report(
        shadow_bridge_report=_autotrader_bridge_report(),
        source_kind="production-shadow",
        source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
        market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
    )

    assert report["schema"] == "zenodex/energy/autotrader_real_shadow_report/v1"
    assert report["context_count"] == 700
    assert report["row_count"] == 7_500
    assert report["top_25_recall"] == 0.996
    assert report["top_25_objective_recall"] == 0.998
    assert report["learned_mean_guard_calls"] == 1.4
    assert report["hand_mean_guard_calls"] == 2.0
    assert report["policy_guards_authoritative"] is True
    assert report["scorer_authorizes_trade"] is False
    assert report["model_output_in_state_root"] is False


def test_builder_rejects_fixture_source_descriptor() -> None:
    try:
        build_upba_real_replay_report(
            benchmark_report=_upba_benchmark_report(),
            source_kind="production-shadow",
            source_descriptor="synthetic fixture replay",
            market_day_count=9,
            deterministic_replay_ok=True,
            no_live_secrets=True,
        )
    except ValueError as exc:
        assert "source_descriptor" in str(exc)
    else:
        raise AssertionError("fixture source descriptor should be rejected")


def test_builder_rejects_autotrader_builtin_fixture_source() -> None:
    bridge = _autotrader_bridge_report()
    bridge["source"] = "built-in-zenograph-baseline"

    try:
        build_autotrader_real_shadow_report(
            shadow_bridge_report=bridge,
            source_kind="production-shadow",
            source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
            market_day_count=9,
            deterministic_replay_ok=True,
            no_live_secrets=True,
        )
    except ValueError as exc:
        assert "not production-grade" in str(exc)
    else:
        raise AssertionError("built-in fixture source should be rejected")


def test_builder_rejects_missing_secret_scrub_attestation() -> None:
    try:
        build_upba_real_replay_report(
            benchmark_report=_upba_benchmark_report(),
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            market_day_count=9,
            deterministic_replay_ok=True,
            no_live_secrets=False,
        )
    except ValueError as exc:
        assert "--no-live-secrets" in str(exc)
    else:
        raise AssertionError("missing no-live-secrets attestation should be rejected")


def test_builder_reports_can_satisfy_production_gate() -> None:
    research_replay = json.loads(
        (
            ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json"
        ).read_text(encoding="utf-8")
    )
    upba = build_upba_real_replay_report(
        benchmark_report=_upba_benchmark_report(),
        source_kind="production-shadow",
        source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
        source_reports=_upba_source_reports(),
        source_manifest_check=_upba_manifest_check(),
        coverage_profile=_upba_coverage_profile(),
    )
    autotrader = build_autotrader_real_shadow_report(
        shadow_bridge_report=_autotrader_bridge_report(),
        source_kind="production-shadow",
        source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
        market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
        source_reports=_autotrader_source_reports(),
        source_manifest_check=_autotrader_manifest_check(),
        coverage_profile=_autotrader_coverage_profile(),
    )

    gate = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=upba,
        autotrader_real_shadow=autotrader,
        operator_release_enabled=True,
    )

    assert gate["decision"] == "allow_ranking_only"
    assert gate["promotion_allowed"] is True


def test_builder_rejects_narrow_coverage_profile() -> None:
    profile = _upba_coverage_profile()
    profile["candidate_family_count"] = 1

    try:
        build_upba_real_replay_report(
            benchmark_report=_upba_benchmark_report(),
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            market_day_count=9,
            deterministic_replay_ok=True,
            no_live_secrets=True,
            source_reports=_upba_source_reports(),
            source_manifest_check=_upba_manifest_check(),
            coverage_profile=profile,
        )
    except ValueError as exc:
        assert "coverage profile check failed" in str(exc)
        assert "upba_candidate_family_count" in str(exc)
    else:
        raise AssertionError("narrow coverage profile should be rejected")


def test_cli_writes_upba_real_replay_report(tmp_path: Path) -> None:
    benchmark = tmp_path / "upba_benchmark.json"
    manifest = tmp_path / "manifest.json"
    coverage = tmp_path / "coverage.json"
    output = tmp_path / "upba_real.json"
    benchmark_payload = _upba_benchmark_report()
    benchmark.write_text(json.dumps(benchmark_payload), encoding="utf-8")
    manifest.write_text(
        json.dumps(
            _source_manifest(
                source_kind="production-shadow",
                source_descriptor="prod-shadow:2026-05-01..2026-05-09",
                source_reports=[
                    {
                        "name": "upba-benchmark",
                        "schema": benchmark_payload["schema"],
                        "sha256": canonical_sha256(benchmark_payload),
                    }
                ],
            )
        ),
        encoding="utf-8",
    )
    coverage.write_text(json.dumps(_upba_coverage_profile()), encoding="utf-8")

    rc = main(
        [
            "upba",
            "--benchmark-report",
            str(benchmark),
            "--source-kind",
            "production-shadow",
            "--source-descriptor",
            "prod-shadow:2026-05-01..2026-05-09",
            "--market-day-count",
            "9",
            "--deterministic-replay-ok",
            "--no-live-secrets",
            "--source-manifest",
            str(manifest),
            "--coverage-profile",
            str(coverage),
            "--output-json",
            str(output),
        ]
    )

    payload = json.loads(output.read_text(encoding="utf-8"))
    assert rc == 0
    assert payload["schema"] == "zenodex/energy/upba_real_replay_report/v1"
    assert payload["source_manifest"]["ok"] is True
    assert payload["coverage_profile"]["ok"] is True
    assert payload["source_reports"][0]["schema"] == "zenodex/energy/upba_v2_benchmark_report/v1"


def _upba_benchmark_report() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
        "batches": 1_250,
        "modes": {
            "hand": {
                "batches": 1_250,
                "candidate_count": 20,
                "invalid_accept_count": 0,
                "mean_verifier_calls": 2.4,
                "permutation_violation_count": 0,
                "top_25_recall": 0.99,
                "top_25_objective_recall": 0.99,
            },
            "hybrid": {
                "batches": 1_250,
                "candidate_count": 20,
                "invalid_accept_count": 0,
                "mean_verifier_calls": 1.7,
                "permutation_violation_count": 0,
                "top_25_recall": 0.995,
                "top_25_objective_recall": 0.998,
            },
        },
        "invalid_accept_count": 0,
    }


def _upba_evaluation_report(*, mode: str, mean_calls: float) -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_v2_evaluation_report/v1",
        "mode": mode,
        "batches": 1_000,
        "candidate_count_mean": 20,
        "invalid_accept_count": 0,
        "mean_verifier_calls": mean_calls,
        "top_25_recall": 0.992,
        "top_25_objective_recall": 0.997,
    }


def _autotrader_bridge_report() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/autotrader_shadow_bridge_report/v1",
        "source": "shadow_logs/autotrader/2026-05-01_2026-05-09.jsonl",
        "shadow": {
            "context_count": 700,
            "row_count": 7_500,
        },
        "modes": {
            "hand": {
                "mode": "hand",
                "mean_guard_calls": 2.0,
                "top_25_recall": 0.995,
                "top_25_objective_recall": 0.996,
                "invalid_accept_count": 0,
            },
            "hybrid": {
                "mode": "hybrid",
                "mean_guard_calls": 1.4,
                "top_25_recall": 0.996,
                "top_25_objective_recall": 0.998,
                "invalid_accept_count": 0,
            },
        },
        "safety": {
            "invalid_accept_count_total": 0,
            "policy_guards_authoritative": True,
            "scorer_authorizes_trade": False,
            "model_output_in_state_root": False,
        },
    }


def _upba_manifest_check() -> dict[str, object]:
    payload = _upba_benchmark_report()
    return validate_replay_source_manifest(
        manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            source_reports=[
                {
                    "name": "upba-benchmark",
                    "schema": payload["schema"],
                    "sha256": canonical_sha256(payload),
                }
            ],
        ),
        source_reports=[
            {
                "schema": payload["schema"],
                "sha256": canonical_sha256(payload),
            }
        ],
    )


def _autotrader_manifest_check() -> dict[str, object]:
    payload = _autotrader_bridge_report()
    return validate_replay_source_manifest(
        manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
            source_reports=[
                {
                    "name": "autotrader-shadow-bridge",
                    "schema": payload["schema"],
                    "sha256": canonical_sha256(payload),
                }
            ],
        ),
        source_reports=[
            {
                "schema": payload["schema"],
                "sha256": canonical_sha256(payload),
            }
        ],
    )


def _upba_source_reports() -> list[dict[str, object]]:
    payload = _upba_benchmark_report()
    return [
        {
            "schema": payload["schema"],
            "sha256": canonical_sha256(payload),
        }
    ]


def _autotrader_source_reports() -> list[dict[str, object]]:
    payload = _autotrader_bridge_report()
    return [
        {
            "schema": payload["schema"],
            "sha256": canonical_sha256(payload),
        }
    ]


def _upba_coverage_profile() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile/v1",
        "profile_type": "upba",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "source_report_count": 1,
        "batch_count": 1_250,
        "pool_count": 4,
        "intent_size_bucket_count": 3,
        "candidate_family_count": 5,
        "hard_negative_family_count": 4,
        "min_batches_per_market_day": 75,
    }


def _autotrader_coverage_profile() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile/v1",
        "profile_type": "autotrader",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:autotrader:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "source_report_count": 1,
        "context_count": 700,
        "strategy_family_count": 3,
        "guard_family_count": 4,
        "decision_family_count": 3,
        "min_contexts_per_market_day": 50,
    }


def _source_manifest(
    *,
    source_kind: str,
    source_descriptor: str,
    source_reports: list[dict[str, object]],
) -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_source_manifest/v1",
        "manifest_id": f"{source_kind}:20260501-20260509",
        "source_kind": source_kind,
        "source_descriptor": source_descriptor,
        "market_day_count": 9,
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "secret_scan": {
            "tool": "local-secret-scan-v1",
            "ok": True,
            "finding_count": 0,
        },
        "artifacts": source_reports,
    }
