from __future__ import annotations

import json
from pathlib import Path

from tools.build_zenoenergy_production_evidence_bundle import (
    build_production_evidence_bundle,
    main,
)
from tools.check_zenoenergy_replay_source_manifest import canonical_sha256


ROOT = Path(__file__).resolve().parents[2]


def test_bundle_allows_ranking_only_when_real_evidence_passes_gate() -> None:
    upba = _upba_benchmark_report()
    autotrader = _autotrader_bridge_report()
    bundle = build_production_evidence_bundle(
        research_replay=_research_replay(),
        upba_benchmark_report=upba,
        upba_source_manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            source_reports=[_artifact("upba-benchmark", upba)],
        ),
        upba_source_reports=[_source_report(upba)],
        upba_source_kind="production-shadow",
        upba_source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        upba_market_day_count=9,
        autotrader_shadow_bridge_report=autotrader,
        autotrader_source_manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
            source_reports=[_artifact("autotrader-shadow-bridge", autotrader)],
        ),
        autotrader_source_reports=[_source_report(autotrader)],
        autotrader_source_kind="production-shadow",
        autotrader_source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
        autotrader_market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
        operator_release_enabled=True,
    )

    assert bundle["schema"] == "zenodex/energy/production_evidence_bundle/v1"
    assert bundle["decision"] == "allow_ranking_only"
    assert bundle["promotion_allowed"] is True
    assert bundle["source_manifest_checks"]["upba"]["ok"] is True
    assert bundle["source_manifest_checks"]["autotrader"]["ok"] is True
    assert bundle["reports"]["production_gate"]["promotion_allowed"] is True
    assert bundle["safety_contract"]["scorer_authorizes_settlement_or_trade"] is False


def test_bundle_blocks_without_operator_enable() -> None:
    upba = _upba_benchmark_report()
    autotrader = _autotrader_bridge_report()
    bundle = build_production_evidence_bundle(
        research_replay=_research_replay(),
        upba_benchmark_report=upba,
        upba_source_manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            source_reports=[_artifact("upba-benchmark", upba)],
        ),
        upba_source_reports=[_source_report(upba)],
        upba_source_kind="production-shadow",
        upba_source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        upba_market_day_count=9,
        autotrader_shadow_bridge_report=autotrader,
        autotrader_source_manifest=_source_manifest(
            source_kind="production-shadow",
            source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
            source_reports=[_artifact("autotrader-shadow-bridge", autotrader)],
        ),
        autotrader_source_reports=[_source_report(autotrader)],
        autotrader_source_kind="production-shadow",
        autotrader_source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
        autotrader_market_day_count=9,
        deterministic_replay_ok=True,
        no_live_secrets=True,
        operator_release_enabled=False,
    )

    assert bundle["decision"] == "blocked"
    assert bundle["promotion_allowed"] is False
    assert "operator must explicitly enable advisory ranking-only promotion" in bundle[
        "blocked_reasons"
    ]


def test_bundle_rejects_source_manifest_hash_mismatch() -> None:
    upba = _upba_benchmark_report()
    autotrader = _autotrader_bridge_report()
    bad_upba_manifest = _source_manifest(
        source_kind="production-shadow",
        source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        source_reports=[
            {
                "name": "upba-benchmark",
                "schema": upba["schema"],
                "sha256": "0" * 64,
            }
        ],
    )

    try:
        build_production_evidence_bundle(
            research_replay=_research_replay(),
            upba_benchmark_report=upba,
            upba_source_manifest=bad_upba_manifest,
            upba_source_reports=[_source_report(upba)],
            upba_source_kind="production-shadow",
            upba_source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            upba_market_day_count=9,
            autotrader_shadow_bridge_report=autotrader,
            autotrader_source_manifest=_source_manifest(
                source_kind="production-shadow",
                source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
                source_reports=[_artifact("autotrader-shadow-bridge", autotrader)],
            ),
            autotrader_source_reports=[_source_report(autotrader)],
            autotrader_source_kind="production-shadow",
            autotrader_source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
            autotrader_market_day_count=9,
            deterministic_replay_ok=True,
            no_live_secrets=True,
            operator_release_enabled=True,
        )
    except ValueError as exc:
        assert "UPBA source manifest check failed" in str(exc)
        assert "source_reports_match" in str(exc)
    else:
        raise AssertionError("bundle should reject mismatched UPBA source manifest")


def test_cli_writes_bundle_json_and_markdown(tmp_path: Path) -> None:
    upba = _upba_benchmark_report()
    autotrader = _autotrader_bridge_report()
    upba_path = tmp_path / "upba_benchmark.json"
    autotrader_path = tmp_path / "autotrader_shadow_bridge.json"
    upba_manifest_path = tmp_path / "upba_manifest.json"
    autotrader_manifest_path = tmp_path / "autotrader_manifest.json"
    output_json = tmp_path / "bundle.json"
    output_markdown = tmp_path / "bundle.md"
    upba_path.write_text(json.dumps(upba), encoding="utf-8")
    autotrader_path.write_text(json.dumps(autotrader), encoding="utf-8")
    upba_manifest_path.write_text(
        json.dumps(
            _source_manifest(
                source_kind="production-shadow",
                source_descriptor="prod-shadow:2026-05-01..2026-05-09",
                source_reports=[_artifact("upba-benchmark", upba)],
            )
        ),
        encoding="utf-8",
    )
    autotrader_manifest_path.write_text(
        json.dumps(
            _source_manifest(
                source_kind="production-shadow",
                source_descriptor="prod-shadow:autotrader:2026-05-01..2026-05-09",
                source_reports=[_artifact("autotrader-shadow-bridge", autotrader)],
            )
        ),
        encoding="utf-8",
    )

    rc = main(
        [
            "--upba-benchmark-report",
            str(upba_path),
            "--upba-source-manifest",
            str(upba_manifest_path),
            "--upba-source-kind",
            "production-shadow",
            "--upba-source-descriptor",
            "prod-shadow:2026-05-01..2026-05-09",
            "--upba-market-day-count",
            "9",
            "--autotrader-shadow-bridge-report",
            str(autotrader_path),
            "--autotrader-source-manifest",
            str(autotrader_manifest_path),
            "--autotrader-source-kind",
            "production-shadow",
            "--autotrader-source-descriptor",
            "prod-shadow:autotrader:2026-05-01..2026-05-09",
            "--autotrader-market-day-count",
            "9",
            "--deterministic-replay-ok",
            "--no-live-secrets",
            "--operator-release-enable",
            "--output-json",
            str(output_json),
            "--output-markdown",
            str(output_markdown),
        ]
    )

    payload = json.loads(output_json.read_text(encoding="utf-8"))
    assert rc == 0
    assert payload["schema"] == "zenodex/energy/production_evidence_bundle/v1"
    assert payload["decision"] == "allow_ranking_only"
    assert "ProductionEvidenceBundle" in output_markdown.read_text(encoding="utf-8")


def _research_replay() -> dict[str, object]:
    return json.loads(
        (
            ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json"
        ).read_text(encoding="utf-8")
    )


def _source_report(payload: dict[str, object]) -> dict[str, object]:
    return {
        "schema": payload["schema"],
        "sha256": canonical_sha256(payload),
    }


def _artifact(name: str, payload: dict[str, object]) -> dict[str, object]:
    return {
        "name": name,
        "schema": payload["schema"],
        "sha256": canonical_sha256(payload),
    }


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
