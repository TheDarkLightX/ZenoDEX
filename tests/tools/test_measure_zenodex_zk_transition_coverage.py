from __future__ import annotations

import json
from pathlib import Path

from tools.measure_zenodex_zk_transition_coverage import build_zk_transition_coverage_report, main

ROOT = Path(__file__).resolve().parents[2]


def test_zk_transition_coverage_reports_current_scope() -> None:
    report = build_zk_transition_coverage_report()

    assert report["ok"] is True
    assert report["proof_operation_coverage"]["covered_count"] == 7
    assert report["proof_operation_coverage"]["total_count"] == 11
    assert report["proof_operation_coverage"]["coverage_pct"] == 63.64
    assert report["value_moving_surface_coverage"]["covered_count"] == 0
    assert report["value_moving_surface_coverage"]["total_count"] == 8
    assert report["value_moving_surface_coverage"]["coverage_pct"] == 0.0
    assert report["succinct_everything_status"] == "open"
    assert "swap_exact_out" in report["proof_operation_coverage"]["not_covered_operations"]
    assert "spot_complete_block_real_proof" in report["value_moving_surface_coverage"]["open_gap_surface_ids"]
    assert "uniform_batch_upba_execution" in report["value_moving_surface_coverage"]["open_surface_ids"]


def test_zk_transition_coverage_consumes_timed_smoke_report(tmp_path: Path) -> None:
    smoke_path = tmp_path / "real_proof_smoke_report.json"
    smoke_path.write_text(
        json.dumps(
            {
                "schema": "zenodex.risc0_real_proof_smoke.v0",
                "ok": True,
                "case_count": 2,
                "cases": [
                    {
                        "case": "empty",
                        "generate_seconds": 1.25,
                        "verify_seconds": 0.2,
                        "total_seconds": 1.45,
                        "proof_base64_len": 10,
                    },
                    {
                        "case": "swap_exact_in",
                        "generate_seconds": 2.75,
                        "verify_seconds": 0.3,
                        "total_seconds": 3.05,
                        "proof_base64_len": 20,
                    },
                ],
            }
        ),
        encoding="utf-8",
    )

    report = build_zk_transition_coverage_report(smoke_report_path=smoke_path)

    assert report["ok"] is True
    assert report["timing"]["summary"]["generate_seconds_median"] == 2.0
    assert report["timing"]["summary"]["total_seconds_max"] == 3.05


def test_zk_transition_coverage_rejects_untimed_smoke_report(tmp_path: Path) -> None:
    smoke_path = tmp_path / "real_proof_smoke_report.json"
    smoke_path.write_text(
        json.dumps(
            {
                "schema": "zenodex.risc0_real_proof_smoke.v0",
                "ok": True,
                "case_count": 1,
                "cases": [{"case": "empty", "proof_base64_len": 10}],
            }
        ),
        encoding="utf-8",
    )

    report = build_zk_transition_coverage_report(smoke_report_path=smoke_path)

    assert report["ok"] is False
    assert report["timing"]["missing_timing_cases"] == ["empty"]


def test_zk_transition_coverage_cli_outputs_report(capsys) -> None:
    code = main([])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["schema"] == "zenodex.zk_transition_coverage_report.v0"


def test_zk_performance_snapshot_redacts_private_hardware_details() -> None:
    snapshot = json.loads((ROOT / "docs/ZENODEX_ZK_PERFORMANCE_SNAPSHOT_2026_05_31.json").read_text(encoding="utf-8"))
    host = snapshot["host"]

    assert host["hardware_details_public"] is False
    assert "cpu" not in host
    assert "gpu" not in host
    public_text = "\n".join(
        [
            (ROOT / "docs/ZENODEX_ZK_PERFORMANCE_SNAPSHOT_2026_05_31.md").read_text(encoding="utf-8"),
            (ROOT / "docs/ZENODEX_HOST_INDEPENDENT_COVERAGE.md").read_text(encoding="utf-8"),
            (ROOT / "docs/claims_registry.yaml").read_text(encoding="utf-8"),
        ]
    )
    forbidden_summary_fields = ("CPU:", "GPU visible:", "Cargo:", "Rustc:")
    assert not any(token in public_text for token in forbidden_summary_fields)
