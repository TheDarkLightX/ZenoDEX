from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools import acceptance_tcb_fuzz_campaign as campaign


ROOT_DIR = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = "tools/acceptance_tcb_dangerous_surfaces.json"


def test_parse_summary_extracts_counts_and_duration() -> None:
    stdout = """== acceptance-tcb: structure-aware fuzz (deep stateful) ==\n........\n42 passed, 1 warning in 268.34s (0:04:28)\nok\n"""
    summary = campaign._parse_summary(stdout)
    assert summary == {
        "passed": 42,
        "failed": 0,
        "warnings": 1,
        "pytest_duration_s": 268.34,
        "summary_line": "42 passed, 1 warning in 268.34s (0:04:28)",
    }


def test_default_report_path_uses_campaign_root_and_run_id() -> None:
    path = campaign._default_report_path(
        campaign_root="internal/fuzz_campaigns",
        gate_lane="deep",
        timestamp_utc="20260405T120000Z",
        run_id="acceptance fuzz",
    )
    assert path == "internal/fuzz_campaigns/20260405T120000Z_acceptance-fuzz/acceptance_tcb_fuzz_report.json"



def test_default_report_path_defaults_to_lane_scoped_root() -> None:
    path = campaign._default_report_path(
        campaign_root=None,
        gate_lane="deep",
        timestamp_utc="20260405T120000Z",
        run_id="acceptance fuzz",
    )
    assert path == str(
        ROOT_DIR / "internal/fuzz_campaigns/deep/20260405T120000Z_acceptance-fuzz/acceptance_tcb_fuzz_report.json"
    )



def test_campaign_artifact_paths_use_campaign_directory() -> None:
    artifacts = campaign._campaign_artifact_paths(
        report_out="internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/acceptance_tcb_fuzz_report.json",
        campaign_root="internal/fuzz_campaigns",
        stateful_exploration=True,
        target_manifest=DEFAULT_MANIFEST,
        include_slow_explorers=False,
    )
    assert artifacts == {
        "campaign_dir": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1",
        "minimized_witness_dir": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/minimized_witnesses",
        "minimized_witness_index_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/minimized_witness_index.json",
        "shared_minimized_witness_index_out": "internal/fuzz_campaigns/minimized_witness_index.json",
        "stateful_report_dir": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/stateful_reports",
        "introspection_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/stateful_introspection.json",
        "atlas_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/weird_machine_atlas.json",
        "surface_suggestions_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/stateful_surface_suggestions.json",
        "guard_attribution_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/guard_attribution.json",
        "exploit_proximity_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/stateful_exploit_proximity.json",
        "target_manifest": DEFAULT_MANIFEST,
        "include_slow_explorers": False,
    }



def test_campaign_artifact_paths_omit_stateful_outputs_when_disabled() -> None:
    artifacts = campaign._campaign_artifact_paths(
        report_out="internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/acceptance_tcb_fuzz_report.json",
        campaign_root="internal/fuzz_campaigns",
        stateful_exploration=False,
        target_manifest=DEFAULT_MANIFEST,
        include_slow_explorers=False,
    )
    assert artifacts["stateful_report_dir"] is None
    assert artifacts["introspection_out"] is None
    assert artifacts["atlas_out"] is None
    assert artifacts["surface_suggestions_out"] is None
    assert artifacts["exploit_proximity_out"] is None
    assert artifacts["target_manifest"] is None



def test_refresh_shared_witness_index_collects_campaign_indexes(tmp_path: Path) -> None:
    root = tmp_path / "fuzz_campaigns"
    first = root / "20260405T120000Z_acceptance-tcb-fuzz-r1"
    second = root / "20260405T130500Z_acceptance-tcb-fuzz-r2"
    first.mkdir(parents=True)
    second.mkdir(parents=True)
    (first / "minimized_witness_index.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-index/v1",
                "gate_lane": "fast",
                "campaign_report": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/acceptance_tcb_fuzz_report.json",
                "count": 1,
                "witnesses": [
                    {
                        "id": "nonce_cross_batch_replay",
                        "target": "nonce_replay_sequence",
                        "derivation": "Seq->CrossBatchReplayWithDeadTail",
                        "outcome_label": "reject:step=1:nonce sequence invalid",
                        "path_id": "5f4f22a06552403c",
                        "minimized_size": 1935,
                        "witness_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/minimized_witnesses/nonce_cross_batch_replay.json",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    (second / "minimized_witness_index.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-index/v1",
                "gate_lane": "deep",
                "campaign_report": "internal/fuzz_campaigns/20260405T130500Z_acceptance-tcb-fuzz-r2/acceptance_tcb_fuzz_report.json",
                "count": 1,
                "witnesses": [
                    {
                        "id": "api_request_unauthorized",
                        "target": "dex_request_envelope",
                        "derivation": "DexReq->UnauthorizedWithDeadFields",
                        "outcome_label": "handled:401:unauthorized",
                        "path_id": "8d3661cc0d8d784c",
                        "minimized_size": 18,
                        "witness_out": "internal/fuzz_campaigns/20260405T130500Z_acceptance-tcb-fuzz-r2/minimized_witnesses/api_request_unauthorized.json",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    out = campaign._refresh_shared_witness_index(campaign_root=str(root), fallback_report_out=None)
    assert out is not None
    payload = json.loads((root / "minimized_witness_index.json").read_text(encoding="utf-8"))
    assert payload["schema"] == "zenodex/acceptance-tcb-fuzz-minimized-witness-shared-index/v1"
    assert payload["campaign_count"] == 2
    assert payload["witness_count"] == 2
    assert {w["id"] for w in payload["witnesses"]} == {"nonce_cross_batch_replay", "api_request_unauthorized"}
    assert {w["gate_lane"] for w in payload["witnesses"]} == {"fast", "deep"}



def test_acceptance_tcb_fuzz_campaign_cli_plan_json_shape(tmp_path: Path) -> None:
    report_path = tmp_path / "report.json"
    proc = subprocess.run(
        [
            sys.executable,
            "tools/acceptance_tcb_fuzz_campaign.py",
            "--plan",
            "--format",
            "json",
            "--report-out",
            str(report_path),
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["schema"] == "zenodex/acceptance-tcb-fuzz-campaign-report/v1"
    assert payload["plan_only"] is True
    assert payload["gate_lane"] == "deep"
    assert payload["gate"] == "tools/run_acceptance_tcb_fuzz_gate_deep.sh"
    assert payload["stateful_config"] == {
        "enabled": True,
        "feedback_mode": "stateful",
        "target_manifest": DEFAULT_MANIFEST,
        "target_id": None,
        "include_slow_explorers": False,
    }
    assert payload["result"] is None
    assert payload["artifacts"]["campaign_dir"] == str(report_path.parent)
    assert payload["artifacts"]["minimized_witness_index_out"] == str(report_path.parent / "minimized_witness_index.json")
    assert payload["artifacts"]["stateful_report_dir"] == str(report_path.parent / "stateful_reports")
    assert payload["artifacts"]["introspection_out"] == str(report_path.parent / "stateful_introspection.json")
    assert payload["artifacts"]["atlas_out"] == str(report_path.parent / "weird_machine_atlas.json")
    assert payload["artifacts"]["surface_suggestions_out"] == str(report_path.parent / "stateful_surface_suggestions.json")
    assert payload["artifacts"]["guard_attribution_out"] == str(report_path.parent / "guard_attribution.json")
    assert payload["artifacts"]["exploit_proximity_out"] == str(report_path.parent / "stateful_exploit_proximity.json")
    on_disk = json.loads(report_path.read_text(encoding="utf-8"))
    assert on_disk == payload



def test_acceptance_tcb_fuzz_campaign_cli_plan_json_shape_fast_lane() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            "tools/acceptance_tcb_fuzz_campaign.py",
            "--plan",
            "--format",
            "json",
            "--gate-lane",
            "fast",
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["gate_lane"] == "fast"
    assert payload["gate"] == "tools/run_acceptance_tcb_fuzz_gate.sh"
    assert payload["stateful_config"]["enabled"] is False
    assert payload["artifacts"]["stateful_report_dir"] is None



def test_acceptance_tcb_fuzz_campaign_refresh_shared_index_only(tmp_path: Path) -> None:
    root = tmp_path / "fuzz_campaigns"
    run_dir = root / "20260405T120000Z_acceptance-tcb-fuzz-r1"
    run_dir.mkdir(parents=True)
    (run_dir / "minimized_witness_index.json").write_text(
        json.dumps(
            {
                "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-index/v1",
                "gate_lane": "deep",
                "campaign_report": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/acceptance_tcb_fuzz_report.json",
                "count": 1,
                "witnesses": [
                    {
                        "id": "nonce_cross_batch_replay",
                        "target": "nonce_replay_sequence",
                        "derivation": "Seq->CrossBatchReplayWithDeadTail",
                        "outcome_label": "reject:step=1:nonce sequence invalid",
                        "path_id": "5f4f22a06552403c",
                        "minimized_size": 1935,
                        "witness_out": "internal/fuzz_campaigns/20260405T120000Z_acceptance-tcb-fuzz-r1/minimized_witnesses/nonce_cross_batch_replay.json",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    proc = subprocess.run(
        [
            sys.executable,
            "tools/acceptance_tcb_fuzz_campaign.py",
            "--format",
            "json",
            "--refresh-shared-index-only",
            "--campaign-root",
            str(root),
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["result"]["mode"] == "refresh_shared_index_only"
    assert payload["result"]["ok"] is True
    assert payload["report_out"] is None
    assert payload["gate_lane"] == "deep"
    assert payload["artifacts"]["campaign_dir"] is None
    assert payload["artifacts"]["minimized_witness_index_out"] is None
    assert payload["result"]["shared_minimized_witness_index_out"] == str(root / "minimized_witness_index.json")
    shared = json.loads((root / "minimized_witness_index.json").read_text(encoding="utf-8"))
    assert shared["campaign_count"] == 1
    assert shared["witness_count"] == 1



def test_witness_specs_are_lane_scoped() -> None:
    fast_ids = {spec["id"] for spec in campaign._witness_specs_for_lane("fast")}
    deep_ids = {spec["id"] for spec in campaign._witness_specs_for_lane("deep")}
    assert "dex_engine_quote_receipt_stale_dead_tail" not in fast_ids
    assert "dex_engine_settlement_stale_dead_tail" not in fast_ids
    assert "route_certificate_candidate_set_hash_mismatch" not in fast_ids
    assert "route_canonicalization_candidate_set_hash_mismatch" not in fast_ids
    assert "settlement_attestation_stale" not in fast_ids
    assert "settlement_attestation_allowlist_drift" not in fast_ids
    assert "settlement_attestation_packet_hash_mismatch" not in fast_ids
    assert "settlement_attestation_signature_invalid" not in fast_ids
    assert "settlement_attestation_future_epoch" not in fast_ids
    assert "dex_engine_quote_receipt_stale_dead_tail" in deep_ids
    assert "dex_engine_settlement_stale_dead_tail" in deep_ids
    assert "route_certificate_candidate_set_hash_mismatch" in deep_ids
    assert "route_canonicalization_candidate_set_hash_mismatch" in deep_ids
    assert "settlement_attestation_stale" in deep_ids
    assert "settlement_attestation_allowlist_drift" in deep_ids
    assert "settlement_attestation_packet_hash_mismatch" in deep_ids
    assert "settlement_attestation_signature_invalid" in deep_ids
    assert "settlement_attestation_future_epoch" in deep_ids
