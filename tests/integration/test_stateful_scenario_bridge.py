from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.stateful_scenario_bridge import (
    DISASTER_REACHABILITY_RATCHET_SCHEMA,
    CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA,
    MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA,
    PROOF_OBLIGATION_PACKET_SCHEMA,
    PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA,
    SCENARIO_CANDIDATE_CHECK_SCHEMA,
    SCENARIO_CANDIDATE_SCHEMA,
    SCENARIO_RUN_RECEIPT_SCHEMA,
    SHAPEFORGE_BRIDGE_SCHEMA,
    build_cross_surface_witness_exploration_plan,
    build_disaster_reachability_ratchet_report,
    build_minimal_witness_language_audit,
    build_shapeforge_promotion_bridge_report,
    build_stateful_disaster_proof_obligation_packet,
    check_scenario_candidate,
    run_stateful_disaster_proof_obligations,
    run_scenario_candidate,
)


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def _valid_candidate() -> dict:
    return {
        "schema": SCENARIO_CANDIDATE_SCHEMA,
        "scenario_id": "what_if_nonce_cross_batch_replay",
        "surface_id": "nonce_replay_guard",
        "disaster_state": "duplicate_side_effect_after_nonce_replay",
        "action_grammar": "intent batch -> accept -> replay or gap -> reject",
        "bounds": {"max_depth": 2, "max_frontier": 32},
        "oracle": {
            "expected_outcome_tokens": ["nonce sequence invalid"],
            "forbidden_outcome_tokens": ["ok:mutated"],
        },
        "expected_guard": "nonce_replay_guard",
        "harness_hint": "state_boundary_concolic:validate_and_apply_intent_nonce_batch",
        "promotion_target": {
            "kind": "shapeforge_scenario",
            "id": "stateful_nonce_replay_guard",
            "evidence_class": "tested_discovery",
        },
        "evidence_class_ceiling": "tested_discovery",
        "campaign": {"gate_lane": "deep", "feedback_mode": "stateful"},
    }


def test_check_scenario_candidate_accepts_manifest_bound_candidate() -> None:
    payload = check_scenario_candidate(_valid_candidate(), target_manifest=MANIFEST_PATH)

    assert payload["schema"] == SCENARIO_CANDIDATE_CHECK_SCHEMA
    assert payload["ok"] is True
    assert payload["surface_id"] == "nonce_replay_guard"
    assert payload["matched_surface"]["machine_family"] == "replay/nonce"
    assert payload["promotion_policy"]["max_evidence_class"] == "tested_discovery"
    assert payload["replay_plan"]["command"][:4] == [
        "python3",
        "tools/acceptance_tcb_fuzz_campaign.py",
        "--gate-lane",
        "deep",
    ]
    assert "--target-id" in payload["replay_plan"]["command"]


def test_check_scenario_candidate_rejects_unbound_or_overclaimed_candidate() -> None:
    candidate = _valid_candidate()
    candidate["oracle"] = {"expected_outcome_tokens": ["made_up_success_token"]}
    candidate["evidence_class_ceiling"] = "proved"
    candidate["promotion_target"] = {
        "kind": "shapeforge_scenario",
        "id": "bad",
        "evidence_class": "contract",
    }

    payload = check_scenario_candidate(candidate, target_manifest=MANIFEST_PATH)

    assert payload["ok"] is False
    assert any("evidence_class_ceiling cannot exceed tested_discovery" in error for error in payload["errors"])
    assert any("promotion_target.evidence_class cannot exceed tested_discovery" in error for error in payload["errors"])
    assert any("oracle.expected_outcome_tokens" in error for error in payload["errors"])


def test_check_stateful_scenario_candidate_cli_emits_json(tmp_path: Path) -> None:
    candidate_path = tmp_path / "candidate.json"
    candidate_path.write_text(json.dumps(_valid_candidate()), encoding="utf-8")

    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/check_stateful_scenario_candidate.py",
            str(candidate_path),
            "--target-manifest",
            str(MANIFEST_PATH),
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        text=True,
    )
    payload = json.loads(raw)
    assert payload["ok"] is True
    assert payload["schema"] == SCENARIO_CANDIDATE_CHECK_SCHEMA


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_bridge_fixture(root: Path) -> Path:
    introspection = root / "stateful_introspection.json"
    atlas = root / "weird_machine_atlas.json"
    suggestions = root / "stateful_surface_suggestions.json"
    guard = root / "guard_attribution.json"
    exploit = root / "stateful_exploit_proximity.json"
    report = root / "acceptance_tcb_fuzz_report.json"

    _write_json(
        introspection,
        {
            "schema": "zenodex/acceptance-tcb-fuzz-introspection/v1",
            "surfaces": [
                {
                    "surface_id": "nonce_replay_guard",
                    "machine_family": "replay/nonce",
                    "invariant_boundary": "nonce sequences must reject replay",
                    "status": "witnessed",
                    "harnesses": ["state_boundary_concolic:validate_and_apply_intent_nonce_batch"],
                    "reached_by": ["witness:nonce_cross_batch_replay"],
                    "witness_ids": ["nonce_cross_batch_replay"],
                    "waypoint_tags": ["nonce", "replay"],
                },
                {
                    "surface_id": "api_request_authorization_boundary",
                    "machine_family": "api/auth-envelope",
                    "invariant_boundary": "unauthorized request envelopes must fail closed",
                    "status": "harnessed_unreached",
                    "harnesses": ["api_server_boundary_concolic:settlement_proof_flags"],
                    "reached_by": [],
                    "witness_ids": [],
                    "waypoint_tags": ["api", "auth"],
                },
            ],
        },
    )
    _write_json(
        atlas,
        {
            "schema": "zenodex/acceptance-tcb-weird-machine-atlas/v1",
            "entries": [
                {
                    "surface_id": "nonce_replay_guard",
                    "witness_status": "witnessed",
                    "sample_witnesses": ["nonce_cross_batch_replay"],
                }
            ],
        },
    )
    _write_json(
        suggestions,
        {
            "schema": "zenodex/acceptance-tcb-surface-suggestions/v1",
            "suggestions": [],
            "suggestion_count": 0,
        },
    )
    _write_json(
        guard,
        {
            "schema": "zenodex/acceptance-tcb-guard-attribution/v1",
            "witnesses": [
                {
                    "witness_id": "nonce_cross_batch_replay",
                    "surface_ids": ["nonce_replay_guard"],
                    "guard_family": "nonce_replay_guard",
                    "guard_reason": "nonce sequence invalid",
                }
            ],
        },
    )
    _write_json(
        exploit,
        {
            "schema": "zenodex/acceptance-tcb-exploit-proximity/v1",
            "top_witnesses": [
                {
                    "witness_id": "nonce_cross_batch_replay",
                    "surface_ids": ["nonce_replay_guard"],
                    "severity_band": "medium",
                }
            ],
        },
    )
    _write_json(
        report,
        {
            "schema": "zenodex/acceptance-tcb-fuzz-campaign-report/v1",
            "plan_only": False,
            "artifacts": {
                "target_manifest": str(MANIFEST_PATH),
                "introspection_out": str(introspection),
                "atlas_out": str(atlas),
                "surface_suggestions_out": str(suggestions),
                "guard_attribution_out": str(guard),
                "exploit_proximity_out": str(exploit),
            },
        },
    )
    return report


def test_build_shapeforge_promotion_bridge_caps_fuzz_evidence(tmp_path: Path) -> None:
    report = _write_bridge_fixture(tmp_path)

    payload = build_shapeforge_promotion_bridge_report(campaign_report=report)

    assert payload["schema"] == SHAPEFORGE_BRIDGE_SCHEMA
    assert payload["ok"] is True
    assert payload["evidence_class_ceiling"] == "tested_discovery"
    assert payload["promotion_policy"]["safe_states_researchable_only"] is True
    assert payload["shape_validation"]["ran"] is False
    assert payload["candidate_count"] == 1
    assert payload["blocked_count"] == 1
    delta = payload["candidate_deltas"][0]
    assert delta["surface_id"] == "nonce_replay_guard"
    assert delta["axis"] == "guard"
    assert delta["evidence_class"] == "tested_discovery"
    assert delta["status_if_unproved"] == "blocked_for_settlement_authority"
    assert "nonce_replay_guard" in delta["evidence_sources"]["guard_families"]
    assert delta["evidence_sources"]["exploit_proximity"]["max_severity_band"] == "medium"


def test_build_stateful_shapeforge_promotion_bridge_cli_writes_report(tmp_path: Path) -> None:
    campaign_report = _write_bridge_fixture(tmp_path / "campaign")
    out = tmp_path / "bridge.json"

    proc = subprocess.run(
        [
            sys.executable,
            "tools/build_stateful_shapeforge_promotion_bridge.py",
            "--campaign-report",
            str(campaign_report),
            "--output",
            str(out),
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    stdout_payload = json.loads(proc.stdout)
    file_payload = json.loads(out.read_text(encoding="utf-8"))
    assert stdout_payload["schema"] == SHAPEFORGE_BRIDGE_SCHEMA
    assert file_payload == stdout_payload
    assert file_payload["candidate_count"] == 1


def test_disaster_reachability_ratchet_fails_on_uncovered_surfaces(tmp_path: Path) -> None:
    campaign_report = _write_bridge_fixture(tmp_path)
    bridge = build_shapeforge_promotion_bridge_report(campaign_report=campaign_report)

    payload = build_disaster_reachability_ratchet_report(bridge_report=bridge)

    assert payload["schema"] == DISASTER_REACHABILITY_RATCHET_SCHEMA
    assert payload["ok"] is False
    assert payload["blocked_count"] == 1
    assert any("blocked surface count 1 exceeds budget 0" in error for error in payload["errors"])
    assert payload["negative_knowledge_candidates"][0]["reachability_status"] == "blocked_by_guard_witness"


def test_disaster_reachability_ratchet_passes_with_explicit_blocked_budget(tmp_path: Path) -> None:
    campaign_report = _write_bridge_fixture(tmp_path)
    bridge = build_shapeforge_promotion_bridge_report(campaign_report=campaign_report)

    payload = build_disaster_reachability_ratchet_report(
        bridge_report=bridge,
        max_blocked_surfaces=1,
        require_witnesses=True,
        require_guard_attribution=True,
    )

    assert payload["ok"] is True
    assert payload["risk_counts"]["medium"] == 1
    record = payload["negative_knowledge_candidates"][0]
    assert record["current_evidence_class"] == "tested_discovery"
    assert record["target_evidence_class"] == "contract_or_proved"
    assert record["witness_ids"] == ["nonce_cross_batch_replay"]


def test_check_stateful_disaster_reachability_ratchet_cli_reports_json(tmp_path: Path) -> None:
    campaign_report = _write_bridge_fixture(tmp_path / "campaign")
    bridge = build_shapeforge_promotion_bridge_report(campaign_report=campaign_report)
    bridge_path = tmp_path / "bridge.json"
    bridge_path.write_text(json.dumps(bridge, indent=2, sort_keys=True), encoding="utf-8")

    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/check_stateful_disaster_reachability_ratchet.py",
            "--bridge-report",
            str(bridge_path),
            "--max-blocked-surfaces",
            "1",
            "--require-guard-attribution",
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        text=True,
    )
    payload = json.loads(raw)
    assert payload["schema"] == DISASTER_REACHABILITY_RATCHET_SCHEMA
    assert payload["ok"] is True


def test_run_scenario_candidate_plan_does_not_execute_campaign() -> None:
    payload = run_scenario_candidate(candidate=_valid_candidate(), target_manifest=MANIFEST_PATH)

    assert payload["schema"] == SCENARIO_RUN_RECEIPT_SCHEMA
    assert payload["ok"] is True
    assert payload["plan_only"] is True
    assert payload["campaign_result"] is None
    assert payload["bridge_report"] is None
    assert "--target-id" in payload["command"]


def test_run_stateful_scenario_candidate_cli_plan_writes_receipt(tmp_path: Path) -> None:
    candidate_path = tmp_path / "candidate.json"
    out = tmp_path / "receipt.json"
    candidate_path.write_text(json.dumps(_valid_candidate()), encoding="utf-8")

    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/run_stateful_scenario_candidate.py",
            str(candidate_path),
            "--target-manifest",
            str(MANIFEST_PATH),
            "--output",
            str(out),
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        text=True,
    )
    stdout_payload = json.loads(raw)
    file_payload = json.loads(out.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    assert file_payload["schema"] == SCENARIO_RUN_RECEIPT_SCHEMA
    assert file_payload["plan_only"] is True


def _critical_ratchet_payload() -> dict:
    return {
        "schema": DISASTER_REACHABILITY_RATCHET_SCHEMA,
        "ok": True,
        "source_bridge_report": "internal/fuzz_campaigns/deep/sample/acceptance_tcb_fuzz_report.json",
        "negative_knowledge_candidates": [
            {
                "surface_id": "stale_settlement_boundary",
                "machine_family": "settlement/staleness",
                "current_evidence_class": "tested_discovery",
                "guard_families": ["settlement_freshness_guard"],
                "witness_ids": ["dex_engine_settlement_stale_dead_tail"],
                "severity_band": "critical",
                "proximity_score": 99,
                "replay_pointer": "internal/fuzz_campaigns/deep/sample/acceptance_tcb_fuzz_report.json",
            },
            {
                "surface_id": "route_canonicalization_boundary",
                "machine_family": "routing/canonicalization",
                "current_evidence_class": "tested_discovery",
                "guard_families": ["route_canonicalization_guard"],
                "witness_ids": ["route_canonicalization_candidate_set_hash_mismatch"],
                "severity_band": "critical",
                "proximity_score": 110,
                "replay_pointer": "internal/fuzz_campaigns/deep/sample/acceptance_tcb_fuzz_report.json",
            },
            {
                "surface_id": "nonce_replay_guard",
                "machine_family": "replay/nonce",
                "current_evidence_class": "tested_discovery",
                "guard_families": ["nonce_replay_guard"],
                "witness_ids": ["nonce_cross_batch_replay"],
                "severity_band": "unknown",
                "proximity_score": 0,
                "replay_pointer": "internal/fuzz_campaigns/deep/sample/acceptance_tcb_fuzz_report.json",
            },
        ],
    }


def test_build_stateful_disaster_proof_obligation_packet_maps_critical_surfaces() -> None:
    payload = build_stateful_disaster_proof_obligation_packet(
        ratchet_report=_critical_ratchet_payload(),
        min_severity="high",
        include_unknown=True,
    )

    assert payload["schema"] == PROOF_OBLIGATION_PACKET_SCHEMA
    assert payload["ok"] is True
    assert payload["obligation_count"] == 2
    assert payload["classification_gap_count"] == 1
    by_surface = {row["surface_id"]: row for row in payload["obligations"]}
    assert by_surface["stale_settlement_boundary"]["formal_lane_count"] >= 3
    assert by_surface["route_canonicalization_boundary"]["target_evidence_class"] == "proved"
    assert all(lane["artifact_status"] == "present" for row in payload["obligations"] for lane in row["lanes"])
    assert payload["classification_gaps"][0]["surface_id"] == "nonce_replay_guard"


def test_build_stateful_disaster_proof_obligation_packet_fails_without_mapping() -> None:
    ratchet = _critical_ratchet_payload()
    ratchet["negative_knowledge_candidates"].append(
        {
            "surface_id": "unmapped_critical_surface",
            "machine_family": "demo",
            "current_evidence_class": "tested_discovery",
            "guard_families": ["demo_guard"],
            "witness_ids": ["demo_witness"],
            "severity_band": "critical",
            "proximity_score": 100,
        }
    )

    payload = build_stateful_disaster_proof_obligation_packet(ratchet_report=ratchet)

    assert payload["ok"] is False
    assert any("no formal lane mapping" in error for error in payload["errors"])


def test_build_stateful_disaster_proof_obligations_cli_writes_json(tmp_path: Path) -> None:
    ratchet_path = tmp_path / "ratchet.json"
    out = tmp_path / "obligations.json"
    ratchet_path.write_text(json.dumps(_critical_ratchet_payload(), indent=2, sort_keys=True), encoding="utf-8")

    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/build_stateful_disaster_proof_obligations.py",
            "--ratchet-report",
            str(ratchet_path),
            "--include-unknown",
            "--output",
            str(out),
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        text=True,
    )
    stdout_payload = json.loads(raw)
    file_payload = json.loads(out.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    assert file_payload["schema"] == PROOF_OBLIGATION_PACKET_SCHEMA
    assert file_payload["obligation_count"] == 2


def test_minimal_witness_language_audit_declares_critical_binding_fields() -> None:
    payload = build_minimal_witness_language_audit()

    assert payload["schema"] == MINIMAL_WITNESS_LANGUAGE_AUDIT_SCHEMA
    assert payload["ok"] is True
    by_surface = {row["surface_id"]: row for row in payload["surfaces"]}
    assert set(by_surface) == {
        "quote_receipt_certificate_boundary",
        "route_canonicalization_boundary",
        "settlement_attestation_policy_boundary",
        "stale_quote_receipt_boundary",
        "stale_settlement_boundary",
    }
    assert "candidate_set_hash" in by_surface["quote_receipt_certificate_boundary"]["required_binding_fields"]
    assert "winner_key" in by_surface["route_canonicalization_boundary"]["required_binding_fields"]
    assert "packet_hash" in by_surface["settlement_attestation_policy_boundary"]["required_binding_fields"]
    assert "quote_pool_fingerprint" in by_surface["stale_quote_receipt_boundary"]["required_binding_fields"]
    assert "pre_state_commitment" in by_surface["stale_settlement_boundary"]["required_binding_fields"]
    assert all(row["rejects_ambiguous_witnesses"] is True for row in payload["surfaces"])


def test_cross_surface_witness_exploration_plan_covers_requested_pairs() -> None:
    payload = build_cross_surface_witness_exploration_plan()

    assert payload["schema"] == CROSS_SURFACE_WITNESS_EXPLORATION_SCHEMA
    assert payload["ok"] is True
    by_pair = {row["pair_id"]: row for row in payload["pairs"]}
    assert set(by_pair) == {
        "quote_certificate_x_stale_quote_receipt",
        "settlement_attestation_x_stale_settlement",
        "route_canonicalization_x_quote_certificate",
        "stale_quote_receipt_x_stale_settlement",
        "route_canonicalization_x_stale_settlement",
    }
    assert by_pair["quote_certificate_x_stale_quote_receipt"]["surface_ids"] == [
        "quote_receipt_certificate_boundary",
        "stale_quote_receipt_boundary",
    ]
    assert by_pair["settlement_attestation_x_stale_settlement"]["surface_ids"] == [
        "settlement_attestation_policy_boundary",
        "stale_settlement_boundary",
    ]
    assert all(row["commands"] for row in payload["pairs"])
    assert all(row["evidence_class_ceiling"] == "tested_discovery" for row in payload["pairs"])


def _closure_packet(command: list[str]) -> dict:
    return {
        "schema": PROOF_OBLIGATION_PACKET_SCHEMA,
        "ok": True,
        "obligations": [
            {
                "obligation_id": "proof_obligation:demo_surface",
                "surface_id": "demo_surface",
                "target_evidence_class": "proved",
                "lanes": [
                    {
                        "kind": "lean",
                        "name": "demo_lane",
                        "commands": [command],
                        "missing_artifacts": [],
                    }
                ],
            }
        ],
    }


def test_run_stateful_disaster_proof_obligations_closes_passing_lane() -> None:
    payload = run_stateful_disaster_proof_obligations(
        packet=_closure_packet([sys.executable, "-c", "print('1 passed in 0.01s')"]),
        timeout_s=5,
    )

    assert payload["schema"] == PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA
    assert payload["ok"] is True
    assert payload["closed_count"] == 1
    result = payload["obligation_results"][0]
    assert result["closure_status"] == "closed"
    assert result["lane_results"][0]["status"] == "passed"


def test_run_stateful_disaster_proof_obligations_treats_skip_as_inconclusive() -> None:
    payload = run_stateful_disaster_proof_obligations(
        packet=_closure_packet([sys.executable, "-c", "print('1 skipped in 0.01s')"]),
        timeout_s=5,
    )

    assert payload["ok"] is False
    assert payload["inconclusive_count"] == 1
    assert payload["obligation_results"][0]["closure_status"] == "inconclusive"
    assert payload["obligation_results"][0]["lane_results"][0]["status"] == "inconclusive"


def test_run_stateful_disaster_proof_obligations_cli_writes_receipt(tmp_path: Path) -> None:
    packet = tmp_path / "packet.json"
    out = tmp_path / "closure.json"
    packet.write_text(
        json.dumps(_closure_packet([sys.executable, "-c", "print('1 passed in 0.01s')"]), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/run_stateful_disaster_proof_obligations.py",
            "--packet",
            str(packet),
            "--output",
            str(out),
            "--format",
            "json",
        ],
        cwd=ROOT_DIR,
        text=True,
    )
    stdout_payload = json.loads(raw)
    file_payload = json.loads(out.read_text(encoding="utf-8"))
    assert stdout_payload == file_payload
    assert file_payload["schema"] == PROOF_OBLIGATION_CLOSURE_RECEIPT_SCHEMA
    assert file_payload["closed_count"] == 1
