from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.stateful_scenario_bridge import (
    DISASTER_REACHABILITY_RATCHET_SCHEMA,
    DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA,
    DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA,
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
    build_disaster_search_expansion_plan,
    build_minimal_witness_language_audit,
    build_shapeforge_promotion_bridge_report,
    build_stateful_disaster_proof_obligation_packet,
    check_scenario_candidate,
    run_disaster_search_expansion_plan,
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


def test_disaster_search_expansion_plan_keeps_what_if_axes_open() -> None:
    payload = build_disaster_search_expansion_plan()

    assert payload["schema"] == DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA
    assert payload["ok"] is True
    assert payload["policy"]["readme_exhaustive_claim"] == "defer"
    by_axis = {row["axis_id"]: row for row in payload["axes"]}
    assert set(by_axis) >= {
        "epoch_split_brain",
        "identity_registry_drift",
        "canonicalization_equivocation",
        "serialization_width_aliasing",
        "resource_budget_abort",
        "repair_after_tamper",
        "external_state_drift",
        "atomicity_partial_side_effect",
        "restart_replay_persistence",
        "dependency_outage_fail_closed",
        "numeric_boundary_coupling",
        "advisory_cache_receipt_coherence",
        "market_namespace_version_isolation",
        "reciprocal_netting_pair_forgery",
        "bounded_advisory_search_envelope",
        "exact_out_candidate_domain_explosion",
        "tau_gate_policy_aliasing",
        "zusd_oracle_recovery_split_brain",
        "confidential_receipt_attestation_drift",
        "strategy_session_capability_replay",
        "fire_registry_proof_tree_supply_chain",
        "batch_clearing_fragmentation_ordering",
        "intent_auth_shape_replay",
        "perp_funding_liquidation_oracle_window",
        "proof_mining_packet_envelope_replay",
        "sealed_bid_reveal_commitment_binding",
        "curve_registry_dispatch_aliasing",
        "vault_reward_carry_spendability",
        "tau_net_client_transport_boundary",
        "tau_operator_policy_supply_chain",
        "settlement_proof_recompute_gate",
        "operations_parser_canonical_envelope",
        "resource_load_shedding_chaos_boundary",
        "cantor_region_partition_invariance",
        "autotrader_policy_artifact_replay",
        "state_accounting_size_boundary",
        "zusd_api_token_policy_surface",
        "dex_engine_sequence_anomaly_surface",
        "quote_receipt_gate_decomposition_consistency",
        "settlement_witness_lifecycle_value_drift",
        "dex_core_ref_parity_drift",
        "confidential_request_admission_gate_decomposition",
        "boundary_concolic_wrapper_consistency",
        "runtime_shell_adapter_consistency",
        "perp_submission_surface_gate_composition",
        "perp_v2_ref_oracle_parity_boundary",
        "exact_out_prefilter_winner_repair_boundary",
        "batch_refinement_mci_parity_boundary",
        "agent_policy_signing_artifact_boundary",
        "tau_runner_api_lifecycle_fail_closed",
        "fire_runtime_receipt_replay_boundary",
        "exact_in_route_certificate_guarded_key_boundary",
        "quote_receipt_transport_intent_boundary",
        "oracle_funding_clock_commitment_boundary",
        "intent_normal_form_nonce_gate_boundary",
        "zenograph_krr_policy_state_boundary",
        "zusd_native_accounting_gate_boundary",
        "proof_mining_manager_slot_control_boundary",
        "strategy_native_policy_guard_surface",
        "autotrader_policy_toolchain_state_boundary",
        "confidential_core_verifier_binding_boundary",
        "cantor_shapeforge_morphism_bridge_boundary",
        "fire_cli_supply_chain_receipt_boundary",
        "settlement_formal_packet_contract_boundary",
        "exact_out_formal_packet_contract_boundary",
        "strategy_residual_guard_binding_boundary",
        "perp_core_legacy_ref_hazard_boundary",
        "perp_engine_integration_oracle_bootstrap_boundary",
        "tau_witness_autotrader_binding_surface",
        "fire_registry_deployment_sync_boundary",
        "tla_queue_lifecycle_model_boundary",
        "exact_out_shadow_runtime_prefilter_boundary",
        "tau_runner_subprocess_transport_boundary",
        "settlement_apply_witness_native_boundary",
        "tau_operator_policy_receipt_symbolic_boundary",
        "settlement_price_provenance_semantic_boundary",
        "fire_kernel_release_verifier_boundary",
        "quote_receipt_native_adapter_parity_boundary",
        "perp_native_adapter_oracle_bva_boundary",
        "intent_nonce_confidential_state_native_boundary",
        "tla_perp_settlement_queue_model_boundary",
        "exact_in_lean_rank_projection_boundary",
        "exact_out_lean_certificate_boundary",
        "settlement_lean_price_oracle_boundary",
        "ltl_oracle_recovery_schedule_boundary",
        "exact_out_lean_concrete_recursion_boundary",
        "exact_out_lean_ordered_presentation_boundary",
        "exact_out_lean_repaired_key_cover_boundary",
        "permissionless_proof_mining_tooling_boundary",
        "claims_falsifier_inventory_boundary",
        "tau_semantic_proof_gate_split_boundary",
        "tau_autotrader_spec_guard_boundary",
        "fire_formal_runtime_note_boundary",
        "numeric_kernel_ml_history_boundary",
        "proof_mining_native_permissionless_boundary",
        "exact_out_lean_stream_support_boundary",
        "cross_module_tool_checker_boundary",
        "stateful_report_bridge_ranking_boundary",
        "tau_operator_library_artifact_boundary",
        "tau_exact_out_resource_spec_boundary",
        "dex_settlement_recovery_proof_unit_boundary",
        "acceptance_tcb_minimized_witness_boundary",
        "rc1_release_readiness_artifact_boundary",
        "advisory_swap_sandwich_preflight_boundary",
        "functional_core_split_parity_branch_boundary",
        "fire_cal_package_claim_boundary",
        "tokenomics_wash_budget_boundary",
        "decision_tau_witness_runner_boundary",
        "optimizer_liveness_prompt_boundary",
        "chaos_regret_campaign_boundary",
        "autotrader_krr_import_supply_chain_boundary",
        "amm_curve_il_parity_boundary",
        "lean_amm_canonical_math_boundary",
        "lean_repair_economics_boundary",
        "lean_autotrader_solver_policy_boundary",
        "krr_region_ba_reasoner_boundary",
        "tool_guard_lint_symbolic_boundary",
        "zusd_support_native_selector_boundary",
        "lean_cross_surface_composition_boundary",
        "operator_environment_tooling_boundary",
        "stateful_bounty_catalog_feedback_boundary",
        "batch_settler_greedy_adapter_boundary",
        "exact_out_adaptive_region_boundary",
        "shapeforge_release_ratchet_artifact_boundary",
        "zenograph_autotrader_ranking_artifact_boundary",
    }
    assert by_axis["epoch_split_brain"]["priority_score"] > by_axis["atomicity_partial_side_effect"]["priority_score"]
    assert "settlement_attestation_policy_boundary" in by_axis["epoch_split_brain"]["surface_ids"]
    assert "low-bit-equal identifiers with full-width disagreement" in by_axis["serialization_width_aliasing"]["mutation_families"]
    assert "split route containing a zero-flow candidate member" in by_axis["advisory_cache_receipt_coherence"]["mutation_families"]
    assert "same-direction COW fills" in by_axis["reciprocal_netting_pair_forgery"]["mutation_families"]
    assert "oracle quorum boundary with one stale or missing commitment" in by_axis["zusd_oracle_recovery_split_brain"]["mutation_families"]
    assert "curve tag changed while reserves and pool id remain stable" in by_axis["curve_registry_dispatch_aliasing"]["mutation_families"]
    assert "current construction mismatch after count or product receipt drift" in by_axis["cantor_region_partition_invariance"]["mutation_families"]
    assert "proof-gated region under shed-only path" in by_axis["resource_load_shedding_chaos_boundary"]["mutation_families"]
    assert "precheck-success with certificate-body drift" in by_axis["quote_receipt_gate_decomposition_consistency"]["mutation_families"]
    assert "adapter IR hash drift after kernel spec update" in by_axis["runtime_shell_adapter_consistency"]["mutation_families"]
    assert "signed surface valid with stale market version prefix" in by_axis["perp_submission_surface_gate_composition"]["mutation_families"]
    assert "prefilter support witness drops a feasible winner" in by_axis["exact_out_prefilter_winner_repair_boundary"]["mutation_families"]
    assert "fact pack replayed after KRR policy history update" in by_axis["zenograph_krr_policy_state_boundary"]["mutation_families"]
    assert "claimability gate passes after manager slot assignment drift" in by_axis["proof_mining_manager_slot_control_boundary"]["mutation_families"]
    assert "signal provenance root changes after signer binding" in by_axis["strategy_native_policy_guard_surface"]["mutation_families"]
    assert "backend invariance receipt valid after morphism product drift" in by_axis["cantor_shapeforge_morphism_bridge_boundary"]["mutation_families"]
    assert "compile receipt valid while object package root changes" in by_axis["fire_cli_supply_chain_receipt_boundary"]["mutation_families"]
    assert "candidate-domain contract valid but certified-winner packet uses different domain" in by_axis["exact_out_formal_packet_contract_boundary"]["mutation_families"]
    assert "oracle freshness guard accepts a strategy observation from a stale context" in by_axis["strategy_residual_guard_binding_boundary"]["mutation_families"]
    assert "first clearing-price publish followed by settle with no usable oracle snapshot" in by_axis["perp_engine_integration_oracle_bootstrap_boundary"]["mutation_families"]
    assert "wallet capability guard passes while session binding belongs to a neighboring policy" in by_axis["tau_witness_autotrader_binding_surface"]["mutation_families"]
    assert "adaptive liveness benchmark exceeds bounded disaster-runner budget and remains backlog" in by_axis["exact_out_shadow_runtime_prefilter_boundary"]["mutation_families"]
    assert "external-binary skipped coverage is mistaken for unreachable transport states" in by_axis["tau_runner_subprocess_transport_boundary"]["mutation_families"]
    assert "add/remove liquidity ratio witness drifts from apply witness under boundary reserves" in by_axis["settlement_apply_witness_native_boundary"]["mutation_families"]
    assert "symbolic policy alias metadata chain points to a neighboring lowered artifact" in by_axis["tau_operator_policy_receipt_symbolic_boundary"]["mutation_families"]
    assert "price provenance root changes after attestation but before compact-bundle replay" in by_axis["settlement_price_provenance_semantic_boundary"]["mutation_families"]
    assert "verifier receipt binds a release root whose compiler registry changed" in by_axis["fire_kernel_release_verifier_boundary"]["mutation_families"]
    assert "native precheck accepts while certificate gate rejects after body repair" in by_axis["quote_receipt_native_adapter_parity_boundary"]["mutation_families"]
    assert "ML-BVA settle_epoch case expects success without oracle_seen and positive index price" in by_axis["perp_native_adapter_oracle_bva_boundary"]["mutation_families"]
    assert "nonce batch policy accepts after confidential request root drift" in by_axis["intent_nonce_confidential_state_native_boundary"]["mutation_families"]
    assert "settlement witness inclusion queue accepts after bounded-open ingress drift" in by_axis["tla_perp_settlement_queue_model_boundary"]["mutation_families"]
    assert "rank projection packet proves a candidate order that the true-key winner proof rejects" in by_axis["exact_in_lean_rank_projection_boundary"]["mutation_families"]
    assert "route certificate proof omits a brute-force-complete candidate" in by_axis["exact_out_lean_certificate_boundary"]["mutation_families"]
    assert "oracle benefit accounting proof binds a different risk class than settlement value packet" in by_axis["settlement_lean_price_oracle_boundary"]["mutation_families"]
    assert "oracle recovery LTL permits a schedule rejected by zUSD Tau recovery" in by_axis["ltl_oracle_recovery_schedule_boundary"]["mutation_families"]
    assert "runtime generator checker emits a path whose structural recursion proof rejects" in by_axis["exact_out_lean_concrete_recursion_boundary"]["mutation_families"]
    assert "ordered quoted path completeness misses a presentation-equivalent candidate" in by_axis["exact_out_lean_ordered_presentation_boundary"]["mutation_families"]
    assert "repaired prefilter contract drops a candidate restored by full-domain certification" in by_axis["exact_out_lean_repaired_key_cover_boundary"]["mutation_families"]
    assert "round ledger accepts a solver claim whose claimability gate rejects" in by_axis["permissionless_proof_mining_tooling_boundary"]["mutation_families"]
    assert "falsifier output changes while claims registry status remains promoted" in by_axis["claims_falsifier_inventory_boundary"]["mutation_families"]
    assert "oracle freshness semantic lane disagrees with proof-mining reward gate" in by_axis["tau_semantic_proof_gate_split_boundary"]["mutation_families"]
    assert "tx envelope guard passes after live-admission or nonce root changes" in by_axis["tau_autotrader_spec_guard_boundary"]["mutation_families"]
    assert "fee-note reference result changes after formal packet construction" in by_axis["fire_formal_runtime_note_boundary"]["mutation_families"]
    assert "LP mint and LP ratio ML-BVA artifacts disagree on shared reserve boundaries" in by_axis["numeric_kernel_ml_history_boundary"]["mutation_families"]
    assert "verification flags gate passes while solver proof-mining claim uses a stale status root" in by_axis["proof_mining_native_permissionless_boundary"]["mutation_families"]
    assert "remaining capacity top-sum proof disagrees with residual allocation proof" in by_axis["exact_out_lean_stream_support_boundary"]["mutation_families"]
    assert "oracle split-brain checker passes while oracle divergence pack flags a neighboring root" in by_axis["cross_module_tool_checker_boundary"]["mutation_families"]
    assert "RC1 candidate index changes after stateful feedback report construction" in by_axis["stateful_report_bridge_ranking_boundary"]["mutation_families"]
    assert "lowered operator policy artifact passes while typed operator manifest changes" in by_axis["tau_operator_library_artifact_boundary"]["mutation_families"]
    assert "exact-out packet facts pass while audited bounds liveness rejects the runtime path" in by_axis["tau_exact_out_resource_spec_boundary"]["mutation_families"]
    assert "proof-mining claimability passes under a recovered Tau Testnet state with stale manager root" in by_axis["dex_settlement_recovery_proof_unit_boundary"]["mutation_families"]
    assert "acceptance campaign root changes after minimized witness publication" in by_axis["acceptance_tcb_minimized_witness_boundary"]["mutation_families"]
    assert "verified surface matrix row points to a stale candidate artifact" in by_axis["rc1_release_readiness_artifact_boundary"]["mutation_families"]
    assert "dynamic-fee sandwich boundary accepts a swap rejected by preflight" in by_axis["advisory_swap_sandwich_preflight_boundary"]["mutation_families"]
    assert "split routing dispatch changes candidate order without ref-parity drift" in by_axis["functional_core_split_parity_branch_boundary"]["mutation_families"]
    assert "FMOS file root differs from formal assurance claim root" in by_axis["fire_cal_package_claim_boundary"]["mutation_families"]
    assert "wash sequence passes while pro-rata budget is exhausted" in by_axis["tokenomics_wash_budget_boundary"]["mutation_families"]
    assert "decision witness adapter normalizes fields differently from Tau witness builder" in by_axis["decision_tau_witness_runner_boundary"]["mutation_families"]
    assert "audited bounds v1 accepts a liveness trace rejected by v2" in by_axis["optimizer_liveness_prompt_boundary"]["mutation_families"]
    assert "regret scheduler output changes after toolkit artifact capture" in by_axis["chaos_regret_campaign_boundary"]["mutation_families"]
    assert "KRR bundle build accepts facts imported under a stale source root" in by_axis["autotrader_krr_import_supply_chain_boundary"]["mutation_families"]
    assert "IL futures ref parity passes while route value differs across AMM family" in by_axis["amm_curve_il_parity_boundary"]["mutation_families"]
    assert "canonical winner proof assumes a rounding envelope not shared by route certificate" in by_axis["lean_amm_canonical_math_boundary"]["mutation_families"]
    assert "multi-incident conservation proof disagrees with treasury budget proof" in by_axis["lean_repair_economics_boundary"]["mutation_families"]
    assert "autotrader stage certificate proof binds a different action than live release proof" in by_axis["lean_autotrader_solver_policy_boundary"]["mutation_families"]
    assert "KRR reasoner fact changes after region BA report construction" in by_axis["krr_region_ba_reasoner_boundary"]["mutation_families"]
    assert "Sympy Tau normalizer changes a guard accepted by system-spec lint" in by_axis["tool_guard_lint_symbolic_boundary"]["mutation_families"]
    assert "support root changes after multi-oracle commit witness construction" in by_axis["zusd_support_native_selector_boundary"]["mutation_families"]
    assert "two-venue governance proof permits a role-collapse state rejected by release gate" in by_axis["lean_cross_surface_composition_boundary"]["mutation_families"]
    assert "Runpod helper captures artifacts that CHC verification wrapper cannot replay" in by_axis["operator_environment_tooling_boundary"]["mutation_families"]
    assert "sealed-bid disaster catalog omits a candidate promoted by RC1 candidate index" in by_axis["stateful_bounty_catalog_feedback_boundary"]["mutation_families"]
    assert "native batch-settler adapter selects an order outside greedy approximation bounds" in by_axis["batch_settler_greedy_adapter_boundary"]["mutation_families"]
    assert "adaptive region boundary accepts a path whose benchmark lane exceeds the disaster-runner cap" in by_axis["exact_out_adaptive_region_boundary"]["mutation_families"]
    assert "ratchet check accepts a ShapeForge artifact whose explorer extraction is stale" in by_axis["shapeforge_release_ratchet_artifact_boundary"]["mutation_families"]
    assert "ranking review bundle verifies after shadow baseline changes" in by_axis["zenograph_autotrader_ranking_artifact_boundary"]["mutation_families"]
    assert all(row["status"] == "not_exhausted" for row in payload["axes"])
    assert all(row["evidence_class_ceiling"] == "tested_discovery" for row in payload["axes"])


def test_disaster_search_expansion_plan_cli_writes_json(tmp_path: Path) -> None:
    out = tmp_path / "search_expansion.json"
    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/build_stateful_disaster_search_expansion_plan.py",
            "--axis-id",
            "epoch_split_brain",
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
    assert file_payload["schema"] == DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA
    assert file_payload["axis_count"] == 1
    assert file_payload["axes"][0]["axis_id"] == "epoch_split_brain"


def test_run_disaster_search_expansion_plan_marks_passing_axis_unreachable() -> None:
    plan = {
        "schema": DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA,
        "ok": True,
        "axes": [
            {
                "axis_id": "demo_axis",
                "priority_score": 1,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [[sys.executable, "-c", "print('ok')"]],
            }
        ],
    }

    payload = run_disaster_search_expansion_plan(plan=plan, timeout_s=10)

    assert payload["schema"] == DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA
    assert payload["ok"] is True
    assert payload["selected_axis_count"] == 1
    assert payload["unreachable_count"] == 1
    assert payload["axis_results"][0]["status"] == "unreachable_under_current_bounds"


def test_run_disaster_search_expansion_plan_can_aggregate_pytest_commands(tmp_path: Path) -> None:
    test_one = tmp_path / "test_one.py"
    test_one.write_text("def test_one():\n    assert True\n", encoding="utf-8")
    test_two = tmp_path / "test_two.py"
    test_two.write_text("def test_smoke_two():\n    assert True\n", encoding="utf-8")
    plan = {
        "schema": DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA,
        "ok": True,
        "axes": [
            {
                "axis_id": "demo_axis_one",
                "priority_score": 2,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [["pytest", "-q", str(test_one)]],
            },
            {
                "axis_id": "demo_axis_two",
                "priority_score": 1,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [["pytest", "-q", "-k", "smoke", str(test_two)]],
            },
        ],
    }

    payload = run_disaster_search_expansion_plan(plan=plan, timeout_s=30, aggregate_pytest=True)

    assert payload["ok"] is True
    assert payload["selected_axis_count"] == 2
    assert payload["unreachable_count"] == 2
    assert len(payload["aggregate_command_results"]) == 2
    for axis in payload["axis_results"]:
        assert axis["status"] == "unreachable_under_current_bounds"
        assert axis["command_results"][0]["covered_by_aggregate_pytest"] is True
        assert len(axis["command_results"][0]["aggregate_pytest_groups"]) == 1


def test_aggregate_pytest_components_join_overlaps_without_coupling_disjoint_axes(
    tmp_path: Path,
) -> None:
    test_one = tmp_path / "test_one.py"
    test_one.write_text("def test_one():\n    assert True\n", encoding="utf-8")
    test_two = tmp_path / "test_two.py"
    test_two.write_text("def test_two():\n    assert False\n", encoding="utf-8")
    test_three = tmp_path / "test_three.py"
    test_three.write_text("def test_three():\n    assert True\n", encoding="utf-8")
    plan = {
        "schema": DISASTER_SEARCH_EXPANSION_PLAN_SCHEMA,
        "ok": True,
        "axes": [
            {
                "axis_id": "overlap_left",
                "priority_score": 3,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [["pytest", "-q", str(test_one)]],
            },
            {
                "axis_id": "disjoint",
                "priority_score": 2,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [["pytest", "-q", str(test_two)]],
            },
            {
                "axis_id": "overlap_right",
                "priority_score": 1,
                "surface_ids": ["stale_settlement_boundary"],
                "what_if": "demo",
                "disaster_state_template": "demo",
                "commands": [["pytest", "-q", str(test_one), str(test_three)]],
            },
        ],
    }

    payload = run_disaster_search_expansion_plan(
        plan=plan,
        timeout_s=30,
        aggregate_pytest=True,
    )

    assert payload["ok"] is False
    assert len(payload["aggregate_command_results"]) == 3
    assert all(
        result["aggregate_pytest_group"]["path_count"] == 1
        for result in payload["aggregate_command_results"]
    )
    components_by_axis = {
        axis["axis_id"]: {
            group["component_id"]
            for group in axis["command_results"][0]["aggregate_pytest_groups"]
        }
        for axis in payload["axis_results"]
    }
    assert components_by_axis["overlap_left"] < components_by_axis["overlap_right"]
    assert components_by_axis["disjoint"].isdisjoint(components_by_axis["overlap_left"])
    status_by_axis = {axis["axis_id"]: axis["status"] for axis in payload["axis_results"]}
    assert status_by_axis == {
        "overlap_left": "unreachable_under_current_bounds",
        "disjoint": "found_or_regressed",
        "overlap_right": "unreachable_under_current_bounds",
    }


def test_run_disaster_search_expansion_plan_cli_writes_receipt(tmp_path: Path) -> None:
    out = tmp_path / "search_receipt.json"
    raw = subprocess.check_output(
        [
            sys.executable,
            "tools/run_stateful_disaster_search_expansion_plan.py",
            "--axis-id",
            "epoch_split_brain",
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
    assert file_payload["schema"] == DISASTER_SEARCH_EXPANSION_RECEIPT_SCHEMA
    assert file_payload["selected_axis_count"] == 1
    assert file_payload["axis_results"][0]["axis_id"] == "epoch_split_brain"


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
