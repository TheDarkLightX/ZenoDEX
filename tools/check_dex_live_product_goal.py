#!/usr/bin/env python3
"""Audit retained product evidence and current route-quarantine posture."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.local_route_quarantine import QUARANTINED_ROUTE_ENVIRONMENT_V1  # noqa: E402

SCHEMA = "zenodex/dex_live_product_goal_audit/v1"


@dataclass(frozen=True)
class AnchorCheck:
    area_id: str
    check_id: str
    path: str
    anchors: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class ForbiddenCheck:
    area_id: str
    check_id: str
    path: str
    pattern: re.Pattern[str]
    description: str


ANCHOR_CHECKS: tuple[AnchorCheck, ...] = (
    AnchorCheck(
        area_id="mounted_ui_direction",
        check_id="app_retains_all_product_tabs",
        path="tools/dex-ui/src/App.jsx",
        description="The ZenoDEX shell retains spot, perps, zUSD, Oracle, Strategy, and Confidential tabs without granting route authority.",
        anchors=(
            "PerpTradingView",
            "StrategyWorkbench",
            "ZUSDWorkbench",
            "ZenoOracleDashboard",
            "ConfidentialWorkbench",
            "{ id: 'perps', label: 'Perpetuals' }",
            "{ id: 'strategy', label: 'Strategy' }",
            "{ id: 'zusd', label: 'zUSD' }",
            "{ id: 'oracle', label: 'Oracle' }",
            "{ id: 'confidential', label: 'Confidential' }",
        ),
    ),
    AnchorCheck(
        area_id="mounted_ui_direction",
        check_id="readme_retains_historical_product_inventory",
        path="tools/dex-ui/README.md",
        description="The UI README distinguishes retained surfaces from currently admitted routes.",
        anchors=(
            "Current route posture:",
            "Swap and pools target the Zeno ledger spot path.",
            "Oracle can bind to the local `tools/zenodex-oracle serve` API.",
            "stream-9 wallet and stream-11 monetary routes",
            "retained stream-8 donor panel",
            "Strategy retains a receipt-backed AutoTrader research panel",
            "Confidential exposes live operator posture through `GET /api/confidential/status`",
            "/api/confidential/attestation/*",
        ),
    ),
    AnchorCheck(
        area_id="mounted_ui_direction",
        check_id="surface_status_matrix_tracks_historical_tabs",
        path="docs/ZENODEX_UI_SURFACE_STATUS_2026_05_20.md",
        description="The dated surface matrix labels its tab inventory as historical donor evidence.",
        anchors=(
            "## Historical donor surface inventory",
            "| Swap / Pools | Yes |",
            "| zUSD | UI retained; stream-9 wallet and stream-11 monetary routes unmounted |",
            "| Oracle | Yes |",
            "| Perpetuals | UI retained; stream-8 live wallet route unmounted |",
            "| Strategy | UI retained; live route unmounted |",
            "| Confidential | Yes |",
        ),
    ),
    AnchorCheck(
        area_id="zeno_oracle_live",
        check_id="oracle_ui_has_write_smoke_hook",
        path="tools/dex-ui/src/components/ZenoOracleDashboard.jsx",
        description="The mounted Oracle tab has a browser smoke hook for local write-enabled receipt flow verification.",
        anchors=(
            "zenodexUiSmokeOracleWrites",
            "oracleSmokeRan",
            "Quick Verify",
        ),
    ),
    AnchorCheck(
        area_id="zeno_oracle_live",
        check_id="oracle_browser_tests_cover_writes_and_fail_closed",
        path="tests/integration/test_zeno_oracle_ui_bridge.py",
        description="Oracle browser tests cover write-enabled local flow and fail-closed dashboard behavior.",
        anchors=(
            "zenodexUiSmokeOracleWrites",
            "zenodexUiSmokeOracleAuthorityExercise",
            "test_oracle_ui_smoke_runs_authority_exercise_flow",
            "test_oracle_ui_smoke_fails_closed_when_local_service_unreachable",
            "test_oracle_ui_smoke_fails_closed_on_malformed_dashboard_response",
        ),
    ),
    AnchorCheck(
        area_id="zeno_oracle_live",
        check_id="oracle_authority_exercise_api_and_ui_are_mounted",
        path="tools/dex-ui/src/components/ZenoOracleDashboard.jsx",
        description="The mounted Oracle Governance view can run a bounded authority exercise and render its receipt state.",
        anchors=(
            "Authority Exercise",
            "Run Authority Exercise",
            "zenodexUiSmokeOracleAuthorityExercise",
            "/api/oracle/authority/exercise/evaluate",
            "oracle authority exercise accepted",
            "Receipt binding",
            "Public evidence binding",
        ),
    ),
    AnchorCheck(
        area_id="zeno_oracle_live",
        check_id="oracle_readme_documents_operator_console",
        path="tools/dex-ui/README.md",
        description="The README documents the local ZenoOracle operator console and its write-enabled mode.",
        anchors=(
            "The Oracle tab is a local ZenoOracle operator console.",
            "Local Oracle writes are disabled by default.",
            "--allow-writes",
            "typed OracleAuthorization",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="zusd_stream11_donor_api_is_retained",
        path="src/integration/zusd_monetary_wallet_api.py",
        description="The unmounted stream-11 zUSD monetary wallet implementation is retained as donor evidence.",
        anchors=(
            "stream-11 zUSD monetary",
            "ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF",
            "verify_live_proof_wrapper",
            "zusd_stream11_live_monetary_v0",
            "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING",
            "_build_prepare_response",
            "external_signed_payload",
            "_status_payload",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="zusd_ui_retains_gated_token_and_monetary_surfaces",
        path="tools/dex-ui/src/components/ZUSDWorkbench.jsx",
        description="The zUSD tab retains both donor components behind exact runtime presentation gates.",
        anchors=(
            "ZUSDMonetarySurface",
            "ZUSDTauWalletSurface",
            "zUSD value routes are quarantined",
            "zusdMonetaryWalletEnabled && <ZUSDMonetarySurface />",
            "zusdTauWalletEnabled && <ZUSDTauWalletSurface />",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="perps_stream8_donor_api_is_retained",
        path="src/integration/perps_wallet_api.py",
        description="The unmounted stream-8 perps wallet implementation is retained as donor evidence.",
        anchors=(
            "PERPS_WALLET_TAU_HOST",
            "PERPS_WALLET_REQUIRE_PRODUCTION_ORACLE_AUTHORITY",
            "PERPS_WALLET_REQUIRE_ZK_PROOF",
            "oracle_authority_exercise",
            "verify_live_proof_wrapper",
            "_build_prepare_response",
            "external_signed_payload",
            "_status_payload",
            "stream11_zusd_zk_wrapper",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="perps_ui_retains_live_wallet_donor_surface",
        path="tools/dex-ui/src/components/perps/PerpTradingView.jsx",
        description="The perps UI retains its donor wallet component behind exact runtime presentation admission.",
        anchors=(
            "PerpLiveWalletSurface",
            "!demoMode && perpsWalletEnabled && (",
            "<PerpLiveWalletSurface />",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="perps_ui_renders_oracle_authority_exercise_receipt",
        path="tools/dex-ui/src/components/perps/PerpLiveWalletSurface.jsx",
        description="The retained perps donor surface renders authority-exercise receipt fields.",
        anchors=(
            "oracleAuthorityExercise",
            "oracle authority exercised",
            "oracle authority receipt",
            "ZK Artifacts",
            "zk artifacts",
            "zk binding",
            "walletRecoveryExercise",
            "recovery exercise",
            "recovery receipt",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="autotrader_api_donor_retains_bounded_guards",
        path="src/integration/autotrader_live_api.py",
        description="The unmounted Strategy donor retains prepare, submit, execute-once, and bounded supervisor guards for future refinement.",
        anchors=(
            "/api/strategy/autotrader/execute-once",
            "/api/strategy/autotrader/supervisor/preflight",
            "/api/strategy/autotrader/supervisor/execute",
            "external_signed_payload",
            "user_rule_summary",
            "supervisor_template_not_allowed",
            "supervisor_action_not_allowed",
            "_build_prepare_response",
            "_build_submit_response",
            "_status_payload",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="strategy_ui_has_submit_and_execute_smokes",
        path="tools/dex-ui/src/components/StrategyWorkbench.jsx",
        description="The retained Strategy donor includes browser test hooks for prepare, submit, execute-once, and supervised local/testnet ticks.",
        anchors=(
            "AutoTrader Live Prepare",
            "zenodexUiSmokeStrategyLive",
            "zenodexUiSmokeStrategyLiveSubmit",
            "zenodexUiSmokeStrategyLiveExecute",
            "zenodexUiSmokeStrategySupervisor",
            "Supervisor Preflight",
            "Run Supervisor Tick",
            "Supervisor template",
            "Supervisor actions",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="beyond_spot_browser_and_backend_tests_exist",
        path="tests/integration/test_zusd_monetary_wallet_ui_bridge.py",
        description="Retained stream-11 browser source records historical donor scenarios without current execution authority.",
        anchors=(
            "test_zusd_monetary_wallet_ui_smoke_through_browser",
            "test_zusd_monetary_wallet_browser_fails_closed_through_toxiproxy_limit_data",
            "zusd_stream11_live_monetary_v0",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="docker_tau_node_zusd_to_perps_test_exists",
        path="tests/integration/test_zusd_monetary_wallet_ui_docker.py",
        description="The zUSD-to-perps Docker scenario is retained as an unmounted donor.",
        anchors=(
            "test_zusd_monetary_wallet_ui_smoke_through_docker_tau_node",
            "perps",
            "zUSD",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="perps_browser_tests_cover_oracle_bridge",
        path="tests/integration/test_perps_wallet_ui_bridge.py",
        description="Perps bridge browser scenarios are retained as unmounted donor evidence.",
        anchors=(
            "test_perps_wallet_ui_settle_epoch_builds_typed_oracle_bridge",
            "test_perps_wallet_ui_fails_closed_through_toxiproxy_limit_data",
            "oracle authority exercised yes",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="zusd_tau_browser_donor_is_quarantined",
        path="tests/integration/test_zusd_tau_wallet_ui_bridge.py",
        description="The zUSD Tau browser scenario is retained without current route authority.",
        anchors=(
            "test_zusd_tau_wallet_ui_smoke_through_browser",
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="zusd_tau_docker_donor_is_quarantined",
        path="tests/integration/test_zusd_tau_wallet_ui_docker.py",
        description="The zUSD Tau Docker scenario is retained without current route authority.",
        anchors=(
            "test_zusd_tau_wallet_ui_smoke_through_docker_tau_node",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="retired_value_route_browser_controls_are_quarantined",
        path="tests/integration/test_retired_value_route_ui_quarantine.py",
        description="A browser scenario attempts URL and fragment overrides and requires perps and zUSD signer controls to remain absent.",
        anchors=(
            "test_current_profile_hides_quarantined_value_route_controls",
            "perpsPreviewWrites=true",
            "operatorPrivkey=hostile-override",
            "signerPrivkey=hostile-override",
            'assert "Operator console" not in perps_dom',
            'assert "Signer credential" not in zusd_dom',
        ),
    ),
    AnchorCheck(
        area_id="transaction_surfaces_beyond_spot",
        check_id="autotrader_browser_donor_covers_execute_once",
        path="tests/integration/test_autotrader_live_ui_bridge.py",
        description="Historical AutoTrader browser donors cover execute-once plus bounded supervisor replay-guard flows.",
        anchors=(
            "test_autotrader_live_execute_once_ui_smoke_through_browser",
            "test_autotrader_live_supervisor_ui_smoke_through_browser",
            "zenodexUiSmokeStrategyLiveExecute",
            "zenodexUiSmokeStrategySupervisor",
            "AutoTrader Live Prepare",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="cross_stream_stateful_replay_names_disaster_states",
        path="tools/zenodex_live_cross_stream_stateful.py",
        description="A deterministic cross-stream replay harness names disaster states across zUSD, perps, AutoTrader, and Confidential.",
        anchors=(
            "zenodex.live_cross_stream_stateful_replay.v1",
            "duplicate_side_effect_after_replay",
            "cross_stream_partial_mutation",
            "stale_or_missing_oracle_evidence_settles",
            "autotrader_ambiguous_send_replayed_or_silently_released",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="cross_stream_stateful_tests_assert_receipt",
        path="tests/integration/test_zenodex_live_cross_stream_stateful.py",
        description="The stateful replay test asserts scenario counts, fuzz bounds, and disaster-state identities.",
        anchors=(
            "test_live_cross_stream_stateful_replay_accepts_all_scenarios",
            "scenario_count",
            "seed_count",
            "long_horizon_cross_stream_partial_mutation",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="confidential_runtime_execute_api_and_ui_are_mounted",
        path="src/integration/confidential_attestation_api.py",
        description="The confidential API exposes a bounded runtime execute route with redacted public receipts and operator-posture binding hashes.",
        anchors=(
            "POST /api/confidential/attestation/execute",
            "local_testnet_external_verifier_bounded_runtime_receipt",
            "bad_runtime_request",
            "result_redacted",
            "operator_status_hash",
            "approved_measurements_hash",
            "external_verifier_binding_hash",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="confidential_runtime_browser_smoke_renders_redacted_receipt",
        path="tests/integration/test_confidential_ui_bridge.py",
        description="Mounted confidential browser smoke renders the bounded runtime receipt and its redaction markers.",
        anchors=(
            "runtime receipt ready",
            "result redacted",
            "effect digest 0x",
            "status hash 0x",
            "allowlist hash 0x",
            "verifier binding 0x",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="confidential_claim_scope_gate_remains_present",
        path="tools/check_public_claim_scope.py",
        description="The public claim-scope checker rejects confidentiality overclaims for the mounted Confidential surface.",
        anchors=(
            "confidential_verifiable_overclaim",
            "tee_hardware_confidentiality_proof_overclaim",
            "hardware_confidentiality_proven_overclaim",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="live_proof_wrapper_carries_artifact_binding",
        path="src/integration/live_proof_wrapper.py",
        description="The shared live proof-wrapper gate carries declared verifier and circuit artifact metadata plus a binding hash.",
        anchors=(
            "artifact_binding_configured",
            "artifact_binding_complete",
            "PROOF_VERIFIER_ARTIFACT_JSON",
            "PROOF_CIRCUIT_ARTIFACT_JSON",
            "binding_hash",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="perps_proof_wrapper_submit_blocks_broadcast",
        path="tests/integration/test_perps_wallet_api.py",
        description="Retained perps test source names rejected proof-wrapper and Tau-send scenarios; execution is outside this lexical inventory.",
        anchors=(
            "test_submit_deposit_collateral_rejected_zk_proof_blocks_sendtx",
            "zk_reject_broadcasts_tx",
            "fixture proof rejected",
            "PERPS_WALLET_REQUIRE_ZK_PROOF",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="zusd_proof_wrapper_submit_blocks_broadcast",
        path="tests/integration/test_zusd_monetary_wallet_api.py",
        description="Retained zUSD test source names rejected proof-wrapper and Tau-send scenarios; execution is outside this lexical inventory.",
        anchors=(
            "test_submit_mint_rejected_zk_proof_blocks_sendtx",
            "zk_reject_broadcasts_tx",
            "fixture proof rejected",
            "ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="perps_wallet_recovery_exercise_receipt",
        path="tests/integration/test_perps_wallet_api.py",
        description="Retained perps test source names recovery, rotation, and lifecycle-receipt scenarios; execution is outside this lexical inventory.",
        anchors=(
            "test_perps_wallet_recovery_exercise_ready_receipt",
            "test_perps_wallet_recovery_exercise_blocks_early_request",
            "test_perps_wallet_recovery_exercise_blocks_bad_guardian_signature_quorum",
            "test_perps_wallet_rotation_exercise_ready_receipt",
            "test_perps_wallet_rotation_exercise_blocks_missing_rotation_transition",
            "test_perps_wallet_rotation_exercise_blocks_bad_guardian_signature_quorum",
            "test_status_loads_ready_perps_wallet_recovery_exercise",
            "test_status_loads_ready_perps_wallet_rotation_exercise",
            "test_recovery_evaluate_endpoint_blocks_threshold_gap",
            "test_recovery_evaluate_endpoint_blocks_bad_guardian_signature_quorum",
            "test_rotation_evaluate_endpoint_blocks_bad_broadcast_epoch",
            "test_rotation_evaluate_endpoint_blocks_bad_guardian_signature_quorum",
            "PERPS_WALLET_RECOVERY_EXERCISE_JSON",
            "recovery_exercise_ready",
            "guardian_signature_quorum",
            "PERPS_WALLET_ROTATION_EXERCISE_JSON",
            "rotation_exercise_ready",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="perps_wallet_device_approval_receipt",
        path="tests/integration/test_perps_wallet_api.py",
        description="Retained perps test source names device-approval and signer-device receipt scenarios; execution is outside this lexical inventory.",
        anchors=(
            "test_perps_wallet_device_approval_exercise_ready_receipt",
            "test_perps_wallet_device_approval_exercise_blocks_missing_user_presence",
            "test_perps_wallet_device_approval_exercise_blocks_reused_nonce",
            "test_perps_wallet_signer_device_integration_ready_receipt",
            "test_perps_wallet_signer_device_integration_blocks_missing_user_presence",
            "test_status_loads_ready_perps_wallet_device_approval_exercise",
            "test_status_loads_ready_perps_wallet_signer_device_integration",
            "test_device_approval_evaluate_endpoint_blocks_missing_user_presence",
            "test_device_approval_evaluate_endpoint_blocks_reused_nonce",
            "test_signer_device_evaluate_endpoint_blocks_missing_user_presence",
            "test_signer_device_evaluate_endpoint_blocks_missing_provider",
            "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",
            "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",
            "device_approval_ready",
            "signer_device_ready",
            "sign_admission_receipt",
            "payload_nonce_reused",
            "local_user_presence_missing",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="perps_wallet_recovery_exercise_browser_receipt",
        path="tests/integration/test_perps_wallet_ui_bridge.py",
        description="Retained perps donor smoke preserves recovery and signer scenarios without mounted authority.",
        anchors=(
            "PERPS_WALLET_RECOVERY_EXERCISE_JSON",
            "recovery exercise ready",
            "recovery signed quorum 2/2",
            "recovery receipt 0x",
            "PERPS_WALLET_ROTATION_EXERCISE_JSON",
            "rotation exercise ready",
            "rotation signed quorum 2/2",
            "rotation receipt 0x",
            "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_JSON",
            "device approval ready",
            "device sign admission ok",
            "device approval receipt 0x",
            "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_JSON",
            "signer device ready",
            "signer backend os-keychain",
            "signer device receipt 0x",
        ),
    ),
    AnchorCheck(
        area_id="assurance_depth",
        check_id="completion_plan_records_residual_limits",
        path="docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md",
        description="The completion plan records current evidence and the remaining production-grade limits.",
        anchors=(
            "public-testnet live exercise of signed production Oracle authority",
            "hardware/OS wallet UX and recovery flows",
            "proof/ZK wrapping",
            "Additional daemon-backed mounted browser Toxiproxy evidence",
            "Additional confidential surface claim-scope evidence",
            "Additional perps Oracle-authority exercise receipt evidence",
            "Additional perps wallet recovery-exercise evidence",
            "Additional stream `8`/`11` proof-wrapper gate evidence",
            "Additional stream `8`/`11` proof-wrapper submit fail-closed evidence",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="api_startup_refuses_stream8_and_stream11",
        path="src/integration/api_server.py",
        description="API startup has raw-environment admission and parsed-config backstops for stream 8 and stream 11.",
        anchors=(
            "quarantined_route_environment_rejections_v1(dict(os.environ))",
            "PERPS_WALLET_API_ENABLED depends on the retired Tau",
            "ZUSD_MONETARY_WALLET_API_ENABLED depends on the retired Tau",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="api_state_attachment_cannot_reenable_retired_routes",
        path="src/integration/api_server.py",
        description="Direct API state attachment rejects retired route flags before imports or server mutation.",
        anchors=(
            'refuse_current_local_operator_operation_v1("api_server_state_attachment")',
            "httpd.perps_wallet_api_enabled = False",
            "httpd.zusd_tau_wallet_api_enabled = False",
            "httpd.zusd_monetary_wallet_api_enabled = False",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="retired_route_helpers_refuse_before_shell_effects",
        path="tools/zenoctl_testnet_local/lifecycle.py",
        description="Retained internal helpers refuse the current profile before compose, file, network, or process effects.",
        anchors=(
            'refuse_current_local_operator_operation_v1("seed_api_state")',
            'refuse_current_local_operator_operation_v1("materialize_release_native_collateral")',
            'refuse_current_local_operator_operation_v1("release_flow_smoke")',
            'refuse_current_local_operator_operation_v1("perps_wallet_cycle_smoke")',
            'refuse_current_local_operator_operation_v1("cloudflare_quick_tunnel")',
            'refuse_current_local_operator_operation_v1("zusd_transfer_payload")',
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="compose_disables_stream8_and_stream11_controls",
        path="docker-compose.local-testnet.yml",
        description="The checked-in compose profile disables route, signing, mining, and faucet controls.",
        anchors=(
            'PERPS_WALLET_API_ENABLED: "false"',
            'PERPS_WALLET_ALLOW_LOCAL_SIGNING: "false"',
            'PERPS_WALLET_AUTO_MINE: "false"',
            'PERPS_WALLET_TESTNET_FAUCET_ENABLED: "false"',
            'ZUSD_MONETARY_WALLET_API_ENABLED: "false"',
            'ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING: "false"',
            'ZUSD_MONETARY_WALLET_AUTO_MINE: "false"',
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="runtime_config_disables_retired_value_route_ui",
        path="tools/dex-ui/public/zenodex-config.json",
        description="The checked-in runtime profile explicitly disables each retired value-route UI surface.",
        anchors=(
            '"perpsWalletUiEnabled": false',
            '"zusdTauWalletUiEnabled": false',
            '"zusdMonetaryWalletUiEnabled": false',
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="runtime_value_route_presentation_is_exact_and_immutable",
        path="tools/dex-ui/src/lib/api.js",
        description="The current UI profile has one immutable false presentation decision that ignores browser input.",
        anchors=(
            "getRuntimeValueRoutePresentationV1",
            "CURRENT_PROFILE_QUARANTINED_VALUE_ROUTES_V1",
            "void runtimeConfig",
            "return CURRENT_PROFILE_QUARANTINED_VALUE_ROUTES_V1",
            "Future activation requires a new release-backed profile and helper",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="perps_ui_gate_resists_write_override",
        path="tools/dex-ui/src/lib/PerpProvider.jsx",
        description="Perps write requests and local defaults remain subordinate to exact runtime presentation admission.",
        anchors=(
            "demoMode || (perpsWalletEnabled && perpsPreviewWritesRequested)",
            "perps_route_quarantined",
            "else if (!perpsWalletEnabled)",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="ui_contract_checks_current_quarantine_flags",
        path="tools/dex-ui/scripts/check-ui-contract.mjs",
        description="The executable UI contract requires every current-profile quarantined route flag to exist and equal false.",
        anchors=(
            "current_quarantined_value_route_ui_flags",
            "runtimeConfig[field] !== false",
            "runtime config must keep ${field} exactly false",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="quarantine_has_named_negative_test_sources",
        path="tests/integration/test_zenoctl_testnet_local.py",
        description="The retained test source names manifest, smoke, direct-helper, and no-effect quarantine scenarios; this lexical check does not execute them.",
        anchors=(
            "test_manifest_rejects_retired_tau_value_lanes",
            "test_identity_bound_retired_route_manifest_is_quiesced_before_lifecycle",
            "test_foreign_manifest_quiesces_only_the_selected_derived_project",
            "test_release_smoke_without_state_creates_no_runtime_effects",
            "test_browser_smoke_cases_omit_quarantined_value_routes",
            "test_compose_overlay_quarantines_retired_perps_and_zusd_monetary_routes",
            "test_quarantined_api_mount_has_no_retired_route_reconstitution_material",
            "test_historical_donor_helpers_refuse_before_any_effect",
            "test_seed_api_state_rejects_current_profile_before_compose_effect",
            "test_release_flow_helper_rejects_current_profile_before_file_or_network_effect",
            "test_perps_cycle_helper_rejects_current_profile_before_network_effect",
            "test_quick_tunnel_helper_rejects_current_profile_before_runner_or_process_effect",
            "test_zusd_transfer_payload_rejects_current_profile_before_role_or_network_effect",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="operator_docs_state_current_quarantine",
        path="docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md",
        description="Operator documentation distinguishes current quarantine from historical donor evidence.",
        anchors=(
            "Current authority correction (2026-08-28)",
            "They do not establish current route reachability, settlement authority, or production readiness.",
            "The current profile refuses the retained perps wallet route",
        ),
    ),
    AnchorCheck(
        area_id="current_route_quarantine",
        check_id="zusd_docs_state_current_quarantine",
        path="docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md",
        description="The zUSD donor-status document identifies current stream 11 quarantine and its authority ceiling.",
        anchors=(
            "Current authority correction (2026-08-28)",
            "The current profile keeps stream `11` unmounted.",
            "does not establish current route reachability",
        ),
    ),
)

FORBIDDEN_CHECKS: tuple[ForbiddenCheck, ...] = (
    ForbiddenCheck(
        area_id="mounted_ui_direction",
        check_id="readme_strategy_no_submit_stale_line_removed",
        path="tools/dex-ui/README.md",
        description="The README must not retain the stale claim that Strategy never submits local/testnet strategies.",
        pattern=re.compile(r"Strategy remains.*does\s+not\s+submit\s+live\s+strategies", re.IGNORECASE | re.DOTALL),
    ),
)

AREA_TITLES: dict[str, str] = {
    "mounted_ui_direction": "Retained UI Direction",
    "zeno_oracle_live": "ZenoOracle Live Mount",
    "transaction_surfaces_beyond_spot": "Retained Transaction Donor Surfaces Beyond Spot",
    "assurance_depth": "Browser, Stateful, And Resilience Evidence",
    "current_route_quarantine": "Current Stream 8 And Stream 11 Route Quarantine",
}

RESIDUAL_LIMITS: tuple[dict[str, str], ...] = (
    {
        "id": "current_tau_route_rebind",
        "description": "Stream 8 perps and stream 11 zUSD monetary remain unmounted until current-Tau ingress, verifier-owned execution time, route proof, and ZenoLedger publication bindings are implemented and admitted.",
    },
    {
        "id": "production_oracle_authority",
        "description": "Oracle and retained perps donor surfaces carry bounded signed authority-exercise evidence, while current perps route admission and public exercise of a signed production Oracle authority profile remain open.",
    },
    {
        "id": "hardware_wallet_ux",
        "description": "Retained perps donor status carries bounded signer-device, device-approval, recovery, and rotation evidence; current route admission and live device execution remain open.",
    },
    {
        "id": "zk_wrapping",
        "description": "Retained zUSD and perps donors can carry declared verifier and circuit-artifact bindings, but current route proofs, production circuit artifacts, and soundness evidence remain open.",
    },
    {
        "id": "production_autotrader",
        "description": "AutoTrader evidence covers explicit local/testnet execute-once plus bounded supervisor ticks with replay guard, per-process run budget, and template/action binding, not unattended production execution.",
    },
    {
        "id": "confidential_runtime",
        "description": "Confidential evidence covers attestation receipt/admission, bounded redacted runtime receipts, replay protection, redaction posture, and public operator or verifier binding hashes, not runtime private execution privacy.",
    },
)


def _normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _read_text(root: Path, rel_path: str) -> tuple[str | None, str | None]:
    path = root / rel_path
    if not path.is_file():
        return None, "missing_file"
    return path.read_text(encoding="utf-8"), None


def check_anchor(check: AnchorCheck, *, root: Path = REPO_ROOT) -> dict[str, Any]:
    text, error = _read_text(root, check.path)
    missing = list(check.anchors)
    if text is not None:
        normalized = _normalize(text)
        missing = [anchor for anchor in check.anchors if _normalize(anchor) not in normalized]
    return {
        "id": check.check_id,
        "kind": "source_anchors",
        "path": check.path,
        "ok": error is None and not missing,
        "description": check.description,
        "execution_verified": False,
        "missing": missing,
        "error": error,
    }


def check_forbidden(check: ForbiddenCheck, *, root: Path = REPO_ROOT) -> dict[str, Any]:
    text, error = _read_text(root, check.path)
    matches: list[str] = []
    if text is not None:
        normalized = _normalize(text)
        matches = [match.group(0) for match in check.pattern.finditer(normalized)]
    return {
        "id": check.check_id,
        "kind": "forbidden",
        "path": check.path,
        "ok": error is None and not matches,
        "description": check.description,
        "matches": matches,
        "error": error,
    }


def _group_by_area(checks: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {area_id: [] for area_id in AREA_TITLES}
    for check in checks:
        grouped.setdefault(str(check["area_id"]), []).append({key: value for key, value in check.items() if key != "area_id"})
    return [
        {
            "id": area_id,
            "title": AREA_TITLES.get(area_id, area_id),
            "ok": all(check["ok"] for check in area_checks),
            "checks": area_checks,
        }
        for area_id, area_checks in grouped.items()
    ]


def audit_live_product_goal(*, root: Path = REPO_ROOT) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    for anchor_check in ANCHOR_CHECKS:
        result = check_anchor(anchor_check, root=root)
        result["area_id"] = anchor_check.area_id
        checks.append(result)
    for forbidden_check in FORBIDDEN_CHECKS:
        result = check_forbidden(forbidden_check, root=root)
        result["area_id"] = forbidden_check.area_id
        checks.append(result)

    areas = _group_by_area(checks)
    ok = all(area["ok"] for area in areas)
    return {
        "schema": SCHEMA,
        "ok": ok,
        "goal_complete": False,
        "status": "source_inventory_present_with_quarantined_retired_tau_routes"
        if ok
        else "missing_required_source_inventory",
        "source_anchor_inventory_only": True,
        "test_execution_verified": False,
        "production_authority": "NONE",
        "vm_gates_closed": [],
        "quarantined_route_authority": "NONE",
        "quarantined_routes": list(QUARANTINED_ROUTE_ENVIRONMENT_V1),
        "areas": areas,
        "residual_limits": list(RESIDUAL_LIMITS),
    }


def _format_failures(report: dict[str, Any]) -> str:
    lines: list[str] = []
    for area in report["areas"]:
        for check in area["checks"]:
            if check["ok"]:
                continue
            location = f"{area['id']}:{check['id']}:{check['path']}"
            if check.get("error"):
                lines.append(f"{location}: {check['error']}")
            for missing in check.get("missing", []):
                lines.append(f"{location}: missing anchor: {missing}")
            for match in check.get("matches", []):
                lines.append(f"{location}: forbidden text: {match}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    args = parser.parse_args(argv)

    report = audit_live_product_goal(root=args.root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print(f"dex live-product source inventory ok: {report['status']}")
        print("residual limits:")
        for limit in report["residual_limits"]:
            print(f"- {limit['id']}: {limit['description']}")
    else:
        print(_format_failures(report), file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
