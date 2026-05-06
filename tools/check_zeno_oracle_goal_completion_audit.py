#!/usr/bin/env python3
"""Fail-closed completion audit for the active ZenoOracle/ZenoProof goal."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "zenodex.oracle.goal_completion_audit.v1"


def _exists(rel_path: str) -> bool:
    return (ROOT / rel_path).exists()


def _git_value(args: list[str]) -> str | None:
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except Exception:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def _evidence_item(
    item_id: int,
    title: str,
    *,
    requirement: str,
    evidence_files: list[str],
    replay_commands: list[str],
    status: str,
    blockers: list[str] | None = None,
    limits: list[str] | None = None,
) -> dict[str, Any]:
    missing = [path for path in evidence_files if not _exists(path)]
    effective_blockers = list(blockers or [])
    if missing:
        effective_blockers.extend(f"missing_evidence_file:{path}" for path in missing)
    complete = not effective_blockers and not missing and status in {
        "accepted",
        "devnet_complete",
        "local_v0_complete",
    }
    return {
        "id": item_id,
        "title": title,
        "requirement": requirement,
        "status": "missing_evidence" if missing else status,
        "complete": bool(complete),
        "evidence_files": evidence_files,
        "missing_files": missing,
        "replay_commands": replay_commands,
        "blockers": effective_blockers,
        "limits": list(limits or []),
    }


def build_audit() -> dict[str, Any]:
    branch = _git_value(["rev-parse", "--abbrev-ref", "HEAD"])
    head = _git_value(["rev-parse", "HEAD"])
    upstream = _git_value(["rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{upstream}"])

    items = [
        _evidence_item(
            1,
            "Integration Branch",
            requirement="Merge Oracle work into one branch with devnet/docs and typed OracleAuthorization.",
            evidence_files=[
                "docs/ZENO_ORACLE_DEVNET_ALPHA.md",
                "docs/papers/zeno-oracle-whitepaper/main.pdf",
                "src/integration/zeno_oracle_authorization.py",
                "src/integration/zeno_oracle_settlement_authorization.py",
                "src/integration/zeno_oracle_trigger_authorization.py",
                "scripts/check_zeno_oracle_devnet_alpha.sh",
            ],
            replay_commands=[
                "git status -sb",
                "git log --oneline -1",
            ],
            status="accepted",
            limits=[
                "local audit cannot prove PR merge, reviewer approval, or remote branch protection",
            ],
        ),
        _evidence_item(
            2,
            "O3 Receipt Flow",
            requirement=(
                "Replay feed registry -> reporter lifecycle -> signed report -> admission -> "
                "aggregate -> accepted read -> action adapter -> terminal DAG replay."
            ),
            evidence_files=[
                "tools/zeno_oracle_o3_receipt_flow_replay.py",
                "tests/test_zeno_oracle_o3_receipt_flow_replay.py",
                "tools/check_zeno_oracle_production_network_config.py",
                "tests/test_check_zeno_oracle_production_network_config.py",
                "tools/zenodex_oracle_devnet_service.py",
                "tools/zenodex_oracle_devnet_disaster_harness.py",
            ],
            replay_commands=[
                "python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text",
                "pytest -q tests/test_zeno_oracle_o3_receipt_flow_replay.py",
                "python3 tools/check_zeno_oracle_production_network_config.py --format text",
                "pytest -q tests/test_check_zeno_oracle_production_network_config.py",
            ],
            status="devnet_complete",
            limits=[
                "production-candidate config gate validates local deployment/signing receipts, but live chain and public soak remain blockers",
                "does_not_claim_production_oracle_network_live",
            ],
        ),
        _evidence_item(
            3,
            "Critical Consumers",
            requirement="Wire zUSD, perps settlement/liquidation, routing/protected swap, triggers, and critical settlement.",
            evidence_files=[
                "tools/check_zeno_oracle_critical_action_map.py",
                "src/integration/zusd_api.py",
                "src/integration/perp_engine.py",
                "src/integration/dex_engine.py",
                "src/integration/zeno_oracle_routing_authorization.py",
                "src/integration/zeno_oracle_trigger_authorization.py",
                "tests/integration/test_perp_engine_oracle_authorization.py",
                "tests/integration/test_dex_engine_protected_swap_oracle_authorization.py",
                "tests/integration/test_dex_engine_critical_settlement_oracle_authorization.py",
                "tests/integration/test_zeno_oracle_trigger_authorization.py",
            ],
            replay_commands=[
                "python3 tools/check_zeno_oracle_critical_action_map.py",
                "bash scripts/check_zeno_oracle_devnet_alpha.sh",
            ],
            status="devnet_complete",
            limits=["runtime adapter flags are optional and must be enabled by deployment policy"],
        ),
        _evidence_item(
            4,
            "Reporter Economics",
            requirement="Make reporter bonds, rewards, disputes, slashing, withdrawals, and fee splits live.",
            evidence_files=[
                "tools/zenodex_oracle_reporter_economics_replay.py",
                "tests/test_zenodex_oracle_reporter_economics_replay.py",
                "tools/check_zeno_oracle_live_economics_policy.py",
                "tests/test_check_zeno_oracle_live_economics_policy.py",
            ],
            replay_commands=[
                "python3 tools/zenodex_oracle_reporter_economics_replay.py self-test",
                "python3 tools/check_zeno_oracle_live_economics_policy.py --format text",
                "pytest -q tests/test_check_zeno_oracle_live_economics_policy.py",
            ],
            status="partial",
            blockers=[
                "live_economics_policy_gate_is_production_candidate_only",
                "onchain_economics_receipts_not_replayed_against_live_chain_state",
                "escrow_funding_governance_and_settlement_execution_not_verified_onchain",
                "settlement_execution_receipt_not_verified_onchain",
            ],
            limits=[
                "local replay validates accounting transitions and local receipt bundles, including settlement-execution totals, only",
                "policy checker binds replay to production-candidate controls but does not prove live chain settlement",
            ],
        ),
        _evidence_item(
            5,
            "Disaster Corpus",
            requirement=(
                "Cover existing chaos plus source cartel, dispute griefing, registry drift, verifier spoofing, "
                "replay, and cross-module split-brain."
            ),
            evidence_files=[
                "tools/zenodex_oracle_devnet_disaster_harness.py",
                "tools/zeno_oracle_disaster_class_corpus.py",
                "tools/check_zeno_oracle_disaster_frontier.py",
                "tools/check_zeno_oracle_perps_snapshot_gate.py",
                "tools/check_zeno_oracle_cross_domain_finality_gate.py",
                "tools/check_zeno_oracle_reporter_soak_gate.py",
                "tools/check_cross_module_oracle_split_brain_v1.py",
                "tests/test_zeno_oracle_disaster_class_corpus.py",
                "tests/test_check_zeno_oracle_disaster_frontier.py",
                "tests/test_check_zeno_oracle_perps_snapshot_gate.py",
                "tests/test_check_zeno_oracle_cross_domain_finality_gate.py",
                "tests/test_check_zeno_oracle_reporter_soak_gate.py",
            ],
            replay_commands=[
                "python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text",
                "python3 tools/zeno_oracle_disaster_class_corpus.py --format text",
                "python3 tools/check_zeno_oracle_disaster_frontier.py --format text",
                "python3 tools/check_zeno_oracle_perps_snapshot_gate.py --format text",
                "python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text",
                "python3 tools/check_zeno_oracle_reporter_soak_gate.py --format text",
                "pytest -q tests/test_check_zeno_oracle_disaster_frontier.py",
            ],
            status="first_shell_complete",
            blockers=[
                "production_disaster_frontier_has_explicit_blockers",
                "cross_domain_finality_requires_live_adapter_receipts",
                "public_reporter_soak_and_live_governance_disaster_search_not_complete",
            ],
            limits=[
                "selected public corpus plus frontier catalog, not exhaustive production safety",
                "frontier checker requires explicit blockers for unclosed families but does not close them",
                "cross-domain finality gate validates local receipt bundles but not live finality adapter receipts",
                "reporter soak gate validates local observations but not public telemetry or legal independence",
            ],
        ),
        _evidence_item(
            6,
            "Obligation Antichain",
            requirement="Quotient equal disaster cases, remove dominated cases, and prove antichain coverage.",
            evidence_files=[
                "tools/check_disaster_obligation_certificate.py",
                "tools/zeno_oracle_disaster_obligation_certificate_manifest.json",
                "tools/check_zeno_oracle_frontier_obligation_projection.py",
                "tests/test_zeno_oracle_disaster_obligation_certificate.py",
                "tests/test_check_zeno_oracle_frontier_obligation_projection.py",
            ],
            replay_commands=[
                "python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json",
                "python3 tools/check_zeno_oracle_frontier_obligation_projection.py --format text",
            ],
            status="first_shell_complete",
            blockers=[
                "coverage_proof_is_manifest_checker_not_general_theorem",
                "antichain_projection_must_expand_with_new_frontier_axes",
            ],
        ),
        _evidence_item(
            7,
            "Math And Formal Lanes",
            requirement="Use Julia, Lean, ESSO, TLA, LTLf, Morph, and PopperPad for replayable evidence.",
            evidence_files=[
                "tools/zeno_oracle_math_witness_sweep.jl",
                "tests/test_zeno_oracle_math_witness_sweep.py",
                "lean-mathlib/Proofs/ZenoOracleMathWitness.lean",
                "formal/ltlf/oracle_recovery_ltlf_v1.yaml",
                "formal/ltlf/oracle_recovery_goal_family_v1.json",
                "formal/tla/OracleRecoveryLifecycle.tla",
                "src/kernels/dex/zusd_oracle_recovery_lifecycle_v1.yaml",
                "tools/zeno_oracle_workflow_evidence_status.py",
                "tools/zeno_oracle_smt_freshness_replay.py",
                "tools/popper_pad.py",
            ],
            replay_commands=[
                "python3 tools/zeno_oracle_workflow_evidence_status.py --format text",
                "python3 tools/zeno_oracle_smt_freshness_replay.py --format text",
                "julia tools/zeno_oracle_math_witness_sweep.jl",
                "pytest -q tests/test_zeno_oracle_math_witness_sweep.py",
                "cd lean-mathlib && lake env lean Proofs/ZenoOracleMathWitness.lean",
            ],
            status="partial",
            blockers=[
                "lean_theorems_are_first_witness_anchors_not_general_oracle_math",
                "julia_lane_is_bounded_witness_search",
                "morph_lane_is_public_smoke_not_exhaustive_campaign",
                "esso_tla_ltlf_lanes_are_first_shell_models",
            ],
        ),
        _evidence_item(
            8,
            "Claims Registry",
            requirement="Promote only public replayable claims into docs/claims_registry.yaml.",
            evidence_files=[
                "docs/claims_registry.yaml",
                "tools/check_claims_registry.py",
                "tests/test_claims_registry.py",
            ],
            replay_commands=[
                "python3 tools/check_claims_registry.py",
                "pytest -q tests/test_claims_registry.py",
            ],
            status="accepted",
        ),
        _evidence_item(
            9,
            "ZenoProof v0",
            requirement="Design proof artifact schema, verifier registry, claim DAG, verifier API, reward gate, and O4/O5 bridge.",
            evidence_files=[
                "docs/ZENOPROOF_V0_DESIGN.md",
                "tools/zenoproof_verify.py",
                "tools/zenoproof_registry_manifest.json",
                "tools/zenoproof_public_replay_verifier.py",
                "tools/zenoproof_reward_payout_replay.py",
                "tools/check_zenoproof_production_governance_policy.py",
                "tests/test_zenoproof_verify.py",
                "tests/test_zenoproof_reward_payout_replay.py",
                "tests/test_check_zenoproof_production_governance_policy.py",
            ],
            replay_commands=[
                "python3 tools/zenoproof_verify.py self-test --registry tools/zenoproof_registry_manifest.json",
                "python3 tools/zenoproof_reward_payout_replay.py --format text --registry tools/zenoproof_registry_manifest.json",
                "python3 tools/check_zenoproof_production_governance_policy.py --format text",
                "pytest -q tests/test_check_zenoproof_production_governance_policy.py",
            ],
            status="local_v0_complete",
            blockers=[
                "zenoproof_production_governance_policy_gate_is_candidate_only",
                "production_verifier_sandbox_and_code_signing_not_verified",
                "production_verifier_release_transparency_log_not_verified",
                "live_proof_network_and_payout_settlement_not_enabled",
            ],
            limits=[
                "local static verifier registry only",
                "production governance policy gate exists and binds verifier-release manifests locally, but rejects --require-live while blockers remain",
                "does_not_claim_live_proof_network",
                "does_not_claim_governance_revocation_live",
            ],
        ),
        _evidence_item(
            10,
            "Devnet Alpha Package",
            requirement="Ship devnet alpha package with docs, replay, CI gate, installer/binary path, and explicit non-claims.",
            evidence_files=[
                "scripts/package_zeno_oracle_rc.sh",
                "tools/check_zeno_oracle_rc_package.py",
                "scripts/check_zeno_oracle_devnet_alpha.sh",
                "scripts/check_zeno_oracle_rc_bundle.sh",
                "docs/ZENO_ORACLE_DEVNET_ALPHA.md",
                "docs/ZENO_ORACLE_CLI_V1.md",
                "docs/papers/zeno-oracle-whitepaper/main.pdf",
            ],
            replay_commands=[
                "bash scripts/package_zeno_oracle_rc.sh zeno-oracle-devnet-alpha-rc1",
                "python3 tools/check_zeno_oracle_rc_package.py --package-dir dist/zeno-oracle-devnet-alpha-rc1 --receipt dist/zeno-oracle-devnet-alpha-rc1.receipt.json --sig dist/zeno-oracle-devnet-alpha-rc1.sig",
                "cd dist/zeno-oracle-devnet-alpha-rc1 && bash scripts/check_zeno_oracle_rc_bundle.sh",
                "bash scripts/check_zeno_oracle_devnet_alpha.sh",
            ],
            status="devnet_complete",
            limits=[
                "does_not_claim_production_code_signing",
                "does_not_claim_platform_native_binary",
                "does_not_claim_onchain_feed_governance",
            ],
        ),
    ]

    incomplete = [item for item in items if not item["complete"]]
    production_blockers = [
        "production_oracle_network_not_live",
        "production_signing_and_code_signing_not_complete",
        "onchain_feed_governance_not_live",
        "live_reporter_economics_settlement_not_complete",
        "generalized_math_proofs_not_complete",
        "broader_disaster_search_not_complete",
        "zenoproof_production_verifier_governance_not_live",
    ]
    return {
        "schema": SCHEMA,
        "status": "complete" if not incomplete and not production_blockers else "blocked",
        "ok": not incomplete and not production_blockers,
        "goal_complete": not incomplete and not production_blockers,
        "objective": "production-candidate O3 ZenoOracle plus ZenoProof v0 design and disaster minimization",
        "branch": branch,
        "head": head,
        "upstream": upstream,
        "item_count": len(items),
        "complete_item_count": len(items) - len(incomplete),
        "incomplete_item_count": len(incomplete),
        "items": items,
        "production_blockers": production_blockers,
        "production_candidate_config_gate": {
            "command": "python3 tools/check_zeno_oracle_production_network_config.py --format text",
            "require_live_command": "python3 tools/check_zeno_oracle_production_network_config.py --require-live",
            "status": "production_candidate_receipt_replay_only",
        },
        "live_economics_policy_gate": {
            "command": "python3 tools/check_zeno_oracle_live_economics_policy.py --format text",
            "require_live_command": "python3 tools/check_zeno_oracle_live_economics_policy.py --require-live",
            "status": "production_candidate_only",
        },
        "disaster_frontier_gate": {
            "command": "python3 tools/check_zeno_oracle_disaster_frontier.py --format text",
            "require_closed_command": "python3 tools/check_zeno_oracle_disaster_frontier.py --require-closed",
            "status": "explicit_blocker_frontier",
        },
        "cross_domain_finality_gate": {
            "command": "python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --format text",
            "require_live_command": "python3 tools/check_zeno_oracle_cross_domain_finality_gate.py --require-live",
            "status": "production_candidate_receipt_replay_only",
        },
        "zenoproof_production_governance_gate": {
            "command": "python3 tools/check_zenoproof_production_governance_policy.py --format text",
            "require_live_command": "python3 tools/check_zenoproof_production_governance_policy.py --require-live",
            "status": "production_candidate_only",
        },
        "not_claimed": [
            "does_not_claim_goal_complete",
            "does_not_claim_production_oracle_truth",
            "does_not_claim_onchain_feed_governance_live",
            "does_not_claim_live_token_settlement",
            "does_not_claim_exhaustive_disaster_search",
            "does_not_claim_generalized_oracle_math_proofs",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument(
        "--expect-blocked",
        action="store_true",
        help="return success only when the audit is blocked/incomplete, matching the current expected state",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    audit = build_audit()
    if args.format == "json":
        print(json.dumps(audit, indent=2, sort_keys=True))
    else:
        print(f"status = {audit['status']}")
        print(f"goal_complete = {str(audit['goal_complete']).lower()}")
        print(f"complete_item_count = {audit['complete_item_count']}")
        print(f"incomplete_item_count = {audit['incomplete_item_count']}")
        print(f"production_blocker_count = {len(audit['production_blockers'])}")
    if args.expect_blocked:
        return 0 if audit["status"] == "blocked" and not audit["goal_complete"] else 1
    return 0 if audit["goal_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
