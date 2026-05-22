#!/usr/bin/env python3
"""Conservative completion audit for the active ZenoDEX next-goal backlog."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zeno_ledger_two_machine_evidence import (  # noqa: E402
    validate_two_machine_evidence_v0,
)

REPORT_SCHEMA = "zenodex.next_goal_backlog_completion_audit.v0"
_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")


@dataclass(frozen=True)
class RequirementSpec:
    requirement_id: str
    description: str
    artifacts: tuple[str, ...] = ()
    commands: tuple[tuple[str, ...], ...] = ()


@dataclass(frozen=True)
class ItemSpec:
    item_id: str
    title: str
    objective: str
    requirements: tuple[RequirementSpec, ...]
    residual_limits: tuple[str, ...] = ()


BACKLOG_ITEMS: tuple[ItemSpec, ...] = (
    ItemSpec(
        item_id="production_boundary_closure_final_audit",
        title="Production-boundary closure final audit",
        objective=(
            "Confirm value-moving paths use safe profiles, production has no nonce-free "
            "path, no legacy settlement validation, no require_settlement_match=false, "
            "and no exposed direct pure-core ingress."
        ),
        requirements=(
            RequirementSpec(
                "production_boundary_checker_accepts",
                "Run the production-boundary checker and tests.",
                artifacts=(
                    "tools/check_production_boundary.py",
                    "tests/test_check_production_boundary.py",
                    "docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md",
                ),
                commands=(
                    ("python3", "tools/check_production_boundary.py", "--json"),
                    ("pytest", "-q", "tests/test_check_production_boundary.py"),
                ),
            ),
        ),
        residual_limits=(
            "This local audit does not replace the fresh two-machine latest-main run.",
        ),
    ),
    ItemSpec(
        item_id="reproducibility_hash_locked_python",
        title="Reproducibility",
        objective=(
            "Verify Python --require-hashes lockfiles and supported install commands, "
            "while keeping proof metadata bound to Rust/RISC0/Lean/Docker/toolchain hashes."
        ),
        requirements=(
            RequirementSpec(
                "python_hash_locks_accept",
                "Run the Python hash-lock checker and tests.",
                artifacts=(
                    "tools/check_python_hash_locks.py",
                    "tests/test_check_python_hash_locks.py",
                    "docs/REPRODUCIBILITY_AUDIT.md",
                    "requirements-core.lock.txt",
                    "requirements-agents.lock.txt",
                    "requirements-dev.lock.txt",
                ),
                commands=(
                    ("python3", "tools/check_python_hash_locks.py", "--json"),
                    ("pytest", "-q", "tests/test_check_python_hash_locks.py"),
                ),
            ),
        ),
        residual_limits=(
            "This does not prove every external ecosystem dependency is reproducible.",
        ),
    ),
    ItemSpec(
        item_id="upba_v1_economic_sufficiency",
        title="UPBA v1 economic sufficiency",
        objective=(
            "Check the bounded-grid economic profiles, epsilon/economic bound, "
            "and production grid profile definitions."
        ),
        requirements=(
            RequirementSpec(
                "upba_v1_grid_profile_gate_accepts",
                "Run the UPBA v1 grid economic profile checker and tests.",
                artifacts=(
                    "tools/upba_v1_grid_economic_profile.py",
                    "tests/tools/test_upba_v1_grid_economic_profile.py",
                    "docs/UPBA_V1_GRID_ECONOMIC_PROFILES.md",
                    "docs/UPBA_V1_EVIDENCE_BOUNDARY.md",
                ),
                commands=(
                    ("python3", "tools/upba_v1_grid_economic_profile.py", "--json"),
                    ("pytest", "-q", "tests/tools/test_upba_v1_grid_economic_profile.py"),
                ),
            ),
        ),
        residual_limits=(
            "The profile gate is an economic-resolution argument over declared bounded profiles.",
        ),
    ),
    ItemSpec(
        item_id="upba_v2_optimality",
        title="UPBA v2 optimality",
        objective=(
            "Verify canonical partial-fill scoring, bounded-grid optimality roots, "
            "and omitted-candidate rejection tests for the scoped v2 model."
        ),
        requirements=(
            RequirementSpec(
                "upba_v2_uniform_batch_proofs_accept",
                "Run the UPBA v2/v3 Lean and Python certificate tests.",
                artifacts=(
                    "lean-mathlib/Proofs/UniformBatchOptimality.lean",
                    "tests/formal/test_lean_uniform_batch_optimality.py",
                    "tests/core/test_uniform_batch_optimality.py",
                    "tests/integration/test_dex_engine_uniform_batch_certificate.py",
                    "docs/UPBA_V2_CERTIFICATE.md",
                    "docs/UPBA_V2_EVIDENCE_BOUNDARY.md",
                ),
                commands=(
                    (
                        "bash",
                        "-lc",
                        "cd lean-mathlib && lake env lean Proofs/UniformBatchOptimality.lean",
                    ),
                    (
                        "pytest",
                        "-q",
                        "tests/core/test_uniform_batch_optimality.py",
                        "tests/integration/test_dex_engine_uniform_batch_certificate.py",
                        "tests/formal/test_lean_uniform_batch_optimality.py",
                    ),
                ),
            ),
        ),
        residual_limits=(
            "Public claims must stay scoped to bounded candidate-completeness evidence.",
        ),
    ),
    ItemSpec(
        item_id="upba_v3_exact_out",
        title="UPBA v3 exact-out",
        objective=(
            "Verify exact-out minimal input semantics, ceil/floor policy, "
            "overdelivery policy, fee_bps < 10000, and mixed exact-in/exact-out boundaries."
        ),
        requirements=(
            RequirementSpec(
                "upba_v3_exact_out_certificate_accepts",
                "Run the shared UPBA exact-out proof and runtime certificate tests.",
                artifacts=(
                    "docs/UPBA_V3_EXACT_OUT_CERTIFICATE.md",
                    "lean-mathlib/Proofs/UniformBatchOptimality.lean",
                    "tests/core/test_uniform_batch_optimality.py",
                    "tests/integration/test_dex_engine_uniform_batch_certificate.py",
                ),
                commands=(
                    (
                        "pytest",
                        "-q",
                        "tests/core/test_uniform_batch_optimality.py",
                        "tests/integration/test_dex_engine_uniform_batch_certificate.py",
                    ),
                ),
            ),
        ),
        residual_limits=(
            "The v3 evidence depends on the same scoped candidate-completeness boundary as v2.",
        ),
    ),
    ItemSpec(
        item_id="broader_zk",
        title="Broader ZK",
        objective=(
            "Track the spot block proof, light-client verifier, UPBA block proof, "
            "and later oracle/zUSD/perps/proof-market coverage."
        ),
        requirements=(
            RequirementSpec(
                "proof_coverage_matrix_accepts",
                "Run the proof coverage matrix checker.",
                artifacts=(
                    "tools/check_zeno_ledger_proof_coverage_matrix.py",
                    "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json",
                    "docs/ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.md",
                    "tests/tools/test_check_zeno_ledger_proof_coverage_matrix.py",
                ),
                commands=(
                    ("python3", "tools/check_zeno_ledger_proof_coverage_matrix.py", "--pretty"),
                    ("pytest", "-q", "tests/tools/test_check_zeno_ledger_proof_coverage_matrix.py"),
                ),
            ),
        ),
        residual_limits=(
            "Coverage-matrix acceptance is evidence of scoped proof coverage, not a full ZK roadmap closure.",
        ),
    ),
    ItemSpec(
        item_id="tee_privacy",
        title="TEE / privacy",
        objective=(
            "Check quote verification, measurement registry, freshness/revocation, "
            "and the attestation verifier path while keeping replay/ZK as correctness anchors."
        ),
        requirements=(
            RequirementSpec(
                "confidential_route_quote_bundle_accepts",
                "Run the confidential route-quote bundle checker tests.",
                artifacts=(
                    "tools/check_confidential_route_quote_bundle.py",
                    "tests/tools/test_check_confidential_route_quote_bundle.py",
                    "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
                ),
                commands=(
                    ("pytest", "-q", "tests/tools/test_check_confidential_route_quote_bundle.py"),
                ),
            ),
        ),
        residual_limits=(
            "These gates do not prove TEE hardware confidentiality or vendor attestation soundness.",
        ),
    ),
    ItemSpec(
        item_id="zeno_ledger_hardening",
        title="ZenoLedger hardening",
        objective=(
            "Check designated-writer rehearsal, validator scheduling, fork-choice, "
            "equivocation handling, and public operator hardening boundaries."
        ),
        requirements=(
            RequirementSpec(
                "zeno_ledger_public_testnet_artifacts_exist",
                "Confirm the ZenoLedger runbook and two-machine archive validators exist.",
                artifacts=(
                    "docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md",
                    "tools/check_zeno_ledger_two_machine_evidence.py",
                    "tools/build_zeno_ledger_two_machine_evidence.py",
                    "tools/build_zeno_ledger_node_evidence_input.py",
                    "tests/tools/test_check_zeno_ledger_two_machine_evidence.py",
                    "tests/tools/test_build_zeno_ledger_two_machine_evidence.py",
                    "tests/test_build_zeno_ledger_node_evidence_input.py",
                ),
                commands=(
                    (
                        "pytest",
                        "-q",
                        "tests/tools/test_check_zeno_ledger_two_machine_evidence.py",
                        "tests/tools/test_build_zeno_ledger_two_machine_evidence.py",
                        "tests/test_build_zeno_ledger_node_evidence_input.py",
                    ),
                ),
            ),
        ),
        residual_limits=(
            "Open P2P, adversarial production fork-choice, and live rotating validators remain outside v0.",
        ),
    ),
    ItemSpec(
        item_id="claims_readme_hygiene",
        title="Claims / README hygiene",
        objective=(
            "Keep public claims scoped for UPBA v2, RISC0, TEE, ZenoCover, and related surfaces."
        ),
        requirements=(
            RequirementSpec(
                "public_claim_scope_accepts",
                "Run the claims registry and public claim-scope gates.",
                artifacts=(
                    "tools/check_claims_registry.py",
                    "tools/check_public_claim_scope.py",
                    "tests/test_claims_registry.py",
                    "tests/test_check_public_claim_scope.py",
                    "docs/claims_registry.yaml",
                ),
                commands=(
                    ("python3", "tools/check_claims_registry.py"),
                    ("python3", "tools/check_public_claim_scope.py", "--json"),
                    (
                        "pytest",
                        "-q",
                        "tests/test_claims_registry.py",
                        "tests/test_check_public_claim_scope.py",
                    ),
                ),
            ),
        ),
    ),
    ItemSpec(
        item_id="tokenomics",
        title="Tokenomics",
        objective=(
            "Check the internal 1B ZENO candidate model, distribution, launch preconditions, "
            "vesting, value-capture, bonds, proof/oracle/operator incentives, and counsel gates."
        ),
        requirements=(
            RequirementSpec(
                "tokenomics_internal_gates_accept",
                "Run the internal tokenomics candidate, reward, games, burn-indexed unlock, and custody gates.",
                artifacts=(
                    "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json",
                    "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.md",
                    "internal/tokenomics/ZENO_DISTRIBUTION_AND_TREASURY_PLAN_V0.md",
                    "internal/tokenomics/ZENO_TOKENOMICS_REWARD_SAFETY_ENVELOPE_V0.json",
                    "internal/tokenomics/ZENO_ECONOMIC_GAMES_BOUNDARY_V0.json",
                    "internal/tokenomics/ZENO_BURN_INDEXED_UNLOCK_ACCELERATOR_V0.json",
                    "internal/tokenomics/ZENO_TREASURY_CUSTODY_BOUNDARY_V0.json",
                    "tools/check_tokenomics_candidate_model.py",
                    "tools/check_tokenomics_reward_safety_envelope.py",
                    "tools/check_zeno_economic_games_boundary.py",
                    "tools/check_burn_indexed_unlock_accelerator.py",
                    "tools/check_zeno_treasury_custody_boundary.py",
                ),
                commands=(
                    (
                        "pytest",
                        "-q",
                        "tests/tools/test_check_tokenomics_candidate_model.py",
                        "tests/tools/test_check_tokenomics_reward_safety_envelope.py",
                        "tests/tools/test_check_zeno_economic_games_boundary.py",
                        "tests/tools/test_check_burn_indexed_unlock_accelerator.py",
                        "tests/tools/test_check_zeno_treasury_custody_boundary.py",
                    ),
                ),
            ),
        ),
        residual_limits=(
            "Internal tokenomics gates are not counsel review or public launch clearance.",
        ),
    ),
    ItemSpec(
        item_id="zenocover",
        title="ZenoCover",
        objective=(
            "Check internal ZenoCover research/spec artifacts for reserve solvency, "
            "claim-verifier model, payout-cap proofs, attack queries, LP-loss cover, and regulatory boundaries."
        ),
        requirements=(
            RequirementSpec(
                "zenocover_internal_gates_accept",
                "Run the internal ZenoCover regulatory, claim, reserve, payout, attack, and LP-loss cover gates.",
                artifacts=(
                    "internal/zenocover/REGULATORY_BOUNDARY_MANIFEST_V0.json",
                    "internal/zenocover/ATTACK_QUERY_MANIFEST_V0.json",
                    "internal/zenocover/ZENOCOVER_LEGAL_REGULATORY_BOUNDARY_V0.md",
                    "internal/tokenomics/ZENOCOVER_CLAIM_VERIFIER_MODEL_V0.md",
                    "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
                    "tools/check_zenocover_regulatory_boundary.py",
                    "tools/check_zenocover_claim_verifier_model.py",
                    "tools/check_zenocover_reserve_solvency.py",
                    "tools/check_zenocover_reserve_withdrawal_safety.py",
                    "tools/check_zenocover_attack_queries.py",
                    "tools/check_zenocover_lp_loss_cover.py",
                    "tests/formal/test_lean_zenocover_payout_cap.py",
                ),
                commands=(
                    (
                        "pytest",
                        "-q",
                        "tests/tools/test_check_zenocover_regulatory_boundary.py",
                        "tests/tools/test_check_zenocover_claim_verifier_model.py",
                        "tests/tools/test_check_zenocover_reserve_solvency.py",
                        "tests/tools/test_check_zenocover_reserve_withdrawal_safety.py",
                        "tests/tools/test_check_zenocover_attack_queries.py",
                        "tests/tools/test_check_zenocover_lp_loss_cover.py",
                        "tests/formal/test_lean_zenocover_payout_cap.py",
                    ),
                ),
            ),
        ),
        residual_limits=(
            "Internal ZenoCover gates are not insurance-product launch clearance or legal advice.",
        ),
    ),
)


def run_completion_audit(
    *,
    latest_pushed_commit_sha: str | None,
    two_machine_evidence_path: Path | None,
    run_supporting_gates: bool,
) -> dict[str, Any]:
    items = [_fresh_two_machine_item(latest_pushed_commit_sha, two_machine_evidence_path)]
    items.extend(
        _supporting_item(item, run_supporting_gates=run_supporting_gates)
        for item in BACKLOG_ITEMS
    )
    missing = [
        f"{item['item_id']}.{requirement['requirement_id']}"
        for item in items
        for requirement in item["requirements"]
        if requirement["ok"] is not True
    ]
    return {
        "schema": REPORT_SCHEMA,
        "ok": not missing,
        "status": "accepted" if not missing else "rejected",
        "objective": "Full Next-Goal Backlog",
        "run_supporting_gates": run_supporting_gates,
        "latest_pushed_commit_sha": latest_pushed_commit_sha,
        "two_machine_evidence_path": (
            None if two_machine_evidence_path is None else str(two_machine_evidence_path)
        ),
        "item_count": len(items),
        "accepted_item_count": sum(1 for item in items if item["ok"] is True),
        "items": items,
        "missing_requirements": missing,
    }


def _fresh_two_machine_item(
    latest_pushed_commit_sha: str | None,
    evidence_path: Path | None,
) -> dict[str, Any]:
    requirements: list[dict[str, Any]] = []

    latest_commit_ok = (
        isinstance(latest_pushed_commit_sha, str)
        and _COMMIT_RE.fullmatch(latest_pushed_commit_sha) is not None
    )
    requirements.append(
        {
            "requirement_id": "latest_pushed_commit_sha_supplied",
            "description": "The latest pushed commit SHA is supplied as lowercase 40-hex.",
            "ok": latest_commit_ok,
            "status": "accepted" if latest_commit_ok else "missing_or_invalid",
            "evidence": latest_pushed_commit_sha,
        }
    )

    evidence_present = evidence_path is not None and evidence_path.is_file()
    requirements.append(
        {
            "requirement_id": "two_machine_evidence_archive_present",
            "description": "A machine-readable two-machine latest-main evidence archive is supplied.",
            "ok": evidence_present,
            "status": "accepted" if evidence_present else "missing",
            "evidence": None if evidence_path is None else str(evidence_path),
        }
    )

    validation_report: dict[str, Any] | None = None
    validation_ok = False
    validation_status = "not_run"
    validation_errors: list[str] = []
    required_fields: Mapping[str, Any] = {}
    if evidence_present:
        try:
            raw = json.loads(evidence_path.read_text(encoding="utf-8"))
            validation_report = validate_two_machine_evidence_v0(
                raw,
                expected_commit=latest_pushed_commit_sha if latest_commit_ok else None,
            )
            required_fields = validation_report.get("required_evidence_fields", {})
            missing_fields = [
                key
                for key, value in required_fields.items()
                if value is not True
            ]
            validation_errors = list(validation_report.get("errors", []))
            if missing_fields:
                validation_errors.append(
                    "required_evidence_fields false: " + ",".join(sorted(missing_fields))
                )
            validation_ok = validation_report.get("ok") is True and not missing_fields
            validation_status = "accepted" if validation_ok else "rejected"
        except Exception as exc:  # pragma: no cover - defensive CLI path
            validation_errors = [str(exc)]
            validation_status = "rejected"
    requirements.append(
        {
            "requirement_id": "two_machine_evidence_archive_validates",
            "description": (
                "The archive validates commit SHA, Python versions, network-config hash, "
                "feature-suite hash, common header hash, accepted/rejected tx counts, "
                "token-test result, watcher attestations, and machine watcher coverage."
            ),
            "ok": validation_ok,
            "status": validation_status,
            "required_evidence_fields": dict(required_fields),
            "errors": validation_errors,
        }
    )
    return {
        "item_id": "fresh_two_machine_latest_main_run",
        "title": "Fresh two-machine latest-main run",
        "objective": (
            "Machine A and Machine B run the latest pushed commit and archive the explicit "
            "machine-readable evidence fields."
        ),
        "ok": all(req["ok"] is True for req in requirements),
        "status": "accepted" if all(req["ok"] is True for req in requirements) else "rejected",
        "requirements": requirements,
        "validation_report": validation_report,
        "residual_limits": [] if validation_ok else ["Real two-host latest-main evidence is still required."],
    }


def _supporting_item(
    spec: ItemSpec,
    *,
    run_supporting_gates: bool,
) -> dict[str, Any]:
    requirements = [
        _supporting_requirement(req, run_supporting_gates=run_supporting_gates)
        for req in spec.requirements
    ]
    ok = all(req["ok"] is True for req in requirements)
    return {
        "item_id": spec.item_id,
        "title": spec.title,
        "objective": spec.objective,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "requirements": requirements,
        "residual_limits": list(spec.residual_limits),
    }


def _supporting_requirement(
    spec: RequirementSpec,
    *,
    run_supporting_gates: bool,
) -> dict[str, Any]:
    artifact_reports = [
        {
            "path": path,
            "ok": (ROOT / path).exists(),
        }
        for path in spec.artifacts
    ]
    commands = [
        _run_command(command) if run_supporting_gates else _not_run_command(command)
        for command in spec.commands
    ]
    ok = all(item["ok"] for item in artifact_reports) and all(
        item["ok"] for item in commands
    )
    return {
        "requirement_id": spec.requirement_id,
        "description": spec.description,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "artifacts": artifact_reports,
        "commands": commands,
    }


def _not_run_command(command: tuple[str, ...]) -> dict[str, Any]:
    return {
        "argv": list(command),
        "ok": False,
        "status": "not_run",
        "returncode": None,
        "stdout_tail": "",
        "stderr_tail": "",
    }


def _run_command(command: tuple[str, ...]) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            list(command),
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=900,
        )
        return {
            "argv": list(command),
            "ok": proc.returncode == 0,
            "status": "accepted" if proc.returncode == 0 else "rejected",
            "returncode": proc.returncode,
            "stdout_tail": _tail(proc.stdout),
            "stderr_tail": _tail(proc.stderr),
        }
    except Exception as exc:  # pragma: no cover - defensive CLI path
        return {
            "argv": list(command),
            "ok": False,
            "status": "error",
            "returncode": None,
            "stdout_tail": "",
            "stderr_tail": str(exc),
        }


def _tail(text: str, *, limit: int = 4000) -> str:
    return text[-limit:] if len(text) > limit else text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--latest-pushed-commit-sha")
    parser.add_argument("--two-machine-evidence", type=Path)
    parser.add_argument(
        "--run-supporting-gates",
        action="store_true",
        help="Run local supporting commands instead of only listing them.",
    )
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = run_completion_audit(
        latest_pushed_commit_sha=args.latest_pushed_commit_sha,
        two_machine_evidence_path=args.two_machine_evidence,
        run_supporting_gates=args.run_supporting_gates,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
