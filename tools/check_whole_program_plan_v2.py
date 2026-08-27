#!/usr/bin/env python3
"""Fail closed when the whole-program plan candidate loses scope or semantics."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PLAN = Path("docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json")
CAPABILITY_MANIFEST = Path("docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json")
SAFETY_CLAIM = Path("docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md")
COMPLETENESS_REVIEW = Path(
    "docs/research/m6_global_economic_core_luna_completeness_review_v1.json"
)
SCHEMA = "zenodex/whole-program-plan/v2.1"
EXPECTED_VM_GATES = tuple(f"VM-{index:02d}" for index in range(1, 13))
EXPECTED_OBLIGATIONS = (
    "O-001",
    "O-003A",
    "O-002",
    "O-003B",
    "O-004",
    "O-005",
    "O-005B",
    "O-006",
    "O-007A",
    "O-007B",
    "O-007C",
    "O-008A",
    "O-008",
    "O-009",
    "O-010A",
    "O-010B",
)
EXPECTED_POLICIES = tuple(f"UP-{index:02d}" for index in range(1, 21))
EXPECTED_EXPANSIONS = tuple(f"RSE-{index:03d}" for index in range(1, 12))
EXPECTED_FINDINGS = tuple(f"CE-{index:03d}" for index in range(1, 9))
EXPECTED_FINDING_STATUSES = (
    "OPEN_BLOCKER",
    "OPEN_BLOCKER",
    "OPEN_BLOCKER",
    "REPAIRED_IN_BOUNDED_MODEL",
    "REPAIRED_IN_BOUNDED_MODEL",
    "OPEN_PRODUCT_AND_THEOREM_DECISION",
    "OPEN_BLOCKER",
    "OPEN_BLOCKER",
)
REQUIRED_RELEASE_STATUSES = (
    "SPECIFIED",
    "IMPLEMENTED",
    "PROVED",
    "MOUNTED",
    "TESTED",
    "TERMINAL_COMPLETE",
    "MIGRATABLE",
    "NO_BYPASS",
    "RELEASE_BACKED",
)
EXPECTED_CAPABILITY_MANIFEST_SHA256 = (
    "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95"
)
EXPECTED_RELEASE_GATE = {
    "required_capability_statuses": list(REQUIRED_RELEASE_STATUSES),
    "excluded_capability_status": "DISABLED_PROVED_NO_WRITER",
    "whole_value_movement_claim": (
        "FORBIDDEN_UNTIL_ALL_12_VM_GATES_PASS_ON_ONE_EXACT_RELEASE_SUBJECT"
    ),
}
EXPECTED_TAU_COMMIT = "0b038824c8583a1a902ef54369d3d0ecf3384cf5"
EXPECTED_TAU_TREE = "445d77a77b451a0babe5b25c2d66bc45ee20ef29"
EXPECTED_TAU_SOURCE_SHA256 = {
    "README.md": "5897a1b965096bbb606e0030da84f6beca050518e99428865c95a09f4d34414c",
    "api_response.py": "1dad7240f3116e6d309856753ff8e4bcce327772c87206d8e2b0c48bc5912b4a",
    "app/container.py": "3a368099b28a23dbac76bee4f4149b1d72b67708d9c9b78dbb725dafff9d708a",
    "commands/gettxstatus.py": "f293977bc334540228cf7f27f9af49902a96436beee58e97661086ba501ae844",
    "commands/sendtx.py": "82a4805e039fa644b099928dc19a600cc1f9d8753580c7b3a6d2a3a09c7248cf",
    "consensus/admission.py": "cf2e11165a17de3191f73739afaa725693b6ff2fb4df8e36c6e3de2cb486516b",
    "server.py": "22cb9ed07749d08bc1b275ad5518c9545eef7da0ce61696741227c00abb22bfb",
    "tau_defs.py": "853d55e054116a13af7854b81789da1dbcbfc27a6a60cd78308dd54cc7b7e5ad",
}
EXPECTED_TAU_LANG_COMMIT = "1195b4a629250d284ac33789021263dd0395cfb3"
EXPECTED_TAU_LANG_TREE = "3d2ee089856c98d29bea3da1c9152dba298485d3"
EXPECTED_TAU_LANG_SOURCE_SHA256 = {
    "README.md": "cd6d6377d49b01bfb1a7bec458bb20f1d943431007edbf902dbf64ef8f9d7137",
    "src/main.cpp": "f9a9bc2ba7b3d12dab00d2161c6577579a57102a93ea692a63926316029c84dc",
}
EXPECTED_COMPLETENESS_REVIEW_SHA256 = (
    "b3a1929422b6399a3c30fb1ead4c7732a8802d08b1d4b59e6fc3ea79463b4698"
)
EXPECTED_DONOR_COMMITS = {
    "57351387ef7f0ad09e0a759baf8826f72d880c66",
    "2085533fefd82d57fbd79049bff618dd9cf484db",
    "ae889ac45429b9211666e6bc4158e89b7523cd2d",
}
EXPECTED_ADMISSION_MODEL = {
    "human_selection": "EXTERNAL_USER_DIRECTIVE_REQUIRED_NOT_MACHINE_VERIFIED",
    "llm_review": "ADVISORY_HASHED_ARTIFACT_ONLY",
    "deterministic_evidence": "REPLAYED_BY_ADMISSION_CHECKER",
    "authority_effect": "NONE",
}
EXPECTED_ADVISORY_REVIEWS = [
    {
        "reviewer": "FABLE_5_HIGH",
        "artifact_path": (
            "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2_1_FABLE_ADVISORY_REVIEW.md"
        ),
        "external_raw_report_sha256": (
            "6093fbaa06371bcf36d88825863055e9b35a5b1de583418ee70f62bcb58435fa"
        ),
        "verdict": "REVISE_V2_CORRECTIONS_APPLIED_TO_V2_1",
        "authority": "ADVISORY_NONE",
    }
]
EXPECTED_NORMATIVE_ROLES = (
    "Provisional closed-name registry and requirements floor: 12 lanes, 103 "
    "capabilities, four required cross-lane routes, explicit exclusions, and "
    "incomplete requirements closure.",
    "Conjunctive claim target and semantic nonclaims.",
    "Eight-decimal integer-atom policy.",
)
EXPECTED_VM_GATE_PROMOTION = {
    "rule": (
        "No individual obligation may close a VM gate. Aggregate deterministic "
        "gate checkers promote a VM gate only after every conjunct in the formal "
        "safety claim passes on one exact subject."
    ),
    "individual_obligation_maximum": "CONTRIBUTES_TO",
}
EXPECTED_COMPLETENESS_ESTIMATION_POLICY = {
    "observed_closure_metric": (
        "Count exact-subject promoted evidence cells over the manifest-derived minimum. "
        "Report the numerator and denominator; do not use it as a product maturity score."
    ),
    "scope_discovery_metric": (
        "Use overlap among preregistered independent top-down, bottom-up, and "
        "adversarial discovery campaigns as diagnostic capture-recapture input only."
    ),
    "numeric_discovery_preconditions": [
        "one shared canonical obligation identity",
        "independent campaign role packets and source sets",
        "complete positive and negative finding inventories",
        "comparable bounded semantic domain",
        "recorded overlap and newly discovered obligation counts",
    ],
    "gap_record_required_fields": [
        "obligation_id",
        "semantic_axes",
        "severity",
        "reachability",
        "minimized_counterexample_or_discovery_contract",
        "closure_layer",
        "evidence_lane",
        "exact_subject",
        "owner",
        "claim_ceiling",
    ],
    "production_rule": (
        "A numerical estimate never promotes a value-movement gate. Exact closure evidence "
        "for every required cell and all aggregate VM-gate conjuncts remains mandatory."
    ),
}
EXPECTED_TAU_INTEGRATION_RULE = (
    "Treat legacy Python bridge execution as a historical research oracle. Current "
    "Tau ingress is shadow or testnet observation only. It may observe tentatively "
    "ordered Tau transactions, but it cannot authenticate a domain-bound "
    "EconomicCommandOccurrenceV1, establish final ZenoDEX ordering, publish "
    "ZenoLedger state, or satisfy external finality."
)
EXPECTED_TAU_LANG_INTEGRATION_RULE = (
    "Tau Language may evaluate release-selected policy predicates only through a "
    "versioned adapter. A Tau verdict grants no settlement, publication, verifier, "
    "migration, or release authority."
)
EXPECTED_TAU_ROLE = (
    "Current Tau may authenticate and tentatively order Tau transactions and may "
    "evaluate governed policy predicates. A versioned adapter must separately "
    "authenticate a domain-bound EconomicCommandOccurrenceV1. ZenoLedger ordering "
    "and publication remain authoritative."
)
EXPECTED_TAU_INGRESS = (
    "A Tau-originated signed observation or policy verdict enters a versioned "
    "shadow/testnet adapter. Separate Zeno-domain authentication is required before "
    "it may become an EconomicCommandOccurrenceV1."
)
EXPECTED_TAU_REORG_PROPERTY = (
    "classify pre-finality observations removed by reorganization as ORPHANED "
    "with no irreversible settlement"
)
EXPECTED_PROOF_SHAPE = {
    "module_receipts_per_route_min": 1,
    "module_receipts_per_route_max": 8,
    "commands_per_epoch_min": 1,
    "commands_per_epoch_max": 64,
    "module_leaf_occurrences_per_epoch_max": 64,
    "aggregation_fanout": 8,
    "command_aggregation_levels_max": 2,
    "required_rejections": [
        "zero_route_receipts",
        "nine_route_receipts",
        "zero_epoch_commands",
        "sixty_five_epoch_commands",
        "journal_byte_excess",
        "cycle_budget_excess",
    ],
}
FORBIDDEN_PLAN_TEXT = (
    "/tmp/",
    "/home/",
    "M6PromotionSubjectV2",
    "GlobalCommandV2",
    "GlobalEconomicStateV2",
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
_VM_GATE_ROW_RE = re.compile(r"^\| (VM-[0-9]{2}) \| ([^|]+?) \|", re.MULTILINE)


def _without_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _load_object_bytes(data: bytes, source_name: str) -> Mapping[str, object]:
    value = json.loads(
        data.decode("utf-8"),
        object_pairs_hook=_without_duplicate_keys,
    )
    if type(value) is not dict:
        raise TypeError(f"{source_name} root must be an object")
    return value


def _exact_ids(rows: object, field: str) -> tuple[object, ...]:
    if type(rows) is not list or any(type(row) is not dict for row in rows):
        return ()
    return tuple(row.get(field) for row in rows)


def _manifest_scope_counts(
    capability_manifest: Mapping[str, object],
    findings: list[str],
) -> tuple[int, int, int, int, int]:
    capability_keys: list[tuple[str, str]] = []
    lane_ids: list[str] = []
    lanes = capability_manifest.get("lanes")
    if type(lanes) is not list or not lanes:
        findings.append("capability manifest lanes must be a nonempty list")
    else:
        for lane in lanes:
            if type(lane) is not dict:
                findings.append("capability manifest lane rows must be objects")
                continue
            lane_id = lane.get("lane_id")
            capabilities = lane.get("capabilities")
            if type(lane_id) is not str or not lane_id:
                findings.append("capability manifest lane id must be a nonempty string")
                continue
            lane_ids.append(lane_id)
            if (
                type(capabilities) is not list
                or not capabilities
                or any(type(value) is not str or not value for value in capabilities)
                or len(capabilities) != len(set(capabilities))
            ):
                findings.append(f"capability manifest lane is not closed and unique: {lane_id}")
                continue
            capability_keys.extend((lane_id, value) for value in capabilities)
    if len(lane_ids) != len(set(lane_ids)):
        findings.append("capability manifest lane ids must be unique")

    routes = capability_manifest.get("required_cross_lane_routes")
    route_ids = routes if type(routes) is list else []
    if (
        not route_ids
        or any(type(value) is not str or not value for value in route_ids)
        or len(route_ids) != len(set(route_ids))
    ):
        findings.append("required cross-lane routes must be nonempty and unique")

    exclusions = capability_manifest.get("explicit_exclusions")
    exclusion_rows_valid = type(exclusions) is list and all(
        type(row) is dict for row in exclusions
    )
    exclusion_ids = _exact_ids(exclusions, "capability")
    if (
        not exclusion_rows_valid
        or not exclusions
        or any(type(value) is not str or not value for value in exclusion_ids)
        or len(exclusion_ids) != len(set(exclusion_ids))
    ):
        findings.append("explicit exclusions must be nonempty and unique")

    lane_count = len(lane_ids)
    capability_count = len(capability_keys)
    route_count = len(route_ids)
    exclusion_count = len(exclusion_ids)
    evidence_cell_count = (
        (capability_count + route_count) * len(REQUIRED_RELEASE_STATUSES)
        + exclusion_count
    )
    return lane_count, capability_count, route_count, exclusion_count, evidence_cell_count


def _claim_vm_gate_pairs(source: str) -> tuple[tuple[str, str], ...]:
    return tuple((gate_id, title.strip()) for gate_id, title in _VM_GATE_ROW_RE.findall(source))


def _safe_repo_path(root: Path, raw: object) -> Path | None:
    if type(raw) is not str or not raw or Path(raw).is_absolute() or ".." in Path(raw).parts:
        return None
    candidate = (root / raw).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError:
        return None
    return candidate


def _git_tree_for_commit(root: Path, commit: str) -> str | None:
    env = {
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "PATH": os.environ.get("PATH", ""),
    }
    try:
        completed = subprocess.run(
            [
                "git",
                "-c",
                "core.hooksPath=/dev/null",
                "-C",
                str(root),
                "rev-parse",
                "--verify",
                f"{commit}^{{tree}}",
            ],
            check=False,
            capture_output=True,
            env=env,
            text=True,
            timeout=5,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if completed.returncode != 0:
        return None
    tree = completed.stdout.strip()
    return tree if _COMMIT_RE.fullmatch(tree) else None


def check_whole_program_plan_v2(
    root: Path = REPO_ROOT,
    plan_path: Path | None = None,
) -> dict[str, object]:
    findings: list[str] = []
    source = plan_path or root / DEFAULT_PLAN
    capability_manifest_path = root / CAPABILITY_MANIFEST
    completeness_review_path = root / COMPLETENESS_REVIEW
    safety_claim_path = root / SAFETY_CLAIM
    try:
        plan_bytes = source.read_bytes()
        capability_manifest_bytes = capability_manifest_path.read_bytes()
        completeness_review_bytes = completeness_review_path.read_bytes()
        safety_claim_bytes = safety_claim_path.read_bytes()
        plan = _load_object_bytes(plan_bytes, source.name)
        capability_manifest = _load_object_bytes(
            capability_manifest_bytes,
            capability_manifest_path.name,
        )
        completeness_review = _load_object_bytes(
            completeness_review_bytes,
            completeness_review_path.name,
        )
        safety_claim_text = safety_claim_bytes.decode("utf-8")
    except (
        OSError,
        TypeError,
        ValueError,
        UnicodeDecodeError,
        json.JSONDecodeError,
    ) as exc:
        return {
            "schema": "zenodex/whole-program-plan-check/v2.1",
            "ok": False,
            "production_authority": "NONE",
            "findings": [f"plan inputs cannot be loaded: {type(exc).__name__}: {exc}"],
        }

    if plan.get("schema") != SCHEMA:
        findings.append("whole-program plan schema mismatch")
    if plan.get("status") != "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION":
        findings.append("plan must remain a candidate until external admission")
    if plan.get("admission_model") != EXPECTED_ADMISSION_MODEL:
        findings.append("research-plan admission model drift")
    advisory_reviews = plan.get("advisory_reviews")
    if advisory_reviews != EXPECTED_ADVISORY_REVIEWS:
        findings.append("advisory planning-review binding drift")
    else:
        review_path = _safe_repo_path(root, advisory_reviews[0].get("artifact_path"))
        if review_path is None or not review_path.is_file():
            findings.append("advisory planning-review artifact unavailable")

    authority = plan.get("authority")
    expected_authority = {
        "production_authority": "NONE",
        "settlement_authority": "NONE",
        "release_ready": False,
        "production_ready": False,
    }
    if authority != expected_authority:
        findings.append("authority ceiling drift")

    subject = plan.get("subject")
    subject_tree_verified = False
    if type(subject) is not dict:
        findings.append("subject must be an object")
    else:
        base_commit = subject.get("implementation_base_commit")
        base_tree = subject.get("implementation_base_tree")
        if type(base_commit) is not str or not _COMMIT_RE.fullmatch(base_commit):
            findings.append("implementation base commit must be exact lowercase SHA-1")
        if type(base_tree) is not str or not _COMMIT_RE.fullmatch(base_tree):
            findings.append("implementation base tree must be exact lowercase SHA-1")
        if type(base_commit) is str and _COMMIT_RE.fullmatch(base_commit):
            observed_tree = _git_tree_for_commit(root, base_commit)
            if observed_tree is None or observed_tree != base_tree:
                findings.append("implementation base commit and tree do not match Git objects")
            else:
                subject_tree_verified = True
        binding = subject.get("plan_commit_binding")
        if type(binding) is not str or "self-referential" not in binding:
            findings.append("plan must state its non-self-referential commit binding")

    normative_inputs = plan.get("normative_inputs")
    expected_normative_paths = (
        "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json",
        "docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md",
        "docs/research/ZENODEX_M6_ASSET_PRECISION_POLICY_V1.json",
    )
    if _exact_ids(normative_inputs, "path") != expected_normative_paths:
        findings.append("normative input set or order drift")
    if _exact_ids(normative_inputs, "role") != EXPECTED_NORMATIVE_ROLES:
        findings.append("normative input role or scope semantics drift")
    if type(normative_inputs) is list:
        cached_input_bytes = {
            CAPABILITY_MANIFEST: capability_manifest_bytes,
            SAFETY_CLAIM: safety_claim_bytes,
        }
        for row in normative_inputs:
            if type(row) is not dict:
                continue
            path = _safe_repo_path(root, row.get("path"))
            expected_hash = row.get("sha256")
            if path is None or type(expected_hash) is not str or not _SHA256_RE.fullmatch(expected_hash):
                findings.append("normative input path or SHA-256 is invalid")
                continue
            try:
                relative_path = path.relative_to(root)
                input_bytes = cached_input_bytes.get(relative_path)
                if input_bytes is None:
                    input_bytes = path.read_bytes()
                actual_hash = hashlib.sha256(input_bytes).hexdigest()
            except OSError as exc:
                findings.append(f"normative input unreadable: {path.name}: {type(exc).__name__}")
                continue
            if actual_hash != expected_hash:
                findings.append(f"normative input hash drift: {path.relative_to(root)}")

    review_hash = hashlib.sha256(completeness_review_bytes).hexdigest()
    capability_manifest_sha256 = hashlib.sha256(capability_manifest_bytes).hexdigest()
    if capability_manifest_sha256 != EXPECTED_CAPABILITY_MANIFEST_SHA256:
        findings.append("exact capability manifest source drift")
    review_expansions = _exact_ids(completeness_review.get("required_spec_expansions"), "id")
    review_findings = completeness_review.get("confirmed_findings")
    review_finding_ids = _exact_ids(review_findings, "id")
    review_finding_statuses = _exact_ids(review_findings, "status")
    if review_hash != EXPECTED_COMPLETENESS_REVIEW_SHA256:
        findings.append("completeness-review source hash drift")
    if review_expansions != EXPECTED_EXPANSIONS:
        findings.append("required-expansion source set or order drift")
    if (
        review_finding_ids != EXPECTED_FINDINGS
        or review_finding_statuses != EXPECTED_FINDING_STATUSES
    ):
        findings.append("confirmed-finding source set, order, or status drift")

    requirements_floor = plan.get("requirements_floor")
    expected_requirements_floor = {
        "classification": "PROVISIONAL_CLOSED_NAME_REGISTRY_REQUIREMENTS_INCOMPLETE",
        "manifest_complete": False,
        "workflow_count": 18,
        "scenario_count": 81,
        "required_expansion_count": 11,
        "required_expansion_ids": list(EXPECTED_EXPANSIONS),
        "confirmed_finding_count": 8,
        "confirmed_findings": [
            {"finding_id": finding_id, "status": status}
            for finding_id, status in zip(
                EXPECTED_FINDINGS,
                EXPECTED_FINDING_STATUSES,
                strict=True,
            )
        ],
        "completeness_review": {
            "path": str(COMPLETENESS_REVIEW),
            "sha256": EXPECTED_COMPLETENESS_REVIEW_SHA256,
            "authority": "ADVISORY_FINDING_SOURCE_REQUIRES_LOCAL_CLOSURE_EVIDENCE",
        },
        "unresolved_policy_count": 20,
        "closure_rule": (
            "Map every workflow, scenario, required expansion, confirmed finding, and "
            "unresolved policy into versioned requirement rows before VM-01 or scope "
            "completeness may pass."
        ),
    }
    if requirements_floor != expected_requirements_floor:
        findings.append("provisional requirements-floor semantics drift")
    if capability_manifest.get("manifest_complete") is not False:
        findings.append("capability manifest must remain explicitly incomplete")
    expected_history = {
        "workflow_count": 18,
        "scenario_count": 81,
        "required_spec_expansion_count": 11,
        "status": "REQUIRED_BUT_NOT_CAPABILITY_COMPLETE",
    }
    if capability_manifest.get("historical_requirements") != expected_history:
        findings.append("capability manifest historical requirements drift")

    architecture = plan.get("selected_architecture")
    if type(architecture) is not dict:
        findings.append("selected architecture must be an object")
    else:
        if architecture.get("settlement_abi") != "GlobalSettlementABI V1":
            findings.append("GlobalSettlementABI V1 selection drift")
        manifest_lanes = capability_manifest.get("lanes")
        expected_lanes = _exact_ids(manifest_lanes, "lane_id")
        observed_lanes = architecture.get("closed_lane_registry")
        if type(observed_lanes) is not list or tuple(observed_lanes) != expected_lanes:
            findings.append("closed lane registry does not match the capability manifest")
        if architecture.get("initial_recursive_qualification") != EXPECTED_PROOF_SHAPE:
            findings.append("initial recursive qualification shape drift")

    historical_inputs = plan.get("historical_inputs")
    donor_commits = {
        commit
        for commit in _exact_ids(historical_inputs, "source_commit")
        if type(commit) is str and commit in EXPECTED_DONOR_COMMITS
    }
    if donor_commits != EXPECTED_DONOR_COMMITS:
        findings.append("whole-program donor reconciliation set drift")
    for donor_commit in donor_commits:
        if _git_tree_for_commit(root, donor_commit) is None:
            findings.append(f"whole-program donor commit unavailable: {donor_commit}")

    upstream = plan.get("upstream_dependencies")
    if (
        type(upstream) is not list
        or len(upstream) != 2
        or type(upstream[0]) is not dict
        or type(upstream[1]) is not dict
    ):
        findings.append("current Tau dependency pins must contain tau-testnet and tau-lang")
    else:
        if upstream[0].get("observed_commit") != EXPECTED_TAU_COMMIT:
            findings.append("current Tau dependency commit drift")
        if upstream[0].get("observed_tree") != EXPECTED_TAU_TREE:
            findings.append("current Tau dependency tree drift")
        if upstream[0].get("source_sha256") != EXPECTED_TAU_SOURCE_SHA256:
            findings.append("current Tau source-hash set drift")
        if upstream[0].get("integration_rule") != EXPECTED_TAU_INTEGRATION_RULE:
            findings.append("current Tau authority-boundary wording drift")
        if upstream[1].get("observed_commit") != EXPECTED_TAU_LANG_COMMIT:
            findings.append("current Tau Language dependency commit drift")
        if upstream[1].get("observed_tree") != EXPECTED_TAU_LANG_TREE:
            findings.append("current Tau Language dependency tree drift")
        if upstream[1].get("source_sha256") != EXPECTED_TAU_LANG_SOURCE_SHA256:
            findings.append("current Tau Language source-hash set drift")
        if upstream[1].get("integration_rule") != EXPECTED_TAU_LANG_INTEGRATION_RULE:
            findings.append("current Tau Language authority-boundary wording drift")

    semantic_anchors = plan.get("semantic_anchors")
    if type(semantic_anchors) is not dict or semantic_anchors.get("tau_role") != EXPECTED_TAU_ROLE:
        findings.append("current Tau semantic role drift")
    tau_contract = plan.get("current_tau_integration_contract")
    if type(tau_contract) is not dict:
        findings.append("current Tau integration contract must be an object")
    else:
        if tau_contract.get("ingress") != EXPECTED_TAU_INGRESS:
            findings.append("current Tau ingress authentication boundary drift")
        properties = tau_contract.get("required_adapter_properties")
        if type(properties) is not list or EXPECTED_TAU_REORG_PROPERTY not in properties:
            findings.append("current Tau reorganization semantics drift")

    value_movement_gates = plan.get("value_movement_gates")
    if _exact_ids(value_movement_gates, "gate_id") != EXPECTED_VM_GATES:
        findings.append("value-movement gate set or order drift")
    claim_gate_pairs = _claim_vm_gate_pairs(safety_claim_text)
    plan_gate_pairs = tuple(
        (row.get("gate_id"), row.get("title"))
        for row in value_movement_gates
        if type(row) is dict
    ) if type(value_movement_gates) is list else ()
    if claim_gate_pairs != plan_gate_pairs:
        findings.append("value-movement gate titles drift from the normative safety claim")
    if plan.get("vm_gate_promotion") != EXPECTED_VM_GATE_PROMOTION:
        findings.append("aggregate VM-gate promotion rule drift")
    if plan.get("completeness_estimation_policy") != EXPECTED_COMPLETENESS_ESTIMATION_POLICY:
        findings.append("semantic completeness estimation policy drift")
    if plan.get("release_gate") != EXPECTED_RELEASE_GATE:
        findings.append("whole-program release gate contract drift")
    obligations = plan.get("next_obligations")
    if _exact_ids(obligations, "obligation_id") != EXPECTED_OBLIGATIONS:
        findings.append("next-obligation set or order drift")
    gap_registry = plan.get("gap_registry")
    gap_ids = _exact_ids(gap_registry, "gap_id")
    gap_owners = _exact_ids(gap_registry, "owner_obligation")
    gap_id_set = {value for value in gap_ids if type(value) is str}
    if (
        type(gap_registry) is not list
        or len(gap_ids) != len(set(gap_ids))
        or any(type(value) is not str or not value for value in gap_ids)
        or any(owner not in EXPECTED_OBLIGATIONS for owner in gap_owners)
    ):
        findings.append("gap registry is not closed, unique, and obligation-owned")
    gap_owner_by_id = dict(zip(gap_ids, gap_owners, strict=False))
    if type(obligations) is list and all(type(row) is dict for row in obligations):
        prior_ids: set[str] = set()
        for row in obligations:
            obligation_id = row.get("obligation_id")
            dependencies = row.get("depends_on")
            if (
                type(obligation_id) is not str
                or type(dependencies) is not list
                or any(type(value) is not str for value in dependencies)
                or not set(dependencies).issubset(prior_ids)
            ):
                findings.append(f"invalid or forward obligation dependency: {obligation_id}")
            closes = row.get("closes", [])
            if type(closes) is not list or any(type(value) is not str for value in closes):
                findings.append(f"invalid closes list: {obligation_id}")
            elif any(value in EXPECTED_VM_GATES for value in closes):
                findings.append(f"individual obligation claims aggregate VM closure: {obligation_id}")
            elif any(value not in gap_id_set for value in closes):
                findings.append(f"unregistered gap target: {obligation_id}")
            elif any(gap_owner_by_id.get(value) != obligation_id for value in closes):
                findings.append(f"gap target owner mismatch: {obligation_id}")
            contributes_to = row.get("contributes_to", [])
            if (
                type(contributes_to) is not list
                or any(value not in EXPECTED_VM_GATES for value in contributes_to)
            ):
                findings.append(f"invalid VM contribution list: {obligation_id}")
            elif contributes_to and (
                type(row.get("bounded_delta")) is not str or not row["bounded_delta"].strip()
            ):
                findings.append(f"VM contribution lacks bounded delta: {obligation_id}")
            blocked_on_policy = row.get("blocked_on_policy", [])
            if (
                type(blocked_on_policy) is not list
                or any(value not in EXPECTED_POLICIES for value in blocked_on_policy)
            ):
                findings.append(f"invalid policy blocker list: {obligation_id}")
            if obligation_id == "O-010B" and (
                row.get("status") != "BLOCKED_PENDING_POLICY_DECISIONS"
                or blocked_on_policy != ["UP-01", "UP-12", "UP-14"]
            ):
                findings.append("buy-and-burn obligation policy blockers drift")
            if type(obligation_id) is str:
                prior_ids.add(obligation_id)
    if _exact_ids(plan.get("unresolved_semantic_decisions"), "decision_id") != EXPECTED_POLICIES:
        findings.append("unresolved semantic-decision set or order drift")

    (
        lane_count,
        capability_count,
        required_route_count,
        explicit_exclusion_count,
        minimum_release_evidence_cell_count,
    ) = _manifest_scope_counts(capability_manifest, findings)
    expected_estimate_warning = (
        "This is an immutable diagnosis of the implementation base. Live progress "
        "belongs in exact-subject obligation and value-movement ledgers. The "
        f"{minimum_release_evidence_cell_count}-cell count is a manifest-derived "
        "minimum and expands when requirement, evidence, migration, or terminal rows "
        "create additional obligations. Zero promoted cells is a release-evidence "
        "result, not a product implementation estimate."
    )

    verdict = plan.get("baseline_verdict")
    if type(verdict) is not dict or verdict.get("closed_value_movement_gates") != 0:
        findings.append("baseline verdict must not claim a closed value-movement gate")
    if type(verdict) is not dict or verdict.get("value_movement_gate_count") != 12:
        findings.append("value-movement gate count drift")
    if type(verdict) is not dict or any(
        (
            verdict.get("architecture_inventory")
            != (
                f"{lane_count}_LANES_{capability_count}_CAPABILITIES_"
                f"{required_route_count}_REQUIRED_ROUTES_"
                f"{explicit_exclusion_count}_EXCLUSIONS"
            ),
            verdict.get("strict_release_closure")
            != (
                f"0_OF_{minimum_release_evidence_cell_count}_"
                "MANIFEST_DERIVED_MINIMUM_EVIDENCE_CELLS"
            ),
            verdict.get("minimum_release_evidence_cell_count")
            != minimum_release_evidence_cell_count,
            verdict.get("minimum_release_evidence_cell_formula")
            != (
                f"({capability_count} capabilities + {required_route_count} routes) * "
                f"{len(REQUIRED_RELEASE_STATUSES)} required statuses + "
                f"{explicit_exclusion_count} exclusion certificates"
            ),
            verdict.get("required_release_statuses")
            != list(REQUIRED_RELEASE_STATUSES),
            verdict.get("required_route_count") != required_route_count,
            verdict.get("explicit_exclusion_count") != explicit_exclusion_count,
            verdict.get("promoted_release_evidence_cell_count") != 0,
            verdict.get("unclosed_release_evidence_cell_count")
            != minimum_release_evidence_cell_count,
            verdict.get("observed_release_closure_basis_points") != 0,
            verdict.get("scope_discovery_confidence")
            != "NOT_NUMERICALLY_ESTIMABLE_REQUIREMENTS_INCOMPLETE",
            verdict.get("estimate_warning") != expected_estimate_warning,
            "PERCENT" in json.dumps(verdict, sort_keys=True),
        )
    ):
        findings.append("manifest-derived release denominator or baseline telemetry drift")

    serialized = json.dumps(plan, sort_keys=True, separators=(",", ":"))
    for forbidden in FORBIDDEN_PLAN_TEXT:
        if forbidden in serialized:
            findings.append(f"forbidden plan text present: {forbidden}")

    return {
        "schema": "zenodex/whole-program-plan-check/v2.1",
        "ok": not findings,
        "plan_status": plan.get("status"),
        "production_authority": "NONE",
        "release_ready": False,
        "subject_tree_verified": subject_tree_verified,
        "lane_count": lane_count,
        "capability_count": capability_count,
        "required_route_count": required_route_count,
        "explicit_exclusion_count": explicit_exclusion_count,
        "minimum_release_evidence_cell_count": minimum_release_evidence_cell_count,
        "value_movement_gate_count": 12,
        "closed_value_movement_gate_count": 0,
        "findings": findings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--plan", type=Path)
    args = parser.parse_args(argv)
    report = check_whole_program_plan_v2(args.root, args.plan)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
