#!/usr/bin/env python3
"""Validate the research-only ZenoDEX architecture tournament.

The tournament separates structural design checks from promotion evidence.
Advisory scores may choose a research leader.  They can never freeze an
architecture: selection requires every hard gate and adversarial scenario to
carry independent evidence at the declared minimum grade.

The checker-owned registries and validation logic stay in one research module
for V1 so the JSON artifact cannot redefine its own oracle.  The file is larger
than the production-code target, while individual validation functions remain
small and mutation-tested.  A later schema freeze may split the registry from
the evaluator with parity vectors.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ARTIFACT = (
    REPO_ROOT / "docs/research/PRODUCTION_READINESS_ARCHITECTURE_TOURNAMENT_V1.json"
)
SCHEMA = "zenodex/production-readiness-architecture-tournament/v1"
REVIEWED_SUBJECT = "a2f5fd44333de7d79050534ee8c6c348bf82a423"

EXPECTED_SOURCE_PATHS = (
    "docs/PRODUCTION_READINESS_PLAN.md",
    "docs/research/PRODUCTION_READINESS_TASK_GRAPH_V1.json",
    "src/core/global_settlement_types_v1.py",
    "src/integration/m6_commit_port_v1.py",
    "zk/global_settlement_abi_v1/src/release.rs",
)

EXPECTED_STATE_DOMAINS = {
    "BALANCES_CUSTODY_SUPPLY",
    "SPOT_AND_LP",
    "ZUSD_MONETARY",
    "PERPS",
    "ORACLE",
    "SEALED_AUCTION",
    "TAU_ESCROW",
    "SERVICE_REWARDS",
    "OUTBOX_HISTORY_NULLIFIERS",
    "RELEASE_AND_MIGRATION",
}

HARD_GATES = {
    "SOLE_DURABLE_WRITER": 3,
    "UNIQUE_STATE_OWNERSHIP": 3,
    "TYPED_CLOSED_PORTS": 3,
    "ACYCLIC_DEPENDENCIES": 3,
    "DETERMINISTIC_COMPOSITION_ORDER": 4,
    "ATOMIC_GLOBAL_RECONCILIATION": 4,
    "REJECT_NO_COMMIT": 4,
    "OPAQUE_VERIFIER_WITNESS": 3,
    "VERIFIER_BACKEND_SUBSTITUTION": 3,
    "VERSION_COEXISTENCE_AND_DRAIN": 3,
    "REPLAY_IDEMPOTENCY": 3,
    "NO_BYPASS_MOUNT": 3,
    "DIRECT_ZRPF_CORE_PARITY": 3,
}

SOFT_METRICS = {
    "AUDITABILITY": 2_000,
    "CHANGE_ISOLATION": 1_600,
    "GLOBAL_INVARIANT_LOCALITY": 1_800,
    "VERIFIER_REPLACEABILITY": 1_200,
    "MIGRATION_SAFETY": 1_200,
    "PROOF_REUSE": 1_200,
    "OPERATIONAL_SIMPLICITY": 1_000,
}

SCENARIOS = {
    "TAU_UNAVAILABLE": 3,
    "TAU_NATIVE_VERIFIER_MISMATCH": 3,
    "CROSS_MODULE_DOUBLE_ALLOCATION": 4,
    "MIGRATION_DRAIN_WITH_OLD_OBJECTS": 3,
    "REJECTED_COMMAND_EXACT_NO_OP": 4,
    "REPLAY_ACROSS_RELEASE_EPOCH": 3,
    "ZRPF_RECEIPT_SUBSTITUTION": 3,
    "STALE_HEAD_CONCURRENT_PUBLICATION": 3,
    "OUTBOX_RETRY_AFTER_RESPONSE_LOSS": 3,
    "SHARED_ASSET_FEE_AND_REWARD_COLLISION": 4,
}

REQUIRED_PORT_ROLES = {
    "COMMAND_INGRESS",
    "LEDGER_INTENT",
    "POLICY_VERIFIER",
    "EXTERNAL_OUTBOX",
}
REQUIRED_RELEASE_LIFECYCLE = (
    "CANDIDATE",
    "SHADOW",
    "ACTIVE_NEW",
    "DRAIN_ONLY",
    "VERIFY_ONLY",
    "RETIRED",
    "REVOKED",
)
REQUIRED_REPLAY_KEY_FIELDS = {
    "COMMAND_ID",
    "SENDER",
    "NONCE",
    "WRITER_EPOCH",
    "CREATOR_RELEASE",
}
ALLOWED_FAMILIES = {
    "GLOBAL_MONOLITH",
    "EVENT_MICROSERVICES",
    "ACTOR_SAGA",
    "SETTLEMENT_MICROKERNEL",
}
REQUIRED_FAMILIES = {
    "GLOBAL_MONOLITH",
    "EVENT_MICROSERVICES",
    "SETTLEMENT_MICROKERNEL",
}
ALLOWED_OPERATORS = {"SEED", "DECOMPOSE", "COMPOSE", "CONSTRAIN", "REPLACE_PORT"}
ALLOWED_GATE_STATUSES = {"DESIGN_SATISFIED", "DESIGN_VIOLATED"}
ALLOWED_EVIDENCE_STATUSES = {"UNVERIFIED", "VERIFIED"}
ALLOWED_SCENARIO_STATUSES = {"UNTESTED", "VERIFIED", "REFUTED"}
ALLOWED_METRIC_STATUSES = {"ADVISORY", "MEASURED"}
ALLOWED_COUNTEREXAMPLE_STATUSES = {"OPEN", "CLOSED_DESIGN_ONLY", "CLOSED_VERIFIED"}
ALLOWED_COUNTEREXAMPLE_SEVERITIES = {"BLOCKER", "WARNING"}
EXPECTED_MUTANTS = {
    "MULTIPLE_DURABLE_WRITERS",
    "MODULE_WRITES_FOREIGN_STATE",
    "UNTYPED_OPEN_EVENT_PORT",
    "CYCLIC_MODULE_DEPENDENCY",
    "NONDETERMINISTIC_MODULE_ORDER",
    "PARTIAL_CROSS_MODULE_COMMIT",
    "REJECT_EMITS_EFFECT",
    "CALLER_CONSTRUCTED_VERIFIED_WITNESS",
    "VERIFIER_MISMATCH_FAILS_OPEN",
    "MIGRATION_WITHOUT_DRAIN",
    "REPLAY_SCOPE_OMITS_RELEASE",
    "DELTA_TRUSTED_FROM_MODULE",
    "SECOND_MOUNTED_WRITER_CAPABILITY",
    "ZRPF_USES_DIFFERENT_CORE",
}

ROOT_KEYS = {
    "schema",
    "status",
    "production_promotion",
    "architecture_frozen",
    "reviewed_subject",
    "source_pins",
    "problem_state",
    "hard_gates",
    "soft_metrics",
    "scenario_pack",
    "candidates",
    "selection",
    "named_mutants",
    "nonclaims",
}
CANDIDATE_KEYS = {
    "id",
    "family",
    "parents",
    "operator",
    "summary",
    "components",
    "state_domains",
    "ports",
    "composition",
    "gate_claims",
    "metrics",
    "scenario_claims",
    "counterexamples",
}
COMPOSITION_KEYS = {
    "order_rule",
    "tie_break",
    "commit_protocol",
    "partial_commit_possible",
    "reject_mutates_state",
    "reject_emits_effects",
    "verifier_witness_constructor",
    "policy_verifier_backends",
    "verifier_mismatch_policy",
    "release_lifecycle",
    "objects_pin_creator_release",
    "replay_key_fields",
    "mounted_writer_capabilities",
    "direct_core_id",
    "zrpf_core_id",
    "value_delta_source",
}


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError("artifact root must be an object")
    return value


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _is_sha256(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _is_relative_path(value: object) -> bool:
    if not isinstance(value, str) or not value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts


def _exact_keys(
    value: object,
    expected: set[str],
    label: str,
    errors: list[str],
) -> Mapping[str, Any] | None:
    if not isinstance(value, Mapping):
        errors.append(f"{label} must be an object")
        return None
    actual = set(value)
    if actual != expected:
        errors.append(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )
    return value


def _string_list(value: object, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        errors.append(f"{label} must be a string list")
        return []
    if len(value) != len(set(value)):
        errors.append(f"{label} must be unique")
    return value


def _rows_by_id(
    value: object,
    label: str,
    errors: list[str],
) -> dict[str, Mapping[str, Any]]:
    if not isinstance(value, list):
        errors.append(f"{label} must be a list")
        return {}
    rows: dict[str, Mapping[str, Any]] = {}
    for index, row in enumerate(value):
        if not isinstance(row, Mapping):
            errors.append(f"{label}[{index}] must be an object")
            continue
        row_id = row.get("id")
        if not isinstance(row_id, str) or not row_id or row_id in rows:
            errors.append(f"{label}[{index}] has invalid or duplicate id")
            continue
        rows[row_id] = row
    return rows


def _has_cycle(edges: Mapping[str, Sequence[str]]) -> bool:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        for dependency in edges.get(node, ()):
            if dependency in edges and visit(dependency):
                return True
        visiting.remove(node)
        visited.add(node)
        return False

    return any(visit(node) for node in edges)


def _check_subject_and_pins(
    document: Mapping[str, Any], repo_root: Path, errors: list[str]
) -> None:
    if document.get("reviewed_subject") != REVIEWED_SUBJECT:
        errors.append("reviewed_subject differs from the frozen tournament subject")
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", REVIEWED_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        errors.append("reviewed_subject is not an ancestor of HEAD")

    pins = _rows_by_id(document.get("source_pins"), "source_pins", errors)
    if set(pins) != set(EXPECTED_SOURCE_PATHS):
        errors.append("source_pins must bind the exact architecture input paths")
    for path, row in pins.items():
        _exact_keys(row, {"id", "sha256"}, f"source_pins[{path}]", errors)
        if not _is_relative_path(path):
            errors.append(f"source pin path is unsafe: {path!r}")
            continue
        source = repo_root / path
        if not source.is_file():
            errors.append(f"source pin path is missing: {path}")
            continue
        digest = row.get("sha256")
        if not _is_sha256(digest) or digest != _sha256(source.read_bytes()):
            errors.append(f"source pin digest mismatch: {path}")


def _check_definitions(document: Mapping[str, Any], errors: list[str]) -> None:
    problem = _exact_keys(
        document.get("problem_state"),
        {"representation", "abstraction", "constraints", "goal", "obligations", "portals", "metadata"},
        "problem_state",
        errors,
    )
    if problem is not None:
        for key in ("constraints", "obligations", "portals", "metadata"):
            if not _string_list(problem.get(key), f"problem_state.{key}", errors):
                errors.append(f"problem_state.{key} must be nonempty")
        for key in ("representation", "abstraction", "goal"):
            if not isinstance(problem.get(key), str) or not problem[key].strip():
                errors.append(f"problem_state.{key} must be nonempty")

    gates = _rows_by_id(document.get("hard_gates"), "hard_gates", errors)
    if set(gates) != set(HARD_GATES):
        errors.append("hard_gates differ from the checker-owned gate registry")
    for gate_id, minimum_grade in HARD_GATES.items():
        row = gates.get(gate_id)
        if row is None:
            continue
        _exact_keys(row, {"id", "description", "minimum_evidence_grade"}, f"hard_gates[{gate_id}]", errors)
        if row.get("minimum_evidence_grade") != minimum_grade:
            errors.append(f"hard_gates[{gate_id}] minimum evidence grade differs")
        if not isinstance(row.get("description"), str) or not row["description"].strip():
            errors.append(f"hard_gates[{gate_id}] description must be nonempty")

    metrics = _rows_by_id(document.get("soft_metrics"), "soft_metrics", errors)
    if set(metrics) != set(SOFT_METRICS):
        errors.append("soft_metrics differ from the checker-owned metric registry")
    for metric_id, weight_bps in SOFT_METRICS.items():
        row = metrics.get(metric_id)
        if row is None:
            continue
        _exact_keys(row, {"id", "description", "weight_bps"}, f"soft_metrics[{metric_id}]", errors)
        if row.get("weight_bps") != weight_bps:
            errors.append(f"soft_metrics[{metric_id}] weight differs")
    if sum(SOFT_METRICS.values()) != 10_000:
        errors.append("checker-owned metric weights do not sum to 10000")

    scenarios = _rows_by_id(document.get("scenario_pack"), "scenario_pack", errors)
    if set(scenarios) != set(SCENARIOS):
        errors.append("scenario_pack differs from the checker-owned scenario registry")
    for scenario_id, minimum_grade in SCENARIOS.items():
        row = scenarios.get(scenario_id)
        if row is None:
            continue
        _exact_keys(
            row,
            {"id", "history", "expected_observation", "minimum_evidence_grade"},
            f"scenario_pack[{scenario_id}]",
            errors,
        )
        if row.get("minimum_evidence_grade") != minimum_grade:
            errors.append(f"scenario_pack[{scenario_id}] minimum evidence grade differs")


def _component_graph(
    candidate: Mapping[str, Any], label: str, errors: list[str]
) -> tuple[dict[str, Mapping[str, Any]], dict[str, list[str]]]:
    components = _rows_by_id(candidate.get("components"), f"{label}.components", errors)
    edges: dict[str, list[str]] = {}
    for component_id, row in components.items():
        _exact_keys(row, {"id", "depends_on"}, f"{label}.components[{component_id}]", errors)
        dependencies = _string_list(
            row.get("depends_on"), f"{label}.components[{component_id}].depends_on", errors
        )
        if any(dependency not in components for dependency in dependencies):
            errors.append(f"{label}.components[{component_id}] has an unknown dependency")
        edges[component_id] = dependencies
    return components, edges


def _state_domain_gates(
    candidate: Mapping[str, Any],
    components: Mapping[str, Mapping[str, Any]],
    label: str,
    errors: list[str],
) -> tuple[bool, bool]:
    domains = _rows_by_id(candidate.get("state_domains"), f"{label}.state_domains", errors)
    if set(domains) != EXPECTED_STATE_DOMAINS:
        errors.append(f"{label}.state_domains differ from the checker-owned domain registry")
    semantic_owner_ok = True
    sole_writer_ok = True
    for domain_id, row in domains.items():
        _exact_keys(
            row,
            {"id", "semantic_owners", "durable_writers"},
            f"{label}.state_domains[{domain_id}]",
            errors,
        )
        owners = _string_list(
            row.get("semantic_owners"), f"{label}.state_domains[{domain_id}].semantic_owners", errors
        )
        writers = _string_list(
            row.get("durable_writers"), f"{label}.state_domains[{domain_id}].durable_writers", errors
        )
        semantic_owner_ok &= len(owners) == 1 and owners[0] in components
        sole_writer_ok &= writers == ["ZENO_LEDGER"]
    return semantic_owner_ok, sole_writer_ok


def _port_gates(
    candidate: Mapping[str, Any],
    components: Mapping[str, Mapping[str, Any]],
    label: str,
    errors: list[str],
) -> tuple[bool, bool]:
    ports = _rows_by_id(candidate.get("ports"), f"{label}.ports", errors)
    roles: set[str] = set()
    typed_ports_ok = bool(ports)
    opaque_witness_ok = False
    for port_id, row in ports.items():
        _exact_keys(
            row,
            {
                "id",
                "role",
                "producer",
                "consumer",
                "request_type",
                "response_type",
                "closed_variants",
                "caller_constructible_authority",
            },
            f"{label}.ports[{port_id}]",
            errors,
        )
        role = row.get("role")
        if isinstance(role, str):
            roles.add(role)
        endpoints_ok = row.get("producer") in components and row.get("consumer") in components
        types = (row.get("request_type"), row.get("response_type"))
        named_types = all(
            isinstance(value, str) and value and value not in {"ANY", "UNTYPED_MAP", "UNTYPED_EVENT"}
            for value in types
        )
        port_ok = (
            endpoints_ok
            and named_types
            and row.get("closed_variants") is True
            and row.get("caller_constructible_authority") is False
        )
        typed_ports_ok &= port_ok
        if role == "POLICY_VERIFIER":
            opaque_witness_ok |= port_ok and row.get("response_type") == "VerifiedAdmissionV2"
    typed_ports_ok &= roles == REQUIRED_PORT_ROLES
    return typed_ports_ok, opaque_witness_ok


def _composition_gates(
    candidate: Mapping[str, Any],
    opaque_witness_ok: bool,
    label: str,
    errors: list[str],
) -> dict[str, bool]:
    composition = _exact_keys(
        candidate.get("composition"), COMPOSITION_KEYS, f"{label}.composition", errors
    )
    if composition is None:
        return {
            gate_id: False
            for gate_id in HARD_GATES
            if gate_id not in {
                "SOLE_DURABLE_WRITER",
                "UNIQUE_STATE_OWNERSHIP",
                "TYPED_CLOSED_PORTS",
                "ACYCLIC_DEPENDENCIES",
            }
        }
    return _composition_predicates(composition, opaque_witness_ok, label, errors)


def _composition_predicates(
    composition: Mapping[str, Any],
    opaque_witness_ok: bool,
    label: str,
    errors: list[str],
) -> dict[str, bool]:
    backend_values = _string_list(
        composition.get("policy_verifier_backends"),
        f"{label}.composition.policy_verifier_backends",
        errors,
    )
    lifecycle = composition.get("release_lifecycle")
    replay_fields = _string_list(
        composition.get("replay_key_fields"),
        f"{label}.composition.replay_key_fields",
        errors,
    )
    writer_capabilities = _string_list(
        composition.get("mounted_writer_capabilities"),
        f"{label}.composition.mounted_writer_capabilities",
        errors,
    )

    return {
        "DETERMINISTIC_COMPOSITION_ORDER": (
            composition.get("order_rule") == "CANONICAL_TOPOLOGICAL_THEN_COMMAND_INDEX"
            and composition.get("tie_break") == "MODULE_ID_ASCENDING"
        ),
        "ATOMIC_GLOBAL_RECONCILIATION": (
            composition.get("commit_protocol") == "ONE_EXPECTED_HEAD_CAS"
            and composition.get("partial_commit_possible") is False
            and composition.get("value_delta_source") == "CENTRAL_DERIVATION"
        ),
        "REJECT_NO_COMMIT": (
            composition.get("reject_mutates_state") is False
            and composition.get("reject_emits_effects") is False
        ),
        "OPAQUE_VERIFIER_WITNESS": (
            opaque_witness_ok and composition.get("verifier_witness_constructor") == "VERIFIER_ONLY"
        ),
        "VERIFIER_BACKEND_SUBSTITUTION": (
            set(backend_values) == {"NATIVE", "TAU"}
            and composition.get("verifier_mismatch_policy") == "REJECT"
        ),
        "VERSION_COEXISTENCE_AND_DRAIN": (
            lifecycle == list(REQUIRED_RELEASE_LIFECYCLE)
            and composition.get("objects_pin_creator_release") is True
        ),
        "REPLAY_IDEMPOTENCY": set(replay_fields) == REQUIRED_REPLAY_KEY_FIELDS,
        "NO_BYPASS_MOUNT": writer_capabilities == ["ZENO_LEDGER_SUBMIT_V2"],
        "DIRECT_ZRPF_CORE_PARITY": (
            isinstance(composition.get("direct_core_id"), str)
            and bool(composition.get("direct_core_id"))
            and composition.get("direct_core_id") == composition.get("zrpf_core_id")
        ),
    }


def _derive_design_gates(
    candidate: Mapping[str, Any], label: str, errors: list[str]
) -> dict[str, bool]:
    components, edges = _component_graph(candidate, label, errors)
    semantic_owner_ok, sole_writer_ok = _state_domain_gates(
        candidate, components, label, errors
    )
    typed_ports_ok, opaque_witness_ok = _port_gates(candidate, components, label, errors)
    gates = {
        "SOLE_DURABLE_WRITER": sole_writer_ok,
        "UNIQUE_STATE_OWNERSHIP": semantic_owner_ok,
        "TYPED_CLOSED_PORTS": typed_ports_ok,
        "ACYCLIC_DEPENDENCIES": not _has_cycle(edges),
    }
    gates.update(_composition_gates(candidate, opaque_witness_ok, label, errors))
    return gates


def _check_gate_claims(
    candidate: Mapping[str, Any],
    derived: Mapping[str, bool],
    label: str,
    errors: list[str],
) -> bool:
    claims = _rows_by_id(candidate.get("gate_claims"), f"{label}.gate_claims", errors)
    if set(claims) != set(HARD_GATES):
        errors.append(f"{label}.gate_claims differ from the checker-owned gate registry")
    # V1 has no authenticated evidence resolver.  Candidate-authored strings
    # therefore cannot promote a gate, regardless of the claimed grade.
    promotion_ready = False
    for gate_id, _minimum_grade in HARD_GATES.items():
        row = claims.get(gate_id)
        if row is None:
            promotion_ready = False
            continue
        _exact_keys(
            row,
            {"id", "design_status", "evidence_status", "evidence_grade", "evidence_refs"},
            f"{label}.gate_claims[{gate_id}]",
            errors,
        )
        expected_design = "DESIGN_SATISFIED" if derived.get(gate_id) else "DESIGN_VIOLATED"
        if row.get("design_status") not in ALLOWED_GATE_STATUSES or row.get("design_status") != expected_design:
            errors.append(f"{label}.gate_claims[{gate_id}] design status differs from derived structure")
        evidence_status = row.get("evidence_status")
        grade = row.get("evidence_grade")
        refs = _string_list(
            row.get("evidence_refs"), f"{label}.gate_claims[{gate_id}].evidence_refs", errors
        )
        if evidence_status not in ALLOWED_EVIDENCE_STATUSES or not isinstance(grade, int):
            errors.append(f"{label}.gate_claims[{gate_id}] has invalid evidence fields")
        if evidence_status != "UNVERIFIED" or grade != 0 or refs:
            errors.append(
                f"{label}.gate_claims[{gate_id}] must remain unverified until "
                "an authenticated evidence resolver is implemented"
            )
    return promotion_ready


def _check_metrics(
    candidate: Mapping[str, Any], label: str, errors: list[str]
) -> tuple[int, int, bool]:
    rows = _rows_by_id(candidate.get("metrics"), f"{label}.metrics", errors)
    if set(rows) != set(SOFT_METRICS):
        errors.append(f"{label}.metrics differ from the checker-owned metric registry")
    values: list[int] = []
    weighted_numerator = 0
    measured = False
    for metric_id, weight_bps in SOFT_METRICS.items():
        row = rows.get(metric_id)
        if row is None:
            measured = False
            continue
        _exact_keys(
            row,
            {"id", "value_milli", "status", "evidence_refs"},
            f"{label}.metrics[{metric_id}]",
            errors,
        )
        value = row.get("value_milli")
        status = row.get("status")
        refs = _string_list(row.get("evidence_refs"), f"{label}.metrics[{metric_id}].evidence_refs", errors)
        if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value <= 1_000:
            errors.append(f"{label}.metrics[{metric_id}] value_milli must be 0..1000")
            value = 0
        if status not in ALLOWED_METRIC_STATUSES:
            errors.append(f"{label}.metrics[{metric_id}] has invalid status")
        if status != "ADVISORY" or refs:
            errors.append(
                f"{label}.metrics[{metric_id}] must remain advisory without "
                "resolver-backed measurement evidence"
            )
        values.append(value)
        weighted_numerator += value * weight_bps
    return (min(values, default=0), weighted_numerator // 10_000, measured)


def _check_scenarios(
    candidate: Mapping[str, Any], label: str, errors: list[str]
) -> bool:
    rows = _rows_by_id(candidate.get("scenario_claims"), f"{label}.scenario_claims", errors)
    if set(rows) != set(SCENARIOS):
        errors.append(f"{label}.scenario_claims differ from the checker-owned scenario registry")
    all_verified = False
    for scenario_id, _minimum_grade in SCENARIOS.items():
        row = rows.get(scenario_id)
        if row is None:
            all_verified = False
            continue
        _exact_keys(
            row,
            {"id", "status", "evidence_grade", "evidence_refs"},
            f"{label}.scenario_claims[{scenario_id}]",
            errors,
        )
        status = row.get("status")
        grade = row.get("evidence_grade")
        refs = _string_list(
            row.get("evidence_refs"), f"{label}.scenario_claims[{scenario_id}].evidence_refs", errors
        )
        if status not in ALLOWED_SCENARIO_STATUSES or not isinstance(grade, int):
            errors.append(f"{label}.scenario_claims[{scenario_id}] has invalid evidence fields")
        if status != "UNTESTED" or grade != 0 or refs:
            errors.append(
                f"{label}.scenario_claims[{scenario_id}] must remain untested until "
                "an authenticated evidence resolver is implemented"
            )
    return all_verified


def _check_counterexamples(
    candidate: Mapping[str, Any], label: str, errors: list[str]
) -> tuple[bool, bool]:
    rows = _rows_by_id(candidate.get("counterexamples"), f"{label}.counterexamples", errors)
    open_blocker = False
    open_any = False
    for counterexample_id, row in rows.items():
        _exact_keys(
            row,
            {"id", "severity", "status", "history", "closure"},
            f"{label}.counterexamples[{counterexample_id}]",
            errors,
        )
        severity = row.get("severity")
        status = row.get("status")
        if severity not in ALLOWED_COUNTEREXAMPLE_SEVERITIES:
            errors.append(f"{label}.counterexamples[{counterexample_id}] has invalid severity")
        if status not in ALLOWED_COUNTEREXAMPLE_STATUSES:
            errors.append(f"{label}.counterexamples[{counterexample_id}] has invalid status")
        if not isinstance(row.get("history"), str) or not row["history"].strip():
            errors.append(f"{label}.counterexamples[{counterexample_id}] history must be nonempty")
        if not isinstance(row.get("closure"), str) or not row["closure"].strip():
            errors.append(f"{label}.counterexamples[{counterexample_id}] closure must be nonempty")
        is_open = status == "OPEN"
        open_any |= is_open
        open_blocker |= is_open and severity == "BLOCKER"
    return open_blocker, open_any


def _check_evolution_dag(
    candidates: Mapping[str, Mapping[str, Any]], errors: list[str]
) -> None:
    edges: dict[str, list[str]] = {}
    for candidate_id, candidate in candidates.items():
        parents = _string_list(candidate.get("parents"), f"candidates[{candidate_id}].parents", errors)
        if any(parent not in candidates for parent in parents):
            errors.append(f"candidates[{candidate_id}] has an unknown parent")
        operator = candidate.get("operator")
        if operator not in ALLOWED_OPERATORS:
            errors.append(f"candidates[{candidate_id}] has an invalid evolution operator")
        if (operator == "SEED") != (not parents):
            errors.append(f"candidates[{candidate_id}] seed/parent relationship is inconsistent")
        edges[candidate_id] = parents
    if _has_cycle(edges):
        errors.append("candidate evolution graph is cyclic")


def _candidate_header(
    candidate: Mapping[str, Any], candidate_id: str, label: str, errors: list[str]
) -> None:
    _exact_keys(candidate, CANDIDATE_KEYS, label, errors)
    if candidate.get("id") != candidate_id:
        errors.append(f"{label}.id differs")
    if candidate.get("family") not in ALLOWED_FAMILIES:
        errors.append(f"{label}.family is invalid")
    if not isinstance(candidate.get("summary"), str) or not candidate["summary"].strip():
        errors.append(f"{label}.summary must be nonempty")


def _assess_candidate(
    candidate: Mapping[str, Any], candidate_id: str, errors: list[str]
) -> tuple[dict[str, Any], tuple[int, int] | None, bool]:
    label = f"candidates[{candidate_id}]"
    _candidate_header(candidate, candidate_id, label, errors)
    derived = _derive_design_gates(candidate, label, errors)
    gates_verified = _check_gate_claims(candidate, derived, label, errors)
    minimum_metric, weighted_metric, metrics_measured = _check_metrics(candidate, label, errors)
    scenarios_verified = _check_scenarios(candidate, label, errors)
    open_blocker, open_any = _check_counterexamples(candidate, label, errors)
    design_satisfied = all(derived.values())
    research_eligible = design_satisfied and not open_blocker
    promotion_eligible = (
        research_eligible
        and gates_verified
        and metrics_measured
        and scenarios_verified
        and not open_any
    )
    report = {
        "id": candidate_id,
        "design_gate_pass_count": sum(derived.values()),
        "design_gate_count": len(HARD_GATES),
        "minimum_metric_milli": minimum_metric,
        "weighted_metric_milli": weighted_metric,
        "research_eligible": research_eligible,
        "promotion_eligible": promotion_eligible,
        "open_blocker": open_blocker,
    }
    ranking = (minimum_metric, weighted_metric) if research_eligible else None
    return report, ranking, promotion_eligible


def _check_candidates(
    document: Mapping[str, Any], errors: list[str]
) -> tuple[
    dict[str, Mapping[str, Any]],
    dict[str, tuple[int, int]],
    list[str],
    list[dict[str, Any]],
]:
    raw_candidates = _rows_by_id(document.get("candidates"), "candidates", errors)
    candidates = dict(raw_candidates)
    if len(candidates) < 3:
        errors.append("at least three architecture candidates are required")
    families = {candidate.get("family") for candidate in candidates.values()}
    if not families <= ALLOWED_FAMILIES or not REQUIRED_FAMILIES <= families:
        errors.append("candidate families do not cover the required architecture alternatives")
    _check_evolution_dag(candidates, errors)

    research_rankings: dict[str, tuple[int, int]] = {}
    promotable: list[str] = []
    candidate_reports: list[dict[str, Any]] = []
    for candidate_id, candidate in sorted(candidates.items()):
        report, ranking, is_promotable = _assess_candidate(candidate, candidate_id, errors)
        candidate_reports.append(report)
        if ranking is not None:
            research_rankings[candidate_id] = ranking
        if is_promotable:
            promotable.append(candidate_id)
    return candidates, research_rankings, promotable, candidate_reports


def _ranked_leader(
    rankings: Mapping[str, tuple[int, int]], candidates: Sequence[str] | None = None
) -> str | None:
    eligible = list(rankings) if candidates is None else list(candidates)
    if not eligible:
        return None
    return sorted(
        eligible,
        key=lambda candidate_id: (
            -rankings[candidate_id][0],
            -rankings[candidate_id][1],
            candidate_id,
        ),
    )[0]


def _check_selection(
    document: Mapping[str, Any],
    research_rankings: Mapping[str, tuple[int, int]],
    promotable: Sequence[str],
    errors: list[str],
) -> tuple[str | None, dict[str, int] | None, object]:
    leader_id = _ranked_leader(research_rankings)
    leader_rank = None
    if leader_id is not None:
        leader_rank = {
            "minimum_metric_milli": research_rankings[leader_id][0],
            "weighted_metric_milli": research_rankings[leader_id][1],
        }

    selection = _exact_keys(
        document.get("selection"),
        {
            "algorithm",
            "research_leader_id",
            "research_leader_rank",
            "promotable_candidate_ids",
            "selected_candidate_id",
            "rationale",
        },
        "selection",
        errors,
    )
    selected_id: object = None
    if selection is not None:
        if selection.get("algorithm") != "HARD_GATE_FILTER_THEN_MAXIMIN_WEIGHTED_V1":
            errors.append("selection algorithm differs")
        if selection.get("research_leader_id") != leader_id:
            errors.append("selection research leader differs from deterministic ranking")
        if selection.get("research_leader_rank") != leader_rank:
            errors.append("selection research leader rank differs from deterministic ranking")
        if selection.get("promotable_candidate_ids") != sorted(promotable):
            errors.append("selection promotable candidate list differs")
        selected_id = selection.get("selected_candidate_id")
        if selected_id is not None and selected_id not in promotable:
            errors.append("selected candidate is not promotion eligible")
        expected_selected = _ranked_leader(research_rankings, promotable)
        if selected_id != expected_selected:
            errors.append("selected candidate differs from deterministic promotable leader")
    return leader_id, leader_rank, selected_id


def _check_mutants_and_nonclaims(document: Mapping[str, Any], errors: list[str]) -> None:
    mutants = _rows_by_id(document.get("named_mutants"), "named_mutants", errors)
    if set(mutants) != EXPECTED_MUTANTS:
        errors.append("named_mutants differ from the checker-owned mutation registry")
    for mutant_id, row in mutants.items():
        _exact_keys(row, {"id", "description", "expected_detection"}, f"named_mutants[{mutant_id}]", errors)
        for key in ("description", "expected_detection"):
            if not isinstance(row.get(key), str) or not row[key].strip():
                errors.append(f"named_mutants[{mutant_id}].{key} must be nonempty")
    if len(_string_list(document.get("nonclaims"), "nonclaims", errors)) < 4:
        errors.append("nonclaims must contain at least four explicit limits")


def check_document(
    document: Mapping[str, Any], repo_root: Path = REPO_ROOT
) -> dict[str, Any]:
    errors: list[str] = []
    _exact_keys(document, ROOT_KEYS, "artifact", errors)
    if document.get("schema") != SCHEMA:
        errors.append("wrong artifact schema")
    if document.get("status") != "RESEARCH_ONLY_UNSELECTED":
        errors.append("status must remain RESEARCH_ONLY_UNSELECTED")
    if document.get("production_promotion") is not False:
        errors.append("production_promotion must remain false")
    if not isinstance(document.get("architecture_frozen"), bool):
        errors.append("architecture_frozen must be boolean")

    _check_subject_and_pins(document, repo_root, errors)
    _check_definitions(document, errors)
    candidates, rankings, promotable, candidate_reports = _check_candidates(document, errors)
    leader_id, _, selected_id = _check_selection(document, rankings, promotable, errors)

    architecture_frozen = document.get("architecture_frozen")
    if architecture_frozen is not (selected_id is not None):
        errors.append("architecture_frozen must exactly track a selected promotion-eligible candidate")
    _check_mutants_and_nonclaims(document, errors)

    ok = not errors
    effective_selected_id = selected_id if ok else None
    effective_architecture_frozen = bool(architecture_frozen) if ok else False

    return {
        "schema": "zenodex/production-readiness-architecture-tournament-check/v1",
        "ok": ok,
        "error_count": len(errors),
        "errors": errors,
        "candidate_count": len(candidates),
        "research_leader_id": leader_id,
        "promotable_candidate_count": len(promotable),
        "selected_candidate_id": effective_selected_id,
        "architecture_frozen": effective_architecture_frozen,
        "production_ready": False,
        "candidate_reports": candidate_reports,
    }


def check_artifact(path: Path = DEFAULT_ARTIFACT) -> dict[str, Any]:
    try:
        document = _load(path)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        return {
            "schema": "zenodex/production-readiness-architecture-tournament-check/v1",
            "ok": False,
            "error_count": 1,
            "errors": [str(exc)],
            "production_ready": False,
        }
    return check_document(document, path.resolve().parents[2])


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--json", action="store_true", dest="as_json")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    report = check_artifact(args.artifact)
    if args.as_json:
        json.dump(report, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    elif report["ok"]:
        print(
            "architecture tournament: PASS "
            f"({report['candidate_count']} candidates; leader={report['research_leader_id']}; "
            f"promotable={report['promotable_candidate_count']}; frozen={report['architecture_frozen']})"
        )
    else:
        print("architecture tournament: FAIL", file=sys.stderr)
        for error in report["errors"]:
            print(f"- {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
