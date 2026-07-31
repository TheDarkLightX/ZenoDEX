#!/usr/bin/env python3
"""Check the review-only M6-R01 OwnedSettlementV2 witness-language contract."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import cast

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT = (
    REPO_ROOT
    / "docs/research/FCIS_M6_R01_OWNED_SETTLEMENT_V2_ATDD_MATRIX_20260731.json"
)
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


from tools.fcis_m6_r01_owned_settlement_v2_contract_policy import (  # noqa: E402
    CASE_FIELDS,
    FORBIDDEN_BACK_EDGES,
    FORBIDDEN_INNER_FIELDS,
    INNER_FIELDS,
    NO_SUCCESSOR_OUTPUTS,
    NONCLAIMS,
    NORMATIVE_SOURCE,
    NORMATIVE_SOURCE_FIELDS,
    OUTER_FIELDS,
    REQUIRED_CASE_IDS,
    REQUIRED_EDGES,
    ROOT_FIELDS,
    SCHEMA,
    SOURCE_ROLE_FIELDS,
    SOURCE_ROLES,
)


class DuplicateJsonMember(ValueError):
    """Raised when JSON repeats an object member."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise DuplicateJsonMember(key)
        value[key] = item
    return value


def _load_contract(path: Path) -> dict[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_object,
        parse_constant=lambda token: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON token: {token}")
        ),
    )
    if type(value) is not dict:
        raise ValueError("contract must contain one object")
    return cast(dict[str, object], value)


def _exact_string_list(value: object) -> list[str] | None:
    if type(value) is not list or any(type(item) is not str for item in value):
        return None
    return cast(list[str], value)


def _field_error(label: str, actual: set[str], expected: set[str]) -> str:
    missing = ",".join(sorted(expected - actual))
    unknown = ",".join(sorted(actual - expected))
    return f"{label}:missing={missing}:unknown={unknown}"


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _validate_sources(
    value: object,
    *,
    repo_root: Path,
) -> list[str]:
    if type(value) is not dict:
        return ["NORMATIVE_SOURCE_TYPE"]
    source = cast(dict[str, object], value)
    errors: list[str] = []
    if set(source) != NORMATIVE_SOURCE_FIELDS:
        errors.append(
            _field_error(
                "NORMATIVE_SOURCE_FIELDS",
                set(source),
                NORMATIVE_SOURCE_FIELDS,
            )
        )
        return errors
    for field, expected_value in NORMATIVE_SOURCE.items():
        if source.get(field) != expected_value:
            errors.append(f"NORMATIVE_SOURCE_IDENTITY:{field}")
    for path_field, digest_field in (
        ("architecture_path", "architecture_sha256"),
        ("current_command_root_path", "current_command_root_sha256"),
    ):
        relative = source.get(path_field)
        expected = source.get(digest_field)
        if type(relative) is not str or type(expected) is not str:
            errors.append(f"NORMATIVE_SOURCE_VALUE:{path_field}")
            continue
        target = repo_root / relative
        if not target.is_file():
            errors.append(f"NORMATIVE_SOURCE_MISSING:{relative}")
        elif _digest(target) != expected:
            errors.append(f"NORMATIVE_SOURCE_HASH:{relative}")
    return errors


def _validate_decision(value: object) -> list[str]:
    if type(value) is not dict:
        return ["DECISION_TYPE"]
    decision = cast(dict[str, object], value)
    expected_fields = {
        "controlled_batch_type",
        "forbidden_inner_claim_fields",
        "inner_claim_fields",
        "inner_claim_type",
        "outer_field_registry",
        "root_strategy",
    }
    errors: list[str] = []
    if set(decision) != expected_fields:
        errors.append(_field_error("DECISION_FIELDS", set(decision), expected_fields))
        return errors
    if decision.get("inner_claim_type") != "ProvisionalProtocolFeeOccurrenceClaimV2":
        errors.append("INNER_CLAIM_TYPE")
    if (
        decision.get("controlled_batch_type")
        != "StateBoundProvisionalProtocolFeeWitnessBatchV2"
    ):
        errors.append("CONTROLLED_BATCH_TYPE")
    if (
        decision.get("root_strategy")
        != "full_settlement_envelope_then_external_state_bound_batch"
    ):
        errors.append("ROOT_STRATEGY")
    if _exact_string_list(decision.get("outer_field_registry")) != OUTER_FIELDS:
        errors.append("OUTER_FIELD_REGISTRY")
    if _exact_string_list(decision.get("inner_claim_fields")) != INNER_FIELDS:
        errors.append("INNER_CLAIM_FIELDS")
    if (
        _exact_string_list(decision.get("forbidden_inner_claim_fields"))
        != FORBIDDEN_INNER_FIELDS
    ):
        errors.append("FORBIDDEN_INNER_CLAIM_FIELDS")
    inner_fields = _exact_string_list(decision.get("inner_claim_fields")) or []
    overlap = sorted(set(inner_fields) & set(FORBIDDEN_INNER_FIELDS))
    if overlap:
        errors.append(f"INNER_CLAIM_DOWNSTREAM_FIELD:{','.join(overlap)}")
    return errors


def _edge_set(value: object) -> tuple[set[tuple[str, str]], list[str]]:
    if type(value) is not list:
        return set(), ["DEPENDENCY_EDGES_TYPE"]
    edges: set[tuple[str, str]] = set()
    errors: list[str] = []
    for index, item in enumerate(cast(list[object], value)):
        if type(item) is not dict:
            errors.append(f"DEPENDENCY_EDGE_TYPE:{index}")
            continue
        edge = cast(dict[str, object], item)
        if set(edge) != {"from", "to"}:
            errors.append(
                _field_error(
                    f"DEPENDENCY_EDGE_FIELDS:{index}",
                    set(edge),
                    {"from", "to"},
                )
            )
            continue
        source = edge.get("from")
        target = edge.get("to")
        if type(source) is not str or type(target) is not str:
            errors.append(f"DEPENDENCY_EDGE_VALUE:{index}")
            continue
        pair = (source, target)
        if pair in edges:
            errors.append(f"DEPENDENCY_EDGE_DUPLICATE:{source}:{target}")
        edges.add(pair)
    return edges, errors


def _validate_graph(value: object) -> list[str]:
    if type(value) is not dict:
        return ["DEPENDENCY_GRAPH_TYPE"]
    graph = cast(dict[str, object], value)
    errors: list[str] = []
    if set(graph) != {"edges", "nodes", "topological_order"}:
        errors.append(
            _field_error(
                "DEPENDENCY_GRAPH_FIELDS",
                set(graph),
                {"edges", "nodes", "topological_order"},
            )
        )
        return errors
    nodes = _exact_string_list(graph.get("nodes"))
    order = _exact_string_list(graph.get("topological_order"))
    if nodes is None or len(nodes) != len(set(nodes)):
        errors.append("DEPENDENCY_NODES")
        nodes = []
    if order is None or Counter(order) != Counter(nodes):
        errors.append("DEPENDENCY_TOPOLOGICAL_COVERAGE")
        order = []
    edges, edge_errors = _edge_set(graph.get("edges"))
    errors.extend(edge_errors)
    node_set = set(nodes)
    if any(source not in node_set or target not in node_set for source, target in edges):
        errors.append("DEPENDENCY_EDGE_UNKNOWN_NODE")
    missing = sorted(REQUIRED_EDGES - edges)
    extra = sorted(edges - REQUIRED_EDGES)
    if missing:
        errors.append(
            "DEPENDENCY_EDGES_MISSING:"
            + ",".join(f"{source}->{target}" for source, target in missing)
        )
    if extra:
        errors.append(
            "DEPENDENCY_EDGES_UNKNOWN:"
            + ",".join(f"{source}->{target}" for source, target in extra)
        )
    forbidden = sorted(edges & FORBIDDEN_BACK_EDGES)
    if forbidden:
        errors.append(
            "DEPENDENCY_BACK_EDGE:"
            + ",".join(f"{source}->{target}" for source, target in forbidden)
        )
    if order:
        positions = {node: index for index, node in enumerate(order)}
        violations = sorted(
            (source, target)
            for source, target in edges
            if positions.get(source, -1) >= positions.get(target, -1)
        )
        if violations:
            errors.append(
                "DEPENDENCY_CYCLE_OR_ORDER:"
                + ",".join(f"{source}->{target}" for source, target in violations)
            )
    return errors


def _validate_cases(value: object) -> list[str]:
    if type(value) is not list:
        return ["ACCEPTANCE_CASES_TYPE"]
    cases = cast(list[object], value)
    errors: list[str] = []
    ids: list[str] = []
    for index, item in enumerate(cases):
        if type(item) is not dict:
            errors.append(f"ACCEPTANCE_CASE_TYPE:{index}")
            continue
        case = cast(dict[str, object], item)
        case_id = case.get("id")
        label = case_id if type(case_id) is str else str(index)
        if set(case) != CASE_FIELDS:
            errors.append(
                _field_error(f"ACCEPTANCE_CASE_FIELDS:{label}", set(case), CASE_FIELDS)
            )
            continue
        if type(case_id) is not str:
            errors.append(f"ACCEPTANCE_CASE_ID:{index}")
            continue
        ids.append(case_id)
        for field in ("counterexample", "given", "invariant", "then", "title", "when"):
            if type(case.get(field)) is not str or not cast(str, case[field]):
                errors.append(f"ACCEPTANCE_CASE_TEXT:{case_id}:{field}")
        if case.get("status") != "design_ready":
            errors.append(f"ACCEPTANCE_CASE_STATUS:{case_id}")
        nonclaims = _exact_string_list(case.get("nonclaims"))
        if nonclaims is None or not nonclaims:
            errors.append(f"ACCEPTANCE_CASE_NONCLAIMS:{case_id}")
    if len(ids) != len(set(ids)):
        duplicates = sorted(key for key, count in Counter(ids).items() if count > 1)
        errors.append(f"ACCEPTANCE_CASE_DUPLICATE:{','.join(duplicates)}")
    actual = set(ids)
    if actual != REQUIRED_CASE_IDS:
        errors.append(_field_error("ACCEPTANCE_CASE_IDS", actual, REQUIRED_CASE_IDS))
    return errors


def validate_contract(
    contract: dict[str, object],
    *,
    repo_root: Path = REPO_ROOT,
) -> list[str]:
    """Return stable errors for one already decoded contract."""

    errors: list[str] = []
    if set(contract) != ROOT_FIELDS:
        errors.append(_field_error("ROOT_FIELDS", set(contract), ROOT_FIELDS))
    if contract.get("schema") != SCHEMA:
        errors.append("SCHEMA")
    if contract.get("contract_version") != "1.0.0":
        errors.append("CONTRACT_VERSION")
    if contract.get("status") != "draft_for_independent_review_unmounted":
        errors.append("STATUS")
    if contract.get("implementation_authorized") is not False:
        errors.append("IMPLEMENTATION_AUTHORITY")
    if contract.get("mount_authorized") is not False:
        errors.append("MOUNT_AUTHORITY")
    errors.extend(_validate_sources(contract.get("normative_source"), repo_root=repo_root))
    errors.extend(_validate_decision(contract.get("decision")))
    errors.extend(_validate_graph(contract.get("dependency_graph")))
    errors.extend(_validate_cases(contract.get("acceptance_cases")))
    if _exact_string_list(contract.get("no_successor_outputs")) != NO_SUCCESSOR_OUTPUTS:
        errors.append("NO_SUCCESSOR_OUTPUTS")
    source_roles = contract.get("source_roles")
    if source_roles != SOURCE_ROLES:
        actual = set(source_roles) if type(source_roles) is dict else set()
        if actual != SOURCE_ROLE_FIELDS:
            errors.append(_field_error("SOURCE_ROLE_FIELDS", actual, SOURCE_ROLE_FIELDS))
        errors.append("SOURCE_ROLES")
        if (
            type(source_roles) is dict
            and source_roles.get("submitted_roots") != "equality targets only"
        ):
            errors.append("SUBMITTED_ROOT_AUTHORITY")
    cardinality = contract.get("claim_cardinality_policy")
    expected_cardinality = {
        "empty_tuple_allowed": True,
        "positive_fee_emits_exactly_one_claim": True,
        "zero_fee_emits_claim": False,
    }
    if cardinality != expected_cardinality:
        errors.append("CLAIM_CARDINALITY_POLICY")
    nonclaims = _exact_string_list(contract.get("nonclaims"))
    if nonclaims != NONCLAIMS:
        errors.append("NONCLAIMS")
    return sorted(set(errors))


def _report(path: Path) -> tuple[int, dict[str, object]]:
    try:
        contract = _load_contract(path)
        errors = validate_contract(contract)
    except (DuplicateJsonMember, OSError, UnicodeError, ValueError) as exc:
        errors = [f"CONTRACT_INVALID:{type(exc).__name__}:{exc}"]
        contract = {}
    report: dict[str, object] = {
        "acceptance_case_count": len(contract.get("acceptance_cases", []))
        if type(contract.get("acceptance_cases")) is list
        else 0,
        "errors": errors,
        "implementation_authorized": contract.get("implementation_authorized"),
        "mount_authorized": contract.get("mount_authorized"),
        "ok": not errors,
        "schema": contract.get("schema"),
        "status": contract.get("status"),
    }
    return (0 if not errors else 1), report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    args = parser.parse_args()
    code, report = _report(args.contract)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
