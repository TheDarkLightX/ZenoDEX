"""Closed model and parsers for the Test Quality Contract V2 overlay."""

from __future__ import annotations

import dataclasses
import datetime as dt
import re
from pathlib import Path
from typing import Any, Mapping, cast

from tools.test_hygiene_model_v1 import (
    REPO_ROOT,
    TestHygieneError,
    exact_fields,
    load_json,
    object_value,
    portable_path,
    require,
    string_list,
    string_value,
)

DEFAULT_CONTRACT = Path(__file__).with_name("test_quality_contract_v2.json")
DEFAULT_EVIDENCE_DIR = REPO_ROOT / "tests/evidence/test_quality"
CONTRACT_SCHEMA = "zenodex/test-quality-contract/v2"
EVIDENCE_SCHEMA = "zenodex/test-quality-evidence/v2"

_QUALITY_ID_RE = re.compile(r"TQV2-[0-9]{8}-[a-z0-9][a-z0-9-]*")
_HYGIENE_ID_RE = re.compile(r"THV1-[0-9]{8}-[a-z0-9][a-z0-9-]*")
_DECISIONS = frozenset({"applied", "not_applicable"})
_REPRESENTATION_STATUSES = frozenset(
    {"unrepresentable", "guarded", "representable", "not_applicable"}
)
_COUNTEREXAMPLE_STATUSES = frozenset({"retained", "not_applicable"})

_CONTRACT_FIELDS = frozenset(
    {
        "schema",
        "evidence_schema",
        "evidence_path_prefix",
        "hygiene_contract_path",
        "allowed_authority_tiers",
        "allowed_techniques",
        "allowed_falsifier_kinds",
        "allowed_falsifier_statuses",
        "quality_requirements",
    }
)
_REQUIREMENT_FIELDS = frozenset({"rule_id", "minimum_oracle_grade", "required_falsifier_kinds"})
_PACKET_FIELDS = frozenset(
    {
        "schema",
        "evidence_id",
        "created_date",
        "hygiene_evidence_id",
        "claim",
        "promotion_scope",
        "authority_tier",
        "authority_surface",
        "failure_model",
        "ripr",
        "representation_review",
        "technique",
        "oracle",
        "falsifiers",
        "minimal_test_inventory",
        "counterexample",
        "metrics",
        "review_decision",
        "nonclaims",
    }
)


@dataclasses.dataclass(frozen=True, slots=True)
class QualityRequirementV2:
    rule_id: str
    minimum_oracle_grade: int
    required_falsifier_kinds: frozenset[str]


@dataclasses.dataclass(frozen=True, slots=True)
class QualityContractV2:
    evidence_path_prefix: str
    hygiene_contract_path: str
    authority_tiers: frozenset[str]
    techniques: frozenset[str]
    falsifier_kinds: frozenset[str]
    falsifier_statuses: frozenset[str]
    requirements: tuple[QualityRequirementV2, ...]

    def requirement_for(self, rule_id: str) -> QualityRequirementV2:
        requirement = next((item for item in self.requirements if item.rule_id == rule_id), None)
        require(requirement is not None, f"quality contract: unknown rule id {rule_id}")
        return cast(QualityRequirementV2, requirement)


@dataclasses.dataclass(frozen=True, slots=True)
class FalsifierV2:
    falsifier_id: str
    kind: str
    status: str
    semantic_change: str
    killed_by_node_ids: tuple[str, ...]


@dataclasses.dataclass(frozen=True, slots=True)
class QualityPacketV2:
    path: Path
    evidence_id: str
    hygiene_evidence_id: str
    authority_tier: str
    oracle_grade: int
    reject_is_noop_status: str
    falsifiers: tuple[FalsifierV2, ...]


def _text(value: object, *, context: str, minimum_length: int = 12) -> str:
    result = string_value(value, context=context)
    require(
        len(result) >= minimum_length,
        f"{context}: explanation is too short to be reviewable",
    )
    require(
        result.strip().lower() not in {"n/a", "none", "todo", "tbd", "replace-me"},
        f"{context}: placeholder value",
    )
    return result


def _unique_objects(value: object, *, context: str) -> list[Mapping[str, Any]]:
    require(type(value) is list and bool(value), f"{context}: expected non-empty list")
    return [
        object_value(item, context=f"{context}[{index}]")
        for index, item in enumerate(cast(list[object], value))
    ]


def load_quality_contract(path: Path) -> QualityContractV2:
    raw = load_json(path, context="quality contract")
    exact_fields(raw, _CONTRACT_FIELDS, context="quality contract")
    require(raw["schema"] == CONTRACT_SCHEMA, "quality contract: schema mismatch")
    require(
        raw["evidence_schema"] == EVIDENCE_SCHEMA,
        "quality contract: evidence schema mismatch",
    )
    evidence_prefix = string_value(
        raw["evidence_path_prefix"], context="quality contract.evidence_path_prefix"
    )
    require(
        evidence_prefix.endswith("/"),
        "quality contract.evidence_path_prefix: must end with '/'",
    )
    portable_path(evidence_prefix[:-1], context="quality contract.evidence_path_prefix")
    hygiene_contract_path = portable_path(
        raw["hygiene_contract_path"],
        context="quality contract.hygiene_contract_path",
    )
    authority_tiers = frozenset(
        string_list(
            raw["allowed_authority_tiers"],
            context="quality contract.allowed_authority_tiers",
        )
    )
    techniques = frozenset(
        string_list(
            raw["allowed_techniques"],
            context="quality contract.allowed_techniques",
        )
    )
    falsifier_kinds = frozenset(
        string_list(
            raw["allowed_falsifier_kinds"],
            context="quality contract.allowed_falsifier_kinds",
        )
    )
    falsifier_statuses = frozenset(
        string_list(
            raw["allowed_falsifier_statuses"],
            context="quality contract.allowed_falsifier_statuses",
        )
    )
    requirements = _parse_requirements(raw["quality_requirements"], falsifier_kinds=falsifier_kinds)
    return QualityContractV2(
        evidence_path_prefix=evidence_prefix,
        hygiene_contract_path=hygiene_contract_path,
        authority_tiers=authority_tiers,
        techniques=techniques,
        falsifier_kinds=falsifier_kinds,
        falsifier_statuses=falsifier_statuses,
        requirements=requirements,
    )


def _parse_requirements(
    value: object, *, falsifier_kinds: frozenset[str]
) -> tuple[QualityRequirementV2, ...]:
    rows = _unique_objects(value, context="quality contract.quality_requirements")
    result: list[QualityRequirementV2] = []
    for index, row in enumerate(rows):
        context = f"quality contract.quality_requirements[{index}]"
        exact_fields(row, _REQUIREMENT_FIELDS, context=context)
        grade = row["minimum_oracle_grade"]
        require(
            type(grade) is int and 0 <= grade <= 4,
            f"{context}.minimum_oracle_grade: expected integer from 0 through 4",
        )
        required_kinds = frozenset(
            string_list(
                row["required_falsifier_kinds"],
                context=f"{context}.required_falsifier_kinds",
                minimum_items=0,
            )
        )
        require(
            required_kinds <= falsifier_kinds,
            f"{context}: unsupported required falsifier kind",
        )
        result.append(
            QualityRequirementV2(
                rule_id=string_value(row["rule_id"], context=f"{context}.rule_id"),
                minimum_oracle_grade=cast(int, grade),
                required_falsifier_kinds=required_kinds,
            )
        )
    rule_ids = [item.rule_id for item in result]
    require(len(rule_ids) == len(set(rule_ids)), "quality contract: duplicate rule ids")
    return tuple(result)


def load_quality_packet(path: Path, contract: QualityContractV2) -> QualityPacketV2:
    context = path.name
    raw = load_json(path, context=context)
    exact_fields(raw, _PACKET_FIELDS, context=context)
    require(raw["schema"] == EVIDENCE_SCHEMA, f"{context}: schema mismatch")
    evidence_id = string_value(raw["evidence_id"], context=f"{context}.evidence_id")
    require(_QUALITY_ID_RE.fullmatch(evidence_id) is not None, f"{context}: invalid evidence id")
    require(path.stem == evidence_id, f"{context}: filename must equal evidence id")
    try:
        dt.date.fromisoformat(string_value(raw["created_date"], context=f"{context}.created_date"))
    except ValueError as exc:
        raise TestHygieneError(f"{context}: invalid created_date") from exc
    hygiene_id = string_value(raw["hygiene_evidence_id"], context=f"{context}.hygiene_evidence_id")
    require(
        _HYGIENE_ID_RE.fullmatch(hygiene_id) is not None, f"{context}: invalid hygiene evidence id"
    )
    _text(raw["claim"], context=f"{context}.claim")
    _text(raw["promotion_scope"], context=f"{context}.promotion_scope")
    authority_tier = string_value(raw["authority_tier"], context=f"{context}.authority_tier")
    require(authority_tier in contract.authority_tiers, f"{context}: unsupported authority tier")
    string_list(raw["authority_surface"], context=f"{context}.authority_surface")
    _parse_failure_model(raw["failure_model"], context=f"{context}.failure_model")
    _parse_ripr(raw["ripr"], context=f"{context}.ripr")
    _parse_representation_review(
        raw["representation_review"], context=f"{context}.representation_review"
    )
    _parse_technique(raw["technique"], context=f"{context}.technique", contract=contract)
    oracle_grade, reject_status = _parse_oracle(raw["oracle"], context=f"{context}.oracle")
    falsifiers = _parse_falsifiers(
        raw["falsifiers"], context=f"{context}.falsifiers", contract=contract
    )
    _parse_minimal_inventory(
        raw["minimal_test_inventory"], context=f"{context}.minimal_test_inventory"
    )
    _parse_counterexample(raw["counterexample"], context=f"{context}.counterexample")
    _parse_metrics(raw["metrics"], context=f"{context}.metrics")
    _parse_review(raw["review_decision"], context=f"{context}.review_decision")
    string_list(raw["nonclaims"], context=f"{context}.nonclaims")
    return QualityPacketV2(
        path=path,
        evidence_id=evidence_id,
        hygiene_evidence_id=hygiene_id,
        authority_tier=authority_tier,
        oracle_grade=oracle_grade,
        reject_is_noop_status=reject_status,
        falsifiers=falsifiers,
    )


def _parse_failure_model(value: object, *, context: str) -> None:
    rows = _unique_objects(value, context=context)
    ids: list[str] = []
    for index, row in enumerate(rows):
        item_context = f"{context}[{index}]"
        exact_fields(
            row,
            frozenset({"id", "description", "severity", "coordinate_changed"}),
            context=item_context,
        )
        ids.append(string_value(row["id"], context=f"{item_context}.id"))
        _text(row["description"], context=f"{item_context}.description")
        severity = string_value(row["severity"], context=f"{item_context}.severity")
        require(
            severity in {"critical", "high", "medium", "low"}, f"{item_context}: invalid severity"
        )
        _text(row["coordinate_changed"], context=f"{item_context}.coordinate_changed")
    require(len(ids) == len(set(ids)), f"{context}: duplicate fault ids")


def _parse_ripr(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    fields = frozenset({"reach", "infect", "propagate", "reveal"})
    exact_fields(raw, fields, context=context)
    for field in sorted(fields):
        _text(raw[field], context=f"{context}.{field}")


def _parse_representation_review(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(
        raw,
        frozenset(
            {
                "invalid_state_status",
                "action",
                "semantic_source_multiplicity",
                "independent_oracle_exception",
            }
        ),
        context=context,
    )
    status = string_value(raw["invalid_state_status"], context=f"{context}.invalid_state_status")
    require(status in _REPRESENTATION_STATUSES, f"{context}: invalid representation status")
    _text(raw["action"], context=f"{context}.action")
    multiplicity = raw["semantic_source_multiplicity"]
    require(
        type(multiplicity) is int and multiplicity >= 1,
        f"{context}: invalid semantic source multiplicity",
    )
    require(
        type(raw["independent_oracle_exception"]) is bool,
        f"{context}: independent_oracle_exception must be boolean",
    )


def _parse_technique(value: object, *, context: str, contract: QualityContractV2) -> None:
    raw = object_value(value, context=context)
    exact_fields(raw, frozenset({"primary", "secondary", "rejected_alternatives"}), context=context)
    primary = string_value(raw["primary"], context=f"{context}.primary")
    require(primary in contract.techniques, f"{context}: unsupported primary technique")
    secondary = string_list(raw["secondary"], context=f"{context}.secondary", minimum_items=0)
    require(set(secondary) <= contract.techniques, f"{context}: unsupported secondary technique")
    require(primary not in secondary, f"{context}: primary technique repeated as secondary")
    alternatives = _unique_objects(
        raw["rejected_alternatives"], context=f"{context}.rejected_alternatives"
    )
    for index, row in enumerate(alternatives):
        item_context = f"{context}.rejected_alternatives[{index}]"
        exact_fields(row, frozenset({"technique", "reason"}), context=item_context)
        alternative = string_value(row["technique"], context=f"{item_context}.technique")
        require(alternative in contract.techniques, f"{item_context}: unsupported technique")
        _text(row["reason"], context=f"{item_context}.reason")


def _parse_oracle(value: object, *, context: str) -> tuple[int, str]:
    raw = object_value(value, context=context)
    exact_fields(
        raw,
        frozenset(
            {
                "description",
                "independence_grade",
                "independent_source",
                "exact_error_or_precedence",
                "reject_is_noop",
            }
        ),
        context=context,
    )
    _text(raw["description"], context=f"{context}.description")
    grade = raw["independence_grade"]
    require(type(grade) is int and 0 <= grade <= 4, f"{context}: invalid independence grade")
    _text(raw["independent_source"], context=f"{context}.independent_source")
    _text(raw["exact_error_or_precedence"], context=f"{context}.exact_error_or_precedence")
    decision = object_value(raw["reject_is_noop"], context=f"{context}.reject_is_noop")
    exact_fields(
        decision,
        frozenset({"status", "reason", "snapshot_fields"}),
        context=f"{context}.reject_is_noop",
    )
    status = string_value(decision["status"], context=f"{context}.reject_is_noop.status")
    require(status in _DECISIONS, f"{context}: invalid reject-is-no-op decision")
    _text(decision["reason"], context=f"{context}.reject_is_noop.reason")
    snapshot_fields = string_list(
        decision["snapshot_fields"],
        context=f"{context}.reject_is_noop.snapshot_fields",
        minimum_items=1 if status == "applied" else 0,
    )
    require(
        status == "applied" or not snapshot_fields,
        f"{context}: inapplicable reject decision cannot name snapshots",
    )
    return cast(int, grade), status


def _parse_falsifiers(
    value: object, *, context: str, contract: QualityContractV2
) -> tuple[FalsifierV2, ...]:
    rows = _unique_objects(value, context=context)
    result: list[FalsifierV2] = []
    for index, row in enumerate(rows):
        item_context = f"{context}[{index}]"
        exact_fields(
            row,
            frozenset(
                {
                    "id",
                    "kind",
                    "status",
                    "semantic_change",
                    "killed_by_node_ids",
                    "result",
                    "smallest_witness",
                }
            ),
            context=item_context,
        )
        kind = string_value(row["kind"], context=f"{item_context}.kind")
        status = string_value(row["status"], context=f"{item_context}.status")
        require(kind in contract.falsifier_kinds, f"{item_context}: unsupported falsifier kind")
        require(
            status in contract.falsifier_statuses, f"{item_context}: unsupported falsifier status"
        )
        if kind == "mutation":
            require(status == "killed", f"{item_context}: mutation must have killed status")
        result.append(
            FalsifierV2(
                falsifier_id=string_value(row["id"], context=f"{item_context}.id"),
                kind=kind,
                status=status,
                semantic_change=_text(
                    row["semantic_change"], context=f"{item_context}.semantic_change"
                ),
                killed_by_node_ids=string_list(
                    row["killed_by_node_ids"], context=f"{item_context}.killed_by_node_ids"
                ),
            )
        )
        _text(row["result"], context=f"{item_context}.result")
        _text(row["smallest_witness"], context=f"{item_context}.smallest_witness")
    ids = [item.falsifier_id for item in result]
    require(len(ids) == len(set(ids)), f"{context}: duplicate falsifier ids")
    return tuple(result)


def _parse_minimal_inventory(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(
        raw, frozenset({"added", "merged_or_deleted", "protected", "rationale"}), context=context
    )
    added = string_list(raw["added"], context=f"{context}.added", minimum_items=0)
    protected = string_list(raw["protected"], context=f"{context}.protected", minimum_items=0)
    string_list(raw["merged_or_deleted"], context=f"{context}.merged_or_deleted", minimum_items=0)
    require(
        bool(added or protected), f"{context}: inventory must add or protect executable evidence"
    )
    _text(raw["rationale"], context=f"{context}.rationale")


def _parse_counterexample(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(
        raw,
        frozenset({"status", "rationale", "retained_path", "replay_command", "minimized_size"}),
        context=context,
    )
    status = string_value(raw["status"], context=f"{context}.status")
    require(status in _COUNTEREXAMPLE_STATUSES, f"{context}: invalid status")
    _text(raw["rationale"], context=f"{context}.rationale")
    retained_path = raw["retained_path"]
    replay_command = raw["replay_command"]
    minimized_size = raw["minimized_size"]
    if status == "retained":
        portable_path(retained_path, context=f"{context}.retained_path")
        _text(replay_command, context=f"{context}.replay_command")
        _text(minimized_size, context=f"{context}.minimized_size")
    else:
        require(
            retained_path is None and replay_command is None and minimized_size is None,
            f"{context}: inapplicable counterexample fields must be null",
        )


def _parse_metrics(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(
        raw,
        frozenset(
            {"production_sloc_delta", "test_sloc_delta", "support_sloc_delta", "runtime_delta"}
        ),
        context=context,
    )
    for field in ("production_sloc_delta", "test_sloc_delta", "support_sloc_delta"):
        require(type(raw[field]) is int, f"{context}.{field}: expected integer")
    _text(raw["runtime_delta"], context=f"{context}.runtime_delta")


def _parse_review(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(raw, frozenset({"ready", "blockers"}), context=context)
    require(raw["ready"] is True, f"{context}: ready must be true")
    blockers = string_list(raw["blockers"], context=f"{context}.blockers", minimum_items=0)
    require(not blockers, f"{context}: ready evidence cannot retain blockers")


def load_quality_packets(
    evidence_dir: Path, contract: QualityContractV2
) -> tuple[QualityPacketV2, ...]:
    if not evidence_dir.exists():
        return ()
    require(evidence_dir.is_dir(), f"quality evidence path is not a directory: {evidence_dir}")
    packets = tuple(
        load_quality_packet(path, contract) for path in sorted(evidence_dir.glob("TQV2-*.json"))
    )
    ids = [packet.evidence_id for packet in packets]
    hygiene_ids = [packet.hygiene_evidence_id for packet in packets]
    require(len(ids) == len(set(ids)), "duplicate quality evidence ids")
    require(
        len(hygiene_ids) == len(set(hygiene_ids)), "duplicate quality packet for hygiene evidence"
    )
    return packets
