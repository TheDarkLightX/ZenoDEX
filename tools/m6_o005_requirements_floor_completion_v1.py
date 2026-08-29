"""Pure core for the narrow, source-pinned O-005 requirements-floor certificate.

This module has no filesystem, Git, release, settlement, or value-moving
authority.  Its caller supplies an immutable snapshot of the exact evidence
subject.  The core derives the certificate from those bytes and rejects every
alternate representation, promotion, or source binding.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Final, NoReturn

try:
    from tools.m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )
except ModuleNotFoundError:
    from m6_normative_requirements_v1 import (
        RequirementsRejectV1,
        canonical_json_bytes_v1,
        decode_json_object_v1,
    )


ARTIFACT_SCHEMA_V1: Final = "zenodex/m6-o005-requirements-floor-completion/v1"
CHECK_SCHEMA_V1: Final = "zenodex/m6-o005-requirements-floor-completion-check/v1"
GENERATOR_COMMAND_V1: Final = "python3 tools/build_m6_o005_requirements_floor_completion_v1.py"

EVIDENCE_SUBJECT_COMMIT_V1: Final = "5ffc76e784db3d0cc05a90c4d002e805f8724fe2"
EVIDENCE_SUBJECT_TREE_V1: Final = "90b60bfaaabd7306dd94e88030fbb00e9a331afb"
ADMITTED_PLAN_COMMIT_V1: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ADMITTED_PLAN_PARENT_V1: Final = "87048abf3bed2adba0e316e4f9c2ea93f438aeb6"
ADMITTED_PLAN_TREE_V1: Final = "7978c0df78428e806e5f19281df537fe1cfc7451"

PLAN_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_ADMISSION_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
ACTIVE_PLAN_PATH_V1: Final = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
NORMATIVE_ARTIFACT_PATH_V1: Final = "docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json"
RESOLUTION_ARTIFACT_PATH_V1: Final = "docs/research/M6_O005_SEMANTIC_RESOLUTIONS_V1.json"

PLAN_SHA256_V1: Final = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
NORMATIVE_ARTIFACT_SHA256_V1: Final = (
    "29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f"
)
NORMATIVE_REGISTRY_ROOT_V1: Final = (
    "971e7c5e277697d0bc833a8016f2d47bbbd17c3b4e5c0762990d13772808a3e6"
)
RESOLUTION_ARTIFACT_SHA256_V1: Final = (
    "001ddc29a48275ddae0a93b180ef827b0488b55ea97485810ca0a4a246a48341"
)
RESOLUTION_REGISTRY_ROOT_V1: Final = (
    "878b2d51ff7fa0637f558019de872c85268a75082c0d3cfb2bf96cd415e5adff"
)

MAX_ARTIFACT_BYTES_V1: Final = 131_072
MAX_EVIDENCE_FILE_BYTES_V1: Final = 1_048_576
MAX_EVIDENCE_FILE_PINS_V1: Final = 16
MAX_REQUIREMENT_ROWS_V1: Final = 256
MAX_ROW_EDGES_V1: Final = 256
MAX_RESOLUTION_ROWS_V1: Final = 32
MAX_ROUTE_ROWS_V1: Final = 16

_SHA1_RE: Final = re.compile(r"^[0-9a-f]{40}$")
_REQUIRED_ROW_COUNTS_V1: Final = {
    "WORKFLOW": 18,
    "BDD": 81,
    "REQUIRED_SPEC_EXPANSION": 11,
    "CONFIRMED_FINDING": 8,
    "UNRESOLVED_POLICY": 20,
}
_ALL_NORMATIVE_ROW_COUNTS_V1: Final = {**_REQUIRED_ROW_COUNTS_V1, "INVARIANT": 14}
_REQUIRED_ROW_TOTAL_V1: Final = sum(_REQUIRED_ROW_COUNTS_V1.values())
_UP_IDS_V1: Final = tuple(f"UP-{ordinal:02d}" for ordinal in range(1, 21))
_UP_STATUS_V1: Final = "UNRESOLVED_POLICY_NOT_SELECTABLE"
_OPEN_VM_GATE_STATUSES_V1: Final = frozenset({"GAP", "PARTIAL_REQUIRES_CURRENT_RECONCILIATION"})
_CEILING_FALSE_FIELDS_V1: Final = (
    "manifest_complete",
    "requirements_closed",
    "semantic_target_inventory_complete",
    "semantic_capability_coverage_complete",
    "structural_mapping_complete",
    "semantic_closure_complete",
    "value_movement_claim_allowed",
)
_AUTHORITY_NONE_FIELDS_V1: Final = (
    "production_authority",
    "settlement_authority",
    "release_authority",
    "migration_authority",
    "value_movement_authority",
)
_ROW_FIELDS_V1: Final = frozenset(
    {
        "edges",
        "kind",
        "parent_requirement_id",
        "requirement_id",
        "source_document",
        "source_fields",
        "status",
    }
)
_EDGE_FIELDS_V1: Final = frozenset({"relation_type", "target_id"})
_RESOLUTION_ROW_FIELDS_V1: Final = frozenset(
    {
        "blockers",
        "disposition",
        "lane_id",
        "policy_rules",
        "resolution_id",
        "resolution_kind",
        "source_missing_target_concept_id",
        "target_id",
    }
)
_ROUTE_ROW_FIELDS_V1: Final = frozenset(
    {
        "blockers",
        "disposition",
        "forbidden_substitutions",
        "missing_workflow_bdd",
        "requires_source_split",
        "resolution_id",
        "retained_supply_policy",
        "route_steps",
        "source_route_id",
    }
)
_CERTIFICATE_FIELDS_V1: Final = frozenset(
    {
        "admitted_plan",
        "certificate_root",
        "claim_ceiling",
        "evidence_subject",
        "generator_command",
        "nonclaims",
        "o005_completion",
        "requirements_floor",
        "resolution_bijections",
        "schema",
        "source_artifacts",
        "source_file_pins",
        "status",
    }
)


@dataclass(frozen=True)
class CompletionRejectV1(ValueError):
    """Stable fail-closed rejection for this certificate boundary."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CompletionRejectV1(code, path, detail)


@dataclass(frozen=True)
class EvidenceFilePinV1:
    """Exact Git and content binding for a source file at the evidence subject."""

    path: str
    git_blob_sha: str
    sha256: str

    def to_json(self) -> dict[str, str]:
        return {"git_blob_sha": self.git_blob_sha, "path": self.path, "sha256": self.sha256}


EVIDENCE_FILE_PINS_V1: Final[tuple[EvidenceFilePinV1, ...]] = (
    EvidenceFilePinV1(PLAN_PATH_V1, "6da997fe32f39a4c1bf0c89a3f6dfc87a16f863f", PLAN_SHA256_V1),
    EvidenceFilePinV1(
        NORMATIVE_ARTIFACT_PATH_V1,
        "289fd40f77c9edbf30187676a00eddf0f9fca27e",
        NORMATIVE_ARTIFACT_SHA256_V1,
    ),
    EvidenceFilePinV1(
        RESOLUTION_ARTIFACT_PATH_V1,
        "4a92cd9a629dd04ed40eb2bc1661f83fb1ae3847",
        RESOLUTION_ARTIFACT_SHA256_V1,
    ),
    EvidenceFilePinV1(
        "tools/m6_normative_requirements_decisions_v1.py",
        "287a3163fd778e87db67b2f7a1ebdef0f87c5496",
        "892f0afb22abba446545880de2ffbcf2effe15956671df1ba90708e299a2e8bd",
    ),
    EvidenceFilePinV1(
        "tools/m6_normative_requirements_v1.py",
        "56d8657e34c1aa6e854914cb153c3fc2838b53bc",
        "519ded69a8d537543056c6561e864323f3b27ecc6fcde227891b8b03250a6039",
    ),
    EvidenceFilePinV1(
        "tools/build_m6_normative_requirements_v1.py",
        "8d56cdeb9141bd0b5fbcebe89ac7bb1044c821e1",
        "c27fe1dcb6b5ca6f583cbb30d82d33b413288f823ada7c74448f4d163a8e93b8",
    ),
    EvidenceFilePinV1(
        "tools/check_m6_normative_requirements_v1.py",
        "7dc31a2f07ad80ea9c105a932e3b4b0191475b5e",
        "0b153c6de3f59685db8909c239dd5fb75abeb8ed330f8481fcf8c0114edaa177",
    ),
    EvidenceFilePinV1(
        "tests/test_check_m6_normative_requirements_v1.py",
        "d8a8d457cf1565f32d6e3b34acb7412b2c4e2c26",
        "01569b17ba01d8321323f96970e405f780840b36f3338d3e42fd800b216748e9",
    ),
    EvidenceFilePinV1(
        "tools/m6_o005_semantic_resolutions_v1.py",
        "aa4aa10b5b963932127c6c0480445bca64ab879a",
        "61c7c4324edbcd388e760a0b0920cf4871d12e2d5b72c6fb2037350b11938dfe",
    ),
    EvidenceFilePinV1(
        "tools/build_m6_o005_semantic_resolutions_v1.py",
        "a63414a83b41f8ee6a110a055f101013f2af596d",
        "07f3025aa6b445c311d79b8195cca531e3ac93274fbffda20258a26574e421f7",
    ),
    EvidenceFilePinV1(
        "tools/check_m6_o005_semantic_resolutions_v1.py",
        "f2de51c6b0ee4b3fc7c3f6c8282505f4d969f9d8",
        "95b6821b6380b45c7c47b54567c3b380bdd741124bf470911e9bb7fe8d396091",
    ),
    EvidenceFilePinV1(
        "tests/test_check_m6_o005_semantic_resolutions_v1.py",
        "e2278eff3aee8f0edfef7161973d28f00006aa4f",
        "a74b05eab145e426c6a00a725728be8b99d24c3875792d849c1c2c1a0b461999",
    ),
    EvidenceFilePinV1(
        PLAN_ADMISSION_PATH_V1,
        "6bc9bc54b5145bbc044312878600e651031ed28d",
        "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d",
    ),
    EvidenceFilePinV1(
        ACTIVE_PLAN_PATH_V1,
        "27bfcde8064a007b5c07fba8d6f09b8a8294e2bd",
        "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4",
    ),
)


@dataclass(frozen=True)
class SubjectEvidenceSnapshotV1:
    """Immutable shell-acquired snapshot consumed by the pure certificate core."""

    captured_git_head: str
    rechecked_git_head: str
    evidence_subject_is_current_ancestor: bool
    evidence_subject_tree: str
    source_subject_entries: tuple[tuple[str, str, str, str], ...]
    current_head_entries: tuple[tuple[str, str, str, str], ...]
    source_subject_bytes: tuple[tuple[str, bytes], ...]
    current_content_bytes: tuple[tuple[str, bytes], ...]


def _expect_object(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict:
        _reject("OBJECT_TYPE", path, "must be an exact object")
    return value


def _expect_list(value: object, path: str, maximum: int) -> list[object]:
    if type(value) is not list:
        _reject("LIST_TYPE", path, "must be an exact list")
    if len(value) > maximum:
        _reject("LIST_LIMIT", path, f"{len(value)}>{maximum}")
    return value


def _expect_str(value: object, path: str) -> str:
    if type(value) is not str or not value:
        _reject("STRING_TYPE", path, "must be a nonempty exact string")
    return value


def _expect_bool(value: object, path: str) -> bool:
    if type(value) is not bool:
        _reject("BOOL_TYPE", path, "must be an exact bool")
    return value


def _expect_int(value: object, path: str) -> int:
    if type(value) is not int:
        _reject("INTEGER_TYPE", path, "must be an exact int")
    return value


def _expect_exact_fields(value: dict[str, object], expected: frozenset[str], path: str) -> None:
    if frozenset(value) != expected:
        _reject("FIELD_SET", path, "unknown, missing, or duplicate semantic field")


def _canonical_bytes(value: object, path: str) -> bytes:
    try:
        return canonical_json_bytes_v1(value)
    except RequirementsRejectV1 as exc:
        _reject("CANONICAL_" + exc.code, path, "upstream canonical codec rejected value")


def _decode_canonical_object(raw: bytes, path: str, maximum: int) -> dict[str, object]:
    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", path, "must have exact bytes type")
    if len(raw) > maximum:
        _reject("JSON_BYTE_LIMIT", path, f"{len(raw)}>{maximum}")
    try:
        decoded = decode_json_object_v1(raw, path)
    except RequirementsRejectV1 as exc:
        _reject("JSON_" + exc.code, path, "upstream JSON boundary rejected input")
    if _canonical_bytes(decoded, path) != raw:
        _reject("JSON_NONCANONICAL", path, "must be exact canonical JSON bytes")
    return decoded


def _decode_hash_bound_object(raw: bytes, path: str, maximum: int) -> dict[str, object]:
    """Decode a pinned legacy JSON object without relaxing its byte binding.

    The admitted-plan receipt predates the canonical artifact ABI and is
    deliberately pretty-printed.  Its immutable subject SHA is checked before
    this helper runs, so this parser exists only to inspect its fixed semantics.
    """

    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", path, "must have exact bytes type")
    if len(raw) > maximum:
        _reject("JSON_BYTE_LIMIT", path, f"{len(raw)}>{maximum}")

    def reject_duplicate(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if type(key) is not str or key in result:
                _reject("JSON_DUPLICATE_KEY", path, "duplicate or non-string object key")
            result[key] = value
        return result

    def reject_float(value: str) -> NoReturn:
        _reject("JSON_FLOAT", path, f"floating point token is forbidden: {value[:32]}")

    def bounded_int(value: str) -> int:
        if len(value.lstrip("-")) > 256:
            _reject("JSON_INTEGER_LIMIT", path, "integer digit ceiling exceeded")
        return int(value)

    def reject_constant(value: str) -> NoReturn:
        _reject("JSON_NONFINITE", path, f"nonfinite token is forbidden: {value[:32]}")

    try:
        decoded = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=reject_duplicate,
            parse_constant=reject_constant,
            parse_float=reject_float,
            parse_int=bounded_int,
        )
    except CompletionRejectV1:
        raise
    except (UnicodeDecodeError, ValueError, json.JSONDecodeError) as exc:
        _reject("JSON_DECODE", path, f"{type(exc).__name__}: {str(exc)[:128]}")
    return _expect_object(decoded, path)


def _sha256(raw: bytes, path: str) -> str:
    if type(raw) is not bytes:
        _reject("BYTES_TYPE", path, "must have exact bytes type")
    return hashlib.sha256(raw).hexdigest()


def _require_unique(values: tuple[str, ...], path: str) -> None:
    if len(values) != len(set(values)):
        _reject("DUPLICATE_ID", path, "duplicate identifier")


def _ids_root(values: tuple[str, ...], path: str) -> str:
    return _sha256(_canonical_bytes(list(values), path), path)


def _snapshot_bytes(snapshot: SubjectEvidenceSnapshotV1, current: bool) -> dict[str, bytes]:
    rows = snapshot.current_content_bytes if current else snapshot.source_subject_bytes
    if type(rows) is not tuple or len(rows) != len(EVIDENCE_FILE_PINS_V1):
        _reject("SNAPSHOT_FILE_COUNT", "snapshot.bytes", "unexpected evidence-file count")
    result: dict[str, bytes] = {}
    for index, row in enumerate(rows):
        if type(row) is not tuple or len(row) != 2:
            _reject("SNAPSHOT_FILE_ROW", f"snapshot.bytes[{index}]", "must be a path/bytes pair")
        path, raw = row
        expected = EVIDENCE_FILE_PINS_V1[index]
        if type(path) is not str or path != expected.path or type(raw) is not bytes:
            _reject("SNAPSHOT_FILE_ROW", f"snapshot.bytes[{index}]", "path or bytes binding drift")
        if len(raw) > MAX_EVIDENCE_FILE_BYTES_V1:
            _reject("SNAPSHOT_FILE_LIMIT", path, "source exceeds byte ceiling")
        result[path] = raw
    return result


def _validate_snapshot_v1(snapshot: SubjectEvidenceSnapshotV1) -> dict[str, bytes]:
    if type(snapshot) is not SubjectEvidenceSnapshotV1:
        _reject("SNAPSHOT_TYPE", "snapshot", "must be an exact SubjectEvidenceSnapshotV1")
    for field_name in ("captured_git_head", "rechecked_git_head"):
        value = getattr(snapshot, field_name)
        if type(value) is not str or _SHA1_RE.fullmatch(value) is None:
            _reject(
                "SNAPSHOT_HEAD_TYPE",
                f"snapshot.{field_name}",
                "must be an exact lowercase Git object ID",
            )
    if snapshot.captured_git_head != snapshot.rechecked_git_head:
        _reject("HEAD_CHANGED", "snapshot.git_head", "head changed during snapshot capture")
    if type(snapshot.evidence_subject_is_current_ancestor) is not bool:
        _reject("ANCESTRY_TYPE", "snapshot.ancestry", "must be an exact bool")
    if not snapshot.evidence_subject_is_current_ancestor:
        _reject(
            "SUBJECT_NOT_ANCESTOR", "snapshot.ancestry", "evidence subject is not current ancestor"
        )
    if (
        type(snapshot.evidence_subject_tree) is not str
        or _SHA1_RE.fullmatch(snapshot.evidence_subject_tree) is None
        or snapshot.evidence_subject_tree != EVIDENCE_SUBJECT_TREE_V1
    ):
        _reject("SUBJECT_TREE", "snapshot.tree", "exact evidence tree drift")

    expected_entries = tuple(
        (pin.path, "100644", "blob", pin.git_blob_sha) for pin in EVIDENCE_FILE_PINS_V1
    )
    for label, entries in (
        ("source_subject_entries", snapshot.source_subject_entries),
        ("current_head_entries", snapshot.current_head_entries),
    ):
        if type(entries) is not tuple or len(entries) != len(expected_entries):
            _reject("GIT_BLOB_BINDING", f"snapshot.{label}", "exact Git blob rows drift")
        for index, (entry, expected) in enumerate(zip(entries, expected_entries, strict=True)):
            if type(entry) is not tuple or len(entry) != 4:
                _reject(
                    "GIT_BLOB_BINDING",
                    f"snapshot.{label}[{index}]",
                    "Git entry must be an exact four-string row",
                )
            if any(type(component) is not str for component in entry) or entry != expected:
                _reject(
                    "GIT_BLOB_BINDING",
                    f"snapshot.{label}[{index}]",
                    "exact Git blob row drift",
                )

    source_bytes = _snapshot_bytes(snapshot, current=False)
    current_bytes = _snapshot_bytes(snapshot, current=True)
    for pin in EVIDENCE_FILE_PINS_V1:
        if _sha256(source_bytes[pin.path], pin.path) != pin.sha256:
            _reject("SOURCE_SHA256", pin.path, "source-subject bytes drift")
        if current_bytes[pin.path] != source_bytes[pin.path]:
            _reject("CURRENT_CONTENT", pin.path, "current content differs from evidence subject")
    return source_bytes


def _certificate_root(unsigned: dict[str, object]) -> str:
    return _sha256(_canonical_bytes(unsigned, "certificate.unsigned"), "certificate.unsigned")


def _parse_admitted_plan_v1(source: dict[str, bytes]) -> dict[str, object]:
    receipt = _decode_hash_bound_object(
        source[PLAN_ADMISSION_PATH_V1], "admission_receipt", MAX_EVIDENCE_FILE_BYTES_V1
    )
    expected_receipt_fields = frozenset(
        {
            "admission_scope",
            "admitted_plan",
            "advisory_review",
            "authority",
            "nonclaims",
            "normative_inputs",
            "receipt_payload_sha256",
            "schema",
            "selection_premise",
            "status",
            "subject_files",
            "upstream_dependency_binding",
        }
    )
    _expect_exact_fields(receipt, expected_receipt_fields, "admission_receipt")
    if (
        _expect_str(receipt.get("schema"), "admission_receipt.schema")
        != "zenodex/plan-admission-receipt/v1"
    ):
        _reject("ADMISSION_SCHEMA", "admission_receipt.schema", "unexpected schema")
    if (
        _expect_str(receipt.get("status"), "admission_receipt.status")
        != "ADMITTED_RESEARCH_IMPLEMENTATION_PLAN"
    ):
        _reject("ADMISSION_STATUS", "admission_receipt.status", "plan is not admitted")
    payload = dict(receipt)
    payload_hash = _expect_str(
        payload.pop("receipt_payload_sha256"), "admission_receipt.receipt_payload_sha256"
    )
    if _certificate_root(payload) != payload_hash:
        _reject(
            "ADMISSION_ROOT", "admission_receipt.receipt_payload_sha256", "payload root mismatch"
        )
    admitted = _expect_object(receipt.get("admitted_plan"), "admission_receipt.admitted_plan")
    expected_admitted: dict[str, object] = {
        "commit": ADMITTED_PLAN_COMMIT_V1,
        "parent": ADMITTED_PLAN_PARENT_V1,
        "plan_path": PLAN_PATH_V1,
        "plan_sha256": PLAN_SHA256_V1,
        "schema": "zenodex/whole-program-plan/v2.1",
        "tree": ADMITTED_PLAN_TREE_V1,
    }
    if admitted != expected_admitted:
        _reject(
            "ADMITTED_PLAN_BINDING", "admission_receipt.admitted_plan", "exact admitted plan drift"
        )
    authority = _expect_object(receipt.get("authority"), "admission_receipt.authority")
    for field in _AUTHORITY_NONE_FIELDS_V1:
        if field == "migration_authority":
            continue
        if _expect_str(authority.get(field), f"admission_receipt.authority.{field}") != "NONE":
            _reject(
                "ADMISSION_AUTHORITY", f"admission_receipt.authority.{field}", "must remain NONE"
            )

    active = _decode_hash_bound_object(
        source[ACTIVE_PLAN_PATH_V1], "active_plan_registry", MAX_EVIDENCE_FILE_BYTES_V1
    )
    expected_active_fields = frozenset(
        {
            "active_plan_count",
            "active_plans",
            "authority",
            "nonclaim",
            "replacement_rule",
            "schema",
            "status",
        }
    )
    _expect_exact_fields(active, expected_active_fields, "active_plan_registry")
    if (
        _expect_str(active.get("schema"), "active_plan_registry.schema")
        != "zenodex/active-whole-program-plan-registry/v1"
    ):
        _reject("ACTIVE_PLAN_SCHEMA", "active_plan_registry.schema", "unexpected schema")
    if _expect_str(active.get("status"), "active_plan_registry.status") != "RESEARCH_ONLY":
        _reject("ACTIVE_PLAN_STATUS", "active_plan_registry.status", "must remain research-only")
    if _expect_int(active.get("active_plan_count"), "active_plan_registry.active_plan_count") != 1:
        _reject("ACTIVE_PLAN_COUNT", "active_plan_registry.active_plan_count", "must equal one")
    plans = _expect_list(active.get("active_plans"), "active_plan_registry.active_plans", 1)
    if (
        len(plans) != 1
        or _expect_object(plans[0], "active_plan_registry.active_plans[0]").get("plan_commit")
        != ADMITTED_PLAN_COMMIT_V1
    ):
        _reject(
            "ACTIVE_PLAN_BINDING",
            "active_plan_registry.active_plans",
            "admitted plan is not uniquely active",
        )
    return expected_admitted


def _parse_plan_baseline_v1(source: dict[str, bytes]) -> dict[str, object]:
    plan = _decode_hash_bound_object(
        source[PLAN_PATH_V1], "admitted_plan", MAX_EVIDENCE_FILE_BYTES_V1
    )
    if _expect_str(plan.get("schema"), "admitted_plan.schema") != "zenodex/whole-program-plan/v2.1":
        _reject("PLAN_SCHEMA", "admitted_plan.schema", "unexpected schema")
    if (
        _expect_str(plan.get("status"), "admitted_plan.status")
        != "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION"
    ):
        _reject("PLAN_STATUS", "admitted_plan.status", "must remain research-only candidate")
    gap_rows = _expect_list(plan.get("gap_registry"), "admitted_plan.gap_registry", 64)
    matching_gaps = [
        row
        for row in gap_rows
        if type(row) is dict and row.get("gap_id") == "incomplete_requirements_registry"
    ]
    if len(matching_gaps) != 1:
        _reject("PLAN_GAP_CARDINALITY", "admitted_plan.gap_registry", "must contain O-005 gap once")
    gap = _expect_object(matching_gaps[0], "admitted_plan.gap_registry[O-005]")
    if gap != {
        "gap_id": "incomplete_requirements_registry",
        "owner_obligation": "O-005",
        "status": "OPEN",
    }:
        _reject("PLAN_GAP_BASELINE", "admitted_plan.gap_registry[O-005]", "baseline gap drift")
    obligations = _expect_list(plan.get("next_obligations"), "admitted_plan.next_obligations", 64)
    matching_obligations = [
        row for row in obligations if type(row) is dict and row.get("obligation_id") == "O-005"
    ]
    if len(matching_obligations) != 1:
        _reject(
            "PLAN_O005_CARDINALITY", "admitted_plan.next_obligations", "must contain O-005 once"
        )
    o005 = _expect_object(matching_obligations[0], "admitted_plan.next_obligations[O-005]")
    if o005.get("closes") != ["incomplete_requirements_registry"]:
        _reject(
            "PLAN_O005_SCOPE", "admitted_plan.next_obligations[O-005].closes", "closure scope drift"
        )
    baseline = _expect_object(plan.get("baseline_verdict"), "admitted_plan.baseline_verdict")
    if (
        _expect_int(
            baseline.get("closed_value_movement_gates"),
            "admitted_plan.baseline_verdict.closed_value_movement_gates",
        )
        != 0
    ):
        _reject("PLAN_VM_PROMOTION", "admitted_plan.baseline_verdict", "must close zero VM gates")
    gates = _expect_list(plan.get("value_movement_gates"), "admitted_plan.value_movement_gates", 12)
    if len(gates) != 12:
        _reject(
            "PLAN_VM_GATE_COUNT", "admitted_plan.value_movement_gates", "must contain twelve gates"
        )
    for index, gate_value in enumerate(gates):
        gate = _expect_object(gate_value, f"admitted_plan.value_movement_gates[{index}]")
        status_path = f"admitted_plan.value_movement_gates[{index}].status"
        if _expect_str(gate.get("status"), status_path) not in _OPEN_VM_GATE_STATUSES_V1:
            _reject("PLAN_VM_PROMOTION", status_path, "gate status is not an allowed open state")
    return gap


def _derive_requirements_floor_v1(
    source: dict[str, bytes],
) -> tuple[dict[str, object], tuple[str, ...], tuple[str, ...]]:
    artifact = _decode_canonical_object(
        source[NORMATIVE_ARTIFACT_PATH_V1], "normative_artifact", MAX_EVIDENCE_FILE_BYTES_V1
    )
    if (
        _expect_str(artifact.get("schema"), "normative_artifact.schema")
        != "zenodex/m6-normative-requirements/v1"
    ):
        _reject("NORMATIVE_SCHEMA", "normative_artifact.schema", "unexpected schema")
    if (
        _expect_str(artifact.get("registry_root"), "normative_artifact.registry_root")
        != NORMATIVE_REGISTRY_ROOT_V1
    ):
        _reject("NORMATIVE_ROOT", "normative_artifact.registry_root", "registry root drift")
    for field in _CEILING_FALSE_FIELDS_V1:
        if _expect_bool(artifact.get(field), f"normative_artifact.{field}"):
            _reject("NORMATIVE_CEILING", f"normative_artifact.{field}", "must remain false")
    for field in ("production_authority", "settlement_authority"):
        if _expect_str(artifact.get(field), f"normative_artifact.{field}") != "NONE":
            _reject("NORMATIVE_AUTHORITY", f"normative_artifact.{field}", "must remain NONE")
    rows = _expect_list(artifact.get("rows"), "normative_artifact.rows", MAX_REQUIREMENT_ROWS_V1)
    if len(rows) != sum(_ALL_NORMATIVE_ROW_COUNTS_V1.values()):
        _reject("NORMATIVE_ROW_COUNT", "normative_artifact.rows", "unexpected total row count")
    row_counts = {kind: 0 for kind in _ALL_NORMATIVE_ROW_COUNTS_V1}
    edge_counts = {kind: 0 for kind in _REQUIRED_ROW_COUNTS_V1}
    row_ids: dict[str, list[str]] = {kind: [] for kind in _REQUIRED_ROW_COUNTS_V1}
    policy_ids: list[str] = []
    for index, row_value in enumerate(rows):
        row = _expect_object(row_value, f"normative_artifact.rows[{index}]")
        _expect_exact_fields(row, _ROW_FIELDS_V1, f"normative_artifact.rows[{index}]")
        kind = _expect_str(row.get("kind"), f"normative_artifact.rows[{index}].kind")
        if kind not in row_counts:
            _reject(
                "NORMATIVE_ROW_KIND", f"normative_artifact.rows[{index}].kind", "unknown row kind"
            )
        row_counts[kind] += 1
        requirement_id = _expect_str(
            row.get("requirement_id"), f"normative_artifact.rows[{index}].requirement_id"
        )
        edges = _expect_list(
            row.get("edges"), f"normative_artifact.rows[{index}].edges", MAX_ROW_EDGES_V1
        )
        for edge_index, edge_value in enumerate(edges):
            edge = _expect_object(
                edge_value, f"normative_artifact.rows[{index}].edges[{edge_index}]"
            )
            _expect_exact_fields(
                edge, _EDGE_FIELDS_V1, f"normative_artifact.rows[{index}].edges[{edge_index}]"
            )
            _expect_str(
                edge.get("relation_type"),
                f"normative_artifact.rows[{index}].edges[{edge_index}].relation_type",
            )
            _expect_str(
                edge.get("target_id"),
                f"normative_artifact.rows[{index}].edges[{edge_index}].target_id",
            )
        if kind in _REQUIRED_ROW_COUNTS_V1:
            if not edges:
                _reject(
                    "VACUOUS_EDGE",
                    f"normative_artifact.rows[{index}].edges",
                    "required row has no edge",
                )
            edge_counts[kind] += 1
            row_ids[kind].append(requirement_id)
            if kind == "UNRESOLVED_POLICY":
                if (
                    _expect_str(row.get("status"), f"normative_artifact.rows[{index}].status")
                    != _UP_STATUS_V1
                ):
                    _reject(
                        "UP_POLICY_STATUS",
                        f"normative_artifact.rows[{index}].status",
                        "policy became selectable",
                    )
                policy_ids.append(requirement_id)
    if row_counts != _ALL_NORMATIVE_ROW_COUNTS_V1:
        _reject("NORMATIVE_KIND_COUNTS", "normative_artifact.rows", "row-kind count drift")
    if edge_counts != _REQUIRED_ROW_COUNTS_V1:
        _reject("REQUIRED_EDGE_COUNTS", "normative_artifact.rows", "nonvacuous edge count drift")
    for kind, ids in row_ids.items():
        _require_unique(tuple(ids), f"normative_artifact.rows.{kind}")
    if tuple(policy_ids) != _UP_IDS_V1:
        _reject(
            "UP_POLICY_IDS",
            "normative_artifact.rows.UNRESOLVED_POLICY",
            "policy ID order or count drift",
        )

    targets = _expect_list(
        artifact.get("targets"), "normative_artifact.targets", MAX_REQUIREMENT_ROWS_V1
    )
    missing_ids: list[str] = []
    route_ids: list[str] = []
    for index, target_value in enumerate(targets):
        target = _expect_object(target_value, f"normative_artifact.targets[{index}]")
        target_type = _expect_str(
            target.get("target_type"), f"normative_artifact.targets[{index}].target_type"
        )
        if target_type == "MISSING_TARGET_CONCEPT":
            missing_ids.append(
                _expect_str(
                    target.get("missing_target_concept_id"),
                    f"normative_artifact.targets[{index}].missing_target_concept_id",
                )
            )
        elif target_type == "REQUIRED_ROUTE":
            route_ids.append(
                _expect_str(target.get("route_id"), f"normative_artifact.targets[{index}].route_id")
            )
    _require_unique(tuple(missing_ids), "normative_artifact.targets.missing_target_concept_id")
    _require_unique(tuple(route_ids), "normative_artifact.targets.route_id")
    if len(missing_ids) != 12 or len(route_ids) != 4:
        _reject(
            "NORMATIVE_TARGET_COUNTS",
            "normative_artifact.targets",
            "missing concept or route count drift",
        )
    requirements_floor = {
        "all_required_rows_have_nonvacuous_edge": True,
        "nonvacuous_edge_counts": edge_counts,
        "required_row_count": _REQUIRED_ROW_TOTAL_V1,
        "required_row_counts": _REQUIRED_ROW_COUNTS_V1,
        "required_row_ids_root": _ids_root(
            tuple(identifier for kind in _REQUIRED_ROW_COUNTS_V1 for identifier in row_ids[kind]),
            "requirements_floor.required_row_ids_root",
        ),
        "unresolved_policy_inventory_complete": True,
        "unresolved_policy_ids": list(policy_ids),
        "unresolved_policy_status": _UP_STATUS_V1,
    }
    return requirements_floor, tuple(missing_ids), tuple(route_ids)


def _derive_resolution_bijections_v1(
    source: dict[str, bytes], missing_ids: tuple[str, ...], route_ids: tuple[str, ...]
) -> dict[str, object]:
    artifact = _decode_canonical_object(
        source[RESOLUTION_ARTIFACT_PATH_V1], "resolution_artifact", MAX_EVIDENCE_FILE_BYTES_V1
    )
    if (
        _expect_str(artifact.get("schema"), "resolution_artifact.schema")
        != "zenodex/m6-o005-semantic-resolutions/v1"
    ):
        _reject("RESOLUTION_SCHEMA", "resolution_artifact.schema", "unexpected schema")
    if (
        _expect_str(artifact.get("registry_root"), "resolution_artifact.registry_root")
        != RESOLUTION_REGISTRY_ROOT_V1
    ):
        _reject("RESOLUTION_ROOT", "resolution_artifact.registry_root", "registry root drift")
    for field in _CEILING_FALSE_FIELDS_V1:
        if _expect_bool(artifact.get(field), f"resolution_artifact.{field}"):
            _reject("RESOLUTION_CEILING", f"resolution_artifact.{field}", "must remain false")
    if (
        _expect_int(
            artifact.get("closed_value_movement_gates"),
            "resolution_artifact.closed_value_movement_gates",
        )
        != 0
    ):
        _reject(
            "RESOLUTION_VM_PROMOTION",
            "resolution_artifact.closed_value_movement_gates",
            "must remain zero",
        )
    if (
        _expect_str(
            artifact.get("production_authority"), "resolution_artifact.production_authority"
        )
        != "NONE"
        or _expect_str(
            artifact.get("settlement_authority"), "resolution_artifact.settlement_authority"
        )
        != "NONE"
    ):
        _reject("RESOLUTION_AUTHORITY", "resolution_artifact", "authority must remain NONE")
    rows = _expect_list(
        artifact.get("resolution_rows"),
        "resolution_artifact.resolution_rows",
        MAX_RESOLUTION_ROWS_V1,
    )
    if len(rows) != len(missing_ids):
        _reject(
            "RESOLUTION_ROW_COUNT",
            "resolution_artifact.resolution_rows",
            "must have exact twelve rows",
        )
    pairs: list[dict[str, str]] = []
    source_ids: list[str] = []
    target_ids: list[str] = []
    resolution_ids: list[str] = []
    for index, row_value in enumerate(rows):
        row = _expect_object(row_value, f"resolution_artifact.resolution_rows[{index}]")
        _expect_exact_fields(
            row, _RESOLUTION_ROW_FIELDS_V1, f"resolution_artifact.resolution_rows[{index}]"
        )
        source_id = _expect_str(
            row.get("source_missing_target_concept_id"),
            f"resolution_artifact.resolution_rows[{index}].source_missing_target_concept_id",
        )
        target_id = _expect_str(
            row.get("target_id"), f"resolution_artifact.resolution_rows[{index}].target_id"
        )
        resolution_id = _expect_str(
            row.get("resolution_id"), f"resolution_artifact.resolution_rows[{index}].resolution_id"
        )
        source_ids.append(source_id)
        target_ids.append(target_id)
        resolution_ids.append(resolution_id)
        pairs.append(
            {
                "proposed_target_id": target_id,
                "resolution_id": resolution_id,
                "source_missing_target_concept_id": source_id,
            }
        )
    if tuple(source_ids) != missing_ids:
        _reject(
            "RESOLUTION_SOURCE_BIJECTION",
            "resolution_artifact.resolution_rows",
            "source concepts do not match exact normative set",
        )
    _require_unique(tuple(target_ids), "resolution_artifact.resolution_rows.target_id")
    _require_unique(tuple(resolution_ids), "resolution_artifact.resolution_rows.resolution_id")
    route_rows = _expect_list(
        artifact.get("route_resolution_rows"),
        "resolution_artifact.route_resolution_rows",
        MAX_ROUTE_ROWS_V1,
    )
    if len(route_rows) != len(route_ids):
        _reject(
            "ROUTE_ROW_COUNT",
            "resolution_artifact.route_resolution_rows",
            "must have exact four rows",
        )
    route_pairs: list[dict[str, str]] = []
    actual_routes: list[str] = []
    actual_route_resolutions: list[str] = []
    for index, row_value in enumerate(route_rows):
        row = _expect_object(row_value, f"resolution_artifact.route_resolution_rows[{index}]")
        _expect_exact_fields(
            row, _ROUTE_ROW_FIELDS_V1, f"resolution_artifact.route_resolution_rows[{index}]"
        )
        source_route_id = _expect_str(
            row.get("source_route_id"),
            f"resolution_artifact.route_resolution_rows[{index}].source_route_id",
        )
        resolution_id = _expect_str(
            row.get("resolution_id"),
            f"resolution_artifact.route_resolution_rows[{index}].resolution_id",
        )
        actual_routes.append(source_route_id)
        actual_route_resolutions.append(resolution_id)
        route_pairs.append({"resolution_id": resolution_id, "source_route_id": source_route_id})
    if tuple(actual_routes) != route_ids:
        _reject(
            "ROUTE_SOURCE_BIJECTION",
            "resolution_artifact.route_resolution_rows",
            "source routes do not match exact normative set",
        )
    _require_unique(
        tuple(actual_route_resolutions), "resolution_artifact.route_resolution_rows.resolution_id"
    )
    source_pins = _expect_object(artifact.get("source_pins"), "resolution_artifact.source_pins")
    policy_ids = _expect_list(
        source_pins.get("unresolved_policy_ids"),
        "resolution_artifact.source_pins.unresolved_policy_ids",
        20,
    )
    if (
        tuple(
            _expect_str(value, f"resolution_artifact.source_pins.unresolved_policy_ids[{index}]")
            for index, value in enumerate(policy_ids)
        )
        != _UP_IDS_V1
    ):
        _reject(
            "RESOLUTION_UP_IDS",
            "resolution_artifact.source_pins.unresolved_policy_ids",
            "policy IDs drift",
        )
    if (
        _expect_str(
            source_pins.get("unresolved_policy_status"),
            "resolution_artifact.source_pins.unresolved_policy_status",
        )
        != _UP_STATUS_V1
    ):
        _reject(
            "RESOLUTION_UP_STATUS",
            "resolution_artifact.source_pins.unresolved_policy_status",
            "policy became selectable",
        )
    return {
        "proposed_target_resolution_count": len(pairs),
        "proposed_target_resolutions": pairs,
        "route_resolution_count": len(route_pairs),
        "route_resolutions": route_pairs,
        "source_missing_target_concept_ids_root": _ids_root(
            missing_ids, "resolution_bijections.missing_ids_root"
        ),
        "source_required_route_ids_root": _ids_root(
            route_ids, "resolution_bijections.route_ids_root"
        ),
    }


def _unsigned_certificate_v1(snapshot: SubjectEvidenceSnapshotV1) -> dict[str, object]:
    source = _validate_snapshot_v1(snapshot)
    admitted_plan = _parse_admitted_plan_v1(source)
    plan_gap = _parse_plan_baseline_v1(source)
    requirements_floor, missing_ids, route_ids = _derive_requirements_floor_v1(source)
    resolution_bijections = _derive_resolution_bijections_v1(source, missing_ids, route_ids)
    return {
        "admitted_plan": {**admitted_plan, "baseline_o005_gap": plan_gap},
        "claim_ceiling": {
            "closed_value_movement_gates": 0,
            "manifest_complete": False,
            "migration_authority": "NONE",
            "production_authority": "NONE",
            "release_authority": "NONE",
            "requirements_closed": False,
            "semantic_closure_complete": False,
            "semantic_policy_closure_complete": False,
            "semantic_target_inventory_complete": False,
            "settlement_authority": "NONE",
            "structural_mapping_complete": False,
            "value_movement_authority": "NONE",
        },
        "evidence_subject": {
            "commit": EVIDENCE_SUBJECT_COMMIT_V1,
            "current_content_matches_subject": True,
            "evidence_subject_is_current_ancestor": True,
            "tree": EVIDENCE_SUBJECT_TREE_V1,
        },
        "generator_command": GENERATOR_COMMAND_V1,
        "nonclaims": [
            "This certificate closes only O-005's incomplete_requirements_registry gap on the exact evidence subject.",
            "It does not establish complete economic semantics, implementation, proof, route mounting, release eligibility, migration correctness, settlement, or value-moving safety.",
            "All 20 unresolved policy decisions remain UNRESOLVED_POLICY_NOT_SELECTABLE; this certificate selects none of them.",
            "The admitted Plan remains immutable baseline evidence whose O-005 gap is OPEN; the successor status is a bounded certificate result only.",
            "The new completion core, build shell, checker, tests, and generated certificate are absent from the evidence subject. Their Git blob bindings would be self-referential and are deliberately not claimed.",
            "This artifact grants no production, settlement, release, migration, or value-moving authority.",
        ],
        "o005_completion": {
            "closes_only": ["incomplete_requirements_registry"],
            "current_successor_o005_status": "COMPLETE_ON_EXACT_SUBJECT",
            "plan_baseline_gap_status": "OPEN",
            "plan_obligation_id": "O-005",
        },
        "requirements_floor": requirements_floor,
        "resolution_bijections": resolution_bijections,
        "schema": ARTIFACT_SCHEMA_V1,
        "source_artifacts": {
            "normative_requirements": {
                "path": NORMATIVE_ARTIFACT_PATH_V1,
                "registry_root": NORMATIVE_REGISTRY_ROOT_V1,
                "sha256": NORMATIVE_ARTIFACT_SHA256_V1,
            },
            "o005_semantic_resolutions": {
                "path": RESOLUTION_ARTIFACT_PATH_V1,
                "registry_root": RESOLUTION_REGISTRY_ROOT_V1,
                "sha256": RESOLUTION_ARTIFACT_SHA256_V1,
            },
        },
        "source_file_pins": [pin.to_json() for pin in EVIDENCE_FILE_PINS_V1],
        "status": "RESEARCH_ONLY_O005_REQUIREMENTS_FLOOR_COMPLETE_ON_EXACT_SUBJECT",
    }


def build_requirements_floor_completion_artifact_v1(snapshot: SubjectEvidenceSnapshotV1) -> bytes:
    """Derive the only valid certificate bytes from a validated shell snapshot."""

    unsigned = _unsigned_certificate_v1(snapshot)
    certificate = {**unsigned, "certificate_root": _certificate_root(unsigned)}
    return _canonical_bytes(certificate, "certificate")


def _validate_certificate_envelope_v1(value: dict[str, object]) -> str:
    """Keep only checks that precede exact expected-byte comparison.

    Canonical decoding already rejects malformed JSON and hostile primitive
    values.  The source-derived expected bytes below decide every nested field,
    type, count, authority ceiling, and ordering property.  This envelope
    preserves the three intentional early diagnostics and independently binds
    the certificate root before reconstruction.
    """

    _expect_exact_fields(value, _CERTIFICATE_FIELDS_V1, "certificate")
    pins = _expect_list(
        value.get("source_file_pins"), "certificate.source_file_pins", MAX_EVIDENCE_FILE_PINS_V1
    )
    if len(pins) != len(EVIDENCE_FILE_PINS_V1):
        _reject(
            "CERTIFICATE_PIN_COUNT", "certificate.source_file_pins", "unexpected source pin count"
        )
    unsigned = dict(value)
    claimed_root = _expect_str(unsigned.pop("certificate_root"), "certificate.certificate_root")
    if _certificate_root(unsigned) != claimed_root:
        _reject("CERTIFICATE_ROOT", "certificate.certificate_root", "root does not bind payload")
    return claimed_root


def check_requirements_floor_completion_artifact_v1(
    raw: bytes, snapshot: SubjectEvidenceSnapshotV1
) -> dict[str, object]:
    """Return one deterministic report; failure leaves every authority ceiling closed."""

    try:
        certificate = _decode_canonical_object(raw, "certificate", MAX_ARTIFACT_BYTES_V1)
        _validate_certificate_envelope_v1(certificate)
        expected = build_requirements_floor_completion_artifact_v1(snapshot)
        if raw != expected:
            _reject(
                "CERTIFICATE_MISMATCH",
                "certificate",
                "bytes do not equal exact derived certificate",
            )
        return {
            "artifact_sha256": _sha256(raw, "certificate"),
            "closed_value_movement_gates": 0,
            "current_successor_o005_status": "COMPLETE_ON_EXACT_SUBJECT",
            "findings": [],
            "manifest_complete": False,
            "ok": True,
            "production_authority": "NONE",
            "release_authority": "NONE",
            "requirements_closed": False,
            "schema": CHECK_SCHEMA_V1,
            "semantic_closure_complete": False,
            "settlement_authority": "NONE",
            "value_movement_authority": "NONE",
        }
    except CompletionRejectV1 as exc:
        return {
            "artifact_sha256": "",
            "closed_value_movement_gates": 0,
            "current_successor_o005_status": "OPEN",
            "findings": [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
            "manifest_complete": False,
            "ok": False,
            "production_authority": "NONE",
            "release_authority": "NONE",
            "requirements_closed": False,
            "schema": CHECK_SCHEMA_V1,
            "semantic_closure_complete": False,
            "settlement_authority": "NONE",
            "value_movement_authority": "NONE",
        }
