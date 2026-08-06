"""Closed data model and contract parser for Test Hygiene Contract V1."""

from __future__ import annotations

import dataclasses
import fnmatch
import hashlib
import json
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT = Path(__file__).with_name("test_hygiene_contract_v1.json")
DEFAULT_EVIDENCE_DIR = REPO_ROOT / "tests/evidence/test_hygiene"

CONTRACT_SCHEMA = "zenodex/test-hygiene-contract/v1"
EVIDENCE_SCHEMA = "zenodex/test-hygiene-evidence/v1"
ALLOWED_STATUSES = frozenset({"A", "M", "D"})
ALLOWED_DECISIONS = frozenset({"applied", "not_applicable"})
ALLOWED_RISK_CLASSES = frozenset(
    {"ordinary", "critical", "authority", "assurance"}
)
CONTRACT_FIELDS = frozenset(
    {
        "schema",
        "evidence_schema",
        "evidence_path_prefix",
        "allowed_change_kinds",
        "allowed_evidence_families",
        "strong_evidence_families",
        "critical_path_rules",
    }
)
RULE_FIELDS = frozenset(
    {
        "id",
        "include_globs",
        "exclude_globs",
        "required_families",
        "minimum_strong_families",
    }
)


class TestHygieneError(RuntimeError):
    """Raised when the contract or evidence fails closed."""

    __test__ = False


@dataclasses.dataclass(frozen=True, slots=True)
class ChangedPathV1:
    """One normalized Git path change."""

    status: str
    path: str

    def __post_init__(self) -> None:
        if self.status not in ALLOWED_STATUSES:
            raise TestHygieneError(f"unsupported changed-path status: {self.status}")
        portable_path(self.path, context="changed path")


@dataclasses.dataclass(frozen=True, slots=True)
class RuleV1:
    rule_id: str
    include_globs: tuple[str, ...]
    exclude_globs: tuple[str, ...]
    required_families: frozenset[str]
    minimum_strong_families: int

    def matches(self, path: str) -> bool:
        included = any(
            fnmatch.fnmatchcase(path, pattern) for pattern in self.include_globs
        )
        excluded = any(
            fnmatch.fnmatchcase(path, pattern) for pattern in self.exclude_globs
        )
        return included and not excluded


@dataclasses.dataclass(frozen=True, slots=True)
class PinV1:
    path: str
    sha256: str
    node_ids: tuple[str, ...] = ()


@dataclasses.dataclass(frozen=True, slots=True)
class RemovedPathV1:
    path: str
    reason: str
    replacement_paths: tuple[str, ...]


@dataclasses.dataclass(frozen=True, slots=True)
class PacketV1:
    path: Path
    evidence_id: str
    risk_class: str
    families: frozenset[str]
    source_pins: tuple[PinV1, ...]
    test_pins: tuple[PinV1, ...]
    removed_paths: tuple[RemovedPathV1, ...]

    @property
    def node_ids(self) -> tuple[str, ...]:
        return tuple(node for pin in self.test_pins for node in pin.node_ids)

    def current_pin_for(self, path: str) -> PinV1 | None:
        return next(
            (pin for pin in (*self.source_pins, *self.test_pins) if pin.path == path),
            None,
        )

    def removal_for(self, path: str) -> RemovedPathV1 | None:
        return next((item for item in self.removed_paths if item.path == path), None)


@dataclasses.dataclass(frozen=True, slots=True)
class ContractV1:
    evidence_path_prefix: str
    allowed_change_kinds: frozenset[str]
    allowed_families: frozenset[str]
    strong_families: frozenset[str]
    rules: tuple[RuleV1, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise TestHygieneError(message)


def object_value(value: object, *, context: str) -> Mapping[str, Any]:
    require(type(value) is dict, f"{context}: expected object")
    return cast(Mapping[str, Any], value)


def exact_fields(
    value: Mapping[str, Any], expected: frozenset[str], *, context: str
) -> None:
    actual = frozenset(value)
    unknown = sorted(actual - expected)
    missing = sorted(expected - actual)
    require(not unknown, f"{context}: unknown fields: {unknown}")
    require(not missing, f"{context}: missing fields: {missing}")


def string_value(value: object, *, context: str) -> str:
    require(
        type(value) is str and bool(value.strip()),
        f"{context}: expected non-empty string",
    )
    return cast(str, value)


def string_list(
    value: object,
    *,
    context: str,
    minimum_items: int = 1,
) -> tuple[str, ...]:
    require(minimum_items >= 0, f"{context}: invalid minimum item count")
    require(type(value) is list, f"{context}: expected list")
    raw = cast(list[object], value)
    require(len(raw) >= minimum_items, f"{context}: must not be empty")
    result = tuple(string_value(item, context=context) for item in raw)
    require(len(result) == len(set(result)), f"{context}: duplicate values")
    return result


def portable_path(value: object, *, context: str) -> str:
    path = string_value(value, context=context)
    pure = PurePosixPath(path)
    require(not pure.is_absolute(), f"{context}: non-portable path")
    require(
        ".." not in pure.parts and "." not in pure.parts,
        f"{context}: non-portable path",
    )
    require(
        "\\" not in path and path == pure.as_posix(),
        f"{context}: non-portable path",
    )
    return path


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path, *, context: str) -> Mapping[str, Any]:
    try:
        return object_value(json.loads(path.read_text(encoding="utf-8")), context=context)
    except (OSError, json.JSONDecodeError) as exc:
        raise TestHygieneError(f"{context}: failed to load JSON: {exc}") from exc


def _parse_rule(value: object, *, index: int, families: frozenset[str]) -> RuleV1:
    context = f"contract.critical_path_rules[{index}]"
    rule = object_value(value, context=context)
    exact_fields(rule, RULE_FIELDS, context=context)
    required = frozenset(
        string_list(
            rule["required_families"],
            context=f"{context}.required_families",
            minimum_items=0,
        )
    )
    require(required <= families, f"{context}: required family is not allowed")
    minimum = rule["minimum_strong_families"]
    require(
        type(minimum) is int and minimum >= 0,
        f"{context}: invalid minimum_strong_families",
    )
    return RuleV1(
        rule_id=string_value(rule["id"], context=f"{context}.id"),
        include_globs=string_list(
            rule["include_globs"], context=f"{context}.include_globs"
        ),
        exclude_globs=string_list(
            rule["exclude_globs"],
            context=f"{context}.exclude_globs",
            minimum_items=0,
        ),
        required_families=required,
        minimum_strong_families=cast(int, minimum),
    )


def load_contract(path: Path) -> ContractV1:
    raw = load_json(path, context="contract")
    exact_fields(raw, CONTRACT_FIELDS, context="contract")
    require(raw["schema"] == CONTRACT_SCHEMA, "contract: schema mismatch")
    require(
        raw["evidence_schema"] == EVIDENCE_SCHEMA,
        "contract: evidence schema mismatch",
    )
    evidence_prefix = string_value(
        raw["evidence_path_prefix"], context="contract.evidence_path_prefix"
    )
    require(
        evidence_prefix.endswith("/"),
        "contract.evidence_path_prefix: must end with '/'",
    )
    portable_path(evidence_prefix[:-1], context="contract.evidence_path_prefix")

    change_kinds = frozenset(
        string_list(raw["allowed_change_kinds"], context="contract.allowed_change_kinds")
    )
    families = frozenset(
        string_list(
            raw["allowed_evidence_families"],
            context="contract.allowed_evidence_families",
        )
    )
    strong = frozenset(
        string_list(
            raw["strong_evidence_families"],
            context="contract.strong_evidence_families",
        )
    )
    require(strong <= families, "contract: strong evidence families must be allowed")
    raw_rules = raw["critical_path_rules"]
    require(
        type(raw_rules) is list and bool(raw_rules),
        "contract.critical_path_rules: expected non-empty list",
    )
    rules = tuple(
        _parse_rule(item, index=index, families=families)
        for index, item in enumerate(cast(list[object], raw_rules))
    )
    rule_ids = [rule.rule_id for rule in rules]
    require(len(rule_ids) == len(set(rule_ids)), "contract: duplicate rule ids")
    return ContractV1(
        evidence_path_prefix=evidence_prefix,
        allowed_change_kinds=change_kinds,
        allowed_families=families,
        strong_families=strong,
        rules=rules,
    )
