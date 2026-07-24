#!/usr/bin/env python3
"""Fail-closed consistency check for the FCIS authority snapshot packet."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
LEDGER = ROOT / "requirements.json"
AUDIT = ROOT / "AUDIT_FINDINGS.md"
COMBINATOR = ROOT / "COMBINATOR_CONTRACT.md"
DESIGN_PATTERNS = ROOT / "DESIGN_PATTERN_AUDIT.md"
TEST_FILES = (ROOT / "TEST_MATRIX.md", ROOT / "TEST_MATRIX_PR477_PR478.md")
CURRENT_ARCHITECTURE_CLAUSES = {
    "COMBINATOR_CONTRACT.md": ("## 8. Pure persistent transition",),
    "DECISIONS.md": ("### FCIS-D004: One-way admission and persistent transition values",),
    "ERRATA.md": (
        "## E9. Persistent committed transitions replace domain scratch conversion",
        "## E11. State ownership, authority ownership, and final mounting are separate review stages",
        "## E12. Closed authority-graph algebra extensions",
    ),
    "PR477_MOUNTED_MIGRATION.md": (
        "### M5. Prepare the reviewed atomic-mount candidate",
        "### M6. Remove the obsolete authority representation in the same mount unit",
    ),
    "PR477_STATE_SCHEMA.md": ("## 2. Exact committed core inputs",),
}
STALE_ARCHITECTURE_CLAUSES = {
    "COMBINATOR_CONTRACT.md": (
        "## 8. Scratch conversion",
        "to_scratch_balance_table(CommittedBalanceTable)",
    ),
    "DECISIONS.md": (
        "### FCIS-D004: Three distinct representations",
        "SourceBuilder -> CommittedValue -> ScratchBuilder",
    ),
    "IMPLEMENTATION_RUNBOOK.md": (
        "### 2.4 Implement read protocols",
        "mutating paths call `to_scratch_*` once",
    ),
    "PR477_STATE_SCHEMA.md": (
        "## 2. Read protocols",
        "### Mutating transition code",
    ),
    "PR478_AUTHORITY_EFFECT_SCHEMA.md": ("## 6. Scratch settlement",),
}
ALLOWED_STATUS = {"OPEN", "SATISFIED", "VIOLATED", "UNVERIFIED"}
LEDGER_ROOT_KEYS = {
    "audit_authority",
    "audit_pattern_bindings",
    "claim_status",
    "design_lock_version",
    "forbidden_mechanisms",
    "mount_sequence",
    "mounted_limits",
    "normative_files",
    "required_pattern_ids",
    "requirements",
    "reviewed_heads",
    "schema",
    "test_bindings",
}
EXPECTED_MOUNT_SEQUENCE = {
    "state_substrate": "review_only_until_atomic_mount",
    "authority_graph": "review_only_until_atomic_mount",
    "atomic_mount": "first_mounted_promotion_candidate",
}
REQUIRED_KEYS = {
    "id",
    "pr",
    "status",
    "requirement",
    "forbidden",
    "source_targets",
    "tests",
    "evidence",
    "claim_impact",
}
TEST_ID_PATTERN = re.compile(r"FCIS-(?:T-[A-Z0-9-]+|PROP-[0-9]{3})")
REQUIREMENT_ID_PATTERN = re.compile(r"FCIS-(?:477|478|PROC)-[0-9]{3}")
PATTERN_ID_PATTERN = re.compile(r"FCIS-PAT-[A-Z0-9-]+-V[0-9]+")
EXPECTED_AUDIT_CASES = {f"STATE-ALIAS-{index:03d}" for index in range(1, 7)}
EXPECTED_AUDIT_WITNESSES = {f"IMMUTABILITY-ALIAS-{index:02d}" for index in range(1, 7)}


class DuplicateJsonMember(ValueError):
    pass


def _reject_duplicate_members(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonMember(key)
        result[key] = value
    return result


def _load_json(path: Path) -> Any:
    return json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_members,
    )


def _error(errors: list[str], code: str, detail: str) -> None:
    errors.append(f"{code}:{detail}")


def _check_packet_inventory(normative: list[str], errors: list[str]) -> None:
    declared = set(normative)
    actual: set[str] = set()
    try:
        paths = sorted(ROOT.rglob("*"))
    except OSError as exc:
        _error(errors, "PACKET_TREE_READ", type(exc).__name__)
        return
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            actual.add(relative)
            _error(errors, "PACKET_SYMLINK", relative)
        elif path.is_file():
            actual.add(relative)
    for relative in sorted(actual - declared):
        if relative == ".patch_probe" or ("/" not in relative and relative.endswith(".orig")):
            continue
        _error(errors, "UNDECLARED_PACKET_FILE", relative)


def _check_test_bindings(
    data: dict[str, Any],
    requirement_ids: set[str],
    declared_tests: set[str],
    referenced_tests: set[str],
    errors: list[str],
) -> set[str]:
    raw_bindings = data.get("test_bindings")
    if type(raw_bindings) is not dict:
        _error(errors, "TEST_BINDINGS_TYPE", "test_bindings")
        return set(referenced_tests)

    explicitly_bound: set[str] = set()
    for test_id, raw_requirement_ids in sorted(raw_bindings.items()):
        if type(test_id) is not str or TEST_ID_PATTERN.fullmatch(test_id) is None:
            _error(errors, "TEST_BINDING_ID", str(test_id))
            continue
        if type(raw_requirement_ids) is not list:
            _error(errors, "TEST_BINDING_REQUIREMENTS_TYPE", test_id)
            continue
        if not raw_requirement_ids:
            _error(errors, "TEST_BINDING_REQUIREMENTS_EMPTY", test_id)
            continue
        if any(type(item) is not str for item in raw_requirement_ids):
            _error(errors, "TEST_BINDING_REQUIREMENTS_TYPE", test_id)
            continue
        if len(raw_requirement_ids) != len(set(raw_requirement_ids)):
            _error(errors, "TEST_BINDING_REQUIREMENT_DUPLICATE", test_id)

        valid_target = False
        for requirement_id in raw_requirement_ids:
            if requirement_id not in requirement_ids:
                _error(
                    errors,
                    "TEST_BINDING_REQUIREMENT_UNKNOWN",
                    f"{test_id}:{requirement_id}",
                )
            else:
                valid_target = True
        if valid_target:
            explicitly_bound.add(test_id)

    bound_tests = referenced_tests | explicitly_bound
    for test_id in sorted(bound_tests - declared_tests):
        _error(errors, "TEST_ID_UNDECLARED", test_id)
    for test_id in sorted(declared_tests - bound_tests):
        _error(errors, "TEST_ID_UNBOUND", test_id)
    return bound_tests


def _check_mount_sequence(data: dict[str, Any], errors: list[str]) -> None:
    sequence = data.get("mount_sequence")
    if type(sequence) is not dict:
        _error(errors, "MOUNT_SEQUENCE_TYPE", "mount_sequence")
        return

    actual_keys = set(sequence)
    expected_keys = set(EXPECTED_MOUNT_SEQUENCE)
    for key in sorted(expected_keys - actual_keys):
        _error(errors, "MOUNT_SEQUENCE_KEY", f"missing:{key}")
    for key in sorted(actual_keys - expected_keys):
        _error(errors, "MOUNT_SEQUENCE_KEY", f"extra:{key}")

    for key, expected_value in EXPECTED_MOUNT_SEQUENCE.items():
        if key not in sequence:
            continue
        actual_value = sequence[key]
        if type(actual_value) is not str or actual_value != expected_value:
            _error(errors, "MOUNT_SEQUENCE_VALUE", key)


def _check_pattern_bindings(data: dict[str, Any], errors: list[str]) -> None:
    if (
        type(data.get("design_lock_version")) is not str
        or re.fullmatch(
            r"[0-9]+\.[0-9]+\.[0-9]+",
            data.get("design_lock_version", ""),
        )
        is None
    ):
        _error(errors, "DESIGN_LOCK_VERSION", "design_lock_version")

    raw_required = data.get("required_pattern_ids")
    if type(raw_required) is not list or any(
        type(item) is not str or PATTERN_ID_PATTERN.fullmatch(item) is None for item in raw_required
    ):
        _error(errors, "PATTERN_IDS_TYPE", "required_pattern_ids")
        required: set[str] = set()
    else:
        required = set(raw_required)
        if len(required) != len(raw_required):
            _error(errors, "PATTERN_ID_DUPLICATE", "required_pattern_ids")

    try:
        pattern_text = DESIGN_PATTERNS.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        _error(errors, "PATTERN_DOC_READ", DESIGN_PATTERNS.name)
        documented: set[str] = set()
    else:
        documented = set(
            re.findall(r"^## Pattern (FCIS-PAT-[A-Z0-9-]+-V[0-9]+)$", pattern_text, re.MULTILINE)
        )
    for pattern_id in sorted(required - documented):
        _error(errors, "PATTERN_DOC_MISSING", pattern_id)
    for pattern_id in sorted(documented - required):
        _error(errors, "PATTERN_DOC_UNDECLARED", pattern_id)

    bindings = data.get("audit_pattern_bindings")
    if type(bindings) is not dict or set(bindings) != {"cases", "witnesses"}:
        _error(errors, "PATTERN_BINDINGS_TYPE", "audit_pattern_bindings")
        return
    for section, expected_keys in (
        ("cases", EXPECTED_AUDIT_CASES),
        ("witnesses", EXPECTED_AUDIT_WITNESSES),
    ):
        section_bindings = bindings.get(section)
        if type(section_bindings) is not dict:
            _error(errors, "PATTERN_BINDINGS_TYPE", section)
            continue
        actual_keys = set(section_bindings)
        for missing in sorted(expected_keys - actual_keys):
            _error(errors, "PATTERN_BINDING_MISSING", f"{section}:{missing}")
        for extra in sorted(actual_keys - expected_keys):
            _error(errors, "PATTERN_BINDING_EXTRA", f"{section}:{extra}")
        for audit_id, pattern_ids in sorted(section_bindings.items()):
            if (
                type(pattern_ids) is not list
                or not pattern_ids
                or any(type(item) is not str for item in pattern_ids)
            ):
                _error(errors, "PATTERN_BINDING_TYPE", f"{section}:{audit_id}")
                continue
            if len(pattern_ids) != len(set(pattern_ids)):
                _error(errors, "PATTERN_BINDING_DUPLICATE", f"{section}:{audit_id}")
            for pattern_id in pattern_ids:
                if pattern_id not in required:
                    _error(
                        errors,
                        "PATTERN_BINDING_UNKNOWN",
                        f"{section}:{audit_id}:{pattern_id}",
                    )


def _check_transition_architecture(errors: list[str]) -> None:
    filenames = sorted(set(CURRENT_ARCHITECTURE_CLAUSES) | set(STALE_ARCHITECTURE_CLAUSES))
    for filename in filenames:
        try:
            text = (ROOT / filename).read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            _error(errors, "ARCHITECTURE_DOC_READ", filename)
            continue
        for clause in CURRENT_ARCHITECTURE_CLAUSES.get(filename, ()):
            if clause not in text:
                _error(errors, "ARCHITECTURE_CLAUSE_MISSING", f"{filename}:{clause}")
        for clause in STALE_ARCHITECTURE_CLAUSES.get(filename, ()):
            if clause in text:
                _error(errors, "STALE_MUTABLE_CORE_CLAUSE", f"{filename}:{clause}")


def main() -> int:
    errors: list[str] = []

    try:
        data = _load_json(LEDGER)
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateJsonMember) as exc:
        print(
            json.dumps(
                {
                    "schema": "zenodex/fcis-authority-snapshot-packet-check/v1",
                    "ok": False,
                    "errors": [f"LEDGER_INVALID:{type(exc).__name__}"],
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 1

    if type(data) is not dict:
        _error(errors, "LEDGER_TYPE", "root")
        requirements: list[Any] = []
        data = {}
    else:
        unknown_root_keys = sorted(set(data) - LEDGER_ROOT_KEYS)
        missing_root_keys = sorted(LEDGER_ROOT_KEYS - set(data))
        for key in unknown_root_keys:
            _error(errors, "LEDGER_ROOT_KEYS", key)
        for key in missing_root_keys:
            _error(errors, "LEDGER_ROOT_KEYS", f"missing:{key}")
        requirements_raw = data.get("requirements")
        requirements = requirements_raw if type(requirements_raw) is list else []
        if type(requirements_raw) is not list:
            _error(errors, "LEDGER_TYPE", "requirements")

    if data.get("schema") != "zenodex/fcis-authority-snapshot-requirements/v1":
        _error(errors, "SCHEMA", "requirements.json")
    if data.get("claim_status") != "blocked":
        _error(errors, "CLAIM_STATUS", "must_be_blocked")
    _check_mount_sequence(data, errors)
    _check_pattern_bindings(data, errors)
    _check_transition_architecture(errors)

    heads = data.get("reviewed_heads")
    if type(heads) is not dict:
        _error(errors, "HEADS_TYPE", "reviewed_heads")
    else:
        for name in ("pr_477", "pr_478"):
            value = heads.get(name)
            if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
                _error(errors, "HEAD", name)

    normative = data.get("normative_files")
    if type(normative) is not list or any(type(item) is not str for item in normative):
        _error(errors, "NORMATIVE_FILES_TYPE", "normative_files")
        normative = []
    if len(normative) != len(set(normative)):
        _error(errors, "DUPLICATE_NORMATIVE_FILE", "normative_files")
    for relative in sorted(normative):
        relative_path = Path(relative)
        if relative_path.is_absolute() or ".." in relative_path.parts:
            _error(errors, "NORMATIVE_FILE_PATH", relative)
            continue
        if not (ROOT / relative).is_file():
            _error(errors, "MISSING_NORMATIVE_FILE", relative)
    if "check_packet.py" not in normative:
        _error(errors, "CHECKER_NOT_NORMATIVE", "check_packet.py")
    _check_packet_inventory(normative, errors)

    ids: list[str] = []
    referenced_tests: set[str] = set()
    for index, requirement in enumerate(requirements):
        requirement_path = f"requirements[{index}]"
        if type(requirement) is not dict:
            _error(errors, "REQUIREMENT_TYPE", requirement_path)
            continue
        if set(requirement) != REQUIRED_KEYS:
            _error(errors, "REQUIREMENT_KEYS", requirement_path)
        requirement_id = requirement.get("id")
        if (
            type(requirement_id) is not str
            or REQUIREMENT_ID_PATTERN.fullmatch(requirement_id) is None
        ):
            _error(errors, "REQUIREMENT_ID", requirement_path)
        else:
            ids.append(requirement_id)
        if requirement.get("status") not in ALLOWED_STATUS:
            _error(errors, "REQUIREMENT_STATUS", requirement_path)
        if requirement.get("pr") not in (477, 478):
            _error(errors, "REQUIREMENT_PR", requirement_path)
        for key in ("forbidden", "source_targets", "tests", "evidence"):
            values = requirement.get(key)
            if type(values) is not list or any(type(item) is not str for item in values):
                _error(errors, "REQUIREMENT_LIST", f"{requirement_path}.{key}")
        if not requirement.get("tests") and not requirement.get("evidence"):
            _error(errors, "REQUIREMENT_UNEVIDENCED", requirement_path)
        tests = requirement.get("tests")
        if type(tests) is list:
            referenced_tests.update(item for item in tests if type(item) is str)

    if len(ids) != len(set(ids)):
        _error(errors, "DUPLICATE_REQUIREMENT_ID", "requirements")

    try:
        audit_text = AUDIT.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        audit_text = ""
        _error(errors, "AUDIT_READ", AUDIT.name)
    audit_ids = set(re.findall(r"^### (FCIS-(?:477|478)-[0-9]{3})", audit_text, re.MULTILINE))
    requirement_ids = set(ids)
    missing_audit = sorted(audit_ids - requirement_ids)
    extra_audit = sorted(
        item for item in requirement_ids - audit_ids if item.startswith(("FCIS-477-", "FCIS-478-"))
    )
    for item in missing_audit:
        _error(errors, "AUDIT_UNMAPPED", item)
    for item in extra_audit:
        _error(errors, "REQUIREMENT_WITHOUT_AUDIT", item)
    if sum(item.startswith("FCIS-477-") for item in audit_ids) != 18:
        _error(errors, "AUDIT_COUNT", "pr_477")
    if sum(item.startswith("FCIS-478-") for item in audit_ids) != 16:
        _error(errors, "AUDIT_COUNT", "pr_478")

    declared_tests: set[str] = set()
    markdown_paths = [ROOT / item for item in normative if item.endswith(".md")]
    for path in TEST_FILES:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            _error(errors, "TEST_MATRIX_READ", path.name)
            continue
        declared_tests.update(re.findall(r"FCIS-(?:T-[A-Z0-9-]+|PROP-[0-9]{3})", text))
    bound_tests = _check_test_bindings(
        data,
        requirement_ids,
        declared_tests,
        referenced_tests,
        errors,
    )

    try:
        combinator_text = COMBINATOR.read_text(encoding="utf-8")
        shared_test_text = TEST_FILES[0].read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        _error(errors, "ADMIT_CODE_READ", "contract_or_test_matrix")
    else:
        enum_match = re.search(
            r"class AdmitCode\(Enum\):(?P<body>.*?)\n\n@dataclass",
            combinator_text,
            re.DOTALL,
        )
        if enum_match is None:
            _error(errors, "ADMIT_CODE_REGISTRY", "missing")
        else:
            admit_codes = set(
                re.findall(
                    r"^\s+([A-Z][A-Z0-9_]*)\s*=",
                    enum_match.group("body"),
                    re.MULTILINE,
                )
            )
            referenced_admit_codes = set(re.findall(r"`([A-Z][A-Z0-9_]+)`", shared_test_text))
            for code in sorted(referenced_admit_codes - admit_codes):
                _error(errors, "ADMIT_CODE_UNDECLARED", code)

    for path in sorted(markdown_paths):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError):
            continue
        if sum(line.startswith("```") for line in lines) % 2 != 0:
            _error(errors, "UNBALANCED_FENCE", path.name)

    if (ROOT / ".patch_probe").exists():
        _error(errors, "PROBE_FILE", ".patch_probe")
    for artifact in sorted(ROOT.glob("*.orig")):
        _error(errors, "UNEXPECTED_BACKUP_FILE", artifact.name)

    errors.sort()
    report = {
        "schema": "zenodex/fcis-authority-snapshot-packet-check/v1",
        "ok": not errors,
        "requirement_count": len(ids),
        "audit_finding_count": len(audit_ids),
        "declared_test_id_count": len(declared_tests),
        "referenced_test_id_count": len(referenced_tests),
        "bound_test_id_count": len(bound_tests),
        "errors": errors,
    }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if not errors else 1


if __name__ == "__main__":
    sys.exit(main())
