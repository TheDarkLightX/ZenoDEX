#!/usr/bin/env python3
"""Check bounded V3 support records without promoting any baseline obligation.

The ledger records reviewed, scoped support work.  It deliberately cannot close
a capability, the formal core, value movement, or the whole product.  A fresh
replay is available only for code-owned gates in ``GATE_CATALOG``.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as element_tree
from pathlib import Path
from typing import Iterable, Mapping, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = Path("docs/research/ZENODEX_V3_PROGRESS.json")
LEDGER_SCHEMA = "zenodex/v3-progress-ledger/v1"
CHECK_SCHEMA = "zenodex/v3-progress-check/v1"
MAX_JSON_BYTES = 1_048_576
MAX_JUNIT_BYTES = 4_194_304
HEX64 = re.compile(r"[0-9a-f]{64}")
HEX40 = re.compile(r"[0-9a-f]{40}")

IMMUTABLE_INPUTS = {
    "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json": (
        "e1b45e9ef9da7fa2c584567db3ac4605b6eb4ec065933b9e71be5ba82ef31adc"
    ),
    "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json": (
        "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95"
    ),
    "docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json": (
        "29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f"
    ),
}

CLAIM_CEILING = {
    "formal_core_complete": False,
    "whole_value_movement_safe": False,
    "production_promotion": False,
    "whole_product_complete": False,
    "closed_value_movement_gate_count": 0,
}

# This is intentionally code-owned.  The ledger can name this gate and bind
# reviewed bytes, but cannot select a command, cwd, environment, or test set.
GATE_CATALOG: dict[str, dict[str, object]] = {
    "receipt_copy_boundaries_v1": {
        "test_paths": (
            "tests/integration/test_zdex_purchase_burn_verifier_boundary_v1.py",
            "tests/integration/test_zdex_fee_allocation_verifier_boundary_v1.py",
        ),
        "source_paths": (
            "src/core/zdex_purchase_burn_receipt_preparation_v1.py",
            "src/core/zdex_fee_allocation_receipt_verification_v1.py",
            "tests/integration/test_zdex_purchase_burn_verifier_boundary_v1.py",
            "tests/integration/test_zdex_fee_allocation_verifier_boundary_v1.py",
        ),
        "support_paths": (
            "pyproject.toml",
            "pytest.ini",
            "src/__init__.py",
            "src/core/__init__.py",
            "src/integration/__init__.py",
            "src/core/economic_receipt_verifier_deployment_v1.py",
            "src/core/global_economic_authority_head_v1.py",
            "src/core/global_economic_proof_v1.py",
            "src/core/global_settlement_types_v1.py",
            "src/core/zdex_atomic_buyback_v1.py",
            "src/core/zdex_buyback_price_authority_v1.py",
            "src/core/zdex_buyback_price_safety_v1.py",
            "src/core/zdex_fee_allocation_v1.py",
            "src/core/zdex_purchase_burn_effects_v1.py",
            "src/core/zdex_purchase_burn_receipt_verification_v1.py",
            "src/core/zdex_purchase_burn_route_types_v1.py",
            "src/integration/zdex_fee_allocation_receipt_verification_v1.py",
            "src/integration/zdex_purchase_burn_receipt_verification_v1.py",
            "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py",
            "tests/__init__.py",
            "tests/conftest.py",
            "tests/core/test_zdex_atomic_buyback_v1.py",
            "tests/core/test_zdex_buyback_spot_safety_receipt_v1.py",
            "tests/core/test_zdex_purchase_burn_route_v1.py",
            "tests/core/test_zdex_purchase_burn_route_v2.py",
        ),
        "support_scope_id": "receipt_copy_direct_support_v1",
        "contract_path": ("docs/research/ZENODEX_POST_CORRECTNESS_SIMPLIFICATION_20260907.md"),
        "expected_test_count": 164,
        "expected_inventory_sha256": (
            "95302b20cb487dd3f2ab710cefd090aa6b53e513a1e9d6f7a7397dc4ef373135"
        ),
        "timeout_seconds": 180,
        "dependency_scope": (
            "The reviewed core/test subject plus the code-owned direct imported "
            "receipt support, test helper, pytest configuration, and package files; "
            "this remains a scoped support contract rather than a whole runtime claim."
        ),
    }
}


class ProgressReject(ValueError):
    """A closed-schema or source-binding failure."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(detail)
        self.code = code
        self.detail = detail


def _require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise ProgressReject(code, detail)


def _canonical(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")


def _without_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ProgressReject("DUPLICATE_JSON_KEY", key)
        result[key] = value
    return result


def _reject_nonfinite(value: str) -> object:
    raise ProgressReject("NONFINITE_JSON", value)


def _read_regular(path: Path, *, maximum: int, label: str) -> bytes:
    try:
        stat = path.lstat()
    except OSError as exc:
        raise ProgressReject("MISSING_FILE", f"{label}: {exc}") from exc
    _require(not path.is_symlink(), "SYMLINK_INPUT", label)
    _require(path.is_file(), "NONREGULAR_INPUT", label)
    _require(0 < stat.st_size <= maximum, "INPUT_SIZE", label)
    try:
        return path.read_bytes()
    except OSError as exc:
        raise ProgressReject("READ_FAILURE", f"{label}: {exc}") from exc


def _repo_path(root: Path, path: str, code: str) -> Path:
    """Reject lexical and symlink-parent escapes before a repository read."""
    _safe_path(path, code)
    candidate = root / path
    try:
        root_resolved = root.resolve(strict=True)
        candidate_resolved = candidate.resolve(strict=False)
        candidate_resolved.relative_to(root_resolved)
    except (OSError, ValueError) as exc:
        raise ProgressReject("PATH_ESCAPE", f"{code}: {path}") from exc
    return candidate


def _load_object(path: Path, *, maximum: int, label: str) -> dict[str, object]:
    raw = _read_regular(path, maximum=maximum, label=label)
    return _decode_object(raw, label)


def _decode_object(raw: bytes, label: str) -> dict[str, object]:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_without_duplicate_keys,
            parse_constant=_reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ProgressReject) as exc:
        if isinstance(exc, ProgressReject):
            raise
        raise ProgressReject("MALFORMED_JSON", f"{label}: {exc}") from exc
    _require(type(value) is dict, "JSON_OBJECT_REQUIRED", label)
    return cast(dict[str, object], value)


def _object(
    value: object,
    fields: Iterable[str],
    code: str,
) -> dict[str, object]:
    expected = set(fields)
    _require(type(value) is dict and set(value) == expected, code, "closed field set")
    return cast(dict[str, object], value)


def _text(value: object, code: str, *, maximum: int = 4096) -> str:
    _require(type(value) is str and 0 < len(value) <= maximum, code, "bounded text")
    return cast(str, value)


def _safe_path(value: object, code: str) -> str:
    text = _text(value, code)
    candidate = Path(text)
    _require(
        not candidate.is_absolute()
        and ".." not in candidate.parts
        and "\\" not in text
        and text == candidate.as_posix(),
        code,
        "repository-relative path required",
    )
    return text


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _hash(value: object, code: str) -> str:
    text = _text(value, code, maximum=64)
    _require(HEX64.fullmatch(text) is not None, code, "sha256 required")
    return text


def _commit(value: object, code: str) -> str:
    text = _text(value, code, maximum=40)
    _require(HEX40.fullmatch(text) is not None, code, "full commit hash required")
    return text


def _strings(
    value: object,
    code: str,
    *,
    allow_empty: bool = False,
) -> list[str]:
    _require(type(value) is list, code, "list required")
    result = [_text(item, code) for item in cast(list[object], value)]
    _require(
        (allow_empty or bool(result)) and len(result) == len(set(result)), code, "unique strings"
    )
    return result


def _safe_paths(
    value: object,
    code: str,
    *,
    allow_empty: bool = False,
) -> list[str]:
    _require(type(value) is list, code, "list required")
    result = [_safe_path(item, code) for item in cast(list[object], value)]
    _require(
        (allow_empty or bool(result)) and len(result) == len(set(result)), code, "unique paths"
    )
    return result


def _run_git(root: Path, args: list[str], code: str) -> bytes:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=root,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            shell=False,
            check=False,
            timeout=20,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ProgressReject("GIT_UNAVAILABLE", f"{code}: {type(exc).__name__}") from exc
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", "replace").strip()[:240]
        raise ProgressReject(code, detail or "git command failed")
    return result.stdout


def _git_blob(root: Path, commit: str, path: str) -> bytes | None:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=root,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        shell=False,
        check=False,
        timeout=20,
    )
    if result.returncode:
        return None
    return result.stdout


def _working_blob(root: Path, path: str) -> bytes | None:
    candidate = _repo_path(root, path, "WORKING_PATH")
    if not candidate.exists():
        return None
    return _read_regular(candidate, maximum=MAX_JUNIT_BYTES, label=path)


def _require_commit(root: Path, commit: str) -> None:
    _run_git(root, ["rev-parse", "--verify", f"{commit}^{{commit}}"], "UNKNOWN_COMMIT")


def _changed_paths(root: Path, before: str, after: str) -> list[dict[str, object]]:
    raw = _run_git(
        root,
        ["diff", "--name-status", "-z", "-M", before, after, "--"],
        "GIT_DIFF_FAILURE",
    )
    values = raw.decode("utf-8", "strict").split("\0")
    if values and values[-1] == "":
        values.pop()
    result: list[dict[str, object]] = []
    index = 0
    while index < len(values):
        status = values[index]
        index += 1
        _require(status, "GIT_DIFF_FAILURE", "empty status")
        kind = status[0]
        _require(kind in {"A", "D", "M", "R"}, "UNSUPPORTED_GIT_CHANGE", status)
        if kind == "R":
            _require(index + 1 < len(values), "GIT_DIFF_FAILURE", "rename path missing")
            before_path, after_path = values[index], values[index + 1]
            index += 2
        else:
            _require(index < len(values), "GIT_DIFF_FAILURE", "path missing")
            path = values[index]
            index += 1
            before_path = None if kind == "A" else path
            after_path = None if kind == "D" else path
        if before_path is not None:
            _safe_path(before_path, "GIT_PATH")
        if after_path is not None:
            _safe_path(after_path, "GIT_PATH")
        result.append({"status": kind, "before_path": before_path, "after_path": after_path})
    _require(bool(result), "EMPTY_GIT_CHANGE", after)
    return result


def _ast_observation(raw: bytes | None, path: str | None) -> dict[str, object]:
    if raw is None:
        return {
            "present": False,
            "sha256": None,
            "line_count": 0,
            "ast": {"status": "NOT_PRESENT", "classes": [], "functions": [], "branch_count": 0},
        }
    observation: dict[str, object] = {
        "present": True,
        "sha256": _sha256(raw),
        "line_count": raw.count(b"\n") + (1 if raw and not raw.endswith(b"\n") else 0),
    }
    if path is None or not path.endswith(".py"):
        observation["ast"] = {
            "status": "NOT_APPLICABLE",
            "classes": [],
            "functions": [],
            "branch_count": 0,
        }
        return observation
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=path)
    except (SyntaxError, UnicodeDecodeError):
        observation["ast"] = {
            "status": "INCOMPLETE",
            "classes": [],
            "functions": [],
            "branch_count": 0,
        }
        return observation
    classes = [node.name for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]
    functions = [
        node.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    branches = sum(
        isinstance(
            node,
            (ast.If, ast.For, ast.AsyncFor, ast.While, ast.IfExp, ast.Match, ast.Try),
        )
        for node in ast.walk(tree)
    )
    observation["ast"] = {
        "status": "PYTHON",
        "classes": sorted(classes),
        "functions": sorted(functions),
        "branch_count": branches,
    }
    return observation


def _change_observations(
    root: Path,
    before: str,
    after: str,
    changes: list[dict[str, object]],
) -> list[dict[str, object]]:
    observations: list[dict[str, object]] = []
    for change in changes:
        before_path = cast(str | None, change["before_path"])
        after_path = cast(str | None, change["after_path"])
        before_raw = None if before_path is None else _git_blob(root, before, before_path)
        after_raw = None if after_path is None else _git_blob(root, after, after_path)
        _require(
            before_path is None or before_raw is not None,
            "MISSING_HISTORICAL_BLOB",
            before_path or "",
        )
        _require(
            after_path is None or after_raw is not None,
            "MISSING_HISTORICAL_BLOB",
            after_path or "",
        )
        before_observation = _ast_observation(before_raw, before_path)
        after_observation = _ast_observation(after_raw, after_path)
        before_ast = cast(dict[str, object], before_observation["ast"])
        after_ast = cast(dict[str, object], after_observation["ast"])
        added_classes = sorted(
            set(cast(list[str], after_ast["classes"])) - set(cast(list[str], before_ast["classes"]))
        )
        added_functions = sorted(
            set(cast(list[str], after_ast["functions"]))
            - set(cast(list[str], before_ast["functions"]))
        )
        observations.append(
            {
                **change,
                "before": _public_file_observation(before_observation),
                "after": _public_file_observation(after_observation),
                "added_classes": added_classes,
                "added_functions": added_functions,
                "branch_delta": (
                    cast(int, after_ast["branch_count"]) - cast(int, before_ast["branch_count"])
                ),
            }
        )
    return observations


def _public_file_observation(observation: Mapping[str, object]) -> dict[str, object]:
    ast_observation = cast(dict[str, object], observation["ast"])
    return {
        "present": observation["present"],
        "sha256": observation["sha256"],
        "line_count": observation["line_count"],
        "ast": {
            "status": ast_observation["status"],
            "class_count": len(cast(list[str], ast_observation["classes"])),
            "function_count": len(cast(list[str], ast_observation["functions"])),
            "branch_count": ast_observation["branch_count"],
        },
    }


def _derive_inventory(
    root: Path,
    immutable_rows: object,
) -> dict[str, object]:
    rows = _require_hash_rows(immutable_rows, "IMMUTABLE_INPUTS", allow_empty=False)
    observed_pins = {row["path"]: row["sha256"] for row in rows}
    _require(observed_pins == IMMUTABLE_INPUTS, "IMMUTABLE_INPUTS", "pin set drift")
    inputs: dict[str, dict[str, object]] = {}
    for path, expected_hash in IMMUTABLE_INPUTS.items():
        source = _repo_path(root, path, "IMMUTABLE_INPUTS")
        raw = _read_regular(source, maximum=MAX_JSON_BYTES, label=path)
        _require(_sha256(raw) == expected_hash, "IMMUTABLE_SOURCE_DRIFT", path)
        inputs[path] = _decode_object(raw, path)

    plan = inputs["docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json"]
    manifest = inputs["docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"]
    normative = inputs["docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json"]
    floor = _object(
        plan.get("requirements_floor"),
        (
            "capability_count",
            "lane_count",
            "route_count",
            "exclusion_count",
            "lanes",
            "required_cross_lane_routes",
            "explicit_exclusions",
            "expansion_rule",
        ),
        "PLAN_REQUIREMENTS_FLOOR",
    )
    lanes = floor["lanes"]
    _require(type(lanes) is list and len(lanes) == 12, "LANE_INVENTORY", "twelve lanes")
    capability_ids: list[str] = []
    for raw_lane in cast(list[object], lanes):
        lane = _object(raw_lane, ("lane_id", "disposition", "capabilities"), "LANE_INVENTORY")
        lane_id = _text(lane["lane_id"], "LANE_INVENTORY")
        capabilities = _strings(lane["capabilities"], "LANE_INVENTORY")
        capability_ids.extend(f"{lane_id}:{capability}" for capability in capabilities)
    _require(len(capability_ids) == 103, "CAPABILITY_INVENTORY", "103 capabilities")
    _require(
        len(capability_ids) == len(set(capability_ids)),
        "CAPABILITY_INVENTORY",
        "unique capabilities",
    )
    _require(floor["lanes"] == manifest.get("lanes"), "MANIFEST_FLOOR_DRIFT", "lane floor")
    route_ids = _strings(floor["required_cross_lane_routes"], "ROUTE_INVENTORY")
    _require(
        len(route_ids) == 4 and route_ids == manifest.get("required_cross_lane_routes"),
        "ROUTE_INVENTORY",
        "exact routes",
    )
    raw_exclusions = floor["explicit_exclusions"]
    _require(
        type(raw_exclusions) is list and len(raw_exclusions) == 4,
        "EXCLUSION_INVENTORY",
        "four exclusions",
    )
    exclusion_ids: list[str] = []
    for raw_exclusion in cast(list[object], raw_exclusions):
        exclusion = _object(raw_exclusion, ("capability", "disposition"), "EXCLUSION_INVENTORY")
        exclusion_ids.append(_text(exclusion["capability"], "EXCLUSION_INVENTORY"))
    _require(
        len(exclusion_ids) == len(set(exclusion_ids)), "EXCLUSION_INVENTORY", "unique exclusions"
    )
    _require(
        raw_exclusions == manifest.get("explicit_exclusions"), "MANIFEST_FLOOR_DRIFT", "exclusions"
    )
    tasks = plan.get("tasks")
    _require(type(tasks) is list and len(tasks) == 14, "TASK_INVENTORY", "fourteen tasks")
    task_ids = []
    for raw_task in cast(list[object], tasks):
        _require(type(raw_task) is dict, "TASK_INVENTORY", "task object")
        task = cast(dict[str, object], raw_task)
        task_ids.append(_text(task.get("id"), "TASK_INVENTORY"))
        _require(task.get("status") == "OPEN", "TASK_STATUS", "baseline task must remain OPEN")
    _require(task_ids == [f"W{i:02d}" for i in range(14)], "TASK_INVENTORY", "W00-W13")
    rows_value = normative.get("rows")
    targets_value = normative.get("targets")
    _require(type(rows_value) is list and len(rows_value) == 152, "NORMATIVE_INVENTORY", "152 rows")
    _require(
        type(targets_value) is list and len(targets_value) == 142,
        "NORMATIVE_INVENTORY",
        "142 targets",
    )
    return {
        "capability_ids": capability_ids,
        "route_ids": route_ids,
        "exclusions": [
            {
                "id": exclusion_id,
                "disposition": cast(dict[str, object], raw)["disposition"],
            }
            for exclusion_id, raw in zip(
                exclusion_ids, cast(list[object], raw_exclusions), strict=True
            )
        ],
        "task_ids": task_ids,
        "normative_registry": {
            "requirement_row_count": 152,
            "target_count": 142,
            "status": "SEPARATE_UNPOOLED",
        },
    }


def _require_hash_rows(
    value: object,
    code: str,
    *,
    allow_empty: bool,
) -> list[dict[str, str]]:
    _require(type(value) is list, code, "hash rows required")
    rows: list[dict[str, str]] = []
    for raw_row in cast(list[object], value):
        row = _object(raw_row, ("path", "sha256"), code)
        rows.append({"path": _safe_path(row["path"], code), "sha256": _hash(row["sha256"], code)})
    _require((allow_empty or bool(rows)), code, "nonempty rows required")
    _require(len(rows) == len({row["path"] for row in rows}), code, "duplicate path")
    return rows


def _gate_scope_paths(gate_id: str) -> tuple[str, ...]:
    gate = GATE_CATALOG[gate_id]
    paths = (
        *cast(tuple[str, ...], gate["source_paths"]),
        *cast(tuple[str, ...], gate["support_paths"]),
    )
    _require(len(paths) == len(set(paths)), "GATE_CATALOG", f"duplicate source path: {gate_id}")
    return tuple(sorted(paths))


def _aggregate_hash(path_hashes: Mapping[str, str]) -> str:
    rows = b"".join(
        path.encode("utf-8") + b"\0" + path_hashes[path].encode("ascii") + b"\n"
        for path in sorted(path_hashes)
    )
    return _sha256(rows)


def _historical_scope_hash(root: Path, commit: str, gate_id: str) -> str:
    path_hashes: dict[str, str] = {}
    for path in _gate_scope_paths(gate_id):
        blob = _git_blob(root, commit, path)
        _require(blob is not None, "GATE_SCOPE_SOURCE_MISSING", path)
        path_hashes[path] = _sha256(blob)
    return _aggregate_hash(path_hashes)


def _working_scope_hash(root: Path, gate_id: str) -> str:
    return _aggregate_hash(_source_hashes(root, _gate_scope_paths(gate_id)))


def _require_change_rows(value: object) -> list[dict[str, object]]:
    _require(type(value) is list and bool(value), "CHANGE_ROWS", "nonempty rows required")
    rows: list[dict[str, object]] = []
    for raw_row in cast(list[object], value):
        row = _object(raw_row, ("status", "before_path", "after_path"), "CHANGE_ROWS")
        status = _text(row["status"], "CHANGE_ROWS", maximum=1)
        _require(status in {"A", "D", "M", "R"}, "CHANGE_ROWS", "change status")
        before_path = row["before_path"]
        after_path = row["after_path"]
        _require(before_path is None or type(before_path) is str, "CHANGE_ROWS", "before path")
        _require(after_path is None or type(after_path) is str, "CHANGE_ROWS", "after path")
        if before_path is not None:
            _safe_path(before_path, "CHANGE_ROWS")
        if after_path is not None:
            _safe_path(after_path, "CHANGE_ROWS")
        _require(
            (status == "A" and before_path is None and after_path is not None)
            or (status == "D" and before_path is not None and after_path is None)
            or (status in {"M", "R"} and before_path is not None and after_path is not None),
            "CHANGE_ROWS",
            "path/status mismatch",
        )
        rows.append({"status": status, "before_path": before_path, "after_path": after_path})
    return rows


def _validate_record(
    root: Path,
    record_value: object,
    inventory: Mapping[str, object],
) -> tuple[dict[str, object], dict[str, object]]:
    record = _object(
        record_value,
        (
            "id",
            "kind",
            "baseline_links",
            "support_scope",
            "subject",
            "declared_scope_paths",
            "acceptance_contract",
            "gate_ids",
            "gate_subject_hashes",
            "gate_scope_aggregate",
            "rationale",
            "recorded_evidence",
            "review_binding",
            "supersedes",
        ),
        "RECORD_FIELDS",
    )
    record_id = _text(record["id"], "RECORD_ID", maximum=128)
    _require(re.fullmatch(r"[A-Z0-9-]+", record_id) is not None, "RECORD_ID", record_id)
    kind = _text(record["kind"], "RECORD_KIND", maximum=10)
    _require(kind in {"SUPPORT", "CORRECTION"}, "RECORD_KIND", kind)

    links = _object(
        record["baseline_links"],
        ("capability_ids", "route_ids", "exclusion_ids", "task_ids"),
        "BASELINE_LINKS",
    )
    capability_ids = _strings(links["capability_ids"], "BASELINE_LINKS", allow_empty=True)
    route_ids = _strings(links["route_ids"], "BASELINE_LINKS", allow_empty=True)
    exclusion_ids = _strings(links["exclusion_ids"], "BASELINE_LINKS", allow_empty=True)
    task_ids = _strings(links["task_ids"], "BASELINE_LINKS", allow_empty=True)
    _require(
        bool(capability_ids or route_ids or exclusion_ids or task_ids),
        "BASELINE_LINKS",
        "at least one linked baseline id",
    )
    _require(
        set(capability_ids) <= set(cast(list[str], inventory["capability_ids"])),
        "BASELINE_LINKS",
        "unknown capability",
    )
    _require(
        set(route_ids) <= set(cast(list[str], inventory["route_ids"])),
        "BASELINE_LINKS",
        "unknown route",
    )
    _require(
        set(exclusion_ids)
        <= {
            cast(str, exclusion["id"])
            for exclusion in cast(list[dict[str, object]], inventory["exclusions"])
        },
        "BASELINE_LINKS",
        "unknown exclusion",
    )
    _require(
        set(task_ids) <= set(cast(list[str], inventory["task_ids"])),
        "BASELINE_LINKS",
        "unknown task",
    )

    support_scope = _object(record["support_scope"], ("summary", "nonclaims"), "SUPPORT_SCOPE")
    _text(support_scope["summary"], "SUPPORT_SCOPE")
    _strings(support_scope["nonclaims"], "SUPPORT_SCOPE")

    subject = _object(
        record["subject"], ("before_commit", "after_commit", "changed_paths"), "SUBJECT"
    )
    before = _commit(subject["before_commit"], "SUBJECT")
    after = _commit(subject["after_commit"], "SUBJECT")
    provided_changes = _require_change_rows(subject["changed_paths"])
    _require_commit(root, before)
    _require_commit(root, after)
    parent = _run_git(root, ["rev-parse", f"{after}^"], "SUBJECT_PARENT").decode("ascii").strip()
    _require(parent == before, "SUBJECT_PARENT", "before commit must be exact parent")
    actual_changes = _changed_paths(root, before, after)
    _require(
        _canonical(provided_changes) == _canonical(actual_changes),
        "SUBJECT_CHANGE_DRIFT",
        record_id,
    )
    declared_paths = _safe_paths(record["declared_scope_paths"], "DECLARED_SCOPE")
    actual_scope = {
        path
        for change in actual_changes
        for path in (change["before_path"], change["after_path"])
        if path is not None
    }
    _require(set(declared_paths) == actual_scope, "OUT_OF_SCOPE_EDIT", record_id)

    acceptance = _object(record["acceptance_contract"], ("path", "sha256"), "ACCEPTANCE_CONTRACT")
    acceptance_path = _safe_path(acceptance["path"], "ACCEPTANCE_CONTRACT")
    acceptance_hash = _hash(acceptance["sha256"], "ACCEPTANCE_CONTRACT")
    acceptance_blob = _git_blob(root, after, acceptance_path)
    _require(
        acceptance_blob is not None and _sha256(acceptance_blob) == acceptance_hash,
        "ACCEPTANCE_CONTRACT",
        acceptance_path,
    )

    gate_ids = _strings(record["gate_ids"], "GATE_IDS", allow_empty=True)
    _require(set(gate_ids) <= set(GATE_CATALOG), "UNKNOWN_GATE", record_id)
    gate_hashes = _require_hash_rows(
        record["gate_subject_hashes"], "GATE_SUBJECT_HASHES", allow_empty=True
    )
    expected_gate_paths = {
        path
        for gate_id in gate_ids
        for path in cast(tuple[str, ...], GATE_CATALOG[gate_id]["source_paths"])
    }
    _require(
        {row["path"] for row in gate_hashes} == expected_gate_paths,
        "GATE_SUBJECT_HASHES",
        record_id,
    )
    for row in gate_hashes:
        blob = _git_blob(root, after, row["path"])
        _require(
            blob is not None and _sha256(blob) == row["sha256"], "GATE_SUBJECT_HASHES", row["path"]
        )
    scope_aggregate = record["gate_scope_aggregate"]
    _require(
        (not gate_ids and scope_aggregate is None)
        or (len(gate_ids) == 1 and type(scope_aggregate) is dict),
        "GATE_SCOPE_AGGREGATE",
        record_id,
    )
    expected_scope_hash: str | None = None
    if gate_ids:
        aggregate = _object(scope_aggregate, ("scope_id", "sha256"), "GATE_SCOPE_AGGREGATE")
        gate = GATE_CATALOG[gate_ids[0]]
        _require(
            aggregate["scope_id"] == gate["support_scope_id"], "GATE_SCOPE_AGGREGATE", record_id
        )
        expected_scope_hash = _hash(aggregate["sha256"], "GATE_SCOPE_AGGREGATE")
        _require(
            expected_scope_hash == _historical_scope_hash(root, after, gate_ids[0]),
            "GATE_SCOPE_AGGREGATE",
            record_id,
        )

    rationale = _object(
        record["rationale"],
        (
            "linked_obligation",
            "acceptance_condition",
            "simpler_alternative",
            "why_added_structure",
            "stop_condition",
        ),
        "RATIONALE",
    )
    for value in rationale.values():
        _text(value, "RATIONALE")

    evidence = _require_hash_rows(
        record["recorded_evidence"], "RECORDED_EVIDENCE", allow_empty=False
    )
    for row in evidence:
        blob = _git_blob(root, after, row["path"])
        _require(
            blob is not None and _sha256(blob) == row["sha256"], "RECORDED_EVIDENCE", row["path"]
        )

    review = _object(
        record["review_binding"],
        ("path", "sha256", "reviewed_subject_commit", "status"),
        "REVIEW_BINDING",
    )
    review_path = _safe_path(review["path"], "REVIEW_BINDING")
    review_hash = _hash(review["sha256"], "REVIEW_BINDING")
    _require(
        _commit(review["reviewed_subject_commit"], "REVIEW_BINDING") == after,
        "REVIEW_BINDING",
        "wrong reviewed subject",
    )
    _require(
        review["status"] == "EXTERNAL_REVIEW_PREMISE_UNACCEPTED",
        "REVIEW_BINDING",
        "review cannot be self-accepted",
    )
    review_blob = _git_blob(root, after, review_path)
    _require(
        review_blob is not None and _sha256(review_blob) == review_hash,
        "REVIEW_BINDING",
        review_path,
    )

    supersedes = record["supersedes"]
    _require(supersedes is None or type(supersedes) is str, "SUPERSEDES", record_id)
    if supersedes is not None:
        _text(supersedes, "SUPERSEDES", maximum=128)
    _require((kind == "SUPPORT") == (supersedes is None), "SUPERSEDES", record_id)

    observations = _change_observations(root, before, after, actual_changes)
    expected_current = {
        cast(str, row["after_path"]): _git_blob(root, after, cast(str, row["after_path"]))
        for row in actual_changes
        if row["after_path"] is not None
    }
    current_drift = any(
        _working_blob(root, path) != expected for path, expected in expected_current.items()
    )
    deleted_reintroduced = any(
        change["after_path"] is None
        and _working_blob(root, cast(str, change["before_path"])) is not None
        for change in actual_changes
    )
    ast_incomplete = any(
        cast(dict[str, object], cast(dict[str, object], observation["before"])["ast"])["status"]
        == "INCOMPLETE"
        or cast(dict[str, object], cast(dict[str, object], observation["after"])["ast"])["status"]
        == "INCOMPLETE"
        for observation in observations
    )
    support_drift = bool(gate_ids) and _working_scope_hash(root, gate_ids[0]) != expected_scope_hash
    record_status = (
        "STALE_SOURCE"
        if current_drift or deleted_reintroduced or support_drift
        else "RECORDED_UNREPLAYED"
    )
    if ast_incomplete and record_status == "RECORDED_UNREPLAYED":
        record_status = "OBSERVATION_INCOMPLETE"
    signature = _sha256(
        _canonical(
            {
                "before_commit": before,
                "after_commit": after,
                "gate_ids": gate_ids,
            }
        )
    )
    return record, {
        "id": record_id,
        "status": record_status,
        "review_status": review["status"],
        "gate_ids": gate_ids,
        "gate_status": "NO_REGISTERED_GATE" if not gate_ids else "RECORDED_UNREPLAYED",
        "signature": signature,
        "subject": {"before_commit": before, "after_commit": after},
        "change_observations": observations,
    }


def _validate_ledger(
    root: Path,
    ledger_path: Path,
) -> tuple[
    dict[str, object],
    dict[str, object],
    list[dict[str, object]],
    list[dict[str, str]],
]:
    ledger = _load_object(ledger_path, maximum=MAX_JSON_BYTES, label="V3 progress ledger")
    _object(
        ledger,
        (
            "schema",
            "immutable_inputs",
            "trusted_local_tools",
            "review_premise",
            "nonclaims",
            "work_records",
        ),
        "LEDGER_FIELDS",
    )
    _require(ledger["schema"] == LEDGER_SCHEMA, "LEDGER_SCHEMA", "schema drift")
    review_premise = _object(ledger["review_premise"], ("status", "statement"), "REVIEW_PREMISE")
    _require(
        review_premise["status"] == "EXTERNAL_MAINTAINER_OR_CI_PREMISE",
        "REVIEW_PREMISE",
        "external premise required",
    )
    _text(review_premise["statement"], "REVIEW_PREMISE")
    _strings(ledger["nonclaims"], "LEDGER_NONCLAIMS")
    trusted_tools = _require_hash_rows(
        ledger["trusted_local_tools"], "TRUSTED_LOCAL_TOOLS", allow_empty=False
    )
    _require(
        {row["path"] for row in trusted_tools} == {"tools/check_v3_progress.py"},
        "TRUSTED_LOCAL_TOOLS",
        "only the local checker is bound here",
    )
    for row in trusted_tools:
        tool_blob = _working_blob(root, row["path"])
        _require(
            tool_blob is not None and _sha256(tool_blob) == row["sha256"],
            "TRUSTED_TOOL_DRIFT",
            row["path"],
        )
    inventory = _derive_inventory(root, ledger["immutable_inputs"])
    _require(type(ledger["work_records"]) is list, "WORK_RECORDS", "list required")
    records = cast(list[object], ledger["work_records"])
    _require(bool(records), "WORK_RECORDS", "seed records required")
    normalized_records: list[dict[str, object]] = []
    reports: list[dict[str, object]] = []
    ids: set[str] = set()
    signatures: set[str] = set()
    signatures_by_id: dict[str, str] = {}
    for raw_record in records:
        record, record_report = _validate_record(root, raw_record, inventory)
        record_id = cast(str, record["id"])
        _require(record_id not in ids, "DUPLICATE_RECORD_ID", record_id)
        ids.add(record_id)
        supersedes = record["supersedes"]
        if supersedes is not None:
            _require(supersedes in ids - {record_id}, "INVALID_SUPERSEDES", record_id)
        signature = cast(str, record_report["signature"])
        if supersedes is not None:
            _require(
                signatures_by_id[cast(str, supersedes)] == signature,
                "CORRECTION_SUBJECT",
                record_id,
            )
        _require(
            signature not in signatures or record["kind"] == "CORRECTION",
            "REPEATED_SUPPORT_WORK",
            record_id,
        )
        signatures.add(signature)
        signatures_by_id[record_id] = signature
        normalized_records.append(record)
        reports.append(record_report)
    return ledger, inventory, reports, trusted_tools


def _ledger_relative_path(root: Path, ledger_path: Path) -> str | None:
    try:
        return ledger_path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return None


def _baseline_history(
    root: Path,
    ledger_path: Path,
    current_records: list[dict[str, object]],
    baseline_commit: str | None,
) -> dict[str, object]:
    if baseline_commit is None:
        return {"status": "NOT_REQUESTED"}
    _require_commit(root, baseline_commit)
    _run_git(
        root, ["merge-base", "--is-ancestor", baseline_commit, "HEAD"], "BASELINE_NOT_ANCESTOR"
    )
    relative_ledger = _ledger_relative_path(root, ledger_path)
    _require(
        relative_ledger is not None, "BASELINE_LEDGER_PATH", "ledger must be inside repository"
    )
    baseline_raw = _git_blob(root, baseline_commit, relative_ledger)
    if baseline_raw is None:
        return {
            "status": "LEDGER_ABSENT_AT_TRUSTED_BASELINE",
            "baseline_commit": baseline_commit,
        }
    try:
        baseline_value = json.loads(
            baseline_raw.decode("utf-8"),
            object_pairs_hook=_without_duplicate_keys,
            parse_constant=_reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ProgressReject) as exc:
        if isinstance(exc, ProgressReject):
            raise
        raise ProgressReject("BASELINE_LEDGER_MALFORMED", str(exc)) from exc
    baseline = _object(
        baseline_value,
        (
            "schema",
            "immutable_inputs",
            "trusted_local_tools",
            "review_premise",
            "nonclaims",
            "work_records",
        ),
        "BASELINE_LEDGER_FIELDS",
    )
    _require(type(baseline["work_records"]) is list, "BASELINE_WORK_RECORDS", "list required")
    old_records = cast(list[dict[str, object]], baseline["work_records"])
    _require(
        len(old_records) <= len(current_records)
        and _canonical(current_records[: len(old_records)]) == _canonical(old_records),
        "BASELINE_REWRITE",
        "current records must preserve the trusted baseline prefix",
    )
    return {
        "status": "PRESERVED",
        "baseline_commit": baseline_commit,
        "preserved_record_count": len(old_records),
    }


def _inventory_report(inventory: Mapping[str, object]) -> dict[str, object]:
    return {
        "capability_ids": inventory["capability_ids"],
        "capability_status": "OPEN",
        "route_ids": inventory["route_ids"],
        "route_status": "OPEN",
        "exclusions": [
            {**exclusion, "status": "BASELINE_OBLIGATION_OPEN"}
            for exclusion in cast(list[dict[str, object]], inventory["exclusions"])
        ],
        "tasks": [
            {"id": task_id, "status": "OPEN"} for task_id in cast(list[str], inventory["task_ids"])
        ],
        "normative_registry": inventory["normative_registry"],
    }


def _base_report() -> dict[str, object]:
    return {
        "schema": CHECK_SCHEMA,
        "ok": False,
        "findings": [],
        "claim_ceiling": dict(CLAIM_CEILING),
        **CLAIM_CEILING,
        "closure_gates": {
            "capability_closure": "UNAVAILABLE",
            "formal_core_closure": "UNAVAILABLE",
            "whole_product_closure": "UNAVAILABLE",
        },
    }


def _source_hashes(root: Path, paths: Iterable[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for path in paths:
        raw = _working_blob(root, path)
        _require(raw is not None, "REPLAY_SOURCE_MISSING", path)
        result[path] = _sha256(raw)
    return result


def _junit_node_id(classname: str, name: str) -> str:
    components = classname.split(".")
    module_components: list[str] = []
    class_components: list[str] = []
    for component in components:
        if component.startswith("Test") and class_components == []:
            class_components.append(component)
        elif class_components:
            class_components.append(component)
        else:
            module_components.append(component)
    _require(bool(module_components), "JUNIT_NODE_ID", classname)
    module = "/".join(module_components) + ".py"
    suffix = "::".join([*class_components, name])
    return module + "::" + suffix


def _junit_inventory(junit_path: Path) -> dict[str, object]:
    raw = _read_regular(junit_path, maximum=MAX_JUNIT_BYTES, label="JUnit report")
    try:
        root = element_tree.fromstring(raw)
    except element_tree.ParseError as exc:
        raise ProgressReject("MALFORMED_JUNIT", str(exc)) from exc
    for node in root.iter():
        tag = node.tag.rsplit("}", 1)[-1]
        if tag in {"failure", "error", "skipped"}:
            raise ProgressReject("JUNIT_NONPASS", tag)
        if tag in {"testsuite", "testsuites"}:
            for field in ("failures", "errors", "skipped", "disabled"):
                if field not in node.attrib:
                    continue
                try:
                    count = int(node.attrib[field])
                except ValueError as exc:
                    raise ProgressReject("JUNIT_SUITE_TOTAL", field) from exc
                _require(count >= 0, "JUNIT_SUITE_TOTAL", field)
                _require(count == 0, "JUNIT_NONPASS", field)
    testcases = [node for node in root.iter() if node.tag.rsplit("}", 1)[-1] == "testcase"]
    _require(bool(testcases), "EMPTY_JUNIT", "no testcases")
    node_ids: list[str] = []
    for testcase in testcases:
        classname = testcase.attrib.get("classname")
        name = testcase.attrib.get("name")
        _require(bool(classname) and bool(name), "JUNIT_NODE_ID", "missing classname/name")
        for child in testcase.iter():
            _require(
                "xfail" not in child.attrib.get("type", "").lower(),
                "JUNIT_NONPASS",
                "xfail",
            )
        node_ids.append(_junit_node_id(cast(str, classname), cast(str, name)))
    _require(len(node_ids) == len(set(node_ids)), "DUPLICATE_JUNIT_NODE", "duplicate testcase")
    canonical_nodes = sorted(node_ids)
    return {
        "test_count": len(canonical_nodes),
        "inventory_sha256": _sha256(("\n".join(canonical_nodes) + "\n").encode("utf-8")),
    }


def _fixed_environment() -> dict[str, str]:
    path = os.environ.get("PATH", "")
    _require(bool(path), "REPLAY_ENVIRONMENT", "PATH unavailable")
    return {
        "PATH": path,
        "LANG": "C",
        "LC_ALL": "C",
        "PYTHONHASHSEED": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1",
    }


def _replay_gate(
    root: Path,
    ledger: Mapping[str, object],
    trusted_tools: list[dict[str, str]],
    gate_id: str,
) -> dict[str, object]:
    _require(gate_id in GATE_CATALOG, "UNKNOWN_GATE", gate_id)
    gate = GATE_CATALOG[gate_id]
    records = cast(list[dict[str, object]], ledger["work_records"])
    superseded = {record["supersedes"] for record in records if record["supersedes"] is not None}
    selected = [
        record
        for record in records
        if gate_id in record["gate_ids"] and record["id"] not in superseded
    ]
    _require(len(selected) == 1, "REPLAY_RECORD_COUNT", gate_id)
    record = selected[0]
    expected_hashes = {
        row["path"]: row["sha256"]
        for row in _require_hash_rows(
            record["gate_subject_hashes"], "REPLAY_HASHES", allow_empty=False
        )
    }
    source_paths = cast(tuple[str, ...], gate["source_paths"])
    _require(set(expected_hashes) == set(source_paths), "REPLAY_HASHES", gate_id)
    contract = _object(record["acceptance_contract"], ("path", "sha256"), "REPLAY_CONTRACT")
    contract_path = _safe_path(contract["path"], "REPLAY_CONTRACT")
    _require(contract_path == gate["contract_path"], "REPLAY_CONTRACT", contract_path)
    expected_hashes[contract_path] = _hash(contract["sha256"], "REPLAY_CONTRACT")
    expected_scope_hash = _object(
        record["gate_scope_aggregate"], ("scope_id", "sha256"), "REPLAY_SCOPE"
    )["sha256"]
    _require(
        _working_scope_hash(root, gate_id) == expected_scope_hash,
        "REPLAY_SOURCE_DRIFT",
        gate_id,
    )
    trusted_hashes = {row["path"]: row["sha256"] for row in trusted_tools}
    before = _source_hashes(root, (*expected_hashes, *trusted_hashes))
    _require(before == {**expected_hashes, **trusted_hashes}, "REPLAY_SOURCE_DRIFT", gate_id)

    with tempfile.TemporaryDirectory(prefix="zenodex-v3-progress-") as directory:
        junit_path = Path(directory) / "receipt-copy.xml"
        command = [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "no:cacheprovider",
            "--junitxml",
            str(junit_path),
            *cast(tuple[str, ...], gate["test_paths"]),
        ]
        try:
            result = subprocess.run(
                command,
                cwd=root,
                env=_fixed_environment(),
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                shell=False,
                check=False,
                timeout=cast(int, gate["timeout_seconds"]),
                text=True,
            )
        except subprocess.TimeoutExpired as exc:
            raise ProgressReject("REPLAY_TIMEOUT", gate_id) from exc
        except OSError as exc:
            raise ProgressReject("REPLAY_EXECUTION", type(exc).__name__) from exc
        _require(result.returncode == 0, "REPLAY_NONZERO", str(result.returncode))
        inventory = _junit_inventory(junit_path)
    _require(inventory["test_count"] == gate["expected_test_count"], "REPLAY_TEST_COUNT", gate_id)
    _require(
        inventory["inventory_sha256"] == gate["expected_inventory_sha256"],
        "REPLAY_INVENTORY",
        gate_id,
    )
    after = _source_hashes(root, (*expected_hashes, *trusted_hashes))
    _require(
        after == before == {**expected_hashes, **trusted_hashes}
        and _working_scope_hash(root, gate_id) == expected_scope_hash,
        "REPLAY_SOURCE_DRIFT",
        gate_id,
    )
    return {
        "gate_id": gate_id,
        "status": "SUPPORT_REPLAY_VERIFIED",
        "test_count": inventory["test_count"],
        "inventory_sha256": inventory["inventory_sha256"],
        "dependency_scope": gate["dependency_scope"],
        "review_status": "EXTERNAL_REVIEW_PREMISE_UNACCEPTED",
    }


def check_v3_progress(
    *,
    root: Path = REPO_ROOT,
    ledger_path: Path = DEFAULT_LEDGER,
    baseline_commit: str | None = None,
    replay_gate: str | None = None,
) -> dict[str, object]:
    """Validate the ledger and optionally run one fixed scoped gate."""
    report = _base_report()
    try:
        path = (
            ledger_path
            if ledger_path.is_absolute()
            else _repo_path(root, ledger_path.as_posix(), "LEDGER_PATH")
        )
        ledger, inventory, record_reports, trusted_tools = _validate_ledger(root, path)
        report["baseline_inventory"] = _inventory_report(inventory)
        report["records"] = record_reports
        report["baseline_history"] = _baseline_history(
            root,
            path,
            cast(list[dict[str, object]], ledger["work_records"]),
            baseline_commit,
        )
        if replay_gate is not None:
            report["replay"] = _replay_gate(root, ledger, trusted_tools, replay_gate)
        report["ok"] = True
    except ProgressReject as exc:
        report["findings"] = [{"code": exc.code, "detail": exc.detail}]
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--baseline-commit")
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--gate")
    parser.add_argument("--json", action="store_true", help="JSON is always emitted")
    args = parser.parse_args(argv)
    if args.replay != (args.gate is not None):
        report = _base_report()
        report["findings"] = [
            {"code": "REPLAY_GATE_REQUIRED", "detail": "use --replay with one --gate"}
        ]
    else:
        report = check_v3_progress(
            root=args.root,
            ledger_path=args.ledger,
            baseline_commit=args.baseline_commit,
            replay_gate=args.gate,
        )
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
