#!/usr/bin/env python3
"""Check the exact-subject G1 state and value-delta obligation gate.

The gate records the declared state fields and delta classes while preserving
their explicit closure gaps.  It does not invent equations, owners, codecs,
or production authority for the economic system.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_STATE_DELTA_GATE_V1.json"
SCHEMA = "zenodex/production-readiness-g1-state-delta-gate/v1"
RUNTIME_SOURCE_PATH = "src/core/global_settlement_types_v1.py"
RUNTIME_CANONICAL_SOURCE_PATH = "src/state/canonical.py"
RUNTIME_STATE_CLASS = "GlobalEconomicStateV1"
RUNTIME_EFFECT_KIND_CLASS = "EconomicEffectKindV1"
RUNTIME_CANONICAL_HELPER = "canonical_json_bytes"

RUNTIME_STATE_FIELD_CANDIDATES: dict[str, tuple[str, ...]] = {
    "balances": ("balances",),
    "custody": ("custody",),
    "supply": ("supplies",),
    "debt": ("liabilities",),
    "lp_state": (),
    "perps_liabilities": ("liabilities",),
    "escrows": ("custody", "outbox", "terminal_obligations"),
    "reserves": ("reserves",),
    "auctions": (),
    "withdrawals": ("outbox", "custody", "terminal_obligations"),
    "outbox": ("outbox",),
    "history": ("history_root",),
    "nullifiers": ("replay_state",),
    "release_state": ("writer_epoch", "profile_root", "lane_roots"),
}
RUNTIME_DELTA_KIND_CANDIDATES: dict[str, tuple[str, ...]] = {
    "internal_transfer": ("ACCOUNT_MOVEMENT",),
    "mint": ("ISSUE",),
    "burn": ("BURN",),
    "liability": ("LIABILITY",),
    "external_in": ("CUSTODY", "ACCOUNT_MOVEMENT"),
    "external_out": ("CUSTODY", "ACCOUNT_MOVEMENT"),
    "refund": ("ACCOUNT_MOVEMENT", "CUSTODY"),
    "slash": ("SLASH",),
}

sys.path.insert(0, str(REPO_ROOT))
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402

STATE_CLOSURE_OBLIGATIONS = (
    "FIELD_TYPES_AND_OWNERSHIP",
    "CANONICAL_ROOT_CODEC_AND_ORDER",
    "VALUE_DELTA_EVENT_EQUATIONS",
    "CONSERVATION_AND_CUSTODY_RECONCILIATION",
    "TERMINAL_CLAIM_AND_LIABILITY_DRAIN",
    "FORMAL_RUNTIME_AND_COMMIT_PARITY",
)


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


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _state_projection(value: Mapping[str, Any]) -> dict[str, Any]:
    fields = value["fields"]
    field_contracts = value["field_contracts"]
    return {
        "schema": value["schema"],
        "status": value["status"],
        "closure_status": value["closure_status"],
        "authority": value["authority"],
        "canonical_order": list(value["canonical_order"]),
        "fields": [dict(field) for field in fields],
        "field_contracts": [dict(contract) for contract in field_contracts],
        "no_production_authority": value["no_production_authority"],
        "obligation_status": "OPEN_GAP",
        "field_count": len(fields),
        "field_contract_count": len(field_contracts),
        "all_fields_have_terminal_paths": all(
            field.get("terminal_path_required") is True for field in fields
        ),
    }


def _value_delta_algebra(value: Mapping[str, Any]) -> dict[str, Any]:
    class_contracts = value["class_contracts"]
    delta_classes = value["delta_classes"]
    return {
        "status": value["status"],
        "closure_status": value["closure_status"],
        "entry_key": list(value["entry_key"]),
        "amount_representation": value["amount_representation"],
        "delta_classes": list(delta_classes),
        "class_contracts": [dict(contract) for contract in class_contracts],
        "laws": list(value["laws"]),
        "no_production_authority": value["no_production_authority"],
        "obligation_status": "OPEN_GAP",
        "delta_class_count": len(delta_classes),
        "class_contract_count": len(class_contracts),
        "all_delta_classes_have_contracts": len(delta_classes) == len(class_contracts),
    }


def _class_definition(tree: ast.Module, name: str) -> ast.ClassDef:
    matches = [node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name]
    if len(matches) != 1:
        raise ValueError(f"runtime source class must occur exactly once: {name}")
    return matches[0]


def _annotated_field_names(node: ast.ClassDef) -> tuple[str, ...]:
    names = tuple(
        child.target.id
        for child in node.body
        if isinstance(child, ast.AnnAssign)
        and isinstance(child.target, ast.Name)
    )
    if not names:
        raise ValueError(f"runtime source class has no annotated fields: {node.name}")
    if len(names) != len(set(names)):
        raise ValueError(f"runtime source class has duplicate annotated fields: {node.name}")
    return names


def _canonical_method_keys(node: ast.ClassDef) -> tuple[str, ...]:
    methods = [
        child
        for child in node.body
        if isinstance(child, ast.FunctionDef) and child.name == "to_canonical"
    ]
    if len(methods) != 1:
        raise ValueError(f"runtime source class must define one to_canonical method: {node.name}")
    body = list(methods[0].body)
    if (
        body
        and isinstance(body[0], ast.Expr)
        and isinstance(body[0].value, ast.Constant)
        and isinstance(body[0].value.value, str)
    ):
        body = body[1:]
    if (
        len(body) != 1
        or not isinstance(body[0], ast.Return)
        or not isinstance(body[0].value, ast.Dict)
    ):
        raise ValueError(f"runtime source to_canonical must be one direct literal return: {node.name}")
    mapping = body[0].value
    keys = tuple(
        key.value
        for key in mapping.keys
        if isinstance(key, ast.Constant) and isinstance(key.value, str)
    )
    if len(keys) != len(mapping.keys):
        raise ValueError(f"runtime source to_canonical has a non-literal key: {node.name}")
    if len(keys) != len(set(keys)):
        raise ValueError(f"runtime source to_canonical has duplicate keys: {node.name}")
    return keys


def _enum_values(node: ast.ClassDef) -> tuple[str, ...]:
    if not any(
        (isinstance(base, ast.Name) and base.id == "Enum")
        or (isinstance(base, ast.Attribute) and base.attr == "Enum")
        for base in node.bases
    ):
        raise ValueError(f"runtime effect-kind class must inherit Enum: {node.name}")
    values: list[str] = []
    for child in node.body:
        if not isinstance(child, ast.Assign):
            continue
        if len(child.targets) != 1 or not isinstance(child.targets[0], ast.Name):
            raise ValueError(f"runtime effect-kind member shape is not a simple assignment: {node.name}")
        member_name = child.targets[0].id
        if member_name.startswith("_"):
            continue
        if not isinstance(child.value, ast.Constant) or not isinstance(child.value.value, str):
            raise ValueError(f"runtime effect-kind member is not a string: {node.name}")
        values.append(child.value.value)
    if not values:
        raise ValueError(f"runtime effect-kind enum has no string values: {node.name}")
    if len(values) != len(set(values)):
        raise ValueError(f"runtime effect-kind enum has duplicate values: {node.name}")
    return tuple(values)


def _function_line(tree: ast.Module, name: str) -> int:
    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    ]
    if len(matches) != 1:
        raise ValueError(f"runtime source function must occur exactly once: {name}")
    return matches[0].lineno


def _returned_call_name(tree: ast.Module, name: str) -> str:
    functions = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    ]
    if len(functions) != 1:
        raise ValueError(f"runtime source function must occur exactly once: {name}")
    calls = [
        child.value.func.id
        for child in ast.walk(functions[0])
        if isinstance(child, ast.Return)
        and isinstance(child.value, ast.Call)
        and isinstance(child.value.func, ast.Name)
    ]
    if len(calls) != 1:
        raise ValueError(f"runtime source function must return one direct call: {name}")
    return calls[0]


def _frozen_source(
    repo_root: Path,
    path: str,
    *,
    read_current: Callable[[Path], bytes] | None = None,
) -> bytes:
    frozen = subprocess.run(
        ["git", "show", f"{semantics.SOURCE_SUBJECT}:{path}"],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout
    current = (repo_root / path).read_bytes() if read_current is None else read_current(repo_root / path)
    if current != frozen:
        raise ValueError(f"runtime source drift from frozen subject: {path}")
    return frozen


def _runtime_projection(
    repo_root: Path,
    *,
    read_current: Callable[[Path], bytes] | None = None,
) -> dict[str, Any]:
    frozen = _frozen_source(repo_root, RUNTIME_SOURCE_PATH, read_current=read_current)
    canonical_frozen = _frozen_source(
        repo_root, RUNTIME_CANONICAL_SOURCE_PATH, read_current=read_current
    )
    tree = ast.parse(frozen.decode("utf-8"), filename=RUNTIME_SOURCE_PATH)
    canonical_tree = ast.parse(
        canonical_frozen.decode("utf-8"), filename=RUNTIME_CANONICAL_SOURCE_PATH
    )
    state_class = _class_definition(tree, RUNTIME_STATE_CLASS)
    effect_kind_class = _class_definition(tree, RUNTIME_EFFECT_KIND_CLASS)
    state_fields = _annotated_field_names(state_class)
    canonical_keys = _canonical_method_keys(state_class)
    effect_kinds = _enum_values(effect_kind_class)
    canonical_delegate = _returned_call_name(tree, "canonical_global_bytes_v1")
    if canonical_delegate != RUNTIME_CANONICAL_HELPER:
        raise ValueError(
            "canonical_global_bytes_v1 delegates to an unexpected helper: "
            f"{canonical_delegate}"
        )
    return {
        "status": "SOURCE_SHAPE_INVENTORY_RESEARCH_ONLY",
        "source_subject": semantics.SOURCE_SUBJECT,
        "source_pins": [
            {
                "path": RUNTIME_SOURCE_PATH,
                "sha256": hashlib.sha256(frozen).hexdigest(),
                "subject": semantics.SOURCE_SUBJECT,
            },
            {
                "path": RUNTIME_CANONICAL_SOURCE_PATH,
                "sha256": hashlib.sha256(canonical_frozen).hexdigest(),
                "subject": semantics.SOURCE_SUBJECT,
            },
        ],
        "state_type": {
            "path": RUNTIME_SOURCE_PATH,
            "class": RUNTIME_STATE_CLASS,
            "class_line": state_class.lineno,
            "declared_field_count": len(state_fields),
            "declared_fields": list(state_fields),
            "literal_projection_key_order": list(canonical_keys),
            "literal_projection_starts_with_schema": canonical_keys[:1] == ("schema",),
            "declared_fields_match_literal_projection": tuple(canonical_keys[1:]) == state_fields,
        },
        "effect_kind_type": {
            "path": RUNTIME_SOURCE_PATH,
            "class": RUNTIME_EFFECT_KIND_CLASS,
            "class_line": effect_kind_class.lineno,
            "kind_count": len(effect_kinds),
            "kinds": list(effect_kinds),
        },
        "canonical_codec": {
            "path": RUNTIME_SOURCE_PATH,
            "symbol": "canonical_global_bytes_v1",
            "line": _function_line(tree, "canonical_global_bytes_v1"),
            "delegate": canonical_delegate,
            "delegate_line": _function_line(canonical_tree, RUNTIME_CANONICAL_HELPER),
            "delegate_path": RUNTIME_CANONICAL_SOURCE_PATH,
            "status": "PRESENT_SOURCE_SHAPE_ONLY",
        },
        "semantic_mapping_status": "GAP_ABSTRACT_14_FIELD_AND_8_DELTA_MAPPING_UNPROVED",
        "production_authority": "NONE",
        "nonclaims": [
            "A source-shape match does not prove that runtime fields implement the abstract G1 projection.",
            "The inventory does not prove event equations, custody reconciliation, terminal drains, or mounted reachability.",
        ],
    }


def _runtime_mapping_gap_ledger(
    state: Mapping[str, Any],
    algebra: Mapping[str, Any],
    runtime: Mapping[str, Any],
) -> dict[str, Any]:
    runtime_fields = tuple(runtime["state_type"]["declared_fields"])
    runtime_effect_kinds = tuple(runtime["effect_kind_type"]["kinds"])
    field_mappings: list[dict[str, Any]] = []
    candidate_fields: set[str] = set()
    for field in state["fields"]:
        abstract_name = field["name"]
        candidate_names = RUNTIME_STATE_FIELD_CANDIDATES[abstract_name]
        present_candidates = tuple(name for name in candidate_names if name in runtime_fields)
        candidate_fields.update(present_candidates)
        field_mappings.append(
            {
                "abstract_field": abstract_name,
                "candidate_runtime_fields": list(present_candidates),
                "status": (
                    "UNPROVED_CANDIDATE"
                    if present_candidates
                    else "NO_DEDICATED_RUNTIME_FIELD_CANDIDATE"
                ),
            }
        )

    delta_mappings: list[dict[str, Any]] = []
    candidate_effect_kinds: set[str] = set()
    for delta_class in algebra["delta_classes"]:
        candidate_names = RUNTIME_DELTA_KIND_CANDIDATES[delta_class]
        present_candidates = tuple(name for name in candidate_names if name in runtime_effect_kinds)
        candidate_effect_kinds.update(present_candidates)
        delta_mappings.append(
            {
                "abstract_delta_class": delta_class,
                "candidate_runtime_effect_kinds": list(present_candidates),
                "status": (
                    "UNPROVED_EFFECT_KIND_CANDIDATE"
                    if present_candidates
                    else "NO_RUNTIME_EFFECT_KIND_CANDIDATE"
                ),
            }
        )

    return {
        "status": "GAP_STRUCTURAL_CANDIDATES_ONLY",
        "source_subject": runtime["source_subject"],
        "abstract_field_count": len(field_mappings),
        "abstract_delta_class_count": len(delta_mappings),
        "field_mappings": field_mappings,
        "delta_mappings": delta_mappings,
        "unmapped_abstract_fields": [
            mapping["abstract_field"]
            for mapping in field_mappings
            if mapping["status"] == "NO_DEDICATED_RUNTIME_FIELD_CANDIDATE"
        ],
        "runtime_fields_without_value_candidate": [
            field for field in runtime_fields if field not in candidate_fields
        ],
        "unmapped_abstract_delta_classes": [
            mapping["abstract_delta_class"]
            for mapping in delta_mappings
            if mapping["status"] == "NO_RUNTIME_EFFECT_KIND_CANDIDATE"
        ],
        "runtime_effect_kinds_without_abstract_delta_candidate": [
            kind for kind in runtime_effect_kinds if kind not in candidate_effect_kinds
        ],
        "semantic_mapping_status": "GAP_ABSTRACT_14_FIELD_AND_8_DELTA_MAPPING_UNPROVED",
        "production_authority": "NONE",
        "nonclaims": [
            "A candidate name or effect-kind correspondence does not prove semantic ownership or event coverage.",
            "A missing dedicated runtime field does not prove that a value cannot be carried indirectly.",
            "Unmapped runtime effect kinds do not authorize their use or establish unsupported behavior safety.",
        ],
    }


def build_document(
    repo_root: Path = REPO_ROOT,
    *,
    read_current: Callable[[Path], bytes] | None = None,
) -> dict[str, Any]:
    semantic = semantics.build_document(repo_root)
    state = semantic["global_state_projection"]
    algebra = semantic["value_delta_algebra"]
    state_projection = _state_projection(state)
    value_delta_algebra = _value_delta_algebra(algebra)
    runtime_projection = _runtime_projection(repo_root, read_current=read_current)
    runtime_mapping_gap_ledger = _runtime_mapping_gap_ledger(
        state, algebra, runtime_projection
    )
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_STATE_DELTA_GATE_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantic["source_subject"],
        "source_pins": semantic["source_pins"],
        "runtime_projection": runtime_projection,
        "runtime_mapping_gap_ledger": runtime_mapping_gap_ledger,
        "state_projection": state_projection,
        "value_delta_algebra": value_delta_algebra,
        "closure_obligations": [
            {
                "id": obligation,
                "status": "OPEN_GAP",
                "required_evidence": [
                    "exact_subject_source_binding",
                    "typed_integer_units_and_ownership",
                    "deterministic_checker_or_machine_checked_proof",
                    "negative_reject_no_commit_evidence",
                ],
            }
            for obligation in STATE_CLOSURE_OBLIGATIONS
        ],
        "exit_gate": {
            "complete": False,
            "status": "BLOCKED_STATE_AND_DELTA_CLOSURE_GAPS",
            "state_field_count": state_projection["field_count"],
            "delta_class_count": value_delta_algebra["delta_class_count"],
            "open_obligation_count": len(STATE_CLOSURE_OBLIGATIONS),
            "production_authority": "NONE",
        },
        "nonclaims": [
            "The declared fields and delta classes are an obligation inventory, not a complete economic algebra.",
            "OPEN_GAP means field types, equations, ownership, codecs, and reconciliation remain unverified.",
            "The gate does not implement, prove, mount, or authorize settlement.",
            "A passing checker result confirms exact source binding only.",
        ],
    }


def check_artifact(
    path: Path,
    repo_root: Path = REPO_ROOT,
    *,
    read_current: Callable[[Path], bytes] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", semantics.SOURCE_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    if ancestry.returncode != 0:
        errors.append("current HEAD does not descend from the frozen G1 source subject")
    try:
        expected = build_document(repo_root, read_current=read_current)
        observed = _load(path)
        if path.read_bytes() != _encoded(observed):
            errors.append("artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated G1 state-delta gate")
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    state = observed.get("state_projection")
    algebra = observed.get("value_delta_algebra")
    runtime = observed.get("runtime_projection")
    mapping = observed.get("runtime_mapping_gap_ledger")
    obligations = observed.get("closure_obligations")
    field_count = state.get("field_count", 0) if isinstance(state, Mapping) else 0
    delta_class_count = algebra.get("delta_class_count", 0) if isinstance(algebra, Mapping) else 0
    open_obligation_count = len(obligations) if isinstance(obligations, list) else 0
    return {
        "schema": "zenodex/production-readiness-g1-state-delta-gate-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "state_field_count": field_count,
        "delta_class_count": delta_class_count,
        "open_obligation_count": open_obligation_count,
        "runtime_state_field_count": runtime.get("state_type", {}).get("declared_field_count", 0)
        if isinstance(runtime, Mapping)
        else 0,
        "runtime_effect_kind_count": runtime.get("effect_kind_type", {}).get("kind_count", 0)
        if isinstance(runtime, Mapping)
        else 0,
        "runtime_mapping_field_count": mapping.get("abstract_field_count", 0)
        if isinstance(mapping, Mapping)
        else 0,
        "runtime_mapping_delta_class_count": mapping.get("abstract_delta_class_count", 0)
        if isinstance(mapping, Mapping)
        else 0,
        "unmapped_abstract_field_count": len(mapping.get("unmapped_abstract_fields", []))
        if isinstance(mapping, Mapping)
        and isinstance(mapping.get("unmapped_abstract_fields"), list)
        else 0,
        "unmapped_runtime_effect_kind_count": len(
            mapping.get("runtime_effect_kinds_without_abstract_delta_candidate", [])
        )
        if isinstance(mapping, Mapping)
        and isinstance(mapping.get("runtime_effect_kinds_without_abstract_delta_candidate"), list)
        else 0,
        "production_authority": "NONE",
        "errors": errors,
        "nonclaim": "PASS means only that the state-delta obligation inventory is exact and source-bound; it does not promote G1 or production readiness.",
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, build_document(args.repo_root))
    report = check_artifact(args.output, args.repo_root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if report["ok"] else "FAIL")
        for error in report["errors"]:
            print(f"error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
