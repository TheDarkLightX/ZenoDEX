#!/usr/bin/env python3
"""Check the exact-subject G1 state and value-delta obligation gate.

The gate records the declared state fields and delta classes while preserving
their explicit closure gaps.  It does not invent equations, owners, codecs,
or production authority for the economic system.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_STATE_DELTA_GATE_V1.json"
SCHEMA = "zenodex/production-readiness-g1-state-delta-gate/v1"

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


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    semantic = semantics.build_document(repo_root)
    state = semantic["global_state_projection"]
    algebra = semantic["value_delta_algebra"]
    state_projection = _state_projection(state)
    value_delta_algebra = _value_delta_algebra(algebra)
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_STATE_DELTA_GATE_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantic["source_subject"],
        "source_pins": semantic["source_pins"],
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


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
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
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated G1 state-delta gate")
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    state = observed.get("state_projection")
    algebra = observed.get("value_delta_algebra")
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
