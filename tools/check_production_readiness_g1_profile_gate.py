#!/usr/bin/env python3
"""Check the exact-subject G1 profile-decision gate.

This gate makes the nine required policy decisions reviewable and replayable
without selecting a policy.  It records the closure conditions and preserves
the no-authority boundary until each decision has one accepted option shape.
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
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_PROFILE_GATE_V1.json"
SCHEMA = "zenodex/production-readiness-g1-profile-gate/v1"

sys.path.insert(0, str(REPO_ROOT))
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402


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


def _decision_gate(decision: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "id": decision["id"],
        "owner": decision["owner"],
        "affected_workflow_families": list(decision["affected_workflow_families"]),
        "question": decision["question"],
        "allowed_option_shapes": list(decision["allowed_option_shapes"]),
        "rejection_conditions": list(decision["rejection_conditions"]),
        "required_outputs": list(decision["required_outputs"]),
        "status": decision["status"],
        "selected_option_shape": None,
        "selected_profile": decision["selected_profile"],
        "production_authority": decision["production_authority"],
        "hold_action": "KEEP_AFFECTED_COMMANDS_UNMOUNTED_UNTIL_DECISION_CLOSED",
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    semantic = semantics.build_document(repo_root)
    decision_gates = [_decision_gate(decision) for decision in semantic["profile_decisions"]]
    option_shapes = {
        shape: dict(details)
        for shape, details in semantic["profile_option_shapes"].items()
    }
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_PROFILE_GATE_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantic["source_subject"],
        "source_pins": semantic["source_pins"],
        "selection_policy": {
            "option_shapes": option_shapes,
            "exactly_one_option_shape_per_decision": True,
            "selected_profile_must_define_all_required_outputs": True,
            "unclosed_decisions_have_no_production_authority": True,
        },
        "decision_gates": decision_gates,
        "exit_gate": {
            "complete": False,
            "status": "BLOCKED_DECISIONS_OPEN",
            "decision_count": len(decision_gates),
            "closed_decision_count": 0,
            "selected_profile_count": 0,
            "production_authority_count": 0,
        },
        "nonclaims": [
            "The gate records required policy decisions and closure conditions only.",
            "No option shape or economic profile is selected by this artifact.",
            "The gate does not implement, prove, mount, or authorize any command.",
            "A decision cannot close until its required outputs and rejection conditions are reviewed.",
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
            errors.append("artifact differs from the exact-subject generated G1 profile gate")
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    gates = observed.get("decision_gates")
    gate_count = len(gates) if isinstance(gates, list) else 0
    closed_count = (
        sum(
            1
            for gate in gates
            if isinstance(gate, Mapping)
            and gate.get("status") == "CLOSED"
            and gate.get("selected_option_shape") is not None
            and gate.get("selected_profile") is not None
        )
        if isinstance(gates, list)
        else 0
    )
    selected_count = (
        sum(
            1
            for gate in gates
            if isinstance(gate, Mapping)
            and (
                gate.get("selected_option_shape") is not None
                or gate.get("selected_profile") is not None
            )
        )
        if isinstance(gates, list)
        else 0
    )
    authority_count = (
        sum(
            1
            for gate in gates
            if isinstance(gate, Mapping) and gate.get("production_authority") != "NONE"
        )
        if isinstance(gates, list)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-profile-gate-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "decision_gate_count": gate_count,
        "closed_decision_count": closed_count,
        "selected_profile_count": selected_count,
        "production_authority_count": authority_count,
        "errors": errors,
        "nonclaim": "PASS means only that the decision gate is exact and source-bound; it does not promote G1 or production readiness.",
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
