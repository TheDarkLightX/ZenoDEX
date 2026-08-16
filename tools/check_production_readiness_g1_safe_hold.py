#!/usr/bin/env python3
"""Check the policy-neutral G1 no-launch safe hold.

The safe hold keeps every command unmounted while the nine G1 profile
decisions remain open.  It records a deterministic fail-closed boundary and
does not select economic policy or create publication authority.
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
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_SAFE_HOLD_V1.json"
SCHEMA = "zenodex/production-readiness-g1-safe-hold/v1"

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


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    semantic = semantics.build_document(repo_root)
    command_registry = semantic["command_registry"]
    profile_decisions = semantic["profile_decisions"]
    command_routes = [
        {
            "command_id": entry["id"],
            "workflow_family": entry["workflow_family"],
            "blocking_profile_decision_ids": list(entry["blocking_profile_decision_ids"]),
            "source_enablement": entry["production_enablement"],
            "safe_hold_status": "UNMOUNTED_RESEARCH_ONLY",
            "production_writer_declared": False,
            "authority": "NONE",
        }
        for entry in command_registry
    ]
    decision_holds = [
        {
            "id": decision["id"],
            "status": decision["status"],
            "selected_profile": decision["selected_profile"],
            "hold_action": "KEEP_AFFECTED_COMMANDS_UNMOUNTED_UNTIL_CLOSED",
            "required_outputs": list(decision["required_outputs"]),
        }
        for decision in profile_decisions
    ]
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_SAFE_HOLD_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantic["source_subject"],
        "source_pins": semantic["source_pins"],
        "hold_policy": {
            "mode": "NO_LAUNCH_PROFILE",
            "action": "KEEP_ALL_COMMANDS_UNMOUNTED_UNTIL_PROFILE_DECISIONS_CLOSE",
            "selected_profile_count": 0,
            "production_writer_count": 0,
            "authority": "NONE",
        },
        "profile_decision_holds": decision_holds,
        "command_routes": command_routes,
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_OPEN_PROFILE_DECISIONS",
            "command_count": len(command_routes),
            "held_command_count": len(command_routes),
            "selected_profile_count": 0,
            "production_writer_count": 0,
        },
        "nonclaims": [
            "The safe hold does not select an economic profile.",
            "The safe hold does not implement, prove, mount, or authorize a command.",
            "UNMOUNTED_RESEARCH_ONLY is a stop condition, not production evidence.",
            "G1 remains incomplete until every enabled command has a closed profile and executable evidence.",
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
            errors.append("artifact differs from the exact-subject generated G1 safe hold")
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    routes = observed.get("command_routes")
    route_count = len(routes) if isinstance(routes, list) else 0
    writer_count = (
        sum(
            1
            for route in routes
            if isinstance(route, dict) and route.get("production_writer_declared") is True
        )
        if isinstance(routes, list)
        else 0
    )
    hold_policy = observed.get("hold_policy")
    selected_profile_count = (
        hold_policy.get("selected_profile_count", 0)
        if isinstance(hold_policy, Mapping)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-safe-hold-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "command_route_count": route_count,
        "declared_production_writer_count": writer_count,
        "selected_profile_count": selected_profile_count,
        "errors": errors,
        "nonclaim": "PASS means only that the no-launch safe hold is exact and source-bound; it does not promote G1 or production readiness.",
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
