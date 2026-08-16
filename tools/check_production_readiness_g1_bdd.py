#!/usr/bin/env python3
"""Check the exact-subject, research-only G1 BDD contract.

This contract is generated from the closed source command registry.  It gives
each command an explicit workflow and scenario obligations while preserving
the distinction between a documented scenario and executable evidence.
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
sys.path.insert(0, str(REPO_ROOT))

from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402

DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_BDD_V1.json"
SCHEMA = "zenodex/production-readiness-g1-bdd/v1"
SEMANTICS_OUTPUT = semantics.DEFAULT_OUTPUT
EXPECTED_COMMANDS = semantics.EXPECTED_COMMANDS
EXPECTED_DISABLED = semantics.EXPECTED_DISABLED
SOURCE_SUBJECT = semantics.SOURCE_SUBJECT
build_semantics_document = semantics.build_document

_STATEFUL_SCENARIO_CLASS = "replay"
_SCENARIO_CLASS_ALIASES = {"cancel": "cancellation"}


def _scenario_classes(entry: Mapping[str, Any]) -> list[str]:
    classes = list(entry["bdd_required_scenario_classes"])
    additional = [_SCENARIO_CLASS_ALIASES.get(value, value) for value in entry["bdd_additional_scenario_classes"]]
    for scenario_class in (_STATEFUL_SCENARIO_CLASS, *additional):
        if scenario_class not in classes:
            classes.append(scenario_class)
    return classes


def _scenario_text(command_id: str, scenario_class: str) -> tuple[str, str, str]:
    if scenario_class == "happy":
        return (
            f"the authenticated {command_id} command binds the current state and selected profile",
            f"an authorized actor submits one canonical {command_id} command",
            "the deterministic candidate contains the complete declared state, value, receipt, and effect projection",
        )
    if scenario_class == "authorization":
        return (
            f"the signer, deployment, epoch, or proof context for {command_id} is foreign or stale",
            f"the actor submits the well-formed {command_id} payload",
            "the command rejects before economic state or external effects change",
        )
    if scenario_class == "rejection":
        return (
            f"the business precondition for {command_id} is false or its integer policy bound fails",
            f"the authenticated {command_id} command reaches the canonical transition",
            "the declared rejection path is observed with reject-is-no-op economic state and no unowned effect",
        )
    if scenario_class == "accounting":
        return (
            f"the {command_id} transition moves one or more value atoms, liabilities, fees, or residues",
            f"the authenticated {command_id} candidate is evaluated",
            "every asset, owner, custody, supply, liability, fee, and rounding delta reconciles with no unnamed remainder",
        )
    if scenario_class == "freshness":
        return (
            f"the current oracle, epoch, or proof context for {command_id} is stale or pending",
            f"the risk-increasing {command_id} command is evaluated",
            "the command rejects or enters only the explicitly declared recovery subset",
        )
    if scenario_class == "commit":
        return (
            f"the {command_id} workflow is in its commit phase with an escrowed amount or inventory",
            f"the actor submits a canonical commitment for {command_id}",
            "the commitment binds the declared fields and phase without revealing or moving unowned value",
        )
    if scenario_class == "reveal":
        return (
            f"a valid or invalid commitment exists for the {command_id} workflow",
            f"the actor submits a reveal for {command_id}",
            "the reveal either matches the commitment and advances the phase or rejects without partial settlement",
        )
    if scenario_class == "cancellation":
        return (
            f"the {command_id} lifecycle has an escrowed amount or inventory eligible for cancellation or expiry",
            f"the authorized actor executes {command_id}",
            "escrow, refund, slash, terminal ownership, and outbox ancestry reconcile exactly once",
        )
    if scenario_class == "recovery":
        return (
            f"a crash or restart occurs around the {command_id} publication boundary",
            "the durable state reopens and attempts to resume the workflow",
            "only the exact committed PRE or POST state is accepted and no reopen alone grants writer authority",
        )
    if scenario_class == "terminal":
        return (
            f"the {command_id} workflow reaches its declared terminal lifecycle",
            "the terminal transition is evaluated with the current state and profile",
            "every claim, custody atom, liability, residue, and effect has one exact terminal owner",
        )
    if scenario_class == "replay":
        return (
            f"the {command_id} command identity, nonce, or nullifier is already committed",
            "the same canonical command is submitted again",
            "the result is classified deterministically without a duplicate economic delta or external effect",
        )
    if scenario_class == "outage":
        return (
            f"the external Tau or destination service is unavailable during {command_id}",
            f"the deterministic {command_id} transition is evaluated",
            "the state does not depend on live reachability and pending custody or outbox identity remains recoverable",
        )
    if scenario_class == "rejoin":
        return (
            f"an actor or deployment returns after an outage with persisted {command_id} state",
            "the authenticated rejoin evidence is evaluated",
            "continuity, pending effects, and authority epoch reconcile exactly without replaying value movement",
        )
    raise ValueError(f"unknown scenario class: {scenario_class}")


def _build_workflow(
    entry: Mapping[str, Any],
    workflow_number: int,
    scenario_number: int,
) -> tuple[dict[str, Any], int]:
    command_id = str(entry["id"])
    classes = _scenario_classes(entry)
    requirements = list(entry["formal_obligation_ids"])
    scenarios: list[dict[str, Any]] = []
    next_scenario = scenario_number
    for scenario_class in classes:
        given, when, then = _scenario_text(command_id, scenario_class)
        scenarios.append(
            {
                "id": f"BDD-G1-{next_scenario:03d}",
                "class": scenario_class,
                "given": given,
                "when": when,
                "then": then,
                "requirements": requirements,
                "evidence_status": "UNIMPLEMENTED_RESEARCH_SCENARIO",
            }
        )
        next_scenario += 1

    return (
        {
            "id": f"WF-G1-{workflow_number:03d}",
            "command_id": command_id,
            "workflow_family": entry["workflow_family"],
            "actor": entry["actor"],
            "owner": entry["economic_owner"],
            "entrypoint": entry["core_transition"],
            "terminal_path": entry["terminal_path"],
            "required_scenario_classes": classes,
            "scenarios": scenarios,
            "production_mount": "UNMOUNTED_RESEARCH_ONLY",
        },
        next_scenario,
    )


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    semantics = build_semantics_document(repo_root)
    entries = semantics["command_registry"]
    if len(entries) != len(EXPECTED_COMMANDS):
        raise ValueError("semantic registry does not cover the exact command count")

    workflows: list[dict[str, Any]] = []
    next_scenario = 1
    for workflow_number, entry in enumerate(entries, start=1):
        workflow, next_scenario = _build_workflow(entry, workflow_number, next_scenario)
        workflows.append(workflow)

    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_BDD_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": semantics["source_subject"],
        "source_pins": semantics["source_pins"],
        "source_mapping_artifact": str(SEMANTICS_OUTPUT.relative_to(repo_root)),
        "registry_binding": {
            "command_count": len(EXPECTED_COMMANDS),
            "disabled_command_count": len(EXPECTED_DISABLED),
            "command_ids": sorted(entry["id"] for entry in entries),
            "disabled_command_ids": sorted(
                entry["id"]
                for entry in entries
                if entry["v1_profile"] == "M6_RESEARCH_DISABLED_COMMANDS_V1"
            ),
        },
        "scenario_policy": {
            "universal_classes": [
                "happy",
                "rejection",
                "authorization",
                "recovery",
                "terminal",
                _STATEFUL_SCENARIO_CLASS,
            ],
            "cancellation_where_applicable": sorted(
                entry["id"]
                for entry in entries
                if "cancellation" in entry["bdd_required_scenario_classes"]
            ),
            "family_additional_classes": sorted(
                {
                    _SCENARIO_CLASS_ALIASES.get(scenario_class, scenario_class)
                    for entry in entries
                    for scenario_class in entry["bdd_additional_scenario_classes"]
                }
            ),
            "scenario_evidence_status": "UNIMPLEMENTED_RESEARCH_SCENARIO",
            "required_before_promotion": [
                "executable BDD or equivalent deterministic tests",
                "reject-is-no-op and terminal-drain evidence",
                "runtime projection and mounted-entrypoint evidence",
            ],
        },
        "open_profile_decisions": [
            decision["id"] for decision in semantics["profile_decisions"]
        ],
        "workflows": workflows,
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_OPEN_PROFILE_DECISIONS_AND_UNIMPLEMENTED_SCENARIOS",
            "claim": "BDD obligations are catalogued; no scenario is executable evidence.",
        },
        "nonclaims": [
            "A BDD scenario text is not a passing test or a proof.",
            "This contract does not select economic policy or authorize a command.",
            "UNMOUNTED_RESEARCH_ONLY entrypoints cannot settle value or promote production readiness.",
        ],
    }


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


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", SOURCE_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    if ancestry.returncode != 0:
        errors.append("current HEAD does not descend from the frozen source subject")
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated BDD contract")
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError):
        errors.append("unable to load or regenerate the exact-subject BDD contract")

    workflows = observed.get("workflows")
    workflow_count = len(workflows) if isinstance(workflows, list) else 0
    scenario_count = (
        sum(
            len(workflow.get("scenarios", []))
            for workflow in workflows
            if isinstance(workflow, dict)
            and isinstance(workflow.get("scenarios"), list)
        )
        if isinstance(workflows, list)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-bdd-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "workflow_count": workflow_count,
        "scenario_count": scenario_count,
        "command_count": len(EXPECTED_COMMANDS),
        "disabled_command_count": len(EXPECTED_DISABLED),
        "errors": errors,
        "nonclaim": "PASS means only that the research BDD catalogue is exact and source-bound; it does not promote executable evidence or production readiness.",
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
