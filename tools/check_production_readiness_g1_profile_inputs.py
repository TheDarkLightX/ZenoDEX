#!/usr/bin/env python3
"""Check source-pinned research inputs for the nine open G1 decisions."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_PROFILE_INPUTS_V1.json"
SCHEMA = "zenodex/production-readiness-g1-profile-inputs/v1"
REPAIR_SOURCE_SUBJECT = "63624a3b08f78fe84ee443dcc25c5c61203283b8"

sys.path.insert(0, str(REPO_ROOT))

from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402
from tools.production_readiness_g1_profile_input_contract import (  # noqa: E402
    DECISION_INPUTS,
    INPUT_STATUS,
    MECHANISM_SECTIONS,
    SOURCE_PATHS,
)


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _plain(value: object) -> Any:
    return json.loads(json.dumps(value, sort_keys=True))


def _run_git_bytes(repo_root: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_material(repo_root: Path) -> tuple[list[dict[str, str]], dict[str, bytes]]:
    pins: list[dict[str, str]] = []
    frozen_by_path: dict[str, bytes] = {}
    for path in SOURCE_PATHS:
        frozen = _run_git_bytes(repo_root, "show", f"{REPAIR_SOURCE_SUBJECT}:{path}")
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"profile-input source drift from repair subject: {path}")
        frozen_by_path[path] = frozen
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": REPAIR_SOURCE_SUBJECT,
            }
        )
    return pins, frozen_by_path


def _semantic_binding(
    repo_root: Path,
) -> tuple[dict[str, Any], dict[str, str]]:
    semantic_document = semantics.build_document(repo_root)
    semantic_path = repo_root / semantics.DEFAULT_OUTPUT.relative_to(semantics.REPO_ROOT)
    report = semantics.check_artifact(semantic_path, repo_root)
    if report["ok"] is not True:
        raise ValueError("G1 semantic artifact does not pass its exact-subject checker")
    observed = semantic_path.read_bytes()
    if observed != _encoded(semantic_document):
        raise ValueError("G1 semantic artifact bytes differ from its generated document")
    return semantic_document, {
        "artifact": str(semantic_path.relative_to(repo_root)),
        "checker_status": "EXACT_SUBJECT_PASS",
        "sha256": _sha256(observed),
        "subject": semantics.SOURCE_SUBJECT,
    }


def _definition_lines(path: str, source: bytes) -> dict[str, int]:
    tree = ast.parse(source.decode("utf-8"), filename=path)
    lines: dict[str, list[int]] = {}
    for node in tree.body:
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            lines.setdefault(node.name, []).append(node.lineno)
    duplicates = sorted(name for name, values in lines.items() if len(values) != 1)
    if duplicates:
        raise ValueError(f"profile-input source has duplicate definitions: {path}:{duplicates}")
    return {name: values[0] for name, values in lines.items()}


def _source_observations(
    source_symbols: Mapping[str, object],
    definitions: Mapping[str, Mapping[str, int]],
) -> list[dict[str, Any]]:
    observations: list[dict[str, Any]] = []
    unexpected = sorted(set(source_symbols) - set(SOURCE_PATHS))
    if unexpected:
        raise ValueError(f"profile input references unpinned source paths: {unexpected}")
    for path in SOURCE_PATHS:
        if path not in source_symbols:
            continue
        raw_symbols = source_symbols[path]
        if not isinstance(raw_symbols, tuple) or not raw_symbols:
            raise TypeError(f"source symbols must be a nonempty tuple: {path}")
        symbols: list[dict[str, object]] = []
        for symbol in raw_symbols:
            if not isinstance(symbol, str) or symbol not in definitions[path]:
                raise ValueError(f"profile-input source symbol is absent: {path}:{symbol}")
            symbols.append({"line": definitions[path][symbol], "symbol": symbol})
        observations.append({"path": path, "symbols": symbols})
    if not observations:
        raise ValueError("profile input has no frozen source observations")
    return observations


def _semantic_decisions(document: Mapping[str, Any]) -> list[dict[str, Any]]:
    raw = document.get("profile_decisions")
    if not isinstance(raw, list):
        raise TypeError("semantic profile decisions must be a list")
    decisions = [entry for entry in raw if isinstance(entry, dict)]
    ids = [entry.get("id") for entry in decisions]
    if len(decisions) != len(raw) or set(ids) != set(DECISION_INPUTS):
        raise ValueError("profile-input registry does not match the nine semantic decisions")
    if len(ids) != len(set(ids)):
        raise ValueError("semantic profile decision ids are not unique")
    return decisions


def _decision_entry(
    semantic_entry: Mapping[str, Any],
    definitions: Mapping[str, Mapping[str, int]],
) -> dict[str, Any]:
    decision_id = semantic_entry.get("id")
    if not isinstance(decision_id, str):
        raise TypeError("semantic profile decision id must be a string")
    inputs = DECISION_INPUTS[decision_id]
    missing_sections = sorted(MECHANISM_SECTIONS - set(inputs))
    if missing_sections:
        raise ValueError(f"profile input omits mechanism sections: {decision_id}:{missing_sections}")
    source_symbols = inputs.get("source_symbols")
    if not isinstance(source_symbols, dict):
        raise TypeError(f"profile input source_symbols must be a mapping: {decision_id}")
    return {
        "affected_workflow_families": semantic_entry["affected_workflow_families"],
        "allowed_option_shapes": semantic_entry["allowed_option_shapes"],
        "attack_query": inputs["attack_query"],
        "bounded_model": inputs["bounded_model"],
        "decision_status": "OPEN_UNSELECTED",
        "evidence_lane": inputs["evidence_lane"],
        "game_surface": inputs["game_surface"],
        "id": decision_id,
        "input_status": INPUT_STATUS,
        "observed_research_behavior": inputs["observed_research_behavior"],
        "production_authority": "NONE",
        "promotion_boundary": inputs["promotion_boundary"],
        "question": semantic_entry["question"],
        "required_outputs": semantic_entry["required_outputs"],
        "selected_profile": None,
        "source_observations": _source_observations(source_symbols, definitions),
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    semantic_document, semantic_binding = _semantic_binding(repo_root)
    source_pins, source_material = _source_material(repo_root)
    definitions = {
        path: _definition_lines(path, source_material[path]) for path in SOURCE_PATHS
    }
    decision_inputs = [
        _decision_entry(entry, definitions)
        for entry in _semantic_decisions(semantic_document)
    ]
    if any(entry["selected_profile"] is not None for entry in decision_inputs):
        raise ValueError("research profile inputs cannot select policy")
    document = {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_DECISION_INPUTS_RESEARCH_ONLY",
        "production_promotion": False,
        "policy_authority": "NONE",
        "source_subject": {
            "semantic_base_commit": semantics.SOURCE_SUBJECT,
            "repair_commit": REPAIR_SOURCE_SUBJECT,
            "current_head_must_descend_from_both": True,
        },
        "semantic_binding": semantic_binding,
        "source_pins": source_pins,
        "decision_inputs": decision_inputs,
        "g1_exit_gate": {
            "complete": False,
            "decision_input_count": len(decision_inputs),
            "selected_profile_count": 0,
            "status": "BLOCKED_NINE_POLICY_SELECTIONS_AND_EVIDENCE_OPEN",
        },
        "nonclaims": [
            "Source-pinned research behavior is not normative production policy.",
            "Resolved symbols and file hashes bind review locations; they do not mechanically prove the prose interpretation.",
            "Game surfaces, attack queries, and bounded-model variables are review inputs rather than proofs.",
            "No fee, ratio, threshold, authority, beneficiary, timeout, retry, or terminal owner is selected here.",
            "A passing checker does not close G1, enable a command, mount a writer, or establish production readiness.",
        ],
    }
    return _plain(document)


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
        raise ValueError("profile-input artifact root must be an object")
    return value


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
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
    for label, subject in (
        ("semantic base", semantics.SOURCE_SUBJECT),
        ("repair", REPAIR_SOURCE_SUBJECT),
    ):
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", subject, "HEAD"],
            cwd=repo_root,
            check=False,
        )
        if result.returncode != 0:
            errors.append(f"current HEAD does not descend from the frozen {label} subject")
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated profile inputs")
    except (OSError, TypeError, ValueError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))
    entries = observed.get("decision_inputs")
    selected_count = (
        sum(
            1
            for entry in entries
            if isinstance(entry, dict) and entry.get("selected_profile") is not None
        )
        if isinstance(entries, list)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-profile-inputs-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "decision_input_count": len(entries) if isinstance(entries, list) else 0,
        "selected_profile_count": selected_count,
        "errors": errors,
        "nonclaim": "PASS means only that nine unselected research input packets are exact and source-bound.",
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
    elif report["ok"]:
        print("production readiness G1 profile inputs: PASS (research only)")
    else:
        for error in report["errors"]:
            print(f"production readiness G1 profile inputs: {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
