#!/usr/bin/env python3
"""Validate the ZenoDEX consensus semantic BDD front door.

This checker is intentionally dependency-free. It treats the Gherkin feature
files as the human-readable front door, then verifies that the machine-readable
contract lists each scenario, preserves layer/status tags, and keeps known
overclaim phrases out of scoped differentials.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


REPO = Path(__file__).resolve().parents[2]
DEFAULT_CONTRACT = REPO / "config" / "semantics" / "zenodex_consensus_contract_v1.json"


@dataclass(frozen=True)
class Scenario:
    scenario_id: str
    name: str
    layer: str
    status: str
    path: Path
    line: int


def _load_json(path: Path) -> Mapping[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path}: invalid JSON: {exc}") from exc
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path}: top-level JSON must be an object")
    return obj


def _repo_path(raw: str) -> Path:
    path = Path(raw)
    return path if path.is_absolute() else REPO / path


def parse_feature(path: Path) -> list[Scenario]:
    text = path.read_text(encoding="utf-8")
    pending_tags: list[str] = []
    scenarios: list[Scenario] = []
    for line_no, raw in enumerate(text.splitlines(), start=1):
        stripped = raw.strip()
        if stripped.startswith("@"):
            pending_tags = re.findall(r"@[^\s]+", stripped)
            continue
        if not stripped.startswith("Scenario:"):
            continue
        tags: dict[str, str] = {}
        for tag in pending_tags:
            body = tag[1:]
            if ":" in body:
                key, value = body.split(":", 1)
                tags[key] = value
        pending_tags = []
        missing = [key for key in ("scenario", "layer", "status") if key not in tags]
        if missing:
            raise ValueError(f"{path}:{line_no}: scenario missing tags {missing}")
        name = stripped.split(":", 1)[1].strip()
        scenarios.append(
            Scenario(
                scenario_id=tags["scenario"],
                name=name,
                layer=tags["layer"],
                status=tags["status"],
                path=path,
                line=line_no,
            )
        )
    return scenarios


def _validate_contract_shape(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if contract.get("schema") != "zenodex.consensus_semantic_contract.v1":
        errors.append("schema must be zenodex.consensus_semantic_contract.v1")
    for key in ("claim_levels", "authority_order", "operations", "bdd"):
        if key not in contract:
            errors.append(f"missing top-level key {key!r}")
    claim_levels = contract.get("claim_levels")
    if isinstance(claim_levels, Mapping):
        for required in ("core_equivalent", "modeled_envelope_equivalent", "live_equivalent"):
            if required not in claim_levels:
                errors.append(f"claim_levels missing {required}")
    else:
        errors.append("claim_levels must be an object")
    return errors


def _validate_bdd(contract: Mapping[str, Any]) -> tuple[list[str], list[Scenario]]:
    errors: list[str] = []
    bdd = contract.get("bdd")
    if not isinstance(bdd, Mapping):
        return ["bdd must be an object"], []
    feature_files = bdd.get("feature_files")
    if not isinstance(feature_files, list) or not feature_files:
        return ["bdd.feature_files must be a non-empty list"], []
    scenarios: list[Scenario] = []
    for raw_path in feature_files:
        if not isinstance(raw_path, str):
            errors.append("bdd.feature_files entries must be strings")
            continue
        path = _repo_path(raw_path)
        if not path.is_file():
            errors.append(f"feature file missing: {raw_path}")
            continue
        try:
            scenarios.extend(parse_feature(path))
        except ValueError as exc:
            errors.append(str(exc))

    by_id: dict[str, Scenario] = {}
    for scenario in scenarios:
        if scenario.scenario_id in by_id:
            first = by_id[scenario.scenario_id]
            errors.append(
                f"duplicate scenario id {scenario.scenario_id}: "
                f"{first.path.relative_to(REPO)}:{first.line} and "
                f"{scenario.path.relative_to(REPO)}:{scenario.line}"
            )
        by_id[scenario.scenario_id] = scenario

    required = bdd.get("required_scenarios")
    if not isinstance(required, Mapping):
        errors.append("bdd.required_scenarios must be an object")
        return errors, scenarios
    for scenario_id, raw_meta in required.items():
        if not isinstance(raw_meta, Mapping):
            errors.append(f"required scenario {scenario_id} metadata must be an object")
            continue
        scenario = by_id.get(str(scenario_id))
        if scenario is None:
            errors.append(f"required scenario missing from feature files: {scenario_id}")
            continue
        expected_layer = raw_meta.get("layer")
        expected_status = raw_meta.get("status")
        if scenario.layer != expected_layer:
            errors.append(
                f"{scenario_id}: layer tag {scenario.layer!r} != contract {expected_layer!r}"
            )
        if scenario.status != expected_status:
            errors.append(
                f"{scenario_id}: status tag {scenario.status!r} != contract {expected_status!r}"
            )
    for scenario_id in by_id:
        if scenario_id not in required:
            errors.append(f"feature scenario not listed in contract: {scenario_id}")
    return errors, scenarios


def _validate_deposit_contract(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    operations = contract.get("operations")
    if not isinstance(operations, Mapping):
        return ["operations must be an object"]
    op = operations.get("perps_np.deposit_collateral")
    if not isinstance(op, Mapping):
        return ["operations missing perps_np.deposit_collateral"]
    core = op.get("core")
    envelope = op.get("envelope")
    guest = op.get("guest")
    if not isinstance(core, Mapping):
        errors.append("perps_np.deposit_collateral.core must be an object")
    else:
        expectations = {
            "zero_amount_behavior": "account_join_no_collateral_delta",
            "negative_amount_behavior": "reject_no_mutation",
            "nonce_layer": "tx_envelope",
            "core_nonce_effect": "unchanged",
        }
        for key, expected in expectations.items():
            if core.get(key) != expected:
                errors.append(f"deposit core {key} must be {expected!r}")
    if not isinstance(envelope, Mapping):
        errors.append("perps_np.deposit_collateral.envelope must be an object")
    else:
        if envelope.get("live_binding_status") != "open_obligation":
            errors.append("deposit envelope live_binding_status must remain open_obligation")
        if envelope.get("open_obligation_id") != "P0-3b":
            errors.append("deposit envelope open_obligation_id must be P0-3b")
    if not isinstance(guest, Mapping):
        errors.append("perps_np.deposit_collateral.guest must be an object")
    else:
        if guest.get("modeled_envelope_claim_level") != "modeled_envelope_equivalent":
            errors.append("guest modeled envelope claim must be modeled_envelope_equivalent")
        if guest.get("live_equivalence_claim_level") != "open_obligation":
            errors.append("guest live equivalence claim must remain open_obligation")
    return errors


def _validate_overclaim_guards(contract: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    guards = contract.get("overclaim_guards", [])
    if not isinstance(guards, list):
        return ["overclaim_guards must be a list"]
    for guard in guards:
        if not isinstance(guard, Mapping):
            errors.append("overclaim guard must be an object")
            continue
        raw_path = guard.get("path")
        if not isinstance(raw_path, str):
            errors.append("overclaim guard path must be a string")
            continue
        path = _repo_path(raw_path)
        if not path.is_file():
            errors.append(f"overclaim guard path missing: {raw_path}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in guard.get("forbidden_tokens", []):
            if not isinstance(token, str):
                errors.append(f"{raw_path}: forbidden token must be a string")
                continue
            if token in text:
                errors.append(f"{raw_path}: forbidden overclaim token present: {token!r}")
        for token in guard.get("required_tokens", []):
            if not isinstance(token, str):
                errors.append(f"{raw_path}: required token must be a string")
                continue
            if token not in text:
                errors.append(f"{raw_path}: required scoping token missing: {token!r}")
    return errors


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO))
    except ValueError:
        return str(path)


def validate(contract_path: Path = DEFAULT_CONTRACT) -> dict[str, Any]:
    contract = _load_json(contract_path)
    errors: list[str] = []
    errors.extend(_validate_contract_shape(contract))
    bdd_errors, scenarios = _validate_bdd(contract)
    errors.extend(bdd_errors)
    errors.extend(_validate_deposit_contract(contract))
    errors.extend(_validate_overclaim_guards(contract))
    return {
        "ok": not errors,
        "contract_path": _display_path(contract_path),
        "scenario_count": len(scenarios),
        "executable_scenarios": sum(1 for scenario in scenarios if scenario.status == "executable"),
        "open_obligations": [
            scenario.scenario_id for scenario in scenarios if scenario.status == "open_obligation"
        ],
        "errors": errors,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--json", action="store_true", help="emit JSON report")
    args = parser.parse_args(argv)
    report = validate(args.contract)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        if report["ok"]:
            print(
                f"ok: {report['scenario_count']} scenarios, "
                f"{report['executable_scenarios']} executable, "
                f"{len(report['open_obligations'])} open obligation(s)"
            )
        else:
            print("semantic contract check failed", file=sys.stderr)
            for error in report["errors"]:
                print(f"- {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
