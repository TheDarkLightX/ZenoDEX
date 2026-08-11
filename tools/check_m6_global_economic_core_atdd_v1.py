#!/usr/bin/env python3
"""Fail-closed structural checker for the M6 global economic ATDD/BDD contract.

This checker establishes source binding and catalogue closure.  It does not
prove the economic laws, runtime refinement, mounting, or production safety.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT = REPO_ROOT / "docs/research/m6_global_economic_core_atdd_bdd_v1.json"
SCHEMA = "zenodex/m6-global-economic-core-atdd-bdd/v1"
STATUS = "RESEARCH_ONLY_DRAFT"

ROOT_KEYS = {
    "schema",
    "status",
    "production_promotion",
    "base_commit",
    "source_pins",
    "authority_topology",
    "managed_asset_policy",
    "actors",
    "invariants",
    "workflows",
    "m6_coverage",
    "open_decisions",
    "nonclaims",
}
MANAGED_ASSET_KEYS = {
    "asset_class",
    "issue_authority",
    "burn_authority",
    "production_rule",
}
EXPECTED_MANAGED_ASSET_CLASSES = {
    "tau_native_coin",
    "canonical_zusd",
    "lp_share",
    "zdex_protocol_token",
    "sealed_bid_payment_or_inventory",
    "registered_ordinary_token",
}
AUTHORITY_KEYS = {
    "semantic_authority",
    "durable_authority",
    "specification_and_verification",
    "sqlite_role",
    "required_relation",
}
EXPECTED_ACTORS = {
    "trader",
    "liquidity_provider",
    "borrower",
    "stability_provider",
    "liquidator",
    "perp_trader",
    "proof_miner",
    "oracle_reporter",
    "sealed_bidder",
    "governance_operator",
    "recovery_operator",
    "outbox_worker",
    "adversary",
}
EXPECTED_INVARIANTS = {f"INV-{index:03d}" for index in range(1, 15)}
EXPECTED_WORKFLOWS = {f"WF-{index:02d}" for index in range(1, 19)}
EXPECTED_SCENARIOS = {f"BDD-{index:03d}" for index in range(1, 82)}
EXPECTED_M6_REQUIREMENTS = {f"M6-R{index:02d}" for index in range(1, 14)}
REQUIRED_SOURCE_PIN_PATHS = frozenset(
    {
        "docs/research/M6_RESEARCH_PROGRAM_20260730.md",
        "src/integration/tau_testnet_dex_plugin.py",
        "src/core/zusd.py",
        "src/core/zusd_generic_token_admission.py",
        "src/integration/zusd_monetary_bridge.py",
        "src/kernels/dex/zusd_generic_token_admission_v1.yaml",
        "src/kernels/dex/zusd_fee_liability_binding_coverage_v1.yaml",
        "src/kernels/dex/m6_global_economic_commit_v1.yaml",
        "src/integration/confidential_sealed_bid_api.py",
        "src/core/sealed_bid_auction.py",
        "src/core/sealed_bid_bonds.py",
        "src/core/m6_safe_mount_types_v1.py",
        "src/core/m6_safe_mount_transition_v1.py",
        "src/core/m6_authority_evidence_v1.py",
        "src/core/m6_zrpf_v1.py",
        "src/integration/m6_commit_port_v1.py",
        "src/integration/global_economic_commit_v1.py",
        "src/integration/m6_durable_store_v1.py",
        "tests/core/test_m6_safe_mount_v1.py",
        "tests/core/test_global_settlement_abi_v1.py",
        "tests/integration/test_m6_durable_store_v1.py",
        "tools/check_m6_global_economic_core_atdd_v1.py",
        "tools/check_m6_global_economic_core_luna_review_v1.py",
        "src/core/m6_migration_lifecycle_v1.py",
        "src/core/m6_safe_mount_v1.py",
        "src/integration/m6_authority_verifier_v1.py",
        "src/integration/m6_external_proof_backend_v1.py",
        "src/integration/m6_migration_admission_v1.py",
        "src/integration/m6_migration_authority_v1.py",
        "src/integration/m6_outbox_delivery_v1.py",
        "tools/check_m6_writer_inventory.py",
        "tools/m6_writer_inventory_manifest_v1.json",
        "tests/core/test_m6_migration_lifecycle_v1.py",
        "tests/integration/test_m6_authority_verifier_v1.py",
        "tests/integration/test_m6_migration_admission_v1.py",
        "tests/integration/test_m6_outbox_delivery_v1.py",
        "tests/kernels/test_m6_global_economic_commit_v1.py",
        "zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs",
    }
)

REJECTION_PARTITION_NAME = "rejection_partition"
REJECTION_PARTITION_MARKERS = (
    "admission or publication rejection",
    "authenticated, well-formed command",
    "committed failure candidate",
    "economic atoms",
    "outbox rows unchanged",
)

PIN_KEYS = {"path", "sha256"}
INVARIANT_KEYS = {"id", "name", "law"}
WORKFLOW_KEYS = {
    "id",
    "name",
    "actor",
    "owner",
    "entrypoints",
    "required_scenario_classes",
    "scenarios",
}
SCENARIO_KEYS = {"id", "class", "given", "when", "then", "requirements"}
LOWER_HEX_64 = re.compile(r"[0-9a-f]{64}\Z")
MIN_SCENARIO_TEXT_LENGTH = 8
VACUOUS_SCENARIO_TEXT = frozenset({"x", "ok", "todo", "n/a"})


class ContractError(ValueError):
    """Raised when the contract cannot be decoded without ambiguity."""


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ContractError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_contract(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ContractError) as exc:
        raise ContractError(f"contract decode failed: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ContractError("contract root must be an object")
    return value


def _exact_keys(value: Any, expected: set[str], label: str, errors: list[str]) -> bool:
    if not isinstance(value, Mapping):
        errors.append(f"{label} must be an object")
        return False
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        surplus = sorted(actual - expected)
        errors.append(f"{label} keys differ: missing={missing}, surplus={surplus}")
        return False
    return True


def _nonempty_string(value: Any, label: str, errors: list[str]) -> bool:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{label} must be a nonempty string")
        return False
    return True


def _scenario_text(value: Any, label: str, errors: list[str]) -> bool:
    """Require a readable scenario clause rather than a catalogue placeholder."""

    if not _nonempty_string(value, label, errors):
        return False
    if not isinstance(value, str):
        return False
    normalized = " ".join(value.split()).lower()
    if normalized in VACUOUS_SCENARIO_TEXT or len(normalized) < MIN_SCENARIO_TEXT_LENGTH:
        errors.append(
            f"{label} is vacuous; provide an executable Given/When/Then clause"
        )
        return False
    if " " not in normalized:
        errors.append(f"{label} must contain a multi-word acceptance clause")
        return False
    return True


def _closed_string_list(value: Any, label: str, errors: list[str]) -> list[str] | None:
    if not isinstance(value, list):
        errors.append(f"{label} must be a list")
        return None
    if any(not isinstance(item, str) or not item.strip() for item in value):
        errors.append(f"{label} must contain only nonempty strings")
        return None
    if len(value) != len(set(value)):
        errors.append(f"{label} must not contain duplicates")
        return None
    return value


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _validate_source_pins(
    value: Any,
    repo_root: Path,
    errors: list[str],
    *,
    require_exact_source_set: bool = False,
) -> int:
    if not isinstance(value, list) or not value:
        errors.append("source_pins must be a nonempty list")
        return 0
    paths: list[str] = []
    for index, pin in enumerate(value):
        label = f"source_pins[{index}]"
        if not _exact_keys(pin, PIN_KEYS, label, errors):
            continue
        raw_path = pin["path"]
        expected = pin["sha256"]
        if not _nonempty_string(raw_path, f"{label}.path", errors):
            continue
        if Path(raw_path).is_absolute() or ".." in Path(raw_path).parts:
            errors.append(f"{label}.path must be repository-relative without '..'")
            continue
        if not isinstance(expected, str) or LOWER_HEX_64.fullmatch(expected) is None:
            errors.append(f"{label}.sha256 must be 64 lowercase hexadecimal characters")
            continue
        paths.append(raw_path)
        source = repo_root / raw_path
        if not source.is_file():
            errors.append(f"{label}.path does not exist: {raw_path}")
            continue
        actual = _sha256(source)
        if actual != expected:
            errors.append(
                f"{label}.sha256 mismatch for {raw_path}: expected={expected}, actual={actual}"
            )
    if len(paths) != len(set(paths)):
        errors.append("source_pins paths must be unique")
    if require_exact_source_set and set(paths) != REQUIRED_SOURCE_PIN_PATHS:
        errors.append("source_pins paths must equal the mandatory M6 source set")
    return len(paths)


def _validate_base_commit(value: Any, repo_root: Path, errors: list[str]) -> None:
    """Bind the contract revision to the repository head being inspected."""

    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        errors.append("base_commit must be 40 lowercase hexadecimal characters")
        return
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--verify", "HEAD"],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        errors.append(f"base_commit repository lookup failed: {exc}")
        return
    actual = result.stdout.strip()
    if result.returncode != 0 or re.fullmatch(r"[0-9a-f]{40}", actual) is None:
        errors.append("base_commit repository lookup did not return an exact HEAD")
    elif value != actual:
        errors.append(f"base_commit must equal current repository HEAD: expected={value}, actual={actual}")


def _repo_relative(path: Path, repo_root: Path, label: str, errors: list[str]) -> str | None:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        errors.append(f"{label} must be inside the inspected repository")
        return None


def _validate_tracked_clean_provenance(
    source_pins: Any,
    base_commit: Any,
    repo_root: Path,
    contract_path: Path | None,
    errors: list[str],
) -> None:
    """Require a promotion candidate to be reproducible from its base commit."""

    if not isinstance(base_commit, str) or re.fullmatch(r"[0-9a-f]{40}", base_commit) is None:
        return
    paths: list[str] = []
    if isinstance(source_pins, list):
        for pin in source_pins:
            if isinstance(pin, Mapping) and isinstance(pin.get("path"), str):
                relative = pin["path"]
                if relative not in paths:
                    paths.append(relative)
    if contract_path is not None:
        relative_contract = _repo_relative(contract_path, repo_root, "contract path", errors)
        if relative_contract is not None and relative_contract not in paths:
            paths.append(relative_contract)
    if not paths:
        errors.append("tracked source provenance requires at least one repository-relative path")
        return
    try:
        tracked_result = subprocess.run(
            ["git", "ls-files", "--", *paths],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        errors.append(f"tracked source provenance lookup failed: {exc}")
        return
    if tracked_result.returncode != 0:
        errors.append("tracked source provenance lookup failed")
        return
    tracked = {line for line in tracked_result.stdout.splitlines() if line}
    missing = sorted(set(paths) - tracked)
    if missing:
        errors.append(f"tracked source provenance has untracked paths: {missing}")
    try:
        changed_result = subprocess.run(
            ["git", "diff", "--name-only", base_commit, "--", *paths],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        errors.append(f"tracked source provenance diff failed: {exc}")
        return
    if changed_result.returncode != 0:
        errors.append("tracked source provenance diff failed")
        return
    changed = sorted({line for line in changed_result.stdout.splitlines() if line})
    if changed:
        errors.append(f"tracked source provenance differs from base commit: {changed}")


def _validate_invariants(value: Any, errors: list[str]) -> set[str]:
    if not isinstance(value, list):
        errors.append("invariants must be a list")
        return set()
    identifiers: list[str] = []
    names: list[str] = []
    for index, invariant in enumerate(value):
        label = f"invariants[{index}]"
        if not _exact_keys(invariant, INVARIANT_KEYS, label, errors):
            continue
        identifier = invariant["id"]
        name = invariant["name"]
        if _nonempty_string(identifier, f"{label}.id", errors):
            identifiers.append(identifier)
        if _nonempty_string(name, f"{label}.name", errors):
            names.append(name)
        law = invariant["law"]
        _nonempty_string(law, f"{label}.law", errors)
        if identifier == "INV-005":
            if name != REJECTION_PARTITION_NAME:
                errors.append(
                    f"{label}.name must equal {REJECTION_PARTITION_NAME!r}"
                )
            if isinstance(law, str):
                lowered_law = law.lower()
                missing_markers = [
                    marker
                    for marker in REJECTION_PARTITION_MARKERS
                    if marker not in lowered_law
                ]
                if missing_markers:
                    errors.append(
                        f"{label}.law must declare both rejection partitions; "
                        f"missing markers={missing_markers}"
                    )
    if set(identifiers) != EXPECTED_INVARIANTS or len(identifiers) != len(set(identifiers)):
        errors.append("invariant IDs must be exactly INV-001 through INV-014 with no duplicates")
    if len(names) != len(set(names)):
        errors.append("invariant names must be unique")
    return set(identifiers)


def _validate_managed_asset_policy(value: Any, errors: list[str]) -> None:
    if not isinstance(value, list):
        errors.append("managed_asset_policy must be a list")
        return
    classes: list[str] = []
    for index, policy in enumerate(value):
        label = f"managed_asset_policy[{index}]"
        if not _exact_keys(policy, MANAGED_ASSET_KEYS, label, errors):
            continue
        asset_class = policy["asset_class"]
        if _nonempty_string(asset_class, f"{label}.asset_class", errors):
            classes.append(asset_class)
        for field in ("issue_authority", "burn_authority", "production_rule"):
            _nonempty_string(policy[field], f"{label}.{field}", errors)
    if set(classes) != EXPECTED_MANAGED_ASSET_CLASSES or len(classes) != len(set(classes)):
        errors.append("managed_asset_policy must equal the closed expected asset-class set")


def _validate_workflows(
    value: Any,
    actors: set[str],
    invariant_ids: set[str],
    errors: list[str],
) -> tuple[set[str], set[str]]:
    if not isinstance(value, list):
        errors.append("workflows must be a list")
        return set(), set()
    workflow_ids: list[str] = []
    scenario_ids: list[str] = []
    workflow_names: list[str] = []
    for index, workflow in enumerate(value):
        label = f"workflows[{index}]"
        if not _exact_keys(workflow, WORKFLOW_KEYS, label, errors):
            continue
        workflow_id = workflow["id"]
        if _nonempty_string(workflow_id, f"{label}.id", errors):
            workflow_ids.append(workflow_id)
        name = workflow["name"]
        if _nonempty_string(name, f"{label}.name", errors):
            workflow_names.append(name)
        actor = workflow["actor"]
        if actor not in actors:
            errors.append(f"{label}.actor is not declared: {actor!r}")
        _nonempty_string(workflow["owner"], f"{label}.owner", errors)
        entrypoints = _closed_string_list(workflow["entrypoints"], f"{label}.entrypoints", errors)
        if entrypoints == []:
            errors.append(f"{label}.entrypoints must be nonempty")
        required_classes = _closed_string_list(
            workflow["required_scenario_classes"],
            f"{label}.required_scenario_classes",
            errors,
        )
        if required_classes == []:
            errors.append(f"{label}.required_scenario_classes must be nonempty")
        scenarios = workflow["scenarios"]
        if not isinstance(scenarios, list) or not scenarios:
            errors.append(f"{label}.scenarios must be a nonempty list")
            continue
        actual_classes: list[str] = []
        for scenario_index, scenario in enumerate(scenarios):
            scenario_label = f"{label}.scenarios[{scenario_index}]"
            if not _exact_keys(scenario, SCENARIO_KEYS, scenario_label, errors):
                continue
            scenario_id = scenario["id"]
            if _nonempty_string(scenario_id, f"{scenario_label}.id", errors):
                scenario_ids.append(scenario_id)
            scenario_class = scenario["class"]
            if _nonempty_string(scenario_class, f"{scenario_label}.class", errors):
                actual_classes.append(scenario_class)
            for field in ("given", "when", "then"):
                _scenario_text(scenario[field], f"{scenario_label}.{field}", errors)
            requirements = _closed_string_list(
                scenario["requirements"], f"{scenario_label}.requirements", errors
            )
            if requirements == []:
                errors.append(f"{scenario_label}.requirements must be nonempty")
            elif requirements is not None:
                unknown = sorted(set(requirements) - invariant_ids)
                if unknown:
                    errors.append(f"{scenario_label}.requirements contains unknown IDs: {unknown}")
        if required_classes is not None and set(actual_classes) != set(required_classes):
            errors.append(
                f"{label} scenario classes differ: "
                f"required={sorted(required_classes)}, actual={sorted(set(actual_classes))}"
            )
    if set(workflow_ids) != EXPECTED_WORKFLOWS or len(workflow_ids) != len(set(workflow_ids)):
        errors.append("workflow IDs must be exactly WF-01 through WF-18 with no duplicates")
    if set(scenario_ids) != EXPECTED_SCENARIOS or len(scenario_ids) != len(set(scenario_ids)):
        errors.append("scenario IDs must be exactly BDD-001 through BDD-081 with no duplicates")
    if len(workflow_names) != len(set(workflow_names)):
        errors.append("workflow names must be unique")
    return set(workflow_ids), set(scenario_ids)


def _validate_m6_coverage(value: Any, workflow_ids: set[str], errors: list[str]) -> None:
    if not isinstance(value, Mapping):
        errors.append("m6_coverage must be an object")
        return
    if set(value) != EXPECTED_M6_REQUIREMENTS:
        errors.append("m6_coverage keys must be exactly M6-R01 through M6-R13")
    for requirement, workflows in value.items():
        closed = _closed_string_list(workflows, f"m6_coverage.{requirement}", errors)
        if closed == []:
            errors.append(f"m6_coverage.{requirement} must be nonempty")
        elif closed is not None:
            unknown = sorted(set(closed) - workflow_ids)
            if unknown:
                errors.append(f"m6_coverage.{requirement} contains unknown workflows: {unknown}")


def validate_contract(
    contract: Mapping[str, Any],
    repo_root: Path = REPO_ROOT,
    *,
    contract_path: Path | None = None,
    require_tracked_clean: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    if not _exact_keys(contract, ROOT_KEYS, "contract", errors):
        return _report(contract, 0, set(), set(), errors)

    if contract["schema"] != SCHEMA:
        errors.append(f"schema must equal {SCHEMA!r}")
    if contract["status"] != STATUS:
        errors.append(f"status must equal {STATUS!r}")
    if contract["production_promotion"] is not False:
        errors.append("production_promotion must be the JSON boolean false")
    _validate_base_commit(contract["base_commit"], repo_root, errors)

    pin_count = _validate_source_pins(
        contract["source_pins"],
        repo_root,
        errors,
        require_exact_source_set=True,
    )
    if require_tracked_clean:
        _validate_tracked_clean_provenance(
            contract["source_pins"],
            contract["base_commit"],
            repo_root,
            contract_path,
            errors,
        )

    topology = contract["authority_topology"]
    if _exact_keys(topology, AUTHORITY_KEYS, "authority_topology", errors):
        for key in sorted(AUTHORITY_KEYS):
            _nonempty_string(topology[key], f"authority_topology.{key}", errors)
        sqlite_role = topology["sqlite_role"]
        if isinstance(sqlite_role, str) and not {
            "unmounted",
            "reference",
        }.issubset(sqlite_role.lower().split()):
            errors.append(
                "authority_topology.sqlite_role must explicitly say 'unmounted reference'"
            )

    actor_list = _closed_string_list(contract["actors"], "actors", errors)
    actors = set(actor_list or [])
    if actors != EXPECTED_ACTORS:
        errors.append("actors do not equal the closed expected actor set")

    _validate_managed_asset_policy(contract["managed_asset_policy"], errors)

    invariant_ids = _validate_invariants(contract["invariants"], errors)
    workflow_ids, scenario_ids = _validate_workflows(
        contract["workflows"], actors, invariant_ids, errors
    )
    _validate_m6_coverage(contract["m6_coverage"], workflow_ids, errors)

    open_decisions = _closed_string_list(contract["open_decisions"], "open_decisions", errors)
    nonclaims = _closed_string_list(contract["nonclaims"], "nonclaims", errors)
    if open_decisions == []:
        errors.append("open_decisions must be nonempty")
    if nonclaims == []:
        errors.append("nonclaims must be nonempty")

    shutdown = next(
        (
            workflow
            for workflow in contract["workflows"]
            if isinstance(workflow, Mapping) and workflow.get("id") == "WF-16"
        ),
        None,
    )
    if not isinstance(shutdown, Mapping) or "unmounted" not in str(shutdown.get("owner", "")):
        errors.append("WF-16 shutdown must remain explicitly unmounted")

    return _report(contract, pin_count, workflow_ids, scenario_ids, errors)


def _report(
    contract: Mapping[str, Any],
    pin_count: int,
    workflow_ids: Iterable[str],
    scenario_ids: Iterable[str],
    errors: Sequence[str],
) -> dict[str, Any]:
    return {
        "schema": "zenodex/m6-global-economic-core-atdd-bdd-check/v1",
        "ok": not errors,
        "contract_schema": contract.get("schema"),
        "contract_status": contract.get("status"),
        "production_promotion": contract.get("production_promotion"),
        "source_pin_count": pin_count,
        "workflow_count": len(set(workflow_ids)),
        "scenario_count": len(set(scenario_ids)),
        "errors": list(errors),
        "nonclaim": "structural closure and source binding do not prove economic laws or runtime safety",
    }


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--require-tracked-clean",
        action="store_true",
        help="reject source pins or the contract that are untracked or differ from base_commit",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        contract = load_contract(args.contract)
        report = validate_contract(
            contract,
            args.repo_root.resolve(),
            contract_path=args.contract.resolve(),
            require_tracked_clean=args.require_tracked_clean,
        )
    except ContractError as exc:
        report = {
            "schema": "zenodex/m6-global-economic-core-atdd-bdd-check/v1",
            "ok": False,
            "errors": [str(exc)],
            "nonclaim": "no contract was accepted",
        }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
