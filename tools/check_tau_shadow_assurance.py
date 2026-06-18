#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX_PATH = ROOT / "formal" / "tau" / "dex_safety_property_matrix.json"
DEFAULT_DELTA_QUEUE_PATH = ROOT / "formal" / "tau" / "semantic_delta_review_queue.json"
DEFAULT_CONTRACT_PATH = ROOT / "src" / "tau_specs" / "recommended" / "semantic_contracts.json"

MATRIX_SCHEMA = "zenodex/tau/safety-property-matrix/v1"
DELTA_QUEUE_SCHEMA = "zenodex/tau/semantic-delta-review-queue/v1"

REVIEW_CLEAR_STATUSES = {"intended"}
REVIEW_BLOCK_STATUSES = {"pending", "suspicious", "forbidden"}


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_path(root: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return root / path


def _json_bool_or_error(value: object, *, name: str, errors: list[str]) -> bool:
    if isinstance(value, bool):
        return value
    errors.append(f"{name}: expected bool")
    return False


def _load_contract_index(path: Path) -> dict[str, dict[str, Any]]:
    raw = _load_json(path)
    specs = raw.get("specs", [])
    if not isinstance(specs, list):
        raise ValueError(f"{path}: specs must be a list")
    out: dict[str, dict[str, Any]] = {}
    for spec in specs:
        if not isinstance(spec, dict):
            continue
        contract_id = str(spec.get("contract_id", "")).strip()
        if contract_id:
            out[contract_id] = spec
    return out


def _contains_definition(text: str, symbol: str) -> bool:
    marker = f"{symbol} =="
    return marker in text


def _validate_assurance_ref(
    *,
    root: Path,
    property_id: str,
    assurance_ref: Any,
    errors: list[str],
) -> bool:
    if not isinstance(assurance_ref, dict):
        errors.append(f"{property_id}: assurance_refs entries must be objects")
        return False

    kind = str(assurance_ref.get("kind", "")).strip()
    path_raw = str(assurance_ref.get("path", "")).strip()
    if not kind:
        errors.append(f"{property_id}: assurance_refs entry missing kind")
        return False
    if not path_raw:
        errors.append(f"{property_id}: assurance_refs entry missing path for kind {kind}")
        return False

    path = _resolve_path(root, path_raw)
    if not path.exists():
        errors.append(f"{property_id}: assurance ref path missing for kind {kind}: {path}")
        return False

    if kind == "tau_formal_contract":
        raw = _load_json(path)
        expected_spec_id = str(assurance_ref.get("expected_spec_id", "")).strip()
        if raw.get("schema") != "zenodex/tau/spec-contract/v1":
            errors.append(f"{property_id}: tau formal contract has wrong schema at {path}")
            return False
        if expected_spec_id and str(raw.get("spec_id", "")).strip() != expected_spec_id:
            errors.append(
                f"{property_id}: tau formal contract spec_id mismatch at {path}: expected {expected_spec_id!r}"
            )
            return False
        return True

    if kind == "tau_behavior_atlas":
        raw = _load_json(path)
        expected_spec_id = str(assurance_ref.get("expected_spec_id", "")).strip()
        if raw.get("schema") != "zenodex/tau/behavior-atlas/v1":
            errors.append(f"{property_id}: tau behavior atlas has wrong schema at {path}")
            return False
        if expected_spec_id and str(raw.get("spec_id", "")).strip() != expected_spec_id:
            errors.append(
                f"{property_id}: tau behavior atlas spec_id mismatch at {path}: expected {expected_spec_id!r}"
            )
            return False
        contract_ref = str(raw.get("contract_ref", "")).strip()
        if not contract_ref:
            errors.append(f"{property_id}: tau behavior atlas missing contract_ref at {path}")
            return False
        contract_path = _resolve_path(root, contract_ref)
        if not contract_path.is_file():
            errors.append(f"{property_id}: tau behavior atlas contract_ref missing: {contract_path}")
            return False
        return True

    if kind in {"pytest_target", "script_gate"}:
        if not path.is_file():
            errors.append(f"{property_id}: {kind} must point to a file: {path}")
            return False
        return True

    errors.append(f"{property_id}: unknown assurance ref kind {kind!r}")
    return False


def check_tau_shadow_assurance(
    *,
    root: Path = ROOT,
    matrix_path: Path = DEFAULT_MATRIX_PATH,
    delta_queue_path: Path = DEFAULT_DELTA_QUEUE_PATH,
    contract_path: Path = DEFAULT_CONTRACT_PATH,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []

    matrix_raw = _load_json(matrix_path)
    if matrix_raw.get("schema") != MATRIX_SCHEMA:
        errors.append(f"{matrix_path}: expected schema {MATRIX_SCHEMA}")
    properties = matrix_raw.get("properties", [])
    if not isinstance(properties, list) or not properties:
        errors.append(f"{matrix_path}: properties must be a non-empty list")
        properties = []

    queue_raw = _load_json(delta_queue_path)
    if queue_raw.get("schema") != DELTA_QUEUE_SCHEMA:
        errors.append(f"{delta_queue_path}: expected schema {DELTA_QUEUE_SCHEMA}")
    queue_entries = queue_raw.get("entries", [])
    if not isinstance(queue_entries, list):
        errors.append(f"{delta_queue_path}: entries must be a list")
        queue_entries = []

    contract_index = _load_contract_index(contract_path)

    seen_property_ids: set[str] = set()
    blocking_property_ids: set[str] = set()
    shadow_scaffolded_property_count = 0
    assurance_scaffolded_property_count = 0

    for index, entry in enumerate(properties):
        if not isinstance(entry, dict):
            errors.append(f"{matrix_path}: properties[{index}] must be an object")
            continue
        property_id = str(entry.get("property_id", "")).strip()
        if not property_id:
            errors.append(f"{matrix_path}: properties[{index}] missing property_id")
            continue
        if property_id in seen_property_ids:
            errors.append(f"{matrix_path}: duplicate property_id {property_id}")
            continue
        seen_property_ids.add(property_id)

        release_blocking = _json_bool_or_error(
            entry.get("release_blocking"),
            name=f"{matrix_path}: properties[{index}].release_blocking",
            errors=errors,
        )
        if release_blocking:
            blocking_property_ids.add(property_id)

        tau_contract_id = str(entry.get("tau_contract_id", "")).strip()
        tau_spec_path = str(entry.get("tau_spec_path", "")).strip()
        status = str(entry.get("status", "")).strip()

        if tau_contract_id:
            contract = contract_index.get(tau_contract_id)
            if contract is None:
                errors.append(f"{property_id}: unknown tau_contract_id {tau_contract_id}")
            else:
                contract_spec_path = str(contract.get("spec_path", "")).strip()
                if tau_spec_path != contract_spec_path:
                    errors.append(
                        f"{property_id}: tau_spec_path {tau_spec_path!r} does not match contract spec_path {contract_spec_path!r}"
                    )
        elif release_blocking:
            errors.append(f"{property_id}: release-blocking property requires tau_contract_id")

        shadow_model = entry.get("shadow_model")
        assurance_refs = entry.get("assurance_refs", [])
        if assurance_refs is None:
            assurance_refs = []
        if not isinstance(assurance_refs, list):
            errors.append(f"{property_id}: assurance_refs must be a list when present")
            assurance_refs = []
        assurance_ref_ok_count = 0
        for assurance_ref in assurance_refs:
            if _validate_assurance_ref(
                root=root,
                property_id=property_id,
                assurance_ref=assurance_ref,
                errors=errors,
            ):
                assurance_ref_ok_count += 1

        if shadow_model is None:
            if release_blocking:
                errors.append(f"{property_id}: release-blocking property requires shadow_model")
            elif status == "planned" and assurance_ref_ok_count == 0:
                warnings.append(f"{property_id}: planned only; no shadow model scaffold yet")
            if assurance_ref_ok_count > 0:
                assurance_scaffolded_property_count += 1
            continue

        if not isinstance(shadow_model, dict):
            errors.append(f"{property_id}: shadow_model must be an object")
            continue

        shadow_scaffolded_property_count += 1
        assurance_scaffolded_property_count += 1
        formalism = str(shadow_model.get("formalism", "")).strip()
        if formalism != "tla":
            errors.append(f"{property_id}: expected shadow_model.formalism == 'tla'")
        module_path_raw = str(shadow_model.get("module_path", "")).strip()
        config_path_raw = str(shadow_model.get("config_path", "")).strip()
        invariants = shadow_model.get("invariants", [])
        if not module_path_raw or not config_path_raw:
            errors.append(f"{property_id}: shadow_model requires module_path and config_path")
            continue
        if not isinstance(invariants, list) or not invariants:
            errors.append(f"{property_id}: shadow_model.invariants must be a non-empty list")
            continue

        module_path = _resolve_path(root, module_path_raw)
        config_path = _resolve_path(root, config_path_raw)
        if not module_path.is_file():
            errors.append(f"{property_id}: missing shadow module {module_path}")
            continue
        if not config_path.is_file():
            errors.append(f"{property_id}: missing shadow config {config_path}")
            continue

        module_text = module_path.read_text(encoding="utf-8")
        config_text = config_path.read_text(encoding="utf-8")
        if "SPECIFICATION Spec" not in config_text:
            errors.append(f"{property_id}: shadow config must contain 'SPECIFICATION Spec'")
        for invariant in invariants:
            if not isinstance(invariant, str) or not invariant.strip():
                errors.append(f"{property_id}: every shadow invariant must be a non-empty string")
                continue
            inv_name = invariant.strip()
            if not _contains_definition(module_text, inv_name):
                errors.append(f"{property_id}: shadow module missing invariant definition {inv_name}")
            if f"INVARIANT {inv_name}" not in config_text:
                errors.append(f"{property_id}: shadow config missing INVARIANT {inv_name}")

    seen_delta_ids: set[str] = set()
    blocking_deltas: list[str] = []
    for index, entry in enumerate(queue_entries):
        if not isinstance(entry, dict):
            errors.append(f"{delta_queue_path}: entries[{index}] must be an object")
            continue
        delta_id = str(entry.get("delta_id", "")).strip()
        if not delta_id:
            errors.append(f"{delta_queue_path}: entries[{index}] missing delta_id")
            continue
        if delta_id in seen_delta_ids:
            errors.append(f"{delta_queue_path}: duplicate delta_id {delta_id}")
            continue
        seen_delta_ids.add(delta_id)

        property_ids = entry.get("property_ids", [])
        if not isinstance(property_ids, list) or not property_ids:
            errors.append(f"{delta_id}: property_ids must be a non-empty list")
            continue
        unknown_ids = [pid for pid in property_ids if pid not in seen_property_ids]
        if unknown_ids:
            errors.append(f"{delta_id}: unknown property_ids {unknown_ids}")
            continue

        status = str(entry.get("status", "")).strip()
        if status in REVIEW_BLOCK_STATUSES:
            if any(pid in blocking_property_ids for pid in property_ids):
                blocking_deltas.append(delta_id)
        elif status not in REVIEW_CLEAR_STATUSES:
            errors.append(f"{delta_id}: unknown review status {status!r}")

    if blocking_deltas:
        errors.append(
            "release-blocking semantic deltas remain unresolved: " + ", ".join(sorted(blocking_deltas))
        )

    return {
        "schema": "zenodex/tau/shadow-assurance-check/v1",
        "matrix_path": str(matrix_path),
        "delta_queue_path": str(delta_queue_path),
        "contract_path": str(contract_path),
        "property_count": len(seen_property_ids),
        "release_blocking_property_count": len(blocking_property_ids),
        "shadow_scaffolded_property_count": shadow_scaffolded_property_count,
        "assurance_scaffolded_property_count": assurance_scaffolded_property_count,
        "pending_or_blocking_delta_count": len(blocking_deltas),
        "warnings": warnings,
        "errors": errors,
        "ok": not errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Fail-closed checker for Tau shadow-semantics scaffolding")
    parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX_PATH)
    parser.add_argument("--delta-queue", type=Path, default=DEFAULT_DELTA_QUEUE_PATH)
    parser.add_argument("--contracts", type=Path, default=DEFAULT_CONTRACT_PATH)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    args = parser.parse_args()

    result = check_tau_shadow_assurance(
        matrix_path=args.matrix,
        delta_queue_path=args.delta_queue,
        contract_path=args.contracts,
    )
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        for warning in result["warnings"]:
            print(f"warning: {warning}")
        for error in result["errors"]:
            print(f"error: {error}")
        print("ok" if result["ok"] else "failed")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
