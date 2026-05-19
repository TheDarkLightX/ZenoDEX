#!/usr/bin/env python3
"""Validate the production key-management ESSO-equivalent finite model."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

import yaml

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_production_key_management_spec import run_check as run_property_check


DEFAULT_ESSO_MODEL = ROOT / "formal/esso/production_key_management_v0.esso.yaml"
DEFAULT_PROPERTY_MODEL = ROOT / "formal/property/production_key_management_v0.json"
RESULT_SCHEMA = "zenodex.production_key_management.esso_equivalent_check.v1"

EXPECTED_ESSO_INVARIANTS = {
    "PKM-ESSO-001-prod-keys-only",
    "PKM-ESSO-002-no-revoked-or-expired",
    "PKM-ESSO-003-role-authorized",
    "PKM-ESSO-004-quorum",
    "PKM-ESSO-005-distinct-custodians",
    "PKM-ESSO-006-storage",
    "PKM-ESSO-007-timelock",
    "PKM-ESSO-008-break-glass-scope",
    "PKM-ESSO-009-transparency",
    "PKM-ESSO-010-no-single-key-critical",
}


def _load_yaml(path: Path) -> Mapping[str, Any]:
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("ESSO model must be a mapping")
    return obj


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("property model must be a mapping")
    return obj


def _domain_values(model: Mapping[str, Any], name: str) -> list[str]:
    domains = model.get("finite_domains")
    if not isinstance(domains, Mapping):
        raise ValueError("ESSO finite_domains must be a mapping")
    domain = domains.get(name)
    if not isinstance(domain, Mapping):
        raise ValueError(f"ESSO domain missing:{name}")
    values = domain.get("values")
    if not isinstance(values, list) or not values:
        raise ValueError(f"ESSO domain {name} must have non-empty values")
    return [str(value) for value in values]


def _json_domain_values(model: Mapping[str, Any], name: str) -> list[str]:
    domains = model.get("domains")
    if not isinstance(domains, Mapping):
        raise ValueError("property domains must be a mapping")
    values = domains.get(name)
    if not isinstance(values, list) or not values:
        raise ValueError(f"property domain {name} must have non-empty values")
    return [str(value) for value in values]


def run_check(
    *,
    esso_model_path: Path = DEFAULT_ESSO_MODEL,
    property_model_path: Path = DEFAULT_PROPERTY_MODEL,
) -> dict[str, Any]:
    errors: list[str] = []
    esso = _load_yaml(esso_model_path)
    prop = _load_json(property_model_path)

    if esso.get("schema") != "esso.ir.v1":
        errors.append("ESSO schema mismatch")
    if esso.get("model_id") != prop.get("model_id"):
        errors.append("model_id mismatch")
    if esso.get("status") != "equivalent_finite_model_backed":
        errors.append("ESSO status must be equivalent_finite_model_backed")

    domain_pairs = {
        "environment": "environment",
        "key_status": "key_status",
        "storage_class": "storage_class",
        "role": "roles",
        "action": "actions",
    }
    for esso_name, json_name in domain_pairs.items():
        try:
            if sorted(_domain_values(esso, esso_name)) != sorted(_json_domain_values(prop, json_name)):
                errors.append(f"domain mismatch:{esso_name}:{json_name}")
        except Exception as exc:
            errors.append(str(exc))

    try:
        bounded_count = esso["finite_domains"]["bounded_count"]
        if int(bounded_count.get("min")) != 0 or int(bounded_count.get("max")) < 5:
            errors.append("bounded_count domain is too small")
    except Exception as exc:
        errors.append(f"bounded_count invalid:{exc}")

    invariants = esso.get("invariants")
    if not isinstance(invariants, list):
        errors.append("ESSO invariants must be a list")
        invariant_ids: set[str] = set()
    else:
        invariant_ids = {str(item.get("id")) for item in invariants if isinstance(item, Mapping)}
        missing = sorted(EXPECTED_ESSO_INVARIANTS - invariant_ids)
        extra = sorted(invariant_ids - EXPECTED_ESSO_INVARIANTS)
        if missing:
            errors.append(f"missing ESSO invariants:{','.join(missing)}")
        if extra:
            errors.append(f"unexpected ESSO invariants:{','.join(extra)}")

    recommended = esso.get("recommended_esso_commands")
    if not isinstance(recommended, Mapping):
        errors.append("recommended_esso_commands must be a mapping")
    else:
        for name in ("validate", "guide", "verify"):
            command = recommended.get(name)
            if not isinstance(command, str) or "production_key_management_v0.esso.yaml" not in command:
                errors.append(f"recommended ESSO command missing or stale:{name}")

    property_result = run_property_check(property_model_path)
    if property_result.get("ok") is not True:
        errors.append("property finite-model twin failed")

    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "esso_model_path": str(esso_model_path),
        "property_model_path": str(property_model_path),
        "property_case_count": int(property_result.get("case_count", 0)),
        "property_invariant_ids": property_result.get("invariant_ids", []),
        "esso_invariant_ids": sorted(invariant_ids),
        "equivalent_finite_model": bool(not errors),
        "external_esso_available": False,
        "external_esso_note": "ESSO is optional here; this check validates the ESSO-ready surface and executable finite-model twin.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--esso-model", type=Path, default=DEFAULT_ESSO_MODEL)
    parser.add_argument("--property-model", type=Path, default=DEFAULT_PROPERTY_MODEL)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args(argv)

    result = run_check(esso_model_path=args.esso_model, property_model_path=args.property_model)
    output = json.dumps(result, indent=2, sort_keys=True)
    print(output)
    if args.json_out is not None:
        args.json_out.write_text(output + "\n", encoding="utf-8")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
