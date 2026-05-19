#!/usr/bin/env python3
"""Completion audit for production key-management readiness criteria."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = "zenodex.production_key_management.completion_audit.v1"


CRITERIA: dict[str, dict[str, list[str]]] = {
    "property_checker_green": {
        "files": [
            "tools/check_production_key_management_spec.py",
            "tests/test_production_key_management_spec.py",
            "formal/property/production_key_management_v0.json",
        ],
        "release_gate_tokens": [
            "tools/check_production_key_management_spec.py",
            "tests/test_production_key_management_spec.py",
        ],
    },
    "ESSO_or_equivalent_finite_model_green": {
        "files": [
            "formal/esso/production_key_management_v0.esso.yaml",
            "tools/check_production_key_management_esso_equivalent.py",
            "tests/test_check_production_key_management_esso_equivalent.py",
        ],
        "release_gate_tokens": [
            "tools/check_production_key_management_esso_equivalent.py",
            "tests/test_check_production_key_management_esso_equivalent.py",
        ],
    },
    "Lean_receipt_green": {
        "files": [
            "lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean",
            "lean-mathlib/proof_receipts/zeno_ledger_production_key_management_v0.md",
        ],
        "traceability_tokens": [
            "lean-mathlib/Proofs/ZenoLedgerProductionKeyManagement.lean",
            "lean-mathlib/proof_receipts/zeno_ledger_production_key_management_v0.md",
        ],
    },
    "runtime_admission_library_green": {
        "files": [
            "src/integration/production_key_management_v0.py",
            "tests/integration/test_production_key_management_v0.py",
        ],
        "release_gate_tokens": [
            "src/integration/production_key_management_v0.py",
            "tests/integration/test_production_key_management_v0.py",
        ],
    },
    "privileged_action_gates_wired": {
        "files": [
            "src/integration/zeno_ledger_production_key_gates_v0.py",
            "tests/integration/test_zeno_ledger_production_key_gates_v0.py",
            "tools/check_production_key_management_bypasses.py",
        ],
        "release_gate_tokens": [
            "src/integration/zeno_ledger_production_key_gates_v0.py",
            "tests/integration/test_zeno_ledger_production_key_gates_v0.py",
            "tools/check_production_key_management_bypasses.py",
        ],
    },
    "release_gate_checks_key_management": {
        "files": [
            "tools/run_release_gate.sh",
            "tests/test_security_posture_files.py",
        ],
        "release_gate_tokens": [
            "tools/check_production_key_management_spec.py",
            "tools/check_production_key_management_bypasses.py",
            "tools/check_production_key_management_esso_equivalent.py",
            "tools/check_production_key_material_absence.py",
        ],
    },
    "operator_runbook_exists": {
        "files": [
            "docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md",
        ],
        "traceability_tokens": [
            "docs/PRODUCTION_KEY_MANAGEMENT_RUNBOOK.md",
        ],
    },
    "no_private_key_material_in_repo": {
        "files": [
            "tools/check_production_key_material_absence.py",
            "tests/test_check_production_key_material_absence.py",
        ],
        "release_gate_tokens": [
            "tools/check_production_key_material_absence.py",
            "tests/test_check_production_key_material_absence.py",
        ],
    },
}


def _read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _criterion_report(name: str, spec: dict[str, list[str]], *, release_gate: str, traceability: str) -> dict[str, Any]:
    errors: list[str] = []
    for path in spec.get("files", []):
        if not (ROOT / path).exists():
            errors.append(f"missing_file:{path}")
    for token in spec.get("release_gate_tokens", []):
        if token not in release_gate:
            errors.append(f"missing_release_gate_token:{token}")
    for token in spec.get("traceability_tokens", []):
        if token not in traceability:
            errors.append(f"missing_traceability_token:{token}")
    return {
        "criterion": name,
        "ok": not errors,
        "errors": errors,
        "files": spec.get("files", []),
    }


def run_check() -> dict[str, Any]:
    release_gate = _read("tools/run_release_gate.sh")
    traceability = _read("docs/production_traceability_matrix.json")
    criteria = [
        _criterion_report(name, spec, release_gate=release_gate, traceability=traceability)
        for name, spec in sorted(CRITERIA.items())
    ]
    errors = [
        f"{entry['criterion']}:{error}"
        for entry in criteria
        for error in entry["errors"]
    ]
    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "criteria": criteria,
        "errors": errors,
    }


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
