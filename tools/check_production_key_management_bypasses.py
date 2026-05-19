#!/usr/bin/env python3
"""Static guard for production key-management bypasses.

Production-sensitive ZenoLedger entrypoints should use the scoped gate helpers
in `src.integration.zeno_ledger_production_key_gates_v0`. Runtime files should
not call the raw production key-management receipt validator directly, because
that skips the operation-to-action mapping layer.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

WATCH_ROOTS = (ROOT / "src", ROOT / "tools")
RAW_VALIDATOR = "validate_production_key_admission_receipt_v0"
RAW_VALIDATOR_MODULE = "src.integration.production_key_management_v0"

ALLOWED_RAW_VALIDATOR_FILES = {
    "src/integration/production_key_management_v0.py",
    "src/integration/zeno_ledger_production_key_gates_v0.py",
}

REQUIRED_GATE_HELPERS = {
    "public_network_config_update": "validate_public_network_config_update_gate_v0",
    "validator_set_update": "validate_validator_set_update_gate_v0",
    "oracle_reporter_registry_update": "validate_oracle_reporter_registry_update_gate_v0",
    "verifier_registry_update": "validate_verifier_registry_update_gate_v0",
    "release_artifact_publish": "validate_release_artifact_publish_gate_v0",
    "emergency_pause": "validate_emergency_pause_gate_v0",
    "emergency_unpause": "validate_emergency_unpause_gate_v0",
}

REQUIRED_WIRING = {
    "public_network_config_update": {
        "path": "tools/zeno_ledger_node.py",
        "tokens": (
            "validate_public_network_config_update_gate_v0",
            "require_production_key_admission",
            "--require-production-key-admission",
        ),
    },
    "verifier_registry_update": {
        "path": "src/integration/zeno_ledger_verifier_registry_v0.py",
        "tokens": (
            "validate_verifier_registry_update_gate_v0",
            "require_production_key_admission",
            "production_key_admission_receipt",
        ),
    },
}


def _rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def _iter_python_files() -> list[Path]:
    files: list[Path] = []
    for root in WATCH_ROOTS:
        if not root.exists():
            continue
        files.extend(path for path in root.rglob("*.py") if "__pycache__" not in path.parts)
    return sorted(files)


def _import_module(node: ast.ImportFrom) -> str:
    dots = "." * int(node.level or 0)
    return dots + (node.module or "")


def _call_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _scan_python_file(path: Path) -> list[dict[str, object]]:
    rel = _rel(path)
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=rel)
    except SyntaxError as exc:
        return [{"path": rel, "line": exc.lineno or 0, "kind": "syntax_error", "detail": str(exc)}]

    issues: list[dict[str, object]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            imported = {alias.name for alias in node.names}
            if _import_module(node) == RAW_VALIDATOR_MODULE and RAW_VALIDATOR in imported:
                if rel not in ALLOWED_RAW_VALIDATOR_FILES:
                    issues.append(
                        {
                            "path": rel,
                            "line": int(getattr(node, "lineno", 0)),
                            "kind": "raw_validator_import",
                            "detail": RAW_VALIDATOR,
                        }
                    )
        elif isinstance(node, ast.Call):
            if _call_name(node.func) == RAW_VALIDATOR and rel not in ALLOWED_RAW_VALIDATOR_FILES:
                issues.append(
                    {
                        "path": rel,
                        "line": int(getattr(node, "lineno", 0)),
                        "kind": "raw_validator_call",
                        "detail": RAW_VALIDATOR,
                    }
                )
    return issues


def _check_gate_module() -> list[dict[str, object]]:
    path = ROOT / "src/integration/zeno_ledger_production_key_gates_v0.py"
    text = path.read_text(encoding="utf-8")
    issues: list[dict[str, object]] = []
    for operation, helper in REQUIRED_GATE_HELPERS.items():
        if f'"{operation}"' not in text:
            issues.append(
                {
                    "path": _rel(path),
                    "line": 0,
                    "kind": "missing_operation_mapping",
                    "detail": operation,
                }
            )
        if f"def {helper}" not in text:
            issues.append(
                {
                    "path": _rel(path),
                    "line": 0,
                    "kind": "missing_gate_helper",
                    "detail": helper,
                }
            )
    return issues


def _check_required_wiring() -> list[dict[str, object]]:
    issues: list[dict[str, object]] = []
    for operation, requirement in REQUIRED_WIRING.items():
        rel = str(requirement["path"])
        path = ROOT / rel
        text = path.read_text(encoding="utf-8")
        for token in requirement["tokens"]:
            if str(token) not in text:
                issues.append(
                    {
                        "path": rel,
                        "line": 0,
                        "kind": "missing_required_wiring_token",
                        "detail": f"{operation}:{token}",
                    }
                )
    return issues


def main() -> int:
    issues: list[dict[str, object]] = []
    for path in _iter_python_files():
        issues.extend(_scan_python_file(path))
    issues.extend(_check_gate_module())
    issues.extend(_check_required_wiring())

    payload = {
        "schema": "zenodex.production_key_management_bypass_check.v1",
        "ok": not issues,
        "checked_file_count": len(_iter_python_files()),
        "required_gate_helpers": REQUIRED_GATE_HELPERS,
        "required_wiring": {
            operation: {
                "path": str(requirement["path"]),
                "tokens": list(requirement["tokens"]),
            }
            for operation, requirement in REQUIRED_WIRING.items()
        },
        "issues": issues,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
