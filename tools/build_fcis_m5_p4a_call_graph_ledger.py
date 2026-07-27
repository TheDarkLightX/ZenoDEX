#!/usr/bin/env python3
"""Mounted authority/effect call-graph ledger for FCIS M5-P4A.

Produces a machine-readable JSON ledger mapping every final-mount authority
path to its violation profile, call-graph edges, and mount readiness status.
The ledger is source-derived from the authority snapshot checker output and
static import analysis of the mounted dispatch.

M5-P4A-CG-001: every final-mount authority path is enumerated.
M5-P4A-CG-002: every violation is classified by code and path.
M5-P4A-CG-003: call-graph edges are derived from static import analysis.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

from src.state.canonical import canonical_json_bytes

_REPO_ROOT = Path(__file__).resolve().parents[1]
_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CALL_GRAPH_LEDGER_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-call-graph-ledger/v1"

_FINAL_MOUNT_PATHS = [
    "src/core/dex.py",
    "src/core/settlement_strong_validator.py",
    "src/state/legacy_state_snapshots.py",
    "src/state/fcis_committed_state_admission.py",
    "src/state/fcis_committed_state_values.py",
    "src/core/fcis_step_evaluation_values.py",
    "src/core/fcis_step_evaluator.py",
    "src/core/fee_accumulator_transition.py",
    "src/core/nonce_batch_transition.py",
    "src/state/snapshot_combinators.py",
    "src/state/owned_collections.py",
    "src/state/perps_account_transitions.py",
    "src/state/perps_collateral_transitions.py",
    "src/state/perps_funding_transitions.py",
    "src/state/perps_liquidation_transitions.py",
    "src/state/perps_market_param_transitions.py",
    "src/state/perps_aggregate_transitions.py",
    "src/state/perps_settlement_transitions.py",
    "src/state/perps_state_transitions.py",
    "src/state/perps_transition_combinators.py",
    "src/state/lp_duration_transitions.py",
    "src/state/lp_duration_policy_values.py",
    "src/state/lp_duration_policy_schema.py",
    "src/state/lp_duration_policy_admission.py",
    "src/state/lp_duration_policy_context.py",
    "src/state/dex_snapshot_profile.py",
    "src/state/fcis_execution_context_values.py",
    "src/state/fcis_execution_context_schema.py",
    "src/state/fcis_execution_context_codec.py",
    "src/state/fcis_execution_context_admission.py",
    "src/state/fcis_execution_context.py",
    "src/state/pool_creation_transition.py",
    "src/state/state_snapshot_values.py",
    "src/state/state_snapshot_schema.py",
    "src/state/state_admission_profile.py",
    "src/state/state_snapshots.py",
    "src/state/state_transitions.py",
    "src/state/spot_state_transitions.py",
    "src/state/committed_spot_roots.py",
    "src/state/committed_dex_snapshot.py",
    "src/core/fcis_authority_admission.py",
    "src/core/fcis_authority_dispatch.py",
    "src/core/fcis_authority_schema.py",
    "src/core/fcis_commit_bundle_derivation.py",
    "src/core/fcis_commit_bundle_values.py",
    "src/core/fcis_commit_reference.py",
    "src/core/fcis_decision_values.py",
    "src/core/fcis_decision_derivation.py",
    "src/core/fcis_outbox_values.py",
    "src/core/fcis_transition_budget.py",
    "src/core/fcis_transition_values.py",
    "src/state/state_admission_profile.py",
    "src/state/state_snapshot_schema.py",
    "src/state/owned_json.py",
    "src/state/intent_field_registry.py",
    "src/state/intent_schema.py",
    "src/state/intent_snapshots.py",
    "src/core/settlement_schema.py",
    "src/core/settlement_snapshots.py",
    "src/core/route_settlement.py",
    "src/core/settlement_strong_validator.py",
    "src/core/fcis_step_evaluator.py",
    "src/core/fcis_commit_bundle_derivation.py",
    "src/core/fcis_commit_reference.py",
    "src/core/fcis_decision_derivation.py",
    "src/core/fcis_state_read_trace_v5.py",
    "src/core/fcis_support_profile_constants_v5.py",
    "src/core/fcis_support_profile_v5.py",
    "src/core/fcis_traced_reads_v5.py",
    "src/core/nonce_batch_transition.py",
    "src/state/support_root.py",
    "src/integration/fcis_spot_shadow.py",
]


def _run_authority_checker() -> dict[str, Any]:
    """Run the final-mount authority snapshot checker and return its JSON."""
    result = subprocess.run(
        [
            sys.executable,
            str(_REPO_ROOT / "tools" / "check_fcis_authority_snapshot_contract.py"),
            "--profile",
            "final-mount",
            "--json",
        ],
        cwd=_REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )
    return json.loads(result.stdout)


def _extract_imports(path: Path) -> list[str]:
    """Extract local import targets from a Python source file."""
    import ast

    try:
        tree = ast.parse(path.read_text())
    except SyntaxError:
        return []
    imports: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            if node.module is None:
                continue
            module = node.module
            if module.startswith("src.") or module.startswith("..") or module.startswith("."):
                imports.append(module)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.startswith("src."):
                    imports.append(alias.name)
    return imports


def _build_call_graph_edges() -> list[dict[str, Any]]:
    """Build call-graph edges from static import analysis."""
    edges: list[dict[str, Any]] = []
    seen_paths = set()
    for path_str in _FINAL_MOUNT_PATHS:
        path = _REPO_ROOT / path_str
        if not path.exists() or path_str in seen_paths:
            continue
        seen_paths.add(path_str)
        imports = _extract_imports(path)
        for imp in imports:
            normalized = imp.lstrip(".")
            if normalized.startswith("src."):
                target = normalized.replace(".", "/") + ".py"
            else:
                parts = normalized.split(".")
                if len(parts) >= 2:
                    target = "src/" + "/".join(parts) + ".py"
                else:
                    continue
            edges.append({
                "source": path_str,
                "target": target,
                "edge_type": "import",
            })
    return edges


def _build_path_ledger(
    violations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Build per-path ledger entries from violations."""
    by_path: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for v in violations:
        by_path[v["path"]].append(v)
    ledger: list[dict[str, Any]] = []
    for path_str in sorted(by_path):
        path_violations = by_path[path_str]
        codes = sorted(set(v["code"] for v in path_violations))
        full_path = _REPO_ROOT / path_str
        exists = full_path.exists()
        line_count = 0
        if exists:
            try:
                line_count = len(full_path.read_text().splitlines())
            except Exception:
                pass
        ledger.append({
            "path": path_str,
            "exists": exists,
            "line_count": line_count,
            "violation_count": len(path_violations),
            "violation_codes": codes,
            "violations": [
                {
                    "code": v["code"],
                    "line": v["line"],
                    "col": v.get("col"),
                    "detail": v.get("detail", ""),
                }
                for v in sorted(path_violations, key=lambda x: (x["line"], x.get("col", 0)))
            ],
        })
    return ledger


def _build_mount_readiness(
    violations: list[dict[str, Any]],
) -> dict[str, Any]:
    """Summarize mount readiness from the violation profile."""
    by_code: dict[str, int] = defaultdict(int)
    by_path: dict[str, int] = defaultdict(int)
    for v in violations:
        by_code[v["code"]] += 1
        by_path[v["path"]] += 1
    total = len(violations)
    return {
        "total_violations": total,
        "violations_by_code": dict(sorted(by_code.items())),
        "violations_by_path": dict(sorted(by_path.items())),
        "ready_for_mount": total == 0,
        "blocker_paths": sorted(
            path for path, count in by_path.items() if count > 0
        ),
    }


def _build_ledger() -> dict[str, Any]:
    checker_output = _run_authority_checker()
    violations = checker_output.get("violations", [])
    path_ledger = _build_path_ledger(violations)
    call_graph_edges = _build_call_graph_edges()
    mount_readiness = _build_mount_readiness(violations)
    ledger: dict[str, Any] = {
        "schema": _SCHEMA,
        "authority_checker_ok": checker_output.get("ok", False),
        "authority_profile": "final-mount",
        "mount_readiness": mount_readiness,
        "path_ledger": path_ledger,
        "call_graph_edges": call_graph_edges,
        "call_graph_edge_count": len(call_graph_edges),
        "authority_path_count": len(_FINAL_MOUNT_PATHS),
    }
    ledger_bytes = canonical_json_bytes(ledger)
    ledger["ledger_sha256"] = "0x" + hashlib.sha256(ledger_bytes).hexdigest()
    return ledger


def _write_ledger(ledger: dict[str, Any]) -> None:
    _REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _REPORT_PATH.write_bytes(canonical_json_bytes(ledger))


def main() -> int:
    check_mode = "--check" in sys.argv
    ledger = _build_ledger()
    if check_mode:
        if not _REPORT_PATH.exists():
            print("ERROR: call-graph ledger does not exist", file=sys.stderr)
            return 1
        existing = _REPORT_PATH.read_bytes()
        new_bytes = canonical_json_bytes(ledger)
        if existing != new_bytes:
            print("ERROR: call-graph ledger changed", file=sys.stderr)
            return 1
        print(f"OK: call-graph ledger matches (sha256={ledger['ledger_sha256']})")
        return 0
    _write_ledger(ledger)
    ready = ledger["mount_readiness"]["ready_for_mount"]
    total = ledger["mount_readiness"]["total_violations"]
    print(
        f"OK: wrote {_REPORT_PATH} "
        f"(ready_for_mount={ready}, violations={total})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
