#!/usr/bin/env python3
"""CBC matrix-closure gate — Phase 0 of the production promotion plan.

Computes the per-surface and scope-level production-security claim from a CBC
surface-evidence registry (see ``config/production/cbc_surface_evidence_v1.json``)
using the pure evaluator in :mod:`src.integration.surface_security_claim`, prints
the matrix, and FAILS CLOSED (exit 1) while any in-scope surface's CBC row is not
cleared. This is the gate the release pipeline consults before any surface may
claim production — the claim is computed from evidence, never asserted.

Clean CLI: human matrix to stderr, machine JSON to stdout (with ``--json``).
Exit 0 only when every in-scope surface's claim is true.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE = REPO_ROOT / "config" / "production" / "cbc_surface_evidence_v1.json"

sys.path.insert(0, str(REPO_ROOT))
from src.integration.surface_security_claim import (  # noqa: E402
    CBC_COLUMNS,
    evaluate_scope_security_claim,
)


def _log(msg: str) -> None:
    print(msg, file=sys.stderr)


def _load_registry(path: Path) -> tuple[list[str], dict[str, Any]]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    surfaces = raw.get("surfaces")
    if not isinstance(surfaces, Mapping) or not surfaces:
        raise ValueError(f"{path}: 'surfaces' must be a non-empty object")
    scope = list(surfaces.keys())
    return scope, dict(surfaces)


def _render_matrix(result: Mapping[str, Any]) -> None:
    _log("CBC matrix-closure gate")
    _log(f"  scope: {', '.join(result['scope'])}")
    _log(f"  production_security_claim: {result['production_security_claim']}  ({result['status']})")
    _log("")
    header = "  surface".ljust(16) + " | " + " ".join(c[:5].ljust(5) for c in CBC_COLUMNS)
    _log(header)
    _log("  " + "-" * (len(header) - 2))
    for surface_id in result["scope"]:
        res = result["per_surface"][surface_id]
        cols = res.get("columns", {})
        row = f"  {surface_id}".ljust(16) + " | " + " ".join(
            ("  ok " if cols.get(c) else "  .. ") for c in CBC_COLUMNS
        )
        _log(row)
    _log("")
    if result["gaps"]:
        _log(f"  {len(result['gaps'])} open gap(s):")
        for gap in result["gaps"]:
            _log(f"    - {gap}")


def run(evidence_path: Path, *, scope_override: Sequence[str] | None, as_json: bool) -> int:
    try:
        scope, surfaces = _load_registry(evidence_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        _log(f"error: {exc}")
        return 2
    if scope_override:
        scope = list(scope_override)
    result = evaluate_scope_security_claim(scope, surfaces)
    if as_json:
        print(json.dumps(result, sort_keys=True))
    else:
        _render_matrix(result)
    # Fail closed: the gate passes only when the scope claim is genuinely true.
    return 0 if result["production_security_claim"] else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="CBC matrix-closure gate (per-surface production claim).")
    parser.add_argument("--evidence", type=Path, default=DEFAULT_EVIDENCE, help="path to the CBC surface-evidence registry")
    parser.add_argument("--scope", nargs="*", default=None, help="override the surface scope (default: all surfaces in the registry)")
    parser.add_argument("--json", action="store_true", help="emit the machine-readable result to stdout")
    args = parser.parse_args(argv)
    return run(args.evidence, scope_override=args.scope, as_json=args.json)


if __name__ == "__main__":
    raise SystemExit(main())
