#!/usr/bin/env python3
"""CBC matrix-closure gate — Phase 0 of the production promotion plan.

Computes the per-surface and scope-level production-security claim from a CBC
surface-evidence registry (see ``config/production/cbc_surface_evidence_v1.json``)
using the pure evaluator in :mod:`src.integration.surface_security_claim`, prints
the matrix, and FAILS CLOSED while the claim is not genuinely true. This is the
gate the release pipeline consults before any surface may claim production — the
claim is computed from evidence, never asserted.

Exit contract (the release pipeline depends on it):
  0  = every in-scope surface's CBC row is cleared (claim true)
  1  = a clean BLOCKED claim (some column unverified) — advisory
  2  = a STRUCTURAL / fail-closed error (bad registry, unknown production scope,
       malformed row, illegal --scope) — never a silent pass and never advisory

Production safety: by default the gate REQUIRES the registry's ``scope_id`` to be
a known, source-pinned production scope (``KNOWN_SCOPE_AUTHORITY_SETS``). Renaming
or omitting ``scope_id`` to dodge the source pin therefore fails closed rather
than silently evaluating an unpinned (shrinkable) scope. ``--allow-unpinned-scope``
relaxes this for dev/test registries only.

Clean CLI: human matrix to stderr, machine JSON to stdout (with ``--json``).
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
    KNOWN_SCOPE_AUTHORITY_SETS,
    claim_role_of,
    evaluate_scope_security_claim,
    is_evidence_only,
)


def _log(msg: str) -> None:
    print(msg, file=sys.stderr)


def _load_registry(
    path: Path, *, require_known_scope: bool
) -> tuple[list[str], dict[str, Any], list[str]]:
    """Return (claim_scope, all_surfaces, evidence_only_ids).

    The claim scope is every surface row EXCEPT those marked
    ``claim_role: evidence_only`` (proof-carriers not on the authority path).
    Evidence-only rows are retained and returned for display, but excluded from
    the production-claim AND so they can neither block nor inflate the claim.

    Raises ``ValueError`` on any structural / fail-closed condition (caller maps
    that to exit 2).
    """
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, Mapping):
        raise ValueError(f"{path}: top-level registry must be an object")
    surfaces = raw.get("surfaces")
    if not isinstance(surfaces, Mapping) or not surfaces:
        raise ValueError(f"{path}: 'surfaces' must be a non-empty object")
    surfaces = dict(surfaces)
    # Every surface row must be an object, and its claim_role must be known — a
    # malformed row or unknown/typo'd role fails closed (not silently authority).
    for sid, ev in surfaces.items():
        if not isinstance(ev, Mapping):
            raise ValueError(f"{path}: surface {sid!r} must be an object, got {type(ev).__name__}")
        claim_role_of(ev)
    evidence_only = [s for s, ev in surfaces.items() if is_evidence_only(ev)]
    scope = [s for s in surfaces if s not in evidence_only]
    if not scope:
        raise ValueError(f"{path}: no claim-scope surfaces (every row is evidence_only)")
    # An evidence-only row must attach to an authority surface that is itself in
    # scope — no dangling / orphaned proof-carriers (and no attaching to another
    # evidence-only row), so a retained row cannot be claim theater.
    for s in evidence_only:
        attached = surfaces[s].get("attached_to")
        if attached not in scope:
            raise ValueError(
                f"{path}: evidence_only surface {s!r} has attached_to={attached!r}, "
                f"which is not an authority surface in scope"
            )
    # The registry MUST declare its authority scope (a non-empty list of strings),
    # and the computed scope must match it exactly. Requiring it (rather than
    # inferring) is what stops a real authority surface from being silently dropped
    # by mismarking it evidence_only — with no declaration there is nothing to
    # mismatch.
    declared = raw.get("claim_scope")
    if not isinstance(declared, list) or not declared or not all(isinstance(x, str) for x in declared):
        raise ValueError(
            f"{path}: 'claim_scope' (the declared authority surfaces) is required and must "
            f"be a non-empty list of strings — refusing to infer it (a missing claim_scope "
            f"would let a real surface be silently dropped by mismarking it evidence_only)"
        )
    if set(declared) != set(scope):
        raise ValueError(
            f"{path}: declared claim_scope {sorted(declared)} != computed authority scope "
            f"{sorted(scope)} (a real authority surface may have been mismarked evidence_only)"
        )
    # Anchor against the SOURCE-CONTROLLED expected set, keyed by scope_id. Both
    # claim_scope and the claim_role markings live in this (mutable) registry, so a
    # coordinated edit could otherwise make declared==computed over a shrunk scope.
    # In production mode the scope_id MUST be a known, source-pinned scope —
    # renaming/omitting it to dodge the pin fails closed (no fail-open name-binding).
    scope_id = raw.get("scope_id")
    expected = KNOWN_SCOPE_AUTHORITY_SETS.get(scope_id) if isinstance(scope_id, str) else None
    if require_known_scope and expected is None:
        raise ValueError(
            f"{path}: production gate requires a known scope_id (one of "
            f"{sorted(KNOWN_SCOPE_AUTHORITY_SETS)}); got {scope_id!r}. Refusing to evaluate an "
            f"unpinned scope — renaming/omitting scope_id must not bypass the source pin. "
            f"(Pass --allow-unpinned-scope only for non-production/dev registries.)"
        )
    if expected is not None and set(scope) != expected:
        raise ValueError(
            f"{path}: scope_id {scope_id!r} authority scope {sorted(scope)} != the "
            f"source-pinned expected set {sorted(expected)} — a registry edit cannot "
            f"shrink or alter a known production scope (change SPOT_DEX_SCOPE in source instead)"
        )
    return scope, surfaces, evidence_only


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
    evidence_only = result.get("evidence_only_surfaces") or []
    if evidence_only:
        surfaces = result.get("_surfaces", {})
        _log("")
        _log("  evidence-only surfaces (retained for traceability, NOT part of the production claim):")
        for sid in evidence_only:
            attached = (surfaces.get(sid) or {}).get("attached_to")
            tail = f"  -> evidence for '{attached}'" if attached else ""
            _log(f"    - {sid}{tail}")


def run(
    evidence_path: Path,
    *,
    scope_override: Sequence[str] | None,
    as_json: bool,
    require_known_scope: bool = True,
) -> int:
    # Every structural / fail-closed condition (bad registry, unknown production
    # scope, malformed row, illegal override, evaluation error) is mapped to exit
    # 2 — never to exit 1 (which the release pipeline treats as advisory).
    try:
        scope, surfaces, evidence_only = _load_registry(
            evidence_path, require_known_scope=require_known_scope
        )
        if scope_override:
            override = list(scope_override)
            # An override may only NARROW the claim to a subset of the authority
            # scope; it must NEVER pull an evidence_only / unknown surface into the
            # claim AND (which would fabricate a passing claim).
            not_authority = [s for s in override if s not in scope]
            if not_authority:
                raise ValueError(
                    f"--scope {not_authority} not in the authority scope {sorted(scope)} "
                    f"(evidence_only or unknown surfaces cannot be claimed)"
                )
            scope = override
            # evidence_only stays the registry-declared set (display only).
        result = evaluate_scope_security_claim(scope, surfaces)
    except (OSError, ValueError, TypeError, KeyError, json.JSONDecodeError) as exc:
        _log(f"error: {exc}")
        return 2
    result["evidence_only_surfaces"] = sorted(evidence_only)
    if as_json:
        # Surface rows themselves are not part of the claim result; expose only
        # the evidence-only id list for machine consumers.
        print(json.dumps({k: v for k, v in result.items() if k != "_surfaces"}, sort_keys=True))
    else:
        result["_surfaces"] = surfaces
        _render_matrix(result)
    # Fail closed: the gate passes only when the scope claim is genuinely true.
    return 0 if result["production_security_claim"] else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="CBC matrix-closure gate (per-surface production claim).")
    parser.add_argument("--evidence", type=Path, default=DEFAULT_EVIDENCE, help="path to the CBC surface-evidence registry")
    parser.add_argument("--scope", nargs="*", default=None, help="narrow the claim to a subset of the authority scope (must be a subset; cannot add evidence_only/unknown surfaces)")
    parser.add_argument("--json", action="store_true", help="emit the machine-readable result to stdout")
    parser.add_argument(
        "--allow-unpinned-scope",
        action="store_true",
        help="allow a registry whose scope_id is not a known production scope (DEV/TEST ONLY; production requires a known, source-pinned scope_id)",
    )
    args = parser.parse_args(argv)
    return run(
        args.evidence,
        scope_override=args.scope,
        as_json=args.json,
        require_known_scope=not args.allow_unpinned_scope,
    )


if __name__ == "__main__":
    raise SystemExit(main())
