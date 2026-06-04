"""Per-surface, *computed* production-security claim — Phase 0 of the production
promotion plan (see ``docs/PRODUCTION_PROMOTION_PLAN.md``).

The production-security claim is COMPUTED from a structured CBC evidence object,
never asserted. A surface's claim is true only when all seven CBC columns are
cleared; the scope-level ``production_security_claim`` is the AND over a declared
set of surfaces. This mirrors the gap-list pattern of
:mod:`src.integration.production_promotion_evidence` (``claim = not gaps``):
missing or unverified evidence becomes a gap, and any gap fails the claim closed.

This module is intentionally *additive*: it establishes the mechanism and is pure
(no I/O, no global state). Wiring it into the release gate and converting the
existing ``production_security_claim``-rejecting validators to consult it are
later, separately-reviewed Phase 0/5 steps — this module does NOT change any
existing authority-path behavior on its own.

Design (CBC core style):
- pure function, explicit inputs/outputs, fail-closed;
- domain-typed evidence (mapping with a ``ref`` + ``verified`` flag per column);
- deterministic gap ordering (the fixed ``CBC_COLUMNS`` order).
"""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Sequence

# The seven CBC matrix columns a surface's row must clear (fixed order — gaps are
# reported deterministically in this order).
CBC_COLUMNS: tuple[str, ...] = (
    "running_impl",
    "formal_spec",
    "proof_artifact",
    "differential_tests",
    "runtime_invariants",
    "authority_mode",
    "open_gaps_closed",
)

# ``open_gaps_closed`` is a closure gate (a boolean), not an evidence reference.
_GATE_COLUMNS: frozenset[str] = frozenset({"open_gaps_closed"})

# The recommended first production-claim scope: the spot-DEX testnet scope. These
# are the consensus surfaces with the most existing proof coverage, used to prove
# the per-surface machinery end-to-end before widening to perps / zUSD / lanes.
SPOT_DEX_SCOPE: tuple[str, ...] = (
    "cpmm_swap",
    "balances",
    "state_root",
    "nonces",
    "replay_guard",
)


def _column_cleared(column: str, value: Any) -> bool:
    """A column is cleared iff its evidence is present AND verified.

    - gate columns (``open_gaps_closed``) clear only on the literal ``True``;
    - evidence columns clear only when given a mapping carrying a non-empty
      ``ref`` (path / artifact id) AND ``verified`` set to the literal ``True``.

    Anything else (absent, wrong type, falsy, ``verified`` not exactly ``True``)
    fails closed.
    """
    if column in _GATE_COLUMNS:
        return value is True
    if not isinstance(value, Mapping):
        return False
    ref = value.get("ref")
    if not isinstance(ref, str) or not ref.strip():
        return False
    return value.get("verified") is True


def evaluate_surface_security_claim(
    surface_id: str, evidence: Mapping[str, Any]
) -> Dict[str, Any]:
    """Compute a single surface's security claim from its CBC evidence object.

    Returns a result dict with the computed ``surface_security_claim`` (true only
    when every CBC column is cleared), the per-column boolean map, and the ordered
    list of gaps. Never raises on incomplete evidence — it reports gaps and fails
    the claim closed; it raises only on structurally invalid *inputs*.
    """
    if not isinstance(surface_id, str) or not surface_id.strip():
        raise ValueError("surface_id must be a non-empty str")
    if not isinstance(evidence, Mapping):
        raise ValueError("evidence must be a mapping")

    columns: Dict[str, bool] = {}
    gaps: List[str] = []
    for column in CBC_COLUMNS:
        cleared = _column_cleared(column, evidence.get(column))
        columns[column] = cleared
        if not cleared:
            gaps.append(f"{surface_id}: CBC column '{column}' not cleared")

    claim = not gaps
    return {
        "surface_id": surface_id,
        "surface_security_claim": claim,
        "status": "ready" if claim else "blocked",
        "columns": columns,
        "gaps": gaps,
    }


def evaluate_scope_security_claim(
    scope: Sequence[str], evidence_by_surface: Mapping[str, Mapping[str, Any]]
) -> Dict[str, Any]:
    """Compute the scope-level ``production_security_claim`` as the AND over the
    per-surface claims of every surface declared in ``scope``.

    A surface in scope with no evidence object is a gap (fail-closed) — the scope
    claim is true only when *every* in-scope surface's claim is true. Per-surface
    results are returned for inspection. Gaps are deterministically ordered by the
    scope order, then by CBC column order within each surface.
    """
    if not isinstance(scope, (list, tuple)) or not scope:
        raise ValueError("scope must be a non-empty sequence of surface ids")
    if not isinstance(evidence_by_surface, Mapping):
        raise ValueError("evidence_by_surface must be a mapping")

    per_surface: Dict[str, Any] = {}
    gaps: List[str] = []
    for surface_id in scope:
        evidence = evidence_by_surface.get(surface_id)
        if evidence is None:
            blocked = {
                "surface_id": surface_id,
                "surface_security_claim": False,
                "status": "blocked",
                "columns": {column: False for column in CBC_COLUMNS},
                "gaps": [f"{surface_id}: no evidence object provided"],
            }
            per_surface[surface_id] = blocked
            gaps.extend(blocked["gaps"])
            continue
        result = evaluate_surface_security_claim(surface_id, evidence)
        per_surface[surface_id] = result
        gaps.extend(result["gaps"])

    claim = not gaps
    return {
        "scope": list(scope),
        # The scope-level production-security claim: AND over the in-scope surfaces.
        "production_security_claim": claim,
        "status": "ready" if claim else "blocked",
        "per_surface": per_surface,
        "gaps": gaps,
    }
