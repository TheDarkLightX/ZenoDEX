"""Per-surface, *computed* production-security claim.

The production-security claim is COMPUTED from a structured CBC evidence object,
never asserted. A surface's claim is true only when all seven CBC columns are
cleared; the scope-level ``production_security_claim`` is the AND over a declared
set of surfaces. The live registry is
``config/production/cbc_surface_evidence_v1.json`` and the release/CI gate is
``tools/gate_cbc_matrix_closure.py``. Missing or unverified evidence becomes a
gap, and any gap fails the claim closed.

This module is intentionally pure (no I/O, no global state). It computes the
claim; consumers decide how to enforce the result. The production release gate
now treats a clean blocked claim as a regression because the reviewed spot-DEX
registry computes ``production_security_claim=true``.

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
# are the consensus AUTHORITY surfaces with the most existing proof coverage, used
# to prove the per-surface machinery end-to-end before widening to perps / zUSD /
# lanes. A surface belongs here only if it is on the live authority path.
SPOT_DEX_SCOPE: tuple[str, ...] = (
    "cpmm_swap",
    "balances",
    "state_root",
    "nonces",
)

# Source-pinned expected authority set per known production ``scope_id``. The gate
# anchors a known scope against THIS (source-controlled) set, so that a registry
# edit alone — even a coordinated one that marks a real surface ``evidence_only``
# AND drops it from ``claim_scope`` — cannot shrink or alter a production claim's
# scope without a reviewed code change here. Adding/removing a production surface
# is therefore a source change, not a config-only edit.
KNOWN_SCOPE_AUTHORITY_SETS: dict[str, frozenset[str]] = {
    "spot_dex": frozenset(SPOT_DEX_SCOPE),
}

# Role marker for a registry surface row that is retained for traceability but
# EXCLUDED from the production claim because it is not on the live authority path
# — a proof-carrier / CBC-core reference form attached to a real surface. Carried
# as ``"claim_role": "evidence_only"`` on the surface row, together with a REQUIRED
# ``"attached_to"`` naming the in-scope authority surface it backs (the gate
# rejects a dangling/orphaned evidence row). Example: ``replay_guard``
# (src/core/replay_guard.py) is the
# single-transition reference whose Kani + differential proofs are EVIDENCE for the
# live ``nonces`` authority (src/state/nonces.py), bound on the single-transition
# slice by tests/runtime/test_replay_guard_nonce_refinement_binding.py. Such a row
# never enters the AND — it can neither block nor inflate the scope claim.
EVIDENCE_ONLY_ROLE: str = "evidence_only"


VALID_CLAIM_ROLES: frozenset[str] = frozenset({"authority", EVIDENCE_ONLY_ROLE})


def claim_role_of(surface_evidence: Any) -> str:
    """Return a surface row's claim role (default ``"authority"`` when absent).

    Raises ``ValueError`` on an unrecognized role so release-gate tooling fails
    closed rather than silently treating a typo'd / unknown role as authority.
    """
    if not isinstance(surface_evidence, Mapping):
        return "authority"
    role = surface_evidence.get("claim_role", "authority")
    if role not in VALID_CLAIM_ROLES:
        raise ValueError(
            f"unknown claim_role {role!r} (expected one of {sorted(VALID_CLAIM_ROLES)})"
        )
    return role


def is_evidence_only(surface_evidence: Any) -> bool:
    """True iff a registry surface row is retained for evidence/traceability only
    (``claim_role == "evidence_only"``) and must be excluded from the claim AND.

    Note: this is an *exact* predicate (a typo'd role is NOT evidence_only, so it
    stays in the claim AND — the safe direction). Use :func:`claim_role_of` when
    you need an unknown role to fail closed instead."""
    return (
        isinstance(surface_evidence, Mapping)
        and surface_evidence.get("claim_role") == EVIDENCE_ONLY_ROLE
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


def validate_surface_columns(surface_id: str, evidence: Mapping[str, Any]) -> None:
    """Raise ``ValueError`` if any PRESENT CBC column has a malformed shape.

    This distinguishes a *schema violation* (which must fail closed / exit 2) from
    a valid-but-unverified column (a normal gap / exit 1). An ABSENT column is a
    gap, not a malformation. A present column must match the schema:

    - ``open_gaps_closed`` (the gate column) must be a JSON boolean;
    - every other CBC column must be an object with a string ``ref`` and a boolean
      ``verified``.

    Without this, ``_column_cleared`` would silently treat e.g. ``"running_impl":
    "src/x.py"`` or ``"open_gaps_closed": "yes"`` as merely uncleared, masking a
    malformed registry as an ordinary blocked claim.
    """
    if not isinstance(evidence, Mapping):
        raise ValueError(f"{surface_id}: surface row must be an object")
    for column in CBC_COLUMNS:
        if column not in evidence:
            continue
        value = evidence[column]
        if column in _GATE_COLUMNS:
            if not isinstance(value, bool):
                raise ValueError(
                    f"{surface_id}: '{column}' must be a boolean, got {type(value).__name__}"
                )
            continue
        if not isinstance(value, Mapping):
            raise ValueError(
                f"{surface_id}: '{column}' must be an object {{ref, verified}}, "
                f"got {type(value).__name__}"
            )
        if not isinstance(value.get("ref"), str):
            raise ValueError(f"{surface_id}: '{column}.ref' must be a string")
        if not isinstance(value.get("verified"), bool):
            raise ValueError(f"{surface_id}: '{column}.verified' must be a boolean")


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
    if any(not isinstance(surface_id, str) or not surface_id.strip() for surface_id in scope):
        raise ValueError("scope entries must be non-empty surface ids")
    if len(set(scope)) != len(scope):
        raise ValueError("scope must not contain duplicate surface ids")
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
