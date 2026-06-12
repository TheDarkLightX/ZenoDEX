"""Node-anchored committed governance surface and apply path (WS5 routing).

`autonomous_governance_live_apply.py` is the admission wrapper, but it takes
the committed surface state and the expected store/context hashes FROM THE
CALLER — correct for a client-side check, insufficient for the deployed node
boundary, where the §5.2 binding precondition of
`docs/AUTONOMOUS_GOVERNANCE_ARCHITECTURE.md` requires that *the runtime owns
the anchor*.

This module is that anchor.  The node's committed governance surface IS the
file-backed session-store head (one source of truth — a second registry would
reintroduce the divergence the design exists to prevent):

- `committed_governance_surface_v1` is the read path consumers use;
- `apply_autonomous_governance_update_from_node_state_v1` is the ONLY
  intended mutation path: it derives the committed surface state, the
  expected store hash, and the live-context hash from the node's OWN store
  head — the caller supplies only the pinned policy, the trajectory receipt,
  and the policy pin it expects — and then routes through
  `admit_autonomous_governance_live_session_file_update_v1`.

A caller therefore CANNOT substitute its own `curr`/state: anything it
asserts about the committed surface is ignored in favor of the head.  The
read-then-admit window is closed by the store's compare-and-swap
(`expected_store_hash` is the head hash read here; a concurrent advance makes
the admission refuse with a store-hash mismatch instead of applying against a
stale anchor).

NOT claimed: global store ordering/distribution across nodes (each node
anchors to its own store; cross-node convergence is the remaining WS5
distribution work), oracle truth, or settlement authority.
"""

from __future__ import annotations

import os
from typing import Any, Mapping

from src.integration.autonomous_governance_live_apply import (
    admit_autonomous_governance_live_session_file_update_v1,
    autonomous_governance_live_session_file_context_hash_v1,
)
from src.integration.autonomous_governance_session_store_file import (
    current_session_store_file_head_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0

AUTONOMOUS_GOVERNANCE_COMMITTED_SURFACE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.committed_surface.v1"
)
AUTONOMOUS_GOVERNANCE_NODE_APPLY_SCHEMA_V1 = (
    "zenodex.autonomous_governance.node_apply.v1"
)

_COMMITTED_SURFACE_HASH_TAG = "autonomous_governance_committed_surface_v1"
_NODE_APPLY_HASH_TAG = "autonomous_governance_node_apply_v1"

ANCHOR_SOURCE_V1 = "session_store_file_head_v1"

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_claim_global_store_ordering",
    "does_not_claim_oracle_truth",
)


def committed_governance_surface_v1(
    *, store_path: str | os.PathLike[str]
) -> dict[str, Any]:
    """Read the node's committed governance surface from its anchor.

    This is the read path a consumer (or operator endpoint) uses; the values
    come from the session-store file head, never from any caller assertion.
    """
    head = current_session_store_file_head_v1(path=store_path)
    ok = head.get("ok") is True
    surface_state = (
        dict(head.get("surface_state", {}))
        if isinstance(head.get("surface_state"), Mapping)
        else {}
    )
    head_pin = (
        dict(head.get("head_pin", {}))
        if isinstance(head.get("head_pin"), Mapping)
        else {}
    )
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_COMMITTED_SURFACE_SCHEMA_V1,
        "ok": ok,
        "errors": tuple(str(error) for error in head.get("errors", ())),
        "anchor_source": ANCHOR_SOURCE_V1,
        "surface_state": surface_state if ok else {},
        "store_hash": str(head.get("store_hash", "")),
        "head_pin_hash": str(head_pin.get("pin_hash", "")),
        "trajectory_chain_head": str(head_pin.get("trajectory_chain_head", "")),
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "committed_surface_hash": hash_v0(_COMMITTED_SURFACE_HASH_TAG, body)}


def apply_autonomous_governance_update_from_node_state_v1(
    *,
    store_path: str | os.PathLike[str],
    policy: object,
    trajectory_receipt: object,
    expected_policy_hash: object,
) -> dict[str, Any]:
    """Apply one autonomous-governance update with the anchor owned by the node.

    The caller supplies ONLY the pinned policy object, the trajectory receipt,
    and the policy pin it expects.  The committed surface state, the expected
    store hash, and the live-context hash are all derived here from the node's
    own session-store file head, then the existing admission wrapper performs
    trajectory verification and the CAS store advance.  Every refusal is a
    total no-op on the store.
    """
    errors: list[str] = []

    expected_hash = expected_policy_hash if type(expected_policy_hash) is str else ""
    if not expected_hash:
        errors.append("node_apply_expected_policy_hash_required")

    head = current_session_store_file_head_v1(path=store_path)
    if head.get("ok") is not True:
        errors.append("node_apply_store_head_unavailable")
        errors.extend(str(error) for error in head.get("errors", ()))

    committed_surface_state: dict[str, Any] = (
        dict(head.get("surface_state", {}))
        if isinstance(head.get("surface_state"), Mapping)
        else {}
    )
    head_pin = (
        dict(head.get("head_pin", {}))
        if isinstance(head.get("head_pin"), Mapping)
        else {}
    )
    store_hash = str(head.get("store_hash", ""))

    receipt = trajectory_receipt if isinstance(trajectory_receipt, Mapping) else {}
    if not receipt:
        errors.append("node_apply_trajectory_receipt_must_be_object")
    trajectory_hash = receipt.get("trajectory_hash", "") if receipt else ""
    if type(trajectory_hash) is not str or not trajectory_hash:
        errors.append("node_apply_trajectory_hash_required")
        trajectory_hash = ""

    admission: dict[str, Any] = {}
    if not errors:
        # Node-derived binding: the context hash is computed over the head this
        # node just read, so the admission below can only succeed against
        # exactly this anchor (CAS on store_hash closes the read->admit race).
        expected_live_context_hash = (
            autonomous_governance_live_session_file_context_hash_v1(
                store_hash=store_hash,
                head_pin_hash=str(head_pin.get("pin_hash", "")),
                committed_surface_state=committed_surface_state,
                trajectory_hash=trajectory_hash,
                expected_policy_hash=expected_hash,
            )
        )
        admission = admit_autonomous_governance_live_session_file_update_v1(
            store_path=store_path,
            policy=policy,
            trajectory_receipt=receipt,
            committed_surface_state=committed_surface_state,
            expected_policy_hash=expected_hash,
            expected_store_hash=store_hash,
            expected_live_context_hash=expected_live_context_hash,
        )
        if admission.get("admitted") is not True:
            errors.append("node_apply_admission_refused")
            errors.extend(str(error) for error in admission.get("errors", ()))

    admitted = not errors
    applied_state = (
        dict(admission.get("applied_state", {}))
        if admitted and isinstance(admission.get("applied_state"), Mapping)
        else committed_surface_state
    )

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_NODE_APPLY_SCHEMA_V1,
        "ok": admitted,
        "admitted": admitted,
        "errors": tuple(errors),
        "anchor_source": ANCHOR_SOURCE_V1,
        "store_path": str(store_path),
        "expected_policy_hash": expected_hash,
        "trajectory_hash": trajectory_hash,
        "committed_state": committed_surface_state,
        "applied_state": applied_state,
        "store_hash_before": store_hash,
        "store_hash_after": str(admission.get("store_hash_after", ""))
        if admission
        else "",
        "admission": admission,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "node_apply_hash": hash_v0(_NODE_APPLY_HASH_TAG, body)}
