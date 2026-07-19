"""HTTP-free handler for the autonomous-governance live-apply API (WS5).

Uses the standard integration pattern: `api_server.py` owns transport,
auth, and the default-OFF feature flag (`AUTOGOV_LIVE_APPLY_API_ENABLED`);
this module owns request semantics and is fully testable without a socket.

Fail-closed production posture:

- the node must configure `AUTOGOV_SESSION_STORE_PATH` (no default store);
- the node must PIN the policy via `AUTOGOV_PINNED_POLICY_HASH`; an apply
  request whose `expected_policy_hash` differs from the node pin is refused —
  the policy choice is a node/operator decision, never a caller decision;
- the committed surface anchor always comes from the node's own store head
  (`autonomous_governance_live_registry.py`); any caller-supplied committed
  state in the request body is ignored by construction.

Routes:

- `GET  /api/autogov/surface` — the committed governance surface (read-only).
- `POST /api/autogov/apply`   — body `{policy, trajectory_receipt,
  expected_policy_hash}`; routes through the node-anchored apply path.
"""

from __future__ import annotations

import json
import os
from typing import Any

from src.integration.autonomous_governance_live_registry import (
    apply_autonomous_governance_update_from_node_state_v1,
    committed_governance_surface_v1,
)

AUTOGOV_LIVE_APPLY_API_ENABLED_ENV = "AUTOGOV_LIVE_APPLY_API_ENABLED"
AUTOGOV_SESSION_STORE_PATH_ENV = "AUTOGOV_SESSION_STORE_PATH"
AUTOGOV_PINNED_POLICY_HASH_ENV = "AUTOGOV_PINNED_POLICY_HASH"

_MAX_BODY_BYTES = 8 * 1024 * 1024


def handle_autogov_request(
    method: str,
    path: str,
    raw_body: bytes | None,
    *,
    store_path: str | None = None,
    pinned_policy_hash: str | None = None,
) -> tuple[int, dict[str, Any]]:
    """Handle one autogov API request; returns (status, response_body).

    `store_path` / `pinned_policy_hash` default to the environment so the
    server glue stays one line; tests inject them directly.
    """
    if store_path is None:
        store_path = os.environ.get(AUTOGOV_SESSION_STORE_PATH_ENV, "").strip()
    if pinned_policy_hash is None:
        pinned_policy_hash = os.environ.get(
            AUTOGOV_PINNED_POLICY_HASH_ENV, ""
        ).strip()

    if not store_path:
        # Fail closed: an enabled route without a configured anchor is a
        # deployment error, not an invitation to default somewhere writable.
        return 503, {
            "ok": False,
            "error": "autogov_store_path_not_configured",
            "required_env": AUTOGOV_SESSION_STORE_PATH_ENV,
        }

    if method == "GET" and path == "/api/autogov/surface":
        surface = committed_governance_surface_v1(store_path=store_path)
        return (200 if surface.get("ok") else 503), surface

    if method == "POST" and path == "/api/autogov/apply":
        if not pinned_policy_hash:
            return 503, {
                "ok": False,
                "error": "autogov_policy_pin_not_configured",
                "required_env": AUTOGOV_PINNED_POLICY_HASH_ENV,
            }
        if raw_body is None or len(raw_body) == 0:
            return 400, {"ok": False, "error": "autogov_body_required"}
        if len(raw_body) > _MAX_BODY_BYTES:
            return 413, {"ok": False, "error": "autogov_body_too_large"}
        try:
            body = json.loads(raw_body.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            return 400, {"ok": False, "error": "autogov_body_invalid_json"}
        if not isinstance(body, dict):
            return 400, {"ok": False, "error": "autogov_body_must_be_object"}

        requested_pin = body.get("expected_policy_hash")
        if type(requested_pin) is not str or not requested_pin:
            return 400, {"ok": False, "error": "autogov_expected_policy_hash_required"}
        if requested_pin != pinned_policy_hash:
            # The node pins the policy; a caller cannot select a different one.
            return 403, {
                "ok": False,
                "error": "autogov_policy_hash_not_node_pinned",
                "node_pinned_policy_hash": pinned_policy_hash,
            }

        result = apply_autonomous_governance_update_from_node_state_v1(
            store_path=store_path,
            policy=body.get("policy"),
            trajectory_receipt=body.get("trajectory_receipt"),
            expected_policy_hash=requested_pin,
        )
        return (200 if result.get("admitted") else 409), result

    return 404, {"ok": False, "error": "autogov_route_not_found"}
