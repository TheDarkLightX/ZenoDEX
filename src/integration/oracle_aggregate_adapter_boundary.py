"""Fail-closed production boundary for aggregate Oracle adapter verification.

The only aggregate-adapter implementation currently in this repository lives
under :mod:`tools`.  Its import graph contains the pre-MVP local Oracle CLI,
sample construction, report signing, and development-service helpers.  Those
capabilities are deliberately absent from production images and must not be
pulled into the value-moving runtime merely to reuse a verifier function.

Until a verification-only implementation is independently extracted,
reviewed, and promoted, every bridge presented to the shipped runtime is
rejected.  Keeping the unavailable state as executable data makes callers
fail closed without an environment-dependent import or an accidental fallback
to development tooling.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

ORACLE_AGGREGATE_ADAPTER_CAPABILITY_SCHEMA = (
    "zenodex.oracle.aggregate_adapter_verifier_capability.v1"
)
ORACLE_AGGREGATE_ADAPTER_RESULT_SCHEMA = (
    "zenodex.oracle.aggregate_adapter_verify_result.v1"
)
ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE = (
    "production_oracle_aggregate_adapter_verifier_not_promoted"
)
ORACLE_AGGREGATE_ADAPTER_VERIFIER_AVAILABLE = False

_NOT_CLAIMED = (
    "does_not_claim_bridge_valid",
    "does_not_claim_aggregate_valid",
    "does_not_claim_receipt_bundle_valid",
    "does_not_claim_production_oracle_network_live",
)


@dataclass(frozen=True, slots=True)
class OracleAggregateAdapterCapability:
    """Immutable runtime capability declaration surfaced to operators."""

    available: bool = ORACLE_AGGREGATE_ADAPTER_VERIFIER_AVAILABLE
    mode: str = "fail_closed"
    reason: str = ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": ORACLE_AGGREGATE_ADAPTER_CAPABILITY_SCHEMA,
            "available": self.available,
            "mode": self.mode,
            "reason": self.reason,
        }


@dataclass(frozen=True, slots=True)
class OracleAggregateAdapterUnavailableResult:
    """Shape-compatible rejection returned at the production boundary."""

    status: str = "rejected"
    errors: tuple[str, ...] = (ORACLE_AGGREGATE_ADAPTER_UNAVAILABLE,)
    bridge_id: None = None
    aggregate_read_bridge_id: None = None
    aggregate_id: None = None
    query_id: None = None
    value_hash: None = None
    consumer_module: None = None
    action_kind: None = None
    action_id: None = None
    read_receipt_id: None = None
    consumer_action_receipt_id: None = None
    profile_id: None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": ORACLE_AGGREGATE_ADAPTER_RESULT_SCHEMA,
            "ok": False,
            "status": self.status,
            "bridge_id": self.bridge_id,
            "aggregate_read_bridge_id": self.aggregate_read_bridge_id,
            "aggregate_id": self.aggregate_id,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "action_id": self.action_id,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "profile_id": self.profile_id,
            "errors": list(self.errors),
            "not_claimed": list(_NOT_CLAIMED),
        }


def oracle_aggregate_adapter_capability() -> OracleAggregateAdapterCapability:
    """Return the immutable production capability declaration."""

    return OracleAggregateAdapterCapability()


def verify_aggregate_adapter_bridge(
    _bridge: Mapping[str, Any],
) -> OracleAggregateAdapterUnavailableResult:
    """Reject every bridge until a verification-only runtime is promoted."""

    return OracleAggregateAdapterUnavailableResult()
