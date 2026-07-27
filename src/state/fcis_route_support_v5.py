"""Exact route-pool support projection for the FCIS v5 authority graph.

The legacy v4 support-root module also reuses this function for differential
evidence.  Exact FCIS consumers import this module directly so their authority
graph never reaches the mixed legacy support-root implementation.
"""

from __future__ import annotations

from .intent_snapshots import OwnedIntentV1, owned_intent_field_v1
from .owned_collections import OwnedMapV1


def route_support_pool_ids_owned_v5(intent: OwnedIntentV1) -> tuple[str, ...]:
    """Return the canonical pool-id support of one admitted route intent."""

    if type(intent) is not OwnedIntentV1:
        raise TypeError("route support intent must be an exact OwnedIntentV1")
    raw_legs = owned_intent_field_v1(intent, "route_legs", None)
    raw_fingerprints = owned_intent_field_v1(
        intent,
        "route_pool_fingerprints",
        None,
    )
    if type(raw_legs) is not tuple or not raw_legs:
        raise ValueError("exact route support requires a nonempty leg tuple")
    if type(raw_fingerprints) is not OwnedMapV1 or not raw_fingerprints:
        raise TypeError("exact route support requires an owned fingerprint map")

    leg_pool_ids: list[str] = []
    for raw_leg in raw_legs:
        if type(raw_leg) is not OwnedMapV1:
            raise TypeError("exact route support requires owned leg maps")
        pool_id = raw_leg.get("pool_id")
        if type(pool_id) is not str or not pool_id:
            raise ValueError("exact route support requires nonempty pool ids")
        leg_pool_ids.append(pool_id)
    fingerprint_pool_ids = tuple(key for key, _value in raw_fingerprints.entries)
    if any(type(pool_id) is not str or not pool_id for pool_id in fingerprint_pool_ids):
        raise ValueError("exact route support fingerprint keys must be nonempty strings")
    if any(type(value) is not str or not value for _key, value in raw_fingerprints.entries):
        raise ValueError("exact route support fingerprints must be nonempty strings")
    canonical_leg_pool_ids = tuple(sorted(set(leg_pool_ids)))
    if canonical_leg_pool_ids != tuple(sorted(fingerprint_pool_ids)):
        raise ValueError("exact route support legs and fingerprints disagree")
    return canonical_leg_pool_ids


__all__ = ("route_support_pool_ids_owned_v5",)
