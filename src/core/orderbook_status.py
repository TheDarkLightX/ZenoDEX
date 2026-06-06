"""
Order / proof lifecycle status enums for the proof-carrying orderbook surface.

This is the STATUS-MODEL layer of the proof-carrying orderbook build spec
(``docs/product_discipline/proof_carrying_orderbook_build_spec.md``). It exists so
that request acknowledgement, execution, replay verification, and proof finality
are *separate* labels in every response, and so that exactly ONE status
(``proof_verified``) maps to trustless client finality.

The acceptance rule the spec pins is::

    ClientAccepts(result) :=
      checkpoint_chain_verified
      and proof_receipt_verified
      and journal_bound_to_header_root
      and verifier_identity_pinned
      and rulebook_hash_pinned_or_validly_upgraded

Stage 0 produces NONE of that proof material. Therefore :func:`is_final` is True
for ``proof_verified`` only; every other status (including ``executed``) is
explicitly NON-final. ``executed`` means the matching kernel applied the order
locally, NOT that a client verified the transition.

CBC discipline: pure, deterministic, no I/O. The enums carry stable string values
because those strings cross the API/SDK boundary and are part of the contract.
"""

from __future__ import annotations

from enum import Enum
from typing import Union

__all__ = [
    "OrderStatus",
    "ProofStatus",
    "DataStatus",
    "is_final",
    "FINAL_ORDER_STATUS_VALUE",
]


class OrderStatus(Enum):
    """
    Lifecycle status of a submitted order.

    The values are the canonical strings used across REST, SDK, and tests. The
    set is fixed by the spec's status model; do not add finality-implying labels.

    * ``received`` — request shape accepted, not yet sequenced.
    * ``sequenced`` — assigned a deterministic order-event sequence.
    * ``executed`` — matching kernel applied the order locally (NOT final).
    * ``replay_verified`` — a client re-derived the transition locally (Stage 1).
    * ``proof_pending`` — proof material is being produced / not yet available.
    * ``proof_verified`` — proof material verified; the ONLY final status.
    * ``rejected`` — a stable reject code applied; reject-is-no-op on state.
    * ``expired`` — deadline / expires_at in the past.
    * ``cancelled`` — a sequenced cancel order event removed the resting order.
    """

    RECEIVED = "received"
    SEQUENCED = "sequenced"
    EXECUTED = "executed"
    REPLAY_VERIFIED = "replay_verified"
    PROOF_PENDING = "proof_pending"
    PROOF_VERIFIED = "proof_verified"
    REJECTED = "rejected"
    EXPIRED = "expired"
    CANCELLED = "cancelled"


class ProofStatus(Enum):
    """
    Status of the proof material attached to an order / fill / market.

    Stage 0 only ever emits ``proof_pending`` or ``not_available``. ``proof_verified``
    is defined so the SDK finality helper has a single positive target, but Stage 0
    never produces it (no proof is generated — see the build spec Non-Goals).
    """

    PROOF_PENDING = "proof_pending"
    NOT_AVAILABLE = "not_available"
    PROOF_VERIFIED = "proof_verified"


class DataStatus(Enum):
    """
    Honest data-availability / staleness label for a market or fill view.

    Stage 0 is a non-persistent, single-process, unproven view. ``live_unproven``
    is the only honest label it can emit: the data reflects the in-memory book but
    carries no proof and no durability guarantee.
    """

    LIVE_UNPROVEN = "live_unproven"


# The single status value that maps to trustless client finality. Kept as a
# module constant so the SDK can compare against it without importing the enum
# class semantics (string equality, positive match, fail-closed).
FINAL_ORDER_STATUS_VALUE: str = OrderStatus.PROOF_VERIFIED.value


def is_final(status: Union[OrderStatus, str, None]) -> bool:
    """
    Return True iff ``status`` is the single final status (``proof_verified``).

    FAIL-CLOSED by construction: this is a POSITIVE equality test, never a
    negation of a known non-final set. Any unknown / unrecognized status string,
    ``None``, or non-string maps to False — it can never "fall through" to final.

    Accepts either an :class:`OrderStatus` or its raw string value so the same
    rule applies whether the caller holds the enum or a decoded wire string.
    """
    if isinstance(status, OrderStatus):
        return status is OrderStatus.PROOF_VERIFIED
    if isinstance(status, str):
        return status == FINAL_ORDER_STATUS_VALUE
    return False
