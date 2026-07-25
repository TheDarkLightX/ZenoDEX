"""Pure immutable reference interpreter for the M5 expected-root commit port.

This module models one compare-and-swap linearization point for deterministic
unit tests. It is not evidence about a production datastore, crash recovery, or
external exactly-once delivery.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from ..core.fcis_atomic_mount_codec import (
    commit_bundle_root_v1,
    committed_state_root_v1,
    validate_commit_bundle_v1,
)
from ..core.fcis_atomic_mount_values import (
    FCISCommitBundleV1,
    FCISCommittedDexStateV1,
    FCISOutboxRecordV1,
    FCISReceiptV1,
    FCISReplayUpdateV1,
    require_digest_v1,
    require_replay_updates_v1,
)


@final
@dataclass(frozen=True, slots=True)
class FCISReferenceAtomicStoreV1:
    state: FCISCommittedDexStateV1
    accepted_bundle_roots: tuple[str, ...] = ()
    receipts: tuple[FCISReceiptV1, ...] = ()
    replay_updates: tuple[FCISReplayUpdateV1, ...] = ()
    outbox_records: tuple[FCISOutboxRecordV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.state) is not FCISCommittedDexStateV1:
            raise TypeError("reference store state must be exact")
        if type(self.accepted_bundle_roots) is not tuple:
            raise TypeError("accepted bundle roots must be an exact tuple")
        for root in self.accepted_bundle_roots:
            require_digest_v1(root, "accepted bundle root")
        if len(set(self.accepted_bundle_roots)) != len(self.accepted_bundle_roots):
            raise ValueError("accepted bundle roots must be unique")
        if type(self.receipts) is not tuple or any(
            type(receipt) is not FCISReceiptV1 for receipt in self.receipts
        ):
            raise TypeError("reference receipts must be exact")
        require_replay_updates_v1(self.replay_updates)
        if type(self.outbox_records) is not tuple or any(
            type(record) is not FCISOutboxRecordV1 for record in self.outbox_records
        ):
            raise TypeError("reference outbox records must be exact")

    @property
    def observed_pre_root(self) -> str:
        return committed_state_root_v1(self.state)


class FCISReferenceCrashPointV1(Enum):
    AFTER_VALIDATION = "after_validation"
    BEFORE_LINEARIZATION = "before_linearization"


class FCISReferenceCommitStatusV1(Enum):
    PUBLISHED = "published"
    STALE = "stale"
    DUPLICATE = "duplicate"
    INVALID = "invalid"
    INJECTED_FAILURE = "injected_failure"


@final
@dataclass(frozen=True, slots=True)
class FCISReferenceCommitResultV1:
    status: FCISReferenceCommitStatusV1
    store: FCISReferenceAtomicStoreV1

    def __post_init__(self) -> None:
        if type(self.status) is not FCISReferenceCommitStatusV1:
            raise TypeError("reference commit status must be exact")
        if type(self.store) is not FCISReferenceAtomicStoreV1:
            raise TypeError("reference commit store must be exact")


def _revalidate_bundle_v1(bundle: object) -> FCISCommitBundleV1 | None:
    if type(bundle) is not FCISCommitBundleV1:
        return None
    try:
        validate_commit_bundle_v1(bundle)
    except (AttributeError, TypeError, ValueError):
        return None
    return bundle


def commit_bundle_reference_v1(
    *,
    store: FCISReferenceAtomicStoreV1,
    bundle: object,
    crash_point: FCISReferenceCrashPointV1 | None = None,
) -> FCISReferenceCommitResultV1:
    """Apply a bundle or expose no publication at all."""

    if type(store) is not FCISReferenceAtomicStoreV1:
        raise TypeError("reference store must be exact")
    if crash_point is not None and type(crash_point) is not FCISReferenceCrashPointV1:
        return FCISReferenceCommitResultV1(FCISReferenceCommitStatusV1.INVALID, store)
    exact_bundle = _revalidate_bundle_v1(bundle)
    if exact_bundle is None:
        return FCISReferenceCommitResultV1(FCISReferenceCommitStatusV1.INVALID, store)

    bundle_root = commit_bundle_root_v1(exact_bundle)
    if bundle_root in store.accepted_bundle_roots:
        return FCISReferenceCommitResultV1(FCISReferenceCommitStatusV1.DUPLICATE, store)
    if exact_bundle.expected_pre_root != store.observed_pre_root:
        return FCISReferenceCommitResultV1(FCISReferenceCommitStatusV1.STALE, store)
    if crash_point is not None:
        return FCISReferenceCommitResultV1(
            FCISReferenceCommitStatusV1.INJECTED_FAILURE,
            store,
        )

    published = FCISReferenceAtomicStoreV1(
        state=exact_bundle.next_state,
        accepted_bundle_roots=(*store.accepted_bundle_roots, bundle_root),
        receipts=(*store.receipts, exact_bundle.receipt),
        replay_updates=(*store.replay_updates, *exact_bundle.replay_updates),
        outbox_records=(*store.outbox_records, *exact_bundle.outbox_plan.records),
    )
    return FCISReferenceCommitResultV1(FCISReferenceCommitStatusV1.PUBLISHED, published)


__all__ = (
    "FCISReferenceAtomicStoreV1",
    "FCISReferenceCommitResultV1",
    "FCISReferenceCommitStatusV1",
    "FCISReferenceCrashPointV1",
    "commit_bundle_reference_v1",
)
