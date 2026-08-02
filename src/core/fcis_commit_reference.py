"""Pure immutable reference commit port for the FCIS atomic publication law.

This module models expected-root atomic publication as one pure immutable store
transition.  It is test evidence for the abstract atomicity law, not a
production database adapter, crash-recovery proof, or delivery worker.

No exception escapes for an exact store plus an exact but post-construction-
corrupted bundle.  Every validation, patch, replay, root, receipt, plan, or
outbox mismatch returns ``INVALID`` and the unchanged exact store.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import cast, final

from ..state.committed_dex_snapshot import canonical_committed_state_root_binding_v1
from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.state_transitions import (
    BalancePatchApplyOkV1,
    CanonicalBalancePatchV1,
    CanonicalLPPositionPatchV1,
    CanonicalNoncePatchV1,
    CanonicalPoolPatchV1,
    LPPositionPatchApplyOkV1,
    NoncePatchApplyOkV1,
    PoolPatchApplyOkV1,
    apply_canonical_balance_patch_v1,
    apply_canonical_lp_position_patch_v1,
    apply_canonical_nonce_patch_v1,
    apply_canonical_pool_patch_v1,
)
from .fcis_commit_bundle_derivation import (
    CommitBundleV1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
    verify_anf_bound_commit_bundle_v1,
)
from .fcis_decision_derivation import AcceptV1, CommittedFailureV1
from .fcis_decision_values import (
    AcceptanceReceiptClaimV1,
    CommittedFailureReceiptClaimV1,
)
from .fcis_outbox_values import OutboxPlanV1, OutboxPlanV2
from .fcis_transition_values import CommitPlanV1


def _has_exact_type_v1(value: object, expected: type[object]) -> bool:
    return type(value) is expected


class ReferenceCommitStatusV1(Enum):
    """Closed status values for one reference commit attempt."""

    PUBLISHED = "published"
    STALE = "stale"
    INVALID = "invalid"
    ALREADY_COMMITTED = "already_committed"
    CRASHED_BEFORE_LINEARIZATION = "crashed_before_linearization"
    CRASHED_AFTER_LINEARIZATION = "crashed_after_linearization"


class ReferenceCrashPointV1(Enum):
    """Test-only crash-point selector for the pure reference simulation."""

    NONE = "none"
    BEFORE_LINEARIZATION = "before_linearization"
    AFTER_LINEARIZATION = "after_linearization"


@final
@dataclass(frozen=True, slots=True)
class ReferencePublicationV1:
    """One complete publication retaining the full bundle lineage."""

    bundle: CommitBundleV1

    def __post_init__(self) -> None:
        if not _has_exact_type_v1(self.bundle, CommitBundleV1):
            raise TypeError("reference publication requires an exact CommitBundleV1")


@final
@dataclass(frozen=True, slots=True)
class ReferenceCommitStoreV1:
    """Immutable reference store: one current state and zero or more publications."""

    current_state: FCISCommittedStateV1
    publications: tuple[ReferencePublicationV1, ...]

    def __post_init__(self) -> None:
        if not _has_exact_type_v1(self.current_state, FCISCommittedStateV1):
            raise TypeError("reference store requires an exact committed state")
        if type(self.publications) is not tuple or any(
            not _has_exact_type_v1(publication, ReferencePublicationV1)
            for publication in self.publications
        ):
            raise TypeError("reference store requires an exact publication tuple")


@final
@dataclass(frozen=True, slots=True)
class ReferenceCommitResultV1:
    """One pure commit result: status and the exact store after the attempt."""

    status: ReferenceCommitStatusV1
    store: ReferenceCommitStoreV1

    def __post_init__(self) -> None:
        if not _has_exact_type_v1(self.status, ReferenceCommitStatusV1):
            raise TypeError("reference result requires an exact ReferenceCommitStatusV1")
        if not _has_exact_type_v1(self.store, ReferenceCommitStoreV1):
            raise TypeError("reference result requires an exact ReferenceCommitStoreV1")


def _initial_reference_commit_store_v1(
    state: object,
) -> ReferenceCommitStoreV1:
    """Construct one initial empty reference store over an exact state."""

    if not _has_exact_type_v1(state, FCISCommittedStateV1):
        raise TypeError("reference store requires an exact committed state")
    exact_state = cast(FCISCommittedStateV1, state)
    return ReferenceCommitStoreV1(exact_state, ())


def _revalidate_bundle_v1(bundle: object) -> bool:
    """Revalidate the entire nested controlled bundle structure."""

    if not _has_exact_type_v1(bundle, CommitBundleV1):
        return False
    exact_bundle = cast(CommitBundleV1, bundle)
    try:
        decision = exact_bundle.decision
        if type(decision) not in (AcceptV1, CommittedFailureV1):
            return False
        if not _has_exact_type_v1(decision.next_state, FCISCommittedStateV1):
            return False
        if not _has_exact_type_v1(decision.commit_plan, CommitPlanV1):
            return False
        if type(decision) is AcceptV1:
            receipt_type: type[object] = AcceptanceReceiptClaimV1
        else:
            receipt_type = CommittedFailureReceiptClaimV1
        if not _has_exact_type_v1(decision.receipt, receipt_type):
            return False
        binding_root = decision.receipt.binding.authority_normal_form_root
        if binding_root is None:
            if not _has_exact_type_v1(exact_bundle.outbox_plan, OutboxPlanV1):
                return False
            if exact_bundle.authority_normal_form is not None:
                return False
        else:
            if not _has_exact_type_v1(exact_bundle.outbox_plan, OutboxPlanV2):
                return False
            if not verify_anf_bound_commit_bundle_v1(exact_bundle):
                return False
        recomputed_outbox = recompute_outbox_plan_v1(exact_bundle)
        if recomputed_outbox != exact_bundle.outbox_plan:
            return False
        recomputed_bytes, recomputed_root = recompute_bundle_root_v1(exact_bundle)
        if recomputed_bytes != exact_bundle._canonical_bundle_bytes:
            return False
        if recomputed_root != exact_bundle._bundle_root:
            return False
    except (AttributeError, OverflowError, TypeError, ValueError):
        return False
    return True


def _apply_patch_atoms_v1(
    pre_state: FCISCommittedStateV1,
    bundle: CommitBundleV1,
) -> FCISCommittedStateV1 | None:
    """Apply every compare-and-replace patch atom and replay nonce advance.

    Returns the applied successor or ``None`` on any mismatch.
    """

    plan = bundle.decision.commit_plan
    patch = plan.patch
    balances = pre_state.balances
    if patch.balance_writes:
        result = apply_canonical_balance_patch_v1(
            balances,
            CanonicalBalancePatchV1(patch.balance_writes),
        )
        if type(result) is not BalancePatchApplyOkV1:
            return None
        balances = result.state
    pools = pre_state.pools
    if patch.pool_writes:
        result = apply_canonical_pool_patch_v1(
            pools,
            CanonicalPoolPatchV1(patch.pool_writes),
        )
        if type(result) is not PoolPatchApplyOkV1:
            return None
        pools = result.state
    lp_balances = pre_state.lp_balances
    if patch.lp_writes:
        result = apply_canonical_lp_position_patch_v1(
            lp_balances,
            CanonicalLPPositionPatchV1(patch.lp_writes),
        )
        if type(result) is not LPPositionPatchApplyOkV1:
            return None
        lp_balances = result.state
    nonces = pre_state.nonces
    if plan.replay.nonce_advances:
        result = apply_canonical_nonce_patch_v1(
            nonces,
            CanonicalNoncePatchV1(plan.replay.nonce_advances),
        )
        if type(result) is not NoncePatchApplyOkV1:
            return None
        nonces = result.state
    fee_write = patch.fee_accumulator_write
    if fee_write is not None:
        if fee_write.expected != pre_state.fee_accumulator:
            return None
        fee_accumulator = fee_write.replacement
    else:
        fee_accumulator = pre_state.fee_accumulator
    vault_write = patch.vault_write
    if vault_write is not None:
        if vault_write.expected != pre_state.vault:
            return None
        vault = vault_write.replacement
    else:
        vault = pre_state.vault
    oracle_write = patch.oracle_write
    if oracle_write is not None:
        if oracle_write.expected != pre_state.oracle:
            return None
        oracle = oracle_write.replacement
    else:
        oracle = pre_state.oracle
    perps_write = patch.perps_write
    if perps_write is not None:
        if perps_write.expected != pre_state.perps:
            return None
        perps = perps_write.replacement
    else:
        perps = pre_state.perps
    return FCISCommittedStateV1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_accumulator,
        perps=perps,
    )


def _state_fields_equal_v1(
    left: FCISCommittedStateV1,
    right: FCISCommittedStateV1,
) -> bool:
    """Compare all eight state fields for exact equality."""

    return bool(
        left.balances == right.balances
        and left.pools == right.pools
        and left.lp_balances == right.lp_balances
        and left.nonces == right.nonces
        and left.vault == right.vault
        and left.oracle == right.oracle
        and left.fee_accumulator == right.fee_accumulator
        and left.perps == right.perps
    )


def _revalidate_store_v1(store: object) -> bool:
    """Revalidate exact store shape, publication bundles, and visible head state."""

    if not _has_exact_type_v1(store, ReferenceCommitStoreV1):
        return False
    exact_store = cast(ReferenceCommitStoreV1, store)
    try:
        if not _has_exact_type_v1(exact_store.current_state, FCISCommittedStateV1):
            return False
        if type(exact_store.publications) is not tuple or any(
            not _has_exact_type_v1(publication, ReferencePublicationV1)
            for publication in exact_store.publications
        ):
            return False
        observed_roots: tuple[str, ...] = ()
        for publication in exact_store.publications:
            if not _revalidate_bundle_v1(publication.bundle):
                return False
            _, root = recompute_bundle_root_v1(publication.bundle)
            if root in observed_roots:
                return False
            observed_roots += (root,)
        if exact_store.publications:
            visible_successor = exact_store.publications[-1].bundle.decision.next_state
            if not _state_fields_equal_v1(exact_store.current_state, visible_successor):
                return False
    except (AttributeError, OverflowError, TypeError, ValueError):
        return False
    return True


def _observed_pre_root_v1(
    state: FCISCommittedStateV1,
    snapshot_version: int,
) -> str:
    """Recompute the observed pre-root using the receipt snapshot version."""

    _, _, root = canonical_committed_state_root_binding_v1(state, snapshot_version)
    return cast(str, root)


def _bundle_root_in_publications_v1(
    store: ReferenceCommitStoreV1,
    bundle_root: str,
) -> bool:
    """Check whether an exact valid bundle root is already in publications."""

    return any(publication.bundle._bundle_root == bundle_root for publication in store.publications)


def reference_commit_v1(
    store: object,
    bundle: object,
    crash_point: object = ReferenceCrashPointV1.NONE,
) -> ReferenceCommitResultV1:
    """Execute one pure reference commit attempt over an immutable store.

    The reference algorithm:
    1. Revalidate the exact store and entire nested controlled bundle.
    2. Recompute observed pre-root and successor root.
    3. If an exact valid bundle root is already in publications, return
       ALREADY_COMMITTED with the unchanged store (after full revalidation).
    4. If observed root differs from expected pre-root, return STALE.
    5. Apply every compare-and-replace patch atom and replay nonce advance.
    6. Require the applied result to equal the bundle successor (all 8 fields).
    7. Require the successor root to equal the expected successor root.
    8. A modeled crash before the linearization point returns the unchanged store.
    9. Otherwise create one new immutable store with the complete publication.
    10. A modeled crash after the linearization point returns that complete new
        store with CRASHED_AFTER_LINEARIZATION; no partial form exists.

    No exception escapes for an exact store plus an exact but corrupted bundle.
    """

    if not _has_exact_type_v1(store, ReferenceCommitStoreV1):
        raise TypeError("reference commit requires an exact ReferenceCommitStoreV1")
    exact_store = cast(ReferenceCommitStoreV1, store)
    if not _has_exact_type_v1(crash_point, ReferenceCrashPointV1):
        raise TypeError("reference commit requires an exact ReferenceCrashPointV1")
    exact_crash_point = cast(ReferenceCrashPointV1, crash_point)
    if not _revalidate_store_v1(exact_store):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    if not _revalidate_bundle_v1(bundle):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    exact_bundle = cast(CommitBundleV1, bundle)
    decision = exact_bundle.decision
    successor = decision.next_state
    snapshot_version = decision.receipt.binding.snapshot_version
    try:
        observed_pre_root = _observed_pre_root_v1(exact_store.current_state, snapshot_version)
        _, _, successor_root = canonical_committed_state_root_binding_v1(
            successor,
            snapshot_version,
        )
    except (AttributeError, OverflowError, TypeError, ValueError):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    expected_pre_root = decision.receipt.binding.pre_state_root
    expected_successor_root = decision.receipt.binding.next_state_root
    if _bundle_root_in_publications_v1(exact_store, exact_bundle._bundle_root):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.ALREADY_COMMITTED,
            exact_store,
        )
    if observed_pre_root != expected_pre_root:
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.STALE,
            exact_store,
        )
    try:
        applied = _apply_patch_atoms_v1(exact_store.current_state, exact_bundle)
    except (AttributeError, OverflowError, TypeError, ValueError):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    if applied is None or not _state_fields_equal_v1(applied, successor):
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    if successor_root != expected_successor_root:
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.INVALID,
            exact_store,
        )
    if exact_crash_point is ReferenceCrashPointV1.BEFORE_LINEARIZATION:
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.CRASHED_BEFORE_LINEARIZATION,
            exact_store,
        )
    publication = ReferencePublicationV1(exact_bundle)
    new_store = ReferenceCommitStoreV1(
        successor,
        exact_store.publications + (publication,),
    )
    if exact_crash_point is ReferenceCrashPointV1.AFTER_LINEARIZATION:
        return ReferenceCommitResultV1(
            ReferenceCommitStatusV1.CRASHED_AFTER_LINEARIZATION,
            new_store,
        )
    return ReferenceCommitResultV1(
        ReferenceCommitStatusV1.PUBLISHED,
        new_store,
    )


__all__ = (
    "ReferenceCommitResultV1",
    "ReferenceCommitStatusV1",
    "ReferenceCommitStoreV1",
    "ReferenceCrashPointV1",
    "ReferencePublicationV1",
    "_initial_reference_commit_store_v1",
    "reference_commit_v1",
)
