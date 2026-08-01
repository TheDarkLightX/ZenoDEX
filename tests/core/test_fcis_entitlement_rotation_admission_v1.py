"""C06 rotation, reset, and deployment-bound migration witnesses."""
from __future__ import annotations

import pytest

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
)
from src.core.fcis_entitlement_rotation_admission_v1 import (
    C06AuthorityCodeV1,
    C06AuthorityContextV1,
    C06AuthorityRejectV1,
    C06MigrationAcceptedV1,
    C06OperationalConfigurationV1,
    C06RotationCodeV1,
    C06RotationRejectV1,
    C06RotationSnapshotV1,
    check_representation_migration_authority_v1,
    check_rotation_preserves_history_v1,
)
from src.core.fcis_entitlement_transport_v1 import (
    transport_srgd_to_agqe_v1,
)
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)


def _key(asset: str = "USDC") -> EntitlementKeyV1:
    return EntitlementKeyV1(
        "protocol-fees",
        asset,
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        FIXED_ROLE_ORDER_ID_V1,
    )


def _state(
    representation_id: str = SRGD_REPRESENTATION_PROFILE_ID_V1,
    *,
    asset: str = "USDC",
    entries: tuple[EntitlementStateEntryV1, ...] | None = None,
) -> EntitlementStateV1:
    return EntitlementStateV1(
        _key(asset),
        representation_id,
        (
            EntitlementStateEntryV1("entry-0", (3, -1, -2)),
            EntitlementStateEntryV1("entry-1", (-4, 2, 2)),
        )
        if entries is None
        else entries,
    )


def _configuration(
    *,
    policy_weights: tuple[int, int, int] = (1, 2, 3),
    destinations: tuple[str, str, str] = ("buyback-A", "treasury-A", "rewards-A"),
    custody_account: str = "custody-A",
) -> C06OperationalConfigurationV1:
    return C06OperationalConfigurationV1(
        policy_weights,
        destinations,
        custody_account,
    )


def _context(
    state: EntitlementStateV1,
    *,
    deployment_id: str = "deployment-A",
    authority_epoch_root: str = "0x" + "11" * 32,
) -> C06AuthorityContextV1:
    return C06AuthorityContextV1(
        deployment_id,
        authority_epoch_root,
        state,
    )


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    "configuration",
    [
        _configuration(policy_weights=(3, 1, 2)),
        _configuration(destinations=("buyback-B", "treasury-B", "rewards-B")),
        _configuration(custody_account="custody-B"),
    ],
)
def test_policy_destination_and_custody_rotation_preserve_history(
    configuration: C06OperationalConfigurationV1,
) -> None:
    state = _state()
    before = C06RotationSnapshotV1(state, _configuration())
    after = C06RotationSnapshotV1(state, configuration)
    assert check_rotation_preserves_history_v1(before, after) is None
    assert before.state.key == after.state.key
    assert before.state.entries == after.state.entries


def test_rotation_sequence_preserves_history_before_representation_migration() -> None:
    state = _state()
    snapshot = C06RotationSnapshotV1(state, _configuration())
    configurations = (
        _configuration(policy_weights=(3, 1, 2)),
        _configuration(destinations=("buyback-B", "treasury-B", "rewards-B")),
        _configuration(custody_account="custody-B"),
    )
    for configuration in configurations:
        next_snapshot = C06RotationSnapshotV1(state, configuration)
        assert check_rotation_preserves_history_v1(snapshot, next_snapshot) is None
        snapshot = next_snapshot
    assert snapshot.state.key == state.key
    assert snapshot.state.entries == state.entries


def test_rotation_key_substitution_rejects() -> None:
    before = C06RotationSnapshotV1(_state(), _configuration())
    after = C06RotationSnapshotV1(
        _state(asset="BTC"),
        _configuration(destinations=("buyback-B", "treasury-B", "rewards-B")),
    )
    assert check_rotation_preserves_history_v1(before, after) == C06RotationRejectV1(
        C06RotationCodeV1.KEY_CHANGED,
        ("after", "state", "key"),
    )


def test_rotation_representation_and_history_mutants_reject() -> None:
    before = C06RotationSnapshotV1(_state(), _configuration())
    representation_changed = C06RotationSnapshotV1(
        _state(AGQE_REPRESENTATION_PROFILE_ID_V1),
        _configuration(),
    )
    assert check_rotation_preserves_history_v1(before, representation_changed) == (
        C06RotationRejectV1(
            C06RotationCodeV1.REPRESENTATION_CHANGED,
            ("after", "state", "representation_id"),
        )
    )
    history_changed = C06RotationSnapshotV1(
        _state(entries=(EntitlementStateEntryV1("entry-0", (4, -1, -3)),)),
        _configuration(),
    )
    assert check_rotation_preserves_history_v1(before, history_changed) == (
        C06RotationRejectV1(
            C06RotationCodeV1.HISTORY_CHANGED,
            ("after", "state", "entries"),
        )
    )


def test_representation_migration_preserves_exact_history_under_authority_check() -> None:
    old_state = _state()
    target_result = transport_srgd_to_agqe_v1(old_state)
    assert isinstance(target_result, EntitlementStateV1)
    current = _context(old_state)
    accepted = check_representation_migration_authority_v1(
        current,
        current,
        _context(
            target_result,
            authority_epoch_root="0x" + "22" * 32,
        ),
    )
    assert isinstance(accepted, C06MigrationAcceptedV1)
    assert accepted.deployment_id == "deployment-A"
    assert accepted.source_state_root == old_state.state_root
    assert accepted.target_state_root == target_result.state_root
    assert accepted.source_authority_epoch_root == "0x" + "11" * 32
    assert accepted.target_authority_epoch_root == "0x" + "22" * 32


def test_zero_reset_migration_rejects_at_authority_boundary() -> None:
    old_state = _state()
    zero_state = _state(
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        entries=(
            EntitlementStateEntryV1("entry-0", (0, 0, 0)),
            EntitlementStateEntryV1("entry-1", (0, 0, 0)),
        ),
    )
    result = check_representation_migration_authority_v1(
        _context(old_state),
        _context(old_state),
        _context(zero_state, authority_epoch_root="0x" + "22" * 32),
    )
    assert result == C06AuthorityRejectV1(
        C06AuthorityCodeV1.TRANSPORT_REJECT,
        ("target_context", "zero_reset"),
    )


def test_partial_entry_migration_rejects_at_authority_boundary() -> None:
    old_state = _state()
    partial_state = _state(
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        entries=(EntitlementStateEntryV1("entry-0", (-3, 1, 2)),),
    )
    result = check_representation_migration_authority_v1(
        _context(old_state),
        _context(old_state),
        _context(partial_state, authority_epoch_root="0x" + "22" * 32),
    )
    assert result == C06AuthorityRejectV1(
        C06AuthorityCodeV1.TRANSPORT_REJECT,
        ("target_context", "entry_set_mismatch"),
    )


def test_cross_deployment_state_substitution_rejects_before_transport() -> None:
    old_state = _state()
    target_result = transport_srgd_to_agqe_v1(old_state)
    assert isinstance(target_result, EntitlementStateV1)
    result = check_representation_migration_authority_v1(
        _context(old_state, deployment_id="deployment-A"),
        _context(old_state, deployment_id="deployment-B"),
        _context(target_result, deployment_id="deployment-B"),
    )
    assert result == C06AuthorityRejectV1(
        C06AuthorityCodeV1.DEPLOYMENT_MISMATCH,
        ("source_context", "deployment_id"),
    )


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    "current, source, target",
    [
        (object(), object(), object()),
        (_context(_state()), object(), object()),
    ],
)
def test_authority_context_types_fail_closed(
    current: object,
    source: object,
    target: object,
) -> None:
    result = check_representation_migration_authority_v1(current, source, target)
    assert isinstance(result, C06AuthorityRejectV1)
    assert result.code is C06AuthorityCodeV1.WRONG_EXACT_TYPE
