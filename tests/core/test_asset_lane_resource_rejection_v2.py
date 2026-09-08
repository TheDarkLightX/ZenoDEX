"""Resource-overflow admission obligations for the bounded V2 asset lane.

An admitted typed pre-state whose post-state would need one more row or byte
than a declared ceiling must yield a typed no-op rejection, never a raised
``ValueError`` escaping the transition.  Malformed or oversized *pre* input
stays a constructor boundary error, and unrelated construction faults stay
raised.  The lane keeps authority NONE and SHADOW profile authentication.

The row-ceiling cases build real 4096-row states, so this file is slower than
the other lane suites; no production constant is changed to reach them.
"""

from __future__ import annotations

import pytest

import src.core.asset_lane_coordinator_v2 as coordinator_module
import src.core.asset_transfer_module_v2 as transfer_module
import src.core.global_settlement_resource_limits_v2 as limits_module
from src.core.asset_lane_coordinator_v2 import (
    AssetLaneAcceptedV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRouteV2,
    transition_asset_lane_v2,
)
from src.core.asset_lane_state_v2 import (
    MAX_ASSET_LANE_BALANCE_ROWS_V2,
    AssetLaneStateV2,
)
from src.core.asset_origin_registry_types_v2 import AssetOriginRegistryStateV2
from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_TRANSFER_COMMAND_KIND_V2,
    AssetTransferCommandV2,
    AssetTransferPolicyV2,
    AssetTransferRejectCodeV2,
    AssetTransferRejectedV2,
)
from src.core.global_settlement_resource_limits_v2 import (
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
    StateResourceLimitExceededV2,
    require_raw_tuple_ceiling_v2,
    require_rootable_asset_state_bytes_v2,
)
from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import (
    transition_managed_asset_lifecycle_v2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectCodeV2,
    ManagedAssetLifecycleRejectedV2,
)
from tests.core import test_asset_lane_coordinator_v2 as _fixture

_ROW_CEILING = MAX_ASSET_LANE_BALANCE_ROWS_V2


def _owner(index: int) -> str:
    return f"holder{index:04d}"


def _policy_frame() -> tuple[
    tuple[AssetTransferPolicyV2, ...],
    tuple[ManagedAssetLifecyclePolicyV2, ...],
    AssetOriginRegistryStateV2,
]:
    """Return EUR as transfer-only and USD as the managed asset."""

    transfers = (
        _fixture._transfer_policy(asset="EUR", fee_atoms=0),
        _fixture._transfer_policy(asset="USD", fee_atoms=0),
    )
    managed = (_fixture._managed_policy(),)
    return transfers, managed, _fixture._registry(transfers, managed)


def _lane_state(
    *,
    eur_rows: int,
    eur_first_atoms: int = 1,
    usd_rows: tuple[tuple[str, int], ...] = (),
) -> AssetLaneStateV2:
    transfers, managed, registry = _policy_frame()
    rows = [
        EconomicAmountV2(
            _owner(index),
            "EUR",
            ACCOUNT_CUSTODY_DOMAIN_V2,
            eur_first_atoms if index == 0 else 1,
        )
        for index in range(eur_rows)
    ]
    rows.extend(
        EconomicAmountV2(owner, "USD", ACCOUNT_CUSTODY_DOMAIN_V2, atoms)
        for owner, atoms in usd_rows
    )
    return AssetLaneStateV2(
        _fixture._root("module-release"),
        registry,
        transfers,
        managed,
        tuple(sorted(rows, key=lambda row: row.key)),
        (
            AssetSupplyV2("EUR", sum(row.amount_atoms for row in rows if row.asset == "EUR")),
            AssetSupplyV2("USD", sum(atoms for _, atoms in usd_rows)),
        ),
    )


def _eur_transfer(sender: str, recipient: str, amount_atoms: int) -> AssetTransferCommandV2:
    return AssetTransferCommandV2(
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V2,
        asset="EUR",
        sender=sender,
        recipient=recipient,
        amount_atoms=amount_atoms,
        max_fee_atoms=0,
        asset_origin_root=_fixture._root("origin:EUR"),
    )


def _assert_resource_noop(
    result: object,
    state: AssetLaneStateV2,
    route: AssetLaneRouteV2,
    code: object,
) -> None:
    """Check the exact route, code, root equality, and empty effect plan."""

    rejected = _fixture._assert_noop(result, state, code)
    assert rejected.route is route
    assert rejected.effects.occurrence_consumptions == ()
    assert rejected.effects.rows == ()
    assert rejected.effects.lane_writes == ()
    assert rejected.effects.external_outbox_enqueue == ()
    assert rejected.production_authority == "NONE"
    assert rejected.profile_authentication == "SHADOW"


def test_issue_over_the_aggregate_row_ceiling_is_a_typed_lane_rejection() -> None:
    """The managed leaf fits at one row while the rebound aggregate cannot."""

    state = _lane_state(eur_rows=_ROW_CEILING)
    command = _fixture._managed_command(owner="alice", amount_atoms=1)
    context = _fixture._context(command)
    pre_root = state.state_root
    assert len(state.balances) == _ROW_CEILING
    assert state.managed_leaf_state().balances == ()

    leaf = transition_managed_asset_lifecycle_v2(
        context.managed_context(),
        state.managed_leaf_state(),
        command,
    )
    assert isinstance(leaf, ManagedAssetLifecycleAcceptedV2)
    assert len(leaf.post_state.balances) == 1

    result = transition_asset_lane_v2(context, state, command)

    _assert_resource_noop(
        result,
        state,
        AssetLaneRouteV2.COORDINATOR,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    assert state.state_root == pre_root
    assert len(state.balances) == _ROW_CEILING
    assert state.supply_atoms("USD") == 0


def test_row_ceiling_admits_its_positive_neighbours() -> None:
    below = _lane_state(eur_rows=_ROW_CEILING - 1)
    issue = _fixture._managed_command(owner="alice", amount_atoms=1)
    issued = transition_asset_lane_v2(_fixture._context(issue), below, issue)

    assert isinstance(issued, AssetLaneAcceptedV2)
    assert len(issued.post_state.balances) == _ROW_CEILING
    assert issued.post_state.balance_atoms("alice", "USD") == 1
    assert issued.post_state.supply_atoms("USD") == 1

    at_ceiling = _lane_state(eur_rows=_ROW_CEILING, eur_first_atoms=5)
    moved = _eur_transfer(_owner(0), _owner(1), 1)
    result = transition_asset_lane_v2(_fixture._context(moved, nonce=2), at_ceiling, moved)

    assert isinstance(result, AssetLaneAcceptedV2)
    assert len(result.post_state.balances) == _ROW_CEILING
    assert result.post_state.balance_atoms(_owner(0), "EUR") == 4
    assert result.post_state.balance_atoms(_owner(1), "EUR") == 2


def test_transfer_creating_a_row_at_the_ceiling_rejects_in_the_transfer_leaf() -> None:
    state = _lane_state(eur_rows=_ROW_CEILING, eur_first_atoms=5)
    command = _eur_transfer(_owner(0), "alice", 1)
    context = _fixture._context(command)
    leaf_state = state.transfer_leaf_state()

    leaf = transition_asset_transfer_v2(context.transfer_context(), leaf_state, command)

    assert isinstance(leaf, AssetTransferRejectedV2)
    assert leaf.code is AssetTransferRejectCodeV2.STATE_RESOURCE_LIMIT
    assert leaf.pre_state_root == leaf.post_state_root == leaf_state.state_root
    assert leaf.effects.is_empty
    assert leaf.effects.occurrence_consumptions == ()

    _assert_resource_noop(
        transition_asset_lane_v2(context, state, command),
        state,
        AssetLaneRouteV2.TRANSFER,
        AssetTransferRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    assert state.balance_atoms(_owner(0), "EUR") == 5
    assert state.balance_atoms("alice", "EUR") == 0


def test_issue_creating_a_row_in_a_full_managed_leaf_is_a_typed_lane_rejection() -> None:
    """Direct managed calls and coordinated calls have the same typed rejection."""

    state = _lane_state(
        eur_rows=0,
        usd_rows=tuple((_owner(index), 1) for index in range(_ROW_CEILING)),
    )
    command = _fixture._managed_command(owner="alice", amount_atoms=1)
    context = _fixture._context(command)
    leaf_state = state.managed_leaf_state()
    assert len(leaf_state.balances) == _ROW_CEILING

    leaf = transition_managed_asset_lifecycle_v2(context.managed_context(), leaf_state, command)
    assert isinstance(leaf, ManagedAssetLifecycleRejectedV2)
    assert leaf.code is ManagedAssetLifecycleRejectCodeV2.STATE_RESOURCE_LIMIT
    assert leaf.pre_state_root == leaf.post_state_root == leaf_state.state_root
    assert leaf.effects.is_empty

    _assert_resource_noop(
        transition_asset_lane_v2(context, state, command),
        state,
        AssetLaneRouteV2.MANAGED_LIFECYCLE,
        ManagedAssetLifecycleRejectCodeV2.STATE_RESOURCE_LIMIT,
    )
    assert state.supply_atoms("USD") == _ROW_CEILING


def test_authorization_and_arithmetic_failures_precede_post_resource_admission() -> None:
    state = _lane_state(eur_rows=_ROW_CEILING)
    issue = _fixture._managed_command(owner="alice", amount_atoms=1)
    _fixture._assert_noop(
        transition_asset_lane_v2(_fixture._context(issue, subject="mallory"), state, issue),
        state,
        ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT,
    )
    transfer = _eur_transfer(_owner(0), "alice", 2)
    _fixture._assert_noop(
        transition_asset_lane_v2(_fixture._context(transfer), state, transfer),
        state,
        AssetTransferRejectCodeV2.INSUFFICIENT_BALANCE,
    )


def test_a_burn_frees_a_row_so_the_rejected_issue_retry_is_admitted() -> None:
    state = _lane_state(eur_rows=_ROW_CEILING - 1, usd_rows=(("bob", 3),))
    issue = _fixture._managed_command(owner="alice", amount_atoms=1)
    assert len(state.balances) == _ROW_CEILING

    first = transition_asset_lane_v2(_fixture._context(issue), state, issue)
    _assert_resource_noop(
        first,
        state,
        AssetLaneRouteV2.COORDINATOR,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )

    retried = transition_asset_lane_v2(_fixture._context(issue, nonce=2), state, issue)
    _assert_resource_noop(
        retried,
        state,
        AssetLaneRouteV2.COORDINATOR,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )

    burn = _fixture._managed_command(
        kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
        owner="bob",
        amount_atoms=3,
    )
    burned = transition_asset_lane_v2(_fixture._context(burn, nonce=3), state, burn)
    assert isinstance(burned, AssetLaneAcceptedV2)
    assert len(burned.post_state.balances) == _ROW_CEILING - 1
    assert burned.post_state.supply_atoms("USD") == 0

    admitted = transition_asset_lane_v2(
        _fixture._context(issue, nonce=4),
        burned.post_state,
        issue,
    )
    assert isinstance(admitted, AssetLaneAcceptedV2)
    assert len(admitted.post_state.balances) == _ROW_CEILING
    assert admitted.post_state.balance_atoms("alice", "USD") == 1
    assert admitted.post_state.supply_atoms("USD") == 1


def test_byte_ceiling_rejects_the_aggregate_while_the_leaf_still_fits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Lowered-threshold control for the byte ceiling.

    Production constants are untouched; only the module-level threshold the
    shared checker reads is lowered, and it is lowered to the exact admitted
    pre-state size so that one extra real row is the only thing that crosses
    it.  Every state, command, and route below is otherwise real.
    """

    state = _lane_state(eur_rows=2)
    command = _fixture._managed_command(owner="alice", amount_atoms=1)
    context = _fixture._context(command)
    threshold = len(canonical_global_bytes_v2(state.to_canonical()))
    monkeypatch.setattr(
        limits_module,
        "MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2",
        threshold,
    )

    leaf = transition_managed_asset_lifecycle_v2(
        context.managed_context(),
        state.managed_leaf_state(),
        command,
    )
    assert isinstance(leaf, ManagedAssetLifecycleAcceptedV2)
    assert len(canonical_global_bytes_v2(leaf.post_state.to_canonical())) <= threshold

    _assert_resource_noop(
        transition_asset_lane_v2(context, state, command),
        state,
        AssetLaneRouteV2.COORDINATOR,
        AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT,
    )


def test_shared_ceiling_helpers_separate_size_excess_from_shape_faults() -> None:
    ceiling = MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
    assert issubclass(StateResourceLimitExceededV2, ValueError)
    assert require_rootable_asset_state_bytes_v2(b"x" * ceiling, name="probe") is None
    assert require_raw_tuple_ceiling_v2((1, 2), name="probe", ceiling=2) == (1, 2)

    with pytest.raises(StateResourceLimitExceededV2, match=f"its {ceiling}-byte ceiling"):
        require_rootable_asset_state_bytes_v2(b"x" * (ceiling + 1), name="probe")
    with pytest.raises(StateResourceLimitExceededV2, match="its 2-item ceiling"):
        require_raw_tuple_ceiling_v2((1, 2, 3), name="probe", ceiling=2)

    with pytest.raises(TypeError, match="must be exact bytes"):
        require_rootable_asset_state_bytes_v2("x", name="probe")
    with pytest.raises(TypeError, match="must be a tuple"):
        require_raw_tuple_ceiling_v2([1], name="probe", ceiling=2)


def test_oversized_pre_state_stays_a_constructor_boundary_error() -> None:
    transfers, managed, registry = _policy_frame()
    rows = tuple(
        EconomicAmountV2(_owner(index), "EUR", ACCOUNT_CUSTODY_DOMAIN_V2, 1)
        for index in range(_ROW_CEILING + 1)
    )

    with pytest.raises(StateResourceLimitExceededV2, match=f"its {_ROW_CEILING}-item ceiling"):
        AssetLaneStateV2(
            _fixture._root("module-release"),
            registry,
            transfers,
            managed,
            rows,
            (AssetSupplyV2("EUR", len(rows)), AssetSupplyV2("USD", 0)),
        )

    with pytest.raises(ValueError) as excinfo:
        AssetLaneStateV2(
            _fixture._root("module-release"),
            registry,
            transfers,
            managed,
            (EconomicAmountV2("alice", "EUR", ACCOUNT_CUSTODY_DOMAIN_V2, 1),),
            (AssetSupplyV2("EUR", 2), AssetSupplyV2("USD", 0)),
        )
    assert not isinstance(excinfo.value, StateResourceLimitExceededV2)


def test_unrelated_post_construction_value_errors_are_not_swallowed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _lane_state(eur_rows=2)
    command = _fixture._managed_command(owner="alice", amount_atoms=1)
    context = _fixture._context(command)

    def _unrelated_aggregate(pre_state: object, candidate: object) -> AssetLaneStateV2:
        raise ValueError("unrelated aggregate fault")

    monkeypatch.setattr(coordinator_module, "_aggregate_post_state_v2", _unrelated_aggregate)
    with pytest.raises(ValueError, match="unrelated aggregate fault"):
        transition_asset_lane_v2(context, state, command)


def test_an_invariant_fault_in_the_transfer_post_state_still_raises(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _lane_state(eur_rows=2, eur_first_atoms=5)
    command = _eur_transfer(_owner(0), _owner(1), 1)
    context = _fixture._context(command)
    leaf_state = state.transfer_leaf_state()

    monkeypatch.setattr(
        transfer_module,
        "_post_balances",
        lambda pre_state, *, asset, deltas: (
            EconomicAmountV2(_owner(0), "EUR", ACCOUNT_CUSTODY_DOMAIN_V2, 0),
        ),
    )

    with pytest.raises(ValueError, match="must omit zero balances") as excinfo:
        transition_asset_transfer_v2(context.transfer_context(), leaf_state, command)
    assert not isinstance(excinfo.value, StateResourceLimitExceededV2)
