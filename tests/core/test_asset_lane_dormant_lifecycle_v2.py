"""Bounded V2 coordinator history for dormant registered assets.

The fixture keeps EUR as a transfer-only account frame, USD as a managed asset
starting at zero, and ZZZ as a dormant registered transfer-only key.  The
coordinator remains SHADOW/NONE evidence.  The fixture context binds an
occurrence pre-root; the coordinator's journal separately binds the selected
leaf pre-root to the aggregate state, so this file makes no global-root
authentication or publication claim.  The explicit stage and effect vectors
keep both leaf views and the EUR frame independently observable, which accounts
for the file exceeding the preferred compact test size.
"""

from __future__ import annotations

import pytest

import src.core.asset_lane_coordinator_v2 as coordinator_module
from src.core.asset_lane_coordinator_v2 import (
    AssetLaneAcceptedV2,
    AssetLaneCommandV2,
    AssetLaneCoordinatorRejectCodeV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
    transition_asset_lane_v2,
)
from src.core.asset_lane_state_v2 import AssetLaneStateV2
from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    AssetTransferRejectCodeV2,
)
from src.core.global_settlement_types_v2 import (
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_result_v2 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectCodeV2,
)
from tests.core import test_asset_lane_coordinator_v2 as _fixture

_ASSETS = ("EUR", "USD", "ZZZ")
# Fixed scalar vectors drive the expected aggregate and both leaf views.
_STAGE_SCALARS = ((0, None), (7, "alice"), (7, "bob"), (0, None), (2, "alice"), (2, "bob"))


def _balance_pairs(rows: tuple[EconomicAmountV2, ...]) -> tuple[tuple[str, str, int], ...]:
    return tuple((row.asset, row.owner, row.amount_atoms) for row in rows)


def _supply_pairs(rows: tuple[AssetSupplyV2, ...]) -> tuple[tuple[str, int], ...]:
    return tuple((row.asset, row.amount_atoms) for row in rows)


def _account_totals(
    rows: tuple[EconomicAmountV2, ...],
) -> tuple[tuple[str, int], ...]:
    return tuple(
        (asset, sum(row.amount_atoms for row in rows if row.asset == asset)) for asset in _ASSETS
    )


def _expected_stage(usd_atoms: int, owner: str | None) -> tuple[object, ...]:
    usd_balance = () if owner is None else (("USD", owner, usd_atoms),)
    balances = (("EUR", "carol", 500), *usd_balance)
    supplies = (("EUR", 500), ("USD", usd_atoms), ("ZZZ", 0))
    totals = (("EUR", 500), ("USD", usd_atoms), ("ZZZ", 0))
    return (balances, supplies, totals, usd_balance, (("USD", usd_atoms),))


_STAGES = tuple(_expected_stage(usd_atoms, owner) for usd_atoms, owner in _STAGE_SCALARS)


_ISSUE_7_ROWS = (
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 7),
    (EconomicEffectKindV2.ISSUE, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 7),
)
_TRANSFER_7_ROWS = (
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, -7),
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "bob", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 7),
)
_BURN_7_ROWS = (
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "bob", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, -7),
    (EconomicEffectKindV2.BURN, "bob", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, -7),
)
_ISSUE_2_ROWS = (
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 2),
    (EconomicEffectKindV2.ISSUE, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 2),
)
_TRANSFER_2_ROWS = (
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "alice", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, -2),
    (EconomicEffectKindV2.ACCOUNT_MOVEMENT, "bob", "USD", ACCOUNT_CUSTODY_DOMAIN_V2, 2),
)


def _state() -> AssetLaneStateV2:
    transfers = tuple(_fixture._transfer_policy(asset=asset, fee_atoms=0) for asset in _ASSETS)
    managed_policies = (_fixture._managed_policy(),)
    return AssetLaneStateV2(
        _fixture._root("module-release"),
        _fixture._registry(transfers, managed_policies),
        transfers,
        managed_policies,
        (EconomicAmountV2("carol", "EUR", ACCOUNT_CUSTODY_DOMAIN_V2, 500),),
        tuple(AssetSupplyV2(asset, 500 if asset == "EUR" else 0) for asset in _ASSETS),
    )


def _managed(kind: str, owner: str, amount_atoms: int) -> AssetLaneCommandV2:
    return _fixture._managed_command(
        kind=kind,
        owner=owner,
        amount_atoms=amount_atoms,
    )


def _issue(amount_atoms: int) -> AssetLaneCommandV2:
    return _managed(MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, "alice", amount_atoms)


def _burn(owner: str, amount_atoms: int) -> AssetLaneCommandV2:
    return _managed(MANAGED_ASSET_BURN_COMMAND_KIND_V2, owner, amount_atoms)


def _transfer(sender: str, recipient: str, amount_atoms: int) -> AssetLaneCommandV2:
    return _fixture._transfer_command(
        sender=sender,
        recipient=recipient,
        amount_atoms=amount_atoms,
        max_fee_atoms=0,
    )


def _invoke(
    state: AssetLaneStateV2,
    command: AssetLaneCommandV2,
    nonce: int,
) -> AssetLaneAcceptedV2 | AssetLaneRejectedV2:
    context = _fixture._context(command, nonce=nonce)
    before = (
        canonical_global_bytes_v2(state.to_canonical()),
        canonical_global_bytes_v2(command.to_canonical()),
        canonical_global_bytes_v2(context.to_canonical()),
    )
    before_root = state.state_root
    assert context.occurrence is not None
    assert context.global_pre_state_root == context.occurrence.pre_state_root
    assert context.global_pre_state_root == _fixture._root(f"global-pre:{nonce}")

    result = transition_asset_lane_v2(context, state, command)

    after = (
        canonical_global_bytes_v2(state.to_canonical()),
        canonical_global_bytes_v2(command.to_canonical()),
        canonical_global_bytes_v2(context.to_canonical()),
    )
    assert after == before
    assert state.state_root == before_root
    if isinstance(result, AssetLaneAcceptedV2):
        assert result.module_journal.pre_lane_root == before_root
        assert result.effects.lane_writes[0].pre_root == before_root
        assert result.effects.lane_writes[0].post_root == result.post_state.state_root
    return result


def _assert_views(
    state: AssetLaneStateV2,
    policy_frame: tuple[object, ...],
    expected: tuple[object, ...],
) -> None:
    balances, supplies, totals, managed_balances, managed_supplies = expected
    assert (state.origin_registry, state.transfer_policies, state.managed_policies) == policy_frame
    assert tuple(policy.asset for policy in state.transfer_policies) == _ASSETS
    assert tuple(policy.asset for policy in state.managed_policies) == ("USD",)
    assert (_balance_pairs(state.balances), _supply_pairs(state.supplies)) == (balances, supplies)
    assert _account_totals(state.balances) == totals
    transfer_leaf = state.transfer_leaf_state()
    managed_leaf = state.managed_leaf_state()
    assert (_balance_pairs(transfer_leaf.balances), _supply_pairs(transfer_leaf.supplies)) == (
        balances,
        supplies,
    )
    assert (_balance_pairs(managed_leaf.balances), _supply_pairs(managed_leaf.supplies)) == (
        managed_balances,
        managed_supplies,
    )


def _effect_vector(
    result: AssetLaneAcceptedV2,
) -> tuple[tuple[object, str, str, str, int], ...]:
    return tuple(
        (row.kind, row.principal, row.asset, row.custody_domain, row.delta_atoms)
        for row in result.effects.rows
    )


def _assert_accept(
    result: object,
    route: AssetLaneRouteV2,
    effect_rows: tuple[tuple[object, str, str, str, int], ...],
    conservation: tuple[str, int, int, int, int, int, int],
) -> AssetLaneAcceptedV2:
    assert isinstance(result, AssetLaneAcceptedV2)
    assert result.route is route
    assert result.production_authority == "NONE"
    assert result.profile_authentication == "SHADOW"
    assert _effect_vector(result) == effect_rows
    assert result.effects.fee_conservation == ()
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.occurrence_consumptions == (result.module_journal.command_occurrence_id,)
    rows = result.effects.asset_conservation
    assert len(rows) == 1
    row = rows[0]
    assert (
        row.asset,
        row.owned_and_custodied_pre_atoms,
        row.owned_and_custodied_post_atoms,
        row.supply_pre_atoms,
        row.supply_post_atoms,
        row.authorized_issue_atoms,
        row.authorized_burn_atoms,
    ) == conservation
    return result


def test_dormant_managed_history_rebinds_both_leaf_views_after_burn_and_reissue() -> None:
    state = _state()
    policy_frame = (state.origin_registry, state.transfer_policies, state.managed_policies)
    assert state.transfer_policies[1].transfer_fee_atoms == 0
    assert {row.asset: row.issue_policy_root for row in state.origin_registry.assets}["ZZZ"] == (
        ZERO_ROOT_V2
    )
    _assert_views(state, policy_frame, _STAGES[0])
    accepted_steps = (
        (
            _issue(7),
            1,
            AssetLaneRouteV2.MANAGED_LIFECYCLE,
            _ISSUE_7_ROWS,
            ("USD", 0, 7, 0, 7, 7, 0),
            1,
        ),
        (
            _transfer("alice", "bob", 7),
            2,
            AssetLaneRouteV2.TRANSFER,
            _TRANSFER_7_ROWS,
            ("USD", 7, 7, 7, 7, 0, 0),
            2,
        ),
        (
            _burn("bob", 7),
            3,
            AssetLaneRouteV2.MANAGED_LIFECYCLE,
            _BURN_7_ROWS,
            ("USD", 7, 0, 7, 0, 0, 7),
            3,
        ),
        (
            _issue(2),
            6,
            AssetLaneRouteV2.MANAGED_LIFECYCLE,
            _ISSUE_2_ROWS,
            ("USD", 0, 2, 0, 2, 2, 0),
            4,
        ),
        (
            _transfer("alice", "bob", 2),
            7,
            AssetLaneRouteV2.TRANSFER,
            _TRANSFER_2_ROWS,
            ("USD", 2, 2, 2, 2, 0, 0),
            5,
        ),
    )
    for command, nonce, route, effect_rows, conservation, stage in accepted_steps[:3]:
        accepted = _assert_accept(_invoke(state, command, nonce), route, effect_rows, conservation)
        state = accepted.post_state
        _assert_views(state, policy_frame, _STAGES[stage])

    for command, nonce, code, route in (
        (
            _transfer("bob", "alice", 1),
            4,
            AssetTransferRejectCodeV2.INSUFFICIENT_BALANCE,
            AssetLaneRouteV2.TRANSFER,
        ),
        (
            _burn("bob", 1),
            5,
            ManagedAssetLifecycleRejectCodeV2.INSUFFICIENT_BALANCE,
            AssetLaneRouteV2.MANAGED_LIFECYCLE,
        ),
    ):
        rejected = _fixture._assert_noop(_invoke(state, command, nonce), state, code)
        assert rejected.route is route

    for command, nonce, route, effect_rows, conservation, stage in accepted_steps[3:]:
        accepted = _assert_accept(_invoke(state, command, nonce), route, effect_rows, conservation)
        state = accepted.post_state
        _assert_views(state, policy_frame, _STAGES[stage])


def test_frozen_managed_aggregate_projection_is_a_named_noop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _state()
    original = coordinator_module._aggregate_post_state_v2

    def frozen_managed_projection(
        pre_state: AssetLaneStateV2, candidate: object
    ) -> AssetLaneStateV2:
        if type(candidate) is ManagedAssetLifecycleAcceptedV2:
            return pre_state
        return original(pre_state, candidate)

    monkeypatch.setattr(
        coordinator_module,
        "_aggregate_post_state_v2",
        frozen_managed_projection,
    )
    result = _invoke(state, _issue(7), 11)

    rejected = _fixture._assert_noop(
        result,
        state,
        AssetLaneCoordinatorRejectCodeV2.PROJECTION_MISMATCH,
    )
    assert rejected.route is AssetLaneRouteV2.COORDINATOR
