"""Required custody states must reach the successor's actual V2 transitions."""

from dataclasses import replace

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2, AssetLaneRouteV2
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_settlement_types_v2 import MAX_ATOMS_V2, AssetSupplyV2, EconomicAmountV2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleRejectCodeV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _managed_policy,
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)


def custody_state(accounts=80, custody=20):
    transfer, managed = _transfer_policy(), _managed_policy()
    leaf = AssetTransferStateV2(
        _root("module-release"),
        (transfer,),
        (EconomicAmountV2("alice", "USD", "accounts", accounts),) if accounts else (),
        (AssetSupplyV2("USD", accounts + custody),),
    )
    return AssetLaneCustodyStateV2(
        leaf,
        _registry((transfer,), (managed,)),
        (managed,),
        (EconomicAmountV2("vault", "USD", "escrow", custody),) if custody else (),
    )


_MULTIASSET_ASSETS = ("AUD", "EUR", "GBP", "JPY", "USD", "VND", "ZZZ")
_MULTIASSET_MANAGED_ASSETS = ("GBP", "USD")


def multiasset_custody_state() -> AssetLaneCustodyStateV2:
    """Build the complete seven-asset table used by the lifecycle history."""

    transfer_policies = tuple(
        _transfer_policy(asset=asset, fee_atoms=0) for asset in _MULTIASSET_ASSETS
    )
    managed_policies = tuple(
        _managed_policy(asset=asset) for asset in _MULTIASSET_MANAGED_ASSETS
    )
    return AssetLaneCustodyStateV2(
        AssetTransferStateV2(
            _root("module-release"),
            transfer_policies,
            (
                EconomicAmountV2("carol", "EUR", "accounts", 7),
                EconomicAmountV2("dana", "GBP", "accounts", 3),
                EconomicAmountV2("erin", "JPY", "accounts", 5),
                EconomicAmountV2("frank", "VND", "accounts", 11),
            ),
            (
                AssetSupplyV2("AUD", 0),
                AssetSupplyV2("EUR", 9),
                AssetSupplyV2("GBP", 3),
                AssetSupplyV2("JPY", 5),
                AssetSupplyV2("USD", 0),
                AssetSupplyV2("VND", 11),
                AssetSupplyV2("ZZZ", 0),
            ),
        ),
        _registry(transfer_policies, managed_policies),
        managed_policies,
        (EconomicAmountV2("vault", "EUR", "escrow", 2),),
    )


def _assert_multiasset_accepted(
    result: object,
    source: AssetLaneCustodyStateV2,
    expected_balances: tuple[EconomicAmountV2, ...],
    expected_supplies: tuple[AssetSupplyV2, ...],
) -> AssetLaneCustodyAcceptedV2:
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    post = result.post_state
    assert result.route is AssetLaneRouteV2.MANAGED_LIFECYCLE
    assert post.transfer_state.balances == expected_balances
    assert post.transfer_state.supplies == expected_supplies
    assert tuple(policy.asset for policy in post.transfer_state.policies) == _MULTIASSET_ASSETS
    assert tuple(row.asset for row in post.origin_registry.assets) == _MULTIASSET_ASSETS
    assert tuple(policy.asset for policy in post.managed_policies) == _MULTIASSET_MANAGED_ASSETS
    assert post.transfer_state.module_release_id == _root("module-release")
    assert post.transfer_state.policies == source.transfer_state.policies
    assert post.origin_registry == source.origin_registry
    assert post.managed_policies == source.managed_policies
    assert source.custody == (EconomicAmountV2("vault", "EUR", "escrow", 2),)
    assert post.custody == (EconomicAmountV2("vault", "EUR", "escrow", 2),)
    assert result.production_authority == "NONE"
    assert result.profile_authentication == "SHADOW"
    return result


def _assert_source_unchanged(
    source: AssetLaneCustodyStateV2,
    canonical: dict[str, object],
    state_root: str,
) -> None:
    assert source.to_canonical() == canonical
    assert source.state_root == state_root


def test_managed_multiasset_history_keeps_complete_rows_and_rejects_unauthorized_burn():
    source = multiasset_custody_state()
    source_canonical = source.to_canonical()
    source_root = source.state_root

    issue = _managed_command(amount_atoms=2)
    issued = _assert_multiasset_accepted(
        transition_asset_lane_custody_v2(_context(issue, nonce=1), source, issue),
        source,
        (
            EconomicAmountV2("carol", "EUR", "accounts", 7),
            EconomicAmountV2("dana", "GBP", "accounts", 3),
            EconomicAmountV2("erin", "JPY", "accounts", 5),
            EconomicAmountV2("alice", "USD", "accounts", 2),
            EconomicAmountV2("frank", "VND", "accounts", 11),
        ),
        (
            AssetSupplyV2("AUD", 0),
            AssetSupplyV2("EUR", 9),
            AssetSupplyV2("GBP", 3),
            AssetSupplyV2("JPY", 5),
            AssetSupplyV2("USD", 2),
            AssetSupplyV2("VND", 11),
            AssetSupplyV2("ZZZ", 0),
        ),
    )
    _assert_source_unchanged(source, source_canonical, source_root)

    middle = issued.post_state
    middle_canonical = middle.to_canonical()
    middle_root = middle.state_root
    burn = _managed_command(
        kind="managed_asset_burn",
        owner="alice",
        amount_atoms=2,
    )
    unauthorized = transition_asset_lane_custody_v2(
        _context(burn, subject="mallory", nonce=2), middle, burn
    )
    assert isinstance(unauthorized, AssetLaneRejectedV2)
    assert unauthorized.route is AssetLaneRouteV2.MANAGED_LIFECYCLE
    assert unauthorized.code is ManagedAssetLifecycleRejectCodeV2.UNAUTHORIZED_SUBJECT
    assert unauthorized.pre_state_root == unauthorized.post_state_root == middle_root
    assert unauthorized.effects.is_empty
    _assert_source_unchanged(middle, middle_canonical, middle_root)

    burned = _assert_multiasset_accepted(
        transition_asset_lane_custody_v2(_context(burn, nonce=3), middle, burn),
        middle,
        (
            EconomicAmountV2("carol", "EUR", "accounts", 7),
            EconomicAmountV2("dana", "GBP", "accounts", 3),
            EconomicAmountV2("erin", "JPY", "accounts", 5),
            EconomicAmountV2("frank", "VND", "accounts", 11),
        ),
        (
            AssetSupplyV2("AUD", 0),
            AssetSupplyV2("EUR", 9),
            AssetSupplyV2("GBP", 3),
            AssetSupplyV2("JPY", 5),
            AssetSupplyV2("USD", 0),
            AssetSupplyV2("VND", 11),
            AssetSupplyV2("ZZZ", 0),
        ),
    )
    _assert_source_unchanged(middle, middle_canonical, middle_root)

    burned_source = burned.post_state
    burned_source_canonical = burned_source.to_canonical()
    burned_source_root = burned_source.state_root
    reissue = _managed_command(amount_atoms=1, owner="bob")
    _assert_multiasset_accepted(
        transition_asset_lane_custody_v2(_context(reissue, nonce=4), burned_source, reissue),
        burned_source,
        (
            EconomicAmountV2("carol", "EUR", "accounts", 7),
            EconomicAmountV2("dana", "GBP", "accounts", 3),
            EconomicAmountV2("erin", "JPY", "accounts", 5),
            EconomicAmountV2("bob", "USD", "accounts", 1),
            EconomicAmountV2("frank", "VND", "accounts", 11),
        ),
        (
            AssetSupplyV2("AUD", 0),
            AssetSupplyV2("EUR", 9),
            AssetSupplyV2("GBP", 3),
            AssetSupplyV2("JPY", 5),
            AssetSupplyV2("USD", 1),
            AssetSupplyV2("VND", 11),
            AssetSupplyV2("ZZZ", 0),
        ),
    )
    _assert_source_unchanged(burned_source, burned_source_canonical, burned_source_root)


def test_given_accounts_and_vault_when_authorized_transfer_then_complete_value_is_preserved():
    before = custody_state()
    command = _transfer_command(amount_atoms=10)
    result = transition_asset_lane_custody_v2(_context(command), before, command)
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    assert result.post_state.transfer_state.balances == (
        EconomicAmountV2("alice", "USD", "accounts", 68),
        EconomicAmountV2("bob", "USD", "accounts", 10),
        EconomicAmountV2("treasury", "USD", "accounts", 2),
    )
    assert result.post_state.custody == before.custody
    row = result.effects.asset_conservation[0]
    assert row.owned_and_custodied_pre_atoms == row.owned_and_custodied_post_atoms == 100
    assert row.supply_pre_atoms == row.supply_post_atoms == 100
    assert result.module_journal.post_lane_root == result.post_state.state_root
    assert result.module_journal.effect_plan_root == result.effects.effect_plan_root


def test_historical_account_only_state_does_not_silently_reinterpret_custody():
    state = custody_state()
    with pytest.raises(ValueError, match="owned account total must equal supply"):
        AssetLaneStateV2(
            state.transfer_state.module_release_id,
            state.origin_registry,
            state.transfer_state.policies,
            state.managed_policies,
            state.transfer_state.balances,
            state.transfer_state.supplies,
        )


def test_issue_then_burn_preserves_custody_and_complete_supply():
    before = custody_state()
    issue = _managed_command(amount_atoms=7)
    issued = transition_asset_lane_custody_v2(_context(issue), before, issue)
    assert isinstance(issued, AssetLaneCustodyAcceptedV2)
    assert issued.post_state.transfer_state.supply_atoms("USD") == 107
    burn = replace(issue, command_kind="managed_asset_burn", authorization_root=_root("burn:USD"))
    burned = transition_asset_lane_custody_v2(_context(burn, nonce=2), issued.post_state, burn)
    assert isinstance(burned, AssetLaneCustodyAcceptedV2)
    assert burned.post_state.to_canonical() == before.to_canonical()


def test_unauthorized_transfer_is_exact_no_effect():
    state = custody_state()
    original = state.to_canonical()
    command = _transfer_command(amount_atoms=10)
    result = transition_asset_lane_custody_v2(_context(command, subject="mallory"), state, command)
    assert result.code.value == "UNAUTHORIZED_SUBJECT"
    assert result.pre_state_root == result.post_state_root == state.state_root
    assert result.effects.is_empty
    assert state.to_canonical() == original


@settings(max_examples=40, derandomize=True, database=None, deadline=None)
@given(
    accounts=st.integers(3, 100_000),
    vault=st.integers(1, 100_000),
    selector=st.integers(0, 100_000),
)
def test_required_valid_custody_domain_has_successful_transfers(accounts, vault, selector):
    before = custody_state(accounts, vault)
    amount = 1 + selector % (accounts - 2)
    command = _transfer_command(amount_atoms=amount)
    result = transition_asset_lane_custody_v2(_context(command), before, command)
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    expected = {"alice": accounts - amount - 2, "bob": amount, "treasury": 2}
    expected = {owner: atoms for owner, atoms in expected.items() if atoms}
    assert {r.owner: r.amount_atoms for r in result.post_state.transfer_state.balances} == expected
    assert result.post_state.custody == before.custody
    assert result.post_state.physical_atoms("USD") == accounts + vault


def test_burn_all_spendable_accounts_leaves_vault_supply_then_reissue():
    before = custody_state()
    burn = replace(
        _managed_command(amount_atoms=80),
        command_kind="managed_asset_burn",
        authorization_root=_root("burn:USD"),
    )
    result = transition_asset_lane_custody_v2(_context(burn), before, burn)
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    assert result.post_state.transfer_state.balances == ()
    assert result.post_state.transfer_state.supply_atoms("USD") == 20
    assert result.post_state.custody == before.custody
    issue = _managed_command(amount_atoms=1)
    restored = transition_asset_lane_custody_v2(_context(issue, nonce=2), result.post_state, issue)
    assert isinstance(restored, AssetLaneCustodyAcceptedV2)
    assert restored.post_state.physical_atoms("USD") == 21


def test_dormant_asset_retains_identity_through_issue_burn_reissue():
    initial = custody_state(0, 0)
    state = initial
    for nonce, kind in enumerate(
        ("managed_asset_issue", "managed_asset_burn", "managed_asset_issue"), 1
    ):
        command = _managed_command(kind=kind, amount_atoms=1)
        result = transition_asset_lane_custody_v2(_context(command, nonce=nonce), state, command)
        assert isinstance(result, AssetLaneCustodyAcceptedV2)
        assert tuple(p.asset for p in result.post_state.transfer_state.policies) == ("USD",)
        state = result.post_state
        if nonce == 2:
            assert state.to_canonical() == initial.to_canonical()


def test_custody_is_owned_at_constructor_and_getter_boundaries():
    original = custody_state()
    leaf, registry, policies, custody = (
        original.transfer_state,
        original.origin_registry,
        original.managed_policies,
        original.custody,
    )
    state = AssetLaneCustodyStateV2(leaf, registry, policies, custody)
    root = state.state_root
    object.__setattr__(custody[0], "amount_atoms", 999)
    object.__setattr__(leaf.balances[0], "amount_atoms", 999)
    object.__setattr__(registry.assets[0], "asset", "OTHER")
    assert state.state_root == root
    object.__setattr__(state.custody[0], "amount_atoms", 999)
    assert state.state_root == root
    command = _transfer_command(amount_atoms=10)
    result = transition_asset_lane_custody_v2(_context(command), state, command)
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    post_root = result.post_state.state_root
    object.__setattr__(result.post_state.custody[0], "amount_atoms", 999)
    object.__setattr__(result.effects.asset_conservation[0], "supply_post_atoms", 999)
    assert result.post_state.state_root == post_root
    assert result.effects.asset_conservation[0].supply_post_atoms == 100


@pytest.mark.parametrize("mutation", ("account_domain", "duplicate", "zero", "foreign", "unbacked"))
def test_invalid_custody_cannot_enter_successor_state(mutation):
    state = custody_state()
    row = state.custody[0]
    malformed = {
        "account_domain": (replace(row, custody_domain="accounts"),),
        "duplicate": (replace(row, amount_atoms=10), replace(row, amount_atoms=10)),
        "zero": (replace(row, amount_atoms=0),),
        "foreign": (replace(row, asset="OTHER"),),
        "unbacked": (replace(row, amount_atoms=19),),
    }[mutation]
    with pytest.raises(ValueError):
        AssetLaneCustodyStateV2(
            state.transfer_state, state.origin_registry, state.managed_policies, malformed
        )


def test_maximum_physical_supply_is_accepted_and_extra_issue_rejects():
    state = custody_state(0, MAX_ATOMS_V2)
    command = _managed_command(amount_atoms=1)
    result = transition_asset_lane_custody_v2(_context(command), state, command)
    assert result.code.value == "SUPPLY_OVERFLOW"
    assert result.effects.is_empty
    assert result.pre_state_root == result.post_state_root == state.state_root


def test_every_custody_row_is_preserved_at_the_declared_ceiling():
    state = custody_state(80, 4096)
    rows = tuple(EconomicAmountV2(f"vault-{i:04d}", "USD", "escrow", 1) for i in range(4096))
    state = AssetLaneCustodyStateV2(
        state.transfer_state, state.origin_registry, state.managed_policies, rows
    )
    command = _transfer_command(amount_atoms=10)
    result = transition_asset_lane_custody_v2(_context(command), state, command)
    assert isinstance(result, AssetLaneCustodyAcceptedV2)
    assert result.post_state.custody == rows
    with pytest.raises(ValueError, match="4096"):
        AssetLaneCustodyStateV2(
            state.transfer_state,
            state.origin_registry,
            state.managed_policies,
            (*rows, EconomicAmountV2("vault-last", "USD", "escrow", 1)),
        )
