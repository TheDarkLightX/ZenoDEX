"""Required custody states must reach the successor's actual V2 transitions."""

from dataclasses import replace

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneStateV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_settlement_types_v2 import MAX_ATOMS_V2, AssetSupplyV2, EconomicAmountV2
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
