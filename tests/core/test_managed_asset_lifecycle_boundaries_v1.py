from __future__ import annotations

import pytest

from src.core.global_settlement_types_v1 import (
    MIN_DELTA_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
)
from src.core.managed_asset_lifecycle_module_v1 import (
    transition_managed_asset_lifecycle_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetClassV1,
    ManagedAssetLifecycleAcceptedV1,
    ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1,
    ManagedAssetLifecyclePolicyV1,
    ManagedAssetLifecycleRejectCodeV1,
    ManagedAssetLifecycleRejectedV1,
    ManagedAssetLifecycleStateV1,
)

I128_MIN_MAGNITUDE = -MIN_DELTA_ATOMS_V1
I128_MAX = I128_MIN_MAGNITUDE - 1


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy() -> ManagedAssetLifecyclePolicyV1:
    return ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject="issuer",
        issue_policy_root=_root(5),
        burn_policy_root=_root(6),
        enabled=True,
    )


def _state(*, account_atoms: int, supply_atoms: int) -> ManagedAssetLifecycleStateV1:
    balances = (
        (EconomicAmountV1("alice", "USD", "accounts", account_atoms),)
        if account_atoms
        else ()
    )
    return ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=(_policy(),),
        balances=balances,
        supplies=(AssetSupplyV1("USD", supply_atoms),),
    )


def _context(*, issue: bool) -> ManagedAssetLifecycleContextV1:
    return ManagedAssetLifecycleContextV1(
        chain_id="zeno-asset-boundary",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id="issuer" if issue else "alice",
        grant_root=_root(5 if issue else 6),
    )


def _command(*, issue: bool, amount_atoms: int) -> ManagedAssetLifecycleCommandV1:
    return ManagedAssetLifecycleCommandV1(
        command_kind=(
            MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
            if issue
            else MANAGED_ASSET_BURN_COMMAND_KIND_V1
        ),
        asset="USD",
        account_owner="alice",
        amount_atoms=amount_atoms,
    )


def test_full_burn_accepts_exact_i128_min_effect_and_removes_zero_rows() -> None:
    # Arrange
    pre_state = _state(
        account_atoms=I128_MIN_MAGNITUDE,
        supply_atoms=I128_MIN_MAGNITUDE,
    )

    # Act
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=False),
        pre_state,
        _command(issue=False, amount_atoms=I128_MIN_MAGNITUDE),
    )

    # Assert
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    assert result.post_state.balances == ()
    assert result.post_state.supply_atoms("USD") == 0
    assert {(row.kind, row.delta_atoms) for row in result.effects.rows} == {
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, MIN_DELTA_ATOMS_V1),
        (EconomicEffectKindV1.BURN, MIN_DELTA_ATOMS_V1),
    }


@pytest.mark.parametrize("issue", (True, False))
def test_issue_and_burn_accept_exact_i128_max_effect(issue: bool) -> None:
    # Arrange
    pre_atoms = 0 if issue else I128_MAX

    # Act
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=issue),
        _state(account_atoms=pre_atoms, supply_atoms=pre_atoms),
        _command(issue=issue, amount_atoms=I128_MAX),
    )

    # Assert
    assert isinstance(result, ManagedAssetLifecycleAcceptedV1)
    expected = I128_MAX if issue else 0
    assert result.post_state.balance_atoms("alice", "USD") == expected
    assert result.post_state.supply_atoms("USD") == expected


@pytest.mark.parametrize(
    ("issue", "amount_atoms"),
    ((True, I128_MIN_MAGNITUDE), (False, I128_MIN_MAGNITUDE + 1)),
)
def test_directional_effect_width_rejects_first_invalid_neighbor_as_noop(
    issue: bool,
    amount_atoms: int,
) -> None:
    # Arrange
    pre_state = _state(account_atoms=I128_MIN_MAGNITUDE + 1, supply_atoms=I128_MIN_MAGNITUDE + 1)

    # Act
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=issue),
        pre_state,
        _command(issue=issue, amount_atoms=amount_atoms),
    )

    # Assert
    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert result.code is ManagedAssetLifecycleRejectCodeV1.EFFECT_DELTA_OVERFLOW
    assert result.pre_state_root == result.post_state_root == pre_state.state_root
    assert result.effects.is_empty


def test_state_allows_supply_atoms_held_in_other_accounting_locations() -> None:
    state = _state(account_atoms=10, supply_atoms=15)

    assert state.balance_atoms("alice", "USD") == 10
    assert state.supply_atoms("USD") == 15


def test_burn_rejects_when_selected_account_is_short_even_if_supply_is_sufficient() -> None:
    # Arrange
    pre_state = _state(account_atoms=5, supply_atoms=10)

    # Act
    result = transition_managed_asset_lifecycle_v1(
        _context(issue=False),
        pre_state,
        _command(issue=False, amount_atoms=6),
    )

    # Assert
    assert isinstance(result, ManagedAssetLifecycleRejectedV1)
    assert result.code is ManagedAssetLifecycleRejectCodeV1.INSUFFICIENT_BALANCE
    assert result.pre_state_root == result.post_state_root == pre_state.state_root
    assert result.effects.is_empty


def test_base_transition_revalidates_retained_command_values() -> None:
    # Arrange
    command = _command(issue=True, amount_atoms=1)
    object.__setattr__(command, "amount_atoms", True)

    # Act / Assert
    with pytest.raises(ValueError, match="managed asset command amount"):
        transition_managed_asset_lifecycle_v1(
            _context(issue=True),
            _state(account_atoms=0, supply_atoms=0),
            command,
        )


def test_base_transition_revalidates_nested_retained_policy_values() -> None:
    # Arrange
    pre_state = _state(account_atoms=0, supply_atoms=0)
    object.__setattr__(pre_state.policies[0], "enabled", 1)

    # Act / Assert
    with pytest.raises(TypeError, match="managed asset lifecycle policy enabled"):
        transition_managed_asset_lifecycle_v1(
            _context(issue=True),
            pre_state,
            _command(issue=True, amount_atoms=1),
        )


def test_base_transition_rejects_substituted_policy_container_before_iteration() -> None:
    # Arrange
    class ExplodingIterable:
        def __iter__(self) -> object:
            raise AssertionError("hostile retained container must not execute")

    pre_state = _state(account_atoms=0, supply_atoms=0)
    object.__setattr__(pre_state, "policies", ExplodingIterable())

    # Act / Assert
    with pytest.raises(TypeError, match="policies must be an exact tuple"):
        transition_managed_asset_lifecycle_v1(
            _context(issue=True),
            pre_state,
            _command(issue=True, amount_atoms=1),
        )
