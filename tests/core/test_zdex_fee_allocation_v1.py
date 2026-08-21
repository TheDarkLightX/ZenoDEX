from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    EconomicEffectKindV1,
)
from src.core.zdex_fee_allocation_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeAllocationRejectedV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
    transition_zdex_fee_allocation_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy(*bps: int) -> ZDEXFeeAllocationPolicyV1:
    return ZDEXFeeAllocationPolicyV1(
        tuple(
            ZDEXFeeShareV1(destination, share)
            for destination, share in zip(
                ZDEX_FEE_DESTINATIONS_V1,
                bps,
                strict=True,
            )
        )
    )


def _state(
    policy: ZDEXFeeAllocationPolicyV1,
    *,
    ingress_atoms: int = 50_000,
    reserve_atoms: int = 700,
    destination_atoms: tuple[int, ...] = (10, 20, 30, 40, 50, 60),
    owned_atoms: int = 1_000_000,
) -> ZDEXFeeStateV1:
    return ZDEXFeeStateV1(
        fee_asset_id=_root(40),
        policy_root=policy.policy_root,
        fee_ingress_atoms=ingress_atoms,
        unallocated_reserve_atoms=reserve_atoms,
        destination_balances=tuple(
            ZDEXFeeDestinationAmountV1(destination, amount)
            for destination, amount in zip(
                ZDEX_FEE_DESTINATIONS_V1,
                destination_atoms,
                strict=True,
            )
        ),
        owned_and_custodied_atoms=owned_atoms,
        supply_atoms=owned_atoms,
    )


def _context(policy: ZDEXFeeAllocationPolicyV1) -> ZDEXFeeAllocationContextV1:
    return ZDEXFeeAllocationContextV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=11,
        allocation_route_release_id=_root(3),
        authorized_buyback_route_release_id=_root(4),
        tokenomics_module_release_id=_root(5),
        command_occurrence_id=_root(6),
        policy_root=policy.policy_root,
    )


def _accept(
    fee_atoms: int,
    *,
    policy: ZDEXFeeAllocationPolicyV1 | None = None,
    state: ZDEXFeeStateV1 | None = None,
) -> ZDEXFeeAllocationAcceptedV1:
    active_policy = policy or candidate_zdex_fee_allocation_policy_v1()
    pre_state = state or _state(active_policy)
    result = transition_zdex_fee_allocation_v1(
        _context(active_policy),
        pre_state,
        active_policy,
        ZDEXFeeAllocationCommandV1(fee_atoms),
    )
    assert type(result) is ZDEXFeeAllocationAcceptedV1
    return result


def test_candidate_policy_assigns_exact_budget_and_carries_all_residue() -> None:
    # Arrange
    policy = candidate_zdex_fee_allocation_policy_v1()
    pre_state = _state(policy)

    # Act
    accepted = _accept(10_003, policy=policy, state=pre_state)

    # Assert
    assert tuple(row.allocation_atoms for row in accepted.occurrence.allocations) == (
        2_000,
        0,
        3_000,
        1_000,
        1_000,
        500,
    )
    assert accepted.occurrence.buyback_quote_atoms == 2_000
    assert accepted.occurrence.carried_residue_atoms == 2_503
    assert accepted.post_state.fee_ingress_atoms == pre_state.fee_ingress_atoms - 10_003
    assert accepted.post_state.unallocated_reserve_atoms == 3_203
    assert tuple(
        row.allocation_atoms for row in accepted.post_state.destination_balances
    ) == (2_010, 20, 3_030, 1_040, 1_050, 560)

    fee_row = accepted.effects.fee_conservation[0]
    assert fee_row.fee_charged_atoms == 10_003
    assert fee_row.current_allocations_atoms == 7_500
    assert fee_row.carried_residue_atoms == 2_503
    assert sum(row.delta_atoms for row in accepted.effects.rows) == 0
    assert accepted.effects.external_outbox_enqueue == ()
    assert accepted.effects.occurrence_consumptions == (_root(6),)


def test_effect_projection_has_one_source_one_reserve_and_nonzero_allocations() -> None:
    # Arrange / Act
    accepted = _accept(10_003)

    # Assert
    kinds = tuple(row.kind for row in accepted.effects.rows)
    assert kinds.count(EconomicEffectKindV1.CUSTODY) == 1
    assert kinds.count(EconomicEffectKindV1.FEE_ALLOCATION) == 5
    assert kinds.count(EconomicEffectKindV1.RESERVE) == 1
    source = next(
        row for row in accepted.effects.rows if row.kind is EconomicEffectKindV1.CUSTODY
    )
    residue = next(
        row for row in accepted.effects.rows if row.kind is EconomicEffectKindV1.RESERVE
    )
    assert source.delta_atoms == -10_003
    assert residue.delta_atoms == 2_503
    assert accepted.effects.asset_conservation[0].owned_and_custodied_pre_atoms == 1_000_000
    assert accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms == 1_000_000
    assert accepted.effects.lane_writes == ()
    assert accepted.occurrence.effect_plan_root == accepted.effects.effect_plan_root


@pytest.mark.parametrize(
    ("fee_atoms", "expected_residue"),
    ((1, 1), (9_999, 2_504), (10_000, 2_500), (10_001, 2_501)),
)
def test_rounding_bva_reconciles_each_fee_atom(
    fee_atoms: int,
    expected_residue: int,
) -> None:
    # Arrange / Act
    accepted = _accept(fee_atoms)

    # Assert
    allocated = sum(row.allocation_atoms for row in accepted.occurrence.allocations)
    assert allocated + accepted.occurrence.carried_residue_atoms == fee_atoms
    assert accepted.occurrence.carried_residue_atoms == expected_residue


def test_complete_policy_can_allocate_every_atom_without_residue() -> None:
    # Arrange
    policy = _policy(10_000, 0, 0, 0, 0, 0)

    # Act
    accepted = _accept(37, policy=policy)

    # Assert
    assert accepted.occurrence.buyback_quote_atoms == 37
    assert accepted.occurrence.carried_residue_atoms == 0
    assert not any(
        row.kind is EconomicEffectKindV1.RESERVE for row in accepted.effects.rows
    )


def test_governed_host_share_targets_only_the_aggregate_qualified_pool() -> None:
    # Arrange
    policy = _policy(0, 10_000, 0, 0, 0, 0)

    # Act
    accepted = _accept(37, policy=policy)

    # Assert
    host_effect = next(
        row
        for row in accepted.effects.rows
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
    )
    assert host_effect.principal == "protocol:fee-qualified-host-pool"
    assert host_effect.delta_atoms == 37
    assert accepted.occurrence.allocations[1].allocation_atoms == 37


@pytest.mark.parametrize(
    "policy",
    (
        _policy(2_000, 0, 3_000, 1_000, 1_000, 500),
        _policy(10_000, 0, 0, 0, 0, 0),
        _policy(1_667, 1_667, 1_667, 1_667, 1_666, 1_666),
        _policy(0, 0, 0, 0, 0, 0),
    ),
)
def test_small_domain_property_conserves_every_fee_atom(
    policy: ZDEXFeeAllocationPolicyV1,
) -> None:
    # Arrange
    state = _state(policy, ingress_atoms=200)
    selected_pre = state.selected_balance_atoms

    # Act / Assert
    for fee_atoms in range(1, 201):
        accepted = _accept(fee_atoms, policy=policy, state=state)
        allocations = sum(
            row.allocation_atoms for row in accepted.occurrence.allocations
        )
        assert tuple(
            row.allocation_atoms for row in accepted.occurrence.allocations
        ) == tuple(
            fee_atoms * share.share_bps // 10_000 for share in policy.shares
        )
        assert allocations + accepted.occurrence.carried_residue_atoms == fee_atoms
        assert accepted.post_state.selected_balance_atoms == selected_pre


@pytest.mark.parametrize(
    ("mutate_context", "mutate_state", "fee_atoms", "expected"),
    (
        (lambda value: value, lambda value: value, 0, ZDEXFeeAllocationRejectCodeV1.ZERO_FEE),
        (
            lambda value: replace(value, policy_root=_root(99)),
            lambda value: value,
            1,
            ZDEXFeeAllocationRejectCodeV1.POLICY_MISMATCH,
        ),
        (
            lambda value: value,
            lambda value: replace(value, fee_ingress_atoms=3),
            4,
            ZDEXFeeAllocationRejectCodeV1.INSUFFICIENT_FEE_INGRESS,
        ),
        (
            lambda value: value,
            lambda value: value,
            MAX_DELTA_ATOMS_V1 + 1,
            ZDEXFeeAllocationRejectCodeV1.EFFECT_WIDTH_EXCEEDED,
        ),
    ),
)
def test_domain_rejection_is_exact_noop(
    mutate_context: object,
    mutate_state: object,
    fee_atoms: int,
    expected: ZDEXFeeAllocationRejectCodeV1,
) -> None:
    # Arrange
    policy = candidate_zdex_fee_allocation_policy_v1()
    state = mutate_state(_state(policy))  # type: ignore[operator]
    context = mutate_context(_context(policy))  # type: ignore[operator]

    # Act
    result = transition_zdex_fee_allocation_v1(
        context,
        state,
        policy,
        ZDEXFeeAllocationCommandV1(fee_atoms),
    )

    # Assert
    assert result == ZDEXFeeAllocationRejectedV1(expected, state, state)
    assert result.effects.is_empty


def test_maximum_valid_destination_neighbor_remains_representable() -> None:
    # Arrange
    policy = _policy(10_000, 0, 0, 0, 0, 0)
    state = _state(
        policy,
        ingress_atoms=1,
        reserve_atoms=0,
        destination_atoms=(MAX_ATOMS_V1 - 1, 0, 0, 0, 0, 0),
        owned_atoms=MAX_ATOMS_V1,
    )

    # Act
    result = transition_zdex_fee_allocation_v1(
        _context(policy),
        state,
        policy,
        ZDEXFeeAllocationCommandV1(1),
    )

    # Assert
    assert type(result) is ZDEXFeeAllocationAcceptedV1
    assert result.post_state.destination_balances[0].allocation_atoms == MAX_ATOMS_V1


def test_occurrence_root_is_deterministic_and_binds_authorized_route() -> None:
    # Arrange / Act
    first = _accept(10_003)
    second = _accept(10_003)
    changed_context = replace(
        _context(candidate_zdex_fee_allocation_policy_v1()),
        authorized_buyback_route_release_id=_root(77),
    )
    changed = transition_zdex_fee_allocation_v1(
        changed_context,
        _state(candidate_zdex_fee_allocation_policy_v1()),
        candidate_zdex_fee_allocation_policy_v1(),
        ZDEXFeeAllocationCommandV1(10_003),
    )

    # Assert
    assert type(changed) is ZDEXFeeAllocationAcceptedV1
    assert first.occurrence.occurrence_root == second.occurrence.occurrence_root
    assert first.occurrence.occurrence_root != changed.occurrence.occurrence_root
    assert (
        first.occurrence.authorized_buyback_route_release_id
        == _context(candidate_zdex_fee_allocation_policy_v1()).authorized_buyback_route_release_id
    )


def test_accepted_wrapper_rejects_disconnected_commitments() -> None:
    # Arrange
    accepted = _accept(10_003)
    disconnected = replace(accepted.occurrence, effect_plan_root=_root(999))

    # Act / Assert
    with pytest.raises(ValueError, match="commitments are disconnected"):
        replace(accepted, occurrence=disconnected)


def test_python_rust_golden_commitments_match() -> None:
    # Arrange / Act
    accepted = _accept(10_003)

    # Assert
    assert accepted.pre_state.policy_root == (
        "0xd810507e5d15fd874a2e75b6f32b71b47174a799b8015301700e4554614032c2"
    )
    assert accepted.pre_state.state_root == (
        "0x0a8970da266b0587f8b5f8e20cb410d95d947b6661ff01eb626430cb0406fffe"
    )
    assert accepted.post_state.state_root == (
        "0xd0769fc96bd93c73b730d272ef2b7d3dd141756409177fd02db0bb425d2d4b4d"
    )
    assert accepted.effects.effect_plan_root == (
        "0xc6ac94bfc7166ae63f006186f856533d19def998eeb924171576c04f177fefaf"
    )
    assert accepted.occurrence.occurrence_root == (
        "0xc00e0d5f4f83c82a18ba0b552aa0129d497be0806b2f833541b937fae16fac4e"
    )


def test_policy_requires_exact_closed_destination_order() -> None:
    # Arrange
    shares = list(candidate_zdex_fee_allocation_policy_v1().shares)

    # Act / Assert
    with pytest.raises(ValueError, match="closed canonical destination order"):
        ZDEXFeeAllocationPolicyV1(tuple(reversed(shares)))
    with pytest.raises(ValueError, match="closed canonical destination order"):
        ZDEXFeeAllocationPolicyV1(tuple(shares[:-1]))
    with pytest.raises(ValueError, match="exceed 10000"):
        _policy(10_000, 1, 0, 0, 0, 0)


@pytest.mark.parametrize("hostile", (True, "1", 1.0, None))
def test_numeric_fields_reject_hostile_non_integer_values(hostile: object) -> None:
    # Arrange / Act / Assert
    with pytest.raises((TypeError, ValueError)):
        ZDEXFeeShareV1(ZDEXFeeDestinationV1.BUYBACK, hostile)  # type: ignore[arg-type]
    with pytest.raises((TypeError, ValueError)):
        ZDEXFeeAllocationCommandV1(hostile)  # type: ignore[arg-type]
