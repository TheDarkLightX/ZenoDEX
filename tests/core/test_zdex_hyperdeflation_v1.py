from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from typing import TypedDict, cast

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
)
from src.core.zdex_hyperdeflation_v1 import (
    ZDEXAmountBucketV1,
    ZDEXBucketScaleV1,
    ZDEXBurnCapacityV1,
    ZDEXBurnEffectV1,
    ZDEXBurnRejectCodeV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXPrecisionEffectV1,
    ZDEXPrecisionRejectCodeV1,
    ZDEXPrecisionRescaleAcceptedV1,
    ZDEXPrecisionRescaleCommandV1,
    ZDEXPrecisionRescaleRejectedV1,
    ZDEXPurchaseAndBurnAcceptedV1,
    ZDEXPurchaseAndBurnCommandV1,
    ZDEXPurchaseAndBurnRejectedV1,
    ZDEXSupplyStateV1,
    compute_zdex_burn_capacity_v1,
    retained_supply_atoms_v1,
    transition_zdex_precision_rescale_v1,
    transition_zdex_purchase_and_burn_v1,
)


class _ContextKwargs(TypedDict, total=False):
    purchased_atoms: int
    burn_source_bucket_id: str
    source_floor_atoms: int
    epoch_cap_atoms: int
    route_cap_atoms: int
    burn_budget_epoch: int


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy(
    *,
    retained_numerator: int = 9,
    retained_denominator: int = 10,
    maximum_decimals: int = 64,
    maximum_decimal_step: int = 8,
) -> ZDEXHyperdeflationPolicyV1:
    return ZDEXHyperdeflationPolicyV1(
        asset_id=_root(1),
        retained_numerator=retained_numerator,
        retained_denominator=retained_denominator,
        maximum_decimals=maximum_decimals,
        maximum_decimal_step=maximum_decimal_step,
    )


def _state(
    policy: ZDEXHyperdeflationPolicyV1,
    *,
    source_atoms: int,
    holder_atoms: int = 0,
    decimals: int = 8,
    precision_epoch: int = 0,
    burn_budget_epoch: int = 0,
    remaining_epoch_burn_cap_atoms: int | None = None,
) -> ZDEXSupplyStateV1:
    buckets = [ZDEXAmountBucketV1("route:buyburn:source", source_atoms)]
    if holder_atoms:
        buckets.append(ZDEXAmountBucketV1("wallet:alice", holder_atoms))
    live_supply_atoms = source_atoms + holder_atoms
    return ZDEXSupplyStateV1(
        asset_id=policy.asset_id,
        policy_root=policy.policy_root,
        decimals=decimals,
        precision_epoch=precision_epoch,
        live_supply_atoms=live_supply_atoms,
        buckets=tuple(buckets),
        burn_budget_epoch=burn_budget_epoch,
        remaining_epoch_burn_cap_atoms=(
            live_supply_atoms
            if remaining_epoch_burn_cap_atoms is None
            else remaining_epoch_burn_cap_atoms
        ),
    )


def _context(
    policy: ZDEXHyperdeflationPolicyV1,
    *,
    purchased_atoms: int = 1,
    burn_source_bucket_id: str = "route:buyburn:source",
    source_floor_atoms: int = 0,
    epoch_cap_atoms: int = MAX_ATOMS_V1,
    route_cap_atoms: int = MAX_ATOMS_V1,
    burn_budget_epoch: int = 0,
) -> ZDEXBurnRouteContextV1:
    return ZDEXBurnRouteContextV1(
        route_release_id=_root(2),
        policy_root=policy.policy_root,
        purchase_occurrence_root=_root(3),
        burn_source_bucket_id=burn_source_bucket_id,
        purchased_zdex_atoms=purchased_atoms,
        source_reserve_floor_atoms=source_floor_atoms,
        remaining_epoch_burn_cap_atoms=epoch_cap_atoms,
        route_safe_output_cap_atoms=route_cap_atoms,
        burn_budget_epoch=burn_budget_epoch,
    )


def _burn_command(
    state: ZDEXSupplyStateV1,
    purchased_atoms: int,
    *,
    source_bucket_id: str = "route:buyburn:source",
) -> ZDEXPurchaseAndBurnCommandV1:
    return ZDEXPurchaseAndBurnCommandV1(
        expected_pre_state_root=state.state_root,
        expected_precision_epoch=state.precision_epoch,
        expected_purchase_occurrence_root=_root(3),
        source_bucket_id=source_bucket_id,
        purchased_zdex_atoms=purchased_atoms,
    )


def _assert_no_effect_reject(
    result: ZDEXPurchaseAndBurnRejectedV1,
    state: ZDEXSupplyStateV1,
) -> None:
    assert result.pre_state is state
    assert result.post_state is state
    assert result.pre_state.state_root == result.post_state.state_root
    assert result.effects == ()


def test_purchase_and_burn_preserves_positive_supply_and_bucket_conservation() -> None:
    # Arrange: a 90% retained fraction limits this event to 100 of 1,000 atoms.
    policy = _policy()
    state = _state(policy, source_atoms=600, holder_atoms=400)
    context = _context(policy, purchased_atoms=100)

    # Act: the composed route purchases and burns exactly the capacity.
    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        context,
        _burn_command(state, 100),
    )

    # Assert: route-source debit, supply burn, and bucket sum are the same amount.
    assert isinstance(result, ZDEXPurchaseAndBurnAcceptedV1)
    assert result.capacity.retained_supply_atoms == 900
    assert result.capacity.maximum_burn_atoms == 100
    assert result.effect.purchase_occurrence_root == context.purchase_occurrence_root
    assert result.effect.source_debit_atoms == result.effect.authorized_burn_atoms == 100
    assert result.effect.authorized_issue_atoms == 0
    assert result.post_state.live_supply_atoms == 900
    assert result.post_state.bucket_atoms("route:buyburn:source") == 500
    assert sum(row.amount_atoms for row in result.post_state.buckets) == 900


def test_sequential_burns_consume_committed_epoch_capacity() -> None:
    # Arrange: the first purchase consumes three of five epoch-budget atoms.
    policy = _policy(retained_numerator=1, retained_denominator=2)
    state = _state(
        policy,
        source_atoms=10,
        remaining_epoch_burn_cap_atoms=5,
    )
    first_context = _context(policy, purchased_atoms=3, epoch_cap_atoms=5)

    # Act: execute a valid first burn, then present a distinct purchase while
    # reusing the stale route claim that five epoch-budget atoms remain.
    first = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        first_context,
        _burn_command(state, 3),
    )
    assert isinstance(first, ZDEXPurchaseAndBurnAcceptedV1)
    second_context = replace(
        first_context,
        purchase_occurrence_root=_root(4),
    )
    second_command = replace(
        _burn_command(first.post_state, 3),
        expected_purchase_occurrence_root=_root(4),
    )
    second = transition_zdex_purchase_and_burn_v1(
        policy,
        first.post_state,
        second_context,
        second_command,
    )

    # Assert: committed capacity, rather than the stale context, is
    # authoritative for the second transition.
    assert first.post_state.remaining_epoch_burn_cap_atoms == 2
    assert isinstance(second, ZDEXPurchaseAndBurnRejectedV1)
    assert second.code is ZDEXBurnRejectCodeV1.PURCHASE_EXCEEDS_BURN_CAPACITY
    _assert_no_effect_reject(second, first.post_state)


def test_burn_rejects_state_outside_policy_precision_envelope() -> None:
    policy = _policy(maximum_decimals=8)
    state = _state(policy, source_atoms=10, decimals=9)

    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy),
        _burn_command(state, 1),
    )

    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is ZDEXBurnRejectCodeV1.STATE_OUTSIDE_POLICY
    _assert_no_effect_reject(result, state)


def test_burn_rejects_route_context_from_another_budget_epoch() -> None:
    policy = _policy()
    state = _state(policy, source_atoms=10, burn_budget_epoch=7)
    context = _context(policy, burn_budget_epoch=6)

    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        context,
        _burn_command(state, 1),
    )

    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is ZDEXBurnRejectCodeV1.BURN_BUDGET_EPOCH_MISMATCH
    _assert_no_effect_reject(result, state)


def test_burn_and_precision_roots_match_rust_golden_vectors() -> None:
    burn_policy = _policy()
    burn_state = _state(burn_policy, source_atoms=600, holder_atoms=400)
    burn = transition_zdex_purchase_and_burn_v1(
        burn_policy,
        burn_state,
        _context(burn_policy, purchased_atoms=100),
        _burn_command(burn_state, 100),
    )
    assert isinstance(burn, ZDEXPurchaseAndBurnAcceptedV1)
    assert burn_policy.policy_root == (
        "0x12748f215bca2c960007fe74b5de2236129f5c285bbcd9b98c07736839ba46c6"
    )
    assert burn_state.state_root == (
        "0xeee0aa653a5af6aa7dd08c8f0d45d6c9184dabbc3901b60fba465444a4dbc305"
    )
    assert burn.post_state.state_root == (
        "0x687eacda4d4e96e65bcefd01b9665a9417d661148462fd50fd40b974a2097119"
    )

    precision_policy = _policy(
        retained_numerator=1,
        retained_denominator=2,
        maximum_decimals=32,
        maximum_decimal_step=8,
    )
    precision_state = _state(
        precision_policy,
        source_atoms=3,
        holder_atoms=2,
        precision_epoch=7,
    )
    precision = transition_zdex_precision_rescale_v1(
        precision_policy,
        precision_state,
        ZDEXPrecisionRescaleCommandV1(
            precision_state.state_root,
            7,
            8,
        ),
    )
    assert isinstance(precision, ZDEXPrecisionRescaleAcceptedV1)
    assert precision_policy.policy_root == (
        "0x9d8a4006811588648e07ad65b7ba890465781e311e4e005210f2e205971b8c56"
    )
    assert precision_state.state_root == (
        "0xc64e6e924955b5a2e81e33bb66daf9c113d14ae34412916ebd1a5e908655135b"
    )
    assert precision.post_state.state_root == (
        "0xb001fa4fc9f895e0e006f556770c45428d3f553a24fb6a55319d32ce06f80198"
    )


def test_ceil_retention_mutant_cannot_burn_the_floor_rounded_extra_atom() -> None:
    # Arrange: ceil(5/2)=3, while an incorrect floor implementation would retain 2.
    policy = _policy(retained_numerator=1, retained_denominator=2)
    state = _state(policy, source_atoms=5)
    context = _context(policy, purchased_atoms=3)

    # Act: attempt the three-atom burn admitted by the floor mutant.
    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        context,
        _burn_command(state, 3),
    )

    # Assert: the exact ceil policy admits at most two atoms and rejects with no effect.
    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is ZDEXBurnRejectCodeV1.PURCHASE_EXCEEDS_BURN_CAPACITY
    _assert_no_effect_reject(result, state)
    assert retained_supply_atoms_v1(5, policy) == 3


@pytest.mark.parametrize(
    ("context_kwargs", "expected_capacity"),
    [
        ({"source_floor_atoms": 550}, 50),
        ({"epoch_cap_atoms": 40}, 40),
        ({"route_cap_atoms": 30}, 30),
    ],
)
def test_burn_capacity_is_the_minimum_of_independent_route_limits(
    context_kwargs: _ContextKwargs,
    expected_capacity: int,
) -> None:
    policy = _policy()
    state = _state(policy, source_atoms=600, holder_atoms=400)

    capacity = compute_zdex_burn_capacity_v1(
        policy,
        state,
        _context(policy, **context_kwargs),
        source_bucket_id="route:buyburn:source",
    )

    assert capacity is not None
    assert capacity.ratio_headroom_atoms == 100
    assert capacity.maximum_burn_atoms == expected_capacity


@pytest.mark.parametrize(
    ("state_kwargs", "context_kwargs", "expected_code"),
    [
        (
            {"source_atoms": 1},
            {},
            ZDEXBurnRejectCodeV1.PRECISION_RESCALE_REQUIRED,
        ),
        (
            {"source_atoms": 10},
            {"source_floor_atoms": 10},
            ZDEXBurnRejectCodeV1.SOURCE_RESERVE_FLOOR_REACHED,
        ),
        (
            {"source_atoms": 10},
            {"epoch_cap_atoms": 0},
            ZDEXBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED,
        ),
        (
            {"source_atoms": 10},
            {"route_cap_atoms": 0},
            ZDEXBurnRejectCodeV1.ROUTE_OUTPUT_CAP_ZERO,
        ),
    ],
)
def test_exhausted_capacity_has_specific_no_effect_rejection(
    state_kwargs: dict[str, int],
    context_kwargs: _ContextKwargs,
    expected_code: ZDEXBurnRejectCodeV1,
) -> None:
    policy = _policy(retained_numerator=1, retained_denominator=2)
    state = _state(policy, **state_kwargs)

    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy, **context_kwargs),
        _burn_command(state, 1),
    )

    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is expected_code
    _assert_no_effect_reject(result, state)


@pytest.mark.parametrize(
    ("command_mutator", "expected_code"),
    [
        (
            lambda command: replace(command, purchased_zdex_atoms=0),
            ZDEXBurnRejectCodeV1.ZERO_PURCHASE,
        ),
        (
            lambda command: replace(command, expected_pre_state_root=_root(99)),
            ZDEXBurnRejectCodeV1.STALE_STATE,
        ),
        (
            lambda command: replace(command, expected_precision_epoch=1),
            ZDEXBurnRejectCodeV1.PRECISION_EPOCH_MISMATCH,
        ),
        (
            lambda command: replace(command, source_bucket_id="pool:unknown"),
            ZDEXBurnRejectCodeV1.PURCHASE_BINDING_MISMATCH,
        ),
        (
            lambda command: replace(
                command,
                expected_purchase_occurrence_root=_root(99),
            ),
            ZDEXBurnRejectCodeV1.PURCHASE_BINDING_MISMATCH,
        ),
        (
            lambda command: replace(command, purchased_zdex_atoms=2),
            ZDEXBurnRejectCodeV1.PURCHASE_BINDING_MISMATCH,
        ),
    ],
)
def test_burn_rejection_is_exact_noop(
    command_mutator,
    expected_code: ZDEXBurnRejectCodeV1,
) -> None:
    policy = _policy()
    state = _state(policy, source_atoms=600, holder_atoms=400)
    command = command_mutator(_burn_command(state, 1))

    result = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy),
        command,
    )

    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is expected_code
    _assert_no_effect_reject(result, state)


def test_policy_binding_rejects_caller_selected_contraction_ratio() -> None:
    state_policy = _policy(retained_numerator=9, retained_denominator=10)
    caller_policy = _policy(retained_numerator=1, retained_denominator=2)
    state = _state(state_policy, source_atoms=100)

    result = transition_zdex_purchase_and_burn_v1(
        caller_policy,
        state,
        _context(caller_policy),
        _burn_command(state, 1),
    )

    assert isinstance(result, ZDEXPurchaseAndBurnRejectedV1)
    assert result.code is ZDEXBurnRejectCodeV1.POLICY_MISMATCH
    _assert_no_effect_reject(result, state)


def test_exhaustive_small_domain_matches_independent_ceil_oracle_and_stays_positive() -> None:
    for supply_atoms in range(1, 41):
        for denominator in range(2, 10):
            for numerator in range(1, denominator):
                policy = _policy(
                    retained_numerator=numerator,
                    retained_denominator=denominator,
                )
                state = _state(policy, source_atoms=supply_atoms)
                retained_oracle = -(
                    -(numerator * supply_atoms) // denominator
                )
                capacity = compute_zdex_burn_capacity_v1(
                    policy,
                    state,
                    _context(policy),
                    source_bucket_id="route:buyburn:source",
                )
                assert capacity is not None
                assert capacity.retained_supply_atoms == retained_oracle
                assert capacity.maximum_burn_atoms == supply_atoms - retained_oracle

                if capacity.maximum_burn_atoms == 0:
                    continue
                result = transition_zdex_purchase_and_burn_v1(
                    policy,
                    state,
                    _context(
                        policy,
                        purchased_atoms=capacity.maximum_burn_atoms,
                    ),
                    _burn_command(state, capacity.maximum_burn_atoms),
                )
                assert isinstance(result, ZDEXPurchaseAndBurnAcceptedV1)
                assert result.post_state.live_supply_atoms == retained_oracle
                assert result.post_state.live_supply_atoms > 0


def test_retained_supply_intermediate_is_safe_at_u128_u64_boundary() -> None:
    policy = _policy(
        retained_numerator=MAX_U64_V1 - 1,
        retained_denominator=MAX_U64_V1,
        maximum_decimals=MAX_U64_V1,
        maximum_decimal_step=38,
    )

    retained = retained_supply_atoms_v1(MAX_ATOMS_V1, policy)
    state = _state(
        policy,
        source_atoms=MAX_ATOMS_V1,
        decimals=MAX_U64_V1,
        precision_epoch=MAX_U64_V1,
        burn_budget_epoch=MAX_U64_V1,
        remaining_epoch_burn_cap_atoms=MAX_ATOMS_V1,
    )

    assert 1 <= retained <= MAX_ATOMS_V1
    assert retained == -(
        -((MAX_U64_V1 - 1) * MAX_ATOMS_V1) // MAX_U64_V1
    )
    assert policy.policy_root == (
        "0xad1bc096a89e8ba0327640f77f2ae0946db17b4fdb25f99fa2ed217f073c6536"
    )
    assert state.state_root == (
        "0x9083fedb16da97f36e8c097322bfced6519e2dd4419607f1134f9f93cc2054ed"
    )


def test_burn_signed_effect_width_accepts_maximum_and_rejects_next_atom() -> None:
    policy = _policy(retained_numerator=1, retained_denominator=3)
    state = _state(
        policy,
        source_atoms=MAX_ATOMS_V1,
        remaining_epoch_burn_cap_atoms=MAX_ATOMS_V1,
    )

    accepted = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy, purchased_atoms=MAX_DELTA_ATOMS_V1),
        _burn_command(state, MAX_DELTA_ATOMS_V1),
    )
    rejected = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy, purchased_atoms=MAX_DELTA_ATOMS_V1 + 1),
        _burn_command(state, MAX_DELTA_ATOMS_V1 + 1),
    )

    assert isinstance(accepted, ZDEXPurchaseAndBurnAcceptedV1)
    assert accepted.effect.authorized_burn_atoms == MAX_DELTA_ATOMS_V1
    assert isinstance(rejected, ZDEXPurchaseAndBurnRejectedV1)
    assert rejected.code is ZDEXBurnRejectCodeV1.EFFECT_WIDTH_EXCEEDED
    _assert_no_effect_reject(rejected, state)
    with pytest.raises(ValueError, match="signed effect atoms"):
        ZDEXBurnEffectV1(
            purchase_occurrence_root=_root(3),
            source_bucket_id="route:buyburn:source",
            source_debit_atoms=MAX_DELTA_ATOMS_V1 + 1,
            authorized_burn_atoms=MAX_DELTA_ATOMS_V1 + 1,
        )


def test_precision_rescale_preserves_each_normalized_bucket_and_total_exactly() -> None:
    # Arrange: normalized quantities are independently represented as rational numbers.
    policy = _policy(maximum_decimals=32, maximum_decimal_step=8)
    state = _state(
        policy,
        source_atoms=3,
        holder_atoms=2,
        decimals=8,
        precision_epoch=7,
    )
    before_values = {
        row.bucket_id: Fraction(row.amount_atoms, 10**state.decimals)
        for row in state.buckets
    }

    # Act: increase precision by eight decimal places.
    result = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            expected_pre_state_root=state.state_root,
            expected_precision_epoch=state.precision_epoch,
            additional_decimals=8,
        ),
    )

    # Assert: value, ownership ratios, supply sum, and no-issue/no-burn all hold.
    assert isinstance(result, ZDEXPrecisionRescaleAcceptedV1)
    assert result.effect.scale_factor == 10**8
    assert result.post_state.decimals == 16
    assert result.post_state.precision_epoch == 8
    assert result.effect.authorized_issue_atoms == 0
    assert result.effect.authorized_burn_atoms == 0
    assert sum(row.amount_atoms for row in result.post_state.buckets) == result.post_state.live_supply_atoms
    after_values = {
        row.bucket_id: Fraction(row.amount_atoms, 10**result.post_state.decimals)
        for row in result.post_state.buckets
    }
    assert after_values == before_values
    assert Fraction(
        result.post_state.live_supply_atoms,
        10**result.post_state.decimals,
    ) == Fraction(state.live_supply_atoms, 10**state.decimals)


@pytest.mark.parametrize(
    ("command_mutator", "expected_code"),
    [
        (
            lambda command: replace(command, additional_decimals=0),
            ZDEXPrecisionRejectCodeV1.ZERO_DECIMAL_STEP,
        ),
        (
            lambda command: replace(command, additional_decimals=9),
            ZDEXPrecisionRejectCodeV1.DECIMAL_STEP_EXCEEDS_POLICY,
        ),
        (
            lambda command: replace(command, expected_pre_state_root=_root(99)),
            ZDEXPrecisionRejectCodeV1.STALE_STATE,
        ),
        (
            lambda command: replace(command, expected_precision_epoch=1),
            ZDEXPrecisionRejectCodeV1.PRECISION_EPOCH_MISMATCH,
        ),
    ],
)
def test_precision_rejection_is_exact_noop(
    command_mutator,
    expected_code: ZDEXPrecisionRejectCodeV1,
) -> None:
    policy = _policy(maximum_decimals=16, maximum_decimal_step=8)
    state = _state(policy, source_atoms=10)
    command = command_mutator(
        ZDEXPrecisionRescaleCommandV1(
            expected_pre_state_root=state.state_root,
            expected_precision_epoch=state.precision_epoch,
            additional_decimals=1,
        )
    )

    result = transition_zdex_precision_rescale_v1(policy, state, command)

    assert isinstance(result, ZDEXPrecisionRescaleRejectedV1)
    assert result.code is expected_code
    assert result.pre_state is state
    assert result.post_state is state
    assert result.effects == ()


def test_precision_rescale_rejects_u128_overflow_without_effect() -> None:
    policy = _policy(maximum_decimals=16, maximum_decimal_step=8)
    state = _state(policy, source_atoms=MAX_ATOMS_V1)

    result = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            expected_pre_state_root=state.state_root,
            expected_precision_epoch=state.precision_epoch,
            additional_decimals=1,
        ),
    )

    assert isinstance(result, ZDEXPrecisionRescaleRejectedV1)
    assert result.code is ZDEXPrecisionRejectCodeV1.ATOM_OVERFLOW
    assert result.post_state is state
    assert result.effects == ()


def test_precision_rescale_reopens_finite_burn_capacity_at_one_atom() -> None:
    # Arrange: fixed precision has reached the one-atom terminal representation.
    policy = _policy(
        retained_numerator=1,
        retained_denominator=2,
        maximum_decimals=16,
        maximum_decimal_step=8,
    )
    state = _state(policy, source_atoms=1, decimals=8)
    blocked = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy),
        _burn_command(state, 1),
    )
    assert isinstance(blocked, ZDEXPurchaseAndBurnRejectedV1)
    assert blocked.code is ZDEXBurnRejectCodeV1.PRECISION_RESCALE_REQUIRED

    # Act: exactly rescale every live bucket, then burn at the new ratio capacity.
    rescaled = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            expected_pre_state_root=state.state_root,
            expected_precision_epoch=state.precision_epoch,
            additional_decimals=1,
        ),
    )
    assert isinstance(rescaled, ZDEXPrecisionRescaleAcceptedV1)
    burned = transition_zdex_purchase_and_burn_v1(
        policy,
        rescaled.post_state,
        _context(policy, purchased_atoms=5),
        _burn_command(rescaled.post_state, 5),
    )

    # Assert: the finite trace remains positive and conserved at every step.
    assert isinstance(burned, ZDEXPurchaseAndBurnAcceptedV1)
    assert burned.post_state.live_supply_atoms == 5
    assert burned.post_state.bucket_atoms("route:buyburn:source") == 5


def test_fixed_precision_liveness_threshold_is_exact() -> None:
    for denominator in range(2, 20):
        for numerator in range(1, denominator):
            policy = _policy(
                retained_numerator=numerator,
                retained_denominator=denominator,
            )
            threshold = -(-(denominator) // (denominator - numerator))
            for supply_atoms in range(1, threshold + 2):
                state = _state(policy, source_atoms=supply_atoms)
                capacity = compute_zdex_burn_capacity_v1(
                    policy,
                    state,
                    _context(policy),
                    source_bucket_id="route:buyburn:source",
                )
                assert capacity is not None
                assert (capacity.maximum_burn_atoms > 0) is (
                    supply_atoms >= threshold
                )


def test_small_precision_step_can_remain_below_liveness_threshold() -> None:
    policy = _policy(
        retained_numerator=10,
        retained_denominator=11,
        maximum_decimals=9,
        maximum_decimal_step=1,
    )
    state = _state(policy, source_atoms=1, decimals=8)
    rescaled = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            expected_pre_state_root=state.state_root,
            expected_precision_epoch=state.precision_epoch,
            additional_decimals=1,
        ),
    )
    assert isinstance(rescaled, ZDEXPrecisionRescaleAcceptedV1)

    blocked = transition_zdex_purchase_and_burn_v1(
        policy,
        rescaled.post_state,
        _context(policy),
        _burn_command(rescaled.post_state, 1),
    )

    assert isinstance(blocked, ZDEXPurchaseAndBurnRejectedV1)
    assert blocked.code is ZDEXBurnRejectCodeV1.PRECISION_RESCALE_REQUIRED


def test_precision_step_bound_accepts_38_and_rejects_39_decimals() -> None:
    policy = _policy(maximum_decimals=64, maximum_decimal_step=38)
    state = _state(policy, source_atoms=1)

    accepted = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            state.state_root,
            state.precision_epoch,
            38,
        ),
    )
    rejected = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            state.state_root,
            state.precision_epoch,
            39,
        ),
    )

    assert isinstance(accepted, ZDEXPrecisionRescaleAcceptedV1)
    assert accepted.effect.scale_factor == 10**38
    assert isinstance(rejected, ZDEXPrecisionRescaleRejectedV1)
    assert rejected.code is ZDEXPrecisionRejectCodeV1.DECIMAL_STEP_EXCEEDS_POLICY
    assert rejected.post_state is state


def test_precision_overflow_boundary_accepts_floor_and_rejects_next_atom() -> None:
    policy = _policy(maximum_decimals=16, maximum_decimal_step=8)
    largest_safe_supply = MAX_ATOMS_V1 // 10
    safe_state = _state(policy, source_atoms=largest_safe_supply)
    overflow_state = _state(policy, source_atoms=largest_safe_supply + 1)

    safe_result = transition_zdex_precision_rescale_v1(
        policy,
        safe_state,
        ZDEXPrecisionRescaleCommandV1(
            safe_state.state_root,
            safe_state.precision_epoch,
            1,
        ),
    )
    overflow_result = transition_zdex_precision_rescale_v1(
        policy,
        overflow_state,
        ZDEXPrecisionRescaleCommandV1(
            overflow_state.state_root,
            overflow_state.precision_epoch,
            1,
        ),
    )

    assert isinstance(safe_result, ZDEXPrecisionRescaleAcceptedV1)
    assert safe_result.post_state.live_supply_atoms == largest_safe_supply * 10
    assert isinstance(overflow_result, ZDEXPrecisionRescaleRejectedV1)
    assert overflow_result.code is ZDEXPrecisionRejectCodeV1.ATOM_OVERFLOW


def test_precision_epoch_exhaustion_is_typed_no_effect_rejection() -> None:
    policy = _policy(maximum_decimals=16, maximum_decimal_step=8)
    state = _state(policy, source_atoms=1, precision_epoch=MAX_U64_V1)

    result = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(
            state.state_root,
            state.precision_epoch,
            1,
        ),
    )

    assert isinstance(result, ZDEXPrecisionRescaleRejectedV1)
    assert result.code is ZDEXPrecisionRejectCodeV1.EPOCH_COUNTER_EXHAUSTED
    assert result.post_state is state
    assert result.effects == ()


@pytest.mark.parametrize("forgery", ["decimals", "bucket_id"])
def test_burn_accepted_value_rejects_forged_pre_effect_post_binding(
    forgery: str,
) -> None:
    policy = _policy()
    state = _state(policy, source_atoms=600, holder_atoms=400)
    valid = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        _context(policy, purchased_atoms=100),
        _burn_command(state, 100),
    )
    assert isinstance(valid, ZDEXPurchaseAndBurnAcceptedV1)
    if forgery == "decimals":
        forged_post = replace(valid.post_state, decimals=9)
    else:
        forged_post = replace(
            valid.post_state,
            buckets=(
                ZDEXAmountBucketV1("pool:renamed", 500),
                ZDEXAmountBucketV1("wallet:alice", 400),
            ),
        )

    with pytest.raises(ValueError, match="changed decimal|wrong bucket transition"):
        ZDEXPurchaseAndBurnAcceptedV1(
            policy=valid.policy,
            route_context=valid.route_context,
            pre_state=state,
            post_state=forged_post,
            capacity=valid.capacity,
            effect=valid.effect,
        )


def test_precision_accepted_value_rejects_forged_bucket_binding() -> None:
    policy = _policy(maximum_decimals=16, maximum_decimal_step=8)
    state = _state(policy, source_atoms=3, holder_atoms=2)
    forged_effect = ZDEXPrecisionEffectV1(
        scale_factor=10,
        supply_before_atoms=5,
        supply_after_atoms=50,
        bucket_scales=(
            ZDEXBucketScaleV1("pool:other", 3, 30),
            ZDEXBucketScaleV1("wallet:alice", 2, 20),
        ),
        burn_budget_remaining_before_atoms=5,
        burn_budget_remaining_after_atoms=50,
    )
    forged_post = replace(
        state,
        decimals=9,
        precision_epoch=1,
        live_supply_atoms=50,
        remaining_epoch_burn_cap_atoms=50,
        buckets=(
            ZDEXAmountBucketV1("pool:other", 30),
            ZDEXAmountBucketV1("wallet:alice", 20),
        ),
    )

    with pytest.raises(ValueError, match="not bound to every pre-state bucket"):
        ZDEXPrecisionRescaleAcceptedV1(
            policy=policy,
            pre_state=state,
            post_state=forged_post,
            effect=forged_effect,
        )


def test_public_accepted_value_rejects_forged_nonzero_issuance() -> None:
    with pytest.raises(ValueError, match="cannot authorize issuance"):
        ZDEXBurnEffectV1(
            purchase_occurrence_root=_root(3),
            source_bucket_id="route:buyburn:source",
            source_debit_atoms=1,
            authorized_burn_atoms=1,
            authorized_issue_atoms=1,
        )

    with pytest.raises(ValueError, match="minimum headroom"):
        ZDEXBurnCapacityV1(
            retained_supply_atoms=1,
            ratio_headroom_atoms=1,
            source_headroom_atoms=1,
            epoch_headroom_atoms=1,
            route_headroom_atoms=1,
            maximum_burn_atoms=2,
        )


def test_accepted_burn_recomputes_route_binding_and_capacity() -> None:
    policy = _policy()
    state = _state(policy, source_atoms=600, holder_atoms=400)
    context = _context(policy, purchased_atoms=100)
    valid = transition_zdex_purchase_and_burn_v1(
        policy,
        state,
        context,
        _burn_command(state, 100),
    )
    assert isinstance(valid, ZDEXPurchaseAndBurnAcceptedV1)

    with pytest.raises(ValueError, match="route binding is inconsistent"):
        ZDEXPurchaseAndBurnAcceptedV1(
            policy=policy,
            route_context=replace(context, purchase_occurrence_root=_root(99)),
            pre_state=state,
            post_state=valid.post_state,
            capacity=valid.capacity,
            effect=valid.effect,
        )

    forged_capacity = replace(
        valid.capacity,
        retained_supply_atoms=400,
        ratio_headroom_atoms=600,
        maximum_burn_atoms=600,
    )
    with pytest.raises(ValueError, match="capacity was not recomputed exactly"):
        ZDEXPurchaseAndBurnAcceptedV1(
            policy=policy,
            route_context=context,
            pre_state=state,
            post_state=valid.post_state,
            capacity=forged_capacity,
            effect=valid.effect,
        )


def test_malformed_bool_amounts_fail_before_transition() -> None:
    policy = _policy()

    with pytest.raises(ValueError, match="non-negative integer"):
        ZDEXAmountBucketV1("route:buyburn:source", True)
    with pytest.raises(ValueError, match="non-negative integer"):
        ZDEXPurchaseAndBurnCommandV1(
            _root(3),
            0,
            _root(4),
            "route:buyburn:source",
            True,
        )
    with pytest.raises(ValueError, match="non-negative integer"):
        ZDEXPrecisionRescaleCommandV1(_root(3), 0, True)
    with pytest.raises(ValueError, match="non-negative integer"):
        replace(policy, retained_numerator=True)


def test_state_rejects_noncanonical_or_incomplete_bucket_projection() -> None:
    policy = _policy()

    with pytest.raises(ValueError, match="uniquely ordered"):
        ZDEXSupplyStateV1(
            policy.asset_id,
            policy.policy_root,
            8,
            0,
            3,
            (
                ZDEXAmountBucketV1("wallet:z", 1),
                ZDEXAmountBucketV1("pool:a", 2),
            ),
        )

    too_many_buckets = tuple(
        ZDEXAmountBucketV1(f"wallet:{index:04d}", 1)
        for index in range(1025)
    )
    with pytest.raises(ValueError, match="projection exceeds"):
        ZDEXSupplyStateV1(
            policy.asset_id,
            policy.policy_root,
            8,
            0,
            len(too_many_buckets),
            too_many_buckets,
        )
    with pytest.raises(ValueError, match="bucket sum"):
        ZDEXSupplyStateV1(
            policy.asset_id,
            policy.policy_root,
            8,
            0,
            4,
            (ZDEXAmountBucketV1("pool:a", 3),),
        )


def test_u64_policy_and_epoch_fields_reject_out_of_range_values() -> None:
    policy = _policy()
    state = _state(policy, source_atoms=5)

    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(policy, retained_denominator=MAX_U64_V1 + 1)
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(state, precision_epoch=MAX_U64_V1 + 1)
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        ZDEXPrecisionRescaleCommandV1(state.state_root, MAX_U64_V1 + 1, 1)


def test_result_and_effect_wrappers_require_exact_owned_types() -> None:
    policy = _policy(maximum_decimals=16)
    state = _state(policy, source_atoms=5)

    with pytest.raises(TypeError, match="exact supply states"):
        ZDEXPurchaseAndBurnRejectedV1(
            ZDEXBurnRejectCodeV1.ZERO_PURCHASE,
            cast(ZDEXSupplyStateV1, object()),
            cast(ZDEXSupplyStateV1, object()),
        )
    with pytest.raises(TypeError, match="bucket scales are not closed"):
        ZDEXPrecisionEffectV1(
            scale_factor=10,
            supply_before_atoms=5,
            supply_after_atoms=50,
            bucket_scales=cast(tuple[ZDEXBucketScaleV1, ...], (object(),)),
        )
    with pytest.raises(TypeError, match="exact effect"):
        ZDEXPrecisionRescaleAcceptedV1(
            policy=policy,
            pre_state=state,
            post_state=state,
            effect=cast(ZDEXPrecisionEffectV1, object()),
        )


def test_forged_accepted_rescale_rejects_huge_decimal_exponent_before_power() -> None:
    policy = _policy(maximum_decimals=MAX_U64_V1, maximum_decimal_step=38)
    state = _state(policy, source_atoms=5)
    valid = transition_zdex_precision_rescale_v1(
        policy,
        state,
        ZDEXPrecisionRescaleCommandV1(state.state_root, 0, 1),
    )
    assert isinstance(valid, ZDEXPrecisionRescaleAcceptedV1)
    forged_post = replace(valid.post_state, decimals=MAX_U64_V1)

    with pytest.raises(ValueError, match="decimal step exceeds the global bound"):
        ZDEXPrecisionRescaleAcceptedV1(policy, state, forged_post, valid.effect)
