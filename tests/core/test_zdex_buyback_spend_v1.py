from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import MAX_DELTA_ATOMS_V1
from src.core.zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendAcceptedV1,
    ZDEXBuybackSpendContextV1,
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
    ZDEXBuybackSpendStateV1,
    transition_zdex_buyback_spend_v1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _fixture(
    *,
    reserve: int = 80,
    fee_atoms: int = 125,
    cap: int = 100,
    safe_limit: int = 70,
    minimum: int = 10,
    interval: int = 5,
    last_height: int | None = None,
    height: int = 20,
) -> tuple[object, ...]:
    quote = _root(1)
    route = _root(3)
    occurrence = _root(4)
    fee_policy = candidate_zdex_fee_allocation_policy_v1()
    spend_policy = ZDEXBuybackSpendPolicyV1(quote, minimum, cap, interval)
    cadence = ZDEXBuybackSpendStateV1(quote, spend_policy.policy_root, last_height)
    balances = tuple(
        ZDEXFeeDestinationAmountV1(
            destination,
            reserve if destination is ZDEXFeeDestinationV1.BUYBACK else 0,
        )
        for destination in ZDEX_FEE_DESTINATIONS_V1
    )
    fee_state = ZDEXFeeStateV1(
        quote,
        fee_policy.policy_root,
        fee_atoms,
        0,
        balances,
        10_000,
        10_000,
    )
    fee_context = ZDEXFeeAllocationContextV1(
        "zenodex-shadow",
        _root(2),
        _root(5),
        11,
        route,
        route,
        _root(6),
        occurrence,
        fee_policy.policy_root,
    )
    context = ZDEXBuybackSpendContextV1(
        _root(5),
        route,
        occurrence,
        fee_state.state_root,
        cadence.state_root,
        _root(7),
        quote,
        height,
        safe_limit,
    )
    return (
        spend_policy,
        cadence,
        fee_policy,
        fee_state,
        fee_context,
        ZDEXFeeAllocationCommandV1(fee_atoms),
        context,
    )


def _run(values: tuple[object, ...]) -> object:
    return transition_zdex_buyback_spend_v1(*values)  # type: ignore[arg-type]


def _replace_context_root(
    context: ZDEXBuybackSpendContextV1,
    field: str,
) -> ZDEXBuybackSpendContextV1:
    if field == "profile_root":
        return replace(context, profile_root=_root(99))
    if field == "route_release_id":
        return replace(context, route_release_id=_root(99))
    if field == "command_occurrence_id":
        return replace(context, command_occurrence_id=_root(99))
    if field == "expected_fee_pre_state_root":
        return replace(context, expected_fee_pre_state_root=_root(99))
    if field == "expected_cadence_pre_state_root":
        return replace(context, expected_cadence_pre_state_root=_root(99))
    raise AssertionError(f"unsupported test field: {field}")


def _assert_noop(
    result: ZDEXBuybackSpendRejectedV1,
    values: tuple[object, ...],
    code: ZDEXBuybackSpendRejectCodeV1,
) -> None:
    assert result.code is code
    assert result.cadence_pre_state is values[1]
    assert result.cadence_post_state is values[1]
    assert result.fee_pre_state is values[3]
    assert result.fee_post_state is values[3]
    assert result.effects.is_empty


@pytest.mark.parametrize(
    ("reserve", "fee", "cap", "limit", "expected"),
    ((80, 125, 100, 70, 70), (30, 25, 100, 70, 35), (80, 125, 40, 70, 40)),
)
def test_spend_is_minimum_of_canonical_reserve_allocation_cap_and_limit(
    reserve: int, fee: int, cap: int, limit: int, expected: int
) -> None:
    values = _fixture(reserve=reserve, fee_atoms=fee, cap=cap, safe_limit=limit)

    result = _run(values)

    assert isinstance(result, ZDEXBuybackSpendAcceptedV1)
    assert result.intent.buyback_allocation_atoms == fee * 2_000 // 10_000
    assert result.intent.quote_spend_atoms == expected
    assert result.fee_post_state.destination_balances[0].allocation_atoms + expected == (
        reserve + result.intent.buyback_allocation_atoms
    )


def test_same_occurrence_bindings_reject_substitution_without_effect() -> None:
    values = _fixture()
    for field in ("profile_root", "route_release_id", "command_occurrence_id"):
        changed = list(values)
        context = values[6]
        assert isinstance(context, ZDEXBuybackSpendContextV1)
        changed[6] = _replace_context_root(context, field)

        result = _run(tuple(changed))

        assert isinstance(result, ZDEXBuybackSpendRejectedV1)
        _assert_noop(result, tuple(changed), ZDEXBuybackSpendRejectCodeV1.SAME_OCCURRENCE_MISMATCH)


def test_stale_fee_or_cadence_root_rejects_without_effect() -> None:
    for field in ("expected_fee_pre_state_root", "expected_cadence_pre_state_root"):
        values = list(_fixture())
        context = values[6]
        assert isinstance(context, ZDEXBuybackSpendContextV1)
        values[6] = _replace_context_root(context, field)

        result = _run(tuple(values))

        assert isinstance(result, ZDEXBuybackSpendRejectedV1)
        _assert_noop(result, tuple(values), ZDEXBuybackSpendRejectCodeV1.STALE_STATE)


def test_cadence_boundary_and_regression() -> None:
    before = _fixture(last_height=20, height=24)
    boundary = _fixture(last_height=20, height=25)
    regressed = _fixture(last_height=20, height=19)

    low = _run(before)
    exact = _run(boundary)
    back = _run(regressed)

    assert isinstance(low, ZDEXBuybackSpendRejectedV1)
    _assert_noop(low, before, ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED)
    assert isinstance(exact, ZDEXBuybackSpendAcceptedV1)
    assert isinstance(back, ZDEXBuybackSpendRejectedV1)
    _assert_noop(back, regressed, ZDEXBuybackSpendRejectCodeV1.HEIGHT_REGRESSION)


def test_fee_allocation_is_recomputed_and_rejection_is_preserved() -> None:
    values = list(_fixture())
    values[5] = ZDEXFeeAllocationCommandV1(126)

    result = _run(tuple(values))

    assert isinstance(result, ZDEXBuybackSpendRejectedV1)
    _assert_noop(result, tuple(values), ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED)
    assert result.fee_code is not None


@pytest.mark.parametrize(
    ("limit", "minimum", "code"),
    (
        (0, 10, ZDEXBuybackSpendRejectCodeV1.ROUTE_SAFE_LIMIT_ZERO),
        (9, 10, ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM),
    ),
)
def test_safe_limit_boundaries_reject_without_effect(
    limit: int, minimum: int, code: ZDEXBuybackSpendRejectCodeV1
) -> None:
    values = _fixture(safe_limit=limit, minimum=minimum)

    result = _run(values)

    assert isinstance(result, ZDEXBuybackSpendRejectedV1)
    _assert_noop(result, values, code)


def test_intent_binds_policy_and_both_authoritative_pre_states() -> None:
    accepted = _run(_fixture())
    assert isinstance(accepted, ZDEXBuybackSpendAcceptedV1)

    assert accepted.intent.spend_policy_root == accepted.policy.policy_root
    assert accepted.intent.cadence_pre_state_root == accepted.cadence_pre_state.state_root
    assert accepted.intent.fee_pre_state_root == accepted.fee_allocation.pre_state.state_root
    assert accepted.intent.fee_allocated_state_root == accepted.fee_allocation.post_state.state_root


def test_forged_acceptance_with_foreign_intent_prestate_rejects_construction() -> None:
    accepted = _run(_fixture())
    assert isinstance(accepted, ZDEXBuybackSpendAcceptedV1)

    with pytest.raises(ValueError):
        replace(
            accepted,
            intent=replace(accepted.intent, cadence_pre_state_root=_root(99)),
        )


def test_small_exhaustive_domain_preserves_reserve_equation() -> None:
    for reserve in range(5):
        for fee in range(1, 21):
            for cap in range(1, 5):
                for limit in range(1, 5):
                    values = _fixture(
                        reserve=reserve,
                        fee_atoms=fee,
                        cap=cap,
                        safe_limit=limit,
                        minimum=1,
                    )
                    result = _run(values)
                    available = reserve + fee * 2_000 // 10_000
                    expected = min(available, cap, limit)
                    if expected == 0:
                        assert isinstance(result, ZDEXBuybackSpendRejectedV1)
                        _assert_noop(
                            result,
                            values,
                            ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM,
                        )
                    else:
                        assert isinstance(result, ZDEXBuybackSpendAcceptedV1)
                        assert result.intent.quote_spend_atoms == expected
                        assert (
                            result.fee_post_state.destination_balances[0].allocation_atoms
                            + expected
                            == available
                        )


def test_policy_rejects_invalid_bounds() -> None:
    quote = _root(1)
    with pytest.raises(ValueError):
        ZDEXBuybackSpendPolicyV1(quote, 0, 1, 1)
    with pytest.raises(ValueError):
        ZDEXBuybackSpendPolicyV1(quote, 2, 1, 1)
    with pytest.raises(ValueError):
        ZDEXBuybackSpendPolicyV1(quote, 1, MAX_DELTA_ATOMS_V1 + 1, 1)
    with pytest.raises(ValueError):
        ZDEXBuybackSpendPolicyV1(quote, 1, 1, 0)
