"""Semantic tests for the bounded Spot-owned ZDEX buyback transition.

RIPR target: one defect at a time must produce the first declared reject,
preserve the identical state object, and emit no effects, ports, journal, or
terminal obligation.  Accepted tests independently check CPMM arithmetic,
state projection, sibling preservation, value conservation, and commitment
roots.  This remains SHADOW evidence, not route or publication authority.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from typing import Any, TypeVar, cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.zdex_spot_buyback_transition_v1 as spot_transition
from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_U64_V1,
    ZERO_ROOT_V1,
    ReleaseStatusV1,
)
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from src.core.zdex_purchase_burn_route_types_v1 import ZDEXBuybackExecutionPolicyV1
from src.core.zdex_spot_buyback_transition_v1 import (
    ZDEXSpotBuybackAcceptedV1,
    ZDEXSpotBuybackAuthorityContextV1,
    ZDEXSpotBuybackInputV1,
    ZDEXSpotBuybackRejectCodeV1,
    ZDEXSpotBuybackRejectedV1,
    ZDEXSpotBuybackReleaseV1,
    ZDEXSpotCurveKindV1,
    ZDEXSpotLaneStateV1,
    ZDEXSpotOracleOccurrenceV1,
    ZDEXSpotOracleRegistryV1,
    ZDEXSpotOracleStatusV1,
    ZDEXSpotPoolCreationReleaseV1,
    ZDEXSpotPoolDefinitionV1,
    ZDEXSpotPoolStatusV1,
    ZDEXSpotPoolV1,
    ZDEXSpotPriceEnvelopeV1,
    ZDEXSpotPrivatePortsV1,
    ZDEXSpotProfileAuthorizationV1,
    ZDEXSpotQuoteInputPortV1,
    ZDEXSpotRegisteredCurveReleaseV1,
    transition_zdex_spot_buyback_v1,
)

T = TypeVar("T")


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _unchecked_replace(value: T, **updates: object) -> T:
    """Construct an exact-type hostile test value without dataclass validation."""

    forged = object.__new__(type(value))
    for field in dataclass_fields(cast(Any, type(value))):
        object.__setattr__(
            forged,
            field.name,
            updates.get(field.name, object.__getattribute__(value, field.name)),
        )
    return forged


def _candidate(
    *,
    fee_bps: int = 0,
    reserve0_atoms: int = 1_000,
    reserve1_atoms: int = 1_000,
    lp_supply_atoms: int = 1_000,
    amount_atoms: int = 125,
    minimum_output_atoms: int = 101,
    oracle_numerator: int = 125,
    oracle_denominator: int = 111,
    observed_height: int = 76,
    pool_status: ZDEXSpotPoolStatusV1 = ZDEXSpotPoolStatusV1.ACTIVE,
) -> ZDEXSpotBuybackInputV1:
    release = ZDEXSpotBuybackReleaseV1(
        spot_module_release_id=_root(1_001),
        tokenomics_module_release_id=_root(1_002),
        route_release_id=_root(2_001),
        cpmm_curve_release_id=_root(8_000),
        protocol_fee_share_bps=0,
        reserve_cap_atoms=3_000_000_000,
        swap_cap_atoms=3_000_000_000,
        pool_count_cap=64,
        pool_creation_releases=(
            ZDEXSpotPoolCreationReleaseV1(
                _root(1_001),
                ReleaseStatusV1.ACTIVE_NEW,
            ),
        ),
        registered_sibling_curve_releases=(),
    )
    definition = ZDEXSpotPoolDefinitionV1(
        asset0=_root(1),
        asset1=_root(2),
        fee_bps=fee_bps,
        curve_kind=ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN,
        curve_release_id=release.cpmm_curve_release_id,
        curve_params_root=ZERO_ROOT_V1,
    )
    pool = ZDEXSpotPoolV1(
        pool_id=definition.pool_id,
        definition=definition,
        reserve0_atoms=reserve0_atoms,
        reserve1_atoms=reserve1_atoms,
        lp_supply_atoms=lp_supply_atoms,
        status=pool_status,
        creation_release_id=release.spot_module_release_id,
        created_height=1,
    )
    state = ZDEXSpotLaneStateV1(
        pools=(pool,),
        lp_ownership_root=_root(11),
        route_batch_root=_root(12),
        fee_residue_root=_root(13),
        pool_terminal_obligations_root=_root(14),
    )
    execution_policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=definition.pool_id,
        pool_definition_root=definition.definition_root,
        quote_asset_id=definition.asset0,
        zdex_asset_id=definition.asset1,
    )
    price_policy = ZDEXBuybackPriceSafetyPolicyV1(
        oracle_id="zdex-buyback-oracle",
        maximum_oracle_age_blocks=3,
        minimum_quote_reserve_atoms=500,
        minimum_zdex_reserve_atoms=500,
        maximum_pool_oracle_deviation_bps=2_000,
        maximum_execution_impact_bps=2_000,
        maximum_oracle_execution_deviation_bps=1_000,
        maximum_quote_reserve_spend_bps=2_000,
    )
    profile_authorization = ZDEXSpotProfileAuthorizationV1(
        profile_root=_root(3_000),
        chain_id="zenodex-test-chain",
        deployment_root=_root(3_001),
        route_release_id=release.route_release_id,
        spot_module_release_id=release.spot_module_release_id,
        tokenomics_module_release_id=release.tokenomics_module_release_id,
        oracle_id=price_policy.oracle_id,
        release_root=release.release_root,
        execution_policy_root=execution_policy.policy_root,
        price_policy_root=price_policy.policy_root,
    )
    oracle_price = ZDEXBuybackOraclePriceOccurrenceV1(
        oracle_id=price_policy.oracle_id,
        quote_asset_id=execution_policy.quote_asset_id,
        zdex_asset_id=execution_policy.zdex_asset_id,
        quote_numerator_atoms=oracle_numerator,
        zdex_denominator_atoms=oracle_denominator,
        observed_height=observed_height,
    )
    oracle = ZDEXSpotOracleOccurrenceV1(
        price=oracle_price,
        finality_root=_root(96),
        status=ZDEXSpotOracleStatusV1.FINAL,
    )
    oracle_registry = ZDEXSpotOracleRegistryV1((oracle,))
    authority = ZDEXSpotBuybackAuthorityContextV1(
        chain_id=profile_authorization.chain_id,
        deployment_root=profile_authorization.deployment_root,
        profile_root=profile_authorization.profile_root,
        profile_authorization_root=profile_authorization.authorization_root,
        route_release_id=release.route_release_id,
        command_occurrence_id=_root(92),
        global_pre_state_root=_root(5_000),
        spot_pre_state_root=state.state_root,
        writer_epoch=0,
        current_height=77,
        spot_module_release_id=release.spot_module_release_id,
        tokenomics_module_release_id=release.tokenomics_module_release_id,
        release=release,
        execution_policy=execution_policy,
        expected_pool_definition=definition,
        price_policy=price_policy,
        profile_authorization=profile_authorization,
        oracle_registry=oracle_registry,
        oracle_occurrence=oracle,
    )
    quote_port = ZDEXSpotQuoteInputPortV1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        spot_pre_state_root=authority.spot_pre_state_root,
        source_module_release_id=authority.tokenomics_module_release_id,
        destination_module_release_id=authority.spot_module_release_id,
        source_pre_state_root=_root(201),
        source_post_state_root=_root(202),
        source_effect_plan_root=_root(203),
        source_journal_root=_root(204),
        source_receipt_binding_root=_root(205),
        amount_atoms=amount_atoms,
    )
    envelope = ZDEXSpotPriceEnvelopeV1(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        spot_pre_state_root=authority.spot_pre_state_root,
        selected_pool_id=execution_policy.pool_id,
        oracle_occurrence_id=oracle.occurrence_id,
        oracle_finality_root=oracle.finality_root,
        quote_amount_atoms=amount_atoms,
        current_height=authority.current_height,
        oracle_observed_height=oracle_price.observed_height,
        oracle_quote_numerator_atoms=oracle_price.quote_numerator_atoms,
        oracle_zdex_denominator_atoms=oracle_price.zdex_denominator_atoms,
        claimed_route_safe_quote_limit_atoms=200,
        minimum_output_atoms=minimum_output_atoms,
    )
    return ZDEXSpotBuybackInputV1(authority, state, quote_port, envelope)


def _with_state(
    candidate: ZDEXSpotBuybackInputV1,
    state: ZDEXSpotLaneStateV1,
) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    root = state.state_root
    return replace(
        candidate,
        authority=replace(authority, spot_pre_state_root=root),
        pre_state=state,
        quote_port=replace(candidate.quote_port, spot_pre_state_root=root),
        price_envelope=replace(candidate.price_envelope, spot_pre_state_root=root),
    )


def _with_oracle(
    candidate: ZDEXSpotBuybackInputV1,
    oracle: ZDEXSpotOracleOccurrenceV1,
) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    return replace(
        candidate,
        authority=replace(
            authority,
            oracle_registry=ZDEXSpotOracleRegistryV1((oracle,)),
            oracle_occurrence=oracle,
        ),
        price_envelope=replace(
            candidate.price_envelope,
            oracle_occurrence_id=oracle.occurrence_id,
            oracle_finality_root=oracle.finality_root,
            oracle_observed_height=oracle.price.observed_height,
            oracle_quote_numerator_atoms=oracle.price.quote_numerator_atoms,
            oracle_zdex_denominator_atoms=oracle.price.zdex_denominator_atoms,
        ),
    )


def _reject_code(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackRejectCodeV1:
    result = transition_zdex_spot_buyback_v1(candidate)
    assert type(result) is ZDEXSpotBuybackRejectedV1
    assert result.pre_state is candidate.pre_state
    assert result.post_state is candidate.pre_state
    assert result.effects.is_empty
    assert result.ports is None
    assert result.journal is None
    assert result.terminal_obligation is None
    return result.code


def test_accepts_derived_cpmm_transition_and_freezes_commitment_roots() -> None:
    # Arrange.
    candidate = _candidate()

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    assert type(result) is ZDEXSpotBuybackAcceptedV1
    assert result.journal.fee_atoms == 0
    assert result.journal.net_input_atoms == 125
    assert result.journal.purchased_zdex_atoms == 111
    assert result.post_state.pools[0].reserve0_atoms == 1_125
    assert result.post_state.pools[0].reserve1_atoms == 889
    assert result.post_state.state_root == (
        "0xb42313a61d18805ae7745a54b5d1bdf1e58479ebeda34861942aa022bc9a1b0f"
    )
    assert result.effects.effect_plan_root == (
        "0xafcb6b6f8bd26a69fe8d637717450f37cc4d0f1ed380f64c19910dd01886d71a"
    )
    assert result.ports.ports_root == (
        "0x8c6e07a5e3614178d98535d27cb170ae306fb4c241727594dea15459cc523994"
    )
    assert result.terminal_obligation.obligation_id == (
        "0xd41633a3185a5cb3528915a2146cf8ac97485b6d804c289b108f451e80300054"
    )
    assert result.journal.journal_root == (
        "0x003711f76c6ae397542cb000cae6445994654275d50d53f930c781c9d9970ae3"
    )


def test_rounding_one_atom_siblings_and_spot_value_conservation() -> None:
    # Arrange: prepend one independently registered CPMM sibling.
    candidate = _candidate(fee_bps=1, minimum_output_atoms=101)
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    sibling_definition = ZDEXSpotPoolDefinitionV1(
        _root(3),
        _root(4),
        0,
        ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN,
        authority.release.cpmm_curve_release_id,
        ZERO_ROOT_V1,
    )
    sibling = ZDEXSpotPoolV1(
        sibling_definition.pool_id,
        sibling_definition,
        500,
        500,
        500,
        ZDEXSpotPoolStatusV1.ACTIVE,
        authority.release.spot_module_release_id,
        1,
    )
    pools = tuple(sorted((sibling, candidate.pre_state.pools[0]), key=lambda row: row.pool_id))
    candidate = _with_state(candidate, replace(candidate.pre_state, pools=pools))

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert: ceil(125/10000)=1, so net=124 and output=110.
    assert type(result) is ZDEXSpotBuybackAcceptedV1
    assert result.journal.fee_atoms == 1
    assert result.journal.net_input_atoms == 124
    assert result.journal.purchased_zdex_atoms == 110
    unchanged = next(pool for pool in result.post_state.pools if pool.pool_id == sibling.pool_id)
    assert unchanged == sibling
    selected_pre = next(
        pool for pool in candidate.pre_state.pools if pool.pool_id == authority.execution_policy.pool_id
    )
    selected_post = next(
        pool for pool in result.post_state.pools if pool.pool_id == selected_pre.pool_id
    )
    assert selected_post.reserve0_atoms - selected_pre.reserve0_atoms == 125
    assert selected_pre.reserve1_atoms - selected_post.reserve1_atoms == 110
    assert selected_post.reserve0_atoms * selected_post.reserve1_atoms >= (
        selected_pre.reserve0_atoms * selected_pre.reserve1_atoms
    )


@settings(max_examples=100, deadline=None, derandomize=True)
@given(
    reserve0_atoms=st.integers(min_value=1_000, max_value=1_000_000),
    amount_atoms=st.integers(min_value=10, max_value=50),
)
def test_generated_accepted_transitions_are_deterministic_and_conserved(
    reserve0_atoms: int,
    amount_atoms: int,
) -> None:
    # Arrange: Oracle ratio 1/2 exactly matches a pool holding twice as much
    # ZDEX as quote, while every generated trade stays inside release caps.
    reserve1_atoms = reserve0_atoms * 2
    purchased_atoms = reserve1_atoms * amount_atoms // (reserve0_atoms + amount_atoms)
    minimum_output_atoms = (amount_atoms * 2 * 10_000 + 10_999) // 11_000
    candidate = _candidate(
        reserve0_atoms=reserve0_atoms,
        reserve1_atoms=reserve1_atoms,
        amount_atoms=amount_atoms,
        fee_bps=0,
        minimum_output_atoms=minimum_output_atoms,
        oracle_numerator=1,
        oracle_denominator=2,
    )
    candidate = replace(
        candidate,
        price_envelope=replace(
            candidate.price_envelope,
            claimed_route_safe_quote_limit_atoms=reserve0_atoms // 5,
        ),
    )
    pre_state = candidate.pre_state

    # Act.
    first = transition_zdex_spot_buyback_v1(candidate)
    second = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    assert type(first) is ZDEXSpotBuybackAcceptedV1
    assert type(second) is ZDEXSpotBuybackAcceptedV1
    assert first.post_state == second.post_state
    assert first.effects.effect_plan_root == second.effects.effect_plan_root
    assert first.journal.journal_root == second.journal.journal_root
    assert candidate.pre_state is pre_state
    selected_pre = pre_state.pools[0]
    selected_post = first.post_state.pools[0]
    assert selected_post.reserve0_atoms - selected_pre.reserve0_atoms == amount_atoms
    assert selected_pre.reserve1_atoms - selected_post.reserve1_atoms == purchased_atoms
    assert tuple(row.delta_atoms for row in first.effects.rows) == (
        amount_atoms,
        -purchased_atoms,
    )


def test_one_atom_boundary_is_live_under_an_explicit_wide_shadow_envelope() -> None:
    # Arrange.
    candidate = _candidate(
        reserve0_atoms=501,
        reserve1_atoms=1_000,
        amount_atoms=1,
        minimum_output_atoms=1,
        oracle_numerator=1,
        oracle_denominator=1,
    )
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    price_policy = replace(
        authority.price_policy,
        minimum_quote_reserve_atoms=1,
        minimum_zdex_reserve_atoms=1,
        maximum_pool_oracle_deviation_bps=9_999,
        maximum_execution_impact_bps=9_999,
        maximum_oracle_execution_deviation_bps=9_999,
    )
    profile = replace(
        authority.profile_authorization,
        price_policy_root=price_policy.policy_root,
    )
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            price_policy=price_policy,
            profile_authorization=profile,
            profile_authorization_root=profile.authorization_root,
        ),
        price_envelope=replace(
            candidate.price_envelope,
            claimed_route_safe_quote_limit_atoms=100,
        ),
    )

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    assert type(result) is ZDEXSpotBuybackAcceptedV1
    assert result.journal.quote_input_atoms == 1
    assert result.journal.purchased_zdex_atoms == 1


def test_reserve_cap_exact_neighbor_accepts_and_successor_rejects() -> None:
    # Arrange: one atom fills the quote reserve to the exact release cap.
    cap = 3_000_000_000
    exact = _candidate(
        reserve0_atoms=cap - 1,
        reserve1_atoms=cap,
        amount_atoms=1,
        minimum_output_atoms=1,
        oracle_numerator=1,
        oracle_denominator=1,
    )
    exact = replace(
        exact,
        price_envelope=replace(
            exact.price_envelope,
            claimed_route_safe_quote_limit_atoms=(cap - 1) * 2_000 // 10_000,
        ),
    )
    successor = _candidate(
        reserve0_atoms=cap,
        reserve1_atoms=cap,
        amount_atoms=1,
        minimum_output_atoms=1,
        oracle_numerator=1,
        oracle_denominator=1,
    )

    # Act / Assert.
    exact_result = transition_zdex_spot_buyback_v1(exact)
    assert type(exact_result) is ZDEXSpotBuybackAcceptedV1
    assert exact_result.post_state.pools[0].reserve0_atoms == cap
    assert _reject_code(successor) is ZDEXSpotBuybackRejectCodeV1.AMOUNT_OUT_OF_RANGE


@pytest.mark.parametrize(
    ("fee_bps", "accepted", "reject"),
    (
        (0, True, None),
        (1, True, None),
        (9_999, False, ZDEXSpotBuybackRejectCodeV1.FEE_CONSUMES_INPUT),
        (10_000, False, ZDEXSpotBuybackRejectCodeV1.FEE_CONSUMES_INPUT),
        (10_001, False, ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED),
    ),
)
def test_fee_basis_point_boundaries_have_exact_first_outcomes(
    fee_bps: int,
    accepted: bool,
    reject: ZDEXSpotBuybackRejectCodeV1 | None,
) -> None:
    # Arrange.
    candidate = _candidate(
        fee_bps=fee_bps,
        minimum_output_atoms=101 if fee_bps <= 1 else 1,
    )

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    if accepted:
        assert type(result) is ZDEXSpotBuybackAcceptedV1
    else:
        assert type(result) is ZDEXSpotBuybackRejectedV1
        assert result.code is reject


def _with_pool_count(
    candidate: ZDEXSpotBuybackInputV1,
    count: int,
) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    pools = list(candidate.pre_state.pools[: min(count, 1)])
    for index in range(max(0, count - 1)):
        definition = ZDEXSpotPoolDefinitionV1(
            _root(10_000 + index * 2),
            _root(10_001 + index * 2),
            0,
            ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN,
            authority.release.cpmm_curve_release_id,
            ZERO_ROOT_V1,
        )
        pools.append(
            ZDEXSpotPoolV1(
                definition.pool_id,
                definition,
                1_000,
                1_000,
                1_000,
                ZDEXSpotPoolStatusV1.ACTIVE,
                authority.release.spot_module_release_id,
                1,
            )
        )
    state = replace(
        candidate.pre_state,
        pools=tuple(sorted(pools, key=lambda pool: pool.pool_id)),
    )
    return _with_state(candidate, state)


@pytest.mark.parametrize(
    ("count", "accepted"),
    ((0, False), (1, True), (64, True), (65, False)),
)
def test_pool_count_boundaries_are_exact(count: int, accepted: bool) -> None:
    # Arrange.
    candidate = _with_pool_count(_candidate(), count)

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    if accepted:
        assert type(result) is ZDEXSpotBuybackAcceptedV1
        assert len(result.post_state.pools) == count
    else:
        assert type(result) is ZDEXSpotBuybackRejectedV1
        assert result.code is ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED


def test_u64_height_maximum_accepts_and_successor_is_unrepresentable() -> None:
    # Arrange.
    exact = _candidate(observed_height=MAX_U64_V1 - 1)
    authority = exact.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    exact = replace(
        exact,
        authority=replace(authority, current_height=MAX_U64_V1),
        price_envelope=replace(exact.price_envelope, current_height=MAX_U64_V1),
    )
    # Act / Assert.
    assert type(transition_zdex_spot_buyback_v1(exact)) is ZDEXSpotBuybackAcceptedV1
    exact_authority = exact.authority
    assert type(exact_authority) is ZDEXSpotBuybackAuthorityContextV1
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(exact_authority, current_height=MAX_U64_V1 + 1)


def test_oracle_registry_rejects_a_pending_sibling_occurrence() -> None:
    # Arrange: the selected occurrence is final, while another committed
    # occurrence from the same provider is pending.
    candidate = _candidate()
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    pending = ZDEXSpotOracleOccurrenceV1(
        replace(authority.oracle_occurrence.price, observed_height=75),
        _root(97),
        ZDEXSpotOracleStatusV1.PENDING,
    )
    occurrences = tuple(
        sorted(
            (authority.oracle_occurrence, pending),
            key=lambda occurrence: occurrence.occurrence_id,
        )
    )
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            oracle_registry=ZDEXSpotOracleRegistryV1(occurrences),
        ),
    )

    # Act / Assert.
    assert _reject_code(candidate) is ZDEXSpotBuybackRejectCodeV1.ORACLE_MISMATCH


def test_registered_drain_only_sibling_curve_is_preserved() -> None:
    # Arrange: the selected pool stays CPMM-v8 while an unrelated pool pins a
    # separately registered draining curve release.
    candidate = _candidate()
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    sibling_curve_release = _root(8_001)
    release = replace(
        authority.release,
        registered_sibling_curve_releases=(
            ZDEXSpotRegisteredCurveReleaseV1(
                sibling_curve_release,
                ReleaseStatusV1.DRAIN_ONLY,
            ),
        ),
    )
    sibling_definition = ZDEXSpotPoolDefinitionV1(
        _root(3),
        _root(4),
        0,
        ZDEXSpotCurveKindV1.REGISTERED_OTHER,
        sibling_curve_release,
        _root(8_002),
    )
    sibling = ZDEXSpotPoolV1(
        sibling_definition.pool_id,
        sibling_definition,
        500,
        500,
        500,
        ZDEXSpotPoolStatusV1.ACTIVE,
        release.spot_module_release_id,
        1,
    )
    pools = tuple(sorted((*candidate.pre_state.pools, sibling), key=lambda pool: pool.pool_id))
    candidate = _with_state(candidate, replace(candidate.pre_state, pools=pools))
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    profile = replace(
        authority.profile_authorization,
        release_root=release.release_root,
    )
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            release=release,
            profile_authorization=profile,
            profile_authorization_root=profile.authorization_root,
        ),
    )

    # Act.
    result = transition_zdex_spot_buyback_v1(candidate)

    # Assert.
    assert type(result) is ZDEXSpotBuybackAcceptedV1
    assert sibling in result.post_state.pools


def test_revoked_pool_creation_release_is_not_admissible() -> None:
    # Arrange.
    candidate = _candidate()
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    release = replace(
        authority.release,
        pool_creation_releases=(
            ZDEXSpotPoolCreationReleaseV1(
                authority.release.spot_module_release_id,
                ReleaseStatusV1.REVOKED,
            ),
        ),
    )
    profile = replace(
        authority.profile_authorization,
        release_root=release.release_root,
    )
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            release=release,
            profile_authorization=profile,
            profile_authorization_root=profile.authorization_root,
        ),
    )

    # Act / Assert.
    assert _reject_code(candidate) is ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED


Mutation = Callable[[ZDEXSpotBuybackInputV1], ZDEXSpotBuybackInputV1]


def _authority_malformed(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    return replace(candidate, authority=object())


def _release_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    return replace(candidate, authority=replace(authority, release=replace(authority.release, swap_cap_atoms=2)))


def _profile_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    return replace(candidate, authority=replace(authority, profile_authorization_root=_root(9_001)))


def _state_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    return replace(candidate, authority=replace(authority, spot_pre_state_root=_root(9_002)))


def _quote_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    return replace(candidate, quote_port=replace(candidate.quote_port, source_post_state_root=candidate.quote_port.source_pre_state_root))


def _oracle_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    oracle = replace(authority.oracle_occurrence, status=ZDEXSpotOracleStatusV1.DISPUTED)
    return _with_oracle(candidate, oracle)


def _price_subject_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    return replace(candidate, price_envelope=replace(candidate.price_envelope, quote_amount_atoms=124))


def _policy_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    bad_definition = replace(authority.expected_pool_definition, curve_params_root=_root(1))
    return replace(candidate, authority=replace(authority, expected_pool_definition=bad_definition))


def _lane_malformed(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    pool = candidate.pre_state.pools[0]
    return _with_state(candidate, replace(candidate.pre_state, pools=(pool, pool)))


def _unregistered_creation_release(
    candidate: ZDEXSpotBuybackInputV1,
) -> ZDEXSpotBuybackInputV1:
    pool = replace(candidate.pre_state.pools[0], creation_release_id=_root(99_001))
    return _with_state(candidate, replace(candidate.pre_state, pools=(pool,)))


def _selection_mismatch(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    definition = ZDEXSpotPoolDefinitionV1(
        _root(3),
        _root(4),
        0,
        ZDEXSpotCurveKindV1.CPMM_V8_EXACT_IN,
        authority.release.cpmm_curve_release_id,
        ZERO_ROOT_V1,
    )
    pool = ZDEXSpotPoolV1(
        definition.pool_id,
        definition,
        1_000,
        1_000,
        1_000,
        ZDEXSpotPoolStatusV1.ACTIVE,
        authority.release.spot_module_release_id,
        1,
    )
    return _with_state(candidate, replace(candidate.pre_state, pools=(pool,)))


def _pool_inactive(candidate: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackInputV1:
    pool = replace(candidate.pre_state.pools[0], status=ZDEXSpotPoolStatusV1.FROZEN)
    return _with_state(candidate, replace(candidate.pre_state, pools=(pool,)))


@pytest.mark.parametrize(
    ("candidate", "expected"),
    (
        (_candidate(amount_atoms=3_000_000_001, minimum_output_atoms=1), ZDEXSpotBuybackRejectCodeV1.AMOUNT_OUT_OF_RANGE),
        (_candidate(oracle_numerator=MAX_ATOMS_V1, minimum_output_atoms=1), ZDEXSpotBuybackRejectCodeV1.ARITHMETIC_OUT_OF_RANGE),
        (_candidate(fee_bps=10_000, minimum_output_atoms=1), ZDEXSpotBuybackRejectCodeV1.FEE_CONSUMES_INPUT),
        (_candidate(reserve0_atoms=1_000_000_000, reserve1_atoms=1, amount_atoms=1, minimum_output_atoms=1), ZDEXSpotBuybackRejectCodeV1.ZERO_OUTPUT),
        (_candidate(minimum_output_atoms=102), ZDEXSpotBuybackRejectCodeV1.MINIMUM_OUTPUT_MISMATCH),
        (_candidate(observed_height=73), ZDEXSpotBuybackRejectCodeV1.PRICE_UNSAFE),
    ),
)
def test_arithmetic_and_price_boundary_rejections_are_exact_noops(
    candidate: ZDEXSpotBuybackInputV1,
    expected: ZDEXSpotBuybackRejectCodeV1,
) -> None:
    # Arrange / Act / Assert.
    assert _reject_code(candidate) is expected


def test_pool_oracle_cross_product_overflow_precedes_price_unsafe() -> None:
    # Arrange: the two-factor reserve-price product fits U128 while the
    # price-deviation products required by the Lean arithmetic guard do not.
    candidate = _candidate(
        oracle_numerator=MAX_ATOMS_V1 // 2_000_000,
        minimum_output_atoms=1,
    )
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    price_policy = replace(
        authority.price_policy,
        maximum_pool_oracle_deviation_bps=9_999,
        maximum_oracle_execution_deviation_bps=0,
    )
    profile = replace(
        authority.profile_authorization,
        price_policy_root=price_policy.policy_root,
    )
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            price_policy=price_policy,
            profile_authorization=profile,
            profile_authorization_root=profile.authorization_root,
        ),
    )

    # Act / Assert: arithmetic has earlier precedence than price policy.
    assert _reject_code(candidate) is ZDEXSpotBuybackRejectCodeV1.ARITHMETIC_OUT_OF_RANGE


@pytest.mark.parametrize(
    ("mutate", "expected"),
    (
        (_authority_malformed, ZDEXSpotBuybackRejectCodeV1.AUTHORITY_MALFORMED),
        (_release_mismatch, ZDEXSpotBuybackRejectCodeV1.RELEASE_MISMATCH),
        (_profile_mismatch, ZDEXSpotBuybackRejectCodeV1.PROFILE_MISMATCH),
        (_state_mismatch, ZDEXSpotBuybackRejectCodeV1.STATE_COMMITMENT_MISMATCH),
        (_quote_mismatch, ZDEXSpotBuybackRejectCodeV1.QUOTE_PORT_MISMATCH),
        (_oracle_mismatch, ZDEXSpotBuybackRejectCodeV1.ORACLE_MISMATCH),
        (_price_subject_mismatch, ZDEXSpotBuybackRejectCodeV1.PRICE_SUBJECT_MISMATCH),
        (_policy_mismatch, ZDEXSpotBuybackRejectCodeV1.POLICY_MISMATCH),
        (_lane_malformed, ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED),
        (_unregistered_creation_release, ZDEXSpotBuybackRejectCodeV1.LANE_MALFORMED),
        (_selection_mismatch, ZDEXSpotBuybackRejectCodeV1.SELECTION_MISMATCH),
        (_pool_inactive, ZDEXSpotBuybackRejectCodeV1.POOL_INACTIVE),
    ),
)
def test_each_structural_guard_has_a_mutation_killing_noop(
    mutate: Mutation,
    expected: ZDEXSpotBuybackRejectCodeV1,
) -> None:
    # Arrange.
    candidate = mutate(_candidate())

    # Act / Assert.
    assert _reject_code(candidate) is expected


def test_release_reject_precedes_profile_and_later_failures() -> None:
    # Arrange: combine two independent defects.
    candidate = _profile_mismatch(_release_mismatch(_candidate()))

    # Act / Assert.
    assert _reject_code(candidate) is ZDEXSpotBuybackRejectCodeV1.RELEASE_MISMATCH


def test_reversed_asset_order_is_a_policy_mismatch_before_lane_validation() -> None:
    # Arrange: keep all earlier authority and Oracle bindings coherent while
    # reversing the policy's canonical quote/ZDEX asset order. The committed
    # pool state remains unchanged so a missing policy guard would fall through
    # to the later lane-state check.
    candidate = _candidate()
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    definition = replace(
        authority.expected_pool_definition,
        asset0=authority.execution_policy.zdex_asset_id,
        asset1=authority.execution_policy.quote_asset_id,
    )
    policy = replace(
        authority.execution_policy,
        pool_id=definition.pool_id,
        pool_definition_root=definition.definition_root,
        quote_asset_id=definition.asset0,
        zdex_asset_id=definition.asset1,
    )
    profile = replace(
        authority.profile_authorization,
        execution_policy_root=policy.policy_root,
    )
    oracle_price = replace(
        authority.oracle_occurrence.price,
        quote_asset_id=policy.quote_asset_id,
        zdex_asset_id=policy.zdex_asset_id,
    )
    oracle = replace(authority.oracle_occurrence, price=oracle_price)
    candidate = replace(
        candidate,
        authority=replace(
            authority,
            execution_policy=policy,
            expected_pool_definition=definition,
            profile_authorization=profile,
            profile_authorization_root=profile.authorization_root,
            oracle_registry=ZDEXSpotOracleRegistryV1((oracle,)),
            oracle_occurrence=oracle,
        ),
        price_envelope=replace(
            candidate.price_envelope,
            selected_pool_id=policy.pool_id,
            oracle_occurrence_id=oracle.occurrence_id,
            oracle_quote_numerator_atoms=oracle_price.quote_numerator_atoms,
            oracle_zdex_denominator_atoms=oracle_price.zdex_denominator_atoms,
        ),
    )

    # Act / Assert.
    assert _reject_code(candidate) is ZDEXSpotBuybackRejectCodeV1.POLICY_MISMATCH


def test_cross_occurrence_substitution_changes_both_flow_identities() -> None:
    # Arrange.
    first = _candidate()
    authority = first.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    second_occurrence = _root(93)
    second = replace(
        first,
        authority=replace(authority, command_occurrence_id=second_occurrence),
        quote_port=replace(first.quote_port, command_occurrence_id=second_occurrence),
        price_envelope=replace(
            first.price_envelope,
            command_occurrence_id=second_occurrence,
        ),
    )

    # Act.
    first_result = transition_zdex_spot_buyback_v1(first)
    second_result = transition_zdex_spot_buyback_v1(second)

    # Assert.
    assert type(first_result) is ZDEXSpotBuybackAcceptedV1
    assert type(second_result) is ZDEXSpotBuybackAcceptedV1
    assert first_result.ports.quote_input.flow_id != second_result.ports.quote_input.flow_id
    assert first_result.ports.purchased_output.flow_id != (
        second_result.ports.purchased_output.flow_id
    )


def test_accepted_result_rederives_and_rejects_private_token_forgery() -> None:
    candidate = _candidate()
    result = transition_zdex_spot_buyback_v1(candidate)
    assert type(result) is ZDEXSpotBuybackAcceptedV1
    result.validate()
    with pytest.raises(TypeError, match="local rederivation"):
        ZDEXSpotBuybackAcceptedV1(object(), candidate, object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        result._fields = object()  # type: ignore[assignment]
    with pytest.raises(ValueError, match="exact role pair"):
        ZDEXSpotPrivatePortsV1(result.ports.quote_input, result.ports.quote_input)

    forged_terminal = replace(result.terminal_obligation, purchased_atoms=1)
    forged_purchased_flow = replace(result.ports.purchased_output, amount_atoms=1)
    forged_ports = ZDEXSpotPrivatePortsV1(
        result.ports.quote_input,
        forged_purchased_flow,
    )
    forged_journal = replace(
        result.journal,
        private_ports_root=forged_ports.ports_root,
        terminal_obligation_id=forged_terminal.obligation_id,
        purchased_zdex_atoms=1,
        post_zdex_reserve_atoms=result.journal.pre_zdex_reserve_atoms - 1,
    )
    forged_fields = replace(
        result._fields,
        ports=forged_ports,
        journal=forged_journal,
        terminal_obligation=forged_terminal,
    )
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXSpotBuybackAcceptedV1(
            spot_transition._ACCEPTED_TOKEN_V1,
            candidate,
            forged_fields,
        )

    forged = object.__new__(ZDEXSpotBuybackAcceptedV1)
    object.__setattr__(forged, "_subject", candidate)
    object.__setattr__(forged, "_fields", forged_fields)
    with pytest.raises(ValueError, match="no longer rederives"):
        forged.validate()

    class AlwaysEqual:
        def __eq__(self, other: object) -> bool:
            return True

    class ExplodingEquality:
        def __eq__(self, other: object) -> bool:
            raise AssertionError("hostile equality must never run")

    for hostile_terminal in (AlwaysEqual(), ExplodingEquality()):
        hostile_fields = replace(
            result._fields,
            terminal_obligation=hostile_terminal,  # type: ignore[arg-type]
        )
        hostile = object.__new__(ZDEXSpotBuybackAcceptedV1)
        object.__setattr__(hostile, "_subject", candidate)
        object.__setattr__(hostile, "_fields", hostile_fields)
        with pytest.raises(TypeError, match="owned graph is not closed"):
            hostile.validate()

    hostile_wrapper = object.__new__(ZDEXSpotBuybackAcceptedV1)
    object.__setattr__(hostile_wrapper, "_subject", candidate)
    object.__setattr__(hostile_wrapper, "_fields", AlwaysEqual())
    with pytest.raises(TypeError, match="accepted fields are not closed"):
        hostile_wrapper.validate()

    false_fee_journal = _unchecked_replace(result.journal, fee_atoms=False)
    false_fee_fields = replace(result._fields, journal=false_fee_journal)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXSpotBuybackAcceptedV1(
            spot_transition._ACCEPTED_TOKEN_V1,
            candidate,
            false_fee_fields,
        )
    false_fee_wrapper = object.__new__(ZDEXSpotBuybackAcceptedV1)
    object.__setattr__(false_fee_wrapper, "_subject", candidate)
    object.__setattr__(false_fee_wrapper, "_fields", false_fee_fields)
    with pytest.raises(ValueError, match="no longer rederives"):
        false_fee_wrapper.validate()

    first_pool = result.pre_state.pools[0]
    true_height_pool = _unchecked_replace(first_pool, created_height=True)
    true_height_state = _unchecked_replace(
        result.pre_state,
        pools=(true_height_pool,),
    )
    true_height_fields = replace(result._fields, pre_state=true_height_state)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXSpotBuybackAcceptedV1(
            spot_transition._ACCEPTED_TOKEN_V1,
            candidate,
            true_height_fields,
        )

    first_effect = result.effects.rows[0]
    string_kind_effect = _unchecked_replace(first_effect, kind=first_effect.kind.value)
    string_kind_plan = _unchecked_replace(
        result.effects,
        rows=(string_kind_effect, *result.effects.rows[1:]),
    )
    string_kind_fields = replace(result._fields, effects=string_kind_plan)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXSpotBuybackAcceptedV1(
            spot_transition._ACCEPTED_TOKEN_V1,
            candidate,
            string_kind_fields,
        )

    cyclic_journal = _unchecked_replace(result.journal)
    object.__setattr__(cyclic_journal, "context_root", cyclic_journal)
    cyclic_fields = replace(result._fields, journal=cyclic_journal)
    cyclic_wrapper = object.__new__(ZDEXSpotBuybackAcceptedV1)
    object.__setattr__(cyclic_wrapper, "_subject", candidate)
    object.__setattr__(cyclic_wrapper, "_fields", cyclic_fields)
    with pytest.raises(ValueError, match="contains a cycle"):
        cyclic_wrapper.validate()

    oversized_journal = _unchecked_replace(
        result.journal,
        context_root=tuple("x" for _ in range(4_097)),
    )
    oversized_fields = replace(result._fields, journal=oversized_journal)
    oversized_wrapper = object.__new__(ZDEXSpotBuybackAcceptedV1)
    object.__setattr__(oversized_wrapper, "_subject", candidate)
    object.__setattr__(oversized_wrapper, "_fields", oversized_fields)
    with pytest.raises(ValueError, match="exceeds node budget"):
        oversized_wrapper.validate()
