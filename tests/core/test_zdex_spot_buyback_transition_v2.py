"""Semantic and adversarial evidence for the V2 Spot buyback successor.

The V2 leaf consumes the shared acyclic quote port directly.  These tests keep
the SHADOW claim ceiling: they exercise deterministic core behavior only and
do not claim proof authentication, route composition, publication, or custody
authority.
"""

from __future__ import annotations

import inspect
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from typing import Any, TypeVar, cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.zdex_spot_buyback_transition_v2 as spot_v2
from src.core.global_settlement_types_v1 import MAX_ATOMS_V1, ZERO_ROOT_V1, ReleaseStatusV1
from src.core.zdex_atomic_buyback_quote_port_v2 import ZDEXAtomicBuybackQuotePortV2
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from src.core.zdex_purchase_burn_route_types_v1 import ZDEXBuybackExecutionPolicyV1
from src.core.zdex_spot_buyback_transition_v1 import (
    ZDEXSpotBuybackAuthorityContextV1,
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
    ZDEXSpotProfileAuthorizationV1,
)
from src.core.zdex_spot_buyback_transition_v2 import (
    ZDEXSpotBuybackAcceptedV2,
    ZDEXSpotBuybackAuthorityContextV2,
    ZDEXSpotBuybackCoordinatesV2,
    ZDEXSpotBuybackInputV2,
    ZDEXSpotBuybackRejectCodeV2,
    ZDEXSpotBuybackRejectedV2,
    ZDEXSpotPriceEnvelopeV2,
    transition_zdex_spot_buyback_v2,
)

T = TypeVar("T")


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _unchecked_replace(value: T, **updates: object) -> T:
    """Forge exact dataclass instances only for malformed-boundary tests."""

    forged = object.__new__(type(value))
    for field in dataclass_fields(cast(Any, type(value))):
        object.__setattr__(
            forged,
            field.name,
            updates.get(field.name, object.__getattribute__(value, field.name)),
        )
    return forged


def _coordinates(
    authority: ZDEXSpotBuybackAuthorityContextV1,
    state: ZDEXSpotLaneStateV1,
    quote_port: ZDEXAtomicBuybackQuotePortV2,
) -> ZDEXSpotBuybackCoordinatesV2:
    return ZDEXSpotBuybackCoordinatesV2(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        spot_pre_state_root=state.state_root,
        producer_quote_pre_state_root=quote_port.producer_quote_pre_state_root,
        producer_quote_post_state_root=quote_port.producer_quote_post_state_root,
        producer_quote_effect_plan_root=quote_port.producer_quote_effect_plan_root,
        quote_port_root=quote_port.port_root,
    )


def _candidate(
    *,
    fee_bps: int = 0,
    reserve0_atoms: int = 1_000,
    reserve1_atoms: int = 1_000,
    amount_atoms: int = 125,
    minimum_output_atoms: int = 101,
    oracle_numerator: int = 125,
    oracle_denominator: int = 111,
    observed_height: int = 76,
    claimed_route_safe_quote_limit_atoms: int = 200,
) -> ZDEXSpotBuybackInputV2:
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
            ZDEXSpotPoolCreationReleaseV1(_root(1_001), ReleaseStatusV1.ACTIVE_NEW),
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
        lp_supply_atoms=1_000,
        status=ZDEXSpotPoolStatusV1.ACTIVE,
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
    policy = ZDEXBuybackExecutionPolicyV1(
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
    profile = ZDEXSpotProfileAuthorizationV1(
        profile_root=_root(3_000),
        chain_id="zenodex-test-chain",
        deployment_root=_root(3_001),
        route_release_id=release.route_release_id,
        spot_module_release_id=release.spot_module_release_id,
        tokenomics_module_release_id=release.tokenomics_module_release_id,
        oracle_id=price_policy.oracle_id,
        release_root=release.release_root,
        execution_policy_root=policy.policy_root,
        price_policy_root=price_policy.policy_root,
    )
    oracle_price = ZDEXBuybackOraclePriceOccurrenceV1(
        oracle_id=price_policy.oracle_id,
        quote_asset_id=policy.quote_asset_id,
        zdex_asset_id=policy.zdex_asset_id,
        quote_numerator_atoms=oracle_numerator,
        zdex_denominator_atoms=oracle_denominator,
        observed_height=observed_height,
    )
    oracle = ZDEXSpotOracleOccurrenceV1(
        price=oracle_price,
        finality_root=_root(96),
        status=ZDEXSpotOracleStatusV1.FINAL,
    )
    authority = ZDEXSpotBuybackAuthorityContextV1(
        chain_id=profile.chain_id,
        deployment_root=profile.deployment_root,
        profile_root=profile.profile_root,
        profile_authorization_root=profile.authorization_root,
        route_release_id=release.route_release_id,
        command_occurrence_id=_root(92),
        global_pre_state_root=_root(5_000),
        spot_pre_state_root=state.state_root,
        writer_epoch=0,
        current_height=77,
        spot_module_release_id=release.spot_module_release_id,
        tokenomics_module_release_id=release.tokenomics_module_release_id,
        release=release,
        execution_policy=policy,
        expected_pool_definition=definition,
        price_policy=price_policy,
        profile_authorization=profile,
        oracle_registry=ZDEXSpotOracleRegistryV1((oracle,)),
        oracle_occurrence=oracle,
    )
    quote_port = ZDEXAtomicBuybackQuotePortV2(
        profile_root=authority.profile_root,
        route_release_id=authority.route_release_id,
        command_occurrence_id=authority.command_occurrence_id,
        global_pre_state_root=authority.global_pre_state_root,
        producer_module_release_id=authority.tokenomics_module_release_id,
        consumer_module_release_id=authority.spot_module_release_id,
        producer_quote_pre_state_root=_root(7_001),
        producer_quote_post_state_root=_root(7_002),
        producer_quote_effect_plan_root=_root(7_003),
        selected_pool_id=definition.pool_id,
        quote_asset_id=definition.asset0,
        amount_atoms=amount_atoms,
    )
    coordinates = _coordinates(authority, state, quote_port)
    envelope = ZDEXSpotPriceEnvelopeV2(
        coordinates=coordinates,
        selected_pool_id=definition.pool_id,
        oracle_occurrence_id=oracle.occurrence_id,
        oracle_finality_root=oracle.finality_root,
        quote_amount_atoms=amount_atoms,
        current_height=authority.current_height,
        oracle_observed_height=oracle.price.observed_height,
        oracle_quote_numerator_atoms=oracle.price.quote_numerator_atoms,
        oracle_zdex_denominator_atoms=oracle.price.zdex_denominator_atoms,
        claimed_route_safe_quote_limit_atoms=claimed_route_safe_quote_limit_atoms,
        minimum_output_atoms=minimum_output_atoms,
    )
    return ZDEXSpotBuybackInputV2(
        authority=ZDEXSpotBuybackAuthorityContextV2(authority),
        pre_state=state,
        quote_port=quote_port,
        price_envelope=envelope,
    )


def _stable_authority(candidate: ZDEXSpotBuybackInputV2) -> ZDEXSpotBuybackAuthorityContextV1:
    authority = candidate.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV2
    return authority.stable_authority


def _rebind(
    candidate: ZDEXSpotBuybackInputV2,
    *,
    authority: ZDEXSpotBuybackAuthorityContextV1 | None = None,
    pre_state: ZDEXSpotLaneStateV1 | None = None,
    quote_port: ZDEXAtomicBuybackQuotePortV2 | None = None,
) -> ZDEXSpotBuybackInputV2:
    stable_authority = _stable_authority(candidate) if authority is None else authority
    state = candidate.pre_state if pre_state is None else pre_state
    port = candidate.quote_port if quote_port is None else quote_port
    coordinates = _coordinates(stable_authority, state, port)
    envelope = replace(
        candidate.price_envelope,
        coordinates=coordinates,
        quote_amount_atoms=port.amount_atoms,
        current_height=stable_authority.current_height,
        oracle_observed_height=stable_authority.oracle_occurrence.price.observed_height,
        oracle_quote_numerator_atoms=(
            stable_authority.oracle_occurrence.price.quote_numerator_atoms
        ),
        oracle_zdex_denominator_atoms=(
            stable_authority.oracle_occurrence.price.zdex_denominator_atoms
        ),
        oracle_occurrence_id=stable_authority.oracle_occurrence.occurrence_id,
        oracle_finality_root=stable_authority.oracle_occurrence.finality_root,
        selected_pool_id=stable_authority.execution_policy.pool_id,
    )
    return ZDEXSpotBuybackInputV2(
        authority=ZDEXSpotBuybackAuthorityContextV2(stable_authority),
        pre_state=state,
        quote_port=port,
        price_envelope=envelope,
    )


def _assert_exact_noop(
    result: object,
    candidate: ZDEXSpotBuybackInputV2,
    code: ZDEXSpotBuybackRejectCodeV2,
) -> None:
    assert type(result) is ZDEXSpotBuybackRejectedV2
    rejected = result
    assert rejected.code is code
    assert rejected.pre_state is candidate.pre_state
    assert rejected.post_state is candidate.pre_state
    assert rejected.effects.is_empty
    assert rejected.context is None
    assert rejected.ports is None
    assert rejected.journal is None
    assert rejected.terminal_obligation is None


def _keys(value: object) -> set[str]:
    if isinstance(value, dict):
        return set(value) | set().union(*(_keys(item) for item in value.values()))
    if isinstance(value, list | tuple):
        return set().union(*(_keys(item) for item in value)) if value else set()
    return set()


def test_accepts_v2_port_bound_cpmm_transition_and_emits_exact_terminal() -> None:
    # Arrange.
    candidate = _candidate()

    # Act.
    result = transition_zdex_spot_buyback_v2(candidate)

    # Assert.
    assert type(result) is ZDEXSpotBuybackAcceptedV2
    accepted = result
    accepted.validate()
    coordinates = accepted.context.coordinates
    assert coordinates.profile_root == candidate.quote_port.profile_root
    assert coordinates.route_release_id == candidate.quote_port.route_release_id
    assert coordinates.command_occurrence_id == candidate.quote_port.command_occurrence_id
    assert coordinates.global_pre_state_root == candidate.quote_port.global_pre_state_root
    assert coordinates.spot_pre_state_root == candidate.pre_state.state_root
    assert coordinates.producer_quote_pre_state_root == (
        candidate.quote_port.producer_quote_pre_state_root
    )
    assert coordinates.producer_quote_post_state_root == (
        candidate.quote_port.producer_quote_post_state_root
    )
    assert coordinates.producer_quote_effect_plan_root == (
        candidate.quote_port.producer_quote_effect_plan_root
    )
    assert accepted.quote_port_root == candidate.quote_port.port_root
    assert accepted.context.coordinates.quote_port_root == candidate.quote_port.port_root
    assert accepted.journal.context.coordinates.quote_port_root == candidate.quote_port.port_root
    assert accepted.ports.quote_input.context.coordinates.quote_port_root == candidate.quote_port.port_root
    assert accepted.ports.purchased_output.context.coordinates.quote_port_root == (
        candidate.quote_port.port_root
    )
    assert accepted.terminal_obligation.context.coordinates.quote_port_root == (
        candidate.quote_port.port_root
    )
    assert accepted.journal.context.coordinates.coordinates_root == coordinates.coordinates_root
    assert accepted.ports.quote_input.context.coordinates.coordinates_root == (
        coordinates.coordinates_root
    )
    assert accepted.ports.purchased_output.context.coordinates.coordinates_root == (
        coordinates.coordinates_root
    )
    assert accepted.terminal_obligation.context.coordinates.coordinates_root == (
        coordinates.coordinates_root
    )
    assert accepted.ports.quote_input.source_principal == candidate.quote_port.source_principal
    assert accepted.ports.quote_input.destination_principal == candidate.quote_port.destination_principal
    assert accepted.journal.quote_input_atoms == 125
    assert accepted.journal.purchased_zdex_atoms == 111
    assert accepted.post_state.pools[0].reserve0_atoms == 1_125
    assert accepted.post_state.pools[0].reserve1_atoms == 889
    assert accepted.terminal_obligation.purchased_atoms == 111
    assert accepted.effects.rows[0].delta_atoms + accepted.effects.rows[1].delta_atoms == 14


def test_v2_projections_exclude_legacy_receipt_and_journal_fields() -> None:
    # Arrange.
    result = transition_zdex_spot_buyback_v2(_candidate())
    assert type(result) is ZDEXSpotBuybackAcceptedV2
    accepted = result

    # Act.
    projection_keys = set().union(
        _keys(accepted.context.to_canonical()),
        _keys(accepted.journal.to_canonical()),
        _keys(accepted.ports.quote_input.to_canonical()),
        _keys(accepted.terminal_obligation.to_canonical()),
    )

    # Assert.
    assert {"source_journal_root", "source_receipt_binding_root"}.isdisjoint(
        projection_keys
    )
    source = inspect.getsource(spot_v2)
    assert "source_journal_root" not in source
    assert "source_receipt_binding_root" not in source


@pytest.mark.parametrize(
    "field_name",
    (
        "profile_root",
        "route_release_id",
        "command_occurrence_id",
        "global_pre_state_root",
        "producer_module_release_id",
        "consumer_module_release_id",
        "selected_pool_id",
        "quote_asset_id",
    ),
)
def test_each_quote_port_coordinate_mutation_is_rejected_before_math(
    field_name: str,
) -> None:
    # Arrange.
    candidate = _candidate()
    bad_port = replace(candidate.quote_port, **{field_name: _root(90_000)})
    mutated = replace(candidate, quote_port=bad_port)

    # Act.
    result = transition_zdex_spot_buyback_v2(mutated)

    # Assert: this kills a missing coordinate guard without relying on price math.
    _assert_exact_noop(result, mutated, ZDEXSpotBuybackRejectCodeV2.QUOTE_PORT_MISMATCH)


def test_price_envelope_port_root_substitution_is_exact_noop() -> None:
    # Arrange.
    candidate = _candidate()
    forged_coordinates = replace(
        candidate.price_envelope.coordinates,
        quote_port_root=_root(90_001),
    )
    mutated = replace(candidate, price_envelope=replace(candidate.price_envelope, coordinates=forged_coordinates))

    # Act.
    result = transition_zdex_spot_buyback_v2(mutated)

    # Assert.
    _assert_exact_noop(result, mutated, ZDEXSpotBuybackRejectCodeV2.PRICE_SUBJECT_MISMATCH)


def test_state_commitment_mismatch_precedes_port_and_price_validation() -> None:
    # Arrange.
    candidate = _candidate()
    stable = _stable_authority(candidate)
    mutated = replace(
        candidate,
        authority=ZDEXSpotBuybackAuthorityContextV2(
            replace(stable, spot_pre_state_root=_root(90_002))
        ),
    )

    # Act.
    result = transition_zdex_spot_buyback_v2(mutated)

    # Assert.
    _assert_exact_noop(result, mutated, ZDEXSpotBuybackRejectCodeV2.STATE_COMMITMENT_MISMATCH)


def test_one_atom_boundary_is_live_with_price_matched_reserves() -> None:
    # Arrange: 6000 * 1 // 501 = 11, matching the exact rounded Oracle floor.
    candidate = _candidate(
        reserve0_atoms=500,
        reserve1_atoms=6_000,
        amount_atoms=1,
        minimum_output_atoms=11,
        oracle_numerator=1,
        oracle_denominator=12,
        claimed_route_safe_quote_limit_atoms=100,
    )

    # Act.
    result = transition_zdex_spot_buyback_v2(candidate)

    # Assert.
    assert type(result) is ZDEXSpotBuybackAcceptedV2
    assert result.journal.purchased_zdex_atoms == 11


def test_swap_cap_successor_rejects_as_an_exact_noop() -> None:
    # Arrange.
    candidate = _candidate(
        amount_atoms=3_000_000_001,
        minimum_output_atoms=1,
    )

    # Act.
    result = transition_zdex_spot_buyback_v2(candidate)

    # Assert.
    _assert_exact_noop(result, candidate, ZDEXSpotBuybackRejectCodeV2.AMOUNT_OUT_OF_RANGE)


def test_zero_or_hostile_port_fields_fail_closed_without_equality_dispatch() -> None:
    # Arrange.
    candidate = _candidate()
    zero_port = _unchecked_replace(candidate.quote_port, amount_atoms=0)
    zero_candidate = _unchecked_replace(candidate, quote_port=zero_port)

    class ExplodingEquality:
        def __eq__(self, other: object) -> bool:
            raise AssertionError("hostile equality must never run")

    hostile_coordinates = _unchecked_replace(
        candidate.price_envelope.coordinates,
        quote_port_root=ExplodingEquality(),
    )
    hostile_envelope = _unchecked_replace(
        candidate.price_envelope,
        coordinates=hostile_coordinates,
    )
    hostile_candidate = _unchecked_replace(candidate, price_envelope=hostile_envelope)

    # Act.
    zero_result = transition_zdex_spot_buyback_v2(zero_candidate)
    hostile_result = transition_zdex_spot_buyback_v2(hostile_candidate)

    # Assert.
    _assert_exact_noop(zero_result, zero_candidate, ZDEXSpotBuybackRejectCodeV2.INPUT_MALFORMED)
    _assert_exact_noop(hostile_result, hostile_candidate, ZDEXSpotBuybackRejectCodeV2.INPUT_MALFORMED)


def test_forged_frozen_v1_state_and_authority_values_fail_closed_before_math() -> None:
    # Arrange: bypass V1 constructors exactly as a hostile in-process caller can.
    candidate = _candidate()
    forged_pool = _unchecked_replace(candidate.pre_state.pools[0], created_height=True)
    forged_state = _unchecked_replace(candidate.pre_state, pools=(forged_pool,))
    malformed_state_candidate = _unchecked_replace(candidate, pre_state=forged_state)
    stable = _stable_authority(candidate)
    forged_release = _unchecked_replace(stable.release, swap_cap_atoms=True)
    forged_authority = _unchecked_replace(stable, release=forged_release)
    malformed_context = _unchecked_replace(
        candidate.authority,
        stable_authority=forged_authority,
    )
    malformed_authority_candidate = _unchecked_replace(
        candidate,
        authority=malformed_context,
    )

    # Act.
    malformed_state_result = transition_zdex_spot_buyback_v2(malformed_state_candidate)
    malformed_authority_result = transition_zdex_spot_buyback_v2(
        malformed_authority_candidate
    )

    # Assert: semantic revalidation precedes pool selection, arithmetic, and hashing.
    _assert_exact_noop(
        malformed_state_result,
        malformed_state_candidate,
        ZDEXSpotBuybackRejectCodeV2.INPUT_MALFORMED,
    )
    _assert_exact_noop(
        malformed_authority_result,
        malformed_authority_candidate,
        ZDEXSpotBuybackRejectCodeV2.AUTHORITY_MALFORMED,
    )


def test_cross_occurrence_rebinding_changes_port_context_flow_and_terminal_ids() -> None:
    # Arrange.
    first = _candidate()
    stable = _stable_authority(first)
    second_authority = replace(stable, command_occurrence_id=_root(93))
    second_port = replace(first.quote_port, command_occurrence_id=_root(93))
    second = _rebind(first, authority=second_authority, quote_port=second_port)

    # Act.
    first_result = transition_zdex_spot_buyback_v2(first)
    second_result = transition_zdex_spot_buyback_v2(second)

    # Assert.
    assert type(first_result) is ZDEXSpotBuybackAcceptedV2
    assert type(second_result) is ZDEXSpotBuybackAcceptedV2
    first_accepted = first_result
    second_accepted = second_result
    assert first_accepted.quote_port_root != second_accepted.quote_port_root
    assert first_accepted.context.context_root != second_accepted.context.context_root
    assert first_accepted.ports.quote_input.flow_id != second_accepted.ports.quote_input.flow_id
    assert first_accepted.terminal_obligation.obligation_id != second_accepted.terminal_obligation.obligation_id


def test_stateful_stale_head_replay_rejects_without_mutating_the_new_snapshot() -> None:
    # Arrange.
    first = _candidate()
    first_result = transition_zdex_spot_buyback_v2(first)
    assert type(first_result) is ZDEXSpotBuybackAcceptedV2
    stale_candidate = replace(first, pre_state=first_result.post_state)

    # Act.
    stale_result = transition_zdex_spot_buyback_v2(stale_candidate)

    # Assert.
    _assert_exact_noop(
        stale_result,
        stale_candidate,
        ZDEXSpotBuybackRejectCodeV2.STATE_COMMITMENT_MISMATCH,
    )


@settings(max_examples=30, deadline=None)
@given(
    amount_atoms=st.integers(min_value=1, max_value=300),
    reserve0_atoms=st.integers(min_value=500, max_value=2_000),
    reserve1_atoms=st.integers(min_value=500, max_value=2_000),
)
def test_property_transition_is_deterministic_and_preserves_pool_projection(
    amount_atoms: int,
    reserve0_atoms: int,
    reserve1_atoms: int,
) -> None:
    # Arrange.
    candidate = _candidate(
        amount_atoms=amount_atoms,
        minimum_output_atoms=1,
        reserve0_atoms=reserve0_atoms,
        reserve1_atoms=reserve1_atoms,
    )

    # Act.
    first = transition_zdex_spot_buyback_v2(candidate)
    second = transition_zdex_spot_buyback_v2(candidate)

    # Assert.
    assert type(first) is type(second)
    if type(first) is ZDEXSpotBuybackRejectedV2:
        assert type(second) is ZDEXSpotBuybackRejectedV2
        _assert_exact_noop(first, candidate, first.code)
        _assert_exact_noop(second, candidate, second.code)
        return
    assert type(first) is ZDEXSpotBuybackAcceptedV2
    assert type(second) is ZDEXSpotBuybackAcceptedV2
    accepted = first
    repeated = second
    pre_pool = accepted.pre_state.pools[0]
    post_pool = accepted.post_state.pools[0]
    assert accepted.journal.journal_root == repeated.journal.journal_root
    assert post_pool.reserve0_atoms == pre_pool.reserve0_atoms + amount_atoms
    assert post_pool.reserve1_atoms + accepted.journal.purchased_zdex_atoms == pre_pool.reserve1_atoms
    assert accepted.journal.purchased_zdex_atoms == (
        pre_pool.reserve1_atoms * accepted.journal.net_input_atoms
    ) // (pre_pool.reserve0_atoms + accepted.journal.net_input_atoms)


def test_accepted_projection_rederives_and_blocks_private_token_forgery() -> None:
    # Arrange.
    candidate = _candidate()
    result = transition_zdex_spot_buyback_v2(candidate)
    assert type(result) is ZDEXSpotBuybackAcceptedV2
    accepted = result
    forged_terminal = replace(accepted.terminal_obligation, purchased_atoms=1)
    forged_fields = replace(accepted._fields, terminal_obligation=forged_terminal)

    # Act / Assert.
    with pytest.raises(TypeError, match="local rederivation"):
        ZDEXSpotBuybackAcceptedV2(object(), candidate, accepted._fields)
    with pytest.raises(ValueError, match="disagree|does not rederive"):
        ZDEXSpotBuybackAcceptedV2(
            spot_v2._ACCEPTED_TOKEN_V2,
            candidate,
            forged_fields,
        )
    forged = object.__new__(ZDEXSpotBuybackAcceptedV2)
    object.__setattr__(forged, "_subject", candidate)
    object.__setattr__(forged, "_fields", forged_fields)
    with pytest.raises(ValueError, match="disagree|no longer rederives"):
        forged.validate()
    with pytest.raises(AttributeError, match="immutable"):
        accepted._fields = forged_fields


def test_amount_over_u128_is_rejected_by_the_shared_port_constructor() -> None:
    # Arrange.
    candidate = _candidate()

    # Act / Assert.
    with pytest.raises(ValueError, match="unsigned 128-bit"):
        replace(candidate.quote_port, amount_atoms=MAX_ATOMS_V1 + 1)
