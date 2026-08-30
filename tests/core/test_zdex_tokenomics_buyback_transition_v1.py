"""Semantic tests for the bounded Tokenomics-owned ZDEX buyback transition.

RIPR target: one defect at a time must produce the first declared reject,
preserve the identical state object, and emit no effects, ports, or journal.
Accepted tests independently check fee allocation, reserve spend, cadence,
the governed quote output consumed by the real Spot leaf, exact burn, supply
conservation, and commitment roots.  This remains SHADOW evidence, not route
or publication authority.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from typing import Any, TypeVar, cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.zdex_tokenomics_buyback_transition_v1 as tokenomics_transition
from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    EconomicEffectKindV1,
    LaneIdV1,
)
from src.core.zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendStateV1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    FEE_BUYBACK_PRINCIPAL_V1,
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)
from src.core.zdex_hyperdeflation_types_v1 import ZDEXHyperdeflationPolicyV1
from src.core.zdex_spot_buyback_transition_v1 import (
    ZDEXSpotBuybackAcceptedV1,
    ZDEXSpotBuybackAuthorityContextV1,
    ZDEXSpotBuybackInputV1,
    transition_zdex_spot_buyback_v1,
)
from src.core.zdex_tokenomics_buyback_transition_v1 import (
    ZDEXAtomicBuybackQuotePortV2,
    ZDEXTokenomicsBurnRejectCodeV1,
    ZDEXTokenomicsBuybackAcceptedV1,
    ZDEXTokenomicsBuybackAuthorityContextV1,
    ZDEXTokenomicsBuybackInputV1,
    ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentV1,
    ZDEXTokenomicsBuybackLaneStateV1,
    ZDEXTokenomicsBuybackRejectCodeV1,
    ZDEXTokenomicsBuybackRejectedV1,
    ZDEXTokenomicsBuybackReleaseV1,
    ZDEXTokenomicsPrivatePortsV1,
    ZDEXTokenomicsProfileAuthorizationV1,
    ZDEXTokenomicsSafeLimitPortV1,
    ZDEXTokenomicsSupplyControlStateV1,
    derive_zdex_tokenomics_buyback_intent_v1,
    transition_zdex_tokenomics_buyback_v1,
)
from tests.core.test_zdex_spot_buyback_transition_v1 import _candidate as _spot_candidate

T = TypeVar("T")

RejectTuple = tuple[
    ZDEXTokenomicsBuybackRejectCodeV1,
    ZDEXBuybackSpendRejectCodeV1 | None,
    ZDEXFeeAllocationRejectCodeV1 | None,
    ZDEXTokenomicsBurnRejectCodeV1 | None,
]


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


def _spot_authority(spot: ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackAuthorityContextV1:
    authority = spot.authority
    assert type(authority) is ZDEXSpotBuybackAuthorityContextV1
    return authority


def _authority(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
) -> ZDEXTokenomicsBuybackAuthorityContextV1:
    authority = candidate.authority
    assert type(authority) is ZDEXTokenomicsBuybackAuthorityContextV1
    return authority


def _fee_state(
    quote_asset_id: str,
    policy_root: str,
    fee_ingress_atoms: int,
    buyback_reserve_atoms: int,
) -> ZDEXFeeStateV1:
    owned = max(10_000, fee_ingress_atoms + buyback_reserve_atoms)
    return ZDEXFeeStateV1(
        quote_asset_id,
        policy_root,
        fee_ingress_atoms,
        0,
        tuple(
            ZDEXFeeDestinationAmountV1(destination, buyback_reserve_atoms if index == 0 else 0)
            for index, destination in enumerate(ZDEX_FEE_DESTINATIONS_V1)
        ),
        owned,
        owned,
    )


def _intent_input(
    *,
    fee_ingress_atoms: int = 125,
    buyback_reserve_atoms: int = 100,
    live_supply_atoms: int = 1_000,
    remaining_cap_atoms: int = 500,
    safe_limit_atoms: int = 200,
    minimum_spend_atoms: int = 1,
    spend_cap_atoms: int = 200,
    interval_blocks: int = 5,
    last_execution_height: int | None = None,
    decimals: int = 8,
    spot: ZDEXSpotBuybackInputV1 | None = None,
) -> ZDEXTokenomicsBuybackIntentInputV1:
    spot_authority = _spot_authority(spot if spot is not None else _spot_candidate())
    policy = spot_authority.execution_policy
    fee_policy = candidate_zdex_fee_allocation_policy_v1()
    spend_policy = ZDEXBuybackSpendPolicyV1(
        policy.quote_asset_id, minimum_spend_atoms, spend_cap_atoms, interval_blocks
    )
    hyperdeflation = ZDEXHyperdeflationPolicyV1(policy.zdex_asset_id, 1, 10, 38, 8)
    state = ZDEXTokenomicsBuybackLaneStateV1(
        ZDEXTokenomicsSupplyControlStateV1(
            hyperdeflation.asset_id,
            hyperdeflation.policy_root,
            decimals,
            0,
            live_supply_atoms,
            0,
            remaining_cap_atoms,
        ),
        (
            _fee_state(
                policy.quote_asset_id,
                fee_policy.policy_root,
                fee_ingress_atoms,
                buyback_reserve_atoms,
            ),
        ),
        (
            ZDEXBuybackSpendStateV1(
                policy.quote_asset_id, spend_policy.policy_root, last_execution_height
            ),
        ),
        _root(800),
        _root(801),
        _root(802),
        _root(803),
        _root(804),
        _root(805),
    )
    release = ZDEXTokenomicsBuybackReleaseV1(
        spot_authority.tokenomics_module_release_id,
        spot_authority.spot_module_release_id,
        spot_authority.route_release_id,
        64,
    )
    profile = ZDEXTokenomicsProfileAuthorizationV1(
        spot_authority.profile_root,
        spot_authority.chain_id,
        spot_authority.deployment_root,
        spot_authority.route_release_id,
        spot_authority.spot_module_release_id,
        spot_authority.tokenomics_module_release_id,
        release.release_root,
        policy.policy_root,
        fee_policy.policy_root,
        spend_policy.policy_root,
        hyperdeflation.policy_root,
        spot_authority.price_policy.policy_root,
    )
    authority = ZDEXTokenomicsBuybackAuthorityContextV1(
        spot_authority.chain_id,
        spot_authority.deployment_root,
        spot_authority.profile_root,
        profile.authorization_root,
        spot_authority.route_release_id,
        spot_authority.command_occurrence_id,
        spot_authority.global_pre_state_root,
        state.state_root,
        spot_authority.writer_epoch,
        spot_authority.current_height,
        spot_authority.spot_module_release_id,
        spot_authority.tokenomics_module_release_id,
        spot_authority.price_policy.policy_root,
        release,
        policy,
        fee_policy,
        spend_policy,
        hyperdeflation,
        profile,
    )
    port = ZDEXTokenomicsSafeLimitPortV1(
        spot_authority.profile_root,
        spot_authority.route_release_id,
        spot_authority.command_occurrence_id,
        spot_authority.global_pre_state_root,
        state.state_root,
        policy.pool_id,
        policy.quote_asset_id,
        policy.zdex_asset_id,
        spot_authority.price_policy.policy_root,
        spot_authority.oracle_occurrence.occurrence_id,
        _root(7_001),
        spot_authority.current_height,
        safe_limit_atoms,
    )
    return ZDEXTokenomicsBuybackIntentInputV1(authority, state, port)


def _with_state(
    candidate: ZDEXTokenomicsBuybackIntentInputV1,
    state: ZDEXTokenomicsBuybackLaneStateV1,
) -> ZDEXTokenomicsBuybackIntentInputV1:
    root = state.state_root
    return replace(
        candidate,
        authority=replace(_authority(candidate), tokenomics_pre_state_root=root),
        pre_state=state,
        safe_limit_port=replace(candidate.safe_limit_port, tokenomics_pre_state_root=root),
    )


def _with_rebound_profile(
    authority: ZDEXTokenomicsBuybackAuthorityContextV1,
) -> ZDEXTokenomicsBuybackAuthorityContextV1:
    profile = replace(
        authority.profile_authorization,
        release_root=authority.release.release_root,
        execution_policy_root=authority.execution_policy.policy_root,
        fee_policy_root=authority.fee_policy.policy_root,
        spend_policy_root=authority.spend_policy.policy_root,
        hyperdeflation_policy_root=authority.hyperdeflation_policy.policy_root,
        price_policy_root=authority.price_policy_root,
    )
    return replace(
        authority,
        profile_authorization=profile,
        profile_authorization_root=profile.authorization_root,
    )


def _spot_accepted(
    intent: ZDEXTokenomicsBuybackIntentV1,
    spot: ZDEXSpotBuybackInputV1 | None = None,
    *,
    amount_override: int | None = None,
) -> ZDEXSpotBuybackAcceptedV1:
    """Run the real Spot leaf on the governed quote output of the intent.

    Spot V1 consumes the acyclic V2 port fields plus two caller-supplied
    provenance roots (``source_journal_root``, ``source_receipt_binding_root``)
    that the fixture leaves as placeholders.  A Spot V2 port without those
    roots is required work; nothing here claims receipt authentication.
    """

    spot = spot if spot is not None else _spot_candidate()
    quote = intent.quote_output
    amount = quote.amount_atoms if amount_override is None else amount_override
    candidate = replace(
        spot,
        quote_port=replace(
            spot.quote_port,
            source_module_release_id=quote.producer_module_release_id,
            destination_module_release_id=quote.consumer_module_release_id,
            source_pre_state_root=quote.producer_quote_pre_state_root,
            source_post_state_root=quote.producer_quote_post_state_root,
            source_effect_plan_root=quote.producer_quote_effect_plan_root,
            amount_atoms=amount,
        ),
        price_envelope=replace(spot.price_envelope, quote_amount_atoms=amount),
    )
    result = transition_zdex_spot_buyback_v1(candidate)
    assert type(result) is ZDEXSpotBuybackAcceptedV1, getattr(result, "code", None)
    return result


def _spot_minimum_output(quote_atoms: int) -> int:
    """Spot fixture derived minimum: ceil(q * 111 * 10000 / (125 * 11000))."""

    numerator = quote_atoms * 111 * 10_000
    denominator = 125 * 11_000
    return (numerator + denominator - 1) // denominator


def _intent(candidate: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentV1:
    intent = derive_zdex_tokenomics_buyback_intent_v1(candidate)
    assert type(intent) is ZDEXTokenomicsBuybackIntentV1, getattr(intent, "code", None)
    return intent


def _candidate(
    intent_input: ZDEXTokenomicsBuybackIntentInputV1 | None = None,
    spot: ZDEXSpotBuybackInputV1 | None = None,
    *,
    amount_override: int | None = None,
) -> ZDEXTokenomicsBuybackInputV1:
    intent_input = intent_input if intent_input is not None else _intent_input(spot=spot)
    spot_result = _spot_accepted(_intent(intent_input), spot, amount_override=amount_override)
    return ZDEXTokenomicsBuybackInputV1(intent_input, spot_result.terminal_obligation)


def _accepted(candidate: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackAcceptedV1:
    result = transition_zdex_tokenomics_buyback_v1(candidate)
    assert type(result) is ZDEXTokenomicsBuybackAcceptedV1, getattr(result, "code", None)
    return result


def _require_noop(
    rejected: object,
    pre_state: ZDEXTokenomicsBuybackLaneStateV1,
) -> RejectTuple:
    assert type(rejected) is ZDEXTokenomicsBuybackRejectedV1
    assert rejected.pre_state is pre_state
    assert rejected.post_state is pre_state
    assert rejected.effects.is_empty
    assert rejected.ports is None
    assert rejected.journal is None
    return (rejected.code, rejected.spend_code, rejected.fee_code, rejected.burn_code)


def _intent_reject(candidate: ZDEXTokenomicsBuybackIntentInputV1) -> RejectTuple:
    return _require_noop(derive_zdex_tokenomics_buyback_intent_v1(candidate), candidate.pre_state)


def _reject(candidate: ZDEXTokenomicsBuybackInputV1) -> RejectTuple:
    return _require_noop(
        transition_zdex_tokenomics_buyback_v1(candidate),
        candidate.intent_input.pre_state,
    )


def _plain(code: ZDEXTokenomicsBuybackRejectCodeV1) -> RejectTuple:
    return (code, None, None, None)


def _spend(
    spend_code: ZDEXBuybackSpendRejectCodeV1,
    fee_code: ZDEXFeeAllocationRejectCodeV1 | None = None,
) -> RejectTuple:
    return (ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED, spend_code, fee_code, None)


def _burn(burn_code: ZDEXTokenomicsBurnRejectCodeV1) -> RejectTuple:
    return (ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED, None, None, burn_code)


def test_accepts_governed_spend_exact_burn_and_freezes_commitment_roots() -> None:
    # Arrange: F=125 -> b=25, other=67, r=33; B0=100 -> q=min(125, 200, 200)=125.
    candidate = _candidate()

    # Act.
    result = _accepted(candidate)

    # Assert: amounts, supply update, and the seven fixed cross-language roots.
    journal = result.journal
    assert (journal.fee_charged_atoms, journal.buyback_allocation_atoms) == (125, 25)
    assert (journal.other_allocations_atoms, journal.carried_residue_atoms) == (67, 33)
    assert (journal.buyback_reserve_pre_atoms, journal.buyback_reserve_post_atoms) == (100, 0)
    assert (journal.quote_spend_atoms, journal.purchased_zdex_atoms) == (125, 111)
    assert (journal.live_supply_pre_atoms, journal.live_supply_post_atoms) == (1_000, 889)
    assert journal.retained_supply_atoms == 100
    assert (journal.remaining_epoch_burn_cap_pre_atoms, journal.remaining_epoch_burn_cap_post_atoms) == (
        500,
        389,
    )
    assert result.post_state.supply.live_supply_atoms == 889
    assert result.post_state.buyback_cadence_states[0].last_execution_height == 77
    assert result.pre_state.state_root == (
        "0x44548c4fded129f4828955555b716701b5ffff55bb708e9dffdfbe0bdb7e63d0"
    )
    assert journal.context_root == (
        "0xf2045fc3df8081d684d162de7827a0ed29da3f8f00a981e4d9e6bbf3e4dba560"
    )
    assert journal.spend_post_state_root == (
        "0x9350876b5f505828506f098d1bff098b121a86a9857a18a464ac33ec7c5d37fb"
    )
    assert journal.post_state_root == (
        "0xd130b5a2697fccd6e0b9216948c9a181edfe6a0fe200464aee22ce36f1e8a7b7"
    )
    assert journal.spend_effect_plan_root == (
        "0x22edf33b9e3436a4beef01c9fdd4f3b00e68f17e7e5dee4d50c8c0bb883aea06"
    )
    assert journal.quote_port_root == (
        "0x7dc8539d4dda504287cf1a05f01afda38d29ba8f094b2d7dc281b105a2064460"
    )
    assert journal.effect_plan_root == (
        "0x4ecdfd59112a923527512bf6c3790ea12fe1a8b64d0f0582d2348687d196f480"
    )
    assert journal.private_ports_root == (
        "0x251feb17eb4488b50a0c33ff2bca17839104692221380d9819812707078357c8"
    )
    assert journal.discharged_obligation_id == (
        "0x8783d36dbb5bfad76dbf286b2bea269d36da560ef38d1ee8a5107c88fb5536ff"
    )
    assert journal.journal_root == (
        "0x8e63890c22ffb41985e051604df2ab01971500bc0c117328d247b259ee9c0381"
    )
    assert result.quote_output.port_root == journal.quote_port_root
    assert result.ports.ports_root == journal.private_ports_root


def test_intent_is_exact_prefix_of_accepted_transition() -> None:
    # Arrange.
    candidate = _candidate()

    # Act.
    intent = _intent(candidate.intent_input)
    result = _accepted(candidate)

    # Assert: phase A is re-derived unchanged inside phase B.
    assert intent.context_root == result.journal.context_root
    assert intent.quote_output == result.quote_output
    assert intent.spend_post_state == result.spend_post_state
    assert intent.spend_effects == result.spend_effects
    assert intent.spend_effects.lane_writes == ()
    assert intent.spend_post_state.supply == intent.pre_state.supply
    assert intent.quote_output.producer_quote_pre_state_root == intent.pre_state.state_root
    assert intent.quote_output.producer_quote_post_state_root == intent.spend_post_state.state_root
    assert (
        intent.quote_output.producer_quote_effect_plan_root
        == intent.spend_effects.effect_plan_root
    )
    assert intent.quote_output.amount_atoms == intent.spend.intent.quote_spend_atoms
    assert result.journal.quote_port_root == intent.quote_output.port_root
    assert result.journal.spend_post_state_root == intent.spend_post_state.state_root


def test_ports_pair_exactly_with_the_spot_leaf_and_discharge_its_obligation() -> None:
    # Arrange.
    intent_input = _intent_input()
    intent = _intent(intent_input)
    spot = _spot_accepted(intent)
    candidate = ZDEXTokenomicsBuybackInputV1(intent_input, spot.terminal_obligation)

    # Act.
    result = _accepted(candidate)

    # Assert: Lean ExactlyPaired witness plus principal-level pairing.
    assert result.ports.quote_output.amount_atoms == spot.ports.quote_input.amount_atoms
    assert result.ports.burn_input.purchased_atoms == spot.ports.purchased_output.amount_atoms
    assert result.ports.quote_output.source_principal == FEE_BUYBACK_PRINCIPAL_V1
    assert result.ports.quote_output.source_principal == spot.ports.quote_input.source_principal
    assert result.ports.quote_output.destination_principal == (
        spot.ports.quote_input.destination_principal
    )
    assert result.ports.burn_input == spot.terminal_obligation
    assert result.ports.burn_input.burn_principal == spot.ports.purchased_output.destination_principal
    assert result.journal.discharged_obligation_id == spot.terminal_obligation.obligation_id
    assert result.journal.private_ports_root == result.ports.ports_root
    assert result.discharged_obligation == spot.terminal_obligation
    assert spot.journal.purchased_zdex_atoms == result.journal.burned_zdex_atoms
    assert spot.journal.quote_input_atoms == result.quote_output.amount_atoms


def test_effect_plan_has_exact_shape_and_no_ephemeral_port_row() -> None:
    # Arrange.
    candidate = _candidate()

    # Act.
    result = _accepted(candidate)

    # Assert.
    effects = result.effects
    kinds = tuple(row.kind for row in effects.rows)
    assert kinds.count(EconomicEffectKindV1.BURN) == 1
    assert kinds.count(EconomicEffectKindV1.CUSTODY) == 2
    assert kinds.count(EconomicEffectKindV1.RESERVE) == 1
    assert kinds.count(EconomicEffectKindV1.FEE_ALLOCATION) == 5
    assert EconomicEffectKindV1.ACCOUNT_MOVEMENT not in kinds
    burn_principal = result.discharged_obligation.burn_principal
    assert all(row.principal != burn_principal for row in effects.rows)
    reserve_debit = next(
        row
        for row in effects.rows
        if row.kind is EconomicEffectKindV1.CUSTODY and row.principal == FEE_BUYBACK_PRINCIPAL_V1
    )
    assert reserve_debit.delta_atoms == -125
    burn_row = next(row for row in effects.rows if row.kind is EconomicEffectKindV1.BURN)
    assert burn_row.delta_atoms == -111
    assert effects.lane_writes == (
        effects.lane_writes[0],
    ) and effects.lane_writes[0].lane_id is LaneIdV1.ZDEX_TOKENOMICS
    assert effects.lane_writes[0].pre_root == result.pre_state.state_root
    assert effects.lane_writes[0].post_root == result.post_state.state_root
    assert effects.occurrence_consumptions == (_authority(candidate.intent_input).command_occurrence_id,)
    assert effects.external_outbox_enqueue == ()
    assert set(result.spend_effects.rows) < set(effects.rows)
    assert effects.fee_conservation == result.spend_effects.fee_conservation
    supply_row = next(row for row in effects.asset_conservation if row.authorized_burn_atoms)
    assert (supply_row.supply_pre_atoms, supply_row.supply_post_atoms) == (1_000, 889)


def test_one_atom_flows_through_both_leaves() -> None:
    # Arrange: the Spot wide-envelope one-atom fixture and a one-atom safe limit.
    spot = _spot_candidate()
    spot_authority = _spot_authority(spot)
    pool = replace(spot.pre_state.pools[0], reserve0_atoms=501, reserve1_atoms=1_000)
    state = replace(spot.pre_state, pools=(pool,))
    price_policy = replace(
        spot_authority.price_policy,
        minimum_quote_reserve_atoms=1,
        minimum_zdex_reserve_atoms=1,
        maximum_pool_oracle_deviation_bps=9_999,
        maximum_execution_impact_bps=9_999,
        maximum_oracle_execution_deviation_bps=9_999,
    )
    oracle_price = replace(
        spot_authority.oracle_occurrence.price, quote_numerator_atoms=1, zdex_denominator_atoms=1
    )
    oracle = replace(spot_authority.oracle_occurrence, price=oracle_price)
    profile = replace(
        spot_authority.profile_authorization, price_policy_root=price_policy.policy_root
    )
    spot_authority = replace(
        spot_authority,
        spot_pre_state_root=state.state_root,
        price_policy=price_policy,
        profile_authorization=profile,
        profile_authorization_root=profile.authorization_root,
        oracle_registry=replace(spot_authority.oracle_registry, occurrences=(oracle,)),
        oracle_occurrence=oracle,
    )
    spot = replace(
        spot,
        authority=spot_authority,
        pre_state=state,
        quote_port=replace(spot.quote_port, spot_pre_state_root=state.state_root),
        price_envelope=replace(
            spot.price_envelope,
            spot_pre_state_root=state.state_root,
            oracle_occurrence_id=oracle.occurrence_id,
            oracle_quote_numerator_atoms=1,
            oracle_zdex_denominator_atoms=1,
            claimed_route_safe_quote_limit_atoms=100,
            minimum_output_atoms=1,
        ),
    )
    candidate = _candidate(_intent_input(safe_limit_atoms=1, spot=spot), spot)

    # Act.
    result = _accepted(candidate)

    # Assert.
    assert result.journal.quote_spend_atoms == 1
    assert result.journal.burned_zdex_atoms == 1
    assert result.post_state.supply.live_supply_atoms == 999


@pytest.mark.parametrize(
    ("safe_limit_atoms", "spend_cap_atoms", "buyback_reserve_atoms", "expected_spend"),
    (
        (200, 200, 100, 125),
        (124, 200, 100, 124),
        (200, 30, 100, 30),
        (200, 200, 0, 25),
        (1, 200, 100, 1),
    ),
)
def test_spend_selection_is_the_governed_minimum(
    safe_limit_atoms: int,
    spend_cap_atoms: int,
    buyback_reserve_atoms: int,
    expected_spend: int,
) -> None:
    # Arrange.
    candidate = _intent_input(
        safe_limit_atoms=safe_limit_atoms,
        spend_cap_atoms=spend_cap_atoms,
        buyback_reserve_atoms=buyback_reserve_atoms,
    )

    # Act.
    intent = _intent(candidate)

    # Assert: q = min(B0 + b, cap, limit) and B1 = B0 + b - q.
    assert intent.quote_output.amount_atoms == expected_spend
    assert intent.spend.fee_post_state.destination_balances[0].allocation_atoms == (
        buyback_reserve_atoms + 25 - expected_spend
    )


def test_minimum_spend_boundary_is_exact() -> None:
    # Arrange / Act / Assert: q=125 equals the minimum, one atom higher rejects.
    assert _intent(_intent_input(minimum_spend_atoms=125)).quote_output.amount_atoms == 125
    assert _intent_reject(_intent_input(minimum_spend_atoms=126)) == _spend(
        ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM
    )


@pytest.mark.parametrize(
    ("fee_ingress_atoms", "expected"),
    (
        (0, _spend(ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED, ZDEXFeeAllocationRejectCodeV1.ZERO_FEE)),
        (
            MAX_DELTA_ATOMS_V1 + 1,
            _spend(
                ZDEXBuybackSpendRejectCodeV1.FEE_ALLOCATION_REJECTED,
                ZDEXFeeAllocationRejectCodeV1.EFFECT_WIDTH_EXCEEDED,
            ),
        ),
    ),
)
def test_fee_ingress_width_boundaries_reject_without_effects(
    fee_ingress_atoms: int,
    expected: RejectTuple,
) -> None:
    # Arrange / Act / Assert.
    assert _intent_reject(_intent_input(fee_ingress_atoms=fee_ingress_atoms)) == expected


def test_fee_ingress_at_signed_effect_maximum_is_live() -> None:
    # Arrange: the committed ingress is the exact i128 maximum.
    candidate = _intent_input(fee_ingress_atoms=MAX_DELTA_ATOMS_V1)

    # Act.
    intent = _intent(candidate)

    # Assert.
    assert intent.spend.fee_allocation.occurrence.fee_charged_atoms == MAX_DELTA_ATOMS_V1
    assert intent.quote_output.amount_atoms == 200


@pytest.mark.parametrize(
    ("last_execution_height", "expected"),
    (
        (72, None),
        (73, _spend(ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED)),
        (78, _spend(ZDEXBuybackSpendRejectCodeV1.HEIGHT_REGRESSION)),
    ),
)
def test_cadence_boundaries_at_height_77_with_interval_5(
    last_execution_height: int,
    expected: RejectTuple | None,
) -> None:
    # Arrange.
    candidate = _intent_input(last_execution_height=last_execution_height)

    # Act / Assert.
    if expected is None:
        assert _intent(candidate).spend.cadence_post_state.last_execution_height == 77
    else:
        assert _intent_reject(candidate) == expected


@pytest.mark.parametrize(
    ("live_supply_atoms", "remaining_cap_atoms", "expected"),
    (
        (1_000, 111, None),
        (1_000, 110, _burn(ZDEXTokenomicsBurnRejectCodeV1.BURN_EXCEEDS_CAPACITY)),
        (1_000, 0, _burn(ZDEXTokenomicsBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED)),
        (124, 500, None),
        (123, 500, _burn(ZDEXTokenomicsBurnRejectCodeV1.BURN_EXCEEDS_CAPACITY)),
        (1, 500, _burn(ZDEXTokenomicsBurnRejectCodeV1.RETAINED_SUPPLY_FLOOR_REACHED)),
    ),
)
def test_burn_capacity_boundaries_are_exact(
    live_supply_atoms: int,
    remaining_cap_atoms: int,
    expected: RejectTuple | None,
) -> None:
    # Arrange: p=111; retained = ceil(live / 10).
    candidate = _candidate(
        _intent_input(live_supply_atoms=live_supply_atoms, remaining_cap_atoms=remaining_cap_atoms)
    )

    # Act / Assert.
    if expected is None:
        result = _accepted(candidate)
        assert result.journal.live_supply_post_atoms == live_supply_atoms - 111
        assert result.journal.live_supply_post_atoms >= result.journal.retained_supply_atoms
        assert result.journal.remaining_epoch_burn_cap_post_atoms == remaining_cap_atoms - 111
    else:
        assert _reject(candidate) == expected


def test_u64_height_maximum_accepts_and_successor_is_unrepresentable() -> None:
    # Arrange.
    candidate = _intent_input()
    authority = replace(_authority(candidate), current_height=MAX_U64_V1)
    candidate = replace(
        candidate,
        authority=authority,
        safe_limit_port=replace(candidate.safe_limit_port, current_height=MAX_U64_V1),
    )

    # Act / Assert.
    assert _intent(candidate).spend.cadence_post_state.last_execution_height == MAX_U64_V1
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(authority, current_height=MAX_U64_V1 + 1)


@pytest.mark.parametrize("count", (0, 65))
def test_fee_registry_width_boundaries_are_unrepresentable(count: int) -> None:
    # Arrange.
    state = _intent_input().pre_state
    fee_states = tuple(
        replace(state.fee_allocation_states[0], fee_asset_id=_root(10_000 + index))
        for index in range(count)
    )
    cadence_states = tuple(
        replace(state.buyback_cadence_states[0], quote_asset_id=_root(10_000 + index))
        for index in range(count)
    )

    # Act / Assert.
    with pytest.raises(ValueError, match="registry width"):
        replace(state, fee_allocation_states=fee_states, buyback_cadence_states=cadence_states)


def test_lane_state_rejects_cadence_drift_and_supply_asset_collision() -> None:
    # Arrange.
    state = _intent_input().pre_state

    # Act / Assert.
    with pytest.raises(ValueError, match="cadence must cover"):
        replace(state, buyback_cadence_states=())
    with pytest.raises(ValueError, match="cannot also be a fee asset"):
        replace(state, supply=replace(state.supply, asset_id=state.fee_allocation_states[0].fee_asset_id))


IntentMutation = Callable[[ZDEXTokenomicsBuybackIntentInputV1], ZDEXTokenomicsBuybackIntentInputV1]


def _authority_malformed(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return replace(c, authority=object())


def _release_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    authority = _authority(c)
    return replace(c, authority=replace(authority, release=replace(authority.release, fee_asset_count_cap=2)))


def _profile_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return replace(c, authority=replace(_authority(c), profile_authorization_root=_root(9_001)))


def _state_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return replace(c, authority=replace(_authority(c), tokenomics_pre_state_root=_root(9_002)))


def _safety_limit_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return replace(c, safe_limit_port=replace(c.safe_limit_port, selected_pool_id=_root(9_003)))


def _policy_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    authority = _authority(c)
    spend_policy = replace(authority.spend_policy, quote_asset_id=authority.execution_policy.zdex_asset_id)
    return replace(c, authority=_with_rebound_profile(replace(authority, spend_policy=spend_policy)))


def _lane_malformed(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return _with_state(c, replace(c.pre_state, supply=replace(c.pre_state.supply, decimals=39)))


def _supply_policy_drift(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return _with_state(c, replace(c.pre_state, supply=replace(c.pre_state.supply, policy_root=_root(9_004))))


def _selection_mismatch(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    fee_state = replace(c.pre_state.fee_allocation_states[0], policy_root=_root(9_005))
    return _with_state(c, replace(c.pre_state, fee_allocation_states=(fee_state,)))


def _cooldown(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    cadence = replace(c.pre_state.buyback_cadence_states[0], last_execution_height=77)
    return _with_state(c, replace(c.pre_state, buyback_cadence_states=(cadence,)))


def _safe_limit_zero(c: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentInputV1:
    return replace(c, safe_limit_port=replace(c.safe_limit_port, route_safe_quote_limit_atoms=0))


@pytest.mark.parametrize(
    ("mutate", "expected"),
    (
        (_authority_malformed, _plain(ZDEXTokenomicsBuybackRejectCodeV1.AUTHORITY_MALFORMED)),
        (_release_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH)),
        (_profile_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PROFILE_MISMATCH)),
        (_state_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.STATE_COMMITMENT_MISMATCH)),
        (_safety_limit_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.SAFETY_LIMIT_MISMATCH)),
        (_policy_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.POLICY_MISMATCH)),
        (_lane_malformed, _plain(ZDEXTokenomicsBuybackRejectCodeV1.LANE_MALFORMED)),
        (_supply_policy_drift, _plain(ZDEXTokenomicsBuybackRejectCodeV1.LANE_MALFORMED)),
        (_selection_mismatch, _plain(ZDEXTokenomicsBuybackRejectCodeV1.SELECTION_MISMATCH)),
        (_cooldown, _spend(ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED)),
        (_safe_limit_zero, _spend(ZDEXBuybackSpendRejectCodeV1.ROUTE_SAFE_LIMIT_ZERO)),
    ),
)
def test_each_intent_guard_has_a_mutation_killing_noop(
    mutate: IntentMutation,
    expected: RejectTuple,
) -> None:
    # Arrange.
    candidate = mutate(_intent_input())

    # Act / Assert: the intent and the full transition reject identically.
    assert _intent_reject(candidate) == expected
    obligation = _candidate().spot_obligation
    assert _reject(ZDEXTokenomicsBuybackInputV1(candidate, obligation)) == expected


ObligationMutation = Callable[[ZDEXTokenomicsBuybackInputV1], ZDEXTokenomicsBuybackInputV1]


def _obligation(candidate: ZDEXTokenomicsBuybackInputV1) -> Any:
    return candidate.spot_obligation


def _foreign_obligation(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=object())


def _wrong_consumer(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), consumer_module_release_id=_root(9_006)))


def _wrong_burn_asset(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), burn_asset=_root(9_007)))


def _wrong_burn_principal(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), burn_principal="mallory:burn-port"))


def _wrong_pool(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), selected_pool_id=_root(9_008)))


def _forged_purchase_amount(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), purchased_atoms=1))


def _forged_quote_flow(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return replace(c, spot_obligation=replace(_obligation(c), quote_input_flow_id=_root(9_009)))


def _spot_ran_with_smaller_quote(c: ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackInputV1:
    return _candidate(c.intent_input, amount_override=124)


@pytest.mark.parametrize(
    ("mutate", "expected"),
    (
        (_foreign_obligation, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_wrong_consumer, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_wrong_burn_asset, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_wrong_burn_principal, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_wrong_pool, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_forged_purchase_amount, _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)),
        (_forged_quote_flow, _plain(ZDEXTokenomicsBuybackRejectCodeV1.QUOTE_FLOW_MISMATCH)),
        (_spot_ran_with_smaller_quote, _plain(ZDEXTokenomicsBuybackRejectCodeV1.QUOTE_FLOW_MISMATCH)),
    ),
)
def test_each_purchase_port_guard_has_a_mutation_killing_noop(
    mutate: ObligationMutation,
    expected: RejectTuple,
) -> None:
    # Arrange.
    candidate = mutate(_candidate())

    # Act / Assert.
    assert _reject(candidate) == expected


def test_release_reject_precedes_profile_and_later_failures() -> None:
    # Arrange: combine two independent defects.
    candidate = _profile_mismatch(_release_mismatch(_intent_input()))

    # Act / Assert.
    assert _intent_reject(candidate) == _plain(ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH)


def test_spend_reject_precedes_purchase_port_and_burn_failures() -> None:
    # Arrange: cooldown plus a forged obligation plus an exhausted epoch cap.
    base = _candidate(_intent_input(remaining_cap_atoms=0))
    candidate = _wrong_consumer(replace(base, intent_input=_cooldown(base.intent_input)))

    # Act / Assert.
    assert _reject(candidate) == _spend(ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED)


def test_purchase_port_reject_precedes_burn_failure() -> None:
    # Arrange.
    candidate = _wrong_consumer(_candidate(_intent_input(remaining_cap_atoms=0)))

    # Act / Assert.
    assert _reject(candidate) == _plain(ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH)


def test_reversed_asset_order_is_a_policy_mismatch_before_lane_validation() -> None:
    # Arrange: keep every earlier binding coherent while reversing the
    # governed quote/ZDEX order so only the canonical-order guard can fire.
    candidate = _intent_input()
    authority = _authority(candidate)
    policy = replace(
        authority.execution_policy,
        quote_asset_id=authority.execution_policy.zdex_asset_id,
        zdex_asset_id=authority.execution_policy.quote_asset_id,
    )
    spend_policy = replace(authority.spend_policy, quote_asset_id=policy.quote_asset_id)
    hyperdeflation = replace(authority.hyperdeflation_policy, asset_id=policy.zdex_asset_id)
    authority = _with_rebound_profile(
        replace(
            authority,
            execution_policy=policy,
            spend_policy=spend_policy,
            hyperdeflation_policy=hyperdeflation,
        )
    )
    candidate = replace(
        candidate,
        authority=authority,
        safe_limit_port=replace(
            candidate.safe_limit_port,
            quote_asset_id=policy.quote_asset_id,
            zdex_asset_id=policy.zdex_asset_id,
        ),
    )

    # Act / Assert.
    assert _intent_reject(candidate) == _plain(ZDEXTokenomicsBuybackRejectCodeV1.POLICY_MISMATCH)


def test_cross_occurrence_substitution_changes_both_flow_identities() -> None:
    # Arrange.
    first = _candidate()
    spot = _spot_candidate()
    spot_authority = _spot_authority(spot)
    second_occurrence = _root(93)
    second_spot = replace(
        spot,
        authority=replace(spot_authority, command_occurrence_id=second_occurrence),
        quote_port=replace(spot.quote_port, command_occurrence_id=second_occurrence),
        price_envelope=replace(spot.price_envelope, command_occurrence_id=second_occurrence),
    )
    second = _candidate(_intent_input(spot=second_spot), second_spot)

    # Act.
    first_result = _accepted(first)
    second_result = _accepted(second)

    # Assert.
    assert first_result.quote_output.port_root != second_result.quote_output.port_root
    assert first_result.ports.ports_root != second_result.ports.ports_root
    assert first_result.journal.discharged_obligation_id != (
        second_result.journal.discharged_obligation_id
    )
    assert first_result.journal.context_root != second_result.journal.context_root


@settings(max_examples=100, deadline=None, derandomize=True)
@given(
    fee_ingress_atoms=st.integers(min_value=1, max_value=1_000_000),
    buyback_reserve_atoms=st.integers(min_value=0, max_value=1_000_000),
    safe_limit_atoms=st.integers(min_value=1, max_value=1_000_000),
    spend_cap_atoms=st.integers(min_value=1, max_value=1_000_000),
)
def test_generated_spend_selection_is_deterministic_and_conserved(
    fee_ingress_atoms: int,
    buyback_reserve_atoms: int,
    safe_limit_atoms: int,
    spend_cap_atoms: int,
) -> None:
    # Arrange.
    candidate = _intent_input(
        fee_ingress_atoms=fee_ingress_atoms,
        buyback_reserve_atoms=buyback_reserve_atoms,
        safe_limit_atoms=safe_limit_atoms,
        spend_cap_atoms=spend_cap_atoms,
    )
    buyback_allocation = fee_ingress_atoms * 2_000 // 10_000
    expected_spend = min(buyback_reserve_atoms + buyback_allocation, spend_cap_atoms, safe_limit_atoms)

    # Act.
    first = derive_zdex_tokenomics_buyback_intent_v1(candidate)
    second = derive_zdex_tokenomics_buyback_intent_v1(candidate)

    # Assert.
    if expected_spend == 0:
        assert _intent_reject(candidate) == _spend(ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM)
        return
    assert type(first) is ZDEXTokenomicsBuybackIntentV1
    assert type(second) is ZDEXTokenomicsBuybackIntentV1
    occurrence = first.spend.fee_allocation.occurrence
    assert first.quote_output == second.quote_output
    assert first.spend == second.spend
    assert first.quote_output.amount_atoms == expected_spend
    assert occurrence.buyback_quote_atoms == buyback_allocation
    assert occurrence.fee_charged_atoms == (
        sum(row.allocation_atoms for row in occurrence.allocations) + occurrence.carried_residue_atoms
    )
    reserve_post = first.spend.fee_post_state.destination_balances[0].allocation_atoms
    assert reserve_post + expected_spend == buyback_reserve_atoms + buyback_allocation
    assert first.spend_post_state.fee_allocation_states[0].fee_ingress_atoms == 0


@settings(max_examples=100, deadline=None, derandomize=True)
@given(safe_limit_atoms=st.integers(min_value=10, max_value=50))
def test_generated_full_transitions_conserve_supply_and_pair_ports(
    safe_limit_atoms: int,
) -> None:
    # Arrange: a Spot pool holding twice as much ZDEX as quote at Oracle 1/2.
    spot = _spot_candidate()
    spot_authority = _spot_authority(spot)
    pool = replace(spot.pre_state.pools[0], reserve0_atoms=1_000, reserve1_atoms=2_000)
    state = replace(spot.pre_state, pools=(pool,))
    oracle_price = replace(
        spot_authority.oracle_occurrence.price, quote_numerator_atoms=1, zdex_denominator_atoms=2
    )
    oracle = replace(spot_authority.oracle_occurrence, price=oracle_price)
    spot_authority = replace(
        spot_authority,
        spot_pre_state_root=state.state_root,
        oracle_registry=replace(spot_authority.oracle_registry, occurrences=(oracle,)),
        oracle_occurrence=oracle,
    )
    purchased = 2_000 * safe_limit_atoms // (1_000 + safe_limit_atoms)
    spot = replace(
        spot,
        authority=spot_authority,
        pre_state=state,
        quote_port=replace(spot.quote_port, spot_pre_state_root=state.state_root),
        price_envelope=replace(
            spot.price_envelope,
            spot_pre_state_root=state.state_root,
            oracle_occurrence_id=oracle.occurrence_id,
            oracle_quote_numerator_atoms=1,
            oracle_zdex_denominator_atoms=2,
            claimed_route_safe_quote_limit_atoms=200,
            minimum_output_atoms=(safe_limit_atoms * 2 * 10_000 + 10_999) // 11_000,
        ),
    )
    intent_input = _intent_input(safe_limit_atoms=safe_limit_atoms, live_supply_atoms=100_000, spot=spot)
    intent = _intent(intent_input)
    spot_result = _spot_accepted(intent, spot)
    candidate = ZDEXTokenomicsBuybackInputV1(intent_input, spot_result.terminal_obligation)

    # Act.
    result = _accepted(candidate)

    # Assert.
    assert result.journal.quote_spend_atoms == safe_limit_atoms
    assert result.journal.burned_zdex_atoms == purchased
    assert result.post_state.supply.live_supply_atoms == 100_000 - purchased
    assert result.ports.quote_output.amount_atoms == spot_result.ports.quote_input.amount_atoms
    assert result.ports.burn_input.purchased_atoms == spot_result.ports.purchased_output.amount_atoms
    burn_row = next(row for row in result.effects.rows if row.kind is EconomicEffectKindV1.BURN)
    assert burn_row.delta_atoms == -purchased


def test_two_occurrence_history_carries_the_reserve_and_rejects_replay() -> None:
    # Arrange: occurrence A at height 77 with F=125, B0=100.
    first = _candidate()
    first_result = _accepted(first)
    assert first_result.journal.buyback_reserve_post_atoms == 0

    # Act 1: replaying occurrence A against its own post-state at the same
    # height is a cadence no-op, and re-running A itself is idempotent.
    replay = ZDEXTokenomicsBuybackInputV1(
        _with_state(first.intent_input, first_result.post_state),
        first.spot_obligation,
    )
    assert _reject(replay) == _spend(ZDEXBuybackSpendRejectCodeV1.COOLDOWN_NOT_ELAPSED)
    assert _accepted(first).journal == first_result.journal

    # Act 2: occurrence B at height 82 with a fresh F=125 and a 60-atom limit.
    spot = _spot_candidate()
    spot_authority = _spot_authority(spot)
    second_occurrence = _root(93)
    second_spot = replace(
        spot,
        authority=replace(
            spot_authority, command_occurrence_id=second_occurrence, current_height=82
        ),
        quote_port=replace(spot.quote_port, command_occurrence_id=second_occurrence),
        price_envelope=replace(
            spot.price_envelope, command_occurrence_id=second_occurrence, current_height=82
        ),
    )
    second_spot_authority = _spot_authority(second_spot)
    oracle_price = replace(second_spot_authority.oracle_occurrence.price, observed_height=81)
    oracle = replace(second_spot_authority.oracle_occurrence, price=oracle_price)
    second_spot = replace(
        second_spot,
        authority=replace(
            second_spot_authority,
            oracle_registry=replace(second_spot_authority.oracle_registry, occurrences=(oracle,)),
            oracle_occurrence=oracle,
        ),
        price_envelope=replace(
            second_spot.price_envelope,
            oracle_occurrence_id=oracle.occurrence_id,
            oracle_observed_height=81,
            minimum_output_atoms=_spot_minimum_output(25),
        ),
    )
    carried = first_result.post_state
    refilled = replace(
        carried,
        fee_allocation_states=(
            replace(carried.fee_allocation_states[0], fee_ingress_atoms=125),
        ),
    )
    second_input = _with_state(_intent_input(safe_limit_atoms=60, spot=second_spot), refilled)
    second = _candidate(second_input, second_spot)

    # Assert: B0' = B1 = 0, b' = 25, q' = min(25, 200, 60) = 25, supply keeps falling.
    second_result = _accepted(second)
    assert second_result.journal.buyback_reserve_pre_atoms == 0
    assert second_result.journal.quote_spend_atoms == 25
    assert second_result.journal.live_supply_pre_atoms == 889
    assert second_result.post_state.supply.live_supply_atoms == 889 - second_result.journal.burned_zdex_atoms
    assert second_result.post_state.buyback_cadence_states[0].last_execution_height == 82
    assert second_result.effects.lane_writes[0].pre_root == refilled.state_root
    assert replace(refilled, fee_allocation_states=carried.fee_allocation_states) == carried


def test_accepted_result_rederives_and_rejects_private_token_forgery() -> None:
    candidate = _candidate()
    result = _accepted(candidate)
    result.validate()
    with pytest.raises(TypeError, match="local rederivation"):
        ZDEXTokenomicsBuybackAcceptedV1(object(), candidate, object())  # type: ignore[arg-type]
    with pytest.raises(AttributeError, match="immutable"):
        result._fields = object()  # type: ignore[assignment]
    with pytest.raises(TypeError, match="exact typed values"):
        ZDEXTokenomicsPrivatePortsV1(result.ports.quote_output, result.ports.quote_output)
    with pytest.raises(ValueError, match="exact role pair"):
        ZDEXTokenomicsPrivatePortsV1(
            replace(result.ports.quote_output, selected_pool_id=_root(9_010)),
            result.ports.burn_input,
        )

    forged_journal = replace(
        result.journal,
        purchased_zdex_atoms=1,
        burned_zdex_atoms=1,
        live_supply_post_atoms=result.journal.live_supply_pre_atoms - 1,
        remaining_epoch_burn_cap_post_atoms=result.journal.remaining_epoch_burn_cap_pre_atoms - 1,
    )
    forged_fields = replace(result._fields, journal=forged_journal)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXTokenomicsBuybackAcceptedV1(
            tokenomics_transition._ACCEPTED_TOKEN_V1, candidate, forged_fields
        )
    forged = object.__new__(ZDEXTokenomicsBuybackAcceptedV1)
    object.__setattr__(forged, "_subject", candidate)
    object.__setattr__(forged, "_fields", forged_fields)
    with pytest.raises(ValueError, match="no longer rederives"):
        forged.validate()

    class AlwaysEqual:
        def __eq__(self, other: object) -> bool:
            return True

    hostile_fields = replace(result._fields, ports=AlwaysEqual())  # type: ignore[arg-type]
    hostile = object.__new__(ZDEXTokenomicsBuybackAcceptedV1)
    object.__setattr__(hostile, "_subject", candidate)
    object.__setattr__(hostile, "_fields", hostile_fields)
    with pytest.raises(TypeError, match="owned graph is not closed"):
        hostile.validate()

    false_burn_journal = _unchecked_replace(result.journal, burned_zdex_atoms=True)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXTokenomicsBuybackAcceptedV1(
            tokenomics_transition._ACCEPTED_TOKEN_V1,
            candidate,
            replace(result._fields, journal=false_burn_journal),
        )

    cyclic_journal = _unchecked_replace(result.journal)
    object.__setattr__(cyclic_journal, "context_root", cyclic_journal)
    cyclic = object.__new__(ZDEXTokenomicsBuybackAcceptedV1)
    object.__setattr__(cyclic, "_subject", candidate)
    object.__setattr__(cyclic, "_fields", replace(result._fields, journal=cyclic_journal))
    with pytest.raises(ValueError, match="contains a cycle"):
        cyclic.validate()

    oversized_journal = _unchecked_replace(
        result.journal, context_root=tuple("x" for _ in range(4_097))
    )
    oversized = object.__new__(ZDEXTokenomicsBuybackAcceptedV1)
    object.__setattr__(oversized, "_subject", candidate)
    object.__setattr__(oversized, "_fields", replace(result._fields, journal=oversized_journal))
    with pytest.raises(ValueError, match="exceeds node budget"):
        oversized.validate()


def test_intent_result_rederives_and_rejects_quote_output_forgery() -> None:
    candidate = _intent_input()
    intent = _intent(candidate)
    intent.validate()
    with pytest.raises(TypeError, match="local rederivation"):
        ZDEXTokenomicsBuybackIntentV1(object(), candidate, object())  # type: ignore[arg-type]
    forged_quote = replace(intent.quote_output, amount_atoms=124)
    with pytest.raises(ValueError, match="does not rederive"):
        ZDEXTokenomicsBuybackIntentV1(
            tokenomics_transition._ACCEPTED_TOKEN_V1,
            candidate,
            replace(intent._fields, quote_output=forged_quote),
        )
    forged = object.__new__(ZDEXTokenomicsBuybackIntentV1)
    object.__setattr__(forged, "_subject", candidate)
    object.__setattr__(forged, "_fields", replace(intent._fields, quote_output=forged_quote))
    with pytest.raises(ValueError, match="no longer rederives"):
        forged.validate()


def test_rejected_value_cannot_carry_inconsistent_phase_codes() -> None:
    state = _intent_input().pre_state
    with pytest.raises(ValueError, match="phase codes"):
        ZDEXTokenomicsBuybackRejectedV1(
            ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED, None, None, None, state, state
        )
    with pytest.raises(ValueError, match="phase codes"):
        ZDEXTokenomicsBuybackRejectedV1(
            ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH,
            None,
            ZDEXFeeAllocationRejectCodeV1.ZERO_FEE,
            None,
            state,
            state,
        )
    with pytest.raises(ValueError, match="phase codes"):
        ZDEXTokenomicsBuybackRejectedV1(
            ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH,
            None,
            None,
            ZDEXTokenomicsBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED,
            state,
            state,
        )


def test_fee_policy_share_registry_keeps_hosting_compensation_separate_from_burn() -> None:
    # Arrange: raising the hosting share to 100% suppresses the buyback
    # allocation and therefore the spend, without any zero-bounty branch.
    candidate = _intent_input(buyback_reserve_atoms=0)
    authority = _authority(candidate)
    shares = tuple(
        ZDEXFeeShareV1(share.destination, 10_000 if index == 1 else 0)
        for index, share in enumerate(authority.fee_policy.shares)
    )
    fee_policy = replace(authority.fee_policy, shares=shares)
    fee_state = replace(candidate.pre_state.fee_allocation_states[0], policy_root=fee_policy.policy_root)
    candidate = _with_state(
        replace(candidate, authority=_with_rebound_profile(replace(authority, fee_policy=fee_policy))),
        replace(candidate.pre_state, fee_allocation_states=(fee_state,)),
    )

    # Act / Assert: no reserve means no spend and no burn, never a silent skip.
    assert _intent_reject(candidate) == _spend(ZDEXBuybackSpendRejectCodeV1.SPEND_BELOW_MINIMUM)
    assert candidate.pre_state.fee_allocation_states[0].destination_balances[1].allocation_atoms == 0


def test_quote_port_v2_is_acyclic_and_proof_independent() -> None:
    # Arrange / Act / Assert: the port carries no journal or receipt-binding
    # root, so no hash fixed point can form with the module journal or an
    # opaque verified leaf wrapper that later commits this port.
    names = {field.name for field in dataclass_fields(ZDEXAtomicBuybackQuotePortV2)}
    assert names == {
        "profile_root",
        "route_release_id",
        "command_occurrence_id",
        "global_pre_state_root",
        "producer_module_release_id",
        "consumer_module_release_id",
        "producer_quote_pre_state_root",
        "producer_quote_post_state_root",
        "producer_quote_effect_plan_root",
        "selected_pool_id",
        "quote_asset_id",
        "amount_atoms",
    }
    assert not any("journal" in name or "receipt" in name for name in names)
    result = _accepted(_candidate())
    port = result.quote_output
    assert result.journal.quote_port_root == port.port_root
    with pytest.raises(ValueError, match="quote phase must change"):
        replace(
            port,
            producer_quote_post_state_root=port.producer_quote_pre_state_root,
        )
    with pytest.raises(ValueError, match="module releases must differ"):
        replace(port, consumer_module_release_id=port.producer_module_release_id)
    assert MAX_ATOMS_V1 > MAX_DELTA_ATOMS_V1
