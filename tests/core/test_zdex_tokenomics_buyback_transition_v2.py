"""Semantic and adversarial evidence for the Tokenomics V2 buyback leaf.

The tests bind Phase A, Spot V2, and Phase B as deterministic SHADOW data.
They grant no receipt provenance, route authority, settlement, or publication
claim. Those obligations remain with authenticated composition.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from typing import Any, TypeVar, cast

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import src.core.zdex_tokenomics_buyback_transition_v2 as tokenomics_v2
from src.core.global_settlement_types_v1 import (
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
)
from src.core.zdex_buyback_spend_v1 import ZDEXBuybackSpendRejectCodeV1
from src.core.zdex_purchase_burn_route_types_v1 import zdex_pool_reserve_principal_v1
from src.core.zdex_spot_buyback_transition_v1 import ZDEXSpotFlowRoleV1
from src.core.zdex_spot_buyback_transition_v2 import (
    ZDEXSpotBuybackAcceptedV2,
    ZDEXSpotBuybackContextV2,
    ZDEXSpotFlowIdentityV2,
    ZDEXSpotTerminalObligationV2,
    transition_zdex_spot_buyback_v2,
)
from src.core.zdex_tokenomics_buyback_transition_v1 import (
    ZDEXTokenomicsBurnRejectCodeV1,
    ZDEXTokenomicsBuybackInputV1,
    ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentV1,
    ZDEXTokenomicsBuybackRejectCodeV1,
    derive_zdex_tokenomics_buyback_intent_v1,
    transition_zdex_tokenomics_buyback_v1,
)
from src.core.zdex_tokenomics_buyback_transition_v2 import (
    ZDEXTokenomicsBuybackAcceptedV2,
    ZDEXTokenomicsBuybackInputV2,
    ZDEXTokenomicsBuybackJournalV2,
    ZDEXTokenomicsBuybackRejectedV2,
    transition_zdex_tokenomics_buyback_v2,
)
from tests.core.test_zdex_spot_buyback_transition_v2 import _candidate as _spot_candidate
from tests.core.test_zdex_spot_buyback_transition_v2 import _rebind as _spot_rebind
from tests.core.test_zdex_tokenomics_buyback_transition_v1 import (
    _authority_malformed,
    _cooldown,
    _intent_input,
    _lane_malformed,
    _policy_mismatch,
    _profile_mismatch,
    _release_mismatch,
    _root,
    _safe_limit_zero,
    _safety_limit_mismatch,
    _selection_mismatch,
    _state_mismatch,
    _with_state,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v1 import (
    _candidate as _v1_candidate,
)

T = TypeVar("T")
IntentMutation = Callable[[ZDEXTokenomicsBuybackIntentInputV1], ZDEXTokenomicsBuybackIntentInputV1]


def _unchecked_replace(value: T, **updates: object) -> T:
    forged = object.__new__(type(value))
    for field in dataclass_fields(cast(Any, type(value))):
        object.__setattr__(
            forged,
            field.name,
            updates.get(field.name, object.__getattribute__(value, field.name)),
        )
    return forged


def _spot_accepted(intent_input: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXSpotBuybackAcceptedV2:
    intent = derive_zdex_tokenomics_buyback_intent_v1(intent_input)
    assert type(intent) is ZDEXTokenomicsBuybackIntentV1
    candidate = _spot_rebind(_spot_candidate(), quote_port=intent.quote_output)
    result = transition_zdex_spot_buyback_v2(candidate)
    assert type(result) is ZDEXSpotBuybackAcceptedV2
    return result


def _candidate(
    intent_input: ZDEXTokenomicsBuybackIntentInputV1 | None = None,
) -> ZDEXTokenomicsBuybackInputV2:
    actual = _intent_input() if intent_input is None else intent_input
    return ZDEXTokenomicsBuybackInputV2(
        actual,
        _spot_accepted(actual).terminal_obligation,
    )


def _accepted(candidate: ZDEXTokenomicsBuybackInputV2) -> ZDEXTokenomicsBuybackAcceptedV2:
    result = transition_zdex_tokenomics_buyback_v2(candidate)
    assert type(result) is ZDEXTokenomicsBuybackAcceptedV2, getattr(result, "code", None)
    result.validate()
    return result


def _assert_noop(
    result: object,
    candidate: ZDEXTokenomicsBuybackInputV2,
    code: ZDEXTokenomicsBuybackRejectCodeV1,
) -> ZDEXTokenomicsBuybackRejectedV2:
    assert type(result) is ZDEXTokenomicsBuybackRejectedV2
    assert result.code is code
    assert result.pre_state is candidate.intent_input.pre_state
    assert result.post_state is candidate.intent_input.pre_state
    assert result.effects.is_empty
    assert result.ports is None
    assert result.journal is None
    result.validate()
    return result


def _rebind_terminal(
    candidate: ZDEXTokenomicsBuybackInputV2,
    *,
    context: ZDEXSpotBuybackContextV2 | None = None,
    post_state_root: str | None = None,
) -> ZDEXSpotTerminalObligationV2:
    terminal = candidate.spot_obligation
    assert type(terminal) is ZDEXSpotTerminalObligationV2
    authority = candidate.intent_input.authority
    policy = authority.execution_policy
    quote = derive_zdex_tokenomics_buyback_intent_v1(candidate.intent_input).quote_output
    actual_context = terminal.context if context is None else context
    quote_flow = ZDEXSpotFlowIdentityV2(
        ZDEXSpotFlowRoleV1.QUOTE_INPUT,
        actual_context,
        terminal.selected_pool_id,
        policy.quote_asset_id,
        quote.source_principal,
        quote.destination_principal,
        quote.amount_atoms,
    )
    purchased_flow = ZDEXSpotFlowIdentityV2(
        ZDEXSpotFlowRoleV1.PURCHASED_ZDEX_OUTPUT,
        actual_context,
        terminal.selected_pool_id,
        terminal.burn_asset,
        zdex_pool_reserve_principal_v1(
            pool_id=terminal.selected_pool_id,
            asset_id=terminal.burn_asset,
        ),
        terminal.burn_principal,
        terminal.purchased_atoms,
    )
    return replace(
        terminal,
        context=actual_context,
        post_state_root=(
            terminal.post_state_root if post_state_root is None else post_state_root
        ),
        quote_input_flow_id=quote_flow.flow_id,
        purchased_output_flow_id=purchased_flow.flow_id,
    )


def test_accepts_same_occurrence_and_burns_exact_purchased_atoms() -> None:
    # Arrange.
    candidate = _candidate()
    pre_supply = candidate.intent_input.pre_state.supply

    # Act.
    accepted = _accepted(candidate)

    # Assert.
    journal = accepted.journal
    assert type(journal) is ZDEXTokenomicsBuybackJournalV2
    assert journal.quote_port_root == accepted.quote_output.port_root
    assert journal.discharged_obligation_id == accepted.discharged_obligation.obligation_id
    assert journal.purchased_zdex_atoms == journal.burned_zdex_atoms == 111
    assert journal.live_supply_pre_atoms == pre_supply.live_supply_atoms == 1_000
    assert journal.live_supply_post_atoms == 889
    assert journal.remaining_epoch_burn_cap_pre_atoms == 500
    assert journal.remaining_epoch_burn_cap_post_atoms == 389
    assert journal.retained_supply_atoms == 100
    burns = tuple(
        row for row in accepted.effects.rows if row.kind is EconomicEffectKindV1.BURN
    )
    assert len(burns) == 1 and burns[0].delta_atoms == -111
    assert len(accepted.effects.lane_writes) == 1
    assert accepted.effects.lane_writes[0].lane_id is LaneIdV1.ZDEX_TOKENOMICS


def test_v2_journal_is_a_new_exact_schema_with_frozen_root() -> None:
    # Arrange / Act.
    accepted = _accepted(_candidate())

    # Assert.
    assert accepted.journal.to_canonical()["schema"] == (
        tokenomics_v2.ZDEX_TOKENOMICS_TRANSITION_JOURNAL_SCHEMA_V2
    )
    assert {
        "ports_root": accepted.ports.ports_root,
        "journal_root": accepted.journal.journal_root,
        "effect_plan_root": accepted.effects.effect_plan_root,
        "post_state_root": accepted.post_state.state_root,
        "lane_coordination_obligation_root": (
            accepted.journal.lane_coordination_obligation_root
        ),
    } == {
        "ports_root": "0x5a3d04c739a9dd512a06ae615302a4cd594df9ae8ef2ace948fa44162e8e7700",
        "journal_root": "0xb831c2c882dabcb28b3876067626a121f5003d9e12e289512893ac9347cbf341",
        "effect_plan_root": "0x4ecdfd59112a923527512bf6c3790ea12fe1a8b64d0f0582d2348687d196f480",
        "post_state_root": "0xd130b5a2697fccd6e0b9216948c9a181edfe6a0fe200464aee22ce36f1e8a7b7",
        "lane_coordination_obligation_root": (
            "0xb3a804a59299dd1349592fafec630720031217d4b3340a385a345d544d4b4553"
        ),
    }
    v1 = transition_zdex_tokenomics_buyback_v1(_v1_candidate())
    assert type(v1).__name__ == "ZDEXTokenomicsBuybackAcceptedV1"
    assert accepted.journal.journal_root != v1.journal.journal_root
    assert accepted.ports.ports_root != v1.ports.ports_root


@pytest.mark.parametrize(
    ("mutate", "code"),
    (
        (_authority_malformed, ZDEXTokenomicsBuybackRejectCodeV1.AUTHORITY_MALFORMED),
        (_release_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.RELEASE_MISMATCH),
        (_profile_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.PROFILE_MISMATCH),
        (_state_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.STATE_COMMITMENT_MISMATCH),
        (_safety_limit_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.SAFETY_LIMIT_MISMATCH),
        (_policy_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.POLICY_MISMATCH),
        (_lane_malformed, ZDEXTokenomicsBuybackRejectCodeV1.LANE_MALFORMED),
        (_selection_mismatch, ZDEXTokenomicsBuybackRejectCodeV1.SELECTION_MISMATCH),
        (_cooldown, ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED),
        (_safe_limit_zero, ZDEXTokenomicsBuybackRejectCodeV1.SPEND_REJECTED),
    ),
)
def test_phase_a_rejections_map_to_v2_without_effects(
    mutate: IntentMutation,
    code: ZDEXTokenomicsBuybackRejectCodeV1,
) -> None:
    # Arrange.
    valid = _candidate()
    candidate = ZDEXTokenomicsBuybackInputV2(
        mutate(_intent_input()),
        valid.spot_obligation,
    )

    # Act / Assert.
    rejected = _assert_noop(
        transition_zdex_tokenomics_buyback_v2(candidate),
        candidate,
        code,
    )
    if mutate in (_cooldown, _safe_limit_zero):
        assert type(rejected.spend_code) is ZDEXBuybackSpendRejectCodeV1


def test_each_shared_occurrence_coordinate_is_required() -> None:
    # Arrange.
    base = _candidate()
    terminal = cast(ZDEXSpotTerminalObligationV2, base.spot_obligation)
    context_mutations = (
        replace(terminal.context, chain_id="foreign-chain"),
        replace(terminal.context, deployment_root=_root(21_001)),
        replace(terminal.context, writer_epoch=terminal.context.writer_epoch + 1),
        replace(terminal.context, current_height=terminal.context.current_height + 1),
        replace(terminal.context, spot_module_release_id=_root(21_002)),
        replace(terminal.context, tokenomics_module_release_id=_root(21_003)),
        replace(terminal.context, execution_policy_root=_root(21_004)),
        replace(terminal.context, price_policy_root=_root(21_005)),
        replace(terminal.context, oracle_occurrence_id=_root(21_006)),
    )
    coordinate_updates = (
        {"profile_root": _root(22_001)},
        {"route_release_id": _root(22_002)},
        {"command_occurrence_id": _root(22_003)},
        {"global_pre_state_root": _root(22_004)},
        {"producer_quote_pre_state_root": _root(22_005)},
        {"producer_quote_post_state_root": _root(22_006)},
        {"producer_quote_effect_plan_root": _root(22_007)},
        {"quote_port_root": _root(22_008)},
    )
    contexts = (*context_mutations, *(
        replace(terminal.context, coordinates=replace(terminal.context.coordinates, **update))
        for update in coordinate_updates
    ))

    # Act / Assert.
    for context in contexts:
        obligation = _rebind_terminal(base, context=context)
        candidate = replace(base, spot_obligation=obligation)
        _assert_noop(
            transition_zdex_tokenomics_buyback_v2(candidate),
            candidate,
            ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH,
        )


def test_wrong_version_and_forged_terminal_values_are_exact_noops() -> None:
    # Arrange.
    candidate = _candidate()
    v1_terminal = _v1_candidate().spot_obligation
    terminal = cast(ZDEXSpotTerminalObligationV2, candidate.spot_obligation)
    forged = _unchecked_replace(terminal, purchased_atoms=0)

    # Act / Assert.
    for value in (object(), v1_terminal, forged):
        actual = replace(candidate, spot_obligation=value)
        _assert_noop(
            transition_zdex_tokenomics_buyback_v2(actual),
            actual,
            ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH,
        )

    v1_candidate = _v1_candidate()
    crossed = ZDEXTokenomicsBuybackInputV1(
        v1_candidate.intent_input,
        candidate.spot_obligation,
    )
    v1_rejected = transition_zdex_tokenomics_buyback_v1(crossed)
    assert v1_rejected.code is ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH


@pytest.mark.parametrize(
    ("cap", "expected"),
    (
        (111, None),
        (110, ZDEXTokenomicsBurnRejectCodeV1.BURN_EXCEEDS_CAPACITY),
        (0, ZDEXTokenomicsBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED),
    ),
)
def test_epoch_cap_boundary_is_exact(
    cap: int,
    expected: ZDEXTokenomicsBurnRejectCodeV1 | None,
) -> None:
    # Arrange.
    original = _intent_input()
    state = replace(
        original.pre_state,
        supply=replace(original.pre_state.supply, remaining_epoch_burn_cap_atoms=cap),
    )
    candidate = _candidate(_with_state(original, state))

    # Act / Assert.
    result = transition_zdex_tokenomics_buyback_v2(candidate)
    if expected is None:
        assert type(result) is ZDEXTokenomicsBuybackAcceptedV2
        assert result.journal.remaining_epoch_burn_cap_post_atoms == 0
    else:
        rejected = _assert_noop(
            result,
            candidate,
            ZDEXTokenomicsBuybackRejectCodeV1.BURN_REJECTED,
        )
        assert rejected.burn_code is expected


@settings(max_examples=20, deadline=None)
@given(
    live_supply=st.integers(min_value=124, max_value=10_000),
    cap=st.integers(min_value=111, max_value=10_000),
)
def test_property_exact_burn_conserves_supply_and_epoch_capacity(
    live_supply: int,
    cap: int,
) -> None:
    # Arrange.
    original = _intent_input()
    state = replace(
        original.pre_state,
        supply=replace(
            original.pre_state.supply,
            live_supply_atoms=live_supply,
            remaining_epoch_burn_cap_atoms=cap,
        ),
    )
    candidate = _candidate(_with_state(original, state))

    # Act.
    result = transition_zdex_tokenomics_buyback_v2(candidate)

    # Assert.
    assert type(result) is ZDEXTokenomicsBuybackAcceptedV2
    journal = result.journal
    assert journal.burned_zdex_atoms == 111
    assert journal.live_supply_post_atoms + 111 == live_supply
    assert journal.remaining_epoch_burn_cap_post_atoms + 111 == cap
    assert journal.live_supply_post_atoms >= journal.retained_supply_atoms


def test_rejected_v2_is_deeply_validated_fresh_and_projection_free() -> None:
    # Arrange.
    candidate = replace(_candidate(), spot_obligation=object())

    # Act.
    first = _assert_noop(
        transition_zdex_tokenomics_buyback_v2(candidate),
        candidate,
        ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH,
    )
    second = _assert_noop(
        transition_zdex_tokenomics_buyback_v2(candidate),
        candidate,
        ZDEXTokenomicsBuybackRejectCodeV1.PURCHASE_PORT_MISMATCH,
    )

    # Assert.
    assert first.effects is not second.effects
    forged_plan = _unchecked_replace(
        GlobalEconomicEffectPlanV1.empty(),
        rows=(object(),),
    )
    for update, error in (
        ({"effects": object()}, TypeError),
        ({"effects": forged_plan}, TypeError),
        ({"ports": object()}, ValueError),
        ({"journal": object()}, ValueError),
    ):
        with pytest.raises(error):
            _unchecked_replace(first, **update).validate()


def test_accepted_wrapper_rederives_and_refuses_forged_journal() -> None:
    # Arrange.
    candidate = _candidate()
    accepted = _accepted(candidate)
    forged_journal = replace(accepted.journal, spot_post_state_root=_root(30_001))
    forged_fields = replace(accepted._fields, journal=forged_journal)

    # Act / Assert.
    with pytest.raises(TypeError, match="local rederivation"):
        ZDEXTokenomicsBuybackAcceptedV2(object(), candidate, accepted._fields)
    with pytest.raises(ValueError, match="disagree|does not rederive"):
        ZDEXTokenomicsBuybackAcceptedV2(
            tokenomics_v2._ACCEPTED_TOKEN_V2,
            candidate,
            forged_fields,
        )


def test_leaf_records_but_does_not_claim_route_owned_spot_provenance() -> None:
    """M16 nonclaim: receipt-authenticated composition owns these coordinates."""

    # Arrange.
    candidate = _candidate()
    terminal = cast(ZDEXSpotTerminalObligationV2, candidate.spot_obligation)
    foreign_coordinates = replace(
        terminal.context.coordinates,
        spot_pre_state_root=_root(31_001),
    )
    foreign_context = replace(
        terminal.context,
        coordinates=foreign_coordinates,
        profile_authorization_root=_root(31_002),
        release_root=_root(31_003),
        oracle_registry_root=_root(31_004),
    )
    foreign_terminal = _rebind_terminal(
        candidate,
        context=foreign_context,
        post_state_root=_root(31_005),
    )

    # Act.
    accepted = _accepted(replace(candidate, spot_obligation=foreign_terminal))

    # Assert: the leaf binds the supplied values for a future authenticated route.
    assert accepted.journal.spot_context_root == foreign_context.context_root
    assert accepted.journal.spot_post_state_root == _root(31_005)
