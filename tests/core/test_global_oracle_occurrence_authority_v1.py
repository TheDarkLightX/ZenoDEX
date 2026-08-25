"""RIPR evidence for route-bound Oracle occurrence authority.

The independent oracle is the explicit relation among the governed route
policy, command occurrence, and exact global pre-state.  These tests preserve
named mutants for omitted consumption, stale data, future data, caller-selected
policy, and stale-head acceptance.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_oracle_occurrence_authority_v1 import (
    GlobalOracleOccurrenceAuthorityCandidateV1,
    GlobalOracleOccurrenceAuthorityV1,
    GlobalOracleOccurrencePolicyV1,
    verify_global_oracle_occurrence_authority_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ReleaseStatusV1,
    RouteReleaseV1,
)
from src.core.oracle_current_dispute_status_v1 import (
    build_oracle_current_dispute_status_v1,
    current_dispute_status_root_from_global_authority_v1,
    global_root_from_current_dispute_status_root_v1,
    verify_oracle_current_dispute_status_v1,
)

ORACLE_ID = "zenodex.oracle.current-dispute-status.v1"
COMMAND_KIND = "PERPS_SETTLE_EPOCH"


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _policy(*, max_age_blocks: int = 2) -> GlobalOracleOccurrencePolicyV1:
    return GlobalOracleOccurrencePolicyV1(
        oracle_id=ORACLE_ID,
        max_observation_age_blocks=max_age_blocks,
    )


def _route(policy: GlobalOracleOccurrencePolicyV1) -> RouteReleaseV1:
    return RouteReleaseV1.build(
        semantic_version="1.0.0-oracle-authority-test",
        command_kind=COMMAND_KIND,
        ordered_lanes=(LaneIdV1.PERPS_MARKET,),
        module_release_ids=(_root(101),),
        dependency_roles=("PERPS_SETTLEMENT",),
        port_schema_roots=(_root(102),),
        guest_image_id=_root(103),
        specification_root=_root(104),
        source_root=_root(105),
        toolchain_root=_root(106),
        oracle_policy_root=policy.policy_root,
        issue_burn_policy_root=_root(107),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )


def _state(
    *,
    observed_height: int = 39,
    finalized: bool = True,
    occurrence_root: str | None = None,
) -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="zeno-oracle-authority-test",
        deployment_root=_root(201),
        writer_epoch=7,
        height=41,
        profile_root=_root(202),
        lane_roots=tuple(
            LaneStateRootV1(
                lane_id=lane_id,
                module_release_id=_root(300 + index),
                enabled=lane_id is LaneIdV1.PERPS_MARKET,
                state_root=_root(400 + index),
            )
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
        oracle_occurrences=(
            OracleOccurrenceStateV1(
                oracle_id=ORACLE_ID,
                occurrence_root=occurrence_root or _root(501),
                observed_height=observed_height,
                finalized=finalized,
            ),
        ),
    )


def _occurrence(
    state: GlobalEconomicStateV1,
    route: RouteReleaseV1,
    *,
    consumed_object_ids: tuple[str, ...] = (ORACLE_ID,),
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id=state.chain_id,
        deployment_root=state.deployment_root,
        height=state.height + 1,
        tx_index=0,
        op_index=0,
        command_kind=route.command_kind,
        command_body_hash=_root(601),
        route_release_id=route.route_release_id,
        subject_id="perps-settlement-operator",
        grant_root=_root(602),
        nonce=1,
        profile_root=state.profile_root,
        pre_state_root=state.state_root,
        consumed_object_ids=consumed_object_ids,
    )


def _candidate(
    *,
    state: GlobalEconomicStateV1 | None = None,
    policy: GlobalOracleOccurrencePolicyV1 | None = None,
) -> GlobalOracleOccurrenceAuthorityCandidateV1:
    selected_policy = policy or _policy()
    selected_state = state or _state()
    selected_route = _route(selected_policy)
    return GlobalOracleOccurrenceAuthorityCandidateV1(
        pre_state=selected_state,
        route=selected_route,
        occurrence=_occurrence(selected_state, selected_route),
        policy=selected_policy,
    )


def test_given_exact_route_boundary_when_verified_then_authority_is_state_bound() -> None:
    # Arrange: age two is the policy's exact accepted maximum.
    candidate = _candidate(state=_state(observed_height=39))

    # Act.
    authority = verify_global_oracle_occurrence_authority_v1(candidate)

    # Assert: the witness identifies every authority-bearing coordinate.
    assert authority.pre_state_root == candidate.pre_state.state_root
    assert authority.route_release_id == candidate.route.route_release_id
    assert authority.command_occurrence_id == candidate.occurrence.occurrence_id
    assert authority.policy_root == candidate.policy.policy_root
    assert authority.oracle_id == ORACLE_ID
    assert authority.occurrence_root == _root(501)
    assert authority.observed_height == 39
    assert authority.state_height == 41
    assert authority.observation_age_blocks == 2
    assert candidate.policy.policy_root == (
        "0xe9236ce39308b70f6b2e762c8c87a1fda35d384e2a582067be108f693d3fda79"
    )
    assert authority.authority_root == (
        "0xd10e4381d237f3d467672934e0f38513148bd32c067a4853ef66c28a5c271486"
    )
    assert current_dispute_status_root_from_global_authority_v1(authority) == (
        "sha256:" + f"{501:064x}"
    )


def test_one_block_past_maximum_age_is_rejected() -> None:
    candidate = _candidate(state=_state(observed_height=38))

    with pytest.raises(ValueError, match="oracle occurrence exceeds governed freshness policy"):
        verify_global_oracle_occurrence_authority_v1(candidate)


def test_zero_age_policy_accepts_same_height_and_rejects_previous_height() -> None:
    policy = _policy(max_age_blocks=0)
    exact = _candidate(state=_state(observed_height=41), policy=policy)
    stale = _candidate(state=_state(observed_height=40), policy=policy)

    assert verify_global_oracle_occurrence_authority_v1(exact).observation_age_blocks == 0
    with pytest.raises(ValueError, match="oracle occurrence exceeds governed freshness policy"):
        verify_global_oracle_occurrence_authority_v1(stale)


def test_future_observation_is_rejected() -> None:
    candidate = _candidate(state=_state(observed_height=42))

    with pytest.raises(ValueError, match="oracle occurrence observed height is in the future"):
        verify_global_oracle_occurrence_authority_v1(candidate)


def test_unfinalized_occurrence_is_rejected() -> None:
    candidate = _candidate(state=_state(finalized=False))

    with pytest.raises(ValueError, match="oracle occurrence is not finalized"):
        verify_global_oracle_occurrence_authority_v1(candidate)


def test_omitted_consumption_declaration_is_rejected() -> None:
    candidate = _candidate()
    hostile = replace(
        candidate,
        occurrence=_occurrence(candidate.pre_state, candidate.route, consumed_object_ids=()),
    )

    with pytest.raises(
        ValueError,
        match="command does not consume route-bound oracle occurrence",
    ):
        verify_global_oracle_occurrence_authority_v1(hostile)


def test_missing_committed_occurrence_is_rejected() -> None:
    candidate = _candidate()
    state_without_oracle = replace(candidate.pre_state, oracle_occurrences=())
    hostile = replace(
        candidate,
        pre_state=state_without_oracle,
        occurrence=replace(candidate.occurrence, pre_state_root=state_without_oracle.state_root),
    )

    with pytest.raises(
        ValueError,
        match="route-bound oracle occurrence is absent from pre-state",
    ):
        verify_global_oracle_occurrence_authority_v1(hostile)


def test_caller_selected_more_permissive_policy_is_rejected() -> None:
    candidate = _candidate(state=_state(observed_height=38))
    caller_policy = _policy(max_age_blocks=3)
    hostile = replace(candidate, policy=caller_policy)

    with pytest.raises(ValueError, match="route oracle policy root mismatch"):
        verify_global_oracle_occurrence_authority_v1(hostile)


def test_stale_head_race_is_rejected_before_authority_construction() -> None:
    candidate = _candidate()
    raced_state = replace(candidate.pre_state, history_root=_root(999))
    hostile = replace(candidate, pre_state=raced_state)

    with pytest.raises(ValueError, match="command pre-state root mismatch"):
        verify_global_oracle_occurrence_authority_v1(hostile)


def test_authority_constructor_is_checker_owned() -> None:
    with pytest.raises(TypeError, match="checker-constructed"):
        GlobalOracleOccurrenceAuthorityV1(object(), object())


def test_object_new_cannot_forge_oracle_authority() -> None:
    # Arrange: bypass __init__, as a hostile in-process caller can attempt.
    forged = object.__new__(GlobalOracleOccurrenceAuthorityV1)

    # Act / Assert: no authority field or root can be observed from the forgery.
    with pytest.raises(TypeError, match="checker-registered"):
        _ = forged.authority_root


def test_current_dispute_status_bridge_rejects_other_oracle_authority() -> None:
    other_oracle_id = "zenodex.oracle.other-finalized-occurrence.v1"
    other_policy = GlobalOracleOccurrencePolicyV1(
        oracle_id=other_oracle_id,
        max_observation_age_blocks=2,
    )
    other_route = _route(other_policy)
    base_state = _state()
    other_state = replace(
        base_state,
        oracle_occurrences=(
            replace(base_state.oracle_occurrences[0], oracle_id=other_oracle_id),
        ),
    )
    other_occurrence = _occurrence(
        other_state,
        other_route,
        consumed_object_ids=(other_oracle_id,),
    )
    authority = verify_global_oracle_occurrence_authority_v1(
        GlobalOracleOccurrenceAuthorityCandidateV1(
            pre_state=other_state,
            route=other_route,
            occurrence=other_occurrence,
            policy=other_policy,
        )
    )

    with pytest.raises(ValueError, match="different Oracle occurrence"):
        current_dispute_status_root_from_global_authority_v1(authority)


def test_global_pre_state_authority_selects_exact_current_status_witness() -> None:
    report_id = "sha256:" + "a1" * 32
    status = build_oracle_current_dispute_status_v1(
        report_ids=(report_id,),
        dispute_entries=(),
        as_of_epoch=7,
    )
    global_status_root = global_root_from_current_dispute_status_root_v1(
        status["current_dispute_status_root"]
    )
    candidate = _candidate(state=_state(occurrence_root=global_status_root))

    authority = verify_global_oracle_occurrence_authority_v1(candidate)
    check = verify_oracle_current_dispute_status_v1(
        status,
        expected_report_ids=(report_id,),
        expected_root=current_dispute_status_root_from_global_authority_v1(authority),
        now_epoch=7,
    )

    assert check.ok is True
    assert check.errors == ()

    substituted_status = {**status, "current_dispute_status_root": "sha256:" + "f1" * 32}
    substituted_check = verify_oracle_current_dispute_status_v1(
        substituted_status,
        expected_report_ids=(report_id,),
        expected_root=current_dispute_status_root_from_global_authority_v1(authority),
        now_epoch=7,
    )
    assert substituted_check.ok is False
    assert "current dispute status root mismatch" in substituted_check.errors
    assert (
        "current dispute status root does not match verifier-selected root"
        in substituted_check.errors
    )


def test_policy_rejects_bool_disguised_as_integer_age() -> None:
    with pytest.raises(TypeError, match="max observation age blocks must be an int"):
        GlobalOracleOccurrencePolicyV1(
            oracle_id=ORACLE_ID,
            max_observation_age_blocks=True,
        )
