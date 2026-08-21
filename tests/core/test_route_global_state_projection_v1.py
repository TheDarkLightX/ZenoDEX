"""RIPR evidence for the profile-selected route/full-state projection obligation.

The direct oracle compares selected lane entries with their journals and every
unselected pre/post lane entry for exact equality. Cross-language golden roots
then detect canonical encoding drift without granting either test authority.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import (
    LaneCompositionJournalV1,
    RouteCompositionJournalV1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    GlobalEconomicStateV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    LaneStateRootV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
)
from src.core.route_global_state_projection_v1 import (
    RouteGlobalStateProjectionCandidateV1,
    RouteGlobalStateProjectionV1,
    project_route_global_state_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _active_evidence() -> tuple[EvidenceStatusV1, ...]:
    return tuple(
        sorted(
            (
                EvidenceStatusV1.SPECIFIED,
                EvidenceStatusV1.IMPLEMENTED,
                EvidenceStatusV1.PROVED,
                EvidenceStatusV1.MOUNTED,
                EvidenceStatusV1.TESTED,
                EvidenceStatusV1.TERMINAL_COMPLETE,
                EvidenceStatusV1.MIGRATABLE,
                EvidenceStatusV1.NO_BYPASS,
                EvidenceStatusV1.RELEASE_BACKED,
            ),
            key=lambda item: item.value,
        )
    )


def _lane_release(lane_id: LaneIdV1, ordinal: int) -> LaneModuleReleaseV1:
    selected = lane_id in {LaneIdV1.ASSET_TRANSFER, LaneIdV1.ZDEX_TOKENOMICS}
    offset = ordinal * 32
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-projection-test",
        state_schema_root=_root(100 + offset),
        command_variants=("PROJECT_ROUTE_STATE",) if selected else (),
        terminal_command_variants=(),
        guest_image_id=_root(101 + offset),
        specification_root=_root(102 + offset),
        source_root=_root(103 + offset),
        toolchain_root=_root(104 + offset),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if selected else ReleaseStatusV1.SHADOW,
        accepts_new_objects=selected,
        evidence_statuses=(
            _active_evidence()
            if selected
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
) -> LaneCoordinatorReleaseV1:
    selected = lane_id in {LaneIdV1.ASSET_TRANSFER, LaneIdV1.ZDEX_TOKENOMICS}
    offset = ordinal * 32
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version="1.0.0-projection-test",
        coordinator_schema_root=_root(700 + offset),
        guest_image_id=_root(701 + offset),
        specification_root=_root(702 + offset),
        source_root=_root(703 + offset),
        toolchain_root=_root(704 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if selected else ReleaseStatusV1.SHADOW,
        accepts_new_objects=selected,
        evidence_statuses=(
            _active_evidence()
            if selected
            else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _profile() -> tuple[EconomicProfileSnapshotV1, RouteReleaseV1]:
    lanes = LaneRegistryV1(
        tuple(
            _lane_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    coordinators = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(lane_id, ordinal)
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    selected_lanes = (LaneIdV1.ASSET_TRANSFER, LaneIdV1.ZDEX_TOKENOMICS)
    route = RouteReleaseV1.build(
        semantic_version="1.0.0-projection-test",
        command_kind="PROJECT_ROUTE_STATE",
        ordered_lanes=selected_lanes,
        module_release_ids=tuple(lanes.release_for(lane).release_id for lane in selected_lanes),
        dependency_roles=("VALUE_OWNER", "FEE_SINK"),
        port_schema_roots=(_root(1_201), _root(1_202)),
        guest_image_id=_root(1_203),
        specification_root=_root(1_204),
        source_root=_root(1_205),
        toolchain_root=_root(1_206),
        oracle_policy_root=_root(1_207),
        issue_burn_policy_root=_root(1_208),
        max_cycles=2_000_000,
        max_journal_bytes=131_072,
        status=ReleaseStatusV1.ACTIVE_NEW,
        accepts_new_objects=True,
        evidence_statuses=_active_evidence(),
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=17,
        lane_registry=lanes,
        lane_coordinator_registry=coordinators,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(1_301),
        root_image_id=_root(1_302),
        verifier_registry_root=_root(1_303),
        migration_registry_root=_root(1_304),
        policy_registry_root=_root(1_305),
        terminal_registry_root=_root(1_306),
        status=ProfileStatusV1.ACTIVE,
    )
    return profile, route


def _state(
    profile: EconomicProfileSnapshotV1,
    *,
    selected_root_delta: int,
) -> GlobalEconomicStateV1:
    lane_roots = tuple(
        LaneStateRootV1(
            lane_id=release.lane_id,
            module_release_id=release.release_id,
            enabled=release.accepts_new_objects,
            state_root=_root(
                2_000
                + ordinal
                + (selected_root_delta if release.accepts_new_objects else 0)
            ),
        )
        for ordinal, release in enumerate(profile.lane_registry.releases, start=1)
    )
    return GlobalEconomicStateV1(
        chain_id="zeno-projection-test",
        deployment_root=_root(1_400),
        writer_epoch=profile.authority_epoch,
        height=41,
        profile_root=profile.profile_id,
        lane_roots=lane_roots,
    )


def _candidate() -> RouteGlobalStateProjectionCandidateV1:
    profile, route = _profile()
    pre_state = _state(profile, selected_root_delta=0)
    post_state = _state(profile, selected_root_delta=10_000)
    occurrence_id = _root(1_500)
    lane_journals = tuple(
        LaneCompositionJournalV1(
            chain_id=pre_state.chain_id,
            deployment_root=pre_state.deployment_root,
            profile_root=profile.profile_id,
            writer_epoch=profile.authority_epoch,
            lane_id=lane_id,
            coordinator_release_id=profile.lane_coordinator_registry.release_for(
                lane_id
            ).coordinator_release_id,
            command_occurrence_id=occurrence_id,
            ordered_module_journal_roots=(_root(1_600 + index),),
            pre_lane_root=pre_state.lane_roots[ALL_LANE_IDS_V1.index(lane_id)].state_root,
            post_lane_root=post_state.lane_roots[ALL_LANE_IDS_V1.index(lane_id)].state_root,
            effect_plan_root=_root(1_700 + index),
            terminal_obligations_root=_root(1_800 + index),
        )
        for index, lane_id in enumerate(route.ordered_lanes)
    )
    route_journal = RouteCompositionJournalV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence_id,
        ordered_lane_journal_roots=tuple(item.journal_root for item in lane_journals),
        pre_state_root=pre_state.state_root,
        post_state_root=post_state.state_root,
        effect_plan_root=_root(1_900),
        terminal_obligations_root=_root(1_901),
    )
    return RouteGlobalStateProjectionCandidateV1(
        profile=profile,
        route=route,
        lane_journals=lane_journals,
        route_journal=route_journal,
        pre_state=pre_state,
        post_state=post_state,
    )


def _replace_lane(
    state: GlobalEconomicStateV1,
    lane_id: LaneIdV1,
    **changes: object,
) -> GlobalEconomicStateV1:
    index = ALL_LANE_IDS_V1.index(lane_id)
    roots = list(state.lane_roots)
    roots[index] = replace(roots[index], **changes)
    return replace(state, lane_roots=tuple(roots))


def test_projection_is_opaque_and_matches_cross_language_golden_root() -> None:
    candidate = _candidate()

    projection = project_route_global_state_v1(candidate)

    assert projection.ordered_lane_ids == candidate.route.ordered_lanes
    assert projection.pre_state_root == candidate.pre_state.state_root
    assert projection.post_state_root == candidate.post_state.state_root
    assert projection.projection_root == (
        "0x11a9c2b222c1c9019efd6803b96bec024f4db47f50087e11bdf389093d46ded7"
    )
    with pytest.raises(TypeError, match="checker-constructed"):
        RouteGlobalStateProjectionV1(object(), projection._fields)


def test_projection_rejects_inactive_profile() -> None:
    candidate = _candidate()

    with pytest.raises(ValueError, match="profile is not ACTIVE"):
        project_route_global_state_v1(
            replace(candidate, profile=replace(candidate.profile, status=ProfileStatusV1.SHADOW))
        )


def test_projection_revalidates_hostile_post_construction_profile_mutation() -> None:
    candidate = _candidate()
    object.__setattr__(candidate.profile, "authority_epoch", 18)

    with pytest.raises(ValueError, match="profile_id is not the exact content-derived id"):
        project_route_global_state_v1(candidate)


def test_projection_revalidates_hostile_route_journal_mutation() -> None:
    candidate = _candidate()
    object.__setattr__(candidate.route_journal, "effect_plan_root", _root(0))

    with pytest.raises(ValueError, match="effect_plan_root"):
        project_route_global_state_v1(candidate)


def test_projection_revalidates_hostile_global_state_mutation() -> None:
    candidate = _candidate()
    object.__setattr__(candidate.post_state, "balances", ({"forged": 1},))

    with pytest.raises(TypeError, match="invalid value"):
        project_route_global_state_v1(candidate)


def test_projection_revalidates_hostile_nested_lane_root_mutation() -> None:
    candidate = _candidate()
    object.__setattr__(candidate.post_state.lane_roots[0], "state_root", "malformed")

    with pytest.raises(ValueError, match="canonical lowercase"):
        project_route_global_state_v1(candidate)


@pytest.mark.parametrize(
    ("field", "value", "message"),
    (
        ("profile_root", _root(9_000), "route journal profile mismatch"),
        ("writer_epoch", 18, "route journal writer epoch mismatch"),
    ),
)
def test_projection_rejects_route_journal_profile_or_epoch_substitution(
    field: str,
    value: object,
    message: str,
) -> None:
    candidate = _candidate()

    with pytest.raises(ValueError, match=message):
        project_route_global_state_v1(
            replace(candidate, route_journal=replace(candidate.route_journal, **{field: value}))
        )


@pytest.mark.parametrize("field", ("pre_state_root", "post_state_root"))
def test_projection_rejects_global_root_substitution(field: str) -> None:
    candidate = _candidate()
    route_journal = replace(candidate.route_journal, **{field: _root(9_001)})

    with pytest.raises(ValueError, match="global state root mismatch"):
        project_route_global_state_v1(replace(candidate, route_journal=route_journal))


@pytest.mark.parametrize("side", ("pre", "post"))
def test_projection_rejects_selected_lane_root_substitution(side: str) -> None:
    candidate = _candidate()
    journal = candidate.lane_journals[0]
    field = "pre_lane_root" if side == "pre" else "post_lane_root"
    journals = (replace(journal, **{field: _root(9_002)}), candidate.lane_journals[1])
    route_journal = replace(
        candidate.route_journal,
        ordered_lane_journal_roots=tuple(item.journal_root for item in journals),
    )

    with pytest.raises(ValueError, match="selected lane root mismatch"):
        project_route_global_state_v1(
            replace(candidate, lane_journals=journals, route_journal=route_journal)
        )


def test_projection_rejects_hidden_unselected_lane_change() -> None:
    candidate = _candidate()
    post_state = _replace_lane(
        candidate.post_state,
        LaneIdV1.PERPS_MARKET,
        state_root=_root(9_003),
    )
    route_journal = replace(candidate.route_journal, post_state_root=post_state.state_root)

    with pytest.raises(ValueError, match="unselected lane changed"):
        project_route_global_state_v1(
            replace(candidate, post_state=post_state, route_journal=route_journal)
        )


@pytest.mark.parametrize(
    ("field", "value", "message"),
    (
        ("module_release_id", _root(9_004), "lane release mismatch"),
        ("enabled", True, "enabled flag"),
    ),
)
def test_projection_rejects_global_lane_metadata_drift(
    field: str,
    value: object,
    message: str,
) -> None:
    candidate = _candidate()
    post_state = _replace_lane(
        candidate.post_state,
        LaneIdV1.PERPS_MARKET,
        **{field: value},
    )
    route_journal = replace(candidate.route_journal, post_state_root=post_state.state_root)

    with pytest.raises(ValueError, match=message):
        project_route_global_state_v1(
            replace(candidate, post_state=post_state, route_journal=route_journal)
        )


@pytest.mark.parametrize(
    ("field", "value", "message"),
    (
        ("chain_id", "other-chain", "chain mismatch"),
        ("deployment_root", _root(9_005), "deployment mismatch"),
        ("writer_epoch", 18, "writer epoch mismatch"),
    ),
)
def test_projection_rejects_post_state_context_drift(
    field: str,
    value: object,
    message: str,
) -> None:
    candidate = _candidate()
    post_state = replace(candidate.post_state, **{field: value})
    route_journal = replace(candidate.route_journal, post_state_root=post_state.state_root)

    with pytest.raises(ValueError, match=message):
        project_route_global_state_v1(
            replace(candidate, post_state=post_state, route_journal=route_journal)
        )


def test_projection_rejects_lane_journal_reorder_duplicate_and_omission() -> None:
    candidate = _candidate()
    variants = (
        tuple(reversed(candidate.lane_journals)),
        (candidate.lane_journals[0], candidate.lane_journals[0]),
        candidate.lane_journals[:1],
    )

    for journals in variants:
        with pytest.raises(ValueError, match="lane journal (count|order) mismatch"):
            project_route_global_state_v1(
                replace(candidate, lane_journals=journals)
            )


def test_projection_rejects_route_and_coordinator_substitution() -> None:
    candidate = _candidate()
    wrong_route = replace(candidate.route, semantic_version="forged-display-version")
    wrong_lane = replace(candidate.lane_journals[0], coordinator_release_id=_root(9_006))
    wrong_lanes = (wrong_lane, candidate.lane_journals[1])
    wrong_journal = replace(
        candidate.route_journal,
        ordered_lane_journal_roots=tuple(item.journal_root for item in wrong_lanes),
    )

    with pytest.raises(ValueError, match="governed route mismatch"):
        project_route_global_state_v1(replace(candidate, route=wrong_route))
    with pytest.raises(ValueError, match="coordinator release mismatch"):
        project_route_global_state_v1(
            replace(candidate, lane_journals=wrong_lanes, route_journal=wrong_journal)
        )


def test_projection_root_changes_for_coherent_selected_lane_transition() -> None:
    candidate = _candidate()
    original = project_route_global_state_v1(candidate)
    changed_post = _replace_lane(
        candidate.post_state,
        LaneIdV1.ASSET_TRANSFER,
        state_root=_root(9_007),
    )
    changed_lanes = (
        replace(candidate.lane_journals[0], post_lane_root=_root(9_007)),
        candidate.lane_journals[1],
    )
    changed_route = replace(
        candidate.route_journal,
        ordered_lane_journal_roots=tuple(item.journal_root for item in changed_lanes),
        post_state_root=changed_post.state_root,
    )

    changed = project_route_global_state_v1(
        replace(
            candidate,
            post_state=changed_post,
            lane_journals=changed_lanes,
            route_journal=changed_route,
        )
    )

    assert changed.projection_root != original.projection_root
