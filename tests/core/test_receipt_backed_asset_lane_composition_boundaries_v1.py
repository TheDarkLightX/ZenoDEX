from __future__ import annotations

import hashlib
import re
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Callable

import pytest

import src.core.receipt_backed_asset_lane_composition_v1 as composition_module
from src.core.asset_lane_projection_v1 import AssetLaneModuleCompatibilityV1
from src.core.global_settlement_types_v1 import ProfileStatusV1
from src.core.receipt_backed_asset_lane_composition_v1 import (
    LaneCompositionAuthorityLevelV1,
    ReceiptBackedAssetLaneCompositionCandidateV1,
    compose_receipt_backed_asset_lane_single_v1,
)
from tests.core import test_lane_module_release_route_binding_v1 as support


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _candidate() -> ReceiptBackedAssetLaneCompositionCandidateV1:
    profile, occurrence, _, accepted, verified, coordinator_context = (
        support._verified_transfer_and_coordinator_context()
    )
    return ReceiptBackedAssetLaneCompositionCandidateV1(
        profile,
        occurrence,
        coordinator_context,
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
        verified,
    )


BoundaryMutation = Callable[
    [ReceiptBackedAssetLaneCompositionCandidateV1],
    ReceiptBackedAssetLaneCompositionCandidateV1,
]


@dataclass(frozen=True, slots=True)
class _BoundaryCase:
    name: str
    mutate: BoundaryMutation
    expected_error: str


def _with_extra_compatible_module(
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1,
) -> ReceiptBackedAssetLaneCompositionCandidateV1:
    modules = (
        *candidate.coordinator_context.compatible_modules,
        AssetLaneModuleCompatibilityV1(_root(999), "foreign/module/schema/v1"),
    )
    return replace(
        candidate,
        coordinator_context=replace(
            candidate.coordinator_context,
            compatible_modules=tuple(
                sorted(modules, key=lambda item: item.module_release_id)
            ),
        ),
    )


_BOUNDARY_CASES = (
    _BoundaryCase(
        "inactive_profile",
        lambda candidate: replace(
            candidate,
            profile=replace(candidate.profile, status=ProfileStatusV1.SHADOW),
        ),
        "receipt-backed lane profile is not ACTIVE",
    ),
    _BoundaryCase(
        "occurrence_profile_substitution",
        lambda candidate: replace(
            candidate,
            occurrence=replace(candidate.occurrence, profile_root=_root(999)),
        ),
        "receipt-backed lane occurrence profile mismatch",
    ),
    _BoundaryCase(
        "coordinator_profile_substitution",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                profile_root=_root(999),
            ),
        ),
        "receipt-backed lane coordinator profile mismatch",
    ),
    _BoundaryCase(
        "coordinator_chain_substitution",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                chain_id="other-chain",
            ),
        ),
        "receipt-backed lane coordinator chain mismatch",
    ),
    _BoundaryCase(
        "coordinator_deployment_substitution",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                deployment_root=_root(999),
            ),
        ),
        "receipt-backed lane coordinator deployment mismatch",
    ),
    _BoundaryCase(
        "coordinator_occurrence_substitution",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                command_occurrence_id=_root(999),
            ),
        ),
        "receipt-backed lane coordinator occurrence mismatch",
    ),
    _BoundaryCase(
        "coordinator_release_substitution",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                coordinator_release_id=_root(999),
            ),
        ),
        "receipt-backed lane selected coordinator release mismatch",
    ),
    _BoundaryCase(
        "module_journal_chain_substitution",
        lambda candidate: replace(
            candidate,
            module_journal=replace(candidate.module_journal, chain_id="other-chain"),
        ),
        "receipt-backed lane module journal chain mismatch",
    ),
    _BoundaryCase(
        "module_journal_deployment_substitution",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                deployment_root=_root(999),
            ),
        ),
        "receipt-backed lane module journal deployment mismatch",
    ),
    _BoundaryCase(
        "module_journal_profile_substitution",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                profile_root=_root(999),
            ),
        ),
        "receipt-backed lane module journal profile mismatch",
    ),
    _BoundaryCase(
        "module_journal_occurrence_substitution",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                command_occurrence_id=_root(999),
            ),
        ),
        "receipt-backed lane module journal occurrence mismatch",
    ),
    _BoundaryCase(
        "route_module_release_substitution",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                module_release_id=_root(999),
            ),
        ),
        "receipt-backed lane route module release mismatch",
    ),
    _BoundaryCase(
        "coordinator_writer_epoch_lower_neighbor",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                writer_epoch=candidate.profile.authority_epoch - 1,
            ),
        ),
        "receipt-backed lane writer epoch mismatch",
    ),
    _BoundaryCase(
        "coordinator_writer_epoch_upper_neighbor",
        lambda candidate: replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                writer_epoch=candidate.profile.authority_epoch + 1,
            ),
        ),
        "receipt-backed lane writer epoch mismatch",
    ),
    _BoundaryCase(
        "module_writer_epoch_lower_neighbor",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                writer_epoch=candidate.profile.authority_epoch - 1,
            ),
        ),
        "receipt-backed lane writer epoch mismatch",
    ),
    _BoundaryCase(
        "module_writer_epoch_upper_neighbor",
        lambda candidate: replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                writer_epoch=candidate.profile.authority_epoch + 1,
            ),
        ),
        "receipt-backed lane writer epoch mismatch",
    ),
    _BoundaryCase(
        "compatible_module_set_extra_member",
        _with_extra_compatible_module,
        "receipt-backed lane compatible module set mismatch",
    ),
    _BoundaryCase(
        "private_port_root_substitution",
        lambda candidate: replace(
            candidate,
            private_port=replace(
                candidate.private_port,
                module_effect_plan_root=_root(999),
            ),
        ),
        "asset lane composition rejected: PRIVATE_PORT_ROOT_MISMATCH",
    ),
    _BoundaryCase(
        "effect_plan_root_substitution",
        lambda candidate: replace(
            candidate,
            module_effects=replace(
                candidate.module_effects,
                occurrence_consumptions=(_root(999),),
            ),
        ),
        "asset lane composition rejected: EFFECT_PLAN_MISMATCH",
    ),
)


@pytest.mark.parametrize("boundary_case", _BOUNDARY_CASES, ids=lambda case: case.name)
def test_one_defect_boundary_pair_rejects_at_its_named_binding(
    boundary_case: _BoundaryCase,
) -> None:
    candidate = boundary_case.mutate(_candidate())

    with pytest.raises(ValueError, match=re.escape(boundary_case.expected_error)):
        compose_receipt_backed_asset_lane_single_v1(candidate)


@pytest.mark.parametrize("target", ("coordinator", "module_journal"))
@pytest.mark.parametrize("epoch_delta", (-1, 0, 1), ids=("lower", "exact", "upper"))
def test_writer_epoch_exact_and_both_neighbors_form_a_closed_boundary(
    target: str,
    epoch_delta: int,
) -> None:
    candidate = _candidate()
    writer_epoch = candidate.profile.authority_epoch + epoch_delta
    if target == "coordinator":
        candidate = replace(
            candidate,
            coordinator_context=replace(
                candidate.coordinator_context,
                writer_epoch=writer_epoch,
            ),
        )
    else:
        candidate = replace(
            candidate,
            module_journal=replace(
                candidate.module_journal,
                writer_epoch=writer_epoch,
            ),
        )

    if epoch_delta == 0:
        composition = compose_receipt_backed_asset_lane_single_v1(candidate)

        assert composition.authority_level is (
            LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY
        )
    else:
        with pytest.raises(ValueError, match="writer epoch mismatch"):
            compose_receipt_backed_asset_lane_single_v1(candidate)


def _trace_outcome(
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1,
) -> tuple[str, str]:
    target_file = Path(composition_module.__file__).resolve()
    visited_lines: list[int] = []

    def tracer(frame, event, arg):
        if event == "line" and Path(frame.f_code.co_filename).resolve() == target_file:
            line_number = frame.f_lineno
            if not visited_lines or visited_lines[-1] != line_number:
                visited_lines.append(line_number)
        return tracer

    previous_tracer = sys.gettrace()
    try:
        sys.settrace(tracer)
        try:
            composition = compose_receipt_backed_asset_lane_single_v1(candidate)
        except (TypeError, ValueError) as exc:
            outcome = f"reject:{exc}"
        else:
            outcome = f"accepted:{composition.authority_level.value}"
    finally:
        sys.settrace(previous_tracer)

    path_bytes = ",".join(str(line) for line in visited_lines).encode("ascii")
    return outcome, hashlib.sha256(path_bytes).hexdigest()[:16]


def test_boundary_exploration_preserves_diverse_outcome_path_archive() -> None:
    valid_candidate = _candidate()
    valid_observation = _trace_outcome(valid_candidate)
    observations = [
        valid_observation,
        *(
            _trace_outcome(boundary_case.mutate(valid_candidate))
            for boundary_case in _BOUNDARY_CASES
        ),
    ]

    archive = set(observations)
    outcomes = {outcome for outcome, _ in observations}
    paths = {path_id for _, path_id in observations}
    expected_outcomes = {
        f"accepted:{LaneCompositionAuthorityLevelV1.RECEIPT_BACKED_STRUCTURAL_ONLY.value}",
        *(f"reject:{boundary_case.expected_error}" for boundary_case in _BOUNDARY_CASES),
    }

    assert outcomes == expected_outcomes
    assert len(archive) >= len(expected_outcomes)
    assert len(paths) >= 12
    assert valid_observation in archive


@pytest.mark.parametrize(
    ("left_index", "right_index"),
    ((2, 8), (11, 14), (15, 16), (16, 17)),
    ids=(
        "profile_bindings",
        "writer_epoch_neighbors",
        "compatibility_before_port",
        "port_before_effects",
    ),
)
def test_bounded_depth_two_frontier_has_stable_reject_precedence(
    left_index: int,
    right_index: int,
) -> None:
    candidate = _candidate()
    left = _BOUNDARY_CASES[left_index]
    right = _BOUNDARY_CASES[right_index]

    left_then_right = _trace_outcome(right.mutate(left.mutate(candidate)))
    right_then_left = _trace_outcome(left.mutate(right.mutate(candidate)))

    assert left_then_right == right_then_left


def test_semantically_identical_rebuild_preserves_composition_root() -> None:
    candidate = _candidate()
    rebuilt = replace(
        candidate,
        profile=replace(candidate.profile),
        occurrence=replace(candidate.occurrence),
        coordinator_context=replace(candidate.coordinator_context),
        module_journal=replace(candidate.module_journal),
        private_port=replace(candidate.private_port),
        module_effects=replace(candidate.module_effects),
    )

    original = compose_receipt_backed_asset_lane_single_v1(candidate)
    replay = compose_receipt_backed_asset_lane_single_v1(rebuilt)

    assert replay.binding_root == original.binding_root
    assert replay.lane_journal_root == original.lane_journal_root
    assert replay.module_journal_digest == original.module_journal_digest
