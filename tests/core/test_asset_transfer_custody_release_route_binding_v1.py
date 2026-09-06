"""Custody release-route binder: exact recomputation, root guards, and legacy parity.

Every rejection control reports the base-transition count, the custody
recomputation count, the legacy recomputation count, and an unchanged
canonical observation of the candidate, so "rejects before recomputation" is
an observed fact rather than a reading of the code. Nothing here claims
receipt, activation, or publication authority.
"""

from __future__ import annotations

import inspect
from dataclasses import dataclass, replace
from types import SimpleNamespace

import pytest

from src.core import asset_transfer_custody_semantics_v1 as semantics
from src.core import asset_transfer_lane_module_custody_v1 as custody
from src.core import asset_transfer_lane_module_v1 as lane_module
from src.core import lane_module_release_route_binding_v1 as binding
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1,
    _receipt_root,
    transition_asset_transfer_lane_module_v1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferStateV1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    LaneIdV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from src.core.lane_module_release_route_binding_v1 import (
    RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
    AssetTransferReleaseRouteBindingCandidateV1,
    ReleaseRouteBoundLaneTransitionV1,
    _bind_asset_transfer_custody_output_structural_v1,
    _snapshot_asset_transfer_route_binding_candidate_v1,
    bind_asset_transfer_lane_output_to_custody_release_route_v1,
    bind_asset_transfer_lane_output_to_release_route_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
from tests.core.test_asset_transfer_custody_semantics_v1 import (
    _COMMAND,
    _LEGACY_ROOTS,
    _SPOOFED_METADATA,
    _CustodyGovernanceV1,
    _foreign_roots,
    _governance,
    _occurrence,
    _root,
    _SemanticRootsV1,
)
from tests.core.test_lane_module_release_route_binding_v1 import (
    _accepted_transfer_with_binding as _legacy_accepted_transfer_with_binding,
)
from tests.core.test_lane_module_release_route_binding_v1 import (
    _asset_input as _legacy_asset_input,
)
from tests.core.test_lane_module_release_route_binding_v1 import (
    _transfer_binding_candidate as _legacy_transfer_binding_candidate,
)

LEGACY_TRANSFER_BINDING_ROOT_VECTOR = (
    "0x3c81585faeffa442eb7d83cff4ccd3c158358a67766f63c8c8f00a579e736fba"
)


@dataclass(slots=True)
class _TransitionCounterV1:
    """Observed transition activity while one binder call runs."""

    base_transitions: int = 0
    custody_recomputations: int = 0
    legacy_recomputations: int = 0
    candidate_snapshots: int = 0

    def snapshot(self) -> tuple[int, int, int]:
        return (self.base_transitions, self.custody_recomputations, self.legacy_recomputations)


def _instrument(monkeypatch: pytest.MonkeyPatch) -> _TransitionCounterV1:
    """Count base transfer transitions, each recomputation entry, and candidate snapshots."""

    counter = _TransitionCounterV1()
    real_base = lane_module.transition_asset_transfer_v1
    real_custody = binding.recompute_asset_transfer_lane_module_custody_v1
    real_legacy = binding._recompute_asset_transfer_lane_module_accepted_v1
    real_snapshot = binding._snapshot_asset_transfer_route_binding_candidate_v1

    def counted_base(
        context: AssetTransferContextV1,
        pre_state: AssetTransferStateV1,
        command: AssetTransferCommandV1,
    ) -> object:
        counter.base_transitions += 1
        return real_base(context, pre_state, command)

    def counted_custody(
        module_input: AssetTransferLaneModuleInputV1,
        accepted: AssetTransferLaneModuleAcceptedV1,
    ) -> AssetTransferLaneModuleAcceptedV1:
        counter.custody_recomputations += 1
        return real_custody(module_input, accepted)

    def counted_legacy(
        module_input: AssetTransferLaneModuleInputV1,
        accepted: AssetTransferLaneModuleAcceptedV1,
    ) -> tuple[AssetTransferLaneModuleInputV1, AssetTransferLaneModuleAcceptedV1]:
        counter.legacy_recomputations += 1
        return real_legacy(module_input, accepted)

    def counted_snapshot(
        candidate: AssetTransferReleaseRouteBindingCandidateV1,
    ) -> AssetTransferReleaseRouteBindingCandidateV1:
        counter.candidate_snapshots += 1
        return real_snapshot(candidate)

    monkeypatch.setattr(lane_module, "transition_asset_transfer_v1", counted_base)
    monkeypatch.setattr(binding, "recompute_asset_transfer_lane_module_custody_v1", counted_custody)
    monkeypatch.setattr(
        binding,
        "_recompute_asset_transfer_lane_module_accepted_v1",
        counted_legacy,
    )
    monkeypatch.setattr(
        binding,
        "_snapshot_asset_transfer_route_binding_candidate_v1",
        counted_snapshot,
    )
    return counter


def _module_input(
    governance: _CustodyGovernanceV1,
    occurrence: EconomicCommandOccurrenceV1,
    *,
    custody_atoms: int = 7,
    module_release_id: str | None = None,
    chain_id: str | None = None,
) -> AssetTransferLaneModuleInputV1:
    registry = governance.asset_policy_registry
    release_id = registry.module_release_id if module_release_id is None else module_release_id
    return AssetTransferLaneModuleInputV1(
        context=AssetTransferContextV1(
            chain_id=occurrence.chain_id if chain_id is None else chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=governance.profile.authority_epoch,
            module_release_id=release_id,
            command_occurrence_id=occurrence.occurrence_id,
            subject_id=occurrence.subject_id,
            grant_root=occurrence.grant_root,
        ),
        pre_state=AssetTransferStateV1(
            module_release_id=release_id,
            policies=registry.policies,
            balances=(
                EconomicAmountV1("alice", "USD", "accounts", 100),
                EconomicAmountV1("bob", "USD", "accounts", 10),
                EconomicAmountV1("treasury", "USD", "accounts", 5),
            ),
            supplies=(AssetSupplyV1("USD", 115 + custody_atoms),),
        ),
        command=_COMMAND,
        asset_policy_registry_root=registry.asset_policy_root,
        fee_policy_registry_root=registry.fee_policy_root,
        custody=() if custody_atoms == 0 else (EconomicAmountV1("vault", "USD", "escrow", custody_atoms),),
    )


def _custody_accepted(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleAcceptedV1:
    accepted = transition_asset_transfer_lane_module_custody_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    return accepted


def _legacy_accepted(module_input: AssetTransferLaneModuleInputV1) -> AssetTransferLaneModuleAcceptedV1:
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    assert isinstance(accepted, AssetTransferLaneModuleAcceptedV1)
    return accepted


def _candidate(
    governance: _CustodyGovernanceV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> AssetTransferReleaseRouteBindingCandidateV1:
    return AssetTransferReleaseRouteBindingCandidateV1(
        governance.profile,
        governance.policy_registry,
        governance.asset_policy_registry,
        occurrence,
        module_input,
        accepted,
    )


def _honest_candidate(
    governance: _CustodyGovernanceV1,
    *,
    custody_atoms: int = 7,
) -> tuple[
    EconomicCommandOccurrenceV1,
    AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleAcceptedV1,
    AssetTransferReleaseRouteBindingCandidateV1,
]:
    occurrence = _occurrence(governance)
    module_input = _module_input(governance, occurrence, custody_atoms=custody_atoms)
    accepted = _custody_accepted(module_input)
    return occurrence, module_input, accepted, _candidate(governance, occurrence, module_input, accepted)


def _observation(candidate: AssetTransferReleaseRouteBindingCandidateV1) -> bytes:
    accepted = candidate.accepted
    return canonical_global_bytes_v1(
        {
            "profile": candidate.profile,
            "policy_registry": candidate.policy_registry,
            "asset_policy_registry": candidate.asset_policy_registry.to_canonical(),
            "occurrence": candidate.occurrence,
            "module_input": candidate.module_input.to_canonical(),
            "accepted": {
                "statement": accepted.statement_root,
                "state": accepted.post_state,
                "effects": accepted.effects,
                "port": accepted.private_port,
                "journal": accepted.module_journal,
            },
        }
    )


def _expected_binding_root(
    governance: _CustodyGovernanceV1,
    occurrence: EconomicCommandOccurrenceV1,
    module_input: AssetTransferLaneModuleInputV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
) -> str:
    """Assemble the witness fields from fixture identities, independent of the binder."""

    return hash_global_v1(
        "release-route-bound-lane-transition-v1",
        {
            "schema": RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
            "profile_id": governance.profile.profile_id,
            "route_release_id": governance.route.route_release_id,
            "lane_id": LaneIdV1.ASSET_TRANSFER,
            "module_release_id": governance.asset_policy_registry.module_release_id,
            "command_occurrence_id": occurrence.occurrence_id,
            "module_journal_root": accepted.module_journal.journal_root,
            "statement_root": module_input.statement_root,
            "producer_module_schema": ASSET_TRANSFER_MODULE_SCHEMA_V1,
            "route_lane_index": 0,
            "port_schema_root": governance.route.port_schema_roots[0],
        },
    )


def _rebound_with_shifted_totals(
    accepted: AssetTransferLaneModuleAcceptedV1,
    delta_atoms: int,
) -> AssetTransferLaneModuleAcceptedV1:
    """Coherently rebuild an accepted value whose caller-supplied totals are shifted."""

    effects = replace(
        accepted.effects,
        asset_conservation=tuple(
            replace(
                row,
                owned_and_custodied_pre_atoms=row.owned_and_custodied_pre_atoms + delta_atoms,
                owned_and_custodied_post_atoms=row.owned_and_custodied_post_atoms + delta_atoms,
            )
            for row in accepted.effects.asset_conservation
        ),
    )
    port = replace(accepted.private_port, module_effect_plan_root=effects.effect_plan_root)
    journal = replace(
        accepted.module_journal,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=port.port_root,
        receipt_root=_receipt_root(accepted.statement_root, accepted.module_journal, port, effects),
    )
    return AssetTransferLaneModuleAcceptedV1(
        accepted.statement_root, accepted.post_state, effects, journal, port
    )


@pytest.mark.parametrize("custody_atoms", (1, 7))
def test_custody_binder_accepts_exact_custody_recomputation_once_for_matching_roots(
    custody_atoms: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given matching refreshed roots and nonzero custody, when the custody binder
    runs, then it returns the existing opaque witness after exactly one custody
    recomputation and no legacy recomputation."""

    # Arrange
    governance = _governance()
    occurrence, module_input, accepted, candidate = _honest_candidate(
        governance, custody_atoms=custody_atoms
    )
    before = _observation(candidate)
    counter = _instrument(monkeypatch)

    # Act
    bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)

    # Assert
    assert type(bound) is ReleaseRouteBoundLaneTransitionV1
    assert counter.snapshot() == (1, 1, 0)
    assert counter.candidate_snapshots == 1
    assert bound.profile_id == governance.profile.profile_id
    assert bound.route_release_id == governance.route.route_release_id
    assert bound.lane_id is LaneIdV1.ASSET_TRANSFER
    assert bound.module_release_id == governance.asset_policy_registry.module_release_id
    assert bound.command_occurrence_id == occurrence.occurrence_id
    assert bound.module_journal_root == accepted.module_journal.journal_root
    assert bound.statement_root == module_input.statement_root
    assert bound.producer_module_schema == ASSET_TRANSFER_MODULE_SCHEMA_V1
    assert bound.route_lane_index == 0
    assert bound.port_schema_root == governance.route.port_schema_roots[0]
    assert bound.binding_root == _expected_binding_root(governance, occurrence, module_input, accepted)
    assert accepted.effects.asset_conservation[0].owned_and_custodied_post_atoms == 115 + custody_atoms
    assert _observation(candidate) == before
    with pytest.raises(AttributeError, match="immutable"):
        bound._profile_id = _root(999)


def test_zero_custody_equalizes_outputs_but_each_binder_still_recomputes_its_own_way(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: with empty custody the completed totals equal the legacy totals.
    governance = _governance()
    occurrence, module_input, accepted, candidate = _honest_candidate(governance, custody_atoms=0)
    legacy = _legacy_accepted(module_input)
    assert _observation(_candidate(governance, occurrence, module_input, legacy)) == _observation(candidate)
    counter = _instrument(monkeypatch)

    # Act
    custody_bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    after_custody = counter.snapshot()
    legacy_bound = bind_asset_transfer_lane_output_to_release_route_v1(candidate)

    # Assert: equal witnesses; one custody recomputation, then one legacy recomputation.
    assert after_custody == (1, 1, 0)
    assert counter.snapshot() == (2, 1, 1)
    assert custody_bound.binding_root == legacy_bound.binding_root
    assert custody_bound.binding_root == _expected_binding_root(
        governance, occurrence, module_input, accepted
    )


def test_one_atom_custody_separates_the_binders_after_structural_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: the smallest nonzero custody makes legacy and custody outputs differ.
    governance = _governance()
    occurrence, module_input, accepted, candidate = _honest_candidate(governance, custody_atoms=1)
    legacy = _legacy_accepted(module_input)
    legacy_candidate = _candidate(governance, occurrence, module_input, legacy)
    assert legacy.effects.effect_plan_root != accepted.effects.effect_plan_root
    before_legacy = _observation(legacy_candidate)
    before_custody = _observation(candidate)
    counter = _instrument(monkeypatch)

    # Act / Assert: each binder recomputes once, then refuses the other family's output.
    with pytest.raises(ValueError, match="custody-complete supplied acceptance differs from recomputation"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(legacy_candidate)
    assert counter.snapshot() == (1, 1, 0)
    with pytest.raises(ValueError, match="asset transfer supplied acceptance differs from recomputation"):
        bind_asset_transfer_lane_output_to_release_route_v1(candidate)
    assert counter.snapshot() == (2, 1, 1)
    assert _observation(legacy_candidate) == before_legacy
    assert _observation(candidate) == before_custody


def test_caller_supplied_totals_cannot_replace_the_custody_recomputation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: a coherent accepted value whose completed totals are shifted by one
    # atom; every root is rebuilt so structural binding cannot notice.
    governance = _governance()
    occurrence, module_input, accepted, _ = _honest_candidate(governance, custody_atoms=7)
    shifted = _rebound_with_shifted_totals(accepted, 1)
    candidate = _candidate(governance, occurrence, module_input, shifted)
    assert _bind_asset_transfer_custody_output_structural_v1(
        _snapshot_asset_transfer_route_binding_candidate_v1(candidate)
    ).statement_root == module_input.statement_root
    before = _observation(candidate)
    counter = _instrument(monkeypatch)

    # Act / Assert: only the recomputation decides the totals.
    with pytest.raises(ValueError, match="custody-complete supplied acceptance differs from recomputation"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    assert counter.snapshot() == (1, 1, 0)
    assert _observation(candidate) == before


@pytest.mark.parametrize("role", ("module", "coordinator", "route", "all-unknown"))
def test_semantic_root_mismatch_rejects_before_recomputation_for_each_role(
    role: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given an unknown or mixed root, when the custody binder runs, then it rejects
    before recomputation and does not alter the candidate or accepted value."""

    # Arrange: rebuild release ids, registry roots, profile, occurrence, and input
    # coherently around the one changed role.
    foreign = _foreign_roots()
    roots = {
        "module": _SemanticRootsV1(module=foreign.module),
        "coordinator": _SemanticRootsV1(coordinator=foreign.coordinator),
        "route": _SemanticRootsV1(route=foreign.route),
        "all-unknown": foreign,
    }[role]
    governance = _governance(roots)
    _, _, _, candidate = _honest_candidate(governance, custody_atoms=7)
    before = _observation(candidate)
    counter = _instrument(monkeypatch)
    expected_label = "module" if role == "all-unknown" else role

    # Act / Assert: one owned snapshot, then the semantic guard, then nothing else.
    with pytest.raises(ValueError, match=f"custody semantics {expected_label} specification root mismatch"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    assert counter.snapshot() == (0, 0, 0)
    assert counter.candidate_snapshots == 1
    assert _observation(candidate) == before


def test_metadata_spoof_cannot_select_and_does_not_block_selection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: successor-looking version/image/source/toolchain on every role.
    spoofed_legacy = _governance(_LEGACY_ROOTS, metadata=_SPOOFED_METADATA)
    spoofed_custody = _governance(metadata=_SPOOFED_METADATA)
    _, _, _, legacy_candidate = _honest_candidate(spoofed_legacy, custody_atoms=7)
    _, _, _, custody_candidate = _honest_candidate(spoofed_custody, custody_atoms=7)
    counter = _instrument(monkeypatch)

    # Act / Assert
    with pytest.raises(ValueError, match="custody semantics module specification root mismatch"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(legacy_candidate)
    assert counter.snapshot() == (0, 0, 0)
    bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(custody_candidate)
    assert type(bound) is ReleaseRouteBoundLaneTransitionV1
    assert counter.snapshot() == (1, 1, 0)


def _boundary_control(name: str) -> tuple[AssetTransferReleaseRouteBindingCandidateV1, str]:
    if name == "inactive-profile":
        governance = _governance(profile_status=ProfileStatusV1.SHADOW)
        return _honest_candidate(governance)[3], "economic profile is not ACTIVE"
    if name == "disabled-route":
        governance = _governance(
            profile_status=ProfileStatusV1.SHADOW,
            route_status=ReleaseStatusV1.SHADOW,
        )
        return _honest_candidate(governance)[3], "command route is disabled for new objects"
    if name == "two-lane-route":
        governance = _governance(route_lanes=(LaneIdV1.ASSET_TRANSFER, LaneIdV1.SPOT_LIQUIDITY))
        return _honest_candidate(governance)[3], "single-lane ASSET_TRANSFER route"
    if name == "wrong-single-lane":
        governance = _governance(route_lanes=(LaneIdV1.SPOT_LIQUIDITY,))
        return _honest_candidate(governance)[3], "single-lane ASSET_TRANSFER route"
    governance = _governance()
    occurrence, module_input, accepted, _ = _honest_candidate(governance)
    if name == "command-kind":
        foreign = _occurrence(governance, command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1)
        return (
            _candidate(governance, foreign, module_input, accepted),
            "custody semantics require an asset transfer command",
        )
    if name == "route-claim":
        foreign = _occurrence(governance, route_release_id=_root(998))
        return (
            _candidate(governance, foreign, module_input, accepted),
            "caller-selected route does not match governed route",
        )
    if name == "profile-root":
        foreign = _occurrence(governance, profile_root=_root(997))
        return (
            _candidate(governance, foreign, module_input, accepted),
            "lane module occurrence profile root mismatch",
        )
    if name == "occurrence-subject":
        foreign = _occurrence(governance, subject_id="mallory")
        return (
            _candidate(governance, foreign, module_input, accepted),
            "lane module release-route subject mismatch",
        )
    if name == "module-release":
        foreign_input = _module_input(governance, occurrence, module_release_id=_root(996))
        return (
            _candidate(governance, occurrence, foreign_input, _custody_accepted(foreign_input)),
            "asset transfer policy registry module release mismatch",
        )
    if name == "context-chain":
        foreign_input = _module_input(governance, occurrence, chain_id="other-chain")
        return (
            _candidate(governance, occurrence, foreign_input, _custody_accepted(foreign_input)),
            "lane module release-route chain id mismatch",
        )
    raise AssertionError(f"unknown boundary control: {name}")


@pytest.mark.parametrize(
    "name",
    (
        "inactive-profile",
        "disabled-route",
        "two-lane-route",
        "wrong-single-lane",
        "command-kind",
        "route-claim",
        "profile-root",
        "occurrence-subject",
        "module-release",
        "context-chain",
    ),
)
def test_boundary_controls_reject_before_recomputation_and_leave_the_candidate_unchanged(
    name: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    candidate, message = _boundary_control(name)
    before = _observation(candidate)
    counter = _instrument(monkeypatch)

    # Act / Assert
    with pytest.raises(ValueError, match=message):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    assert counter.snapshot() == (0, 0, 0)
    assert _observation(candidate) == before


def test_structural_helper_selects_semantics_before_the_reused_structural_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: an owned honest candidate, plus a statement-mismatched output under
    # matching roots and under legacy roots.
    governance = _governance()
    occurrence, module_input, accepted, candidate = _honest_candidate(governance)
    foreign_output = _custody_accepted(
        replace(module_input, command=replace(module_input.command, amount_atoms=29))
    )
    mismatched = _candidate(governance, occurrence, module_input, foreign_output)
    legacy_governance = _governance(_LEGACY_ROOTS)
    legacy_occurrence, legacy_input, _, _ = _honest_candidate(legacy_governance)
    legacy_mismatched = _candidate(
        legacy_governance,
        legacy_occurrence,
        legacy_input,
        _custody_accepted(replace(legacy_input, command=replace(legacy_input.command, amount_atoms=29))),
    )
    counter = _instrument(monkeypatch)

    # Act
    bound = _bind_asset_transfer_custody_output_structural_v1(
        _snapshot_asset_transfer_route_binding_candidate_v1(candidate)
    )

    # Assert: transition-free, equal to the public witness, semantic guard first.
    assert counter.snapshot() == (0, 0, 0)
    assert bound.binding_root == _expected_binding_root(governance, occurrence, module_input, accepted)
    with pytest.raises(ValueError, match="asset transfer accepted statement mismatch"):
        _bind_asset_transfer_custody_output_structural_v1(
            _snapshot_asset_transfer_route_binding_candidate_v1(mismatched)
        )
    with pytest.raises(ValueError, match="custody semantics module specification root mismatch"):
        _bind_asset_transfer_custody_output_structural_v1(
            _snapshot_asset_transfer_route_binding_candidate_v1(legacy_mismatched)
        )
    assert counter.snapshot() == (0, 0, 0)


def test_retained_command_subclass_rejects_at_the_single_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: mutate the retained input alias after the candidate is built.
    governance = _governance()
    _, module_input, _, candidate = _honest_candidate(governance)
    advertised_hash = module_input.command.command_body_hash

    class _ForgedBodyHashCommand(AssetTransferCommandV1):
        @property
        def command_body_hash(self) -> str:
            return advertised_hash

    object.__setattr__(
        module_input,
        "command",
        _ForgedBodyHashCommand(
            module_input.command.command_kind,
            module_input.command.asset,
            module_input.command.sender,
            "mallory",
            module_input.command.amount_atoms,
            module_input.command.max_fee_atoms,
        ),
    )
    counter = _instrument(monkeypatch)

    # Act / Assert
    with pytest.raises(TypeError, match="command must have the exact typed value"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    assert counter.snapshot() == (0, 0, 0)
    assert counter.candidate_snapshots == 1


def test_duck_typed_candidate_with_genuine_fields_rejects_at_the_single_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: every field is genuine; only the candidate type is foreign.
    governance = _governance()
    occurrence, module_input, accepted, _ = _honest_candidate(governance)
    duck = SimpleNamespace(
        profile=governance.profile,
        policy_registry=governance.policy_registry,
        asset_policy_registry=governance.asset_policy_registry,
        occurrence=occurrence,
        module_input=module_input,
        accepted=accepted,
    )
    counter = _instrument(monkeypatch)

    # Act / Assert: the single snapshot is the type boundary; nothing runs behind it.
    with pytest.raises(TypeError, match="asset transfer route candidate must have the exact type"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(
            duck,  # type: ignore[arg-type]
        )
    assert counter.snapshot() == (0, 0, 0)
    assert counter.candidate_snapshots == 1


def test_legacy_binder_observables_are_unchanged_for_accepted_and_rejected_vectors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given a legacy candidate, when the legacy binder runs, then its accepted and
    rejected observables are exactly the existing ones, and the custody binder
    refuses the legacy fixture before any recomputation."""

    # Arrange: the existing legacy fixture and its cross-language vector.
    governance, occurrence, module_input, accepted, bound = _legacy_accepted_transfer_with_binding()
    profile = governance.profile
    assert bound.binding_root == LEGACY_TRANSFER_BINDING_ROOT_VECTOR
    candidate = _legacy_transfer_binding_candidate(governance, occurrence, module_input, accepted)
    wrong_route = replace(occurrence, route_release_id=_root(998))
    wrong_route_input = _legacy_asset_input(profile, wrong_route)
    foreign_input = _legacy_asset_input(profile, occurrence, module_release_id=_root(997))
    rejected_vectors = (
        (
            _legacy_transfer_binding_candidate(
                governance, wrong_route, wrong_route_input, _legacy_accepted(wrong_route_input)
            ),
            "caller-selected route",
        ),
        (
            AssetTransferReleaseRouteBindingCandidateV1(
                replace(profile, status=ProfileStatusV1.SHADOW),
                governance.policy_registry,
                governance.asset_policy_registry,
                occurrence,
                module_input,
                accepted,
            ),
            "profile is not ACTIVE",
        ),
        (
            _legacy_transfer_binding_candidate(
                governance, occurrence, foreign_input, _legacy_accepted(foreign_input)
            ),
            "module release mismatch",
        ),
    )
    counter = _instrument(monkeypatch)

    # Act / Assert: legacy acceptance recomputes through the legacy path only.
    rebound = bind_asset_transfer_lane_output_to_release_route_v1(candidate)
    assert rebound.binding_root == LEGACY_TRANSFER_BINDING_ROOT_VECTOR
    assert counter.snapshot() == (1, 0, 1)
    for rejected, message in rejected_vectors:
        with pytest.raises(ValueError, match=message):
            bind_asset_transfer_lane_output_to_release_route_v1(rejected)
    assert counter.snapshot() == (1, 0, 1)
    # The legacy fixture roots are not the custody root; selection refuses first.
    with pytest.raises(ValueError, match="custody semantics module specification root mismatch"):
        bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    assert counter.snapshot() == (1, 0, 1)


def test_legacy_binder_remains_root_agnostic_under_a_custody_profile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: legacy output over a custody-root profile with empty custody.
    governance = _governance()
    occurrence, module_input, _, _ = _honest_candidate(governance, custody_atoms=0)
    legacy_candidate = _candidate(governance, occurrence, module_input, _legacy_accepted(module_input))
    counter = _instrument(monkeypatch)

    # Act / Assert: unchanged legacy behavior; no custody semantics are consulted.
    bound = bind_asset_transfer_lane_output_to_release_route_v1(legacy_candidate)
    assert type(bound) is ReleaseRouteBoundLaneTransitionV1
    assert counter.snapshot() == (1, 0, 1)


def test_custody_binder_adds_no_authority_surface_constructor_or_callback() -> None:
    parameters = inspect.signature(bind_asset_transfer_lane_output_to_custody_release_route_v1).parameters
    assert list(parameters) == ["candidate"]
    assert binding.__all__ == [
        "RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1",
        "ReleaseRouteBoundLaneTransitionV1",
        "AssetTransferReleaseRouteBindingCandidateV1",
        "ManagedAssetLifecycleReleaseRouteBindingCandidateV1",
        "PerpsMarginReleaseRouteBindingCandidateV1",
        "bind_asset_transfer_lane_output_to_release_route_v1",
        "bind_asset_transfer_lane_output_to_custody_release_route_v1",
        "bind_managed_asset_lifecycle_lane_output_to_release_route_v1",
        "bind_perps_margin_lane_output_to_release_route_v1",
    ]
    assert binding.require_asset_transfer_custody_semantics_v1 is (
        semantics.require_asset_transfer_custody_semantics_v1
    )
    assert binding.recompute_asset_transfer_lane_module_custody_v1 is (
        custody.recompute_asset_transfer_lane_module_custody_v1
    )
    assert not hasattr(binding, "transition_asset_transfer_lane_module_custody_v1")
    assert not any(
        marker in name.lower()
        for name in vars(binding)
        for marker in ("receipt", "publish", "activat", "verifier")
    )
    with pytest.raises(TypeError, match="binder-constructed"):
        ReleaseRouteBoundLaneTransitionV1(
            object(),
            _root(1),
            _root(2),
            LaneIdV1.ASSET_TRANSFER,
            _root(3),
            _root(4),
            _root(5),
            _root(6),
            ASSET_TRANSFER_MODULE_SCHEMA_V1,
            0,
            _root(7),
        )
