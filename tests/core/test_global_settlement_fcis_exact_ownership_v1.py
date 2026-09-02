from __future__ import annotations

from pathlib import Path

import pytest

from src.core.asset_lane_projection_v1 import (
    AssetLaneCompositionAcceptedV1,
    AssetLaneStateProjectionV1,
    project_asset_transfer_state_v1,
)
from src.core.global_economic_refinement_snapshot_v1 import (
    _snapshot_effect_plan_v1,
    _snapshot_state_v1,
)
from src.core.global_settlement_types_v1 import (
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    EconomicProfileSnapshotV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateRootV1,
    GlobalEconomicStateV1,
    LaneCoordinatorReleaseV1,
    LaneModuleReleaseV1,
    LaneStateRootV1,
    LaneTransitionAcceptedV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
    RouteReleaseV1,
    _require_root,
    _require_token,
    canonical_global_bytes_v1,
)
from tests.core.test_global_settlement_abi_v1 import (
    _epoch_asset_module_state,
    _profile,
    _root,
    _state,
)

_REPO_ROOT = Path(__file__).resolve().parents[2]


class _BehaviorBearingString(str):
    encode_called = False
    startswith_called = False

    def encode(self, *args: object, **kwargs: object) -> bytes:
        type(self).encode_called = True
        return super().encode(*args, **kwargs)

    def startswith(self, *args: object, **kwargs: object) -> bool:
        type(self).startswith_called = True
        return super().startswith(*args, **kwargs)


class _BehaviorBearingMapping(dict[str, object]):
    iteration_called = False

    def items(self):  # type: ignore[no-untyped-def]
        type(self).iteration_called = True
        return super().items()


class _BehaviorBearingSequence(list[object]):
    iteration_called = False

    def __iter__(self):  # type: ignore[no-untyped-def]
        type(self).iteration_called = True
        return super().__iter__()


class _BehaviorBearingLaneStateRoot(LaneStateRootV1):
    canonical_called = False

    def to_canonical(self) -> dict[str, object]:
        type(self).canonical_called = True
        return {"forged": True}


class _BehaviorBearingEffectRow(EconomicEffectRowV1):
    key_called = False

    @property
    def key(self) -> tuple[str, str, str, str]:
        type(self).key_called = True
        return super().key


class _BehaviorBearingState(GlobalEconomicStateV1):
    pass


class _BehaviorBearingEffectPlan(GlobalEconomicEffectPlanV1):
    pass


class _BehaviorBearingStateRoot(GlobalEconomicStateRootV1):
    pass


class _BehaviorBearingRejection(LaneTransitionRejectedV1):
    pass


class _BehaviorBearingLaneRelease(LaneModuleReleaseV1):
    pass


class _BehaviorBearingCoordinatorRelease(LaneCoordinatorReleaseV1):
    pass


class _BehaviorBearingRouteRelease(RouteReleaseV1):
    pass


class _BehaviorBearingProfile(EconomicProfileSnapshotV1):
    pass


def _reset_hooks() -> None:
    _BehaviorBearingString.encode_called = False
    _BehaviorBearingString.startswith_called = False
    _BehaviorBearingMapping.iteration_called = False
    _BehaviorBearingSequence.iteration_called = False
    _BehaviorBearingLaneStateRoot.canonical_called = False
    _BehaviorBearingEffectRow.key_called = False


def test_scalar_subclasses_reject_before_behavior_runs() -> None:
    _reset_hooks()

    with pytest.raises(TypeError, match="must be a string"):
        _require_token(_BehaviorBearingString("alice"), name="subject")
    with pytest.raises(TypeError, match="must be a string"):
        _require_root(_BehaviorBearingString(_root(1)), name="root")

    assert not _BehaviorBearingString.encode_called
    assert not _BehaviorBearingString.startswith_called


def test_canonical_encoder_rejects_mapping_subclass_before_iteration() -> None:
    _reset_hooks()

    with pytest.raises(
        TypeError,
        match="canonical mapping subclasses are unsupported",
    ) as exc_info:
        canonical_global_bytes_v1(_BehaviorBearingMapping({"value": 1}))

    assert not _BehaviorBearingMapping.iteration_called
    assert _BehaviorBearingMapping.__name__ not in str(exc_info.value)


def test_canonical_encoder_rejects_sequence_subclass_before_iteration() -> None:
    _reset_hooks()

    with pytest.raises(TypeError, match="canonical sequence subclasses are unsupported"):
        canonical_global_bytes_v1(_BehaviorBearingSequence([1]))

    assert not _BehaviorBearingSequence.iteration_called


def test_global_state_rejects_nested_subclass_before_projection() -> None:
    _reset_hooks()
    profile, _ = _profile()
    state = _state(profile, height=1)
    source = state.lane_roots[0]
    hostile = _BehaviorBearingLaneStateRoot(
        source.lane_id,
        source.module_release_id,
        source.enabled,
        source.state_root,
    )

    with pytest.raises(TypeError, match="invalid lane root"):
        GlobalEconomicStateV1(
            chain_id=state.chain_id,
            deployment_root=state.deployment_root,
            writer_epoch=state.writer_epoch,
            height=state.height,
            profile_root=state.profile_root,
            lane_roots=(hostile, *state.lane_roots[1:]),
            balances=state.balances,
            supplies=state.supplies,
            custody=state.custody,
            liabilities=state.liabilities,
            reserves=state.reserves,
            oracle_occurrences=state.oracle_occurrences,
            replay_state=state.replay_state,
            terminal_obligations=state.terminal_obligations,
            history_root=state.history_root,
            outbox=state.outbox,
        )

    assert not _BehaviorBearingLaneStateRoot.canonical_called


def test_effect_plan_rejects_nested_subclass_before_key_access() -> None:
    _reset_hooks()
    hostile = _BehaviorBearingEffectRow(
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        "alice",
        "USD",
        "ledger",
        1,
    )

    with pytest.raises(TypeError, match="contains an invalid value"):
        GlobalEconomicEffectPlanV1((hostile,), (), (), (), (), ())

    assert not _BehaviorBearingEffectRow.key_called


def test_snapshot_boundaries_reject_outer_subclasses() -> None:
    profile, _ = _profile()
    state = _state(profile, height=1)
    hostile_state = _BehaviorBearingState(
        state.chain_id,
        state.deployment_root,
        state.writer_epoch,
        state.height,
        state.profile_root,
        state.lane_roots,
        state.balances,
        state.supplies,
        state.custody,
        state.liabilities,
        state.reserves,
        state.oracle_occurrences,
        state.replay_state,
        state.terminal_obligations,
        state.history_root,
        state.outbox,
    )
    hostile_plan = _BehaviorBearingEffectPlan((), (), (), (), (), ())

    with pytest.raises(TypeError, match="state must have the exact typed value"):
        _snapshot_state_v1(hostile_state)
    with pytest.raises(TypeError, match="effect plan must have the exact typed value"):
        _snapshot_effect_plan_v1(hostile_plan)


def test_accepted_transition_rejects_effect_plan_subclass() -> None:
    hostile_plan = _BehaviorBearingEffectPlan((), (), (), (), (), ())

    with pytest.raises(TypeError, match="effects are invalid"):
        LaneTransitionAcceptedV1(
            command_occurrence_id=_root(1),
            pre_state_root=_root(2),
            post_state_root=_root(3),
            effects=hostile_plan,
            private_ports_root=_root(4),
            receipt_root=_root(5),
            terminal_obligations=(),
        )


def test_closed_factories_reject_subclass_dispatch() -> None:
    profile, route = _profile()
    state = _state(profile, height=1)
    lane_release = profile.lane_registry.releases[0]
    coordinator_release = profile.lane_coordinator_registry.releases[0]

    with pytest.raises(TypeError, match="state root factory requires"):
        _BehaviorBearingStateRoot.from_state(state)
    with pytest.raises(TypeError, match="effect plan factory requires"):
        _BehaviorBearingEffectPlan.empty()
    with pytest.raises(TypeError, match="lane rejection factory requires"):
        _BehaviorBearingRejection.reject(
            LaneTransitionRejectCodeV1.UNKNOWN_COMMAND,
            state.state_root,
        )
    with pytest.raises(TypeError, match="lane release factory requires"):
        _BehaviorBearingLaneRelease.build(
            lane_id=lane_release.lane_id,
            semantic_version=lane_release.semantic_version,
            state_schema_root=lane_release.state_schema_root,
            command_variants=lane_release.command_variants,
            terminal_command_variants=lane_release.terminal_command_variants,
            guest_image_id=lane_release.guest_image_id,
            specification_root=lane_release.specification_root,
            source_root=lane_release.source_root,
            toolchain_root=lane_release.toolchain_root,
            terminal_coverage_root=lane_release.terminal_coverage_root,
            migration_compatibility_root=lane_release.migration_compatibility_root,
            max_cycles=lane_release.max_cycles,
            max_journal_bytes=lane_release.max_journal_bytes,
            status=lane_release.status,
            accepts_new_objects=lane_release.accepts_new_objects,
            evidence_statuses=lane_release.evidence_statuses,
        )
    with pytest.raises(TypeError, match="lane coordinator factory requires"):
        _BehaviorBearingCoordinatorRelease.build(
            lane_id=coordinator_release.lane_id,
            semantic_version=coordinator_release.semantic_version,
            coordinator_schema_root=coordinator_release.coordinator_schema_root,
            guest_image_id=coordinator_release.guest_image_id,
            specification_root=coordinator_release.specification_root,
            source_root=coordinator_release.source_root,
            toolchain_root=coordinator_release.toolchain_root,
            max_cycles=coordinator_release.max_cycles,
            max_journal_bytes=coordinator_release.max_journal_bytes,
            status=coordinator_release.status,
            accepts_new_objects=coordinator_release.accepts_new_objects,
            evidence_statuses=coordinator_release.evidence_statuses,
        )
    with pytest.raises(TypeError, match="route release factory requires"):
        _BehaviorBearingRouteRelease.build(
            semantic_version=route.semantic_version,
            command_kind=route.command_kind,
            ordered_lanes=route.ordered_lanes,
            module_release_ids=route.module_release_ids,
            dependency_roles=route.dependency_roles,
            port_schema_roots=route.port_schema_roots,
            guest_image_id=route.guest_image_id,
            specification_root=route.specification_root,
            source_root=route.source_root,
            toolchain_root=route.toolchain_root,
            oracle_policy_root=route.oracle_policy_root,
            issue_burn_policy_root=route.issue_burn_policy_root,
            max_cycles=route.max_cycles,
            max_journal_bytes=route.max_journal_bytes,
            status=route.status,
            accepts_new_objects=route.accepts_new_objects,
            evidence_statuses=route.evidence_statuses,
        )
    with pytest.raises(TypeError, match="economic profile factory requires"):
        _BehaviorBearingProfile.build(
            authority_epoch=profile.authority_epoch,
            lane_registry=profile.lane_registry,
            lane_coordinator_registry=profile.lane_coordinator_registry,
            route_registry=profile.route_registry,
            proof_shape_root=profile.proof_shape_root,
            root_image_id=profile.root_image_id,
            verifier_registry_root=profile.verifier_registry_root,
            migration_registry_root=profile.migration_registry_root,
            policy_registry_root=profile.policy_registry_root,
            terminal_registry_root=profile.terminal_registry_root,
            status=profile.status,
        )


# --- C9a'' (Opus P28 F1 audit, mechanical pin) -------------------------------------------------

_ADMISSION_PATH_MODULES = (
    "src/core/asset_transfer_receipt_admission_v1.py",
    "src/core/global_accounting_lane_producers_v1.py",
    "src/core/asset_transfer_lane_module_v1.py",
    "src/core/asset_lane_projection_v1.py",
    "src/core/asset_transfer_types_v1.py",
    "src/core/lane_module_receipt_verification_v1.py",
    "src/core/lane_module_release_route_binding_v1.py",
    "src/core/receipt_backed_asset_lane_composition_v1.py",
)

# Every surviving isinstance on the receipt-admission path, keyed by
# (module, enclosing definition, second-argument source), with its licence.
# Input gates use `type(x) is not T`; isinstance survives only as result
# discrimination on a closed *RejectedV1 return value (never negated, never a
# gate on a caller-supplied value).
_ADMISSION_PATH_ISINSTANCE_INVENTORY = {
    ("src/core/asset_transfer_lane_module_v1.py", "_transition_owned_asset_transfer_lane_module_v1", "AssetTransferRejectedV1"):
        "result discrimination on the inner transition's closed RejectedV1 return",
    ("src/core/asset_transfer_receipt_admission_v1.py", "verify_asset_transfer_fragment_receipt_v1", "ReceiptBackedProducerRejectedV1"):
        "result discrimination on the producer's closed RejectedV1 return",
}


def _isinstance_sites(path: Path) -> list[tuple[str, str, str, bool]]:
    import ast

    tree = ast.parse(path.read_text(encoding="utf-8"))
    sites: list[tuple[str, str, str, bool]] = []

    def visit(node: ast.AST, scope: str, negated_parent: bool) -> None:
        for child in ast.iter_child_nodes(node):
            child_scope = scope
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                child_scope = child.name if not scope else f"{scope}.{child.name}"
            negated = isinstance(child, ast.UnaryOp) and isinstance(child.op, ast.Not)
            if isinstance(child, ast.Call) and getattr(child.func, "id", None) == "isinstance":
                sites.append((str(path.relative_to(_REPO_ROOT)), child_scope, ast.unparse(child.args[1]), negated_parent))
            visit(child, child_scope, negated)

    visit(tree, "", False)
    return sites


def test_admission_path_isinstance_inventory_is_pinned() -> None:
    """Opus P28 F1 audit: an ordinary subclass admitted by isinstance reported a
    genuine root over foreign rows. Rule, pinned mechanically: on the seven
    modules of the receipt-admission path, isinstance may survive only as
    result discrimination on a closed *RejectedV1 return, never as an input
    gate (input gates are exact: type(x) is not T). Adding any isinstance to the
    path fails here until the inventory is amended with a licence."""

    observed: dict[tuple[str, str, str], bool] = {}
    for module in _ADMISSION_PATH_MODULES:
        for path_text, scope, arg, negated in _isinstance_sites(_REPO_ROOT / module):
            key = (path_text, scope.split(".")[-1], arg)
            assert key not in observed, key
            observed[key] = negated
    assert set(observed) == set(_ADMISSION_PATH_ISINSTANCE_INVENTORY), (
        sorted(set(observed) ^ set(_ADMISSION_PATH_ISINSTANCE_INVENTORY))
    )
    for (module, scope, arg), negated in observed.items():
        assert arg.endswith("RejectedV1"), (module, scope, arg)
        assert not negated, (module, scope, arg)
        assert scope != "__post_init__", (module, scope, arg)


class _SpoofedProjection(AssetLaneStateProjectionV1):
    @property
    def state_root(self) -> str:  # type: ignore[override]
        return "0x" + "ab" * 32


def test_asset_lane_composition_accepted_rejects_root_bearing_subclasses() -> None:
    """The third F1 site: AssetLaneCompositionAcceptedV1 compares
    lane_journal.post_lane_root to post_state.state_root, an overridable
    property; a projection subclass reporting a chosen root is refused at the
    exact-type gate before that comparison runs."""

    profile, _ = _profile()
    state = _state(profile, height=1)
    genuine = project_asset_transfer_state_v1(
        _epoch_asset_module_state(profile),
        asset_policy_registry_root=_root(7),
        fee_policy_registry_root=_root(8),
    )
    spoofed = _SpoofedProjection(
        genuine.asset_policy_registry_root,
        genuine.fee_policy_registry_root,
        genuine.balances,
        genuine.custody,
        genuine.supplies,
    )
    assert spoofed.state_root != genuine.state_root
    with pytest.raises(TypeError, match="exact typed value"):
        AssetLaneCompositionAcceptedV1(
            post_state=spoofed,
            effects=_BehaviorBearingEffectPlan((), (), (), (), (), ()),
            lane_journal=object(),  # type: ignore[arg-type]
        )
    del state


# --- C9a''' (P30 verdict repairs): behavioural killers for every declared construction gate ------

def _transfer_accepted_parts():
    from tests.core.test_global_accounting_lane_producers_v1 import _wave_b_accepted

    accepted = _wave_b_accepted()
    return accepted.post_state, accepted.effects, accepted.module_journal


@pytest.mark.parametrize("field", ["post_state", "effects", "module_journal"])
def test_asset_transfer_accepted_rejects_root_bearing_subclasses(field: str) -> None:
    """Fable P30 P2-1: each nested gate of AssetTransferAcceptedV1 has its own killer. A
    subclass of the nested value reporting the genuine root (state_root, effect_plan_root,
    journal_root) over foreign content is refused at the exact-type gate, so the root
    comparisons in __post_init__ never read a property a subclass controls."""

    from src.core.asset_transfer_types_v1 import AssetTransferAcceptedV1, AssetTransferStateV1
    from src.core.global_economic_proof_v1 import LaneModuleTransitionJournalV1
    from src.core.global_settlement_types_v1 import GlobalEconomicEffectPlanV1

    post_state, effects, journal = _transfer_accepted_parts()
    AssetTransferAcceptedV1(post_state, effects, journal)  # the genuine parts construct

    if field == "post_state":
        class SpoofedState(AssetTransferStateV1):
            @property
            def state_root(self) -> str:  # type: ignore[override]
                return post_state.state_root
        parts = (SpoofedState(**{n: getattr(post_state, n) for n in type(post_state).__dataclass_fields__}), effects, journal)
    elif field == "effects":
        class SpoofedPlan(GlobalEconomicEffectPlanV1):
            @property
            def effect_plan_root(self) -> str:  # type: ignore[override]
                return effects.effect_plan_root
        parts = (post_state, SpoofedPlan(**{n: getattr(effects, n) for n in type(effects).__dataclass_fields__}), journal)
    else:
        class SpoofedJournal(LaneModuleTransitionJournalV1):
            @property
            def journal_root(self) -> str:  # type: ignore[override]
                return journal.journal_root
        parts = (post_state, effects, SpoofedJournal(**{n: getattr(journal, n) for n in type(journal).__dataclass_fields__}))
    with pytest.raises(TypeError, match="exact typed value"):
        AssetTransferAcceptedV1(*parts)


def test_projection_sources_reject_state_subclasses() -> None:
    """Fable P30 P2-1: both projection sources are exact gates; a state subclass that
    overrides the rows it projects is refused before any row is read."""

    from src.core.asset_lane_projection_v1 import project_managed_asset_lifecycle_state_v1
    from src.core.asset_transfer_types_v1 import AssetTransferStateV1
    from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1
    from src.core.managed_asset_lifecycle_types_v1 import (
        ManagedAssetClassV1,
        ManagedAssetLifecyclePolicyV1,
        ManagedAssetLifecycleStateV1,
    )

    post_state, _effects, _journal = _transfer_accepted_parts()

    class LooseTransferState(AssetTransferStateV1):
        """A plain subclass; the exact-type gate refuses it before any row is read."""

    loose_transfer = LooseTransferState(**{n: getattr(post_state, n) for n in type(post_state).__dataclass_fields__})
    with pytest.raises(TypeError, match="exact typed value"):
        project_asset_transfer_state_v1(loose_transfer, asset_policy_registry_root=_root(7), fee_policy_registry_root=_root(8))

    policy = ManagedAssetLifecyclePolicyV1(
        asset="USD",
        asset_class=ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN,
        issue_authority_subject="issuer",
        issue_policy_root=_root(5),
        burn_policy_root=_root(6),
        enabled=True,
    )
    managed = ManagedAssetLifecycleStateV1(
        module_release_id=_root(3),
        policies=(policy,),
        balances=(EconomicAmountV1("rich", "USD", "accounts", 5),),
        supplies=(AssetSupplyV1("USD", 5),),
    )

    class LooseManagedState(ManagedAssetLifecycleStateV1):
        """A plain subclass; the exact-type gate refuses it before any row is read."""

    loose_managed = LooseManagedState(**{n: getattr(managed, n) for n in type(managed).__dataclass_fields__})
    with pytest.raises(TypeError, match="exact typed value"):
        project_managed_asset_lifecycle_state_v1(loose_managed, asset_policy_registry_root=_root(7), fee_policy_registry_root=_root(8))


@pytest.mark.parametrize("side", ["pre_state", "post_state"])
def test_asset_lane_private_port_rejects_projection_subclasses(side: str) -> None:
    """Opus P30 NEW-3: both port projection gates have a killer (the P30 test covered only
    post_state)."""

    from src.core.asset_lane_projection_v1 import AssetLanePrivatePortV1
    from tests.core.test_global_accounting_lane_producers_v1 import _wave_b_accepted

    port = _wave_b_accepted().private_port
    genuine = getattr(port, side)
    spoofed = _SpoofedProjection(
        genuine.asset_policy_registry_root,
        genuine.fee_policy_registry_root,
        genuine.balances,
        genuine.custody,
        genuine.supplies,
    )
    kwargs = {n: getattr(port, n) for n in type(port).__dataclass_fields__}
    kwargs[side] = spoofed
    with pytest.raises(TypeError, match="exact typed value"):
        AssetLanePrivatePortV1(**kwargs)


def test_receipt_backed_composition_candidate_rejects_subclasses() -> None:
    """Opus P30 NEW-4: the receipt-backed composition candidate's seven input gates are
    exact; a private-port subclass reporting the genuine port root is refused at
    construction, before any composition reads a root through a property."""

    from src.core.asset_lane_projection_v1 import AssetLanePrivatePortV1
    from src.core.receipt_backed_asset_lane_composition_v1 import (
        ReceiptBackedAssetLaneCompositionCandidateV1,
    )
    from tests.core.test_global_accounting_lane_producers_v1 import _wave_b_accepted

    accepted = _wave_b_accepted()
    port = accepted.private_port

    class SpoofedPort(AssetLanePrivatePortV1):
        @property
        def port_root(self) -> str:  # type: ignore[override]
            return port.port_root

    spoofed = SpoofedPort(**{n: getattr(port, n) for n in type(port).__dataclass_fields__})
    with pytest.raises(TypeError, match="exact typed value"):
        ReceiptBackedAssetLaneCompositionCandidateV1(
            profile=object(),  # type: ignore[arg-type]
            occurrence=object(),  # type: ignore[arg-type]
            coordinator_context=object(),  # type: ignore[arg-type]
            module_journal=accepted.module_journal,
            private_port=spoofed,
            module_effects=accepted.effects,
            verified_module=object(),  # type: ignore[arg-type]
        )
