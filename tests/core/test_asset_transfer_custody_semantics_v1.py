"""Custody semantic selection: literal derivation, root decision table, and controls.

The fixture builders here are shared with the custody release-route binder
tests. Every governed identity (release ids, registry roots, profile id, route
id, occurrence) is rebuilt coherently from the requested specification roots,
so a rejection isolates the semantic guard rather than a stale identity. No
test here claims receipt, activation, or publication authority.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
import json
from dataclasses import dataclass, fields
from pathlib import Path
from types import SimpleNamespace

import pytest

from src.core import asset_transfer_custody_semantics_v1 as semantics
from src.core.asset_transfer_custody_semantics_v1 import (
    ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1,
    require_asset_transfer_custody_semantics_v1,
)
from src.core.asset_transfer_policy_registry_v1 import (
    ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
    ASSET_TRANSFER_FEE_POLICY_KIND_V1,
    AssetTransferPolicyRegistryV1,
)
from src.core.asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferCommandV1,
    AssetTransferPolicyV1,
)
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    REQUIRED_ACTIVE_EVIDENCE_V1,
    ZERO_ROOT_V1,
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    EvidenceStatusV1,
    LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    LaneRegistryV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteRegistryV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from src.core.managed_asset_lifecycle_types_v1 import MANAGED_ASSET_ISSUE_COMMAND_KIND_V1
from src.state.canonical import domain_sep_bytes

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
BUNDLE_PATH = REPOSITORY_ROOT / "docs" / "specifications" / (
    "asset-transfer-custody-semantic-bundle-v1.json"
)
BUNDLE_DOMAIN = "zenodex/asset-transfer-custody-semantic-bundle/v1"
BUNDLE_SHA256 = "4b16964671cd4e4f4585437ad632eb5aa13fee17a5f49c65a96b59335b43ba72"
BUNDLE_BYTE_LENGTH = 3_333
ROOT = ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1


def _root(value: int) -> str:
    return f"0x{value:064x}"


LEGACY_ROOT = _root(0x1E6AC7)
"""A fixture-style root of the legacy semantic family; never the custody root."""


@dataclass(frozen=True, slots=True)
class _SemanticRootsV1:
    """Specification roots carried by the ASSET module, coordinator, and route."""

    module: str = ROOT
    coordinator: str = ROOT
    route: str = ROOT


@dataclass(frozen=True, slots=True)
class _ReleaseMetadataV1:
    """Non-selecting release metadata: version text plus image/source/toolchain seeds."""

    semantic_version: str = "1.0.0-custody-test"
    root_seed: int = 1_000


_MATCHING_ROOTS = _SemanticRootsV1()
_LEGACY_ROOTS = _SemanticRootsV1(LEGACY_ROOT, LEGACY_ROOT, LEGACY_ROOT)
_DEFAULT_METADATA = _ReleaseMetadataV1()
_SPOOFED_METADATA = _ReleaseMetadataV1("9.9.9-custody-complete-successor", 5_000)
_COMMAND = AssetTransferCommandV1(ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "alice", "bob", 30, 2)


@dataclass(frozen=True, slots=True)
class _CustodyGovernanceV1:
    """One profile whose ASSET module, coordinator, and transfer route carry given roots."""

    profile: EconomicProfileSnapshotV1
    route: RouteReleaseV1
    policy_registry: EconomicPolicyRegistryV1
    asset_policy_registry: AssetTransferPolicyRegistryV1


def _active_evidence() -> tuple[EvidenceStatusV1, ...]:
    return tuple(sorted(REQUIRED_ACTIVE_EVIDENCE_V1, key=lambda item: item.value))


def _lane_release(
    lane_id: LaneIdV1,
    ordinal: int,
    *,
    active: bool,
    specification_root: str,
    metadata: _ReleaseMetadataV1,
) -> LaneModuleReleaseV1:
    offset = ordinal * 16
    return LaneModuleReleaseV1.build(
        lane_id=lane_id,
        semantic_version=metadata.semantic_version,
        state_schema_root=_root(100 + offset),
        command_variants=(ASSET_TRANSFER_COMMAND_KIND_V1,) if active else (),
        terminal_command_variants=(),
        guest_image_id=_root(metadata.root_seed + offset + 1),
        specification_root=specification_root,
        source_root=_root(metadata.root_seed + offset + 2),
        toolchain_root=_root(metadata.root_seed + offset + 3),
        terminal_coverage_root=_root(105 + offset),
        migration_compatibility_root=_root(106 + offset),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if active else ReleaseStatusV1.SHADOW,
        accepts_new_objects=active,
        evidence_statuses=(
            _active_evidence() if active else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _coordinator_release(
    lane_id: LaneIdV1,
    ordinal: int,
    *,
    active: bool,
    specification_root: str,
    metadata: _ReleaseMetadataV1,
) -> LaneCoordinatorReleaseV1:
    offset = 300 + ordinal * 16
    return LaneCoordinatorReleaseV1.build(
        lane_id=lane_id,
        semantic_version=metadata.semantic_version,
        coordinator_schema_root=_root(offset),
        guest_image_id=_root(metadata.root_seed + offset + 1),
        specification_root=specification_root,
        source_root=_root(metadata.root_seed + offset + 2),
        toolchain_root=_root(metadata.root_seed + offset + 3),
        max_cycles=1_000_000,
        max_journal_bytes=65_536,
        status=ReleaseStatusV1.ACTIVE_NEW if active else ReleaseStatusV1.SHADOW,
        accepts_new_objects=active,
        evidence_statuses=(
            _active_evidence() if active else (EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,)
        ),
    )


def _route_release(
    lane_registry: LaneRegistryV1,
    *,
    route_lanes: tuple[LaneIdV1, ...],
    specification_root: str,
    metadata: _ReleaseMetadataV1,
    status: ReleaseStatusV1,
) -> RouteReleaseV1:
    active = status is ReleaseStatusV1.ACTIVE_NEW
    return RouteReleaseV1.build(
        semantic_version=metadata.semantic_version,
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
        ordered_lanes=route_lanes,
        module_release_ids=tuple(
            lane_registry.release_for(lane_id).release_id for lane_id in route_lanes
        ),
        dependency_roles=tuple(f"VALUE_OWNER_{index}" for index in range(len(route_lanes))),
        port_schema_roots=tuple(_root(500 + index) for index in range(len(route_lanes))),
        guest_image_id=_root(metadata.root_seed + 601),
        specification_root=specification_root,
        source_root=_root(metadata.root_seed + 602),
        toolchain_root=_root(metadata.root_seed + 603),
        oracle_policy_root=_root(510),
        issue_burn_policy_root=_root(511),
        max_cycles=2_000_000,
        max_journal_bytes=131_072,
        status=status,
        accepts_new_objects=active,
        evidence_statuses=_active_evidence() if active else (),
    )


def _governance(
    roots: _SemanticRootsV1 = _MATCHING_ROOTS,
    *,
    metadata: _ReleaseMetadataV1 = _DEFAULT_METADATA,
    profile_status: ProfileStatusV1 = ProfileStatusV1.ACTIVE,
    route_status: ReleaseStatusV1 = ReleaseStatusV1.ACTIVE_NEW,
    route_lanes: tuple[LaneIdV1, ...] = (LaneIdV1.ASSET_TRANSFER,),
) -> _CustodyGovernanceV1:
    """Coherently rebuild every governed identity from the requested roots.

    The ASSET lane stays active even when the route names another lane, so a
    lane-shape rejection cannot be confused with a disabled module. Lanes other
    than ASSET carry unrelated specification roots to show they never select.
    """

    active_lanes = {LaneIdV1.ASSET_TRANSFER, *route_lanes}
    lane_registry = LaneRegistryV1(
        tuple(
            _lane_release(
                lane_id,
                ordinal,
                active=lane_id in active_lanes,
                specification_root=(
                    roots.module
                    if lane_id is LaneIdV1.ASSET_TRANSFER
                    else _root(102 + ordinal * 16)
                ),
                metadata=metadata,
            )
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    coordinator_registry = LaneCoordinatorRegistryV1(
        tuple(
            _coordinator_release(
                lane_id,
                ordinal,
                active=lane_id in active_lanes,
                specification_root=(
                    roots.coordinator
                    if lane_id is LaneIdV1.ASSET_TRANSFER
                    else _root(302 + ordinal * 16)
                ),
                metadata=metadata,
            )
            for ordinal, lane_id in enumerate(ALL_LANE_IDS_V1, start=1)
        )
    )
    route = _route_release(
        lane_registry,
        route_lanes=route_lanes,
        specification_root=roots.route,
        metadata=metadata,
        status=route_status,
    )
    asset_release = lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    asset_policy_registry = AssetTransferPolicyRegistryV1(
        asset_release.release_id,
        (AssetTransferPolicyV1("USD", "treasury", 2, True),),
    )
    policy_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (
                    EconomicPolicyBindingV1(
                        ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
                        ASSET_TRANSFER_COMMAND_KIND_V1,
                        asset_policy_registry.asset_policy_root,
                    ),
                    EconomicPolicyBindingV1(
                        ASSET_TRANSFER_FEE_POLICY_KIND_V1,
                        ASSET_TRANSFER_COMMAND_KIND_V1,
                        asset_policy_registry.fee_policy_root,
                    ),
                ),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    profile = EconomicProfileSnapshotV1.build(
        authority_epoch=7,
        lane_registry=lane_registry,
        lane_coordinator_registry=coordinator_registry,
        route_registry=RouteRegistryV1((route,)),
        proof_shape_root=_root(520),
        root_image_id=_root(521),
        verifier_registry_root=_root(522),
        migration_registry_root=_root(523),
        policy_registry_root=policy_registry.registry_root,
        terminal_registry_root=_root(525),
        status=profile_status,
    )
    return _CustodyGovernanceV1(profile, route, policy_registry, asset_policy_registry)


def _occurrence(
    governance: _CustodyGovernanceV1,
    *,
    command_kind: str = ASSET_TRANSFER_COMMAND_KIND_V1,
    route_release_id: str | None = None,
    profile_root: str | None = None,
    subject_id: str = "alice",
) -> EconomicCommandOccurrenceV1:
    return EconomicCommandOccurrenceV1(
        chain_id="zeno-custody-route-test",
        deployment_root=_root(1),
        height=11,
        tx_index=2,
        op_index=3,
        command_kind=command_kind,
        command_body_hash=_COMMAND.command_body_hash,
        route_release_id=(
            governance.route.route_release_id if route_release_id is None else route_release_id
        ),
        subject_id=subject_id,
        grant_root=_root(7),
        nonce=9,
        profile_root=governance.profile.profile_id if profile_root is None else profile_root,
        pre_state_root=_root(2),
        consumed_object_ids=(),
    )


def _bundle_value() -> dict[str, object]:
    value = json.loads(BUNDLE_PATH.read_bytes())
    if type(value) is not dict:
        raise AssertionError("custody bundle must decode to a JSON object")
    return value


def _foreign_roots() -> _SemanticRootsV1:
    """Three distinct unknown roots: a mutated bundle, a wrong domain, a fixture root."""

    value = _bundle_value()
    return _SemanticRootsV1(
        module=hash_global_v1(BUNDLE_DOMAIN, {**value, "family": "CUSTODY_COMPLETE_V2"}),
        coordinator=hash_global_v1("zenodex/asset-transfer-custody-semantic-bundle/v2", value),
        route=LEGACY_ROOT,
    )


def _selection_observation(
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> bytes:
    return canonical_global_bytes_v1({"profile": profile, "occurrence": occurrence})


def test_specification_root_literal_is_derived_from_committed_canonical_bundle_bytes() -> None:
    # Arrange: the committed bytes are the only input; the runtime literal is the claim.
    raw = BUNDLE_PATH.read_bytes()

    # Act
    value = json.loads(raw)
    hand_rolled_root = "0x" + hashlib.sha256(domain_sep_bytes(BUNDLE_DOMAIN, version=1) + raw).hexdigest()

    # Assert: exact byte subject, canonical preimage, and both root derivations agree.
    assert len(raw) == BUNDLE_BYTE_LENGTH
    assert not raw.endswith(b"\n")
    assert hashlib.sha256(raw).hexdigest() == BUNDLE_SHA256
    assert raw == canonical_global_bytes_v1(value)
    assert value["schema"] == BUNDLE_DOMAIN
    assert hash_global_v1(BUNDLE_DOMAIN, value) == ROOT
    assert hash_global_v1(value["schema"], value) == ROOT
    assert hand_rolled_root == ROOT
    assert len(ROOT) == 66 and ROOT.startswith("0x") and ROOT == ROOT.lower()
    assert ROOT != ZERO_ROOT_V1 and len(bytes.fromhex(ROOT[2:])) == 32
    # The identity commits semantic text only; foreign families derive other roots.
    foreign = _foreign_roots()
    assert len({ROOT, foreign.module, foreign.coordinator, foreign.route}) == 4


def test_bundle_selection_text_matches_the_selector_one_lane_contract() -> None:
    value = _bundle_value()
    selection = value["selection"]
    assert type(selection) is dict
    assert value["command_kind"] == ASSET_TRANSFER_COMMAND_KIND_V1
    assert value["lane_id"] == LaneIdV1.ASSET_TRANSFER.value
    assert selection["ordered_lanes"] == [LaneIdV1.ASSET_TRANSFER.value]
    assert selection["occurrences_per_route"] == 1
    assert selection["module_coordinator_route_subject"] == "this_bundle"
    assert "authority" in value and "no cryptographic verification" in str(value["authority"])


def test_runtime_module_carries_the_literal_without_file_io_or_callbacks() -> None:
    tree = ast.parse(inspect.getsource(semantics))
    absolute_imports = {
        alias.name.split(".")[0]
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    } | {
        node.module.split(".")[0]
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module is not None and node.level == 0
    }
    relative_imports = {
        node.module
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 1
    }
    called_names = {
        node.func.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    literal_assignments = [
        node.value.value
        for node in ast.walk(tree)
        if isinstance(node, ast.AnnAssign)
        and isinstance(node.target, ast.Name)
        and node.target.id == "ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1"
        and isinstance(node.value, ast.Constant)
    ]

    assert semantics.__all__ == [
        "ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1",
        "require_asset_transfer_custody_semantics_v1",
    ]
    # The root is a source literal, not a value computed or loaded at runtime.
    assert literal_assignments == [ROOT]
    assert absolute_imports == {"__future__", "typing"}
    assert relative_imports == {
        "asset_transfer_types_v1",
        "global_economic_proof_v1",
        "global_settlement_types_v1",
    }
    assert "open" not in called_names
    assert not {"open", "Path", "os", "io", "json", "pathlib"} & set(vars(semantics))
    parameters = inspect.signature(require_asset_transfer_custody_semantics_v1).parameters
    assert list(parameters) == ["profile", "occurrence"]
    assert all(parameter.default is inspect.Parameter.empty for parameter in parameters.values())


@pytest.mark.parametrize("metadata", (_DEFAULT_METADATA, _SPOOFED_METADATA))
def test_matching_roots_select_regardless_of_metadata_and_leave_inputs_unchanged(
    metadata: _ReleaseMetadataV1,
) -> None:
    # Arrange: matching roots; version text, image, source, and toolchain vary freely.
    governance = _governance(metadata=metadata)
    occurrence = _occurrence(governance)
    before = _selection_observation(governance.profile, occurrence)

    # Act
    require_asset_transfer_custody_semantics_v1(governance.profile, occurrence)

    # Assert: selection preserves the complete input observation.
    assert _selection_observation(governance.profile, occurrence) == before


@pytest.mark.parametrize(
    ("module_matches", "coordinator_matches", "route_matches"),
    (
        (False, True, True),
        (True, False, True),
        (True, True, False),
        (False, False, True),
        (False, True, False),
        (True, False, False),
        (False, False, False),
    ),
)
def test_unknown_or_mixed_root_families_reject_with_the_first_nonmatching_role(
    module_matches: bool,
    coordinator_matches: bool,
    route_matches: bool,
) -> None:
    # Arrange: each nonmatching role carries its own distinct unknown root.
    foreign = _foreign_roots()
    roots = _SemanticRootsV1(
        module=ROOT if module_matches else foreign.module,
        coordinator=ROOT if coordinator_matches else foreign.coordinator,
        route=ROOT if route_matches else foreign.route,
    )
    governance = _governance(roots)
    occurrence = _occurrence(governance)
    before = _selection_observation(governance.profile, occurrence)
    expected_label = next(
        label
        for matches, label in (
            (module_matches, "module"),
            (coordinator_matches, "coordinator"),
            (route_matches, "route"),
        )
        if not matches
    )

    # Act / Assert
    with pytest.raises(
        ValueError,
        match=f"custody semantics {expected_label} specification root mismatch",
    ):
        require_asset_transfer_custody_semantics_v1(governance.profile, occurrence)
    assert _selection_observation(governance.profile, occurrence) == before


def test_metadata_spoof_with_nonmatching_specification_root_rejects() -> None:
    # Arrange: successor-looking version text, image, source, and toolchain roots
    # on every role, with the legacy specification root left in place.
    governance = _governance(_LEGACY_ROOTS, metadata=_SPOOFED_METADATA)
    occurrence = _occurrence(governance)

    # Act / Assert: metadata cannot select; the specification root decides.
    with pytest.raises(ValueError, match="custody semantics module specification root mismatch"):
        require_asset_transfer_custody_semantics_v1(governance.profile, occurrence)


def test_route_status_and_accepts_new_objects_boundary_rejects_at_governed_lookup() -> None:
    # Arrange: a SHADOW route (accepts_new_objects False) needs a non-ACTIVE profile.
    disabled = _governance(profile_status=ProfileStatusV1.SHADOW, route_status=ReleaseStatusV1.SHADOW)
    enabled = _governance(profile_status=ProfileStatusV1.SHADOW)

    # Act / Assert: the boolean/status boundary rejects before any root comparison.
    with pytest.raises(ValueError, match="command route is disabled for new objects"):
        require_asset_transfer_custody_semantics_v1(disabled.profile, _occurrence(disabled))
    # Profile activation is the structural binder's obligation, not the selector's;
    # the custody binder tests show a SHADOW profile rejects before recomputation.
    require_asset_transfer_custody_semantics_v1(enabled.profile, _occurrence(enabled))


def test_command_kind_route_claim_and_missing_route_controls_reject() -> None:
    governance = _governance()

    with pytest.raises(ValueError, match="custody semantics require an asset transfer command"):
        require_asset_transfer_custody_semantics_v1(
            governance.profile,
            _occurrence(governance, command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V1),
        )
    with pytest.raises(ValueError, match="caller-selected route does not match governed route"):
        require_asset_transfer_custody_semantics_v1(
            governance.profile,
            _occurrence(governance, route_release_id=_root(998)),
        )
    routeless = EconomicProfileSnapshotV1.build(
        authority_epoch=governance.profile.authority_epoch,
        lane_registry=governance.profile.lane_registry,
        lane_coordinator_registry=governance.profile.lane_coordinator_registry,
        route_registry=RouteRegistryV1(()),
        proof_shape_root=governance.profile.proof_shape_root,
        root_image_id=governance.profile.root_image_id,
        verifier_registry_root=governance.profile.verifier_registry_root,
        migration_registry_root=governance.profile.migration_registry_root,
        policy_registry_root=governance.profile.policy_registry_root,
        terminal_registry_root=governance.profile.terminal_registry_root,
        status=ProfileStatusV1.ACTIVE,
    )
    with pytest.raises(ValueError, match="unknown or unregistered command kind"):
        require_asset_transfer_custody_semantics_v1(
            routeless,
            _occurrence(governance, profile_root=routeless.profile_id),
        )


@pytest.mark.parametrize(
    "route_lanes",
    (
        (LaneIdV1.ASSET_TRANSFER, LaneIdV1.SPOT_LIQUIDITY),
        (LaneIdV1.SPOT_LIQUIDITY,),
    ),
)
def test_route_lane_shape_must_be_exactly_the_single_asset_transfer_lane(
    route_lanes: tuple[LaneIdV1, ...],
) -> None:
    # Arrange: matching roots everywhere; only the route lane shape differs.
    governance = _governance(route_lanes=route_lanes)

    # Act / Assert
    with pytest.raises(ValueError, match="single-lane ASSET_TRANSFER route"):
        require_asset_transfer_custody_semantics_v1(governance.profile, _occurrence(governance))


def test_empty_route_lanes_are_unrepresentable_at_the_type() -> None:
    governance = _governance()
    with pytest.raises(ValueError, match="between one and eight"):
        _route_release(
            governance.profile.lane_registry,
            route_lanes=(),
            specification_root=ROOT,
            metadata=_DEFAULT_METADATA,
            status=ReleaseStatusV1.ACTIVE_NEW,
        )


def test_route_module_release_membership_is_checked_before_roots() -> None:
    # Arrange: bypass profile validation to detach the route from the selected module.
    governance = _governance()
    occurrence = _occurrence(governance)
    object.__setattr__(governance.route, "module_release_ids", (_root(999),))

    # Act / Assert: the explicit membership check is load-bearing on its own.
    with pytest.raises(ValueError, match="custody semantics route module release mismatch"):
        require_asset_transfer_custody_semantics_v1(governance.profile, occurrence)


def test_exact_type_requirements_reject_subclasses_and_duck_types() -> None:
    governance = _governance()
    occurrence = _occurrence(governance)

    class _HostileProfile(EconomicProfileSnapshotV1):
        pass

    hostile_profile = _HostileProfile(
        *(getattr(governance.profile, field.name) for field in fields(EconomicProfileSnapshotV1))
    )
    with pytest.raises(TypeError, match="custody semantics profile type is not closed"):
        require_asset_transfer_custody_semantics_v1(hostile_profile, occurrence)
    duck_occurrence = SimpleNamespace(
        command_kind=occurrence.command_kind,
        route_release_id=occurrence.route_release_id,
    )
    with pytest.raises(TypeError, match="custody semantics occurrence type is not closed"):
        require_asset_transfer_custody_semantics_v1(
            governance.profile,
            duck_occurrence,  # type: ignore[arg-type]
        )
