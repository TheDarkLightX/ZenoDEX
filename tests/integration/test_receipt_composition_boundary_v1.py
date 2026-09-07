"""Exact coordinator and route execution evidence over explicitly simulated RISC0 replies.

These cases use the real measured-port factory and transport with the existing
synthetic process fixture. They establish phase/subject binding and logical
no-write behavior, not a genuine receipt, release or production qualification.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
import textwrap
from collections.abc import Callable
from dataclasses import dataclass, replace
from dataclasses import fields as dataclass_fields
from pathlib import Path
from typing import cast

import pytest

from src.core import global_economic_proof_v1 as proof
from src.core import lane_composition_receipt_verification_v1 as lane_core
from src.core import receipt_backed_asset_lane_composition_v1 as asset_structural
from src.core import receipt_backed_perps_margin_lane_composition_v1 as perps_structural
from src.core import route_composition_receipt_verification_v1 as route_core
from src.core.economic_receipt_verifier_registry_v1 import EconomicReceiptVerifierRegistryV1
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    canonical_global_bytes_v1,
)
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from src.integration import isolated_profile_receipt_ports_v1 as ports
from src.integration import lane_composition_receipt_verification_v1 as lane_shell
from src.integration import route_composition_receipt_verification_v1 as route_shell
from tests.core import receipt_composition_fixtures_v1 as unit
from tests.core.test_economic_receipt_verifier_release_v1 import _release
from tests.integration import asset_receipt_pipeline_fixtures_v1 as fixtures
from tests.integration import publisher_receipt_port_fixtures_v1 as process
from tests.integration.test_isolated_asset_receipt_pipeline_v1 import _bind, _verify

simulated_measured_publisher_crypto_v1 = process.simulated_measured_publisher_crypto_v1
_ROOT = "0x" + "ab" * 32
_BYTE_FIELDS = ("receipt_bytes", "expected_journal_bytes")
_LANE_FIELDS = (
    "profile_id", "route_release_id", "lane_id", "coordinator_release_id",
    "command_occurrence_id", "writer_epoch", "structural_composition_root",
    "lane_journal_root", "lane_journal_digest", "expected_image_id", "receipt_digest",
    "receipt_kind",
)
_ROUTE_FIELDS = (
    "profile_id", "route_release_id", "command_occurrence_id", "writer_epoch",
    "ordered_lane_ids", "ordered_lane_binding_roots", "ordered_lane_journal_roots",
    "route_journal_root", "route_journal_digest", "expected_image_id", "receipt_digest",
    "receipt_kind",
)
_FAMILY_NAMES = ("coordinator", "route")


@dataclass(frozen=True)
class _Family:
    """One extracted receipt family: its core phases, shell wrapper and port role method."""

    name: str
    core: object
    shell_verify: Callable[..., object]
    prepare: Callable[[object], object]
    bind: Callable[..., object]
    snapshot: Callable[[object], object]
    prepared_type: type
    prepared_token: object
    execution_type: type
    execution_token: object
    port_method: str
    fields_attr: str
    witness_fields: tuple[str, ...]
    journal_digest_field: str
    expected_index: int


_FAMILIES = {
    "coordinator": _Family(
        "coordinator", lane_core, lane_shell.verify_asset_lane_composition_receipt_v1,
        lane_core.prepare_asset_lane_composition_receipt_v1,
        lane_core.bind_verified_lane_composition_receipt_v1,
        lane_core.snapshot_prepared_lane_composition_receipt_v1,
        lane_core.PreparedLaneCompositionReceiptV1,
        lane_core._PREPARED_LANE_COMPOSITION_RECEIPT_TOKEN_V1,
        lane_core.VerifiedLaneCompositionReceiptExecutionV1,
        lane_core._VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
        "verify_prepared_coordinator_receipt_v1", "composition_fields", _LANE_FIELDS,
        "lane_journal_digest", 1,
    ),
    "route": _Family(
        "route", route_core, route_shell.verify_route_composition_receipt_v1,
        route_core.prepare_route_composition_receipt_v1,
        route_core.bind_verified_route_composition_receipt_v1,
        route_core.snapshot_prepared_route_composition_receipt_v1,
        route_core.PreparedRouteCompositionReceiptV1,
        route_core._PREPARED_ROUTE_COMPOSITION_RECEIPT_TOKEN_V1,
        route_core.VerifiedRouteCompositionReceiptExecutionV1,
        route_core._VERIFIED_ROUTE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
        "verify_prepared_route_receipt_v1", "route_fields", _ROUTE_FIELDS,
        "route_journal_digest", 2,
    ),
}


@dataclass(frozen=True)
class _Stage:
    candidate: object
    prepared: object
    port: ports.IsolatedReceiptPortV1
    expected: tuple[object, ...]
    expected_row: tuple[object, ...]


@dataclass(frozen=True)
class _Boundary:
    subject: fixtures._Fixture
    scope: ports.IsolatedProfileReceiptPortsV1
    stages: dict[str, _Stage]
    pre_bytes: bytes


@dataclass
class _SyntheticBackend:
    """Synthetic process reply for expected statements only; never cryptographic evidence."""

    expected: tuple[tuple[object, ...], ...]
    calls: list[tuple[object, ...]]

    def verify_succinct_receipt(self, receipt, *, expected_image_id, expected_journal_bytes):
        row = (receipt, expected_image_id, expected_journal_bytes)
        self.calls.append(row)
        if row not in self.expected:
            raise ValueError("synthetic receipt statement rejected")


def _witness(witness, names: tuple[str, ...]) -> tuple[object, ...]:
    values = tuple(getattr(witness, name) for name in names) + (witness.binding_root,)
    if names is _ROUTE_FIELDS:
        values += (witness.assumption_root,)
    return values


@pytest.fixture
def boundary(simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch) -> _Boundary:
    subject = fixtures._fixture(simulated_measured_publisher_crypto_v1)
    captured: dict[str, tuple[object, ports.IsolatedReceiptPortV1]] = {}

    def capture(name: str, shell_verify):
        def call(candidate, receipt_verifier):
            captured[name] = (candidate, receipt_verifier)
            return shell_verify(candidate, receipt_verifier)

        return call

    # Acquire the actual coordinator and route candidates through the existing pipeline.
    with monkeypatch.context() as patch:
        patch.setattr(
            pipeline, "verify_asset_lane_composition_receipt_v1",
            capture("coordinator", lane_shell.verify_asset_lane_composition_receipt_v1),
        )
        patch.setattr(
            pipeline, "verify_route_composition_receipt_v1",
            capture("route", route_shell.verify_route_composition_receipt_v1),
        )
        result = _verify(_bind(subject), subject)
    assert sorted(captured) == list(_FAMILY_NAMES)
    lane_candidate, lane_port = captured["coordinator"]
    route_candidate, route_port = captured["route"]
    scope = process.bind_publisher_test_receipt_ports_v1(subject.candidate, subject)
    subject.calls.clear()
    stages = {
        "coordinator": _Stage(
            lane_candidate, lane_core.prepare_asset_lane_composition_receipt_v1(lane_candidate),
            lane_port, _witness(route_candidate.verified_lanes[0], _LANE_FIELDS),
            subject.expected[1],
        ),
        "route": _Stage(
            route_candidate, route_core.prepare_route_composition_receipt_v1(route_candidate),
            route_port, _witness(result.candidate.verified_routes[0], _ROUTE_FIELDS),
            subject.expected[2],
        ),
    }
    return _Boundary(subject, scope, stages, canonical_global_bytes_v1(subject.candidate.pre_state))


def _stage(boundary: _Boundary, family_name: str) -> tuple[_Family, _Stage]:
    return _FAMILIES[family_name], boundary.stages[family_name]


def _execute(port: ports.IsolatedReceiptPortV1, family: _Family, prepared):
    return getattr(port, family.port_method)(prepared)


def _bind_execution(family: _Family, stage: _Stage, prepared, execution):
    return family.bind(
        prepared, execution, expected_verifier_binding_root=stage.port.verifier_binding_root
    )


def _select_port(boundary: _Boundary, role: str) -> ports.IsolatedReceiptPortV1:
    profile = boundary.subject.candidate.profile
    return {
        "root": boundary.scope.root_port,
        "module": lambda: boundary.scope.module_port(LaneIdV1.ASSET_TRANSFER),
        "coordinator": lambda: boundary.scope.coordinator_port(LaneIdV1.ASSET_TRANSFER),
        "route": lambda: boundary.scope.route_port(profile.route_registry.routes[0].route_release_id),
    }[role]()


def _foreign_value(field: str, current: object) -> object:
    if field == "lane_id":
        return LaneIdV1.SPOT_LIQUIDITY
    if field == "writer_epoch":
        return cast(int, current) + 1
    if field == "ordered_lane_ids":
        return (LaneIdV1.SPOT_LIQUIDITY,)
    if field in ("ordered_lane_binding_roots", "ordered_lane_journal_roots"):
        return (_ROOT,)
    if field in _BYTE_FIELDS:
        return cast(bytes, current) + b" changed"
    return _ROOT


def _changed_prepared(family: _Family, prepared, **changes: object):
    """Construct one explicit malformed subject for the independent field matrix.

    This test-only token use supplies no real preparation authority. Every row
    must be rejected by the production evidence consumer or measured role port.
    """
    original = prepared._fields
    outer = {name: value for name, value in changes.items() if name in _BYTE_FIELDS}
    inner = {name: value for name, value in changes.items() if name not in _BYTE_FIELDS}
    fields = replace(getattr(original, family.fields_attr), **inner)
    return family.prepared_type(
        family.prepared_token, replace(original, **{family.fields_attr: fields}, **outer)
    )


def _zero_hash_for_domain(monkeypatch: pytest.MonkeyPatch, module, domain: str) -> None:
    """Selective hash-function substitution: exactly one hash domain returns the zero root.

    A synthetic hash-domain control, not a preimage claim. It exposes a changed
    acceptance domain for one computed root without touching any other root, so the
    old entry point's own bindings stay satisfied.
    """
    real = module.hash_global_v1

    def selective(hash_domain: str, value: object) -> str:
        return ZERO_ROOT_V1 if hash_domain == domain else real(hash_domain, value)

    monkeypatch.setattr(module, "hash_global_v1", selective)


def _core_effect_calls(source: str) -> tuple[str, ...]:
    forbidden = {
        "verify_succinct_receipt", "verify_prepared_module_receipt_v1",
        "verify_prepared_coordinator_receipt_v1", "verify_prepared_route_receipt_v1",
    }
    return tuple(
        node.func.attr
        for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in forbidden
    )


@pytest.mark.parametrize(
    ("core", "prepares"),
    (
        (
            lane_core,
            (
                "prepare_asset_lane_composition_receipt_v1",
                "prepare_perps_margin_lane_composition_receipt_v1",
            ),
        ),
        (route_core, ("prepare_route_composition_receipt_v1",)),
    ),
)
def test_core_preparation_and_binding_have_no_receipt_callback_or_shell_import(core, prepares):
    source = Path(core.__file__).read_text()
    assert _core_effect_calls(source) == ()
    for name in prepares:
        assert tuple(inspect.signature(getattr(core, name)).parameters) == ("candidate",)
        assert name in core.__all__
    imports = tuple(
        node.module or "" for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.ImportFrom)
    )
    assert all("integration" not in name for name in imports)
    assert all(not name.startswith("verify_") for name in core.__all__)
    # A prohibited effect inserted into the same surface is detected by this check.
    specimen = source + "\ndef prohibited(port):\n    port.verify_succinct_receipt(b'x')\n"
    assert _core_effect_calls(specimen) == ("verify_succinct_receipt",)


def test_shell_wrappers_keep_existing_names_with_exact_factory_port_parameters():
    expected = (
        (
            lane_shell,
            (
                "verify_asset_lane_composition_receipt_v1",
                "verify_perps_margin_lane_composition_receipt_v1",
            ),
        ),
        (route_shell, ("verify_route_composition_receipt_v1",)),
    )
    for module, names in expected:
        assert tuple(module.__all__) == names
        for name in names:
            signature = inspect.signature(getattr(module, name))
            assert tuple(signature.parameters) == ("candidate", "receipt_verifier")
            assert signature.parameters["receipt_verifier"].annotation == "IsolatedReceiptPortV1"
    assert pipeline.verify_asset_lane_composition_receipt_v1 is (
        lane_shell.verify_asset_lane_composition_receipt_v1
    )
    assert pipeline.verify_route_composition_receipt_v1 is (
        route_shell.verify_route_composition_receipt_v1
    )


def test_pipeline_supplies_coordinator_and_route_role_ports_to_the_shell(boundary):
    coordinator = ports._CALLS[boundary.stages["coordinator"].port]
    route = ports._CALLS[boundary.stages["route"].port]
    assert coordinator.role is ports._ReceiptRoleV1.COORDINATOR
    assert coordinator.lane_id is LaneIdV1.ASSET_TRANSFER
    assert coordinator.release_id == boundary.stages["coordinator"].prepared.coordinator_release_id
    assert route.role is ports._ReceiptRoleV1.ROUTE
    assert route.lane_id is None
    assert route.release_id == boundary.stages["route"].prepared.route_release_id
    for authority, stage in ((coordinator, boundary.stages["coordinator"]), (route, boundary.stages["route"])):
        assert authority.profile.profile.profile_id == stage.prepared.profile_root


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_preparation_is_owned_and_only_measured_execution_mints_bound_result(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    prepared = family.prepare(stage.candidate)
    assert boundary.subject.calls == []
    assert (
        prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes
    ) == stage.expected_row
    execution = _execute(stage.port, family, prepared)
    result = _bind_execution(family, stage, prepared, execution)
    assert _witness(result, family.witness_fields) == stage.expected
    # Exact re-binding is deterministic and executes no additional verifier call.
    assert _witness(_bind_execution(family, stage, prepared, execution), family.witness_fields) == (
        stage.expected
    )
    assert boundary.subject.calls == [stage.expected_row]
    # The shell wrapper reaches the same witness through the same single statement.
    assert _witness(family.shell_verify(stage.candidate, stage.port), family.witness_fields) == (
        stage.expected
    )
    assert boundary.subject.calls == [stage.expected_row, stage.expected_row]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def _governed_perps_profile(original: Callable[[], tuple], **changes: object) -> Callable[[], tuple]:
    def build() -> tuple:
        profile, authorizations, signature_verifiers, oracle_policy = original()
        values = {
            field.name: getattr(profile, field.name)
            for field in dataclass_fields(profile)
            if field.name != "profile_id"
        }
        values.update(changes)
        return EconomicProfileSnapshotV1.build(**values), authorizations, signature_verifiers, oracle_policy

    return build


def test_perps_margin_coordinator_positive_control_under_measured_ports(
    simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch
):
    """The perps family runs under the same measured factory; synthetic RISC0 replies only."""
    from tests.core import test_perps_margin_release_receipt_binding_v1 as perps
    from tests.core import test_receipt_backed_perps_margin_lane_composition_v1 as composition

    owner = simulated_measured_publisher_crypto_v1
    original = perps._profile
    # The synthetic manifest measures the selected image set, which does not depend on
    # the verifier registry root; fix the root image first, then govern the registry.
    shape = _governed_perps_profile(original, root_image_id=owner.manifest().root_image_id)()[0]
    owner.template = owner.artifacts(shape, None)
    manifest = owner.manifest()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    monkeypatch.setattr(
        perps, "_profile",
        _governed_perps_profile(
            original, root_image_id=manifest.root_image_id,
            verifier_registry_root=registry.registry_root,
        ),
    )
    fixture, _, structural, lane_journal = composition._structural_fixture()
    release = fixture.profile.lane_coordinator_registry.release_for(LaneIdV1.PERPS_MARKET)
    expected_row = (b"perps-coordinator", release.guest_image_id, canonical_global_bytes_v1(lane_journal))
    backend = _SyntheticBackend((expected_row,), [])
    scope = ports.bind_isolated_profile_receipt_ports_v1(
        profile=fixture.profile, verifier_registry=registry, evidence_manifest=manifest,
        artifacts=owner.artifacts(fixture.profile, backend.verify_succinct_receipt),
        deployment_root=fixture.occurrence.deployment_root, timeout_ms=1000,
    )
    candidate = lane_core.LaneCompositionReceiptCandidateV1(
        fixture.profile, fixture.occurrence, structural, lane_journal,
        lane_core.LaneCompositionReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"perps-coordinator"),
    )
    port = scope.coordinator_port(LaneIdV1.PERPS_MARKET)
    prepared = lane_core.prepare_perps_margin_lane_composition_receipt_v1(candidate)
    assert backend.calls == []
    execution = port.verify_prepared_coordinator_receipt_v1(prepared)
    measured = lane_core.bind_verified_lane_composition_receipt_v1(
        prepared, execution, expected_verifier_binding_root=port.verifier_binding_root
    )
    via_shell = lane_shell.verify_perps_margin_lane_composition_receipt_v1(candidate, port)
    recording = _SyntheticBackend((expected_row,), [])
    via_unit = unit.verify_perps_margin_lane_composition_receipt_v1(candidate, recording)
    assert measured.lane_id is LaneIdV1.PERPS_MARKET
    assert measured.expected_image_id == release.guest_image_id
    assert _witness(measured, _LANE_FIELDS) == _witness(via_shell, _LANE_FIELDS)
    assert _witness(measured, _LANE_FIELDS) == _witness(via_unit, _LANE_FIELDS)
    assert backend.calls == [expected_row, expected_row]
    assert recording.calls == [expected_row]
    # Other roles of the same measured profile cannot execute the perps coordinator subject.
    for wrong in (scope.root_port(), scope.route_port(fixture.occurrence.route_release_id)):
        with pytest.raises(ValueError, match="coordinator receipt subject is outside the port"):
            wrong.verify_prepared_coordinator_receipt_v1(prepared)
    # The asset preparation rejects the perps candidate before any port is consulted.
    with pytest.raises(ValueError, match="declared single-lane route"):
        lane_shell.verify_asset_lane_composition_receipt_v1(candidate, port)
    assert backend.calls == [expected_row, expected_row]
    # Root-confirmed old domain for the perps family: a zero structural binding root is
    # accepted and executed exactly once; the unchanged later consumer still refuses it.
    _zero_hash_for_domain(
        monkeypatch, perps_structural, "receipt-backed-perps-margin-lane-composition-v1"
    )
    assert structural.binding_root == ZERO_ROOT_V1
    zero_prepared = lane_core.prepare_perps_margin_lane_composition_receipt_v1(candidate)
    assert backend.calls == [expected_row, expected_row]
    zero_witness = lane_core.bind_verified_lane_composition_receipt_v1(
        zero_prepared, port.verify_prepared_coordinator_receipt_v1(zero_prepared),
        expected_verifier_binding_root=port.verifier_binding_root,
    )
    assert zero_witness.structural_composition_root == ZERO_ROOT_V1
    assert backend.calls == [expected_row] * 3
    with pytest.raises(ValueError, match="nonzero canonical root"):
        route_core._snapshot_verified_lane_v1(zero_witness)


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_plain_callback_and_success_values_cannot_supply_execution_authority(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    for fake in (None, True, object(), boundary.subject):
        with pytest.raises(TypeError, match="measured isolated receipt port"):
            family.shell_verify(stage.candidate, cast(ports.IsolatedReceiptPortV1, fake))
        with pytest.raises(TypeError, match="execution must be the exact typed value"):
            _bind_execution(family, stage, stage.prepared, fake)
    for cls, arguments in (
        (family.prepared_type, (object(), object())),
        (family.execution_type, (object(), stage.prepared, _ROOT)),
    ):
        with pytest.raises(TypeError, match="constructed"):
            cls(*arguments)
    # A module-role handle is a factory port but never coordinator or route authority.
    with pytest.raises(ValueError, match="subject is outside the port"):
        family.shell_verify(stage.candidate, boundary.scope.module_port(LaneIdV1.ASSET_TRANSFER))
    assert boundary.subject.calls == []
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("role", ("root", "module", "route"))
def test_wrong_factory_role_cannot_verify_a_coordinator_subject(boundary, role):
    with pytest.raises(ValueError, match="coordinator receipt subject is outside the port"):
        _select_port(boundary, role).verify_prepared_coordinator_receipt_v1(
            boundary.stages["coordinator"].prepared
        )
    assert boundary.subject.calls == []


@pytest.mark.parametrize("role", ("root", "module", "coordinator"))
def test_wrong_factory_role_cannot_verify_a_route_subject(boundary, role):
    with pytest.raises(ValueError, match="route receipt subject is outside the port"):
        _select_port(boundary, role).verify_prepared_route_receipt_v1(
            boundary.stages["route"].prepared
        )
    assert boundary.subject.calls == []


@pytest.mark.parametrize(
    ("family_name", "field"),
    [("coordinator", field) for field in ("profile_id", "lane_id", "coordinator_release_id")]
    + [("route", field) for field in ("profile_id", "route_release_id")],
)
def test_port_rejects_each_foreign_context_before_execution(boundary, family_name, field):
    family, stage = _stage(boundary, family_name)
    current = getattr(getattr(stage.prepared._fields, family.fields_attr), field)
    changed = _changed_prepared(family, stage.prepared, **{field: _foreign_value(field, current)})
    with pytest.raises(ValueError, match="subject is outside the port"):
        _execute(stage.port, family, changed)
    assert boundary.subject.calls == []


@pytest.mark.parametrize(
    ("family_name", "field"),
    [
        (name, field)
        for name in _FAMILY_NAMES
        for field in (*_FAMILIES[name].witness_fields, *_BYTE_FIELDS)
        if field != "receipt_kind"
    ],
)
def test_execution_evidence_binds_every_final_field_and_byte_field(boundary, family_name, field):
    family, stage = _stage(boundary, family_name)
    execution = _execute(stage.port, family, stage.prepared)
    if field in _BYTE_FIELDS:
        current: object = getattr(stage.prepared, field)
    else:
        current = getattr(getattr(stage.prepared._fields, family.fields_attr), field)
    changed = _changed_prepared(family, stage.prepared, **{field: _foreign_value(field, current)})
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(family, stage, changed, execution)
    assert boundary.subject.calls == [stage.expected_row]


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
@pytest.mark.parametrize("field", _BYTE_FIELDS)
def test_execution_evidence_binds_complete_bytes_with_consistent_digests(boundary, family_name, field):
    family, stage = _stage(boundary, family_name)
    execution = _execute(stage.port, family, stage.prepared)
    raw = getattr(stage.prepared, field) + b" changed"
    digest_field = "receipt_digest" if field == "receipt_bytes" else family.journal_digest_field
    changed = _changed_prepared(
        family, stage.prepared,
        **{field: raw, digest_field: "0x" + hashlib.sha256(raw).hexdigest()},
    )
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(family, stage, changed, execution)
    assert boundary.subject.calls == [stage.expected_row]


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
@pytest.mark.parametrize("field", _BYTE_FIELDS)
def test_bind_recomputes_digests_over_the_executed_bytes(boundary, family_name, field):
    """Executed bytes whose retained digest is stale reject at bind, not only at subject equality."""
    family, stage = _stage(boundary, family_name)
    raw = getattr(stage.prepared, field) + b" changed"
    forged = _changed_prepared(family, stage.prepared, **{field: raw})
    forged_row = (forged.receipt_bytes, forged.expected_image_id, forged.expected_journal_bytes)
    boundary.subject.expected = (*boundary.subject.expected, forged_row)
    execution = _execute(stage.port, family, forged)
    label = "receipt digest" if field == "receipt_bytes" else "journal digest"
    with pytest.raises(ValueError, match=f"{label} mismatch"):
        _bind_execution(family, stage, forged, execution)
    assert boundary.subject.calls == [forged_row]


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_backend_refusal_propagates_without_execution_evidence(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    forged = _changed_prepared(family, stage.prepared, receipt_bytes=b"foreign")
    with pytest.raises(ValueError, match="synthetic receipt statement rejected"):
        _execute(stage.port, family, forged)
    assert boundary.subject.calls == [
        (b"foreign", stage.prepared.expected_image_id, stage.prepared.expected_journal_bytes)
    ]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_zero_subject_digests_keep_entry_point_acceptance_and_downstream_rejection(
    boundary, family_name, monkeypatch: pytest.MonkeyPatch
):
    """Bounded digest-function substitution: only the subject's own digest calls return zero.

    This is a synthetic hash-domain control, not a preimage claim. The old entry point
    minted a witness carrying zero digests once the verifier accepted the statement; the
    prepared, measured and bound path keeps that domain, while the unchanged downstream
    consumers still refuse zero digests. Child lane digests are never substituted.
    """
    family, stage = _stage(boundary, family_name)
    subject_bytes = (stage.prepared.receipt_bytes, stage.prepared.expected_journal_bytes)
    real_digest = family.core._sha256_root_v1

    def zero_for_subject(value: bytes) -> str:
        return ZERO_ROOT_V1 if value in subject_bytes else real_digest(value)

    monkeypatch.setattr(family.core, "_sha256_root_v1", zero_for_subject)
    prepared = family.prepare(stage.candidate)
    fields = getattr(prepared._fields, family.fields_attr)
    assert (fields.receipt_digest, getattr(fields, family.journal_digest_field)) == (
        ZERO_ROOT_V1, ZERO_ROOT_V1
    )
    assert boundary.subject.calls == []
    execution = _execute(stage.port, family, prepared)
    witness = _bind_execution(family, stage, prepared, execution)
    assert (witness.receipt_digest, getattr(witness, family.journal_digest_field)) == (
        ZERO_ROOT_V1, ZERO_ROOT_V1
    )
    assert boundary.subject.calls == [stage.expected_row]
    # Existing downstream constraints are unchanged: they refuse the zero digests later.
    with pytest.raises(ValueError, match="nonzero canonical root"):
        if family_name == "coordinator":
            route_core._snapshot_verified_lane_v1(witness)
        else:
            _ = witness.assumption_root
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_zero_structural_composition_root_keeps_asset_entry_point_acceptance(
    boundary, monkeypatch: pytest.MonkeyPatch
):
    """Root-confirmed old domain: a zero structural binding root is accepted and executed once.

    No pre-existing admission check constrains the structural binding_root; only the later
    route consumer requires it nonzero, and that rule is unchanged.
    """
    family, stage = _stage(boundary, "coordinator")
    _zero_hash_for_domain(monkeypatch, asset_structural, "receipt-backed-asset-lane-composition-v1")
    assert stage.candidate.structural_composition.binding_root == ZERO_ROOT_V1
    prepared = family.prepare(stage.candidate)
    assert boundary.subject.calls == []
    execution = _execute(stage.port, family, prepared)
    witness = _bind_execution(family, stage, prepared, execution)
    assert witness.structural_composition_root == ZERO_ROOT_V1
    assert witness.lane_journal_root == stage.candidate.lane_journal.journal_root
    assert boundary.subject.calls == [stage.expected_row]
    with pytest.raises(ValueError, match="nonzero canonical root"):
        route_core._snapshot_verified_lane_v1(witness)
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_zero_route_journal_root_keeps_entry_point_acceptance(
    boundary, monkeypatch: pytest.MonkeyPatch
):
    """Root-confirmed old domain: a zero route journal root is accepted and executed once.

    Lane journal roots stay real, so the route journal's validated lane roots and the
    consumed lane witnesses still bind; only the later assumption root refuses the zero.
    """
    family, stage = _stage(boundary, "route")
    _zero_hash_for_domain(monkeypatch, proof, "route-composition-journal-v1")
    assert stage.candidate.route_journal.journal_root == ZERO_ROOT_V1
    lane_root = stage.candidate.lane_journals[0].journal_root
    assert lane_root != ZERO_ROOT_V1
    prepared = family.prepare(stage.candidate)
    assert boundary.subject.calls == []
    execution = _execute(stage.port, family, prepared)
    witness = _bind_execution(family, stage, prepared, execution)
    assert witness.route_journal_root == ZERO_ROOT_V1
    assert witness.ordered_lane_journal_roots == (lane_root,)
    assert boundary.subject.calls == [stage.expected_row]
    with pytest.raises(ValueError, match="nonzero canonical root"):
        _ = witness.assumption_root
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_zero_lane_binding_roots_keep_route_entry_point_acceptance(
    boundary, monkeypatch: pytest.MonkeyPatch
):
    """Root-confirmed old domain: zero consumed lane binding roots are accepted and executed once.

    No admission check or later consumer constrains the lane binding roots; the assumption
    root does not include them and derives exactly as before.
    """
    family, stage = _stage(boundary, "route")
    _zero_hash_for_domain(monkeypatch, route_core, "verified-lane-composition-v1")
    prepared = family.prepare(stage.candidate)
    assert boundary.subject.calls == []
    execution = _execute(stage.port, family, prepared)
    witness = _bind_execution(family, stage, prepared, execution)
    assert witness.ordered_lane_binding_roots == (ZERO_ROOT_V1,)
    assert witness.route_journal_root == stage.candidate.route_journal.journal_root
    assert witness.assumption_root == stage.expected[-1]
    assert witness.binding_root != stage.expected[-2]
    assert boundary.subject.calls == [stage.expected_row]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_canonical_journal_ceiling_rejects_before_any_port_io(
    boundary, family_name, monkeypatch: pytest.MonkeyPatch
):
    """Bounded encoder substitution: only the subject journal's canonical bytes grow.

    The retained release ceiling is reached without rebuilding a governed profile;
    child lane journal bytes are never substituted. Preparation rejects before any
    verifier port is consulted.
    """
    family, stage = _stage(boundary, family_name)
    profile = boundary.subject.candidate.profile
    if family_name == "coordinator":
        subject_journal = stage.candidate.lane_journal
        ceiling = profile.lane_coordinator_registry.release_for(LaneIdV1.ASSET_TRANSFER).max_journal_bytes
    else:
        subject_journal = stage.candidate.route_journal
        ceiling = profile.route_registry.route_for_command(
            stage.candidate.occurrence.command_kind
        ).max_journal_bytes
    real_encoder = family.core.canonical_global_bytes_v1

    def grown_for_subject(value: object) -> bytes:
        encoded = real_encoder(value)
        if value == subject_journal:
            return encoded + b"\0" * (ceiling + 1 - len(encoded))
        return encoded

    monkeypatch.setattr(family.core, "canonical_global_bytes_v1", grown_for_subject)
    with pytest.raises(ValueError, match="exceeds its release byte ceiling"):
        family.prepare(stage.candidate)
    with pytest.raises(ValueError, match="exceeds its release byte ceiling"):
        family.shell_verify(stage.candidate, stage.port)
    assert boundary.subject.calls == []
    # One byte under the ceiling is still prepared and executed exactly.
    monkeypatch.setattr(
        family.core, "canonical_global_bytes_v1",
        lambda value: grown_for_subject(value)[:-1] if value == subject_journal else real_encoder(value),
    )
    prepared = family.prepare(stage.candidate)
    assert len(prepared.expected_journal_bytes) == ceiling
    assert boundary.subject.calls == []


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_wrong_verifier_binding_cannot_consume_matching_execution(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    execution = _execute(stage.port, family, stage.prepared)
    with pytest.raises(ValueError, match="verifier binding mismatch"):
        family.bind(stage.prepared, execution, expected_verifier_binding_root=_ROOT)


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_prepared_alias_mutation_during_io_cannot_relabel_execution(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    prepared = stage.prepared
    original = family.snapshot(prepared)
    changed = _changed_prepared(family, prepared, command_occurrence_id=_ROOT)

    def mutate_caller_alias():
        object.__setattr__(prepared, "_fields", changed._fields)

    boundary.subject.on_call = mutate_caller_alias
    execution = _execute(stage.port, family, prepared)
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(family, stage, prepared, execution)
    assert _witness(_bind_execution(family, stage, original, execution), family.witness_fields) == (
        stage.expected
    )
    assert boundary.subject.calls == [stage.expected_row]


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_snapshot_omission_mutant_is_revealed_by_the_alias_subject_observation(
    boundary, family_name, monkeypatch: pytest.MonkeyPatch
):
    """Execute one in-memory Tier 1 mutant; retain the ordinary law as its oracle."""
    family, stage = _stage(boundary, family_name)
    source = textwrap.dedent(inspect.getsource(getattr(ports.IsolatedReceiptPortV1, family.port_method)))
    needle = f"owned = {family.snapshot.__name__}(prepared)"
    assert source.count(needle) == 1
    mutated = source.replace(needle, "owned = prepared", 1)
    namespace = dict(vars(ports))
    exec(compile(mutated, f"<{family.name}-snapshot-omission-mutant>", "exec"), namespace)
    monkeypatch.setattr(ports.IsolatedReceiptPortV1, family.port_method, namespace[family.port_method])
    # The mutant's globals are a detached copy: confirm its bad subject actually reaches the
    # issued evidence before crediting the kill below.
    alias = family.snapshot(stage.prepared)
    changed = _changed_prepared(family, alias, command_occurrence_id=_ROOT)
    boundary.subject.on_call = lambda: object.__setattr__(alias, "_fields", changed._fields)
    execution = _execute(stage.port, family, alias)
    assert execution._fields.prepared_fields == changed._fields
    assert execution._fields.prepared_fields != stage.prepared._fields
    boundary.subject.calls.clear()
    with pytest.raises(pytest.fail.Exception, match="DID NOT RAISE"):
        test_prepared_alias_mutation_during_io_cannot_relabel_execution(boundary, family_name)


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
@pytest.mark.parametrize("field", ("role", "release_id", "lane_id", "call"))
def test_changed_port_authority_during_io_cannot_issue_execution_evidence(boundary, family_name, field):
    family, stage = _stage(boundary, family_name)

    def change_authority():
        authority = ports._CALLS[stage.port]
        changes = {
            "role": replace(authority, role=ports._ReceiptRoleV1.ROOT),
            "release_id": replace(authority, release_id=_ROOT),
            "lane_id": replace(authority, lane_id=LaneIdV1.SPOT_LIQUIDITY),
            "call": replace(authority, call=lambda *args, **kwargs: authority.call(*args, **kwargs)),
        }
        ports._CALLS[stage.port] = changes[field]

    boundary.subject.on_call = change_authority
    with pytest.raises(ValueError, match=f"{family.name} receipt authority changed during verification"):
        _execute(stage.port, family, stage.prepared)
    assert boundary.subject.calls == [stage.expected_row]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_port_requires_exact_backend_success_contract(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    authority = ports._CALLS[stage.port]

    def wrong_success(*args, **kwargs):
        authority.call(*args, **kwargs)
        return True

    ports._CALLS[stage.port] = replace(authority, call=wrong_success)
    with pytest.raises(ValueError, match=f"{family.name} receipt backend violated success contract"):
        _execute(stage.port, family, stage.prepared)
    assert boundary.subject.calls == [stage.expected_row]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("family_name", _FAMILY_NAMES)
def test_verifier_failure_propagates_without_execution_evidence_or_state_change(boundary, family_name):
    family, stage = _stage(boundary, family_name)
    boundary.subject.fail_at = family.name
    with pytest.raises(RuntimeError, match=f"synthetic {family.name} verifier unavailable"):
        _execute(stage.port, family, stage.prepared)
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes
    assert boundary.subject.calls == [stage.expected_row]


def test_prepared_guards_pin_kind_bytes_epoch_roots_and_route_lane_pairing(boundary):
    lane, lane_stage = _stage(boundary, "coordinator")
    route, route_stage = _stage(boundary, "route")
    lanes = tuple(LaneIdV1)
    rejected = (
        (lane, lane_stage, {"receipt_kind": ReceiptKindV1.COMPOSITE}, ValueError, "must be succinct"),
        (route, route_stage, {"receipt_kind": ReceiptKindV1.COMPOSITE}, ValueError, "must be succinct"),
        (lane, lane_stage, {"receipt_bytes": b""}, TypeError, "non-empty exact bytes"),
        (route, route_stage, {"expected_journal_bytes": bytearray(b"x")}, TypeError, "non-empty exact bytes"),
        (lane, lane_stage, {"writer_epoch": 1 << 64}, ValueError, "writer epoch"),
        (route, route_stage, {"writer_epoch": True}, ValueError, "writer epoch"),
        # Roots fixed nonzero by actual upstream validators (profile, releases, journals,
        # consumed lane witnesses) stay nonzero at the prepared guard.
        (lane, lane_stage, {"profile_id": ZERO_ROOT_V1}, ValueError, "must be nonzero"),
        (lane, lane_stage, {"command_occurrence_id": ZERO_ROOT_V1}, ValueError, "must be nonzero"),
        (lane, lane_stage, {"expected_image_id": ZERO_ROOT_V1}, ValueError, "must be nonzero"),
        (route, route_stage, {"command_occurrence_id": ZERO_ROOT_V1}, ValueError, "nonzero canonical root"),
        (route, route_stage, {"ordered_lane_journal_roots": (ZERO_ROOT_V1,)}, ValueError, "nonzero canonical root"),
        (lane, lane_stage, {"lane_id": "ASSET_TRANSFER"}, TypeError, "lane id is not closed"),
        (route, route_stage, {"ordered_lane_binding_roots": (_ROOT, _ROOT)}, ValueError, "pair every lane"),
        (route, route_stage, {"ordered_lane_journal_roots": (_ROOT, _ROOT)}, ValueError, "pair every lane"),
        (route, route_stage, {"ordered_lane_binding_roots": ()}, ValueError, "pair every lane"),
        (
            route, route_stage,
            {"ordered_lane_ids": (), "ordered_lane_binding_roots": (), "ordered_lane_journal_roots": ()},
            ValueError, "outside the route scope",
        ),
        (
            route, route_stage,
            {
                "ordered_lane_ids": lanes[:9], "ordered_lane_binding_roots": (_ROOT,) * 9,
                "ordered_lane_journal_roots": (_ROOT,) * 9,
            },
            ValueError, "outside the route scope",
        ),
        (
            route, route_stage,
            {
                "ordered_lane_ids": lanes[:1] * 2, "ordered_lane_binding_roots": (_ROOT,) * 2,
                "ordered_lane_journal_roots": (_ROOT,) * 2,
            },
            ValueError, "must be unique",
        ),
        (
            route, route_stage,
            {"ordered_lane_ids": list(lanes[:1])}, TypeError, "must be exact tuple",
        ),
    )
    for family, stage, changes, error, message in rejected:
        with pytest.raises(error, match=message):
            _changed_prepared(family, stage.prepared, **changes)
    # Computed roots with no pre-existing admission check keep the old entry-point domain
    # that permits zero; only the unchanged later consumers require them nonzero.
    for family, stage, zero_field in (
        (lane, lane_stage, "lane_journal_digest"), (lane, lane_stage, "receipt_digest"),
        (lane, lane_stage, "structural_composition_root"), (lane, lane_stage, "lane_journal_root"),
        (route, route_stage, "route_journal_digest"), (route, route_stage, "receipt_digest"),
        (route, route_stage, "route_journal_root"),
    ):
        zero_root = _changed_prepared(family, stage.prepared, **{zero_field: ZERO_ROOT_V1})
        assert type(zero_root) is family.prepared_type
    zero_lane_binding = _changed_prepared(
        route, route_stage.prepared, ordered_lane_binding_roots=(ZERO_ROOT_V1,)
    )
    assert type(zero_lane_binding) is route.prepared_type
    # The exact route scope maximum of eight distinct lanes is representable.
    widest = _changed_prepared(
        route, route_stage.prepared,
        ordered_lane_ids=lanes[:8], ordered_lane_binding_roots=(_ROOT,) * 8,
        ordered_lane_journal_roots=(_ROOT,) * 8,
    )
    assert type(widest) is route.prepared_type
    assert boundary.subject.calls == []
