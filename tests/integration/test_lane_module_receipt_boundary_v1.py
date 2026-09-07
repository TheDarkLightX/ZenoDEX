"""Exact module execution evidence over explicitly simulated RISC0 replies.

These cases use the real measured-port factory and transport with the existing
synthetic process fixture. They establish phase/subject binding and logical
no-write behavior, not a genuine receipt, release or production qualification.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
import textwrap
from dataclasses import dataclass, replace
from pathlib import Path
from typing import cast

import pytest

from src.core import lane_module_receipt_verification_v1 as core
from src.core.global_settlement_types_v1 import LaneIdV1, canonical_global_bytes_v1
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from src.integration import isolated_profile_receipt_ports_v1 as ports
from src.integration import lane_module_receipt_verification_v1 as shell
from tests.integration import asset_receipt_pipeline_fixtures_v1 as fixtures
from tests.integration import publisher_receipt_port_fixtures_v1 as process
from tests.integration.test_isolated_asset_receipt_pipeline_v1 import _bind, _verify

simulated_measured_publisher_crypto_v1 = process.simulated_measured_publisher_crypto_v1
_ROOT = "0x" + "ab" * 32
_FIELDS = (
    "authenticated_command_binding_root", "release_route_binding_root",
    "expected_image_id", "module_journal_root", "module_journal_digest",
    "statement_root", "command_occurrence_id", "receipt_digest", "receipt_kind",
)
_PREPARES = (
    "prepare_asset_transfer_lane_module_receipt_v1",
    "prepare_asset_transfer_lane_module_custody_receipt_v1",
    "prepare_managed_asset_lifecycle_lane_module_receipt_v1",
    "prepare_perps_margin_lane_module_receipt_v1",
)


@dataclass(frozen=True)
class _Boundary:
    subject: fixtures._Fixture
    candidate: core.AssetTransferLaneModuleReceiptCandidateV1
    prepared: core.PreparedLaneModuleReceiptV1
    port: ports.IsolatedReceiptPortV1
    scope: ports.IsolatedProfileReceiptPortsV1
    expected: tuple[object, ...]
    pre_bytes: bytes


def _witness(witness: core.VerifiedLaneModuleTransitionV1) -> tuple[object, ...]:
    return tuple(getattr(witness, name) for name in _FIELDS) + (witness.binding_root,)


@pytest.fixture
def boundary(simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch) -> _Boundary:
    subject = fixtures._fixture(simulated_measured_publisher_crypto_v1)
    captured: list[tuple[core.AssetTransferLaneModuleReceiptCandidateV1, ports.IsolatedReceiptPortV1]] = []

    def capture(candidate, receipt_verifier):
        captured.append((candidate, receipt_verifier))
        return shell.verify_asset_transfer_lane_module_receipt_v1(candidate, receipt_verifier)

    # Acquire the actual authenticated candidate through the existing pipeline.
    with monkeypatch.context() as patch:
        patch.setattr(pipeline, "verify_asset_transfer_lane_module_receipt_v1", capture)
        result = _verify(_bind(subject), subject)
    assert len(captured) == 1
    candidate, port = captured[0]
    scope = process.bind_publisher_test_receipt_ports_v1(subject.candidate, subject)
    subject.calls.clear()
    return _Boundary(
        subject, candidate, core.prepare_asset_transfer_lane_module_receipt_v1(candidate),
        port, scope, _witness(result.module_evidence[0][1]),
        canonical_global_bytes_v1(subject.candidate.pre_state),
    )


def _bind_execution(boundary: _Boundary, prepared, execution):
    return core.bind_verified_lane_module_receipt_v1(
        prepared, execution, expected_verifier_binding_root=boundary.port.verifier_binding_root
    )


def _core_effect_calls(source: str) -> tuple[str, ...]:
    forbidden = {"verify_succinct_receipt", "verify_prepared_module_receipt_v1"}
    return tuple(
        node.func.attr
        for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in forbidden
    )


def test_core_preparation_and_binding_have_no_receipt_callback_or_shell_import():
    source = Path(core.__file__).read_text()
    assert _core_effect_calls(source) == ()
    for name in _PREPARES:
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


def test_preparation_is_owned_and_only_measured_execution_mints_bound_result(boundary):
    prepared = core.prepare_asset_transfer_lane_module_receipt_v1(boundary.candidate)
    assert boundary.subject.calls == []
    assert (
        prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes
    ) == boundary.subject.expected[0]
    execution = boundary.port.verify_prepared_module_receipt_v1(prepared)
    result = _bind_execution(boundary, prepared, execution)
    assert _witness(result) == boundary.expected
    # Exact re-binding is deterministic and executes no additional verifier call.
    assert _witness(_bind_execution(boundary, prepared, execution)) == boundary.expected
    assert boundary.subject.calls == [boundary.subject.expected[0]]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_plain_callback_and_success_values_cannot_supply_execution_authority(boundary):
    for fake in (None, True, object(), boundary.subject):
        with pytest.raises(TypeError, match="measured isolated receipt port"):
            shell.verify_asset_transfer_lane_module_receipt_v1(
                boundary.candidate, cast(ports.IsolatedReceiptPortV1, fake)
            )
        with pytest.raises(TypeError, match="execution must be the exact typed value"):
            _bind_execution(boundary, boundary.prepared, fake)
    for cls, arguments in (
        (core.PreparedLaneModuleReceiptV1, (object(), object())),
        (core.VerifiedLaneModuleReceiptExecutionV1, (object(), boundary.prepared, _ROOT)),
    ):
        with pytest.raises(TypeError, match="constructed"):
            cls(*arguments)
    assert boundary.subject.calls == []
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


@pytest.mark.parametrize("role", ("root", "coordinator", "route"))
def test_wrong_factory_role_cannot_verify_a_module_subject(boundary, role):
    selected = {
        "root": boundary.scope.root_port,
        "coordinator": lambda: boundary.scope.coordinator_port(LaneIdV1.ASSET_TRANSFER),
        "route": lambda: boundary.scope.route_port(
            boundary.candidate.profile.route_registry.routes[0].route_release_id
        ),
    }[role]()
    with pytest.raises(ValueError, match="subject is outside the port"):
        selected.verify_prepared_module_receipt_v1(boundary.prepared)
    assert boundary.subject.calls == []


def _changed_prepared(prepared, group: str, field: str):
    """Construct one explicit malformed subject for the independent field matrix.

    This test-only token use supplies no real preparation authority. Every row
    must be rejected by the production evidence consumer or measured role port.
    """
    original = prepared._fields
    if group == "request":
        value = LaneIdV1.SPOT_LIQUIDITY if field == "lane_id" else _ROOT
        request = replace(original.request, **{field: value})
        changed = replace(original, request=request)
    else:
        changed = replace(
            original, transition_fields=replace(original.transition_fields, **{field: _ROOT})
        )
        if field == "expected_image_id":
            changed = replace(changed, request=replace(changed.request, expected_image_id=_ROOT))
    return core.PreparedLaneModuleReceiptV1(core._PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1, changed)


@pytest.mark.parametrize("field", ("profile_root", "lane_id", "module_release_id"))
def test_port_rejects_each_foreign_context_before_execution(boundary, field):
    changed = _changed_prepared(boundary.prepared, "request", field)
    with pytest.raises(ValueError, match="subject is outside the port"):
        boundary.port.verify_prepared_module_receipt_v1(changed)
    assert boundary.subject.calls == []


@pytest.mark.parametrize(
    ("group", "field"),
    [("request", field) for field in ("profile_root", "lane_id", "module_release_id")]
    + [("transition", field) for field in _FIELDS if field != "receipt_kind"],
)
def test_execution_evidence_binds_every_context_and_final_field(boundary, group, field):
    execution = boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    changed = _changed_prepared(boundary.prepared, group, field)
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(boundary, changed, execution)
    assert boundary.subject.calls == [boundary.subject.expected[0]]


@pytest.mark.parametrize("field", ("receipt_bytes", "expected_journal_bytes"))
def test_execution_evidence_binds_complete_bytes_with_consistent_digests(boundary, field):
    execution = boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    original = boundary.prepared._fields
    raw = getattr(original.request, field) + b" changed"
    digest_field = "receipt_digest" if field == "receipt_bytes" else "module_journal_digest"
    changed = core.PreparedLaneModuleReceiptV1(
        core._PREPARED_LANE_MODULE_RECEIPT_TOKEN_V1,
        replace(
            original, request=replace(original.request, **{field: raw}),
            transition_fields=replace(
                original.transition_fields, **{digest_field: "0x" + hashlib.sha256(raw).hexdigest()}
            ),
        ),
    )
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(boundary, changed, execution)
    assert boundary.subject.calls == [boundary.subject.expected[0]]


def test_wrong_verifier_binding_cannot_consume_matching_execution(boundary):
    execution = boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    with pytest.raises(ValueError, match="verifier binding mismatch"):
        core.bind_verified_lane_module_receipt_v1(
            boundary.prepared, execution, expected_verifier_binding_root=_ROOT
        )


def test_prepared_alias_mutation_during_io_cannot_relabel_execution(boundary):
    prepared = boundary.prepared
    original = core.snapshot_prepared_lane_module_receipt_v1(prepared)
    changed = _changed_prepared(prepared, "transition", "authenticated_command_binding_root")

    def mutate_caller_alias():
        object.__setattr__(prepared, "_fields", changed._fields)

    boundary.subject.on_call = mutate_caller_alias
    execution = boundary.port.verify_prepared_module_receipt_v1(prepared)
    with pytest.raises(ValueError, match="execution subject mismatch"):
        _bind_execution(boundary, prepared, execution)
    assert _witness(_bind_execution(boundary, original, execution)) == boundary.expected
    assert boundary.subject.calls == [boundary.subject.expected[0]]


def test_snapshot_omission_mutant_is_revealed_by_the_alias_subject_observation(
    boundary, monkeypatch: pytest.MonkeyPatch
):
    """Execute one in-memory Tier 1 mutant; retain the ordinary law as its oracle."""
    source = textwrap.dedent(
        inspect.getsource(ports.IsolatedReceiptPortV1.verify_prepared_module_receipt_v1)
    )
    needle = "owned = snapshot_prepared_lane_module_receipt_v1(prepared)"
    assert source.count(needle) == 1
    mutated = source.replace(needle, "owned = prepared", 1)
    namespace = dict(vars(ports))
    exec(compile(mutated, "<module-snapshot-omission-mutant>", "exec"), namespace)
    monkeypatch.setattr(
        ports.IsolatedReceiptPortV1, "verify_prepared_module_receipt_v1",
        namespace["verify_prepared_module_receipt_v1"],
    )
    with pytest.raises(pytest.fail.Exception, match="DID NOT RAISE"):
        test_prepared_alias_mutation_during_io_cannot_relabel_execution(boundary)


@pytest.mark.parametrize("field", ("role", "release_id", "lane_id", "call"))
def test_changed_port_authority_during_io_cannot_issue_execution_evidence(boundary, field):
    def change_authority():
        authority = ports._CALLS[boundary.port]
        changes = {
            "role": replace(authority, role=ports._ReceiptRoleV1.ROOT),
            "release_id": replace(authority, release_id=_ROOT),
            "lane_id": replace(authority, lane_id=LaneIdV1.SPOT_LIQUIDITY),
            "call": replace(authority, call=lambda *args, **kwargs: authority.call(*args, **kwargs)),
        }
        ports._CALLS[boundary.port] = changes[field]

    boundary.subject.on_call = change_authority
    with pytest.raises(ValueError, match="authority changed during verification"):
        boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    assert boundary.subject.calls == [boundary.subject.expected[0]]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_module_port_requires_exact_backend_success_contract(boundary):
    authority = ports._CALLS[boundary.port]

    def wrong_success(*args, **kwargs):
        authority.call(*args, **kwargs)
        return True

    ports._CALLS[boundary.port] = replace(authority, call=wrong_success)
    with pytest.raises(ValueError, match="backend violated success contract"):
        boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    assert boundary.subject.calls == [boundary.subject.expected[0]]
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes


def test_verifier_failure_propagates_without_execution_evidence_or_state_change(boundary):
    boundary.subject.fail_at = "module"
    with pytest.raises(RuntimeError, match="synthetic module verifier unavailable"):
        boundary.port.verify_prepared_module_receipt_v1(boundary.prepared)
    assert canonical_global_bytes_v1(boundary.subject.candidate.pre_state) == boundary.pre_bytes
    assert boundary.subject.calls == [boundary.subject.expected[0]]
