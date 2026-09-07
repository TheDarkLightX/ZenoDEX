"""Boundary evidence for the tokenomics burn-lane and fee-lane receipt extraction.

Core prepares one exact detached subject (final marker fields plus the exact
request bytes) and calls no verifier; the integration shell executes exactly
that subject on the caller-supplied reference verifier and mints the existing
non-authoritative marker from the executed subject only.  Every verifier here
is a deterministic recorder, never cryptographic evidence, and nothing below
grants publication or production authority.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

import src.core.zdex_tokenomics_fee_lane_receipt_verification_v1 as fee_core
import src.core.zdex_tokenomics_lane_receipt_common_v1 as common
import src.core.zdex_tokenomics_lane_receipt_verification_v1 as burn_core
import src.integration.zdex_tokenomics_lane_receipt_verification_v1 as shell
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    ReleaseStatusV1,
    canonical_global_bytes_v1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import ZDEXLaneReceiptEnvelopeV1
from src.core.zdex_tokenomics_fee_lane_coordinator_v1 import (
    compose_zdex_tokenomics_fee_allocation_lane_v1,
)
from src.core.zdex_tokenomics_lane_coordinator_v1 import compose_zdex_tokenomics_burn_lane_v1
from src.core.zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneCompositionAcceptedV1
from tests.core.test_zdex_purchase_burn_route_v1 import _fee_lane_receipt_fixture
from tests.core.test_zdex_tokenomics_lane_coordinator_v1 import _receipt_fixture, _root

REPO_ROOT = Path(__file__).resolve().parents[2]

_CORE_MODULES = (
    "src/core/zdex_tokenomics_lane_receipt_common_v1.py",
    "src/core/zdex_tokenomics_lane_receipt_verification_v1.py",
    "src/core/zdex_tokenomics_fee_lane_receipt_verification_v1.py",
)
_SHELL_MODULE = "src/integration/zdex_tokenomics_lane_receipt_verification_v1.py"
_EFFECT_IMPORT_ROOTS = frozenset(
    {"threading", "weakref", "os", "sys", "time", "datetime", "random", "pathlib", "importlib"}
)
_REMOVED_CORE_NAMES = (
    "verify_zdex_tokenomics_lane_receipt_v1",
    "verify_zdex_tokenomics_fee_lane_receipt_v1",
    "_verify_and_build_zdex_tokenomics_lane_v1",
)
# Marker binding roots captured on the pre-extraction tree (base 8b4554dd0) by the
# retained core tests.  The extraction must reproduce them exactly.
_BURN_BINDING_ROOT_PIN = "0x3d9398fda81e68baa95f537e08197e6474bbe9d5ecef562853d25888e1dbdd5f"
_FEE_BINDING_ROOT_PIN = "0x5a0edace975c58c0954cdaa2f73d72594b6d8e256e6ccc796daa75ba38cf6654"
_MARKER_FIELD_NAMES = (
    "profile_root",
    "route_release_id",
    "module_release_id",
    "coordinator_release_id",
    "command_occurrence_id",
    "writer_epoch",
    "module_journal_root",
    "lane_journal_root",
    "lane_journal_digest",
    "pre_lane_root",
    "post_lane_root",
    "effect_plan_root",
    "module_image_id",
    "expected_image_id",
    "receipt_digest",
    "receipt_kind",
)


def _digest(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


class _RecordingVerifier:
    """Reference recorder: returns a caller-chosen value, optionally raises."""

    def __init__(self, *, result: object = None, reject: bool = False) -> None:
        self.result = result
        self.reject = reject
        self.calls: list[tuple[bytes, str, bytes]] = []

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object:
        self.calls.append((receipt_bytes, expected_image_id, expected_journal_bytes))
        if self.reject:
            raise ValueError("boundary verifier rejection")
        return self.result


@dataclass(frozen=True)
class _Lane:
    name: str
    candidate: object
    governed: object
    profile: object
    route_release: object
    module_release: object
    coordinator_release: object
    prepare: Callable[[object, object], common.PreparedZDEXTokenomicsLaneReceiptV1]
    verify: Callable[[object, object, object], common.VerifiedZDEXTokenomicsLaneV1]
    recompute: Callable[[object], object]
    binding_root_pin: str
    context_mismatch: str


def _lane(name: str) -> _Lane:
    if name == "burn":
        candidate, governed, _ = _receipt_fixture()
        fields = governed._fields
        return _Lane(
            name,
            candidate,
            governed,
            fields.profile,
            fields.route_release,
            fields.module_release,
            fields.coordinator_release,
            burn_core.prepare_zdex_tokenomics_lane_receipt_v1,
            shell.verify_zdex_tokenomics_lane_receipt_v1,
            compose_zdex_tokenomics_burn_lane_v1,
            _BURN_BINDING_ROOT_PIN,
            "candidate binding mismatch",
        )
    candidate, governed = _fee_lane_receipt_fixture()
    fields = governed._fields
    return _Lane(
        name,
        candidate,
        governed,
        fields.profile,
        fields.allocation_route,
        fields.module_release,
        fields.coordinator_release,
        fee_core.prepare_zdex_tokenomics_fee_lane_receipt_v1,
        shell.verify_zdex_tokenomics_fee_lane_receipt_v1,
        compose_zdex_tokenomics_fee_allocation_lane_v1,
        _FEE_BINDING_ROOT_PIN,
        "fee-lane candidate mismatch",
    )


def _expected_fields(lane: _Lane) -> common._VerifiedZDEXTokenomicsLaneFieldsV1:
    """Independent derivation of the old marker fields from fixture facts."""

    recomputed = lane.recompute(lane.candidate.lane_candidate)
    assert type(recomputed) is ZDEXTokenomicsLaneCompositionAcceptedV1
    journal = recomputed.lane_journal
    return common._VerifiedZDEXTokenomicsLaneFieldsV1(
        lane.profile.profile_id,
        lane.route_release.route_release_id,
        lane.module_release.release_id,
        lane.coordinator_release.coordinator_release_id,
        lane.candidate.occurrence.occurrence_id,
        lane.profile.authority_epoch,
        lane.candidate.lane_candidate.module_journal.journal_root,
        journal.journal_root,
        _digest(canonical_global_bytes_v1(journal)),
        journal.pre_lane_root,
        journal.post_lane_root,
        journal.effect_plan_root,
        lane.module_release.guest_image_id,
        lane.coordinator_release.guest_image_id,
        _digest(lane.candidate.receipt.receipt_bytes),
        ReceiptKindV1.SUCCINCT,
    )


def _expected_request(lane: _Lane) -> tuple[bytes, str, bytes]:
    recomputed = lane.recompute(lane.candidate.lane_candidate)
    return (
        lane.candidate.receipt.receipt_bytes,
        lane.coordinator_release.guest_image_id,
        canonical_global_bytes_v1(recomputed.lane_journal),
    )


def _marker_fields(marker: common.VerifiedZDEXTokenomicsLaneV1) -> tuple[object, ...]:
    return tuple(getattr(marker, name) for name in _MARKER_FIELD_NAMES)


def _record_fields(fields: common._VerifiedZDEXTokenomicsLaneFieldsV1) -> tuple[object, ...]:
    return tuple(getattr(fields, name) for name in _MARKER_FIELD_NAMES)


def _with_lane_candidate(candidate: object, **changes: object) -> object:
    return replace(candidate, lane_candidate=replace(candidate.lane_candidate, **changes))


def _parse(relative: str) -> ast.Module:
    return ast.parse((REPO_ROOT / relative).read_text(encoding="utf-8"), filename=relative)


def _call_names(tree: ast.AST) -> list[str]:
    names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                names.append(node.func.attr)
            elif isinstance(node.func, ast.Name):
                names.append(node.func.id)
    return names


def _import_targets(tree: ast.AST) -> list[str]:
    targets: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            targets.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            targets.append("." * node.level + (node.module or ""))
    return targets


def _parameter_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            args = node.args
            names.update(
                parameter.arg
                for parameter in (*args.posonlyargs, *args.args, *args.kwonlyargs)
            )
    return names


# --- construction conformance ------------------------------------------------


def test_core_tokenomics_modules_have_no_callback_parameter_call_or_shell_import() -> None:
    for relative in _CORE_MODULES:
        tree = _parse(relative)
        imports = _import_targets(tree)
        assert not any(name.split(".")[0] in _EFFECT_IMPORT_ROOTS for name in imports), relative
        assert not any(
            "integration" in name.split(".") or name.startswith("..") for name in imports
        ), relative
        assert "verify_succinct_receipt" not in _call_names(tree), relative
        assert "receipt_verifier" not in _parameter_names(tree), relative
        assert not any(
            isinstance(node, ast.Name) and node.id == "ZDEXLaneSuccinctReceiptVerifierV1"
            for node in ast.walk(tree)
        ), relative
    for module in (common, burn_core, fee_core):
        assert not any(name.startswith("verify_") for name in module.__all__), module.__name__
        assert not any(hasattr(module, name) for name in _REMOVED_CORE_NAMES), module.__name__
    assert tuple(
        inspect.signature(burn_core.prepare_zdex_tokenomics_lane_receipt_v1).parameters
    ) == ("candidate", "governed")
    assert tuple(
        inspect.signature(fee_core.prepare_zdex_tokenomics_fee_lane_receipt_v1).parameters
    ) == ("candidate", "governed")
    assert "prepare_zdex_tokenomics_lane_receipt_v1" in burn_core.__all__
    assert "prepare_zdex_tokenomics_fee_lane_receipt_v1" in fee_core.__all__
    assert "PreparedZDEXTokenomicsLaneReceiptV1" in common.__all__
    assert "VerifiedZDEXTokenomicsLaneV1" in common.__all__
    assert "VerifiedZDEXTokenomicsLaneV1" in burn_core.__all__


def test_shell_owns_exactly_one_callback_invocation_and_the_public_verify_signatures() -> None:
    tree = _parse(_SHELL_MODULE)
    assert _call_names(tree).count("verify_succinct_receipt") == 1
    assert all(
        not name.startswith("..") or name.startswith("..core") for name in _import_targets(tree)
    )
    for name in (
        "verify_zdex_tokenomics_lane_receipt_v1",
        "verify_zdex_tokenomics_fee_lane_receipt_v1",
    ):
        assert tuple(inspect.signature(getattr(shell, name)).parameters) == (
            "candidate",
            "governed",
            "receipt_verifier",
        )
    assert shell.__all__ == [
        "verify_zdex_tokenomics_fee_lane_receipt_v1",
        "verify_zdex_tokenomics_lane_receipt_v1",
    ]
    # The marker type and its constructor discipline stay in core, unchanged.
    with pytest.raises(TypeError, match="verifier-constructed"):
        common.VerifiedZDEXTokenomicsLaneV1(object(), object())


# --- pure preparation -------------------------------------------------------


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_prepare_is_deterministic_and_preserves_every_old_marker_field(name: str) -> None:
    # Arrange
    lane = _lane(name)
    expected_fields = _expected_fields(lane)
    expected_request = _expected_request(lane)

    # Act: prepare twice with no verifier anywhere.
    first = lane.prepare(lane.candidate, lane.governed)
    second = lane.prepare(lane.candidate, lane.governed)

    # Assert: exact typed data, identical decision, complete request and field set.
    assert type(first) is common.PreparedZDEXTokenomicsLaneReceiptV1
    assert first == second
    assert first.verified_fields == expected_fields
    assert (first.receipt_bytes, first.expected_image_id, first.expected_journal_bytes) == (
        expected_request
    )
    assert first.verified_fields.receipt_digest == _digest(first.receipt_bytes)
    assert first.verified_fields.lane_journal_digest == _digest(first.expected_journal_bytes)
    assert first.expected_image_id == first.verified_fields.expected_image_id
    assert len(first.expected_journal_bytes) <= min(
        lane.route_release.max_journal_bytes,
        lane.coordinator_release.max_journal_bytes,
    )


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_prepared_subject_is_detached_from_candidate_and_governed_graph(name: str) -> None:
    # Arrange
    lane = _lane(name)
    prepared = lane.prepare(lane.candidate, lane.governed)
    facts = (prepared.verified_fields, prepared.receipt_bytes, prepared.expected_journal_bytes)

    # Act: mutate every caller-held source after preparation.
    object.__setattr__(lane.candidate.receipt, "receipt_bytes", b"mutated-after-prepare")
    object.__setattr__(lane.candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)
    object.__setattr__(lane.coordinator_release, "guest_image_id", _root(90_001))
    object.__setattr__(lane.coordinator_release, "coordinator_release_id", _root(90_002))
    object.__setattr__(lane.module_release, "guest_image_id", _root(90_003))
    snapshot = common.snapshot_prepared_zdex_tokenomics_lane_receipt_v1(prepared)

    # Assert
    assert (
        prepared.verified_fields,
        prepared.receipt_bytes,
        prepared.expected_journal_bytes,
    ) == facts
    assert snapshot == prepared
    assert snapshot is not prepared
    assert snapshot.verified_fields is not prepared.verified_fields


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_prepared_record_requires_exact_types_and_field_to_request_binding(name: str) -> None:
    lane = _lane(name)
    prepared = lane.prepare(lane.candidate, lane.governed)

    class _Forged(common.PreparedZDEXTokenomicsLaneReceiptV1):
        pass

    forged = _Forged(
        prepared.verified_fields, prepared.receipt_bytes, prepared.expected_journal_bytes
    )
    wrong_receipt_digest = replace(
        prepared,
        verified_fields=replace(prepared.verified_fields, receipt_digest=_root(1)),
    )
    wrong_journal_digest = replace(
        prepared,
        verified_fields=replace(prepared.verified_fields, lane_journal_digest=_root(2)),
    )
    verifier = _RecordingVerifier()

    for subject, error, message in (
        (forged, TypeError, "exact typed data"),
        (object(), TypeError, "exact typed data"),
        (wrong_receipt_digest, ValueError, "receipt digest mismatch"),
        (wrong_journal_digest, ValueError, "journal digest mismatch"),
    ):
        with pytest.raises(error, match=message):
            common.snapshot_prepared_zdex_tokenomics_lane_receipt_v1(subject)
        with pytest.raises(error, match=message):
            common._build_verified_zdex_tokenomics_lane_v1(subject)
        with pytest.raises(error, match=message):
            shell._execute_prepared_zdex_tokenomics_lane_receipt_v1(subject, verifier)
    assert verifier.calls == []
    with pytest.raises(TypeError, match="exact bytes"):
        common.PreparedZDEXTokenomicsLaneReceiptV1(
            prepared.verified_fields, bytearray(prepared.receipt_bytes), prepared.expected_journal_bytes
        )
    with pytest.raises(TypeError, match="exact typed data"):
        common.PreparedZDEXTokenomicsLaneReceiptV1(
            object(), prepared.receipt_bytes, prepared.expected_journal_bytes
        )


# --- rejection before any callback ------------------------------------------


@pytest.mark.parametrize("name", ("burn", "fee"))
@pytest.mark.parametrize(
    ("label", "error", "message"),
    (
        ("wrong_context", ValueError, "mismatch"),
        ("conditional_receipt_kind", ValueError, "requires a succinct receipt"),
        ("empty_receipt_bytes", ValueError, "receipt bytes must be nonempty"),
        ("rejected_lane_composition", ValueError, "composition rejected"),
        ("not_a_candidate", TypeError, "must be exact"),
    ),
)
def test_invalid_context_kind_journal_and_shape_reject_before_callback(
    name: str, label: str, error: type[Exception], message: str
) -> None:
    # Arrange: one-defect subjects.
    lane = _lane(name)
    candidate = lane.candidate
    if label == "wrong_context":
        candidate = _with_lane_candidate(
            candidate,
            context=replace(candidate.lane_candidate.context, coordinator_release_id=_root(999)),
        )
        message = lane.context_mismatch
    elif label == "conditional_receipt_kind":
        candidate = replace(
            candidate, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional")
        )
    elif label == "empty_receipt_bytes":
        candidate = replace(candidate, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""))
    elif label == "rejected_lane_composition":
        candidate = _with_lane_candidate(
            candidate,
            post_state=replace(candidate.lane_candidate.post_state, staking_state_root=_root(997)),
        )
    else:
        candidate = object()
    verifier = _RecordingVerifier()

    # Act / Assert: core rejects with no callback available; shell rejects with no call.
    with pytest.raises(error, match=message):
        lane.prepare(candidate, lane.governed)
    with pytest.raises(error, match=message):
        lane.verify(candidate, lane.governed, verifier)
    assert verifier.calls == []


def test_burn_lane_journal_ceiling_rejects_before_callback() -> None:
    candidate, governed, _ = _receipt_fixture(tokenomics_max_journal_bytes=1)
    verifier = _RecordingVerifier()

    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        burn_core.prepare_zdex_tokenomics_lane_receipt_v1(candidate, governed)
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        shell.verify_zdex_tokenomics_lane_receipt_v1(candidate, governed, verifier)
    assert verifier.calls == []


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_common_preparation_rejects_journal_binding_and_ceiling_without_any_callback(
    name: str,
) -> None:
    # Arrange: the exact recomputed lane journal plus the entry point's own bindings.
    lane = _lane(name)
    recomputed = lane.recompute(lane.candidate.lane_candidate)
    journal = recomputed.lane_journal
    binding = common._ZDEXTokenomicsLaneBindingV1(
        lane.profile.profile_id,
        lane.route_release.route_release_id,
        lane.module_release.release_id,
        lane.candidate.occurrence.occurrence_id,
        lane.profile.authority_epoch,
        lane.candidate.lane_candidate.module_journal.journal_root,
        lane.module_release.guest_image_id,
    )
    expectation = common._ZDEXTokenomicsCoordinatorReceiptExpectationV1(
        lane.route_release, lane.coordinator_release
    )
    tight = LaneCoordinatorReleaseV1.build(
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        semantic_version="1.0.0-shadow-test",
        coordinator_schema_root=_root(9_700),
        guest_image_id=_root(9_701),
        specification_root=_root(9_702),
        source_root=_root(9_703),
        toolchain_root=_root(9_704),
        max_cycles=1_000_000,
        max_journal_bytes=1,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_objects=False,
    )
    assert tuple(
        inspect.signature(common._prepare_zdex_tokenomics_lane_receipt_v1).parameters
    ) == ("receipt", "journal", "expectation", "binding")

    # Act / Assert: the control subject prepares; each one-defect subject rejects.
    control = common._prepare_zdex_tokenomics_lane_receipt_v1(
        lane.candidate.receipt, journal, expectation, binding
    )
    assert control == lane.prepare(lane.candidate, lane.governed)
    with pytest.raises(ValueError, match="verified-lane binding mismatch"):
        common._prepare_zdex_tokenomics_lane_receipt_v1(
            lane.candidate.receipt,
            replace(journal, command_occurrence_id=_root(31)),
            expectation,
            binding,
        )
    with pytest.raises(ValueError, match="verified-lane binding mismatch"):
        common._prepare_zdex_tokenomics_lane_receipt_v1(
            lane.candidate.receipt,
            journal,
            expectation,
            replace(binding, module_journal_root=_root(32)),
        )
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        common._prepare_zdex_tokenomics_lane_receipt_v1(
            lane.candidate.receipt,
            replace(journal, coordinator_release_id=tight.coordinator_release_id),
            common._ZDEXTokenomicsCoordinatorReceiptExpectationV1(lane.route_release, tight),
            binding,
        )
    with pytest.raises(TypeError, match="binding must be exact typed data"):
        common._prepare_zdex_tokenomics_lane_receipt_v1(
            lane.candidate.receipt, journal, expectation, object()
        )


# --- shell execution ---------------------------------------------------------


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_shell_executes_exactly_the_prepared_receipt_image_and_journal(name: str) -> None:
    # Arrange
    lane = _lane(name)
    prepared = lane.prepare(lane.candidate, lane.governed)
    expected_request = _expected_request(lane)
    verifier = _RecordingVerifier()

    # Act
    marker = lane.verify(lane.candidate, lane.governed, verifier)

    # Assert: one call, exact request, marker minted from exactly those bytes and fields.
    assert verifier.calls == [expected_request]
    assert verifier.calls == [
        (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    ]
    assert type(marker) is common.VerifiedZDEXTokenomicsLaneV1
    assert _marker_fields(marker) == _record_fields(prepared.verified_fields)
    assert marker.receipt_digest == _digest(verifier.calls[0][0])
    assert marker.expected_image_id == verifier.calls[0][1]
    assert marker.lane_journal_digest == _digest(verifier.calls[0][2])
    assert marker.binding_root == lane.binding_root_pin
    with pytest.raises(AttributeError, match="immutable"):
        marker._fields = object()


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_callback_exception_propagates_and_no_marker_is_returned(name: str) -> None:
    lane = _lane(name)
    verifier = _RecordingVerifier(reject=True)
    outcome: object = None

    try:
        outcome = lane.verify(lane.candidate, lane.governed, verifier)
    except ValueError as exc:
        assert str(exc) == "boundary verifier rejection"
    else:
        raise AssertionError("verifier rejection did not propagate")

    assert outcome is None
    assert verifier.calls == [_expected_request(lane)]


@pytest.mark.parametrize("name", ("burn", "fee"))
@pytest.mark.parametrize("result", (True, object(), b"ok", 0))
def test_reference_callback_non_none_return_is_still_ignored(name: str, result: object) -> None:
    lane = _lane(name)
    verifier = _RecordingVerifier(result=result)

    marker = lane.verify(lane.candidate, lane.governed, verifier)

    assert len(verifier.calls) == 1
    assert marker.binding_root == lane.binding_root_pin


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker(
    name: str,
) -> None:
    # Arrange: the caller keeps every alias the callback could reach.
    lane = _lane(name)
    prepared = lane.prepare(lane.candidate, lane.governed)
    expected_fields = _record_fields(prepared.verified_fields)
    expected_request = (
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
    )
    forged_fields = replace(
        prepared.verified_fields,
        coordinator_release_id=_root(78_501),
        expected_image_id=_root(78_502),
        receipt_digest=_digest(b"mutated-lane"),
        lane_journal_digest=_digest(b"mutated-journal"),
    )

    class _MutatingVerifier(_RecordingVerifier):
        def verify_succinct_receipt(
            self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            object.__setattr__(prepared, "verified_fields", forged_fields)
            object.__setattr__(prepared, "receipt_bytes", b"mutated-lane")
            object.__setattr__(prepared, "expected_journal_bytes", b"mutated-journal")
            object.__setattr__(lane.coordinator_release, "coordinator_release_id", _root(78_501))
            object.__setattr__(lane.coordinator_release, "guest_image_id", _root(78_502))
            object.__setattr__(lane.candidate.receipt, "receipt_bytes", b"mutated-lane")
            object.__setattr__(lane.candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)

    verifier = _MutatingVerifier()

    # Act: execute the caller-held prepared alias directly.
    marker = shell._execute_prepared_zdex_tokenomics_lane_receipt_v1(prepared, verifier)

    # Assert: the marker is the executed subject, not the mutated alias.
    assert verifier.calls == [expected_request]
    assert _marker_fields(marker) == expected_fields
    assert marker.binding_root == lane.binding_root_pin
    assert prepared.verified_fields == forged_fields


def test_substituted_prepared_subject_is_never_accepted_as_the_executed_one() -> None:
    # Arrange: two valid subjects; the callback swaps the fee subject into the burn alias.
    burn = _lane("burn")
    fee = _lane("fee")
    burn_prepared = burn.prepare(burn.candidate, burn.governed)
    fee_prepared = fee.prepare(fee.candidate, fee.governed)
    assert burn_prepared != fee_prepared
    burn_fields = _record_fields(burn_prepared.verified_fields)
    burn_request = (
        burn_prepared.receipt_bytes,
        burn_prepared.expected_image_id,
        burn_prepared.expected_journal_bytes,
    )

    class _SubstitutingVerifier(_RecordingVerifier):
        def verify_succinct_receipt(
            self, receipt_bytes: bytes, *, expected_image_id: str, expected_journal_bytes: bytes
        ) -> None:
            super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            object.__setattr__(burn_prepared, "verified_fields", fee_prepared.verified_fields)
            object.__setattr__(burn_prepared, "receipt_bytes", fee_prepared.receipt_bytes)
            object.__setattr__(
                burn_prepared, "expected_journal_bytes", fee_prepared.expected_journal_bytes
            )

    verifier = _SubstitutingVerifier()

    # Act
    marker = shell._execute_prepared_zdex_tokenomics_lane_receipt_v1(burn_prepared, verifier)

    # Assert: only the executed burn subject is labelled; the fee subject was never executed.
    assert verifier.calls == [burn_request]
    assert _marker_fields(marker) == burn_fields
    assert marker.binding_root == _BURN_BINDING_ROOT_PIN
    assert marker.binding_root != _FEE_BINDING_ROOT_PIN
    assert burn_prepared == fee_prepared
    # No public binding API accepts a separate execution-evidence label here.
    # This shell path mints from its executed snapshot; the private core factory
    # remains available and grants no authority on its own.
    assert not any(name.startswith("bind_") for name in shell.__all__)
    assert not any(name.startswith("bind_verified") for name in common.__all__)


# --- semantic mutants (executed, structure-preserving) -----------------------


def _mutant(module: object, original: Callable[..., object], target: str, body: str) -> object:
    source = inspect.getsource(original)
    assert source.count(target) == 1, "mutant target is no longer unique"
    namespace = dict(vars(module))
    exec(  # noqa: S102 - deliberate structure-preserving mutant of the boundary
        compile(source.replace(target, body, 1), f"<mutant:{original.__name__}>", "exec"),
        namespace,
    )
    return namespace[original.__name__]


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_execute_before_prepare_mutant_is_killed_by_the_no_call_law(name: str) -> None:
    lane = _lane(name)
    original = lane.verify
    prepare_name = lane.prepare.__name__
    target = f"    prepared = {prepare_name}(candidate, governed)\n"
    mutant_body = (
        "    receipt_verifier.verify_succinct_receipt(\n"
        "        candidate.receipt.receipt_bytes,\n"
        "        expected_image_id=governed._fields.coordinator_release.guest_image_id,\n"
        "        expected_journal_bytes=b'',\n"
        "    )\n"
        f"    prepared = {prepare_name}(candidate, governed)\n"
    )
    mutant = _mutant(shell, original, target, mutant_body)
    tampered = replace(
        lane.candidate, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional")
    )

    # Control: the ordinary law holds on the unmutated shell.
    control_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        original(tampered, lane.governed, control_verifier)
    assert control_verifier.calls == []

    # Mutant: the same rejection is raised, but the no-call assertion is reachable and fails.
    mutant_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        mutant(tampered, lane.governed, mutant_verifier)
    assert mutant_verifier.calls == [
        (b"conditional", lane.coordinator_release.guest_image_id, b"")
    ]
    with pytest.raises(AssertionError):
        assert mutant_verifier.calls == []


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_mint_from_caller_alias_mutant_is_killed_by_the_alias_mutation_observation(
    name: str,
) -> None:
    lane = _lane(name)
    original = shell._execute_prepared_zdex_tokenomics_lane_receipt_v1
    mutant = _mutant(
        shell,
        original,
        "    return _build_verified_zdex_tokenomics_lane_v1(owned)\n",
        "    return _build_verified_zdex_tokenomics_lane_v1(prepared)\n",
    )
    forged_id = _root(78_601)

    def _run(execute: Callable[..., common.VerifiedZDEXTokenomicsLaneV1]) -> str:
        prepared = lane.prepare(lane.candidate, lane.governed)
        forged = replace(prepared.verified_fields, coordinator_release_id=forged_id)

        class _MutatingVerifier(_RecordingVerifier):
            def verify_succinct_receipt(
                self,
                receipt_bytes: bytes,
                *,
                expected_image_id: str,
                expected_journal_bytes: bytes,
            ) -> None:
                super().verify_succinct_receipt(
                    receipt_bytes,
                    expected_image_id=expected_image_id,
                    expected_journal_bytes=expected_journal_bytes,
                )
                object.__setattr__(prepared, "verified_fields", forged)

        return execute(prepared, _MutatingVerifier()).coordinator_release_id

    # Control: the unmutated shell reports the executed subject.
    assert _run(original) == lane.coordinator_release.coordinator_release_id
    # Mutant: the caller alias relabels the marker, so the observation fails.
    assert _run(mutant) == forged_id
    with pytest.raises(AssertionError):
        assert _run(mutant) == lane.coordinator_release.coordinator_release_id


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_wrong_image_request_mutant_is_killed_by_the_exact_request_observation(
    name: str,
) -> None:
    lane = _lane(name)
    original = shell._execute_prepared_zdex_tokenomics_lane_receipt_v1
    mutant = _mutant(
        shell,
        original,
        "        expected_image_id=owned.expected_image_id,\n",
        "        expected_image_id=owned.verified_fields.module_image_id,\n",
    )
    prepared = lane.prepare(lane.candidate, lane.governed)
    expected_request = (
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
    )
    assert lane.module_release.guest_image_id != lane.coordinator_release.guest_image_id

    control_verifier = _RecordingVerifier()
    original(prepared, control_verifier)
    assert control_verifier.calls == [expected_request]

    mutant_verifier = _RecordingVerifier()
    mutant(prepared, mutant_verifier)
    assert mutant_verifier.calls == [
        (prepared.receipt_bytes, lane.module_release.guest_image_id, prepared.expected_journal_bytes)
    ]
    with pytest.raises(AssertionError):
        assert mutant_verifier.calls == [expected_request]


@pytest.mark.parametrize("name", ("burn", "fee"))
def test_missing_field_to_request_binding_mutant_is_killed_by_the_digest_observation(
    name: str,
) -> None:
    lane = _lane(name)
    original = common.snapshot_prepared_zdex_tokenomics_lane_receipt_v1
    mutant = _mutant(
        common,
        original,
        "    _require_prepared_zdex_tokenomics_lane_digests_v1(prepared)\n",
        "    pass\n",
    )
    prepared = lane.prepare(lane.candidate, lane.governed)
    inconsistent = replace(
        prepared,
        verified_fields=replace(prepared.verified_fields, receipt_digest=_digest(b"other")),
    )

    # Control: the unmutated snapshot refuses a record whose digest is unbound to its bytes.
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        original(inconsistent)
    # Mutant: the same record is accepted with its digest unbound from its bytes, so
    # the control rejection is unreachable and the shell would execute unbound bytes.
    accepted = mutant(inconsistent)
    assert accepted == inconsistent
    assert accepted.verified_fields.receipt_digest != _digest(accepted.receipt_bytes)
    verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        shell._execute_prepared_zdex_tokenomics_lane_receipt_v1(inconsistent, verifier)
    assert verifier.calls == []
