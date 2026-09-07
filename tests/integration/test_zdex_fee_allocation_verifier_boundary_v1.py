"""Boundary evidence for the ZDEX fee-allocation leaf receipt extraction.

Core prepares one exact detached subject (the 18 marker fields plus the exact
receipt, module image and canonical allocation journal bytes) and calls no
verifier; the integration shell executes exactly that subject on the
caller-supplied reference verifier and mints the existing non-authoritative
marker from the executed subject only.  Every verifier here is a deterministic
recorder, never cryptographic evidence, and nothing below grants publication or
production authority.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
from collections.abc import Callable
from dataclasses import fields as dataclass_fields
from dataclasses import replace
from pathlib import Path
from typing import Any, TypeVar, cast

import pytest

import src.core.zdex_fee_allocation_receipt_verification_v1 as core
import src.integration.zdex_fee_allocation_receipt_verification_v1 as shell
from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    RouteReleaseV1,
    canonical_global_bytes_v1,
)
from src.core.zdex_fee_allocation_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    transition_zdex_fee_allocation_v1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import ZDEXLaneReceiptEnvelopeV1
from src.core.zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
)
from tests.core.test_zdex_purchase_burn_route_v1 import (
    _allocation_route_release,
    _fee_receipt_candidate_fixture,
    _governed_shadow_profile,
    _HostileRoot,
    _lane_release,
    _root,
    _route_release,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
_ReleaseT = TypeVar("_ReleaseT", LaneModuleReleaseV1, RouteReleaseV1)

_CORE_MODULE = "src/core/zdex_fee_allocation_receipt_verification_v1.py"
_SHELL_MODULE = "src/integration/zdex_fee_allocation_receipt_verification_v1.py"
_EFFECT_IMPORT_ROOTS = frozenset(
    {"threading", "weakref", "os", "sys", "time", "datetime", "random", "pathlib", "importlib"}
)
# Marker binding root captured on the pre-extraction tree (base 6cc1fc7ee) with the
# retained route fixture and recorder.  The extraction must reproduce it exactly.
_BINDING_ROOT_PIN = "0x3859e5a636d74429c1757ff56f9dc4f1b71212a7fe3c4448eea40eda1ff04f14"
_JOURNAL_LEN_PIN = 1472
_MARKER_FIELD_NAMES = (
    "allocation_route_release_id",
    "authorized_buyback_route_release_id",
    "module_release_id",
    "command_occurrence_id",
    "profile_root",
    "writer_epoch",
    "journal_root",
    "journal_digest",
    "effect_plan_root",
    "expected_image_id",
    "receipt_digest",
    "receipt_kind",
    "policy_root",
    "fee_asset_id",
    "fee_ingress_atoms",
    "buyback_quote_atoms",
    "pre_lane_root",
    "post_lane_root",
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


def _expected_fields(
    candidate: core.ZDEXFeeAllocationReceiptCandidateV1,
    governed: core.GovernedZDEXFeeAllocationProfileV1,
) -> core._VerifiedZDEXFeeAllocationFieldsV1:
    """Independent derivation of the old 18 marker fields from fixture facts."""

    fields = governed._fields
    occurrence = candidate.occurrence
    accepted = transition_zdex_fee_allocation_v1(
        ZDEXFeeAllocationContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=occurrence.profile_root,
            writer_epoch=candidate.journal.writer_epoch,
            allocation_route_release_id=fields.allocation_route.route_release_id,
            authorized_buyback_route_release_id=fields.buyback_route.route_release_id,
            tokenomics_module_release_id=fields.module_release.release_id,
            command_occurrence_id=occurrence.occurrence_id,
            policy_root=candidate.policy.policy_root,
        ),
        candidate.pre_state,
        candidate.policy,
        ZDEXFeeAllocationCommandV1(candidate.journal.fee_charged_atoms),
    )
    assert type(accepted) is ZDEXFeeAllocationAcceptedV1
    journal = accepted.occurrence
    return core._VerifiedZDEXFeeAllocationFieldsV1(
        fields.allocation_route.route_release_id,
        fields.buyback_route.route_release_id,
        fields.module_release.release_id,
        occurrence.occurrence_id,
        occurrence.profile_root,
        journal.writer_epoch,
        journal.occurrence_root,
        _digest(canonical_global_bytes_v1(journal)),
        accepted.effects.effect_plan_root,
        fields.module_release.guest_image_id,
        _digest(candidate.receipt.receipt_bytes),
        ReceiptKindV1.SUCCINCT,
        candidate.policy.policy_root,
        journal.fee_asset_id,
        candidate.pre_state.fee_ingress_atoms,
        journal.buyback_quote_atoms,
        journal.pre_lane_root,
        journal.post_lane_root,
    )


def _expected_request(
    candidate: core.ZDEXFeeAllocationReceiptCandidateV1,
    governed: core.GovernedZDEXFeeAllocationProfileV1,
) -> tuple[bytes, str, bytes]:
    return (
        candidate.receipt.receipt_bytes,
        governed._fields.module_release.guest_image_id,
        canonical_global_bytes_v1(candidate.journal),
    )


def _marker_fields(marker: core.VerifiedZDEXFeeAllocationV1) -> tuple[object, ...]:
    return tuple(getattr(marker, name) for name in _MARKER_FIELD_NAMES)


def _record_fields(fields: core._VerifiedZDEXFeeAllocationFieldsV1) -> tuple[object, ...]:
    return tuple(getattr(fields, name) for name in _MARKER_FIELD_NAMES)


def _prepared_facts(prepared: core.PreparedZDEXFeeAllocationReceiptV1) -> tuple[object, ...]:
    return (
        _record_fields(prepared.verified_fields),
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
    )


def _rebuilt_release(
    release: _ReleaseT,
    build: Callable[..., _ReleaseT],
    *,
    id_field: str,
    max_journal_bytes: int,
) -> _ReleaseT:
    values = {
        field.name: getattr(release, field.name)
        for field in dataclass_fields(release)
        if field.name != id_field
    }
    values["max_journal_bytes"] = max_journal_bytes
    return build(**values)


def _governed_with_journal_ceilings(
    base: core.ZDEXFeeAllocationReceiptCandidateV1,
    base_governed: core.GovernedZDEXFeeAllocationProfileV1,
    *,
    module_max_journal_bytes: int,
    allocation_route_max_journal_bytes: int,
) -> core.GovernedZDEXFeeAllocationProfileV1:
    """Rebuild and bind the retained profile with only its two ceilings changed."""

    spot_release = _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1)
    burn_release = _rebuilt_release(
        _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2),
        LaneModuleReleaseV1.build,
        id_field="release_id",
        max_journal_bytes=module_max_journal_bytes,
    )
    assert type(burn_release) is LaneModuleReleaseV1
    route = _route_release(spot_release, burn_release)
    allocation_route = _rebuilt_release(
        _allocation_route_release(burn_release),
        RouteReleaseV1.build,
        id_field="route_release_id",
        max_journal_bytes=allocation_route_max_journal_bytes,
    )
    assert type(allocation_route) is RouteReleaseV1
    profile, policy_registry = _governed_shadow_profile(
        spot_release=spot_release,
        tokenomics_release=burn_release,
        buyback_route=route,
        allocation_route=allocation_route,
        policy_root=base.policy.policy_root,
        buyback_execution_policy_root=base_governed._fields.policy_registry.require_binding(
            policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
            command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        ).policy_root,
    )
    return core.bind_zdex_fee_allocation_shadow_profile_v1(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
        policy_registry=policy_registry,
    )


def _fixture_with_journal_ceilings(
    *,
    module_max_journal_bytes: int,
    allocation_route_max_journal_bytes: int,
    receipt_bytes: bytes = b"fee-allocation-receipt",
) -> tuple[
    core.ZDEXFeeAllocationReceiptCandidateV1,
    core.GovernedZDEXFeeAllocationProfileV1,
]:
    """Derive a candidate through the transition under the rebuilt profile."""

    base, base_governed = _fee_receipt_candidate_fixture()
    governed = _governed_with_journal_ceilings(
        base,
        base_governed,
        module_max_journal_bytes=module_max_journal_bytes,
        allocation_route_max_journal_bytes=allocation_route_max_journal_bytes,
    )
    fields = governed._fields
    occurrence = replace(
        base.occurrence,
        route_release_id=fields.allocation_route.route_release_id,
        profile_root=fields.profile.profile_id,
    )
    accepted = transition_zdex_fee_allocation_v1(
        ZDEXFeeAllocationContextV1(
            chain_id=occurrence.chain_id,
            deployment_root=occurrence.deployment_root,
            profile_root=fields.profile.profile_id,
            writer_epoch=base.journal.writer_epoch,
            allocation_route_release_id=fields.allocation_route.route_release_id,
            authorized_buyback_route_release_id=fields.buyback_route.route_release_id,
            tokenomics_module_release_id=fields.module_release.release_id,
            command_occurrence_id=occurrence.occurrence_id,
            policy_root=base.policy.policy_root,
        ),
        base.pre_state,
        base.policy,
        ZDEXFeeAllocationCommandV1(base.journal.fee_charged_atoms),
    )
    assert type(accepted) is ZDEXFeeAllocationAcceptedV1
    candidate = core.ZDEXFeeAllocationReceiptCandidateV1(
        occurrence,
        base.policy,
        base.pre_state,
        accepted.post_state,
        accepted.occurrence,
        accepted.effects,
        ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, receipt_bytes),
    )
    assert len(canonical_global_bytes_v1(candidate.journal)) == _JOURNAL_LEN_PIN
    return candidate, governed


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


def test_core_fee_leaf_module_has_no_callback_parameter_call_or_shell_import() -> None:
    tree = _parse(_CORE_MODULE)
    imports = _import_targets(tree)
    assert not any(name.split(".")[0] in _EFFECT_IMPORT_ROOTS for name in imports)
    assert not any("integration" in name.split(".") or name.startswith("..") for name in imports)
    assert "verify_succinct_receipt" not in _call_names(tree)
    assert "receipt_verifier" not in _parameter_names(tree)
    assert not any(
        isinstance(node, ast.Name) and node.id == "ZDEXLaneSuccinctReceiptVerifierV1"
        for node in ast.walk(tree)
    )
    assert not any(name.startswith("verify_") for name in core.__all__)
    assert not hasattr(core, "verify_zdex_fee_allocation_receipt_v1")
    assert tuple(inspect.signature(core.prepare_zdex_fee_allocation_receipt_v1).parameters) == (
        "candidate",
        "governed",
    )
    for name in (
        "GovernedZDEXFeeAllocationProfileV1",
        "PreparedZDEXFeeAllocationReceiptV1",
        "VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1",
        "VerifiedZDEXFeeAllocationV1",
        "ZDEXFeeAllocationReceiptCandidateV1",
        "bind_zdex_fee_allocation_shadow_profile_v1",
        "prepare_zdex_fee_allocation_receipt_v1",
        "snapshot_prepared_zdex_fee_allocation_receipt_v1",
    ):
        assert name in core.__all__, name
    assert len(dataclass_fields(core._VerifiedZDEXFeeAllocationFieldsV1)) == 18
    assert tuple(
        field.name for field in dataclass_fields(core._VerifiedZDEXFeeAllocationFieldsV1)
    ) == _MARKER_FIELD_NAMES


def test_shell_owns_exactly_one_callback_invocation_and_the_public_verify_signature() -> None:
    tree = _parse(_SHELL_MODULE)
    assert _call_names(tree).count("verify_succinct_receipt") == 1
    assert all(
        not name.startswith("..") or name.startswith("..core") for name in _import_targets(tree)
    )
    assert tuple(
        inspect.signature(shell.verify_zdex_fee_allocation_receipt_v1).parameters
    ) == ("candidate", "governed", "receipt_verifier")
    assert shell.__all__ == ["verify_zdex_fee_allocation_receipt_v1"]
    # The marker type and its constructor discipline stay in core, unchanged.
    with pytest.raises(TypeError, match="verifier-constructed"):
        core.VerifiedZDEXFeeAllocationV1(object(), cast(Any, object()))


# --- pure preparation -------------------------------------------------------


def test_prepare_is_deterministic_and_preserves_all_18_fields_and_binding_root() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    expected_fields = _expected_fields(candidate, governed)

    # Act: prepare twice with no verifier anywhere.
    first = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    second = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)

    # Assert: exact typed data, identical decision, complete request and field set.
    assert type(first) is core.PreparedZDEXFeeAllocationReceiptV1
    assert first == second
    assert first.verified_fields == expected_fields
    assert (first.receipt_bytes, first.expected_image_id, first.expected_journal_bytes) == (
        _expected_request(candidate, governed)
    )
    assert first.verified_fields.receipt_digest == _digest(first.receipt_bytes)
    assert first.verified_fields.journal_digest == _digest(first.expected_journal_bytes)
    assert len(first.expected_journal_bytes) == _JOURNAL_LEN_PIN
    assert len(first.expected_journal_bytes) <= min(
        fields.module_release.max_journal_bytes,
        fields.allocation_route.max_journal_bytes,
    )
    # Expected image is the module release image, distinct from coordinator and route.
    assert first.expected_image_id == fields.module_release.guest_image_id
    assert first.expected_image_id != fields.coordinator_release.guest_image_id
    assert first.expected_image_id != fields.allocation_route.guest_image_id
    # Ingress comes from the pre-state, buyback quote from the recomputed journal.
    assert first.verified_fields.fee_ingress_atoms == candidate.pre_state.fee_ingress_atoms
    assert first.verified_fields.buyback_quote_atoms == candidate.journal.buyback_quote_atoms
    assert first.verified_fields.fee_ingress_atoms != first.verified_fields.buyback_quote_atoms
    # The private factory mints the identical binding root the old path produced.
    marker = core._build_verified_zdex_fee_allocation_v1(first)
    assert _marker_fields(marker) == _record_fields(expected_fields)
    assert marker.binding_root == _BINDING_ROOT_PIN


def test_prepared_subject_is_detached_from_candidate_and_governed_graph() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    facts = _prepared_facts(prepared)

    # Act: mutate every nested caller-held source after preparation.
    object.__setattr__(candidate.journal.allocations[0], "allocation_atoms", 90_001)
    object.__setattr__(candidate.policy.shares[0], "share_bps", 1)
    object.__setattr__(candidate.pre_state.destination_balances[0], "allocation_atoms", 90_002)
    object.__setattr__(candidate.pre_state, "fee_ingress_atoms", 90_003)
    object.__setattr__(candidate, "effects", GlobalEconomicEffectPlanV1.empty())
    object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-after-prepare")
    object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)
    object.__setattr__(fields.module_release, "guest_image_id", _root(90_004))
    object.__setattr__(fields.module_release, "release_id", _root(90_005))
    object.__setattr__(fields.allocation_route, "route_release_id", _root(90_006))
    snapshot = core.snapshot_prepared_zdex_fee_allocation_receipt_v1(prepared)

    # Assert
    assert _prepared_facts(prepared) == facts
    assert snapshot == prepared
    assert snapshot is not prepared
    assert snapshot.verified_fields is not prepared.verified_fields


def test_prepared_record_requires_exact_types_and_field_to_request_binding() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)

    class _Forged(core.PreparedZDEXFeeAllocationReceiptV1):
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
        verified_fields=replace(prepared.verified_fields, journal_digest=_root(2)),
    )
    hostile_scalar = replace(
        prepared,
        verified_fields=replace(
            prepared.verified_fields,
            fee_asset_id=_HostileRoot(prepared.verified_fields.fee_asset_id),
        ),
    )
    verifier = _RecordingVerifier()

    for subject, error, message in (
        (forged, TypeError, "exact typed data"),
        (object(), TypeError, "exact typed data"),
        (hostile_scalar, TypeError, "exact primitive"),
        (wrong_receipt_digest, ValueError, "receipt digest mismatch"),
        (wrong_journal_digest, ValueError, "journal digest mismatch"),
    ):
        # These values intentionally cross the typed boundary malformed.
        untyped_subject: Any = subject
        with pytest.raises(error, match=message):
            core.snapshot_prepared_zdex_fee_allocation_receipt_v1(untyped_subject)
        with pytest.raises(error, match=message):
            core._build_verified_zdex_fee_allocation_v1(untyped_subject)
        with pytest.raises(error, match=message):
            shell._execute_prepared_zdex_fee_allocation_receipt_v1(untyped_subject, verifier)
    assert verifier.calls == []


def test_prepared_constructor_refuses_non_exact_field_and_byte_types() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)

    with pytest.raises(TypeError, match="exact bytes"):
        core.PreparedZDEXFeeAllocationReceiptV1(
            prepared.verified_fields,
            cast(Any, bytearray(prepared.receipt_bytes)),
            prepared.expected_journal_bytes,
        )
    with pytest.raises(TypeError, match="exact bytes"):
        core.PreparedZDEXFeeAllocationReceiptV1(
            prepared.verified_fields,
            prepared.receipt_bytes,
            cast(Any, prepared.expected_journal_bytes.decode("ascii")),
        )
    with pytest.raises(TypeError, match="exact typed data"):
        core.PreparedZDEXFeeAllocationReceiptV1(
            cast(Any, object()),
            prepared.receipt_bytes,
            prepared.expected_journal_bytes,
        )


# --- rejection before any callback ------------------------------------------


def _shifted_allocations(
    candidate: core.ZDEXFeeAllocationReceiptCandidateV1,
) -> core.ZDEXFeeAllocationReceiptCandidateV1:
    allocations = list(candidate.journal.allocations)
    allocations[0] = replace(allocations[0], allocation_atoms=allocations[0].allocation_atoms - 1)
    allocations[2] = replace(allocations[2], allocation_atoms=allocations[2].allocation_atoms + 1)
    return replace(candidate, journal=replace(candidate.journal, allocations=tuple(allocations)))


@pytest.mark.parametrize(
    ("label", "error", "message"),
    (
        ("not_a_candidate", TypeError, "candidate must be exact typed data"),
        ("wrong_profile_binding", ValueError, "governed profile binding mismatch"),
        ("wrong_occurrence_command", ValueError, "occurrence mismatch"),
        ("shifted_allocations", ValueError, "journal or effects mismatch"),
        ("conditional_receipt_kind", ValueError, "requires a succinct receipt"),
        ("empty_receipt_bytes", ValueError, "receipt bytes must be nonempty"),
        # Paired defects: the earlier phase's rejection must be the first error.
        ("profile_binding_then_receipt_kind", ValueError, "governed profile binding mismatch"),
        ("occurrence_then_shifted_allocations", ValueError, "occurrence mismatch"),
        ("shifted_allocations_then_empty_receipt", ValueError, "journal or effects mismatch"),
        ("fake_kind_then_empty_bytes", ValueError, "requires a succinct receipt"),
    ),
)
def test_invalid_input_rejects_before_callback_in_the_reference_order(
    label: str, error: type[Exception], message: str
) -> None:
    # Arrange: one- and two-defect subjects.
    candidate, governed = _fee_receipt_candidate_fixture()
    subject: Any = candidate
    if label == "not_a_candidate":
        subject = object()
    if label in {"wrong_profile_binding", "profile_binding_then_receipt_kind"}:
        subject = replace(candidate, occurrence=replace(candidate.occurrence, profile_root=_root(998)))
    if label in {"wrong_occurrence_command", "occurrence_then_shifted_allocations"}:
        subject = replace(
            candidate,
            occurrence=replace(candidate.occurrence, command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1),
        )
    if label in {
        "shifted_allocations",
        "occurrence_then_shifted_allocations",
        "shifted_allocations_then_empty_receipt",
    }:
        subject = _shifted_allocations(subject)
    if label in {"conditional_receipt_kind", "profile_binding_then_receipt_kind"}:
        subject = replace(
            subject,
            receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional"),
        )
    if label in {"empty_receipt_bytes", "shifted_allocations_then_empty_receipt"}:
        subject = replace(subject, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b""))
    if label == "fake_kind_then_empty_bytes":
        subject = replace(candidate, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.FAKE, b""))
    verifier = _RecordingVerifier()

    # Act / Assert: core rejects with no callback available; shell rejects with no call.
    with pytest.raises(error, match=message):
        core.prepare_zdex_fee_allocation_receipt_v1(subject, governed)
    with pytest.raises(error, match=message):
        shell.verify_zdex_fee_allocation_receipt_v1(subject, governed, verifier)
    assert verifier.calls == []


@pytest.mark.parametrize("tight", ("module_release", "allocation_route"))
def test_journal_ceiling_accepts_at_bound_and_rejects_one_below_on_either_release(
    tight: str,
) -> None:
    # Arrange: the tight side is the minimum; the other side keeps the fixture ceiling.
    loose = 65_536

    def fixture(
        limit: int, receipt_bytes: bytes = b"fee-allocation-receipt"
    ) -> tuple[
        core.ZDEXFeeAllocationReceiptCandidateV1,
        core.GovernedZDEXFeeAllocationProfileV1,
    ]:
        return _fixture_with_journal_ceilings(
            module_max_journal_bytes=limit if tight == "module_release" else loose,
            allocation_route_max_journal_bytes=limit if tight == "allocation_route" else loose,
            receipt_bytes=receipt_bytes,
        )

    # A receipt longer than the journal ceiling shows the ceiling is a journal bound,
    # never a receipt-byte bound.
    long_receipt = b"r" * (_JOURNAL_LEN_PIN + 1)
    at_bound, at_bound_governed = fixture(_JOURNAL_LEN_PIN, long_receipt)
    one_below, one_below_governed = fixture(_JOURNAL_LEN_PIN - 1)
    fields = at_bound_governed._fields
    assert min(fields.module_release.max_journal_bytes, fields.allocation_route.max_journal_bytes) == (
        _JOURNAL_LEN_PIN
    )

    # Act / Assert: at bound prepares and executes exactly once.
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(at_bound, at_bound_governed)
    assert len(prepared.expected_journal_bytes) == _JOURNAL_LEN_PIN
    assert len(prepared.receipt_bytes) > _JOURNAL_LEN_PIN
    accepting = _RecordingVerifier()
    marker = shell.verify_zdex_fee_allocation_receipt_v1(at_bound, at_bound_governed, accepting)
    assert accepting.calls == [_expected_request(at_bound, at_bound_governed)]
    assert marker.receipt_digest == _digest(long_receipt)

    # Act / Assert: one below rejects in core and in the shell before any call.
    rejecting = _RecordingVerifier()
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        core.prepare_zdex_fee_allocation_receipt_v1(one_below, one_below_governed)
    with pytest.raises(ValueError, match="journal exceeds release byte ceiling"):
        shell.verify_zdex_fee_allocation_receipt_v1(one_below, one_below_governed, rejecting)
    assert rejecting.calls == []

    # Paired failures observe precedence directly: empty receipt bytes reject
    # before the same over-ceiling journal is considered.
    empty_and_over_ceiling = replace(
        one_below, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"")
    )
    with pytest.raises(ValueError, match="receipt bytes must be nonempty"):
        core.prepare_zdex_fee_allocation_receipt_v1(empty_and_over_ceiling, one_below_governed)
    with pytest.raises(ValueError, match="receipt bytes must be nonempty"):
        shell.verify_zdex_fee_allocation_receipt_v1(
            empty_and_over_ceiling, one_below_governed, rejecting
        )
    assert rejecting.calls == []


# --- shell execution ---------------------------------------------------------


def test_shell_executes_exactly_the_prepared_receipt_image_and_journal() -> None:
    # Arrange
    candidate, governed = _fee_receipt_candidate_fixture()
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    expected_request = _expected_request(candidate, governed)
    verifier = _RecordingVerifier()

    # Act
    marker = shell.verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)

    # Assert: one call, exact request, marker minted from exactly those bytes and fields.
    assert verifier.calls == [expected_request]
    assert verifier.calls == [
        (prepared.receipt_bytes, prepared.expected_image_id, prepared.expected_journal_bytes)
    ]
    assert type(marker) is core.VerifiedZDEXFeeAllocationV1
    assert _marker_fields(marker) == _record_fields(prepared.verified_fields)
    assert marker.receipt_digest == _digest(verifier.calls[0][0])
    assert marker.expected_image_id == verifier.calls[0][1]
    assert marker.expected_image_id == governed._fields.module_release.guest_image_id
    assert marker.journal_digest == _digest(verifier.calls[0][2])
    assert marker.binding_root == _BINDING_ROOT_PIN
    with pytest.raises(AttributeError, match="immutable"):
        marker._fields = cast(Any, object())


def test_callback_exception_propagates_and_no_marker_is_returned() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    verifier = _RecordingVerifier(reject=True)
    outcome: object = None

    try:
        outcome = shell.verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)
    except ValueError as exc:
        assert str(exc) == "boundary verifier rejection"
    else:
        raise AssertionError("verifier rejection did not propagate")

    assert outcome is None
    assert verifier.calls == [_expected_request(candidate, governed)]


@pytest.mark.parametrize("result", (True, object(), b"ok", 0))
def test_reference_callback_non_none_return_is_still_ignored(result: object) -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    verifier = _RecordingVerifier(result=result)

    marker = shell.verify_zdex_fee_allocation_receipt_v1(candidate, governed, verifier)

    # Historical contract: the reference return value is not an admission condition.
    assert verifier.calls == [_expected_request(candidate, governed)]
    assert _marker_fields(marker) == _record_fields(_expected_fields(candidate, governed))
    assert marker.binding_root == _BINDING_ROOT_PIN


def test_candidate_and_prepared_alias_mutation_during_callback_cannot_relabel_marker() -> None:
    # Arrange: the caller keeps every alias the callback could reach.
    candidate, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    expected_fields = _record_fields(prepared.verified_fields)
    expected_request = (
        prepared.receipt_bytes,
        prepared.expected_image_id,
        prepared.expected_journal_bytes,
    )
    forged_fields = replace(
        prepared.verified_fields,
        module_release_id=_root(78_501),
        expected_image_id=_root(78_502),
        fee_ingress_atoms=78_503,
        receipt_digest=_digest(b"mutated-leaf"),
        journal_digest=_digest(b"mutated-journal"),
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
            object.__setattr__(prepared, "receipt_bytes", b"mutated-leaf")
            object.__setattr__(prepared, "expected_journal_bytes", b"mutated-journal")
            object.__setattr__(fields.module_release, "release_id", _root(78_501))
            object.__setattr__(fields.module_release, "guest_image_id", _root(78_502))
            object.__setattr__(candidate.pre_state, "fee_ingress_atoms", 78_503)
            object.__setattr__(candidate.journal.allocations[0], "allocation_atoms", 78_504)
            object.__setattr__(candidate.receipt, "receipt_bytes", b"mutated-leaf")
            object.__setattr__(candidate.receipt, "receipt_kind", ReceiptKindV1.FAKE)

    verifier = _MutatingVerifier()

    # Act: execute the caller-held prepared alias directly.
    marker = shell._execute_prepared_zdex_fee_allocation_receipt_v1(prepared, verifier)

    # Assert: the marker is the executed subject, not the mutated alias.
    assert verifier.calls == [expected_request]
    assert _marker_fields(marker) == expected_fields
    assert marker.binding_root == _BINDING_ROOT_PIN
    assert prepared.verified_fields == forged_fields
    # No public binding API accepts a separate execution-evidence label here.
    assert not any(name.startswith("bind_verified") for name in (*shell.__all__, *core.__all__))


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


def test_execute_before_prepare_mutant_is_killed_by_the_no_call_law() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    original = shell.verify_zdex_fee_allocation_receipt_v1
    target = "    prepared = prepare_zdex_fee_allocation_receipt_v1(candidate, governed)\n"
    mutant_body = (
        "    receipt_verifier.verify_succinct_receipt(\n"
        "        candidate.receipt.receipt_bytes,\n"
        "        expected_image_id=governed._fields.module_release.guest_image_id,\n"
        "        expected_journal_bytes=b'',\n"
        "    )\n"
        "    prepared = prepare_zdex_fee_allocation_receipt_v1(candidate, governed)\n"
    )
    mutant = _mutant(shell, original, target, mutant_body)
    tampered = replace(
        candidate, receipt=ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.CONDITIONAL, b"conditional")
    )

    # Control: the ordinary law holds on the unmutated shell.
    control_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        original(tampered, governed, control_verifier)
    assert control_verifier.calls == []

    # Mutant: the same rejection is raised, but the no-call assertion is reachable and fails.
    mutant_verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="requires a succinct receipt"):
        mutant(tampered, governed, mutant_verifier)  # type: ignore[operator]
    assert mutant_verifier.calls == [
        (b"conditional", governed._fields.module_release.guest_image_id, b"")
    ]
    with pytest.raises(AssertionError):
        assert mutant_verifier.calls == []


def test_mint_from_caller_alias_mutant_is_killed_by_the_alias_mutation_observation() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    original = shell._execute_prepared_zdex_fee_allocation_receipt_v1
    mutant = _mutant(
        shell,
        original,
        "    return _build_verified_zdex_fee_allocation_v1(owned)\n",
        "    return _build_verified_zdex_fee_allocation_v1(prepared)\n",
    )
    forged_id = _root(78_601)

    def _run(execute: Callable[..., core.VerifiedZDEXFeeAllocationV1]) -> str:
        prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
        forged = replace(prepared.verified_fields, module_release_id=forged_id)

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

        return execute(prepared, _MutatingVerifier()).module_release_id

    # Control: the unmutated shell reports the executed subject.
    assert _run(original) == governed._fields.module_release.release_id
    # Mutant: the caller alias relabels the marker, so the observation fails.
    assert _run(mutant) == forged_id  # type: ignore[arg-type]
    with pytest.raises(AssertionError):
        assert _run(mutant) == governed._fields.module_release.release_id  # type: ignore[arg-type]


def test_coordinator_image_mutant_is_killed_by_the_module_image_observation() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    fields = governed._fields
    original = core.prepare_zdex_fee_allocation_receipt_v1
    mutant = _mutant(
        core,
        original,
        "        fields.module_release.guest_image_id,\n",
        "        fields.coordinator_release.guest_image_id,\n",
    )
    assert fields.module_release.guest_image_id != fields.coordinator_release.guest_image_id

    # Control: the unmutated preparation requests the module image.
    control = original(candidate, governed)
    assert control.expected_image_id == fields.module_release.guest_image_id

    # Mutant: the prepared request names the coordinator image, so the observation fails
    # and a shell executing the mutant subject would ask the verifier for the wrong image.
    mutated = mutant(candidate, governed)  # type: ignore[operator]
    assert mutated.expected_image_id == fields.coordinator_release.guest_image_id
    with pytest.raises(AssertionError):
        assert mutated.expected_image_id == fields.module_release.guest_image_id
    verifier = _RecordingVerifier()
    marker = shell._execute_prepared_zdex_fee_allocation_receipt_v1(mutated, verifier)
    assert verifier.calls[0][1] == fields.coordinator_release.guest_image_id
    assert marker.binding_root != _BINDING_ROOT_PIN


def test_missing_field_to_request_binding_mutant_is_killed_by_the_digest_observation() -> None:
    candidate, governed = _fee_receipt_candidate_fixture()
    original = core.snapshot_prepared_zdex_fee_allocation_receipt_v1
    mutant = _mutant(
        core,
        original,
        "    _require_prepared_zdex_fee_allocation_digests_v1(prepared)\n",
        "    pass\n",
    )
    prepared = core.prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    inconsistent = replace(
        prepared,
        verified_fields=replace(prepared.verified_fields, receipt_digest=_digest(b"other")),
    )

    # Control: the unmutated snapshot refuses a record whose digest is unbound to its bytes.
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        original(inconsistent)
    # Mutant: the same record is accepted with its digest unbound from its bytes, so the
    # control rejection is unreachable and the shell would execute unbound bytes.
    accepted = mutant(inconsistent)  # type: ignore[operator]
    assert accepted == inconsistent
    assert accepted.verified_fields.receipt_digest != _digest(accepted.receipt_bytes)
    verifier = _RecordingVerifier()
    with pytest.raises(ValueError, match="receipt digest mismatch"):
        shell._execute_prepared_zdex_fee_allocation_receipt_v1(inconsistent, verifier)
    assert verifier.calls == []
