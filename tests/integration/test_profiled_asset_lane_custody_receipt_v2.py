"""Selected-role admission; receipt exchanges are protocol fixtures, not proofs."""

from __future__ import annotations

import inspect
from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_custody_guest_role_v2 import (
    ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2,
    ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2,
    ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2,
    ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2,
    AssetLaneCustodyGuestRoleBindingV2,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceArtifactV1,
    EconomicReceiptVerifierEvidenceManifestV1,
    economic_receipt_verifier_backend_protocol_root_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1,
)
from src.core.global_settlement_primitives_v2 import canonical_global_bytes_v2
from src.integration import global_receipt_verifier_v1 as receipt_transport
from src.integration import profiled_asset_lane_custody_receipt_v2 as admission
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
)
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _case,
    _receipt_exchange,
    _sign,
)
from tests.integration.test_global_receipt_verifier_v1 import IMAGE, OTHER_IMAGE, backend
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as protocol_case,
)


def _binding(case, artifact, **changes):
    manifest = EconomicReceiptVerifierEvidenceManifestV1(
        proof_system="risc0-succinct",
        implementation_root=economic_receipt_verifier_implementation_root_v1(artifact),
        receipt_schema_root=ASSET_LANE_CUSTODY_RECEIPT_SCHEMA_ROOT_V2,
        journal_schema_root=ASSET_LANE_CUSTODY_JOURNAL_SCHEMA_ROOT_V2,
        root_image_id=IMAGE,
        specification_root=ASSET_LANE_CUSTODY_GUEST_SPECIFICATION_ROOT_V2,
        source_root="0x" + "31" * 32,
        toolchain_root="0x" + "32" * 32,
        backend_protocol_root=economic_receipt_verifier_backend_protocol_root_v1(),
        max_receipt_bytes=16 * 1024 * 1024,
        max_journal_bytes=1024 * 1024,
        evidence_artifacts=tuple(
            EconomicReceiptVerifierEvidenceArtifactV1(status, "0x" + "33" * 32)
            for status in sorted(
                REQUIRED_SHADOW_ECONOMIC_RECEIPT_VERIFIER_EVIDENCE_V1,
                key=lambda item: item.value,
            )
        ),
    )
    return AssetLaneCustodyGuestRoleBindingV2(
        profile_root=case.candidate.profile.profile_id,
        authority_epoch=case.candidate.profile.authority_epoch,
        state_schema_root=ASSET_LANE_CUSTODY_STATE_SCHEMA_ROOT_V2,
        evidence_manifest=replace(manifest, **changes),
    )


def _run(case, signature_path, receipt_path, binding, **changes):
    options = {
        "guest_role_binding": binding,
        "expected_guest_role_binding_root": binding.binding_root,
        "receipt_executable_path": str(receipt_path),
        "receipt_timeout_ms": 5_000,
        "signature_artifact_path": signature_path,
        "signature_evidence_manifest": case.manifest,
        "signature_timeout_ms": 5_000,
        "receipt_bytes": _RECEIPT,
    }
    options.update(changes)
    return admission.verify_isolated_profiled_asset_lane_custody_receipt_v2(
        case.candidate, *case.inputs, **options
    )


@pytest.fixture
def receipt_artifact(tmp_path):
    path = tmp_path / "receipt-endpoint"
    path.write_bytes(b"\x7fELFisolated-selected-role-protocol-fixture")
    return path


@pytest.mark.parametrize("index", range(5))
def test_given_selected_custody_role_when_authenticated_then_exact_statement(
    protocol_case, receipt_artifact, monkeypatch, index
):
    _, signature_path, signatures = protocol_case
    case = _case(index)
    binding = _binding(case, receipt_artifact.read_bytes())
    profile_bytes = canonical_global_bytes_v2(case.candidate.profile.to_canonical())
    requests = _receipt_exchange(monkeypatch, case.expected)

    assert _run(case, signature_path, receipt_artifact, binding) == case.expected
    assert len(requests) == len(signatures) == 1
    assert canonical_global_bytes_v2(case.candidate.profile.to_canonical()) == profile_bytes


def test_unselected_self_consistent_role_rejects_before_signature_or_artifact_io(
    protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, signatures = protocol_case
    case = _case()
    original = _binding(case, receipt_artifact.read_bytes())
    foreign = _binding(case, receipt_artifact.read_bytes(), root_image_id=OTHER_IMAGE)
    monkeypatch.setattr(admission, "_acquire_artifact_v1", lambda _: pytest.fail("artifact IO"))

    with pytest.raises(ValueError, match="binding root"):
        _run(
            case,
            signature_path,
            receipt_artifact,
            foreign,
            expected_guest_role_binding_root=original.binding_root,
        )
    assert signatures == []


def test_raw_verifier_cannot_replace_selected_role_input(protocol_case, receipt_artifact):
    _, signature_path, signatures = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes())
    parameters = inspect.signature(
        admission.verify_isolated_profiled_asset_lane_custody_receipt_v2
    ).parameters
    assert "receipt_verifier" not in parameters
    with pytest.raises(TypeError, match="unexpected keyword argument"):
        _run(case, signature_path, receipt_artifact, binding, receipt_verifier=backend())
    assert signatures == []


def test_authenticated_rejection_needs_no_receipt_endpoint(protocol_case, tmp_path, monkeypatch):
    _, signature_path, signatures = protocol_case
    case = _case(amount=0)
    binding = _binding(case, b"\x7fELFnot-needed")
    monkeypatch.setattr(admission, "_acquire_artifact_v1", lambda _: pytest.fail("artifact IO"))

    rejected = _run(case, signature_path, tmp_path / "absent", binding, receipt_bytes=b"")
    assert type(rejected) is AssetLaneRejectedV2
    assert rejected == case.expected
    assert rejected.effects.is_empty
    assert len(signatures) == 1


@pytest.mark.parametrize("amount", [None, 0])
def test_bad_signature_precedes_economics_and_receipt_measurement(
    protocol_case, receipt_artifact, monkeypatch, amount
):
    _, signature_path, signatures = protocol_case
    case = _case(amount=amount)
    case = replace(case, candidate=_sign(case.candidate, scalar=18))
    binding = _binding(case, receipt_artifact.read_bytes())
    monkeypatch.setattr(admission, "_acquire_artifact_v1", lambda _: pytest.fail("artifact IO"))
    with pytest.raises(ValueError, match="signature rejected"):
        _run(case, signature_path, receipt_artifact, binding)
    assert len(signatures) == 1


@pytest.mark.parametrize("field,limit", [("max_receipt_bytes", 1), ("max_journal_bytes", 1)])
def test_selected_resource_ceiling_rejects_before_receipt_endpoint_io(
    protocol_case, receipt_artifact, monkeypatch, field, limit
):
    _, signature_path, signatures = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes(), **{field: limit})
    monkeypatch.setattr(admission, "_acquire_artifact_v1", lambda _: pytest.fail("artifact IO"))
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, receipt_artifact, binding)
    assert error.value.reason is GlobalReceiptVerifierRejectV1.INPUT_BOUNDS
    assert len(signatures) == 1


def test_endpoint_must_match_the_selected_implementation(
    protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes())
    receipt_artifact.write_bytes(b"\x7fELFsubstituted")
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, receipt_artifact, binding)
    assert error.value.reason is GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING
    assert requests == []


@pytest.mark.parametrize(
    "fault,reason",
    [
        ("proof_rejection", GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED),
        ("foreign_request", GlobalReceiptVerifierRejectV1.RESPONSE_BINDING),
        ("foreign_image", GlobalReceiptVerifierRejectV1.RESPONSE_BINDING),
    ],
)
def test_receipt_refusal_cannot_return_success_or_change_economic_inputs(
    protocol_case, receipt_artifact, monkeypatch, fault, reason
):
    _, signature_path, signatures = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes())
    before = canonical_global_bytes_v2([value.to_canonical() for value in case.inputs])
    requests = _receipt_exchange(monkeypatch, case.expected)
    exchange = receipt_transport._invoke_v1

    def refuse(descriptor, request, timeout_ms):
        response, _, _ = exchange(descriptor, request, timeout_ms)
        if fault == "proof_rejection":
            return b"", b"", 2
        if fault == "foreign_request":
            return response[:8] + b"\x00" * 32 + response[40:], b"", 0
        return response[:40] + bytes.fromhex(OTHER_IMAGE[2:]), b"", 0

    monkeypatch.setattr(receipt_transport, "_invoke_v1", refuse)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, receipt_artifact, binding)
    assert error.value.reason is reason
    assert len(signatures) == len(requests) == 1
    assert canonical_global_bytes_v2([value.to_canonical() for value in case.inputs]) == before


def test_replacement_after_measurement_is_rejected_by_sealed_transport(
    protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes())
    acquire = admission._acquire_artifact_v1

    def replace_after(path):
        raw = acquire(path)
        receipt_artifact.write_bytes(b"\x7fELFchanged-after-measurement")
        return raw

    monkeypatch.setattr(admission, "_acquire_artifact_v1", replace_after)
    requests = _receipt_exchange(monkeypatch, case.expected)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as error:
        _run(case, signature_path, receipt_artifact, binding)
    assert error.value.reason is GlobalReceiptVerifierRejectV1.EXECUTABLE_BINDING
    assert requests == []


@pytest.mark.parametrize("target", ["command", "global_post", "manifest"])
def test_caller_mutation_during_signature_io_cannot_change_verified_subject(
    protocol_case, receipt_artifact, monkeypatch, target
):
    _, signature_path, _ = protocol_case
    case = _case()
    binding = _binding(case, receipt_artifact.read_bytes())
    original = admission.verify_isolated_economic_command_occurrence_v2
    seen = []

    def mutate(candidate, occurrence, **kwargs):
        seen.append(candidate.envelope.command_body_bytes)
        if target == "command":
            object.__setattr__(case.inputs[2], "amount_atoms", 99)
        elif target == "global_post":
            object.__setattr__(case.inputs[4], "history_root", OTHER_IMAGE)
        else:
            object.__setattr__(binding.evidence_manifest, "root_image_id", OTHER_IMAGE)
        return original(candidate, occurrence, **kwargs)

    monkeypatch.setattr(admission, "verify_isolated_economic_command_occurrence_v2", mutate)
    requests = _receipt_exchange(monkeypatch, case.expected)
    selected_root = binding.binding_root
    assert (
        _run(
            case,
            signature_path,
            receipt_artifact,
            binding,
            expected_guest_role_binding_root=selected_root,
        )
        == case.expected
    )
    assert len(requests) == len(seen) == 1
