"""Adversarial runtime-refinement tests for the M6 Tau profile boundary."""

from __future__ import annotations

import os
from dataclasses import replace
from hashlib import sha256
from pathlib import Path
from typing import cast

import pytest

from src.core.fcis_m6_tau_profile_v1 import (
    TauIntegrationObservationV1,
    TauIntegrationProfileV1,
    TauOperationClassV1,
    TauSubstrateDispositionV1,
    build_tau_integration_profile_v1,
)
from src.integration.fcis_m6_tau_profile_runtime_v1 import (
    TauDispositionContextV1,
    TauDispositionEvidenceV1,
    TauIntegrationProfileReceiptV1,
    TauProfileRuntimeRejectCodeV1,
    TauProfileRuntimeRejectV1,
    TauProfileVerificationContextV1,
    TauProfileVerificationEvidenceV1,
    TauSubstrateDispositionDecisionV1,
    TauWriterProfileBindingV1,
    bind_tau_profile_to_writer_target_v1,
    build_tau_disposition_context_v1,
    build_tau_disposition_evidence_v1,
    build_tau_profile_verification_context_v1,
    build_tau_profile_verification_evidence_v1,
    is_verified_tau_integration_profile_receipt_v1,
    is_verified_tau_substrate_disposition_v1,
    is_verified_tau_writer_profile_binding_v1,
    project_tau_profile_gate_inputs_v1,
    project_tau_substrate_disposition_inputs_v1,
    verify_tau_integration_profile_v1,
    verify_tau_substrate_disposition_v1,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps

ROOT = Path(__file__).resolve().parents[2]


def _digest(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


def _tau_bin() -> str:
    tau_bin = os.environ.get("TAU_BIN", "").strip() or find_tau_bin(ROOT)
    if not isinstance(tau_bin, str) or tau_bin == "":
        pytest.skip("Tau binary not available for runtime-refinement parity")
    return cast(str, tau_bin)


def _profile() -> TauIntegrationProfileV1:
    return build_tau_integration_profile_v1(
        network_id="tau-testnet-alpha",
        protocol_version="0.7.0-alpha",
        source_origin="https://github.com/IDNI/tau-lang",
        source_commit="c43c66b84966aac0e2830aa778dfda79b2857608",
        source_tree="01829511c6961cde5b6121bb1cf205f106de9203",
        parser_origin="https://github.com/IDNI/parser.git",
        parser_commit="ec62e2b78c342c9265876fc6edbadc82806ee493",
        version_output="Tau Language Framework version 0.7.0-alpha (c43c66b8)",
        binary_sha256="588ebf63dfbcf5101b30e02d149678143cbcb89e60e51e0aa8bed0f9d716b157",
        language_semantics_root=_digest("language-semantics"),
        governance_root=_digest("governance"),
        rule_history_root=_digest("rule-history"),
        capabilities=(
            "compact_policy_relations_v1",
            "direct_bv_stream_arithmetic_v1",
        ),
        refinement_root=_digest("refinement"),
        resource_envelope_root=_digest("resource-envelope"),
        proof_format_root=_digest("proof-format"),
        asset_semantics_root=_digest("asset-semantics"),
        finality_semantics_root=_digest("finality-semantics"),
        rule_change_procedure_root=_digest("rule-change-procedure"),
    )


def _profile_context(profile: TauIntegrationProfileV1) -> TauProfileVerificationContextV1:
    return build_tau_profile_verification_context_v1(
        deployment_id="zenodex/research-deployment",
        promotion_subject_root=_digest("promotion-subject"),
        current_state_root=_digest("current-state"),
        deployment_config_root=_digest("deployment-config"),
        authority_epoch=7,
        expected_profile_root=profile.profile_root,
        expected_governance_root=profile.governance_root,
        expected_rule_history_root=profile.rule_history_root,
        required_capabilities=("compact_policy_relations_v1",),
        expected_refinement_root=profile.refinement_root,
        verifier_profile_root=_digest("profile-verifier"),
    )


def _profile_evidence(
    profile: TauIntegrationProfileV1,
    context: TauProfileVerificationContextV1,
    *,
    observation: TauIntegrationObservationV1 = TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
) -> TauProfileVerificationEvidenceV1:
    return build_tau_profile_verification_evidence_v1(
        observation=observation,
        observed_profile_root=profile.profile_root,
        observed_governance_root=profile.governance_root,
        observed_rule_history_root=profile.rule_history_root,
        observed_capabilities=profile.capabilities,
        observed_refinement_root=profile.refinement_root,
        profile_proof_root=_digest("profile-proof"),
        binding_context_root=context.context_root,
    )


class _ProfileVerifier:
    def __init__(self, decision: object = True) -> None:
        self.decision = decision

    def verify_tau_integration_profile(self, *_args: object, **_kwargs: object) -> object:
        return self.decision


class _DispositionVerifier:
    def __init__(self, decision: object = True) -> None:
        self.decision = decision
        self.kwargs: dict[str, object] | None = None

    def verify_tau_substrate_disposition(self, *_args: object, **kwargs: object) -> object:
        self.kwargs = dict(kwargs)
        return self.decision


def _receipt(
    *,
    observation: TauIntegrationObservationV1 = TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
) -> TauIntegrationProfileReceiptV1:
    profile = _profile()
    context = _profile_context(profile)
    result = verify_tau_integration_profile_v1(
        profile=profile,
        context=context,
        evidence=_profile_evidence(profile, context, observation=observation),
        verifier_adapter=_ProfileVerifier(),
    )
    assert type(result) is TauIntegrationProfileReceiptV1
    return result


def _disposition_context(
    receipt: TauIntegrationProfileReceiptV1,
    *,
    portable: bool = False,
    safe_exit: bool = False,
) -> TauDispositionContextV1:
    return build_tau_disposition_context_v1(
        profile_receipt=receipt,
        expected_operation_root=_digest("operation"),
        last_adopted_semantics_root=_digest("adopted-semantics"),
        zeno_ledger_state_root=_digest("ledger-state"),
        expected_portable_certificate_root=(_digest("portable-certificate") if portable else None),
        expected_safe_exit_single_issuer_root=(
            _digest("safe-exit-single-issuer") if safe_exit else None
        ),
        verifier_profile_root=_digest("disposition-verifier"),
    )


def _disposition_evidence(
    context: TauDispositionContextV1,
    *,
    operation_class: TauOperationClassV1,
    proposed: TauSubstrateDispositionV1,
    operation_root: str | None = None,
) -> TauDispositionEvidenceV1:
    return build_tau_disposition_evidence_v1(
        operation_class=operation_class,
        proposed_disposition=proposed,
        operation_root=operation_root or context.expected_operation_root,
        portable_certificate_root=context.expected_portable_certificate_root,
        safe_exit_single_issuer_root=context.expected_safe_exit_single_issuer_root,
        observed_last_adopted_semantics_root=context.last_adopted_semantics_root,
        observed_zeno_ledger_state_root=context.zeno_ledger_state_root,
        request_proof_root=_digest("request-proof"),
        binding_context_root=context.context_root,
    )


def test_verified_profile_receipt_is_opaque_and_revalidated_at_use() -> None:
    receipt = _receipt()
    assert receipt.profile_usable
    assert is_verified_tau_integration_profile_receipt_v1(receipt)
    with pytest.raises(TypeError, match="profile verifier"):
        replace(receipt)
    object.__setattr__(receipt, "receipt_root", _digest("forged"))
    assert not is_verified_tau_integration_profile_receipt_v1(receipt)


def test_profile_receipt_has_a_frozen_canonical_identity_vector() -> None:
    receipt = _receipt()
    assert receipt.profile.capability_manifest_root == (
        "beea585af34115cc325964f1bd6f51cc206818b8099e6f649ded63f655904f53"
    )
    assert receipt.profile.profile_root == (
        "d96ca475d20343f5737a11f0f8b9f7edd5d18f38f02c338898f0423ec9f85290"
    )
    assert receipt.context.context_root == (
        "2969fb1f218340e08aa47e5548f040cd593814568ab580a25371b52bff4e9b21"
    )
    assert receipt.evidence.evidence_root == (
        "37f544fad3cb51afc205d3ea81d3452833a361e816ae8882154b97e720c2b402"
    )
    assert receipt.receipt_root == (
        "2872450cd3fa0433633b60a77579677c7ae2ff234abc2e66a2d790e3e2457742"
    )


def test_negative_observation_is_attested_without_becoming_usable() -> None:
    receipt = _receipt(observation=TauIntegrationObservationV1.UNAVAILABLE)
    assert not receipt.profile_usable
    assert is_verified_tau_integration_profile_receipt_v1(receipt)
    inputs = project_tau_profile_gate_inputs_v1(receipt)
    assert inputs["i1"] == 0
    assert inputs["i2"] == 1


def test_profile_verifier_requires_exact_true() -> None:
    profile = _profile()
    context = _profile_context(profile)
    result = verify_tau_integration_profile_v1(
        profile=profile,
        context=context,
        evidence=_profile_evidence(profile, context),
        verifier_adapter=_ProfileVerifier(1),
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.EXTERNAL_VERIFIER_REJECTED


def _profile_builder_values(profile: TauIntegrationProfileV1) -> dict[str, object]:
    return {
        name: (tuple(value) if name == "capabilities" else value)
        for name, value in profile.to_wire().items()
        if name not in {"schema", "profile_root", "capability_manifest_root"}
    }


@pytest.mark.parametrize(
    "mutation",
    (
        "profile_governance",
        "context_profile",
        "evidence_context",
        "evidence_capabilities",
        "evidence_refinement",
    ),
)
def test_profile_crossed_or_incomplete_fibers_fail_closed(mutation: str) -> None:
    profile = _profile()
    context = _profile_context(profile)
    evidence = _profile_evidence(profile, context)
    changed_profile = profile
    changed_context = context
    changed_evidence = evidence
    if mutation == "profile_governance":
        profile_values = _profile_builder_values(profile)
        profile_values["governance_root"] = _digest("foreign-governance")
        changed_profile = build_tau_integration_profile_v1(**profile_values)  # type: ignore[arg-type]
    elif mutation == "context_profile":
        changed_context = build_tau_profile_verification_context_v1(
            deployment_id=context.deployment_id,
            promotion_subject_root=context.promotion_subject_root,
            current_state_root=context.current_state_root,
            deployment_config_root=context.deployment_config_root,
            authority_epoch=context.authority_epoch,
            expected_profile_root=_digest("foreign-profile"),
            expected_governance_root=context.expected_governance_root,
            expected_rule_history_root=context.expected_rule_history_root,
            required_capabilities=context.required_capabilities,
            expected_refinement_root=context.expected_refinement_root,
            verifier_profile_root=context.verifier_profile_root,
        )
    else:
        evidence_values = {
            "observation": evidence.observation,
            "observed_profile_root": evidence.observed_profile_root,
            "observed_governance_root": evidence.observed_governance_root,
            "observed_rule_history_root": evidence.observed_rule_history_root,
            "observed_capabilities": evidence.observed_capabilities,
            "observed_refinement_root": evidence.observed_refinement_root,
            "profile_proof_root": evidence.profile_proof_root,
            "binding_context_root": evidence.binding_context_root,
        }
        if mutation == "evidence_context":
            evidence_values["binding_context_root"] = _digest("foreign-context")
        elif mutation == "evidence_capabilities":
            evidence_values["observed_capabilities"] = ()
        else:
            evidence_values["observed_refinement_root"] = _digest("foreign-refinement")
        changed_evidence = build_tau_profile_verification_evidence_v1(
            **evidence_values  # type: ignore[arg-type]
        )
    result = verify_tau_integration_profile_v1(
        profile=changed_profile,
        context=changed_context,
        evidence=changed_evidence,
        verifier_adapter=_ProfileVerifier(),
    )
    assert type(result) is TauProfileRuntimeRejectV1


def test_profile_capability_language_is_canonical_and_bool_epoch_is_rejected() -> None:
    profile = _profile()
    with pytest.raises(ValueError, match="canonical"):
        replace(profile, capabilities=tuple(reversed(profile.capabilities)))
    with pytest.raises(TypeError, match="authority_epoch"):
        build_tau_profile_verification_context_v1(
            deployment_id="zenodex/research-deployment",
            promotion_subject_root=_digest("promotion-subject"),
            current_state_root=_digest("current-state"),
            deployment_config_root=_digest("deployment-config"),
            authority_epoch=True,
            expected_profile_root=profile.profile_root,
            expected_governance_root=profile.governance_root,
            expected_rule_history_root=profile.rule_history_root,
            required_capabilities=("compact_policy_relations_v1",),
            expected_refinement_root=profile.refinement_root,
            verifier_profile_root=_digest("profile-verifier"),
        )


@pytest.mark.parametrize(
    ("observation", "operation_class", "proposed", "portable", "safe_exit", "authorized"),
    (
        (
            TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
            TauOperationClassV1.TAU_INDEPENDENT,
            TauSubstrateDispositionV1.USE_TAU,
            False,
            False,
            True,
        ),
        (
            TauIntegrationObservationV1.UNAVAILABLE,
            TauOperationClassV1.TAU_INDEPENDENT,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            False,
            False,
            True,
        ),
        (
            TauIntegrationObservationV1.UNAVAILABLE,
            TauOperationClassV1.TAU_DEPENDENT,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            True,
            False,
            True,
        ),
        (
            TauIntegrationObservationV1.CENSORING,
            TauOperationClassV1.TAU_NATIVE_ASSET,
            TauSubstrateDispositionV1.REJECT_OR_PEND,
            False,
            False,
            False,
        ),
        (
            TauIntegrationObservationV1.CENSORING,
            TauOperationClassV1.TAU_NATIVE_ASSET,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            False,
            True,
            True,
        ),
    ),
)
def test_disposition_relation_uses_only_receipt_derived_profile_status(
    observation: TauIntegrationObservationV1,
    operation_class: TauOperationClassV1,
    proposed: TauSubstrateDispositionV1,
    portable: bool,
    safe_exit: bool,
    authorized: bool,
) -> None:
    receipt = _receipt(observation=observation)
    context = _disposition_context(receipt, portable=portable, safe_exit=safe_exit)
    evidence = _disposition_evidence(
        context,
        operation_class=operation_class,
        proposed=proposed,
    )
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        verifier_adapter=_DispositionVerifier(),
    )
    assert type(result) is TauSubstrateDispositionDecisionV1
    assert result.authorizes_execution is authorized
    assert is_verified_tau_substrate_disposition_v1(result)


def test_unsafe_disposition_is_rejected_without_decision_or_effects() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_ZENO_LEDGER,
    )
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        verifier_adapter=_DispositionVerifier(),
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.DISPOSITION_REJECTED


def test_disposition_verifier_requires_exact_true() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_TAU,
    )
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        verifier_adapter=_DispositionVerifier(1),
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.EXTERNAL_VERIFIER_REJECTED


def test_crossed_profile_receipt_cannot_enter_disposition() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    foreign = _receipt(observation=TauIntegrationObservationV1.CHANGED)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_TAU,
    )
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=foreign,
        context=context,
        evidence=evidence,
        verifier_adapter=_DispositionVerifier(),
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH


def test_crossed_operation_root_cannot_enter_disposition() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_TAU,
        operation_root=_digest("foreign-operation"),
    )
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        verifier_adapter=_DispositionVerifier(),
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.CONTEXT_MISMATCH


def test_disposition_decision_is_opaque_and_profile_status_has_no_caller_field() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_TAU,
    )
    verifier = _DispositionVerifier()
    result = verify_tau_substrate_disposition_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        verifier_adapter=verifier,
    )
    assert type(result) is TauSubstrateDispositionDecisionV1
    assert verifier.kwargs is not None
    assert verifier.kwargs["expected_operation_root"] == context.expected_operation_root
    assert "profile_usable" not in TauDispositionEvidenceV1.__dataclass_fields__
    with pytest.raises(TypeError, match="disposition verifier"):
        replace(result)


def test_writer_target_binding_requires_same_usable_profile_and_current_context() -> None:
    receipt = _receipt()
    result = bind_tau_profile_to_writer_target_v1(
        profile_receipt=receipt,
        expected_writer_profile_root=receipt.profile.profile_root,
        current_state_root=receipt.context.current_state_root,
        deployment_config_root=receipt.context.deployment_config_root,
        authority_epoch=receipt.context.authority_epoch,
    )
    assert type(result) is TauWriterProfileBindingV1
    assert is_verified_tau_writer_profile_binding_v1(result)
    with pytest.raises(TypeError, match="writer-profile binder"):
        replace(result)


def test_unusable_or_stale_profile_cannot_bind_a_writer_target() -> None:
    unusable = _receipt(observation=TauIntegrationObservationV1.INCOMPATIBLE)
    result = bind_tau_profile_to_writer_target_v1(
        profile_receipt=unusable,
        expected_writer_profile_root=unusable.profile.profile_root,
        current_state_root=unusable.context.current_state_root,
        deployment_config_root=unusable.context.deployment_config_root,
        authority_epoch=unusable.context.authority_epoch,
    )
    assert type(result) is TauProfileRuntimeRejectV1
    assert result.code is TauProfileRuntimeRejectCodeV1.PROFILE_NOT_USABLE


def test_profile_root_changes_when_any_source_identity_changes() -> None:
    profile = _profile()
    values = _profile_builder_values(profile)
    values["source_commit"] = "d43c66b84966aac0e2830aa778dfda79b2857608"
    changed = build_tau_integration_profile_v1(**values)  # type: ignore[arg-type]
    assert changed.profile_root != profile.profile_root


def test_disposition_projection_has_exact_closed_tau_input_set() -> None:
    receipt = _receipt()
    context = _disposition_context(receipt)
    evidence = _disposition_evidence(
        context,
        operation_class=TauOperationClassV1.TAU_INDEPENDENT,
        proposed=TauSubstrateDispositionV1.USE_TAU,
    )
    inputs = project_tau_substrate_disposition_inputs_v1(
        profile_receipt=receipt,
        context=context,
        evidence=evidence,
        external_verifier_accepted=True,
    )
    assert tuple(inputs) == tuple(f"i{index}" for index in range(1, 15))
    assert all(type(value) is int and value in (0, 1) for value in inputs.values())


def test_profile_receipt_projection_matches_exact_tau_relation() -> None:
    receipts = (
        _receipt(),
        _receipt(observation=TauIntegrationObservationV1.UNAVAILABLE),
        _receipt(observation=TauIntegrationObservationV1.CHANGED),
    )
    inputs = [project_tau_profile_gate_inputs_v1(receipt) for receipt in receipts]
    outputs = run_tau_spec_steps(
        _tau_bin(),
        ROOT / "src/tau_specs/recommended/m6_tau_substrate_profile_gate_v1.tau",
        inputs,
        timeout_s=30.0,
    )
    assert [outputs[index]["o1"] == 1 for index in range(len(receipts))] == [
        receipt.profile_usable for receipt in receipts
    ]


def test_disposition_decision_projection_matches_exact_tau_relation() -> None:
    cases = (
        (
            TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
            TauOperationClassV1.TAU_INDEPENDENT,
            TauSubstrateDispositionV1.USE_TAU,
            False,
            False,
        ),
        (
            TauIntegrationObservationV1.UNAVAILABLE,
            TauOperationClassV1.TAU_INDEPENDENT,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            False,
            False,
        ),
        (
            TauIntegrationObservationV1.UNAVAILABLE,
            TauOperationClassV1.TAU_DEPENDENT,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            True,
            False,
        ),
        (
            TauIntegrationObservationV1.CENSORING,
            TauOperationClassV1.TAU_NATIVE_ASSET,
            TauSubstrateDispositionV1.REJECT_OR_PEND,
            False,
            False,
        ),
        (
            TauIntegrationObservationV1.CENSORING,
            TauOperationClassV1.TAU_NATIVE_ASSET,
            TauSubstrateDispositionV1.USE_ZENO_LEDGER,
            False,
            True,
        ),
    )
    inputs: list[dict[str, int]] = []
    expected: list[tuple[int, int]] = []
    for observation, operation_class, proposed, portable, safe_exit in cases:
        receipt = _receipt(observation=observation)
        context = _disposition_context(receipt, portable=portable, safe_exit=safe_exit)
        evidence = _disposition_evidence(
            context,
            operation_class=operation_class,
            proposed=proposed,
        )
        projected = project_tau_substrate_disposition_inputs_v1(
            profile_receipt=receipt,
            context=context,
            evidence=evidence,
            external_verifier_accepted=True,
        )
        runtime = verify_tau_substrate_disposition_v1(
            profile_receipt=receipt,
            context=context,
            evidence=evidence,
            verifier_adapter=_DispositionVerifier(),
        )
        assert type(runtime) is TauSubstrateDispositionDecisionV1
        inputs.append(projected)
        expected.append((1, int(runtime.authorizes_execution)))
    outputs = run_tau_spec_steps(
        _tau_bin(),
        ROOT / "src/tau_specs/recommended/m6_substrate_disposition_gate_v1.tau",
        inputs,
        timeout_s=60.0,
    )
    assert [(outputs[index]["o1"], outputs[index]["o2"]) for index in range(len(cases))] == (
        expected
    )
