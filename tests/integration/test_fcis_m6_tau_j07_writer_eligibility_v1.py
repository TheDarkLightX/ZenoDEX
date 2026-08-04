"""Adversarial tests for the Tau-to-J07 writer eligibility refinement."""

from __future__ import annotations

import json
from hashlib import sha256

from experiments.fcis_m6_j07_authority_switch_check import (
    build_f06_token,
    build_gate,
)
from experiments.fcis_m6_tau_j07_writer_authority_check import (
    TAU_WRITER_VECTOR_PATH,
    build_tau_writer_authority_payload_v2,
)
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j06_quiescence import (
    J06QuiescenceGateV1,
    _mint_gate_v1,
    quiescence_root_from_body_v1,
)
from src.core.fcis_m6_j07_authority_switch import (
    J07SwitchSuccessV1,
    switch_authority_v1,
)
from src.core.fcis_m6_j07_writer_admission_v2 import (
    J07WriterAdmissionContextV2,
    J07WriterAdmissionRejectCodeV2,
    J07WriterAdmissionRejectV2,
    verify_j07_writer_admission_context_v2,
)
from src.core.fcis_m6_j07_writer_token_v3 import (
    J07WriterAcceptedV3,
    J07WriterTokenV3,
    authorize_writer_v3,
    issue_writer_token_v3,
)
from src.core.fcis_m6_tau_profile_v1 import (
    TauIntegrationObservationV1,
    TauIntegrationProfileV1,
    build_tau_integration_profile_v1,
)
from src.core.fcis_m6_writer_profile_eligibility_v1 import (
    WriterProfileEligibilityReceiptV1,
)
from src.integration.fcis_m6_tau_j07_writer_eligibility_v1 import (
    TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V1,
    TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2,
    TauJ07WriterEligibilityRejectCodeV1,
    TauJ07WriterEligibilityRejectV1,
    verify_tau_j07_writer_profile_eligibility_v1,
    verify_tau_j07_writer_profile_eligibility_v2,
)
from src.integration.fcis_m6_tau_profile_runtime_v1 import (
    TauIntegrationProfileReceiptV1,
    TauProfileVerificationContextV1,
    TauProfileVerificationEvidenceV1,
    TauWriterProfileBindingV1,
    bind_tau_profile_to_writer_target_v1,
    build_tau_profile_verification_context_v1,
    build_tau_profile_verification_evidence_v1,
    verify_tau_integration_profile_v1,
)


def _digest(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


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
        binary_sha256=_digest("tau-binary"),
        language_semantics_root=_digest("language-semantics"),
        governance_root=_digest("governance"),
        rule_history_root=_digest("rule-history"),
        capabilities=("compact_policy_relations_v1",),
        refinement_root=_digest("refinement"),
        resource_envelope_root=_digest("resource-envelope"),
        proof_format_root=_digest("proof-format"),
        asset_semantics_root=_digest("asset-semantics"),
        finality_semantics_root=_digest("finality-semantics"),
        rule_change_procedure_root=_digest("rule-change-procedure"),
    )


def _retarget_gate(
    gate: J06QuiescenceGateV1,
    target_profile_root: str,
) -> J06QuiescenceGateV1:
    body: dict[str, object] = {
        "manifest_root": gate.manifest_root,
        "entrypoint_inventory_root": gate.entrypoint_inventory_root,
        "phase": gate.phase.value,
        "activation_sequence": gate.activation_sequence,
        "authority_epoch_index": gate.authority_epoch_index,
        "authority_state_root": gate.authority_state_root,
        "legacy_profile_root": gate.legacy_profile_root,
        "target_profile_root": target_profile_root,
        "current_head_root": gate.current_head_root,
        "replay_head_root": gate.replay_head_root,
        "current_snapshot_root": gate.current_snapshot_root,
        "replay_snapshot_root": gate.replay_snapshot_root,
        "replay_evidence_root": gate.replay_evidence_root,
        "covered_writer_ids": list(gate.covered_writer_ids),
        "evidence_markers": list(gate.evidence_markers),
    }
    return _mint_gate_v1(
        manifest_root=gate.manifest_root,
        entrypoint_inventory_root=gate.entrypoint_inventory_root,
        phase=dra.MigrationPhaseV1.QUIESCED,
        activation_sequence=gate.activation_sequence,
        authority_epoch_index=gate.authority_epoch_index,
        authority_state_root=gate.authority_state_root,
        legacy_profile_root=gate.legacy_profile_root,
        target_profile_root=target_profile_root,
        current_head_root=gate.current_head_root,
        replay_head_root=gate.replay_head_root,
        current_snapshot_root=gate.current_snapshot_root,
        replay_snapshot_root=gate.replay_snapshot_root,
        replay_evidence_root=gate.replay_evidence_root,
        covered_writer_ids=gate.covered_writer_ids,
        evidence_markers=gate.evidence_markers,
        quiescence_root=quiescence_root_from_body_v1(body),
    )


def _switched(profile: TauIntegrationProfileV1) -> J07SwitchSuccessV1:
    reopened, genesis, migration_token, verifier = build_f06_token()
    gate = _retarget_gate(build_gate(migration_token), profile.writer_profile_root)
    result = switch_authority_v1(
        gate,
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    assert type(result) is J07SwitchSuccessV1
    return result


class _TauProfileVerifier:
    def verify_tau_integration_profile(
        self,
        *_args: object,
        **_kwargs: object,
    ) -> object:
        return True


class _EligibilityVerifier:
    def __init__(self, decision: object = True) -> None:
        self.decision = decision
        self.kwargs: dict[str, object] | None = None

    def verify_writer_profile_eligibility(
        self,
        _claim: object,
        **kwargs: object,
    ) -> object:
        self.kwargs = dict(kwargs)
        return self.decision


class _AdmissionVerifier:
    def verify_j07_writer_admission_context(self, **_kwargs: object) -> object:
        return True


def _profile_receipt(
    profile: TauIntegrationProfileV1,
    switched: J07SwitchSuccessV1,
    *,
    observation: TauIntegrationObservationV1 = TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
) -> TauIntegrationProfileReceiptV1:
    post = switched.post_context
    context: TauProfileVerificationContextV1 = build_tau_profile_verification_context_v1(
        deployment_id="zenodex/research-deployment",
        promotion_subject_root=_digest("promotion-subject"),
        current_state_root=post.current_state_root,
        deployment_config_root=post.deployment_config_root,
        authority_epoch=post.epoch_index,
        expected_profile_root=profile.profile_root,
        expected_governance_root=profile.governance_root,
        expected_rule_history_root=profile.rule_history_root,
        required_capabilities=("compact_policy_relations_v1",),
        expected_refinement_root=profile.refinement_root,
        verifier_profile_root=_digest("tau-profile-verifier"),
    )
    evidence: TauProfileVerificationEvidenceV1 = build_tau_profile_verification_evidence_v1(
        observation=observation,
        observed_profile_root=profile.profile_root,
        observed_governance_root=profile.governance_root,
        observed_rule_history_root=profile.rule_history_root,
        observed_capabilities=profile.capabilities,
        observed_refinement_root=profile.refinement_root,
        profile_proof_root=_digest("tau-profile-proof"),
        binding_context_root=context.context_root,
    )
    result = verify_tau_integration_profile_v1(
        profile=profile,
        context=context,
        evidence=evidence,
        verifier_adapter=_TauProfileVerifier(),
    )
    assert type(result) is TauIntegrationProfileReceiptV1
    return result


def _binding(
    receipt: TauIntegrationProfileReceiptV1,
    switched: J07SwitchSuccessV1,
) -> TauWriterProfileBindingV1:
    post = switched.post_context
    result = bind_tau_profile_to_writer_target_v1(
        profile_receipt=receipt,
        expected_writer_profile_root=post.target_profile_root,
        current_state_root=post.current_state_root,
        deployment_config_root=post.deployment_config_root,
        authority_epoch=post.epoch_index,
    )
    assert type(result) is TauWriterProfileBindingV1
    return result


def _sources() -> tuple[
    TauIntegrationProfileReceiptV1,
    TauWriterProfileBindingV1,
    J07SwitchSuccessV1,
]:
    profile = _profile()
    switched = _switched(profile)
    receipt = _profile_receipt(profile, switched)
    return receipt, _binding(receipt, switched), switched


def _admission(
    receipt: TauIntegrationProfileReceiptV1,
    switched: J07SwitchSuccessV1,
    *,
    promotion_subject_root: str | None = None,
    source_schema_root: str | None = None,
) -> J07WriterAdmissionContextV2:
    result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        promotion_subject_root=(promotion_subject_root or receipt.context.promotion_subject_root),
        source_schema_root=(source_schema_root or TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2),
        eligibility_policy_root=_digest("eligibility-policy"),
        eligibility_verifier_profile_root=_digest("eligibility-verifier"),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=_AdmissionVerifier(),
    )
    assert type(result) is J07WriterAdmissionContextV2
    return result


def test_tau_receipts_refine_to_eligibility_and_j07_authorization() -> None:
    receipt, binding, switched = _sources()
    verifier = _EligibilityVerifier()
    admission = _admission(receipt, switched)
    eligibility = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=binding,
        authority_context=switched.post_context,
        writer_admission_context=admission,
        verifier_adapter=verifier,
    )
    assert type(eligibility) is WriterProfileEligibilityReceiptV1
    assert eligibility.claim.promotion_subject_root == receipt.context.promotion_subject_root
    assert eligibility.claim.source_receipt_root == receipt.receipt_root
    assert eligibility.claim.source_binding_root == binding.binding_root
    assert verifier.kwargs is not None
    assert verifier.kwargs["expected_authority_context_root"] == (
        switched.post_context.context_root
    )

    token = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(token) is J07WriterTokenV3
    accepted = authorize_writer_v3(
        switched.post_context,
        admission,
        token,
        eligibility,
    )
    assert type(accepted) is J07WriterAcceptedV3
    assert accepted.promotion_subject_root == receipt.context.promotion_subject_root


def test_tau_j07_eligibility_has_a_frozen_canonical_identity_vector() -> None:
    receipt, binding, switched = _sources()
    admission = _admission(receipt, switched)
    eligibility = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=binding,
        authority_context=switched.post_context,
        writer_admission_context=admission,
        verifier_adapter=_EligibilityVerifier(),
    )
    assert type(eligibility) is WriterProfileEligibilityReceiptV1
    token = issue_writer_token_v3(switched.post_context, admission, eligibility)
    assert type(token) is J07WriterTokenV3
    assert build_tau_writer_authority_payload_v2() == json.loads(
        TAU_WRITER_VECTOR_PATH.read_text(encoding="utf-8")
    )
    assert TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V1 == (
        "931312071fb68f1bc102ba264e3a1f281b51ea64a5654c4ff02d04143d7d399a"
    )
    assert receipt.receipt_root == (
        "1519c5bf5336cd8f9e6731a76beffedaa6283b810f401fef8094442e85a291a1"
    )
    assert binding.binding_root == (
        "6968f4cf61abe60c4b95426907640a2a69d0f7877f354f34a537c4bf1b7be1ff"
    )
    assert TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2 == (
        "dbf4ce4860bf8c45f64f65708985cd9477a854d97268c617a8d2948570f0e7bc"
    )
    assert eligibility.claim.claim_root == (
        "bc550e5d4134bc2fe4dde31e84a650769e89efc0ac5a1a0a0b9591caa88c910f"
    )
    assert eligibility.receipt_root == (
        "f462b80e4557fcc33c15df19ae6149eb9b0a160b4f872335e485500da3ed9191"
    )
    assert admission.admission_context_root == (
        "e3f9c91512911fb81bd2cb4d2efe8a7904b473883230ffc003805a9d16ca0353"
    )
    assert token.token_root == ("e52dcd85a16d3899f57124a1beec8f2c6e263b4b66b435af150676208538ebd0")


def test_tau_eligibility_rejects_quiesced_or_crossed_j07_context() -> None:
    receipt, binding, switched = _sources()
    result = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=binding,
        authority_context=switched.pre_context,
        writer_admission_context=_admission(receipt, switched),
        verifier_adapter=_EligibilityVerifier(),
    )
    assert type(result) is TauJ07WriterEligibilityRejectV1
    assert result.code is TauJ07WriterEligibilityRejectCodeV1.J07_CONTEXT_MISMATCH


def test_tau_eligibility_rejects_unregistered_writer_binding() -> None:
    receipt, _binding_value, switched = _sources()
    result = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=object(),
        authority_context=switched.post_context,
        writer_admission_context=_admission(receipt, switched),
        verifier_adapter=_EligibilityVerifier(),
    )
    assert type(result) is TauJ07WriterEligibilityRejectV1
    assert result.code is TauJ07WriterEligibilityRejectCodeV1.WRITER_BINDING_REJECTED


def test_unusable_tau_profile_never_reaches_eligibility_verifier() -> None:
    profile = _profile()
    switched = _switched(profile)
    receipt = _profile_receipt(
        profile,
        switched,
        observation=TauIntegrationObservationV1.UNAVAILABLE,
    )
    verifier = _EligibilityVerifier()
    result = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=object(),
        authority_context=switched.post_context,
        writer_admission_context=_admission(receipt, switched),
        verifier_adapter=verifier,
    )
    assert type(result) is TauJ07WriterEligibilityRejectV1
    assert result.code is TauJ07WriterEligibilityRejectCodeV1.PROFILE_NOT_USABLE
    assert verifier.kwargs is None


def test_tau_eligibility_verifier_requires_exact_true() -> None:
    receipt, binding, switched = _sources()
    result = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=receipt,
        writer_binding=binding,
        authority_context=switched.post_context,
        writer_admission_context=_admission(receipt, switched),
        verifier_adapter=_EligibilityVerifier(1),
    )
    assert type(result) is TauJ07WriterEligibilityRejectV1
    assert result.code is TauJ07WriterEligibilityRejectCodeV1.ELIGIBILITY_REJECTED


def test_tau_eligibility_rejects_invalid_policy_before_receipt_issue() -> None:
    receipt, _binding_value, switched = _sources()
    result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        eligibility_policy_root=True,
        promotion_subject_root=receipt.context.promotion_subject_root,
        source_schema_root=TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2,
        eligibility_verifier_profile_root=_digest("eligibility-verifier"),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=_AdmissionVerifier(),
    )
    assert type(result) is J07WriterAdmissionRejectV2
    assert result.code is J07WriterAdmissionRejectCodeV2.INVALID_POLICY_CONTEXT


def test_tau_v1_refinement_is_closed_without_admission_context() -> None:
    receipt, binding, switched = _sources()
    result = verify_tau_j07_writer_profile_eligibility_v1(
        profile_receipt=receipt,
        writer_binding=binding,
        authority_context=switched.post_context,
        eligibility_policy_root=_digest("eligibility-policy"),
        verifier_profile_root=_digest("eligibility-verifier"),
        verifier_adapter=_EligibilityVerifier(),
    )
    assert type(result) is TauJ07WriterEligibilityRejectV1
    assert result.code is (TauJ07WriterEligibilityRejectCodeV1.WRITER_ADMISSION_CONTEXT_REQUIRED)


def test_tau_v2_rejects_crossed_promotion_or_source_schema_context() -> None:
    receipt, binding, switched = _sources()
    for admission in (
        _admission(
            receipt,
            switched,
            promotion_subject_root=_digest("foreign-promotion-subject"),
        ),
        _admission(
            receipt,
            switched,
            source_schema_root=_digest("foreign-source-schema"),
        ),
    ):
        verifier = _EligibilityVerifier()
        result = verify_tau_j07_writer_profile_eligibility_v2(
            profile_receipt=receipt,
            writer_binding=binding,
            authority_context=switched.post_context,
            writer_admission_context=admission,
            verifier_adapter=verifier,
        )
        assert type(result) is TauJ07WriterEligibilityRejectV1
        assert result.code is (
            TauJ07WriterEligibilityRejectCodeV1.WRITER_ADMISSION_CONTEXT_MISMATCH
        )
        assert verifier.kwargs is None
