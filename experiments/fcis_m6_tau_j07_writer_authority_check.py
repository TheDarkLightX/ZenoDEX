"""Independent Tau-profile-to-J07 V2/V3 checker and vector builder."""

from __future__ import annotations

import json
from hashlib import sha256
from pathlib import Path

from experiments.fcis_m6_j07_authority_switch_check import build_f06_token, build_gate
from src.core.fcis_m6_j07_authority_switch import (
    J07SwitchSuccessV1,
    switch_authority_v1,
)
from src.core.fcis_m6_j07_writer_admission_v2 import (
    J07WriterAdmissionContextV2,
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
    TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2,
    verify_tau_j07_writer_profile_eligibility_v2,
)
from src.integration.fcis_m6_tau_profile_runtime_v1 import (
    TauIntegrationProfileReceiptV1,
    TauWriterProfileBindingV1,
    bind_tau_profile_to_writer_target_v1,
    build_tau_profile_verification_context_v1,
    build_tau_profile_verification_evidence_v1,
    verify_tau_integration_profile_v1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
TAU_WRITER_VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_J07_TAU_WRITER_AUTHORITY_V2.json"


def _digest(label: str) -> str:
    return sha256(label.encode("ascii")).hexdigest()


class _AcceptingTauProfileVerifier:
    """Deterministic experiment adapter with no production authority."""

    def verify_tau_integration_profile(
        self,
        *_args: object,
        **_kwargs: object,
    ) -> object:
        return True


class _AcceptingWriterAdmissionVerifier:
    """Deterministic experiment adapter with no production authority."""

    def verify_j07_writer_admission_context(self, **_kwargs: object) -> object:
        return True


class _AcceptingWriterEligibilityVerifier:
    """Deterministic experiment adapter with no production authority."""

    def verify_writer_profile_eligibility(
        self,
        _claim: object,
        **_kwargs: object,
    ) -> object:
        return True


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


def _switched(profile: TauIntegrationProfileV1) -> J07SwitchSuccessV1:
    reopened, genesis, migration_token, verifier = build_f06_token()
    result = switch_authority_v1(
        build_gate(
            migration_token,
            target_profile_root=profile.writer_profile_root,
        ),
        reopened,
        genesis=genesis,
        migration_token=migration_token,
        verifier_adapter=verifier,
        current_epoch=3,
    )
    if type(result) is not J07SwitchSuccessV1:
        raise AssertionError("Tau J07 fixture did not switch")
    return result


def _verified_tau_sources(
    profile: TauIntegrationProfileV1,
    switched: J07SwitchSuccessV1,
) -> tuple[TauIntegrationProfileReceiptV1, TauWriterProfileBindingV1]:
    post = switched.post_context
    context = build_tau_profile_verification_context_v1(
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
    evidence = build_tau_profile_verification_evidence_v1(
        observation=TauIntegrationObservationV1.VERIFIED_COMPATIBLE,
        observed_profile_root=profile.profile_root,
        observed_governance_root=profile.governance_root,
        observed_rule_history_root=profile.rule_history_root,
        observed_capabilities=profile.capabilities,
        observed_refinement_root=profile.refinement_root,
        profile_proof_root=_digest("tau-profile-proof"),
        binding_context_root=context.context_root,
    )
    receipt = verify_tau_integration_profile_v1(
        profile=profile,
        context=context,
        evidence=evidence,
        verifier_adapter=_AcceptingTauProfileVerifier(),
    )
    if type(receipt) is not TauIntegrationProfileReceiptV1:
        raise AssertionError("Tau profile fixture did not verify")
    binding = bind_tau_profile_to_writer_target_v1(
        profile_receipt=receipt,
        expected_writer_profile_root=post.target_profile_root,
        current_state_root=post.current_state_root,
        deployment_config_root=post.deployment_config_root,
        authority_epoch=post.epoch_index,
    )
    if type(binding) is not TauWriterProfileBindingV1:
        raise AssertionError("Tau writer binding fixture did not verify")
    return receipt, binding


def _admission(
    receipt: TauIntegrationProfileReceiptV1,
    switched: J07SwitchSuccessV1,
) -> J07WriterAdmissionContextV2:
    result = verify_j07_writer_admission_context_v2(
        authority_context=switched.post_context,
        promotion_subject_root=receipt.context.promotion_subject_root,
        source_schema_root=TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2,
        eligibility_policy_root=_digest("eligibility-policy"),
        eligibility_verifier_profile_root=_digest("eligibility-verifier"),
        verification_evidence_root=_digest("writer-admission-evidence"),
        verifier_adapter=_AcceptingWriterAdmissionVerifier(),
    )
    if type(result) is not J07WriterAdmissionContextV2:
        raise AssertionError("Tau writer-admission fixture did not verify")
    return result


def build_tau_writer_authority_payload_v2() -> dict[str, object]:
    """Build the exact Tau-profile-to-J07 V2/V3 canonical vector."""

    profile = _profile()
    switched = _switched(profile)
    post = switched.post_context
    profile_receipt, writer_binding = _verified_tau_sources(profile, switched)
    admission = _admission(profile_receipt, switched)
    eligibility = verify_tau_j07_writer_profile_eligibility_v2(
        profile_receipt=profile_receipt,
        writer_binding=writer_binding,
        authority_context=post,
        writer_admission_context=admission,
        verifier_adapter=_AcceptingWriterEligibilityVerifier(),
    )
    if type(eligibility) is not WriterProfileEligibilityReceiptV1:
        raise AssertionError("Tau J07 writer eligibility fixture did not verify")
    token = issue_writer_token_v3(post, admission, eligibility)
    if type(token) is not J07WriterTokenV3:
        raise AssertionError("Tau J07 writer token fixture did not issue")
    accepted = authorize_writer_v3(post, admission, token, eligibility)
    if type(accepted) is not J07WriterAcceptedV3:
        raise AssertionError("Tau J07 writer token fixture was not accepted")
    return {
        "schema": "zenodex/fcis/m6/j07/tau-writer-authority-vector/v2",
        "profile_id": "research-unmounted-tau-j07-writer-authority",
        "tau_profile_root": profile.profile_root,
        "tau_profile_receipt_root": profile_receipt.receipt_root,
        "tau_writer_binding_root": writer_binding.binding_root,
        "source_schema_root": TAU_J07_WRITER_ELIGIBILITY_SOURCE_SCHEMA_ROOT_V2,
        "authority_context_root": post.context_root,
        "writer_admission_context_root": admission.admission_context_root,
        "eligibility_claim_root": eligibility.claim.claim_root,
        "eligibility_receipt_root": eligibility.receipt_root,
        "writer_profile_root": eligibility.claim.writer_profile_root,
        "writer_token_root": token.token_root,
        "accepted_authority_state_root": accepted.authority_state_root,
        "accepted_head_root": accepted.head_root,
        "accepted_snapshot_root": accepted.snapshot_root,
    }


def run_checks() -> dict[str, object]:
    payload = build_tau_writer_authority_payload_v2()
    expected = json.loads(TAU_WRITER_VECTOR_PATH.read_text(encoding="utf-8"))
    if canonical_json_bytes(payload) != canonical_json_bytes(expected):
        raise SystemExit("FAIL: J07 Tau writer-authority vector is stale")
    return payload


if __name__ == "__main__":
    result = run_checks()
    print("J07_TAU_WRITER_AUTHORITY_MATCH", result["writer_token_root"])
