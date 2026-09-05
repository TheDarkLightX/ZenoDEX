"""Real BLS controls with explicitly synthetic RISC0 process replies.

The measured-port factory/transport and all deterministic core joins run here.
This is no new genuine proof qualification: the retained e7faba profile pins a
test signature registry and requires new proofs when its signer policy changes.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, fields, replace
from pathlib import Path

from py_ecc.bls import G2Basic

import tests.core.test_global_settlement_abi_v1 as abi_fixtures
from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as abi
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_transfer_lane_module_v1 import transition_asset_transfer_lane_module_v1
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1,
    EconomicCommandAuthenticationEnvelopeV1,
    EconomicCommandIntentV1,
)
from src.core.economic_command_authentication_v1 import (
    _isolated_economic_command_authentication_message_bytes_v1,
)
from src.core.economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationRegistryV1,
    EconomicCommandAuthorizationV1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1,
    EconomicCommandSignatureVerifierRegistryV1,
    EconomicCommandSignatureVerifierReleaseV1,
)
from src.core.economic_receipt_verifier_registry_v1 import EconomicReceiptVerifierRegistryV1
from src.core.route_composition_receipt_verification_v1 import (
    derive_route_composition_assumption_root_v1,
)
from src.integration import economic_command_bls_signature_verifier_v1 as bls
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from tests.core.test_asset_transfer_global_allocation_v1 import _global_allocation_fixture
from tests.core.test_economic_command_authentication_v1 import (
    _signature_verifier_manifest,
    _signature_verifier_release,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _release
from tests.core.test_global_settlement_abi_v1 import (
    _asset_lane_context,
    _asset_module_input_for_occurrence,
    _asset_transfer_policy_registry_for_route_v1,
    _epoch_admission_fixture,
    _epoch_asset_module_state,
    _epoch_candidate,
    _governed_policy_registry_for_profile_v1,
)

_SECRET = 25  # Public deterministic test scalar only.


@dataclass
class _Fixture:
    candidate: proof.EconomicEpochReceiptCandidateV1
    raw: pipeline.RawAssetTransferReceiptEvidenceV1
    policy: abi.EconomicPolicyRegistryV1
    signature_manifest: object
    signature_release: object
    expected: tuple
    calls: list
    fail_at: str | None = None
    on_call: object = None

    def verify_succinct_receipt(self, receipt, *, expected_image_id, expected_journal_bytes):
        row = (receipt, expected_image_id, expected_journal_bytes)
        self.calls.append(row)
        if self.on_call is not None:
            self.on_call()
        name = receipt.decode()
        if name == self.fail_at:
            raise RuntimeError(f"synthetic {name} verifier unavailable")
        if row not in self.expected:
            raise ValueError("synthetic receipt statement rejected")


def _fixture(owner, *, pre_state=None, nonce_start=1):
    base, route, _, _, _, pre, _ = _global_allocation_fixture()
    # Retiring the unrelated lane releases changes the exact endpoint set.
    owner.template = owner.artifacts(base, None)
    artifact = Path(bls.__file__)
    sig_manifest = replace(
        _signature_verifier_manifest(artifact_bytes=artifact.read_bytes()),
        max_public_key_bytes=98,
        max_signature_bytes=96,
    )
    sig_release = _signature_verifier_release(sig_manifest)
    # These deterministic evidence roots are synthetic test labels. The isolated
    # selection uses only the five required labels and never claims production.
    sig_manifest = replace(
        sig_manifest,
        evidence_artifacts=tuple(
            row
            for row in sig_manifest.evidence_artifacts
            if row.status in REQUIRED_ISOLATED_COMMAND_SIGNATURE_VERIFIER_EVIDENCE_V1
        ),
    )
    release_fields = {
        field.name: getattr(sig_release, field.name)
        for field in fields(sig_release)
        if field.name != "release_id"
    }
    release_fields.update(
        evidence_manifest_root=sig_manifest.manifest_root,
        evidence_statuses=tuple(row.status for row in sig_manifest.evidence_artifacts),
        status=abi.ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
    )
    sig_release = EconomicCommandSignatureVerifierReleaseV1.build(**release_fields)
    signatures = EconomicCommandSignatureVerifierRegistryV1((sig_release,))
    original_occurrence = abi_fixtures._occurrence(base, route, pre)
    authorization = EconomicCommandAuthorizationV1(
        "asset_transfer",
        "alice",
        original_occurrence.grant_root,
        route.route_release_id,
        "alice-key-1",
        "0x" + G2Basic.SkToPk(_SECRET).hex(),
        "BLS12_381_G2_BASIC_V1",
        0,
        10,
        0,
        10,
        True,
    )
    authorizations = EconomicCommandAuthorizationRegistryV1((authorization,))
    bindings = _governed_policy_registry_for_profile_v1(base).bindings
    new_roots = {
        "command_authentication_registry": authorizations.registry_root,
        "command_signature_verifier_registry": signatures.registry_root,
    }
    policy = abi.EconomicPolicyRegistryV1(
        tuple(
            replace(row, policy_root=new_roots.get(row.policy_kind, row.policy_root))
            for row in bindings
        )
    )
    profile_fields = {f.name: getattr(base, f.name) for f in fields(base) if f.name != "profile_id"}
    profile_fields.update(
        policy_registry_root=policy.registry_root,
        verifier_registry_root=EconomicReceiptVerifierRegistryV1(
            (_release(owner.manifest()),)
        ).registry_root,
    )
    profile = abi.EconomicProfileSnapshotV1.build(**profile_fields)
    pre = replace(pre, profile_root=profile.profile_id) if pre_state is None else pre_state
    if pre.profile_root != profile.profile_id:
        raise ValueError("pipeline fixture predecessor profile mismatch")
    occurrence = replace(abi_fixtures._occurrence(profile, route, pre), nonce=nonce_start)
    module_state = replace(
        _epoch_asset_module_state(profile),
        balances=pre.balances,
        supplies=pre.supplies,
    )
    module_input = _asset_module_input_for_occurrence(
        profile,
        occurrence,
        module_state,
    )
    accepted = transition_asset_transfer_lane_module_v1(module_input)
    lane = compose_asset_lane_single_v1(
        _asset_lane_context(profile, occurrence, module_input, accepted),
        accepted.module_journal,
        accepted.private_port,
        accepted.effects,
    )
    projected = accepted.private_port.post_state
    post = replace(
        pre,
        height=pre.height + 1,
        balances=projected.balances,
        supplies=projected.supplies,
        lane_roots=(
            replace(pre.lane_roots[0], state_root=projected.state_root),
            *pre.lane_roots[1:],
        ),
        replay_state=tuple(
            sorted(
                (
                    *pre.replay_state,
                    abi.ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id),
                )
            )
        ),
    )
    journal = proof.RouteCompositionJournalV1(
        pre.chain_id,
        pre.deployment_root,
        profile.profile_id,
        pre.writer_epoch,
        route.route_release_id,
        occurrence.occurrence_id,
        (lane.lane_journal.journal_root,),
        pre.state_root,
        post.state_root,
        lane.effects.effect_plan_root,
        lane.lane_journal.terminal_obligations_root,
    )
    assumption = derive_route_composition_assumption_root_v1(
        profile_id=profile.profile_id,
        route_release_id=route.route_release_id,
        command_occurrence_id=occurrence.occurrence_id,
        writer_epoch=pre.writer_epoch,
        route_journal_root=journal.journal_root,
        route_journal_digest="0x"
        + hashlib.sha256(abi.canonical_global_bytes_v1(journal)).hexdigest(),
        expected_image_id=route.guest_image_id,
    )
    template = _epoch_admission_fixture(1)
    certificate = replace(
        template.certificate,
        profile_root=profile.profile_id,
        height=post.height,
        pre_state_root=pre.state_root,
        post_state_root=post.state_root,
        ordered_occurrence_ids=(occurrence.occurrence_id,),
        ordered_route_journal_roots=(journal.journal_root,),
        ordered_route_assumption_roots=(assumption,),
        effect_plan_root=lane.effects.effect_plan_root,
        root_image_id=profile.root_image_id,
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    candidate = _epoch_candidate(
        profile,
        certificate,
        pre,
        post,
        (occurrence,),
        (journal,),
        (proof.EconomicEpochRouteStateDisclosureV1((lane.lane_journal,), post),),
        (),
        (lane.effects,),
        lane.effects,
        template.receipt_bytes,
    )
    intent = EconomicCommandIntentV1(
        occurrence.chain_id,
        occurrence.deployment_root,
        profile.profile_id,
        occurrence.command_kind,
        occurrence.command_body_hash,
        occurrence.route_release_id,
        occurrence.subject_id,
        occurrence.grant_root,
        occurrence.nonce,
        occurrence.consumed_object_ids,
        0,
        10,
    )
    envelope = EconomicCommandAuthenticationEnvelopeV1(
        abi.canonical_economic_command_body_bytes_v1("asset_transfer", module_input.command),
        authorization.signer_key_id,
        authorization.signer_public_key,
        authorization.signature_algorithm,
        b"x",
    )
    message = _isolated_economic_command_authentication_message_bytes_v1(
        EconomicCommandAuthenticationCandidateV1(
            profile, policy, authorizations, signatures, intent, envelope
        ),
        authorization,
    )
    envelope = replace(envelope, signature_bytes=G2Basic.Sign(_SECRET, message))
    raw = pipeline.RawAssetTransferReceiptEvidenceV1(
        intent,
        envelope,
        authorizations,
        signatures,
        _asset_transfer_policy_registry_for_route_v1(route),
        module_input,
        b"module",
        b"coordinator",
        b"route",
    )
    expected = tuple(
        (receipt, image, abi.canonical_global_bytes_v1(value))
        for receipt, image, value in (
            (
                b"module",
                profile.lane_registry.release_for(abi.LaneIdV1.ASSET_TRANSFER).guest_image_id,
                accepted.module_journal,
            ),
            (
                b"coordinator",
                profile.lane_coordinator_registry.release_for(
                    abi.LaneIdV1.ASSET_TRANSFER
                ).guest_image_id,
                lane.lane_journal,
            ),
            (b"route", route.guest_image_id, journal),
        )
    )
    return _Fixture(candidate, raw, policy, sig_manifest, sig_release, expected, [])
