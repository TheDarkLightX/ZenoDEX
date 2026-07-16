"""Bind one candidate-bound Spot V7 Firecracker result to a locked release.

The Linux runner returns a private, process-local result only after its root
supervisor contract has checked the request-bound output and completed cgroup
and network-namespace teardown.  The result still carries no release
selection.  This module reparses the selected release, binds every retained
runtime and supervisor identity, and keeps that join inside the same SQLite
write transaction as the later atomic consumer.

The resulting value proves a bounded release-to-runtime identity join.  Python
module privacy does not resist hostile code in the same interpreter, and this
join is not external execution attestation.  It performs no database write and
mints no runtime, release, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import json
import sqlite3
import struct
from dataclasses import dataclass
from typing import Any, NoReturn, SupportsIndex, cast, final

from src.integration import _zrpf_spot_v7_release_bound_finality_v1 as finality_v1
from src.integration import _zrpf_spot_v7_release_bound_proof_v1 as proof_v1
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_firecracker_linux_runner as linux_runner
from tools import zrpf_spot_v7_firecracker_root_supervisor as supervisor_v1
from tools import zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 as policy_v1
from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_manifest_v1
from tools import zrpf_spot_v7_firecracker_runtime_protocol as protocol_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1
from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    DecodedSpotV7FirecrackerAuthorityInputManifestV1,
    SpotV7FirecrackerAuthorityInputRejectV1,
    decode_exact_authority_input_manifest_v1,
)
from tools.zrpf_spot_v7_verifier_payload_codec import (
    StructurallyDecodedSpotV7VerifierPayloadV1,
)


class SpotV7ReleaseBoundFirecrackerRejectV1(ValueError):
    """Stable fail-closed rejection at the release-to-runtime join."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@dataclass(frozen=True, slots=True)
class _FirecrackerJoinInputsV1:
    execution: linux_runner.CandidateBoundSpotV7RootSupervisorRunV1
    proof: proof_v1._ReleaseBoundSpotV7SemanticProofV1
    finality: finality_v1._ReleaseBoundSpotV7CheckpointFinalityV1
    exact_execution_authority_manifest_bytes: bytes
    exact_runtime_manifest_bytes: bytes
    exact_machine_config_bytes: bytes
    exact_runtime_artifact_manifest_bytes: bytes
    exact_root_supervisor_contract_bytes: bytes
    exact_root_supervisor_executable_bytes: bytes
    exact_firecracker_profile_bytes: bytes
    exact_authority_input_profile_bytes: bytes
    exact_request_bytes: bytes
    exact_settlement_intent_bytes: bytes


@dataclass(frozen=True, slots=True)
class _CheckedFirecrackerReleaseBindingsV1:
    release_candidate_id: bytes
    release_candidate_sha256: bytes
    release_revision: int
    evidence_inventory_root: bytes
    candidate_bound_identity_sha256: bytes
    runtime_manifest_sha256: bytes
    runtime_artifact_manifest_sha256: bytes
    artifact_set_id: bytes
    machine_config_sha256: bytes
    runtime_profile_sha256: bytes
    authority_input_profile_sha256: bytes
    firecracker_profile_sha256: bytes
    root_supervisor_contract_sha256: bytes
    root_supervisor_executable_sha256: bytes
    netns_helper_sha256: bytes
    firecracker_executable_sha256: bytes
    jailer_executable_sha256: bytes
    guest_init_executable_sha256: bytes
    kernel_sha256: bytes
    rootfs_sha256: bytes
    input_drive_sha256: bytes
    request_sha256: bytes
    run_nonce_256: bytes
    settlement_intent_sha256: bytes
    output_payload_sha256: bytes
    proof_receipt_sha256: bytes
    proof_guest_input_sha256: bytes
    proof_source_v6_receipt_sha256: bytes
    proof_journal_sha256: bytes
    proof_plan_b_sha256: bytes
    settlement_effect_plan_commitment: bytes
    pre_state_root: bytes
    post_state_root: bytes
    finality_epoch_id: int
    prior_checkpoint_sequence: int
    prior_checkpoint_hash: bytes
    next_checkpoint_sequence: int
    next_checkpoint_hash: bytes
    prepare_observation_sha256: bytes
    launch_observation_sha256: bytes
    finish_observation_sha256: bytes
    v7_image_id: tuple[int, ...]
    v6_image_id: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _CheckedProofFinalityBindingsV1:
    proof_receipt_sha256: bytes
    proof_guest_input_sha256: bytes
    proof_source_v6_receipt_sha256: bytes
    proof_journal_sha256: bytes
    proof_plan_b_sha256: bytes
    settlement_effect_plan_commitment: bytes
    pre_state_root: bytes
    post_state_root: bytes
    finality_epoch_id: int
    prior_checkpoint_sequence: int
    prior_checkpoint_hash: bytes
    next_checkpoint_sequence: int
    next_checkpoint_hash: bytes


class _ReleaseBoundFirecrackerSealV1:
    __slots__ = ()


_RELEASE_BOUND_FIRECRACKER_SEAL_V1 = _ReleaseBoundFirecrackerSealV1()


@final
class _ReleaseBoundSpotV7FirecrackerExecutionV1:
    """Non-transferable, authority-false runtime result for one locked release."""

    __slots__ = ("_checked", "_identity", "_inputs", "_release", "_seal")

    _checked: _CheckedFirecrackerReleaseBindingsV1
    _identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3
    _inputs: _FirecrackerJoinInputsV1
    _release: release_v7._TransactionBoundSpotV7CurrentReleaseV7
    _seal: _ReleaseBoundFirecrackerSealV1

    def __new__(cls) -> _ReleaseBoundSpotV7FirecrackerExecutionV1:
        raise TypeError("release-bound Firecracker execution requires verified construction")

    @classmethod
    def _from_verified_join(
        cls,
        *,
        identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
        release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
        inputs: _FirecrackerJoinInputsV1,
        checked: _CheckedFirecrackerReleaseBindingsV1,
        seal: _ReleaseBoundFirecrackerSealV1,
    ) -> _ReleaseBoundSpotV7FirecrackerExecutionV1:
        if seal is not _RELEASE_BOUND_FIRECRACKER_SEAL_V1:
            raise TypeError("release-bound Firecracker execution requires the private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "_identity", identity)
        object.__setattr__(value, "_release", release)
        object.__setattr__(value, "_inputs", inputs)
        object.__setattr__(value, "_checked", checked)
        object.__setattr__(value, "_seal", seal)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-bound Firecracker execution cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-bound Firecracker execution is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-bound Firecracker execution is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-bound Firecracker execution cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-bound Firecracker execution cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-bound Firecracker execution cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-bound Firecracker execution cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _RELEASE_BOUND_FIRECRACKER_SEAL_V1

    @property
    def release_candidate_id(self) -> bytes:
        return self._checked.release_candidate_id

    @property
    def release_candidate_sha256(self) -> bytes:
        return self._checked.release_candidate_sha256

    @property
    def release_revision(self) -> int:
        return self._checked.release_revision

    @property
    def evidence_inventory_root(self) -> bytes:
        return self._checked.evidence_inventory_root

    @property
    def candidate_bound_identity_sha256(self) -> bytes:
        return self._checked.candidate_bound_identity_sha256

    @property
    def runtime_manifest_sha256(self) -> bytes:
        return self._checked.runtime_manifest_sha256

    @property
    def runtime_artifact_manifest_sha256(self) -> bytes:
        return self._checked.runtime_artifact_manifest_sha256

    @property
    def artifact_set_id(self) -> bytes:
        return self._checked.artifact_set_id

    @property
    def machine_config_sha256(self) -> bytes:
        return self._checked.machine_config_sha256

    @property
    def runtime_profile_sha256(self) -> bytes:
        return self._checked.runtime_profile_sha256

    @property
    def authority_input_profile_sha256(self) -> bytes:
        return self._checked.authority_input_profile_sha256

    @property
    def firecracker_profile_sha256(self) -> bytes:
        return self._checked.firecracker_profile_sha256

    @property
    def root_supervisor_contract_sha256(self) -> bytes:
        return self._checked.root_supervisor_contract_sha256

    @property
    def root_supervisor_executable_sha256(self) -> bytes:
        return self._checked.root_supervisor_executable_sha256

    @property
    def netns_helper_sha256(self) -> bytes:
        return self._checked.netns_helper_sha256

    @property
    def firecracker_executable_sha256(self) -> bytes:
        return self._checked.firecracker_executable_sha256

    @property
    def jailer_executable_sha256(self) -> bytes:
        return self._checked.jailer_executable_sha256

    @property
    def guest_init_executable_sha256(self) -> bytes:
        return self._checked.guest_init_executable_sha256

    @property
    def kernel_sha256(self) -> bytes:
        return self._checked.kernel_sha256

    @property
    def rootfs_sha256(self) -> bytes:
        return self._checked.rootfs_sha256

    @property
    def input_drive_sha256(self) -> bytes:
        return self._checked.input_drive_sha256

    @property
    def request_sha256(self) -> bytes:
        return self._checked.request_sha256

    @property
    def run_nonce_256(self) -> bytes:
        return self._checked.run_nonce_256

    @property
    def settlement_intent_sha256(self) -> bytes:
        return self._checked.settlement_intent_sha256

    @property
    def output_payload_sha256(self) -> bytes:
        return self._checked.output_payload_sha256

    @property
    def proof_receipt_sha256(self) -> bytes:
        return self._checked.proof_receipt_sha256

    @property
    def proof_guest_input_sha256(self) -> bytes:
        return self._checked.proof_guest_input_sha256

    @property
    def proof_source_v6_receipt_sha256(self) -> bytes:
        return self._checked.proof_source_v6_receipt_sha256

    @property
    def proof_journal_sha256(self) -> bytes:
        return self._checked.proof_journal_sha256

    @property
    def proof_plan_b_sha256(self) -> bytes:
        return self._checked.proof_plan_b_sha256

    @property
    def settlement_effect_plan_commitment(self) -> bytes:
        return self._checked.settlement_effect_plan_commitment

    @property
    def pre_state_root(self) -> bytes:
        return self._checked.pre_state_root

    @property
    def post_state_root(self) -> bytes:
        return self._checked.post_state_root

    @property
    def finality_epoch_id(self) -> int:
        return self._checked.finality_epoch_id

    @property
    def prior_checkpoint_sequence(self) -> int:
        return self._checked.prior_checkpoint_sequence

    @property
    def prior_checkpoint_hash(self) -> bytes:
        return self._checked.prior_checkpoint_hash

    @property
    def next_checkpoint_sequence(self) -> int:
        return self._checked.next_checkpoint_sequence

    @property
    def next_checkpoint_hash(self) -> bytes:
        return self._checked.next_checkpoint_hash

    @property
    def prepare_observation_sha256(self) -> bytes:
        return self._checked.prepare_observation_sha256

    @property
    def launch_observation_sha256(self) -> bytes:
        return self._checked.launch_observation_sha256

    @property
    def finish_observation_sha256(self) -> bytes:
        return self._checked.finish_observation_sha256

    @property
    def v7_image_id(self) -> tuple[int, ...]:
        return self._checked.v7_image_id

    @property
    def v6_image_id(self) -> tuple[int, ...]:
        return self._checked.v6_image_id

    @property
    def release_governed_runtime_identities_verified(self) -> bool:
        return True

    @property
    def candidate_bound_supervisor_result_verified(self) -> bool:
        return True

    @property
    def output_payload_structurally_verified(self) -> bool:
        return True

    @property
    def proof_runtime_payload_binding_verified(self) -> bool:
        return True

    @property
    def checkpoint_post_state_binding_verified(self) -> bool:
        return True

    @property
    def sandbox_authority(self) -> bool:
        return False

    @property
    def full_output_device_identity_retained(self) -> bool:
        return False

    @property
    def root_supervisor_executable_execution_attested(self) -> bool:
        return False

    @property
    def external_execution_attestation_authenticated(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _bind_release_locked_spot_v7_firecracker_execution_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    execution: linux_runner.CandidateBoundSpotV7RootSupervisorRunV1,
    proof: proof_v1._ReleaseBoundSpotV7SemanticProofV1,
    finality: finality_v1._ReleaseBoundSpotV7CheckpointFinalityV1,
    exact_execution_authority_manifest_bytes: bytes,
    exact_runtime_manifest_bytes: bytes,
    exact_machine_config_bytes: bytes,
    exact_runtime_artifact_manifest_bytes: bytes,
    exact_root_supervisor_contract_bytes: bytes,
    exact_root_supervisor_executable_bytes: bytes,
    exact_firecracker_profile_bytes: bytes,
    exact_authority_input_profile_bytes: bytes,
    exact_request_bytes: bytes,
    exact_settlement_intent_bytes: bytes,
) -> _ReleaseBoundSpotV7FirecrackerExecutionV1:
    """Bind one exact process-local supervisor result without consuming release."""

    if type(release) is not release_v7._TransactionBoundSpotV7CurrentReleaseV7:
        raise TypeError("Firecracker join requires the exact transaction-bound release")
    if type(identity) is not store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3:
        raise TypeError("Firecracker join requires the exact release-store identity")
    inputs = _FirecrackerJoinInputsV1(
        execution=execution,
        proof=proof,
        finality=finality,
        exact_execution_authority_manifest_bytes=(exact_execution_authority_manifest_bytes),
        exact_runtime_manifest_bytes=exact_runtime_manifest_bytes,
        exact_machine_config_bytes=exact_machine_config_bytes,
        exact_runtime_artifact_manifest_bytes=(exact_runtime_artifact_manifest_bytes),
        exact_root_supervisor_contract_bytes=exact_root_supervisor_contract_bytes,
        exact_root_supervisor_executable_bytes=exact_root_supervisor_executable_bytes,
        exact_firecracker_profile_bytes=exact_firecracker_profile_bytes,
        exact_authority_input_profile_bytes=exact_authority_input_profile_bytes,
        exact_request_bytes=exact_request_bytes,
        exact_settlement_intent_bytes=exact_settlement_intent_bytes,
    )
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    _require_same_release_capabilities_v1(
        connection,
        identity=identity,
        release=release,
        proof=proof,
        finality=finality,
    )
    checked = _check_firecracker_release_bindings_v1(release, inputs)
    _require_same_release_capabilities_v1(
        connection,
        identity=identity,
        release=release,
        proof=proof,
        finality=finality,
    )
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    return _ReleaseBoundSpotV7FirecrackerExecutionV1._from_verified_join(
        identity=identity,
        release=release,
        inputs=inputs,
        checked=checked,
        seal=_RELEASE_BOUND_FIRECRACKER_SEAL_V1,
    )


def _require_release_bound_firecracker_still_locked_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    execution: _ReleaseBoundSpotV7FirecrackerExecutionV1,
) -> _ReleaseBoundSpotV7FirecrackerExecutionV1:
    """Recheck release currentness and every retained runtime identity."""

    if type(execution) is not _ReleaseBoundSpotV7FirecrackerExecutionV1:
        raise TypeError("atomic join requires the exact release-bound Firecracker type")
    if not execution._has_private_seal():
        raise TypeError("release-bound Firecracker execution lacks its private seal")
    if identity != execution._identity:
        raise ValueError("release-bound Firecracker execution retained another identity")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=execution._release,
    )
    _require_same_release_capabilities_v1(
        connection,
        identity=identity,
        release=execution._release,
        proof=execution._inputs.proof,
        finality=execution._inputs.finality,
    )
    fresh = _check_firecracker_release_bindings_v1(
        execution._release,
        execution._inputs,
    )
    if fresh != execution._checked:
        raise _reject("RETAINED_BINDING_DRIFT", "retained runtime bindings changed")
    return execution


def _require_same_release_capabilities_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    proof: proof_v1._ReleaseBoundSpotV7SemanticProofV1,
    finality: finality_v1._ReleaseBoundSpotV7CheckpointFinalityV1,
) -> None:
    if type(proof) is not proof_v1._ReleaseBoundSpotV7SemanticProofV1:
        raise TypeError("Firecracker join requires the exact release-bound proof")
    if type(finality) is not finality_v1._ReleaseBoundSpotV7CheckpointFinalityV1:
        raise TypeError("Firecracker join requires the exact release-bound finality")
    if proof._release is not release or finality._release is not release:
        raise _reject(
            "RELEASE_CAPABILITY_BINDING",
            "proof and finality must retain the exact same locked release",
        )
    proof_v1._require_release_bound_proof_still_locked_v1(
        connection,
        identity=identity,
        proof=proof,
    )
    finality_v1._require_release_bound_finality_still_locked_v1(
        connection,
        identity=identity,
        finality=finality,
    )
    expected = (
        release.current_candidate_id,
        release.current_candidate_sha256,
        release.current_release_revision,
    )
    if (
        proof.release_candidate_id,
        proof.release_candidate_sha256,
        proof.release_revision,
    ) != expected or (
        finality.release_candidate_id,
        finality.release_candidate_sha256,
        finality.release_revision,
    ) != expected:
        raise _reject(
            "RELEASE_CAPABILITY_BINDING",
            "proof or finality release identity differs",
        )


def _check_firecracker_release_bindings_v1(
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    inputs: _FirecrackerJoinInputsV1,
) -> _CheckedFirecrackerReleaseBindingsV1:
    candidate, document = _checked_release_candidate(release)
    manifest = _checked_execution_manifest(release, inputs)
    runtime = _checked_runtime_manifest(inputs)
    inventory = _candidate_inventory(document)
    _bind_exact_release_artifacts(inventory, runtime, inputs)
    prepared_policy = _checked_supervisor_policy(release, inputs)
    completed = _checked_candidate_execution(
        candidate=candidate,
        execution=inputs.execution,
        runtime=runtime,
        prepared_policy=prepared_policy,
    )
    request, intent, payload = _checked_request_intent_and_output(
        inputs=inputs,
        runtime=runtime,
        completed=completed,
    )
    semantic = _checked_proof_finality_bindings_v1(
        release=release,
        inputs=inputs,
        runtime=runtime,
        intent=intent,
        payload=payload,
    )
    artifacts = manifest.execution_manifest._artifacts
    _bind_authority_artifacts(
        artifacts=artifacts,
        runtime=runtime,
        prepared_policy=prepared_policy,
        inputs=inputs,
    )
    roles = {row.role: row.sha256 for row in runtime.artifacts}
    return _CheckedFirecrackerReleaseBindingsV1(
        release_candidate_id=release.current_candidate_id,
        release_candidate_sha256=release.current_candidate_sha256,
        release_revision=release.current_release_revision,
        evidence_inventory_root=candidate.evidence_inventory_root,
        candidate_bound_identity_sha256=inputs.execution.candidate_bound_identity_sha256,
        runtime_manifest_sha256=hashlib.sha256(inputs.exact_runtime_manifest_bytes).digest(),
        runtime_artifact_manifest_sha256=hashlib.sha256(
            inputs.exact_runtime_artifact_manifest_bytes
        ).digest(),
        artifact_set_id=runtime.artifact_set_id,
        machine_config_sha256=runtime.machine_config_sha256,
        runtime_profile_sha256=runtime.runtime_profile_sha256,
        authority_input_profile_sha256=runtime.authority_input_profile_sha256,
        firecracker_profile_sha256=prepared_policy.firecracker_profile_sha256,
        root_supervisor_contract_sha256=prepared_policy.contract_sha256,
        root_supervisor_executable_sha256=hashlib.sha256(
            inputs.exact_root_supervisor_executable_bytes
        ).digest(),
        netns_helper_sha256=bytes.fromhex(prepared_policy.netns_helper_sha256),
        firecracker_executable_sha256=roles["firecracker"],
        jailer_executable_sha256=roles["jailer"],
        guest_init_executable_sha256=roles["guest_init"],
        kernel_sha256=roles["kernel"],
        rootfs_sha256=roles["rootfs"],
        input_drive_sha256=roles["input"],
        request_sha256=request.sha256,
        run_nonce_256=request.run_nonce_256,
        settlement_intent_sha256=intent.sha256,
        output_payload_sha256=payload.payload_sha256,
        proof_receipt_sha256=semantic.proof_receipt_sha256,
        proof_guest_input_sha256=semantic.proof_guest_input_sha256,
        proof_source_v6_receipt_sha256=semantic.proof_source_v6_receipt_sha256,
        proof_journal_sha256=semantic.proof_journal_sha256,
        proof_plan_b_sha256=semantic.proof_plan_b_sha256,
        settlement_effect_plan_commitment=(semantic.settlement_effect_plan_commitment),
        pre_state_root=semantic.pre_state_root,
        post_state_root=semantic.post_state_root,
        finality_epoch_id=semantic.finality_epoch_id,
        prior_checkpoint_sequence=semantic.prior_checkpoint_sequence,
        prior_checkpoint_hash=semantic.prior_checkpoint_hash,
        next_checkpoint_sequence=semantic.next_checkpoint_sequence,
        next_checkpoint_hash=semantic.next_checkpoint_hash,
        prepare_observation_sha256=completed.prepare_observation_sha256,
        launch_observation_sha256=completed.launch_observation_sha256,
        finish_observation_sha256=completed.finish_observation_sha256,
        v7_image_id=runtime.v7_image_id,
        v6_image_id=runtime.v6_image_id,
    )


def _checked_proof_finality_bindings_v1(
    *,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    inputs: _FirecrackerJoinInputsV1,
    runtime: runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    intent: DecodedSpotV7FirecrackerAuthorityInputManifestV1,
    payload: StructurallyDecodedSpotV7VerifierPayloadV1,
) -> _CheckedProofFinalityBindingsV1:
    proof = inputs.proof
    finality = inputs.finality
    observation = proof._observation
    if (
        proof._release is not release
        or finality._release is not release
        or proof.exact_execution_authority_manifest_bytes
        != inputs.exact_execution_authority_manifest_bytes
        or finality._exact_execution_authority_manifest_bytes
        != inputs.exact_execution_authority_manifest_bytes
    ):
        raise _reject(
            "RELEASE_CAPABILITY_BINDING",
            "proof, finality, and runtime do not share one release authority manifest",
        )

    proof_receipt_sha256 = hashlib.sha256(proof.exact_v7_receipt_bytes).digest()
    proof_guest_input_sha256 = hashlib.sha256(observation.exact_guest_input_bytes).digest()
    proof_source_v6_receipt_sha256 = hashlib.sha256(
        observation.exact_source_v6_receipt_bytes
    ).digest()
    expected_intent = (
        len(proof.exact_v7_receipt_bytes),
        proof_receipt_sha256,
        len(observation.exact_guest_input_bytes),
        proof_guest_input_sha256,
        len(observation.exact_source_v6_receipt_bytes),
        proof_source_v6_receipt_sha256,
    )
    observed_intent = (
        intent.v7_receipt_length,
        intent.v7_receipt_sha256,
        intent.guest_input_length,
        intent.guest_input_sha256,
        intent.v6_receipt_length,
        intent.v6_receipt_sha256,
    )
    if observed_intent != expected_intent:
        raise _reject(
            "PROOF_INTENT_BINDING",
            "authority input does not bind the release-governed proof artifacts",
        )

    if (
        payload.raw_bytes != observation.exact_verifier_output_bytes
        or payload.journal_bytes != proof.exact_v7_journal_bytes
        or payload.plan_b_bytes != proof.exact_plan_b_bytes
    ):
        raise _reject(
            "PROOF_OUTPUT_BINDING",
            "Firecracker output differs from the authenticated proof output",
        )

    proof_journal_sha256 = hashlib.sha256(proof.exact_v7_journal_bytes).digest()
    proof_plan_b_sha256 = hashlib.sha256(proof.exact_plan_b_bytes).digest()
    pre_state_root = _canonical_hex_digest(observation.pre_state_root, "pre-state root")
    post_state_root = _canonical_hex_digest(observation.post_state_root, "post-state root")
    expected_output = (
        struct.pack("<8I", *runtime.v7_image_id),
        struct.pack("<8I", *runtime.v6_image_id),
        proof_journal_sha256,
        proof.settlement_effect_plan_commitment,
        proof_plan_b_sha256,
        pre_state_root,
        post_state_root,
    )
    observed_output = (
        payload.fixed_fields[0],
        payload.fixed_fields[4],
        payload.fixed_fields[3],
        payload.fixed_fields[10],
        payload.fixed_fields[11],
        payload.fixed_fields[12],
        payload.fixed_fields[13],
    )
    if observed_output != expected_output:
        raise _reject(
            "PROOF_OUTPUT_ROOT_BINDING",
            "Firecracker output identities or proof roots differ",
        )
    if (
        finality.epoch_id != observation.epoch_id
        or finality.proof_journal_hash != proof_journal_sha256
        or finality.post_state_root != post_state_root
    ):
        raise _reject(
            "CHECKPOINT_PROOF_BINDING",
            "finalized checkpoint does not bind the proof journal and post-state",
        )
    return _CheckedProofFinalityBindingsV1(
        proof_receipt_sha256=proof_receipt_sha256,
        proof_guest_input_sha256=proof_guest_input_sha256,
        proof_source_v6_receipt_sha256=proof_source_v6_receipt_sha256,
        proof_journal_sha256=proof_journal_sha256,
        proof_plan_b_sha256=proof_plan_b_sha256,
        settlement_effect_plan_commitment=proof.settlement_effect_plan_commitment,
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        finality_epoch_id=finality.epoch_id,
        prior_checkpoint_sequence=finality.prior_checkpoint_sequence,
        prior_checkpoint_hash=finality.prior_checkpoint_hash,
        next_checkpoint_sequence=finality.next_checkpoint_sequence,
        next_checkpoint_hash=finality.next_checkpoint_hash,
    )


def _checked_release_candidate(
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
) -> tuple[candidate_v1.SpotV7ReleaseCandidateManifestV1, dict[str, Any]]:
    try:
        candidate = candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(
            release.current_candidate_bytes
        )
        document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    except (TypeError, ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise _reject("RELEASE_CANDIDATE", "selected candidate did not reparse") from exc
    observed = (
        candidate.candidate_id,
        hashlib.sha256(candidate.canonical_bytes).digest(),
        candidate.release_revision,
    )
    expected = (
        release.current_candidate_id,
        release.current_candidate_sha256,
        release.current_release_revision,
    )
    if observed != expected:
        raise _reject("RELEASE_CANDIDATE_BINDING", "selected candidate identity differs")
    return candidate, document


def _checked_execution_manifest(
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    inputs: _FirecrackerJoinInputsV1,
) -> authority_v1.CheckedSpotV7ExecutionAuthorityManifestV1:
    try:
        checked = authority_v1.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=release.current_candidate_bytes,
            exact_authority_manifest_bytes=(inputs.exact_execution_authority_manifest_bytes),
        )
    except (TypeError, ValueError) as exc:
        raise _reject(
            "EXECUTION_AUTHORITY_MANIFEST",
            "execution authority manifest differs from selected release",
        ) from exc
    if (
        checked.candidate_id,
        checked.candidate_manifest_sha256,
        checked.release_revision,
    ) != (
        release.current_candidate_id,
        release.current_candidate_sha256,
        release.current_release_revision,
    ):
        raise _reject("EXECUTION_AUTHORITY_BINDING", "authority release identity differs")
    return checked


def _checked_runtime_manifest(
    inputs: _FirecrackerJoinInputsV1,
) -> runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1:
    _require_bytes(inputs.exact_runtime_manifest_bytes, "runtime manifest")
    _require_bytes(inputs.exact_machine_config_bytes, "machine config")
    try:
        return runtime_manifest_v1.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            inputs.exact_runtime_manifest_bytes,
            exact_machine_config_bytes=inputs.exact_machine_config_bytes,
        )
    except (TypeError, ValueError) as exc:
        raise _reject("RUNTIME_MANIFEST", "runtime manifest or machine config rejected") from exc


def _candidate_inventory(document: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = cast(list[dict[str, Any]], document["evidence_inventory"])
    return {cast(str, row["role"]): row for row in rows}


def _bind_exact_release_artifacts(
    inventory: dict[str, dict[str, Any]],
    runtime: runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    inputs: _FirecrackerJoinInputsV1,
) -> None:
    artifacts = (
        ("runtime_manifest", inputs.exact_runtime_manifest_bytes),
        ("machine_config", inputs.exact_machine_config_bytes),
        ("runtime_artifact_manifest", inputs.exact_runtime_artifact_manifest_bytes),
        ("root_supervisor_contract", inputs.exact_root_supervisor_contract_bytes),
        ("root_supervisor_executable", inputs.exact_root_supervisor_executable_bytes),
        ("firecracker_profile", inputs.exact_firecracker_profile_bytes),
        ("authority_input_profile", inputs.exact_authority_input_profile_bytes),
    )
    for role, raw in artifacts:
        _require_inventory_artifact(inventory, role=role, raw=raw)
    if (
        inputs.exact_authority_input_profile_bytes
        != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
    ):
        raise _reject("AUTHORITY_INPUT_PROFILE", "authority-input profile bytes differ")
    runtime_artifact_document = _canonical_json_document(
        inputs.exact_runtime_artifact_manifest_bytes,
        code="RUNTIME_ARTIFACT_MANIFEST",
    )
    if (
        runtime_artifact_document.get("schema")
        != authority_v1.RUNTIME_ARTIFACT_MANIFEST_SCHEMA_V2
        or runtime_artifact_document.get("artifact_set_id")
        != runtime.artifact_set_id.hex()
    ):
        raise _reject(
            "RUNTIME_ARTIFACT_MANIFEST",
            "runtime artifact manifest does not name the selected artifact set",
        )
    firecracker_profile = _canonical_json_document(
        inputs.exact_firecracker_profile_bytes,
        code="FIRECRACKER_PROFILE",
    )
    if firecracker_profile.get("schema") != authority_v1.FIRECRACKER_REPLAY_PROFILE_SCHEMA_V1:
        raise _reject("FIRECRACKER_PROFILE", "Firecracker profile schema differs")


def _require_inventory_artifact(
    inventory: dict[str, dict[str, Any]],
    *,
    role: str,
    raw: bytes,
) -> None:
    _require_bytes(raw, role)
    row = inventory.get(role)
    if row is None or row.get("size_bytes") != len(raw):
        raise _reject("RELEASE_ARTIFACT_SIZE", f"{role} size differs from release")
    if row.get("artifact_sha256") != hashlib.sha256(raw).hexdigest():
        raise _reject("RELEASE_ARTIFACT_DIGEST", f"{role} digest differs from release")


def _checked_supervisor_policy(
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    inputs: _FirecrackerJoinInputsV1,
) -> policy_v1.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    try:
        return policy_v1.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=(inputs.exact_root_supervisor_contract_bytes),
            exact_release_candidate_bytes=release.current_candidate_bytes,
            expected_candidate_id=release.current_candidate_id,
        )
    except (TypeError, ValueError) as exc:
        raise _reject(
            "ROOT_SUPERVISOR_CONTRACT",
            "root supervisor contract differs from selected release",
        ) from exc


def _checked_candidate_execution(
    *,
    candidate: candidate_v1.SpotV7ReleaseCandidateManifestV1,
    execution: linux_runner.CandidateBoundSpotV7RootSupervisorRunV1,
    runtime: runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    prepared_policy: policy_v1.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1,
) -> supervisor_v1.CompletedSpotV7RootSupervisorRunV1:
    if (
        type(execution) is not linux_runner.CandidateBoundSpotV7RootSupervisorRunV1
        or getattr(execution, "_seal", None)
        is not linux_runner._CANDIDATE_BOUND_RESULT_SEAL_V1
    ):
        raise TypeError("Firecracker join requires the exact sealed candidate-bound result")
    completed = execution.completed_run
    if (
        type(completed) is not supervisor_v1.CompletedSpotV7RootSupervisorRunV1
        or getattr(completed, "_seal", None) is not supervisor_v1._COMPLETED_SUPERVISOR_SEAL_V1
    ):
        raise TypeError("Firecracker join requires the exact sealed supervisor result")
    expected = (
        candidate.candidate_id,
        hashlib.sha256(candidate.canonical_bytes).digest(),
        candidate.evidence_inventory_root,
        prepared_policy.contract_sha256,
        hashlib.sha256(runtime.canonical_bytes).digest(),
        runtime.artifact_set_id,
        runtime.machine_config_sha256,
        runtime.authority_input_profile_sha256,
        prepared_policy.firecracker_profile_sha256,
        bytes.fromhex(prepared_policy.netns_helper_sha256),
    )
    observed = (
        execution.candidate_id,
        execution.candidate_manifest_sha256,
        execution.evidence_inventory_root,
        execution.contract_sha256,
        execution.runtime_manifest_sha256,
        execution.artifact_set_id,
        execution.machine_config_sha256,
        execution.authority_input_profile_sha256,
        execution.firecracker_profile_sha256,
        execution.netns_helper_sha256,
    )
    if observed != expected:
        raise _reject("EXECUTION_RESULT_BINDING", "candidate-bound result identity differs")
    jail_id = completed.network_namespace_path.name
    expected_cgroup = f"/{prepared_policy.cgroup_parent_relative_path}/{jail_id}"
    expected_namespace = prepared_policy.network_namespace_root / jail_id
    if (
        completed.cgroup_relative_path != expected_cgroup
        or completed.network_namespace_path != expected_namespace
    ):
        raise _reject("EXECUTION_CONTROL_BINDING", "completed control paths differ")
    expected_plan_id = policy_v1._candidate_bound_plan_identity_sha256(
        candidate_id=candidate.candidate_id,
        evidence_inventory_root=candidate.evidence_inventory_root,
        candidate_manifest_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        contract_sha256=prepared_policy.contract_sha256,
        runtime_manifest_sha256=hashlib.sha256(runtime.canonical_bytes).digest(),
        artifact_set_id=runtime.artifact_set_id,
        machine_config_sha256=runtime.machine_config_sha256,
        authority_input_profile_sha256=runtime.authority_input_profile_sha256,
        firecracker_profile_sha256=prepared_policy.firecracker_profile_sha256,
        netns_helper_sha256=bytes.fromhex(prepared_policy.netns_helper_sha256),
        jail_id=jail_id,
    )
    if execution.candidate_bound_identity_sha256 != expected_plan_id:
        raise _reject("EXECUTION_PLAN_BINDING", "candidate-bound plan identity differs")
    return completed


def _checked_request_intent_and_output(
    *,
    inputs: _FirecrackerJoinInputsV1,
    runtime: runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    completed: supervisor_v1.CompletedSpotV7RootSupervisorRunV1,
) -> tuple[
    protocol_v1.SpotV7FirecrackerRequestV1,
    DecodedSpotV7FirecrackerAuthorityInputManifestV1,
    StructurallyDecodedSpotV7VerifierPayloadV1,
]:
    try:
        request = protocol_v1.decode_exact_request_v1(inputs.exact_request_bytes)
    except (TypeError, ValueError) as exc:
        raise _reject("REQUEST", "exact Firecracker request rejected") from exc
    input_identity = next(row for row in runtime.artifacts if row.role == "input")
    if (
        request.sha256 != completed.request_sha256
        or request.runtime_manifest_sha256
        != hashlib.sha256(runtime.canonical_bytes).digest()
        or request.machine_config_sha256 != runtime.machine_config_sha256
        or request.input_drive_sha256 != input_identity.sha256
    ):
        raise _reject("REQUEST_BINDING", "request differs from runtime or completed result")
    try:
        intent = decode_exact_authority_input_manifest_v1(
            inputs.exact_settlement_intent_bytes
        )
    except (SpotV7FirecrackerAuthorityInputRejectV1, TypeError, ValueError) as exc:
        raise _reject("SETTLEMENT_INTENT", "authority-input intent rejected") from exc
    if (
        intent.sha256 != request.settlement_intent_sha256
        or intent.v7_image_id != runtime.v7_image_id
        or intent.v6_image_id != runtime.v6_image_id
    ):
        raise _reject("SETTLEMENT_INTENT_BINDING", "intent differs from request or images")
    try:
        payload = protocol_v1.decode_structural_v7_verifier_payload_v1(
            completed.payload_bytes
        )
    except (TypeError, ValueError) as exc:
        raise _reject("OUTPUT_PAYLOAD", "completed V7 output payload rejected") from exc
    if payload.payload_sha256 != completed.payload_sha256:
        raise _reject("OUTPUT_PAYLOAD_BINDING", "completed output payload digest differs")
    return request, intent, payload


def _bind_authority_artifacts(
    *,
    artifacts: Any,
    runtime: runtime_manifest_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    prepared_policy: policy_v1.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1,
    inputs: _FirecrackerJoinInputsV1,
) -> None:
    expected = {
        "authority_input_profile_sha256": runtime.authority_input_profile_sha256,
        "firecracker_profile_sha256": prepared_policy.firecracker_profile_sha256,
        "machine_config_sha256": runtime.machine_config_sha256,
        "root_supervisor_contract_sha256": prepared_policy.contract_sha256,
        "root_supervisor_executable_sha256": hashlib.sha256(
            inputs.exact_root_supervisor_executable_bytes
        ).digest(),
        "runtime_artifact_manifest_sha256": hashlib.sha256(
            inputs.exact_runtime_artifact_manifest_bytes
        ).digest(),
        "runtime_artifact_set_id": runtime.artifact_set_id,
        "runtime_manifest_sha256": hashlib.sha256(runtime.canonical_bytes).digest(),
    }
    if any(artifacts[name] != value for name, value in expected.items()):
        raise _reject(
            "EXECUTION_AUTHORITY_ARTIFACT_BINDING",
            "runtime identity differs from execution authority manifest",
        )


def _canonical_json_document(raw: bytes, *, code: str) -> dict[str, Any]:
    _require_bytes(raw, code)
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise _reject(code, "artifact is not strict canonical JSON") from exc
    if type(value) is not dict or candidate_v1.canonical_document_bytes_v1(value) != raw:
        raise _reject(code, "artifact is not strict canonical JSON")
    return cast(dict[str, Any], value)


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate JSON key")
        output[key] = value
    return output


def _reject_json_number(_value: str) -> NoReturn:
    raise ValueError("non-integer JSON number")


def _require_bytes(value: object, name: str) -> bytes:
    if type(value) is not bytes or not value:
        raise TypeError(f"{name} must be nonempty exact bytes")
    return value


def _canonical_hex_digest(value: object, name: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise _reject("PROOF_ROOT_ENCODING", f"{name} is not canonical lowercase hex")
    decoded = bytes.fromhex(value)
    if not any(decoded):
        raise _reject("PROOF_ROOT_ENCODING", f"{name} must be nonzero")
    return decoded


def _reject(code: str, detail: str) -> SpotV7ReleaseBoundFirecrackerRejectV1:
    return SpotV7ReleaseBoundFirecrackerRejectV1(code, detail)
