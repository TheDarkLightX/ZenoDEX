"""Governed ZenoLedger BLS-quorum adapter for Spot V7 checkpoint finality.

The adapter accepts one sealed Spot V7 settlement candidate and one sealed
operational policy. It snapshots bounded plain-data inputs, authenticates an
app-hash-consistent ZenoLedger checkpoint with the policy-pinned BLS signer
registry, verifies the canonical validator schedule and the scheduled
proposer's BLS authorship, binds the application checkpoint cursor and Spot V7
journal/state roots, and derives the canonical ``checkpoint_finality_v2``
certificate itself.

The resulting private capability is suitable for the authority-false V2 atomic
store sink. Release provenance, data availability, economic settlement, and
production authority remain separate gates.
"""

from __future__ import annotations

import hashlib
from typing import Any, Mapping, NoReturn, Sequence, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _GovernedSpotV7OperationalPolicyV2,
    _require_operational_policy_v2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _AuthenticatedCheckpointFinalityProjectionV2,
    _require_policy_binding,
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    MAX_FINALITY_EVIDENCE_BYTES_V2,
    _build_test_only_checkpoint_finality_artifacts_v2,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    _MAX_FINALITY_VALIDATORS_V1,
    _ZERO_ROOT,
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
    SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1,
    SpotV7ZenoLedgerFinalityBindingErrorV1,
    ZenoLedgerCheckpointFinalityCursorV1,
    _FinalityInputSnapshotV1,
    _require_hash,
    _require_nonempty_string,
    _require_positive_u64,
    _snapshot_inputs,
    derive_zeno_ledger_external_finality_policy_hash_v2,
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_proposer_authorship_payload_hash_v1,
)
from src.integration.zeno_ledger_live_quorum_v0 import build_live_checkpoint_quorum_admission_v0
from src.integration.zeno_ledger_signature import (
    validate_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import (
    validate_signer_registry_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
)
from src.integration.zeno_ledger_validator_schedule_v0 import (
    build_proposer_duty_v0,
    build_scheduled_header_admission_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
)


@final
class SpotV7ZenoLedgerCheckpointFinalityAdapterV2:
    """Authenticate one policy-pinned ZenoLedger checkpoint BLS quorum."""

    __slots__ = ("_policy",)

    _policy: _GovernedSpotV7OperationalPolicyV2

    def __init__(self, policy: object) -> None:
        object.__setattr__(self, "_policy", _require_operational_policy_v2(policy))

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SpotV7ZenoLedgerCheckpointFinalityAdapterV2 cannot be subclassed")

    @property
    def cryptographic_checkpoint_quorum_supported(self) -> bool:
        return True

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def authenticate(
        self,
        *,
        settlement: object,
        prior_cursor: object,
        header: object,
        checkpoint: object,
        validator_set: object,
        proposer_id: object,
        proposer_key_id: object,
        proposer_envelope: object,
        registry: object,
        envelopes: object,
    ) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
        """Verify exact BLS evidence, then derive and seal finality V2 facts."""

        settlement_value = _require_settlement_capability(settlement)
        cursor = _require_cursor(prior_cursor)
        snapshot = _snapshot_inputs(
            header=header,
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=proposer_id,
            proposer_key_id=proposer_key_id,
            proposer_envelope=proposer_envelope,
            registry=registry,
            envelopes=envelopes,
        )
        candidate = settlement_value._candidate_for_atomic_store()
        policy_projection = self._policy._projection
        _require_policy_binding(candidate, policy_projection)
        try:
            self._policy._require_active_at_epoch_for_operational_use(candidate.epoch_id)
        except ValueError as exc:
            raise SpotV7ZenoLedgerFinalityBindingErrorV1(
                "operational_policy_inactive"
            ) from exc
        policy = self._policy._policy_for_atomic_store()
        _validate_checkpoint_structure(snapshot)
        _validate_header_app_hash(snapshot.header)
        _require_checkpoint_transition_binding(
            candidate=candidate,
            cursor=cursor,
            header=snapshot.header,
            checkpoint=snapshot.checkpoint,
            policy=policy,
        )
        scheduled_header_admission = _require_scheduled_header_admission(snapshot)
        _require_registry_and_external_policy_binding(
            header=snapshot.header,
            registry=snapshot.registry,
            policy=policy,
        )
        proposer_authorship_admission = _require_proposer_authorship(snapshot)
        admission = build_live_checkpoint_quorum_admission_v0(
            header=snapshot.header,
            checkpoint=snapshot.checkpoint,
            registry=snapshot.registry,
            envelopes=snapshot.envelopes,
        )
        evidence_bytes = _canonical_finality_evidence(
            candidate=candidate,
            cursor=cursor,
            snapshot=snapshot,
            scheduled_header_admission=scheduled_header_admission,
            proposer_authorship_admission=proposer_authorship_admission,
            admission=admission,
        )
        return _derive_exact_finality_capability(
            candidate=candidate,
            policy=self._policy,
            cursor=cursor,
            checkpoint=snapshot.checkpoint,
            evidence_bytes=evidence_bytes,
        )


def _validate_checkpoint_structure(snapshot: _FinalityInputSnapshotV1) -> None:
    validate_checkpoint_header_binding_v0(snapshot.checkpoint, snapshot.header)
    if snapshot.checkpoint["signature_set"] != []:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("embedded_signature_set")
    if snapshot.checkpoint["signature_set_root"] != _ZERO_ROOT:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("embedded_signature_set_root")


def _validate_header_app_hash(header: Mapping[str, Any]) -> None:
    expected = compute_app_hash_v0(
        {
            "chain_id": header["chain_id"],
            "height": header["height"],
            "post_state_root": header["post_state_root"],
            "evidence_root": header["evidence_root"],
            "config_digest": header["config_digest"],
            "module_versions_digest": header["module_versions_digest"],
        }
    )
    if header["app_hash"] != expected:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("app_hash")


def _require_scheduled_header_admission(
    snapshot: _FinalityInputSnapshotV1,
) -> dict[str, Any]:
    try:
        return build_scheduled_header_admission_v0(
            header=snapshot.header,
            validator_set=snapshot.validator_set,
            proposer_id=snapshot.proposer_id,
            key_id=snapshot.proposer_key_id,
        )
    except (TypeError, ValueError) as exc:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("scheduled_header_admission") from exc


def _require_proposer_authorship(
    snapshot: _FinalityInputSnapshotV1,
) -> dict[str, Any]:
    """Authenticate the scheduled proposer over the exact canonical header."""

    try:
        duty = build_proposer_duty_v0(
            validator_set=snapshot.validator_set,
            height=int(snapshot.header["height"]),
        )
        proposer = duty["proposer"]
        if type(proposer) is not dict:
            raise TypeError("scheduled proposer must be an exact dict")
        if (
            proposer.get("validator_id") != snapshot.proposer_id
            or proposer.get("key_id") != snapshot.proposer_key_id
        ):
            raise ValueError("proposer identity does not match scheduled duty")
        envelope = snapshot.proposer_envelope
        if (
            envelope.get("signer_id") != snapshot.proposer_id
            or envelope.get("key_id") != snapshot.proposer_key_id
        ):
            raise ValueError("proposer envelope identity mismatch")
        header_hash = canonical_header_hash_v0(snapshot.header)
        authorship_payload_hash = derive_zeno_ledger_proposer_authorship_payload_hash_v1(
            chain_id=snapshot.header["chain_id"],
            height=snapshot.header["height"],
            header_hash=header_hash,
            validator_set_hash=snapshot.validator_set["validator_set_hash"],
            duty_hash=duty["duty_hash"],
        )
        public_key = _require_nonempty_string(
            proposer.get("public_key"),
            name="scheduled proposer public key",
        )
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind="checkpoint",
            expected_payload_hash=authorship_payload_hash,
            expected_public_key=public_key,
        )
        body = {
            "schema": SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1,
            "ok": True,
            "status": "accepted",
            "chain_id": snapshot.header["chain_id"],
            "height": snapshot.header["height"],
            "header_hash": header_hash,
            "authorship_payload_hash": authorship_payload_hash,
            "validator_set_hash": snapshot.validator_set["validator_set_hash"],
            "duty_hash": duty["duty_hash"],
            "proposer_id": snapshot.proposer_id,
            "key_id": snapshot.proposer_key_id,
            "public_key": public_key,
            "envelope_hash": envelope["envelope_hash"],
        }
        return {
            **body,
            "admission_hash": hash_v0(
                "zrpf_spot_v7_proposer_authorship_admission_v1",
                body,
            ),
        }
    except (KeyError, RuntimeError, TypeError, ValueError) as exc:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("proposer_authorship") from exc


def _require_checkpoint_transition_binding(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    policy_genesis_sequence = policy.genesis_application_checkpoint_sequence
    policy_genesis_hash = policy.genesis_application_checkpoint_hash
    if cursor.sequence < policy_genesis_sequence:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("prior_before_genesis")
    if cursor.sequence == policy_genesis_sequence and cursor.checkpoint_hash != policy_genesis_hash:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("genesis_checkpoint_hash")
    if cursor.sequence == MAX_U64:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("checkpoint_sequence_overflow")
    expected_sequence = cursor.sequence + 1
    checks = (
        (header["height"] == expected_sequence, "checkpoint_sequence"),
        (candidate.epoch_id == expected_sequence, "checkpoint_epoch"),
        (header["prev_header_hash"] == cursor.checkpoint_hash, "prior_checkpoint_hash"),
        (header["pre_state_root"] == candidate.pre_state_root, "pre_state_root"),
        (header["post_state_root"] == candidate.post_state_root, "post_state_root"),
        (header["data_availability_root"] == candidate.data_root, "data_root"),
        (
            header["proof_journal_hash"] == _candidate_journal_hash(candidate),
            "proof_journal_hash",
        ),
        (checkpoint["post_state_root"] == candidate.post_state_root, "post_state_root"),
        (
            checkpoint["proof_journal_hash"] == _candidate_journal_hash(candidate),
            "proof_journal_hash",
        ),
    )
    _require_checks(checks)


def _require_registry_and_external_policy_binding(
    *,
    header: Mapping[str, Any],
    registry: dict[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    validate_signer_registry_v0(registry)
    signers = registry["signers"]
    if type(signers) is not list or not signers or len(signers) > _MAX_FINALITY_VALIDATORS_V1:
        raise ValueError("signer registry count is outside the governed bound")
    chain_id = _require_nonempty_string(header["chain_id"], name="header.chain_id")
    registry_hash = _require_hash(registry["registry_hash"], name="registry hash")
    expected_external_policy = derive_zeno_ledger_external_finality_policy_hash_v2(
        chain_id=chain_id,
        config_digest=_require_hash(header["config_digest"], name="header config digest"),
        sequencer_set_hash=_require_hash(
            header["sequencer_set_hash"],
            name="header sequencer set hash",
        ),
    )
    checks = (
        (
            policy.finality_verifier_set_root == registry_hash,
            "verifier_set_root",
        ),
        (
            policy.finality_network_id == derive_zeno_ledger_finality_network_id_v1(chain_id),
            "finality_network",
        ),
        (
            policy.finality_protocol_id == derive_zeno_ledger_finality_protocol_id_v2(),
            "finality_protocol",
        ),
        (
            policy.external_finality_policy_hash == expected_external_policy,
            "external_finality_policy",
        ),
    )
    _require_checks(checks)
    active_weight = _active_weight(signers)
    threshold = _require_positive_u64(registry["threshold"], name="registry threshold")
    if threshold * 3 <= active_weight * 2:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("quorum_intersection")


def _active_weight(signers: Sequence[object]) -> int:
    total = 0
    for index, signer in enumerate(signers):
        if type(signer) is not dict:
            raise TypeError(f"registry.signers[{index}] must be an exact dict")
        if signer.get("status") == "active":
            weight = _require_positive_u64(
                signer.get("weight"),
                name=f"registry.signers[{index}].weight",
            )
            total += weight
            if total > MAX_U64:
                raise ValueError("active signer weight exceeds u64")
    if total == 0:
        raise ValueError("signer registry has no active weight")
    return total


def _canonical_finality_evidence(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    snapshot: _FinalityInputSnapshotV1,
    scheduled_header_admission: Mapping[str, Any],
    proposer_authorship_admission: Mapping[str, Any],
    admission: Mapping[str, Any],
) -> bytes:
    body = {
        "schema": SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
        "application_binding": {
            "application_id": candidate.application_id,
            "chain_or_domain_id": candidate.chain_or_domain_id,
            "epoch_id": candidate.epoch_id,
            "post_state_root": candidate.post_state_root,
            "proof_journal_hash": _candidate_journal_hash(candidate),
        },
        "prior_application_checkpoint": {
            "sequence": cursor.sequence,
            "checkpoint_hash": cursor.checkpoint_hash,
        },
        "header": snapshot.header,
        "checkpoint": snapshot.checkpoint,
        "validator_set": snapshot.validator_set,
        "scheduled_header_admission": dict(scheduled_header_admission),
        "proposer_envelope": snapshot.proposer_envelope,
        "proposer_authorship_admission": dict(proposer_authorship_admission),
        "registry": snapshot.registry,
        "envelopes": list(snapshot.envelopes),
        "live_quorum_admission": dict(admission),
    }
    encoded = canonical_json_bytes_v0(body)
    if not encoded or len(encoded) > MAX_FINALITY_EVIDENCE_BYTES_V2:
        raise ValueError("canonical finality evidence exceeds checkpoint-finality V2 bound")
    return encoded


def _derive_exact_finality_capability(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedSpotV7OperationalPolicyV2,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    checkpoint: Mapping[str, Any],
    evidence_bytes: bytes,
) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    store_policy = policy._policy_for_atomic_store()
    store_settlement = _seal_test_only_spot_v7_settlement_v1(candidate)
    artifacts = _build_test_only_checkpoint_finality_artifacts_v2(
        policy=store_policy,
        settlement=store_settlement,
        prior_application_checkpoint_sequence=cursor.sequence,
        prior_application_checkpoint_hash=cursor.checkpoint_hash,
        next_application_checkpoint_hash=_require_hash(
            checkpoint["header_hash"],
            name="checkpoint header hash",
        ),
        exact_finality_evidence_bytes=evidence_bytes,
    )
    projection = _AuthenticatedCheckpointFinalityProjectionV2(
        application_id=store_policy.application_id,
        chain_or_domain_id=store_policy.chain_or_domain_id,
        epoch_id=artifacts.epoch_id,
        proof_journal_hash=artifacts.proof_journal_hash,
        post_state_root=artifacts.post_state_root,
        policy_root=artifacts.policy_root,
        certificate_root=artifacts.certificate_root,
        finality_evidence_root=artifacts.finality_evidence_root,
        prior_application_checkpoint_sequence=(artifacts.prior_application_checkpoint_sequence),
        prior_application_checkpoint_hash=artifacts.prior_application_checkpoint_hash,
        next_application_checkpoint_sequence=(artifacts.next_application_checkpoint_sequence),
        next_application_checkpoint_hash=artifacts.next_application_checkpoint_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV2(
        projection,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_finality_evidence_bytes=artifacts.exact_finality_evidence_bytes,
        seal=_AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    )


def _require_cursor(value: object) -> ZenoLedgerCheckpointFinalityCursorV1:
    if type(value) is not ZenoLedgerCheckpointFinalityCursorV1:
        raise TypeError("prior_cursor must be exact ZenoLedgerCheckpointFinalityCursorV1")
    return value


def _candidate_journal_hash(candidate: _SpotV7SettlementCandidateInputV1) -> str:
    return "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()


def _require_checks(checks: Sequence[tuple[bool, str]]) -> None:
    for accepted, code in checks:
        if not accepted:
            raise SpotV7ZenoLedgerFinalityBindingErrorV1(code)


__all__ = [
    "SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2",
    "SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1",
    "SpotV7ZenoLedgerCheckpointFinalityAdapterV2",
    "SpotV7ZenoLedgerFinalityBindingErrorV1",
    "ZenoLedgerCheckpointFinalityCursorV1",
    "derive_zeno_ledger_external_finality_policy_hash_v2",
    "derive_zeno_ledger_finality_network_id_v1",
    "derive_zeno_ledger_finality_protocol_id_v2",
    "derive_zeno_ledger_proposer_authorship_payload_hash_v1",
]
