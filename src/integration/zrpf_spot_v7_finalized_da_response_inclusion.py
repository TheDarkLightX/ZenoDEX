"""Finalized ZenoLedger inclusion of one sampled-response evidence digest.

The adapter joins an already authenticated sampled-evidence value with one
already authenticated checkpoint-finality V3 value.  It verifies that the
finalized header commits a canonical body containing the exact V1 inclusion
record before the response deadline.  The body carries a digest and response
commitments, not the sampled evidence bytes themselves.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _decode_exact_json_object,
)
from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    validate_header_body_roots_v0,
)
from src.integration.zrpf_sampled_retrievability_v1.ledger_inclusion import (
    SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1,
    SampledResponseLedgerInclusionRecordV1,
    build_sampled_response_ledger_inclusion_record_v1,
    parse_sampled_response_ledger_inclusion_record_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.model import (
    require_root,
    require_token,
    require_u64,
)
from src.integration.zrpf_sampled_retrievability_v1.projection import (
    _VerifiedProjectionV1,
)
from src.integration.zrpf_sampled_retrievability_v1.verifier import (
    _AuthenticatedSampledRetrievabilityEvidenceV1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)

MAX_ZENO_LEDGER_ORACLE_PACKETS_FOR_DA_INCLUSION_V1 = 256
_FINALITY_EVIDENCE_SCHEMA_V3 = "zenodex/zrpf/spot_v7/zeno_ledger_checkpoint_finality_evidence/v3"


class SpotV7FinalizedDaResponseInclusionErrorV1(ValueError):
    """Stable fail-closed rejection before the private inclusion fact exists."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_FINALIZED_DA_RESPONSE_INCLUSION_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class _FinalizedSampledResponseInclusionProjectionV1:
    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    data_epoch_id: int
    checked_epoch: int
    response_deadline_epoch: int
    inclusion_height: int
    policy_root: str
    certificate_root: str
    data_root: str
    beacon_commitment: str
    sampled_evidence_sha256: str
    accepted_provider_set_root: str
    response_records_root: str
    inclusion_record_root: str
    finalized_body_root: str
    finalized_header_hash: str
    finality_policy_root: str
    finality_certificate_root: str
    finality_evidence_root: str

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "policy_root",
            "certificate_root",
            "data_root",
            "beacon_commitment",
            "sampled_evidence_sha256",
            "accepted_provider_set_root",
            "response_records_root",
            "inclusion_record_root",
            "finalized_body_root",
            "finalized_header_hash",
            "finality_policy_root",
            "finality_certificate_root",
            "finality_evidence_root",
        ):
            require_root(getattr(self, name), name=f"finalized DA inclusion {name}")
        require_token(
            self.zeno_ledger_chain_id,
            name="finalized DA inclusion zeno_ledger_chain_id",
        )
        for name in (
            "data_epoch_id",
            "checked_epoch",
            "response_deadline_epoch",
            "inclusion_height",
        ):
            require_u64(getattr(self, name), name=f"finalized DA inclusion {name}")
        if not self.checked_epoch <= self.inclusion_height <= self.response_deadline_epoch:
            raise ValueError("finalized DA inclusion height is outside the response window")


@dataclass(frozen=True, slots=True)
class _FinalizedBodyContextV1:
    body: dict[str, Any]
    finality_evidence: dict[str, Any]
    header: dict[str, Any]
    body_root: str
    header_hash: str


class _FinalizedSampledResponseInclusionSealV1:
    __slots__ = ()


_FINALIZED_SAMPLED_RESPONSE_INCLUSION_SEAL_V1 = _FinalizedSampledResponseInclusionSealV1()


@final
class _AuthenticatedFinalizedSampledResponseInclusionV1:
    """Non-transferable finalized digest-inclusion fact with authority disabled."""

    __slots__ = (
        "_exact_body_bytes",
        "_finality",
        "_projection",
        "_record",
        "_sampled",
        "_seal",
    )

    _exact_body_bytes: bytes
    _finality: _AuthenticatedExactCheckpointFinalityTransitionV3
    _projection: _FinalizedSampledResponseInclusionProjectionV1
    _record: SampledResponseLedgerInclusionRecordV1
    _sampled: _AuthenticatedSampledRetrievabilityEvidenceV1
    _seal: _FinalizedSampledResponseInclusionSealV1

    def __init__(
        self,
        projection: _FinalizedSampledResponseInclusionProjectionV1,
        *,
        sampled: _AuthenticatedSampledRetrievabilityEvidenceV1,
        finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
        exact_body_bytes: bytes,
        record: SampledResponseLedgerInclusionRecordV1,
        seal: _FinalizedSampledResponseInclusionSealV1,
    ) -> None:
        if type(projection) is not _FinalizedSampledResponseInclusionProjectionV1:
            raise TypeError("finalized DA inclusion projection has the wrong type")
        if seal is not _FINALIZED_SAMPLED_RESPONSE_INCLUSION_SEAL_V1:
            raise TypeError("finalized DA inclusion requires the module-private seal")
        expected, expected_record = _derive_projection_v1(
            sampled=sampled,
            finality=finality,
            exact_body_bytes=exact_body_bytes,
        )
        if projection != expected or record != expected_record:
            raise ValueError("finalized DA inclusion projection drift")
        object.__setattr__(self, "_sampled", sampled)
        object.__setattr__(self, "_finality", finality)
        object.__setattr__(self, "_exact_body_bytes", exact_body_bytes)
        object.__setattr__(self, "_record", record)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("finalized DA inclusion cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("finalized DA inclusion cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("finalized DA inclusion cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("finalized DA inclusion cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("finalized DA inclusion cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _FINALIZED_SAMPLED_RESPONSE_INCLUSION_SEAL_V1

    def _projection_for_da_store_v5(
        self,
    ) -> _FinalizedSampledResponseInclusionProjectionV1:
        if not self._has_private_seal():
            raise TypeError("finalized DA inclusion lacks its private seal")
        expected, record = _derive_projection_v1(
            sampled=self._sampled,
            finality=self._finality,
            exact_body_bytes=self._exact_body_bytes,
        )
        if expected != self._projection or record != self._record:
            raise ValueError("finalized DA inclusion drift")
        return self._projection

    @property
    def finalized_sampled_evidence_digest_included_by_deadline(self) -> bool:
        self._projection_for_da_store_v5()
        return True

    @property
    def exact_response_and_signature_envelope_digests_committed(self) -> bool:
        self._projection_for_da_store_v5()
        return True

    @property
    def sampled_evidence_bytes_published_in_ledger_body(self) -> bool:
        return False

    @property
    def provider_response_generation_time_verified(self) -> bool:
        return False

    @property
    def response_timing_provenance_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
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


def bind_finalized_sampled_response_inclusion_v1(
    *,
    sampled_response: object,
    checkpoint_finality: object,
    exact_body_bytes: bytes,
) -> _AuthenticatedFinalizedSampledResponseInclusionV1:
    """Authenticate exact digest inclusion under one finalized body root."""

    sampled = _require_sampled(sampled_response)
    finality = _require_finality(checkpoint_finality)
    body_bytes = _require_exact_bytes(exact_body_bytes, name="exact ledger body")
    try:
        projection, record = _derive_projection_v1(
            sampled=sampled,
            finality=finality,
            exact_body_bytes=body_bytes,
        )
    except SpotV7FinalizedDaResponseInclusionErrorV1:
        raise
    except (KeyError, TypeError, ValueError) as exc:
        raise SpotV7FinalizedDaResponseInclusionErrorV1(_reject_code(exc)) from exc
    return _AuthenticatedFinalizedSampledResponseInclusionV1(
        projection,
        sampled=sampled,
        finality=finality,
        exact_body_bytes=body_bytes,
        record=record,
        seal=_FINALIZED_SAMPLED_RESPONSE_INCLUSION_SEAL_V1,
    )


def _derive_projection_v1(
    *,
    sampled: _AuthenticatedSampledRetrievabilityEvidenceV1,
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
    exact_body_bytes: bytes,
) -> tuple[
    _FinalizedSampledResponseInclusionProjectionV1,
    SampledResponseLedgerInclusionRecordV1,
]:
    sampled_value = _require_sampled(sampled)
    finality_value = _require_finality(finality)
    body_bytes = _require_exact_bytes(exact_body_bytes, name="exact ledger body")
    sampled_projection = sampled_value._projection_for_spot_v7_da_prerequisite_v1()
    context = _decode_finalized_body_context_v1(finality_value, body_bytes)
    _require_finality_projection_bindings(
        sampled_projection=sampled_projection,
        finality=finality_value,
        context=context,
    )
    record = _find_inclusion_record(context.body)
    expected_document = build_sampled_response_ledger_inclusion_record_v1(
        sampled_value.exact_evidence_bytes,
        zeno_ledger_chain_id=context.header["chain_id"],
        inclusion_height=context.header["height"],
    )
    if canonical_json_bytes_v0(record.to_document()) != canonical_json_bytes_v0(expected_document):
        raise ValueError("ledger inclusion record disagrees with authenticated evidence")
    if record.application_id != sampled_projection.application_id:
        raise ValueError("ledger inclusion application mismatch")
    if record.chain_or_domain_id != sampled_projection.chain_or_domain_id:
        raise ValueError("ledger inclusion domain mismatch")
    if record.sampled_evidence_sha256 != "0x" + sampled_projection.evidence_sha256:
        raise ValueError("ledger inclusion sampled-evidence digest mismatch")
    if record.accepted_provider_ids != sampled_projection.accepted_provider_ids:
        raise ValueError("ledger inclusion provider set mismatch")
    projection = finality_value._projection
    return (
        _FinalizedSampledResponseInclusionProjectionV1(
            application_id=record.application_id,
            chain_or_domain_id=record.chain_or_domain_id,
            zeno_ledger_chain_id=record.zeno_ledger_chain_id,
            data_epoch_id=record.data_epoch_id,
            checked_epoch=record.checked_epoch,
            response_deadline_epoch=record.response_deadline_epoch,
            inclusion_height=record.inclusion_height,
            policy_root=record.policy_root,
            certificate_root=record.certificate_root,
            data_root=record.data_root,
            beacon_commitment=record.beacon_commitment,
            sampled_evidence_sha256=record.sampled_evidence_sha256,
            accepted_provider_set_root=record.accepted_provider_set_root,
            response_records_root=record.response_records_root,
            inclusion_record_root=record.record_root,
            finalized_body_root=context.body_root,
            finalized_header_hash=context.header_hash,
            finality_policy_root=projection.policy_root,
            finality_certificate_root=projection.certificate_root,
            finality_evidence_root=projection.finality_evidence_root,
        ),
        record,
    )


def _decode_finalized_body_context_v1(
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
    exact_body_bytes: bytes,
) -> _FinalizedBodyContextV1:
    body = _decode_exact_json_object(
        exact_body_bytes,
        name="exact finalized DA ledger body",
    )
    finality_evidence = _decode_exact_json_object(
        finality._exact_finality_evidence_bytes,
        name="exact checkpoint-finality evidence",
    )
    if finality_evidence.get("schema") != _FINALITY_EVIDENCE_SCHEMA_V3:
        raise ValueError("checkpoint-finality evidence schema mismatch")
    header = _require_exact_dict(finality_evidence.get("header"), name="finalized header")
    try:
        validate_header_body_roots_v0(header, body)
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("finalized header does not commit the exact body") from exc
    return _FinalizedBodyContextV1(
        body=body,
        finality_evidence=finality_evidence,
        header=header,
        body_root=canonical_body_root_v0(body),
        header_hash=canonical_header_hash_v0(header),
    )


def _require_finality_projection_bindings(
    *,
    sampled_projection: _VerifiedProjectionV1,
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
    context: _FinalizedBodyContextV1,
) -> None:
    projection = finality._projection
    application = _require_exact_dict(
        context.finality_evidence.get("application_binding"),
        name="finality application binding",
    )
    prior = _require_exact_dict(
        context.finality_evidence.get("prior_application_checkpoint"),
        name="prior application checkpoint",
    )
    replay = _require_exact_dict(
        context.finality_evidence.get("settlement_replay_observation"),
        name="settlement replay observation",
    )
    checkpoint = _require_exact_dict(
        context.finality_evidence.get("checkpoint"),
        name="finalized checkpoint",
    )
    header = context.header
    checks = (
        (projection.application_id == sampled_projection.application_id, "application"),
        (projection.chain_or_domain_id == sampled_projection.chain_or_domain_id, "domain"),
        (projection.epoch_id == header["height"], "finality epoch"),
        (
            projection.next_application_checkpoint_sequence == header["height"],
            "finality sequence",
        ),
        (
            projection.next_application_checkpoint_hash == context.header_hash,
            "finality header",
        ),
        (application.get("application_id") == projection.application_id, "application binding"),
        (application.get("chain_or_domain_id") == projection.chain_or_domain_id, "domain binding"),
        (application.get("epoch_id") == projection.epoch_id, "epoch binding"),
        (application.get("post_state_root") == projection.post_state_root, "state binding"),
        (application.get("proof_journal_hash") == projection.proof_journal_hash, "journal binding"),
        (
            prior.get("sequence") == projection.prior_application_checkpoint_sequence,
            "prior sequence",
        ),
        (
            prior.get("checkpoint_hash") == projection.prior_application_checkpoint_hash,
            "prior checkpoint",
        ),
        (header["chain_id"] == replay.get("chain_id"), "replay chain"),
        (header["height"] == replay.get("height"), "replay height"),
        (context.header_hash == replay.get("header_hash"), "replay header"),
        (context.body_root == replay.get("body_root"), "replay body"),
        (
            checkpoint.get("header_hash") == context.header_hash,
            "checkpoint header",
        ),
    )
    for accepted, name in checks:
        if not accepted:
            raise ValueError(f"finalized sampled-response inclusion {name} mismatch")


def _find_inclusion_record(body: dict[str, Any]) -> SampledResponseLedgerInclusionRecordV1:
    evidence = _require_exact_dict(body.get("evidence"), name="ledger body evidence")
    packets = evidence.get("oracle_packets")
    if (
        type(packets) is not list
        or len(packets) > MAX_ZENO_LEDGER_ORACLE_PACKETS_FOR_DA_INCLUSION_V1
    ):
        raise ValueError("ledger body oracle-packet count exceeds the inclusion bound")
    candidates = [
        item
        for item in packets
        if type(item) is dict
        and item.get("schema") == SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1
    ]
    if len(candidates) != 1:
        raise ValueError("ledger body must contain one exact sampled-response inclusion record")
    return parse_sampled_response_ledger_inclusion_record_v1(candidates[0])


def _require_sampled(value: object) -> _AuthenticatedSampledRetrievabilityEvidenceV1:
    if (
        not isinstance(value, _AuthenticatedSampledRetrievabilityEvidenceV1)
        or type(value) is not _AuthenticatedSampledRetrievabilityEvidenceV1
    ):
        raise TypeError("sampled_response must be exact authenticated sampled evidence V1")
    sampled = value
    if not sampled._has_private_seal():
        raise TypeError("sampled_response lacks its private seal")
    sampled._projection_for_spot_v7_da_prerequisite_v1()
    return sampled


def _require_finality(value: object) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    if (
        not isinstance(value, _AuthenticatedExactCheckpointFinalityTransitionV3)
        or type(value) is not _AuthenticatedExactCheckpointFinalityTransitionV3
    ):
        raise TypeError("checkpoint_finality must be exact authenticated finality V3")
    finality = value
    if not finality._has_private_seal():
        raise TypeError("checkpoint_finality lacks its private seal")
    if _sha256_prefixed(finality._exact_finality_evidence_bytes) != (
        finality._projection.finality_evidence_root
    ):
        raise ValueError("checkpoint-finality evidence digest drift")
    return finality


def _require_exact_bytes(value: object, *, name: str) -> bytes:
    if type(value) is not bytes or not value:
        raise TypeError(f"{name} must be non-empty exact bytes")
    return value


def _require_exact_dict(value: object, *, name: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise TypeError(f"{name} must be an exact dict")
    return value


def _sha256_prefixed(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _reject_code(exc: Exception) -> str:
    message = str(exc)
    if "deadline" in message or "timing" in message or "response window" in message:
        return "INCLUSION_AFTER_DEADLINE"
    if "record" in message or "oracle-packet" in message:
        return "INCLUSION_RECORD_MISMATCH"
    if "finality" in message or "checkpoint" in message:
        return "FINALITY_BINDING_MISMATCH"
    if "body" in message or "header" in message or "replay" in message:
        return "LEDGER_BODY_BINDING_MISMATCH"
    if "sampled" in message or "provider" in message:
        return "SAMPLED_EVIDENCE_BINDING_MISMATCH"
    return "FINALIZED_INCLUSION_BINDING_MISMATCH"


__all__ = [
    "MAX_ZENO_LEDGER_ORACLE_PACKETS_FOR_DA_INCLUSION_V1",
    "SpotV7FinalizedDaResponseInclusionErrorV1",
    "bind_finalized_sampled_response_inclusion_v1",
]
