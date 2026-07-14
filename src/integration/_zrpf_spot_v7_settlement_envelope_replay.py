"""Bounded, authority-false Spot V7 settlement-envelope replay.

This lane closes the local relation between one governed V7 candidate, one
canonical body envelope, four typed cell openings, one nonce advance, and the
full restricted Spot pre/post state roots. The V7 receipt/runtime capability
remains an external prerequisite. The resulting observation grants no
settlement, release, or production authority.
"""

from __future__ import annotations

import copy
from typing import Any, NoReturn, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_settlement_envelope_codec import (
    MAX_ENVELOPE_ITEMS_V1,
    MAX_HEADER_OR_CONFIG_BYTES_V1,
    MAX_LEDGER_BODY_BYTES_V1,
    MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
    MAX_PRE_STATE_SNAPSHOT_ITEMS_V1,
    _candidate_proposal,
    _receipt,
    _semantic_projection,
    _sha256,
    _snapshot_envelope,
    _snapshot_exact_dict,
    build_spot_v7_settlement_envelope_v1,
    decode_exact_spot_v7_settlement_envelope_v1,
    encode_spot_v7_settlement_envelope_v1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1,
    ENVELOPE_PROPOSAL_HASH_DOMAIN_V1,
    ENVELOPE_RECEIPT_HASH_DOMAIN_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1,
    SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
    SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1,
    SpotV7SettlementEnvelopeReplayErrorV1,
    _AuthenticatedSpotV7SettlementReplayObservationV1,
    _EnvelopeEvaluationV1,
    _NonTransferableSettlementReplayV1,
    _SpotV7SettlementReplayProjectionV1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_state import (
    _apply_exact_candidate,
    _require_ledger_bindings,
)
from src.integration.zeno_ledger_replay import (
    parse_replay_engine_config_v0,
    replay_engine_config_digest_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    hash_v0,
)

MAX_OBSERVATION_EVIDENCE_BYTES_V1 = 512 * 1_024


@final
class SpotV7SettlementEnvelopeReplayAdapterV1(_NonTransferableSettlementReplayV1):
    """Evaluate or authenticate one restricted singleton settlement envelope."""

    __slots__ = ("_config_chain_id", "_config_document_bytes", "_config_digest")

    _config_chain_id: str
    _config_document_bytes: bytes
    _config_digest: str

    def __init__(self, engine_config_document: object) -> None:
        document = _snapshot_exact_dict(
            engine_config_document,
            name="engine config",
            max_bytes=MAX_HEADER_OR_CONFIG_BYTES_V1,
            max_items=MAX_ENVELOPE_ITEMS_V1,
            reject_code="engine_config",
        )
        try:
            config, canonical = parse_replay_engine_config_v0(document)
            digest = replay_engine_config_digest_v0(canonical)
        except (KeyError, TypeError, ValueError) as exc:
            raise SpotV7SettlementEnvelopeReplayErrorV1("engine_config") from exc
        object.__setattr__(self, "_config_chain_id", config.chain_id)
        object.__setattr__(
            self,
            "_config_document_bytes",
            canonical_json_bytes_v0(canonical),
        )
        object.__setattr__(self, "_config_digest", digest)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SpotV7SettlementEnvelopeReplayAdapterV1 cannot be subclassed")

    @property
    def proof_receipt_authentication_established(self) -> bool:
        return False

    @property
    def application_domain_to_ledger_chain_binding_established(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def evaluate(
        self,
        *,
        settlement: object,
        envelope: object,
        pre_snapshot: object,
    ) -> dict[str, Any]:
        """Return deterministic data-only acceptance or rejection receipt."""

        candidate = _candidate_from_settlement(settlement)
        envelope_value = _snapshot_envelope(envelope)
        pre_value = _snapshot_pre_state(pre_snapshot)
        return copy.deepcopy(_evaluate(candidate, envelope_value, pre_value).receipt)

    def authenticate(
        self,
        *,
        settlement: object,
        header: object,
        body: object,
        pre_snapshot: object,
        parent_header: object | None = None,
    ) -> _AuthenticatedSpotV7SettlementReplayObservationV1:
        """Replay one body-committed envelope and seal its exact observation."""

        candidate = _candidate_from_settlement(settlement)
        header_value = _snapshot_header(header, name="header")
        body_value = _snapshot_body(body)
        pre_value = _snapshot_pre_state(pre_snapshot)
        parent_value = (
            None if parent_header is None else _snapshot_header(parent_header, name="parent header")
        )
        _require_ledger_bindings(
            candidate=candidate,
            header=header_value,
            body=body_value,
            config_digest=self._config_digest,
            config_chain_id=self._config_chain_id,
            parent_header=parent_value,
        )
        envelope = _single_body_envelope(body_value)
        evaluation = _evaluate(candidate, envelope, pre_value)
        _require_accepted_committed_receipt(envelope, evaluation)
        return _seal_observation(
            candidate=candidate,
            header=header_value,
            body=body_value,
            parent_header=parent_value,
            evaluation=evaluation,
            config_digest=self._config_digest,
        )


def _candidate_from_settlement(value: object) -> _SpotV7SettlementCandidateInputV1:
    settlement = _require_settlement_capability(value)
    return settlement._candidate_for_atomic_store()


def _evaluate(
    candidate: _SpotV7SettlementCandidateInputV1,
    envelope: dict[str, Any],
    pre_snapshot: dict[str, Any],
) -> _EnvelopeEvaluationV1:
    envelope_bytes = encode_spot_v7_settlement_envelope_v1(envelope)
    proposal = envelope["proposal"]
    if type(proposal) is not dict:
        raise SpotV7SettlementEnvelopeReplayErrorV1("canonical_envelope")
    proposal_hash = hash_v0(ENVELOPE_PROPOSAL_HASH_DOMAIN_V1, proposal)
    try:
        semantic = _semantic_projection(candidate)
        if not _canonical_json_equal(proposal, _candidate_proposal(candidate, semantic)):
            raise SpotV7SettlementEnvelopeReplayErrorV1("candidate_binding")
        post_state = _apply_exact_candidate(candidate, semantic, pre_snapshot)
    except SpotV7SettlementEnvelopeReplayErrorV1 as exc:
        return _EnvelopeEvaluationV1(
            envelope_bytes=envelope_bytes,
            proposal_hash=proposal_hash,
            receipt=_receipt(
                candidate,
                proposal_hash=proposal_hash,
                accepted=False,
                reject_code=exc.code,
            ),
            post_state=None,
        )
    return _EnvelopeEvaluationV1(
        envelope_bytes=envelope_bytes,
        proposal_hash=proposal_hash,
        receipt=_receipt(
            candidate,
            proposal_hash=proposal_hash,
            accepted=True,
            reject_code=None,
        ),
        post_state=post_state,
    )


def _single_body_envelope(body: dict[str, Any]) -> dict[str, Any]:
    envelopes = body["settlement_envelopes"]
    if type(envelopes) is not list or len(envelopes) != 1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("envelope_count")
    return _snapshot_envelope(envelopes[0])


def _require_accepted_committed_receipt(
    envelope: dict[str, Any],
    evaluation: _EnvelopeEvaluationV1,
) -> None:
    committed_receipt = envelope["expected_receipt"]
    if evaluation.receipt["accepted"] is not True:
        if _canonical_json_equal(committed_receipt, evaluation.receipt):
            raise SpotV7SettlementEnvelopeReplayErrorV1("settlement_rejected")
        raise SpotV7SettlementEnvelopeReplayErrorV1(str(evaluation.receipt["reject_code"]))
    if not _canonical_json_equal(committed_receipt, evaluation.receipt):
        raise SpotV7SettlementEnvelopeReplayErrorV1("committed_receipt")


def _canonical_json_equal(left: object, right: object) -> bool:
    """Compare JSON values without Python's bool/int equality alias."""

    return canonical_json_bytes_v0(left) == canonical_json_bytes_v0(right)


def _seal_observation(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    header: dict[str, Any],
    body: dict[str, Any],
    parent_header: dict[str, Any] | None,
    evaluation: _EnvelopeEvaluationV1,
    config_digest: str,
) -> _AuthenticatedSpotV7SettlementReplayObservationV1:
    receipt_hash = hash_v0(ENVELOPE_RECEIPT_HASH_DOMAIN_V1, evaluation.receipt)
    effect_ids_root = hash_v0(
        "zrpf_spot_v7_settlement_envelope_effect_ids_v1",
        {"effect_ids": [row.effect_id for row in candidate.asset_effects]},
    )
    header_hash = canonical_header_hash_v0(header)
    body_root = canonical_body_root_v0(body)
    evidence = _observation_evidence(candidate, evaluation, header_hash, body_root, receipt_hash)
    evidence_bytes = canonical_json_bytes_v0(evidence)
    if not evidence_bytes or len(evidence_bytes) > MAX_OBSERVATION_EVIDENCE_BYTES_V1:
        raise SpotV7SettlementEnvelopeReplayErrorV1("observation_evidence")
    projection = _SpotV7SettlementReplayProjectionV1(
        chain_id=header["chain_id"],
        height=header["height"],
        header_hash=header_hash,
        parent_header_hash=(
            None if parent_header is None else canonical_header_hash_v0(parent_header)
        ),
        body_root=body_root,
        config_digest=config_digest,
        candidate_settlement_commitment=_derive_capability_commitment(candidate),
        proof_journal_hash=_sha256(candidate.exact_v7_journal_bytes),
        envelope_sha256=_sha256(evaluation.envelope_bytes),
        envelope_proposal_hash=evaluation.proposal_hash,
        receipt_hash=receipt_hash,
        receipt_accepted=True,
        settlement_effect_plan_commitment=candidate.settlement_effect_plan_commitment,
        pre_state_root=candidate.pre_state_root,
        post_state_root=candidate.post_state_root,
        economic_action_id=candidate.economic_action_id,
        authorization_nullifier=candidate.authorization_nullifier,
        authorization_grant_spend_nullifier=candidate.authorization_grant_spend_nullifier,
        cell_transitions_root=candidate.cell_transitions_root,
        asset_effect_ids_root=effect_ids_root,
        observation_evidence_root=_sha256(evidence_bytes),
    )
    return _AuthenticatedSpotV7SettlementReplayObservationV1(
        projection,
        exact_header_bytes=canonical_json_bytes_v0(header),
        exact_body_bytes=canonical_json_bytes_v0(body),
        exact_envelope_bytes=evaluation.envelope_bytes,
        exact_receipt_bytes=canonical_json_bytes_v0(evaluation.receipt),
        exact_evidence_bytes=evidence_bytes,
        seal=_SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1,
    )


def _observation_evidence(
    candidate: _SpotV7SettlementCandidateInputV1,
    evaluation: _EnvelopeEvaluationV1,
    header_hash: str,
    body_root: str,
    receipt_hash: str,
) -> dict[str, Any]:
    return {
        "schema": SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1,
        "status": "authenticated_candidate_bound_settlement_envelope_replay",
        "candidate_settlement_commitment": _derive_capability_commitment(candidate),
        "header_hash": header_hash,
        "body_root": body_root,
        "envelope_sha256": _sha256(evaluation.envelope_bytes),
        "receipt_hash": receipt_hash,
        "claims": {
            "canonical_envelope_bytes_checked": True,
            "typed_cell_openings_replayed": True,
            "full_restricted_state_roots_recomputed": True,
            "settlement_effect_plan_commitment_cross_bound": True,
            "economic_action_and_nullifiers_cross_bound": True,
            "deterministic_receipt_checked": True,
            "application_domain_to_ledger_chain_binding_established": False,
            "proof_receipt_authentication_established": False,
            "settlement_authority": False,
            "release_authority": False,
            "production_authority": False,
        },
    }


def _snapshot_header(value: object, *, name: str) -> dict[str, Any]:
    return _snapshot_exact_dict(
        value,
        name=name,
        max_bytes=MAX_HEADER_OR_CONFIG_BYTES_V1,
        max_items=MAX_ENVELOPE_ITEMS_V1,
        reject_code="header_size",
    )


def _snapshot_body(value: object) -> dict[str, Any]:
    return _snapshot_exact_dict(
        value,
        name="body",
        max_bytes=MAX_LEDGER_BODY_BYTES_V1,
        max_items=16_384,
        reject_code="body_size",
    )


def _snapshot_pre_state(value: object) -> dict[str, Any]:
    return _snapshot_exact_dict(
        value,
        name="pre-state snapshot",
        max_bytes=MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
        max_items=MAX_PRE_STATE_SNAPSHOT_ITEMS_V1,
        reject_code="pre_snapshot_size",
    )


__all__ = [
    "SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1",
    "SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1",
    "SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1",
    "SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1",
    "SpotV7SettlementEnvelopeReplayAdapterV1",
    "SpotV7SettlementEnvelopeReplayErrorV1",
    "build_spot_v7_settlement_envelope_v1",
    "decode_exact_spot_v7_settlement_envelope_v1",
    "encode_spot_v7_settlement_envelope_v1",
]
