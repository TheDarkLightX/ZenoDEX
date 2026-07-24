"""Private replay-bound ZenoLedger body/state observation for Spot V7 finality.

The public adapter accepts bounded canonical ledger inputs and invokes the
existing deterministic replay verifier.  Only the resulting module-sealed
object may enter the Spot V7 finality adapter.  The observation establishes one
transaction-body replay.  It does not execute body settlement envelopes,
authenticate the Spot proof receipt, or grant settlement or production
authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict
from typing import Any, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    _snapshot_plain_dict,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_contract import (
    MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1,
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1,
    SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1,
    SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1,
    SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1,
    SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1,
    SpotV7ZenoLedgerReplayObservationErrorV1,
    _ReplayBoundBlockProjectionV1,
)
from src.integration.zeno_ledger_replay import (
    _replay_bound_block_details_v0,
    parse_replay_engine_config_v0,
    replay_engine_config_digest_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    dex_state_root_v0,
    hash_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes

_MAX_REPLAY_OBSERVATION_EVIDENCE_BYTES_V1 = 64 * 1_024


class _ReplayBoundObservationSealV1:
    __slots__ = ()


_REPLAY_BOUND_OBSERVATION_SEAL_V1 = _ReplayBoundObservationSealV1()


class _NonTransferableReplayObservationV1:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("replay-bound ZenoLedger observation cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("replay-bound ZenoLedger observation cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("replay-bound ZenoLedger observation cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("replay-bound ZenoLedger observation cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("replay-bound ZenoLedger observation cannot be serialized")


@final
class _AuthenticatedReplayBoundBlockObservationV1(_NonTransferableReplayObservationV1):
    """Exact replay evidence retained behind a module-private seal."""

    __slots__ = (
        "_projection",
        "_exact_header_bytes",
        "_exact_body_bytes",
        "_exact_evidence_bytes",
        "_seal",
    )

    _projection: _ReplayBoundBlockProjectionV1
    _exact_header_bytes: bytes
    _exact_body_bytes: bytes
    _exact_evidence_bytes: bytes
    _seal: _ReplayBoundObservationSealV1

    def __init__(
        self,
        projection: _ReplayBoundBlockProjectionV1,
        *,
        exact_header_bytes: bytes,
        exact_body_bytes: bytes,
        exact_evidence_bytes: bytes,
        seal: _ReplayBoundObservationSealV1,
    ) -> None:
        if type(projection) is not _ReplayBoundBlockProjectionV1:
            raise TypeError("replay observation projection has the wrong type")
        if seal is not _REPLAY_BOUND_OBSERVATION_SEAL_V1:
            raise TypeError("replay observation requires the module-private seal")
        for name, value in (
            ("header", exact_header_bytes),
            ("body", exact_body_bytes),
            ("evidence", exact_evidence_bytes),
        ):
            if type(value) is not bytes or not value:
                raise TypeError(f"exact replay observation {name} must be non-empty bytes")
        if _sha256(exact_body_bytes) != projection.body_sha256:
            raise ValueError("exact replay body disagrees with its sealed projection")
        if _sha256(exact_evidence_bytes) != projection.observation_evidence_root:
            raise ValueError("exact replay evidence disagrees with its sealed projection")
        header = _decode_exact_dict(exact_header_bytes, name="sealed replay header")
        if canonical_header_hash_v0(header) != projection.header_hash:
            raise ValueError("exact replay header disagrees with its sealed projection")
        body = _decode_exact_dict(exact_body_bytes, name="sealed replay body")
        if canonical_body_root_v0(body) != projection.body_root:
            raise ValueError("exact replay body root disagrees with its sealed projection")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_header_bytes", exact_header_bytes)
        object.__setattr__(self, "_exact_body_bytes", exact_body_bytes)
        object.__setattr__(self, "_exact_evidence_bytes", exact_evidence_bytes)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _REPLAY_BOUND_OBSERVATION_SEAL_V1

    def _header_for_finality_adapter(self) -> dict[str, Any]:
        _require_replay_observation(self)
        return _decode_exact_dict(self._exact_header_bytes, name="sealed replay header")

    def _projection_for_finality_adapter(self) -> _ReplayBoundBlockProjectionV1:
        _require_replay_observation(self)
        return self._projection

    def _canonical_projection_for_finality_adapter(self) -> dict[str, Any]:
        _require_replay_observation(self)
        return asdict(self._projection)

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@final
class SpotV7ZenoLedgerReplayBoundObservationAdapterV1(
    _NonTransferableReplayObservationV1
):
    """Replay one canonical body under one canonical engine configuration."""

    __slots__ = ("_config_document_bytes", "_config_digest")

    _config_document_bytes: bytes
    _config_digest: str

    def __init__(self, engine_config_document: object) -> None:
        snapshot = _snapshot_plain_dict(engine_config_document, name="engine_config_document")
        try:
            config, canonical_document = parse_replay_engine_config_v0(snapshot)
            config_digest = replay_engine_config_digest_v0(canonical_document)
        except (KeyError, TypeError, ValueError) as exc:
            raise SpotV7ZenoLedgerReplayObservationErrorV1("engine_config") from exc
        del config
        object.__setattr__(
            self,
            "_config_document_bytes",
            canonical_json_bytes_v0(canonical_document),
        )
        object.__setattr__(self, "_config_digest", config_digest)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError(
            "SpotV7ZenoLedgerReplayBoundObservationAdapterV1 cannot be subclassed"
        )

    def authenticate(
        self,
        *,
        header: object,
        body: object,
        pre_snapshot: object,
        parent_header: object | None = None,
    ) -> _AuthenticatedReplayBoundBlockObservationV1:
        """Replay exact canonical inputs and mint one non-transferable observation."""

        try:
            return self._authenticate_exact(
                header=header,
                body=body,
                pre_snapshot=pre_snapshot,
                parent_header=parent_header,
            )
        except SpotV7ZenoLedgerReplayObservationErrorV1:
            raise
        except (KeyError, TypeError, ValueError) as exc:
            raise SpotV7ZenoLedgerReplayObservationErrorV1(
                _replay_reject_code(exc)
            ) from exc

    def _authenticate_exact(
        self,
        *,
        header: object,
        body: object,
        pre_snapshot: object,
        parent_header: object | None,
    ) -> _AuthenticatedReplayBoundBlockObservationV1:
        """Run the exact replay after the public boundary installs typed rejects."""

        header_value = _snapshot_plain_dict(header, name="replay header")
        body_value = _snapshot_plain_dict(body, name="replay body")
        pre_snapshot_value = _snapshot_plain_dict(pre_snapshot, name="pre-state snapshot")
        parent_value = (
            None
            if parent_header is None
            else _snapshot_plain_dict(parent_header, name="parent header")
        )
        config_document = _decode_exact_dict(
            self._config_document_bytes,
            name="sealed engine config",
        )
        config, canonical_config_document = parse_replay_engine_config_v0(
            config_document
        )
        canonical_config_bytes = canonical_json_bytes_v0(canonical_config_document)
        if canonical_config_bytes != self._config_document_bytes:
            raise ValueError("sealed engine config is not canonical")
        if replay_engine_config_digest_v0(canonical_config_document) != self._config_digest:
            raise ValueError("sealed engine config_digest mismatch")
        next_state, replayed_body, receipts = _replay_bound_block_details_v0(
            header=header_value,
            body=body_value,
            pre_snapshot=pre_snapshot_value,
            config=config,
            config_digest=self._config_digest,
            parent_header=parent_value,
            carried_state=None,
        )
        if replayed_body != body_value:
            raise SpotV7ZenoLedgerReplayObservationErrorV1("replayed_body")
        projection_payload = _build_projection_payload(
            header=header_value,
            body=body_value,
            pre_snapshot=pre_snapshot_value,
            parent_header=parent_value,
            config_document=canonical_config_document,
            config_digest=self._config_digest,
            next_state_root=dex_state_root_v0(next_state),
            receipts=receipts,
        )
        evidence_bytes = canonical_json_bytes_v0(
            {
                "schema": SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1,
                "profile": SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1,
                "status": "authenticated_deterministic_replay",
                "projection": projection_payload,
                "scope": {
                    "body_settlement_envelopes": "required_empty",
                    "proof_receipt_authentication": "not_established",
                    "spot_v7_settlement_semantics": "not_established",
                    "settlement_authority": "false",
                    "production_authority": "false",
                },
            }
        )
        if not evidence_bytes or len(evidence_bytes) > _MAX_REPLAY_OBSERVATION_EVIDENCE_BYTES_V1:
            raise ValueError("canonical replay observation evidence exceeds its byte bound")
        projection = _ReplayBoundBlockProjectionV1(
            **projection_payload,
            observation_evidence_root=_sha256(evidence_bytes),
        )
        return _AuthenticatedReplayBoundBlockObservationV1(
            projection,
            exact_header_bytes=canonical_json_bytes_v0(header_value),
            exact_body_bytes=canonical_json_bytes_v0(body_value),
            exact_evidence_bytes=evidence_bytes,
            seal=_REPLAY_BOUND_OBSERVATION_SEAL_V1,
        )

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _build_projection_payload(
    *,
    header: dict[str, Any],
    body: dict[str, Any],
    pre_snapshot: dict[str, Any],
    parent_header: dict[str, Any] | None,
    config_document: dict[str, Any],
    config_digest: str,
    next_state_root: str,
    receipts: tuple[dict[str, Any], ...],
) -> dict[str, Any]:
    rejections = body["evidence"]["rejection_receipts"]
    proof_receipts = body["evidence"]["proof_receipts"]
    body_committed_proof_journal_hash = _parse_body_proof_receipt_projection(
        proof_receipts
    )
    for name, values in (
        ("replayed receipts", receipts),
        ("replayed rejections", rejections),
        ("committed proof receipts", proof_receipts),
    ):
        if len(values) > MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1:
            raise ValueError(f"{name} exceed the governed count bound")
    return {
        "chain_id": header["chain_id"],
        "height": header["height"],
        "header_hash": canonical_header_hash_v0(header),
        "prior_header_hash": header["prev_header_hash"],
        "parent_header_hash": (
            None if parent_header is None else canonical_header_hash_v0(parent_header)
        ),
        "body_root": canonical_body_root_v0(body),
        "body_sha256": _sha256(canonical_json_bytes_v0(body)),
        "config_digest": config_digest,
        "config_document_root": hash_v0(
            SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1,
            config_document,
        ),
        "pre_state_root": header["pre_state_root"],
        "post_state_root": next_state_root,
        "pre_snapshot_sha256": _sha256(canonical_json_bytes_v0(pre_snapshot)),
        "ingress_root": header["ingress_root"],
        "transaction_root": header["tx_root"],
        "evidence_root": header["evidence_root"],
        "replayed_receipts_root": hash_v0(
            SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1,
            {"receipts": list(receipts)},
        ),
        "replayed_rejections_root": hash_v0(
            SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1,
            {"rejection_receipts": rejections},
        ),
        "committed_proof_receipts_root": hash_v0(
            SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1,
            {"proof_receipts": proof_receipts},
        ),
        "body_committed_proof_journal_hash": body_committed_proof_journal_hash,
        "replayed_receipt_count": len(receipts),
        "replayed_rejection_count": len(rejections),
        "committed_proof_receipt_count": len(proof_receipts),
    }


def _parse_body_proof_receipt_projection(value: object) -> str:
    if type(value) is not list:
        raise TypeError("body proof receipts must be an exact list")
    if len(value) != SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1:
        raise ValueError("body proof receipt projection count mismatch")
    receipt = value[0]
    if type(receipt) is not dict:
        raise TypeError("body proof receipt projection must be an exact dict")
    expected_keys = {"schema", "proof_journal_hash"}
    if set(receipt) != expected_keys:
        raise ValueError("body proof receipt projection keys mismatch")
    if (
        receipt["schema"]
        != SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1
    ):
        raise ValueError("body proof receipt projection schema mismatch")
    journal_hash = receipt["proof_journal_hash"]
    if type(journal_hash) is not str:
        raise TypeError("body proof receipt proof_journal_hash must be a str")
    _hash_bytes(journal_hash, name="body proof receipt proof_journal_hash")
    return journal_hash


def _require_replay_observation(
    value: object,
) -> _AuthenticatedReplayBoundBlockObservationV1:
    if type(value) is not _AuthenticatedReplayBoundBlockObservationV1:
        raise TypeError(
            "replay_observation must be the exact private replay-bound observation"
        )
    if not value._has_private_seal():
        raise TypeError("replay_observation lacks its module-private seal")
    return value


def _decode_exact_dict(value: bytes, *, name: str) -> dict[str, Any]:
    decoded = json.loads(value)
    if type(decoded) is not dict:
        raise TypeError(f"{name} did not decode to an exact dict")
    if canonical_json_bytes_v0(decoded) != value:
        raise ValueError(f"{name} is not canonical JSON")
    return decoded


def _replay_reject_code(exc: Exception) -> str:
    message = str(exc)
    if "proof receipt" in message:
        return "proof_receipt_projection"
    if "config_digest" in message or "engine config" in message:
        return "config_digest"
    if "rejection receipts" in message:
        return "rejection_receipts"
    if "header " in message and "mismatch" in message:
        return "body_binding"
    if "body" in message and "state" not in message:
        return "body_binding"
    if "state" in message or "parent" in message:
        return "state_continuity"
    return "deterministic_replay"


def _sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


__all__ = [
    "SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1",
    "SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1",
    "SpotV7ZenoLedgerReplayBoundObservationAdapterV1",
    "SpotV7ZenoLedgerReplayObservationErrorV1",
]
