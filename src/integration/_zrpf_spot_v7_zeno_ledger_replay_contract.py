"""Authority-neutral contract for one replay-bound ZenoLedger observation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
)

SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_replay_bound_observation/v1"
)
SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1: Final = (
    "deterministic_transaction_body_replay_v0"
)
SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1: Final = (
    "zrpf_spot_v7_zeno_ledger_config_document_v1"
)
SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1: Final = (
    "zrpf_spot_v7_zeno_ledger_replayed_receipts_v1"
)
SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1: Final = (
    "zrpf_spot_v7_zeno_ledger_replayed_rejections_v1"
)
SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1: Final = (
    "zrpf_spot_v7_zeno_ledger_committed_proof_receipts_v1"
)
SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1: Final = (
    "zenodex/zrpf/spot_v7/zeno_ledger_body_proof_receipt_projection/v1"
)
MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1: Final = 65_536
SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1: Final = 1


class SpotV7ZenoLedgerReplayObservationErrorV1(ValueError):
    """Stable fail-closed rejection before replay observation sealing."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_ZENO_LEDGER_REPLAY_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class _ReplayBoundBlockProjectionV1:
    """Plain immutable projection; this type alone carries no authority."""

    chain_id: str
    height: int
    header_hash: str
    prior_header_hash: str
    parent_header_hash: str | None
    body_root: str
    body_sha256: str
    config_digest: str
    config_document_root: str
    pre_state_root: str
    post_state_root: str
    pre_snapshot_sha256: str
    ingress_root: str
    transaction_root: str
    evidence_root: str
    replayed_receipts_root: str
    replayed_rejections_root: str
    committed_proof_receipts_root: str
    body_committed_proof_journal_hash: str
    replayed_receipt_count: int
    replayed_rejection_count: int
    committed_proof_receipt_count: int
    observation_evidence_root: str

    def __post_init__(self) -> None:
        if type(self.chain_id) is not str or not self.chain_id:
            raise ValueError("replay observation chain_id must be a non-empty str")
        _require_uint(self.height, name="replay observation height", maximum=MAX_U64)
        for name, value in (
            ("header_hash", self.header_hash),
            ("prior_header_hash", self.prior_header_hash),
            ("body_root", self.body_root),
            ("body_sha256", self.body_sha256),
            ("config_digest", self.config_digest),
            ("config_document_root", self.config_document_root),
            ("pre_state_root", self.pre_state_root),
            ("post_state_root", self.post_state_root),
            ("pre_snapshot_sha256", self.pre_snapshot_sha256),
            ("ingress_root", self.ingress_root),
            ("transaction_root", self.transaction_root),
            ("evidence_root", self.evidence_root),
            ("replayed_receipts_root", self.replayed_receipts_root),
            ("replayed_rejections_root", self.replayed_rejections_root),
            ("committed_proof_receipts_root", self.committed_proof_receipts_root),
            (
                "body_committed_proof_journal_hash",
                self.body_committed_proof_journal_hash,
            ),
            ("observation_evidence_root", self.observation_evidence_root),
        ):
            _hash_bytes(value, name=f"replay observation {name}")
        if self.parent_header_hash is not None:
            _hash_bytes(
                self.parent_header_hash,
                name="replay observation parent_header_hash",
            )
        for count_name, count_value in (
            ("replayed_receipt_count", self.replayed_receipt_count),
            ("replayed_rejection_count", self.replayed_rejection_count),
            ("committed_proof_receipt_count", self.committed_proof_receipt_count),
        ):
            _require_uint(
                count_value,
                name=f"replay observation {count_name}",
                maximum=MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1,
            )
        if self.replayed_rejection_count > self.replayed_receipt_count:
            raise ValueError("replay rejection count exceeds replayed receipt count")


__all__ = [
    "MAX_SPOT_V7_ZENO_LEDGER_REPLAY_RECEIPTS_V1",
    "SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_COUNT_V1",
    "SPOT_V7_ZENO_LEDGER_BODY_PROOF_RECEIPT_PROJECTION_SCHEMA_V1",
    "SPOT_V7_ZENO_LEDGER_CONFIG_DOCUMENT_ROOT_DOMAIN_V1",
    "SPOT_V7_ZENO_LEDGER_PROOF_RECEIPTS_ROOT_DOMAIN_V1",
    "SPOT_V7_ZENO_LEDGER_REJECTIONS_ROOT_DOMAIN_V1",
    "SPOT_V7_ZENO_LEDGER_RECEIPTS_ROOT_DOMAIN_V1",
    "SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_PROFILE_V1",
    "SPOT_V7_ZENO_LEDGER_REPLAY_OBSERVATION_SCHEMA_V1",
    "SpotV7ZenoLedgerReplayObservationErrorV1",
]
