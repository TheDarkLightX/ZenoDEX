"""Keyed Tau retrieval helpers for export acceptance receipts."""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Mapping, Protocol, Sequence

from src.integration.zeno_ledger_app_hash_history import (
    verify_app_hash_history_merkle_proof_for_range_v0,
    verify_app_hash_history_merkle_proof_v0,
)
from src.integration.zeno_ledger_tau_export import (
    TauExportAcceptanceReceiptV0,
    build_tau_export_acceptance_receipt_v0,
    validate_tau_export_acceptance_receipt_v0,
    validate_tau_export_packet_v0,
)
from src.integration.zeno_ledger_v0 import ROOT_NBYTES, hash_v0
from src.integration.zeno_ledger_watcher import (
    validate_compact_watcher_attestation_v0,
    validate_watcher_attestation_v0,
)
from src.integration.zeno_ledger_watcher_quorum import (
    SIGNED_WATCHER_QUORUM_STATE_LANE_KIND_V0,
    build_signed_watcher_quorum_state_leaf_v0,
    verify_compact_watcher_quorum_certificate_v0,
    verify_signed_compact_watcher_quorum_certificate_v0,
)
from src.state.app_root import verify_app_root_leaf
from src.state.canonical import canonical_hex_fixed_allow_0x

MAX_TAU_RETRIEVAL_RECORD_BYTES_V0 = 1_048_576
STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0 = (
    "zeno_ledger_state_root_bound_signed_watcher_quorum_app_hash_history_merkle_v0"
)
TAU_STATE_ROOT_BOUND_WATCHER_READONLY_FINALITY_RECEIPT_SCHEMA_V0 = (
    "zenodex.tau.state_root_bound_watcher_readonly_finality_receipt.v0"
)
TAU_STATE_ROOT_BOUND_WATCHER_READONLY_FINALITY_RECEIPT_STATUS_V0 = (
    "read_only_finality_confirmed"
)


class TauRecordReaderV0(Protocol):
    def read_tau_record(self, key: str) -> Mapping[str, Any] | str | bytes | bytearray:
        """Return the raw record stored at `key`, or raise on a missing record."""


class TauSnapshotRpcClientV0(Protocol):
    def getappstate(self, *, full: bool = False) -> str:
        """Return the Tau app-state RPC payload as JSON text."""

    def getstateproof(self, *, full: bool = False) -> str:
        """Return the Tau state-proof RPC payload as JSON text."""


class TauStateProofVerifierV0(Protocol):
    def verify_tau_state_proof(self, request: Mapping[str, Any]) -> Mapping[str, Any]:
        """Return a fail-closed verifier receipt for a Tau state-proof request."""


@dataclass(frozen=True)
class TauFinalityPolicyV0:
    min_confirmations: int
    max_staleness_blocks: int
    accepted_chain_id: str | None = None

    def __post_init__(self) -> None:
        min_confirmations = _require_nonnegative_int(
            self.min_confirmations,
            name="finality_policy.min_confirmations",
        )
        max_staleness_blocks = _require_nonnegative_int(
            self.max_staleness_blocks,
            name="finality_policy.max_staleness_blocks",
        )
        if min_confirmations > max_staleness_blocks:
            raise ValueError("finality_policy min_confirmations must be <= max_staleness_blocks")
        if self.accepted_chain_id is not None:
            _require_nonempty_str(self.accepted_chain_id, name="finality_policy.accepted_chain_id")

    def as_receipt(self) -> Mapping[str, Any]:
        return {
            "schema": "zenodex.tau.finality_policy.v0",
            "min_confirmations": self.min_confirmations,
            "max_staleness_blocks": self.max_staleness_blocks,
            "accepted_chain_id": self.accepted_chain_id,
        }


@dataclass(frozen=True)
class TauRetrievedStateProofRecordsV0:
    tau_state_hash: str
    tau_state_key: str
    state_proof_key: str
    tau_state: Mapping[str, Any]
    state_proof: Mapping[str, Any]


@dataclass(frozen=True)
class TauRpcStateProofSnapshotReaderV0:
    """Immutable keyed reader built from one stabilized Tau RPC snapshot."""

    tau_state_hash: str
    app_hash: str
    tau_state_key: str
    state_proof_key: str
    tau_state: Mapping[str, Any]
    state_proof: Mapping[str, Any]

    @classmethod
    def from_client(
        cls,
        client: TauSnapshotRpcClientV0,
        *,
        max_record_bytes: int = MAX_TAU_RETRIEVAL_RECORD_BYTES_V0,
    ) -> "TauRpcStateProofSnapshotReaderV0":
        app_state_before = _decode_tau_record(
            _call_tau_rpc_json(client.getappstate, full=True),
            name="getappstate(before)",
            max_record_bytes=max_record_bytes,
        )
        state_proof = _decode_tau_record(
            _call_tau_rpc_json(client.getstateproof, full=True),
            name="getstateproof",
            max_record_bytes=max_record_bytes,
        )
        app_state_after = _decode_tau_record(
            _call_tau_rpc_json(client.getappstate, full=True),
            name="getappstate(after)",
            max_record_bytes=max_record_bytes,
        )
        app_hash_before = _extract_app_hash(
            app_state_before,
            name="getappstate(before).app_hash",
        )
        app_hash_after = _extract_app_hash(
            app_state_after,
            name="getappstate(after).app_hash",
        )
        if app_hash_before != app_hash_after:
            raise ValueError("Tau app_hash changed during state-proof snapshot")
        if state_proof.get("present") is not True:
            raise ValueError("Tau state_proof.present must be true")
        proof_app_hash = state_proof.get("app_hash")
        if proof_app_hash is not None:
            normalized_proof_app_hash = _normalize_tau_state_hash(
                proof_app_hash,
                name="getstateproof.app_hash",
            )
            if normalized_proof_app_hash != app_hash_before:
                raise ValueError("Tau state proof app_hash does not match app-state snapshot")
        tau_state_hash = _normalize_tau_state_hash(
            _extract_state_proof_hash(state_proof),
            name="getstateproof.state_hash",
        )
        return cls(
            tau_state_hash=tau_state_hash,
            app_hash=app_hash_before,
            tau_state_key=tau_state_record_key_v0(tau_state_hash),
            state_proof_key=tau_state_proof_record_key_v0(tau_state_hash),
            tau_state=dict(app_state_after),
            state_proof=dict(state_proof),
        )

    def read_tau_record(self, key: str) -> Mapping[str, Any]:
        if key == self.tau_state_key:
            return self.tau_state
        if key == self.state_proof_key:
            return self.state_proof
        raise KeyError(key)

    def verified_by(
        self,
        verifier: TauStateProofVerifierV0,
        *,
        block: Mapping[str, Any] | None = None,
        context: Mapping[str, Any] | None = None,
    ) -> "TauVerifiedStateProofSnapshotReaderV0":
        request = build_tau_state_proof_verification_request_v0(
            snapshot=self,
            block=block,
            context=context,
        )
        receipt = _verify_tau_state_proof_request(
            verifier=verifier,
            request=request,
            expected_state_hash=self.tau_state_hash,
            expected_app_hash=self.app_hash,
        )
        return TauVerifiedStateProofSnapshotReaderV0(
            snapshot=self,
            verification_request=request,
            verification_receipt=receipt,
        )


@dataclass(frozen=True)
class TauVerifiedStateProofSnapshotReaderV0:
    """Keyed Tau snapshot reader whose state proof has a bound verifier receipt."""

    snapshot: TauRpcStateProofSnapshotReaderV0
    verification_request: Mapping[str, Any]
    verification_receipt: Mapping[str, Any]

    @property
    def tau_state_hash(self) -> str:
        return self.snapshot.tau_state_hash

    @property
    def app_hash(self) -> str:
        return self.snapshot.app_hash

    @property
    def tau_state_key(self) -> str:
        return self.snapshot.tau_state_key

    @property
    def state_proof_key(self) -> str:
        return self.snapshot.state_proof_key

    @property
    def tau_state(self) -> Mapping[str, Any]:
        return self.snapshot.tau_state

    @property
    def state_proof(self) -> Mapping[str, Any]:
        return self.snapshot.state_proof

    def read_tau_record(self, key: str) -> Mapping[str, Any]:
        return self.snapshot.read_tau_record(key)

    def finalized_by(
        self,
        *,
        checkpoint: Mapping[str, Any],
        policy: TauFinalityPolicyV0,
    ) -> "TauFinalizedStateProofSnapshotReaderV0":
        finality_receipt = _validate_tau_finality_checkpoint_v0(
            verified_snapshot=self,
            checkpoint=checkpoint,
            policy=policy,
        )
        return TauFinalizedStateProofSnapshotReaderV0(
            verified_snapshot=self,
            finality_policy=policy.as_receipt(),
            finality_checkpoint=finality_receipt,
        )


@dataclass(frozen=True)
class TauFinalizedStateProofSnapshotReaderV0:
    """Verified snapshot reader additionally accepted by a local finality policy."""

    verified_snapshot: TauVerifiedStateProofSnapshotReaderV0
    finality_policy: Mapping[str, Any]
    finality_checkpoint: Mapping[str, Any]

    @property
    def tau_state_hash(self) -> str:
        return self.verified_snapshot.tau_state_hash

    @property
    def app_hash(self) -> str:
        return self.verified_snapshot.app_hash

    @property
    def tau_state_key(self) -> str:
        return self.verified_snapshot.tau_state_key

    @property
    def state_proof_key(self) -> str:
        return self.verified_snapshot.state_proof_key

    @property
    def tau_state(self) -> Mapping[str, Any]:
        return self.verified_snapshot.tau_state

    @property
    def state_proof(self) -> Mapping[str, Any]:
        return self.verified_snapshot.state_proof

    @property
    def verification_request(self) -> Mapping[str, Any]:
        return self.verified_snapshot.verification_request

    @property
    def verification_receipt(self) -> Mapping[str, Any]:
        return self.verified_snapshot.verification_receipt

    def read_tau_record(self, key: str) -> Mapping[str, Any]:
        return self.verified_snapshot.read_tau_record(key)


def build_tau_finality_checkpoint_from_watcher_attestations_v0(
    *,
    watcher_attestations: Sequence[Mapping[str, Any]],
    verify_reports: Sequence[Mapping[str, Any]],
    state_hash: str,
    profile: Mapping[str, Any] | None = None,
    required_watcher_count: int = 1,
) -> Mapping[str, Any]:
    """Build a Tau finality checkpoint from locally validated watcher reports.

    The current watcher report commits to the final root at its range tip, so
    this checkpoint finalizes exactly `to_height`. Historical confirmations
    require a richer per-height app-hash or finality proof artifact.
    """

    if isinstance(required_watcher_count, bool) or not isinstance(required_watcher_count, int):
        raise ValueError("required_watcher_count must be a positive int")
    if required_watcher_count <= 0:
        raise ValueError("required_watcher_count must be a positive int")
    if len(watcher_attestations) != len(verify_reports):
        raise ValueError("watcher_attestations and verify_reports length mismatch")
    if len(watcher_attestations) < required_watcher_count:
        raise ValueError("watcher quorum below required_watcher_count")

    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau watcher finality state_hash",
    )
    entries: list[dict[str, Any]] = []
    seen_watchers: set[str] = set()
    for index, (raw_attestation, raw_report) in enumerate(zip(watcher_attestations, verify_reports, strict=True)):
        attestation = _require_mapping(raw_attestation, name=f"watcher_attestations[{index}]")
        report = _require_mapping(raw_report, name=f"verify_reports[{index}]")
        validate_watcher_attestation_v0(
            attestation=attestation,
            verify_report=report,
            profile=profile,
        )
        watcher_id = _require_nonempty_str(
            attestation.get("watcher_id"),
            name=f"watcher_attestations[{index}].watcher_id",
        )
        if watcher_id in seen_watchers:
            raise ValueError("watcher quorum duplicate watcher_id")
        seen_watchers.add(watcher_id)
        checked_heights = _require_nonempty_int_list(
            attestation.get("checked_heights"),
            name=f"watcher_attestations[{index}].checked_heights",
        )
        from_height = _require_nonnegative_int(
            attestation.get("from_height"),
            name=f"watcher_attestations[{index}].from_height",
        )
        to_height = _require_nonnegative_int(
            attestation.get("to_height"),
            name=f"watcher_attestations[{index}].to_height",
        )
        if checked_heights[0] != from_height or checked_heights[-1] != to_height:
            raise ValueError("watcher checked_heights must match attested range")
        entries.append(
            {
                "watcher_id": watcher_id,
                "from_height": from_height,
                "to_height": to_height,
                "checked_heights": checked_heights,
                "chain_id": _require_nonempty_str(
                    attestation.get("chain_id"),
                    name=f"watcher_attestations[{index}].chain_id",
                ),
                "last_header_hash": _normalize_tau_state_hash(
                    attestation.get("last_header_hash"),
                    name=f"watcher_attestations[{index}].last_header_hash",
                ),
                "last_post_state_root": _normalize_tau_state_hash(
                    attestation.get("last_post_state_root"),
                    name=f"watcher_attestations[{index}].last_post_state_root",
                ),
                "last_app_hash": _normalize_tau_state_hash(
                    attestation.get("last_app_hash"),
                    name=f"watcher_attestations[{index}].last_app_hash",
                ),
                "attestation_hash": _normalize_tau_state_hash(
                    attestation.get("attestation_hash"),
                    name=f"watcher_attestations[{index}].attestation_hash",
                ),
                "verify_report_hash": _normalize_tau_state_hash(
                    attestation.get("verify_report_hash"),
                    name=f"watcher_attestations[{index}].verify_report_hash",
                ),
            }
        )

    entries.sort(key=lambda item: item["watcher_id"])
    first = entries[0]
    agreement_key = (
        first["from_height"],
        first["to_height"],
        tuple(first["checked_heights"]),
        first["chain_id"],
        first["last_header_hash"],
        first["last_post_state_root"],
        first["last_app_hash"],
    )
    for entry in entries[1:]:
        current_key = (
            entry["from_height"],
            entry["to_height"],
            tuple(entry["checked_heights"]),
            entry["chain_id"],
            entry["last_header_hash"],
            entry["last_post_state_root"],
            entry["last_app_hash"],
        )
        if current_key != agreement_key:
            raise ValueError("Tau watcher finality attestations must agree on range and final roots")

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": first["chain_id"],
        "snapshot_height": first["to_height"],
        "latest_height": first["to_height"],
        "finalized_height": first["to_height"],
        "state_hash": normalized_state_hash,
        "app_hash": first["last_app_hash"],
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_watcher_quorum_v0",
        "watcher_count": len(entries),
        "required_watcher_count": required_watcher_count,
        "watcher_ids": [entry["watcher_id"] for entry in entries],
        "attestation_hashes": [entry["attestation_hash"] for entry in entries],
        "verify_report_hashes": [entry["verify_report_hash"] for entry in entries],
        "checked_heights": list(first["checked_heights"]),
        "last_header_hash": first["last_header_hash"],
        "last_post_state_root": first["last_post_state_root"],
    }
    checkpoint_hash = hash_v0("tau_watcher_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_watcher_quorum:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0("tau_watcher_finality_checkpoint_v0", body)
    return body


def build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
    *,
    watcher_attestations: Sequence[Mapping[str, Any]],
    verify_reports: Sequence[Mapping[str, Any]],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any] | None = None,
    required_watcher_count: int = 1,
) -> Mapping[str, Any]:
    """Build a finality checkpoint for a historical height in a watcher range.

    This consumes `verify_report.app_hashes_by_height`, which is covered by the
    watcher attestation's `verify_report_hash`. The history must cover exactly
    the checked range, in order, and its final row must match `last_app_hash`.
    """

    if isinstance(required_watcher_count, bool) or not isinstance(required_watcher_count, int):
        raise ValueError("required_watcher_count must be a positive int")
    if required_watcher_count <= 0:
        raise ValueError("required_watcher_count must be a positive int")
    if len(watcher_attestations) != len(verify_reports):
        raise ValueError("watcher_attestations and verify_reports length mismatch")
    if len(watcher_attestations) < required_watcher_count:
        raise ValueError("watcher quorum below required_watcher_count")

    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau watcher history finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau watcher history finality snapshot_height",
    )
    entries: list[dict[str, Any]] = []
    seen_watchers: set[str] = set()
    for index, (raw_attestation, raw_report) in enumerate(zip(watcher_attestations, verify_reports, strict=True)):
        attestation = _require_mapping(raw_attestation, name=f"watcher_attestations[{index}]")
        report = _require_mapping(raw_report, name=f"verify_reports[{index}]")
        validate_watcher_attestation_v0(
            attestation=attestation,
            verify_report=report,
            profile=profile,
        )
        watcher_id = _require_nonempty_str(
            attestation.get("watcher_id"),
            name=f"watcher_attestations[{index}].watcher_id",
        )
        if watcher_id in seen_watchers:
            raise ValueError("watcher quorum duplicate watcher_id")
        seen_watchers.add(watcher_id)
        checked_heights = _require_nonempty_int_list(
            attestation.get("checked_heights"),
            name=f"watcher_attestations[{index}].checked_heights",
        )
        from_height = _require_nonnegative_int(
            attestation.get("from_height"),
            name=f"watcher_attestations[{index}].from_height",
        )
        to_height = _require_nonnegative_int(
            attestation.get("to_height"),
            name=f"watcher_attestations[{index}].to_height",
        )
        if checked_heights[0] != from_height or checked_heights[-1] != to_height:
            raise ValueError("watcher checked_heights must match attested range")
        last_app_hash = _normalize_tau_state_hash(
            attestation.get("last_app_hash"),
            name=f"watcher_attestations[{index}].last_app_hash",
        )
        history = _extract_app_hash_history_rows(
            report,
            checked_heights=checked_heights,
            last_app_hash=last_app_hash,
            name=f"verify_reports[{index}].app_hashes_by_height",
        )
        if selected_height not in history["by_height"]:
            raise ValueError("snapshot_height must be covered by watcher app_hash history")
        entries.append(
            {
                "watcher_id": watcher_id,
                "from_height": from_height,
                "to_height": to_height,
                "checked_heights": checked_heights,
                "chain_id": _require_nonempty_str(
                    attestation.get("chain_id"),
                    name=f"watcher_attestations[{index}].chain_id",
                ),
                "last_header_hash": _normalize_tau_state_hash(
                    attestation.get("last_header_hash"),
                    name=f"watcher_attestations[{index}].last_header_hash",
                ),
                "last_post_state_root": _normalize_tau_state_hash(
                    attestation.get("last_post_state_root"),
                    name=f"watcher_attestations[{index}].last_post_state_root",
                ),
                "last_app_hash": last_app_hash,
                "selected_app_hash": history["by_height"][selected_height],
                "app_hash_history_hash": history["history_hash"],
                "attestation_hash": _normalize_tau_state_hash(
                    attestation.get("attestation_hash"),
                    name=f"watcher_attestations[{index}].attestation_hash",
                ),
                "verify_report_hash": _normalize_tau_state_hash(
                    attestation.get("verify_report_hash"),
                    name=f"watcher_attestations[{index}].verify_report_hash",
                ),
            }
        )

    entries.sort(key=lambda item: item["watcher_id"])
    first = entries[0]
    agreement_key = (
        first["from_height"],
        first["to_height"],
        tuple(first["checked_heights"]),
        first["chain_id"],
        first["last_header_hash"],
        first["last_post_state_root"],
        first["last_app_hash"],
        first["selected_app_hash"],
        first["app_hash_history_hash"],
    )
    for entry in entries[1:]:
        current_key = (
            entry["from_height"],
            entry["to_height"],
            tuple(entry["checked_heights"]),
            entry["chain_id"],
            entry["last_header_hash"],
            entry["last_post_state_root"],
            entry["last_app_hash"],
            entry["selected_app_hash"],
            entry["app_hash_history_hash"],
        )
        if current_key != agreement_key:
            raise ValueError("Tau watcher history attestations must agree on range and app-hash history")

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": first["chain_id"],
        "snapshot_height": selected_height,
        "latest_height": first["to_height"],
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": first["selected_app_hash"],
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_watcher_app_hash_history_v0",
        "watcher_count": len(entries),
        "required_watcher_count": required_watcher_count,
        "watcher_ids": [entry["watcher_id"] for entry in entries],
        "attestation_hashes": [entry["attestation_hash"] for entry in entries],
        "verify_report_hashes": [entry["verify_report_hash"] for entry in entries],
        "app_hash_history_hashes": [entry["app_hash_history_hash"] for entry in entries],
        "checked_heights": list(first["checked_heights"]),
        "last_header_hash": first["last_header_hash"],
        "last_post_state_root": first["last_post_state_root"],
        "range_tip_app_hash": first["last_app_hash"],
    }
    checkpoint_hash = hash_v0("tau_watcher_app_hash_history_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_watcher_app_hash_history:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0("tau_watcher_app_hash_history_finality_checkpoint_v0", body)
    return body


def build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
    *,
    watcher_attestations: Sequence[Mapping[str, Any]],
    verify_reports: Sequence[Mapping[str, Any]],
    app_hash_history_proofs: Sequence[Mapping[str, Any]],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any] | None = None,
    required_watcher_count: int = 1,
) -> Mapping[str, Any]:
    """Build a historical finality checkpoint from compact app-hash proofs.

    The verify report supplies a watcher-bound `app_hash_history_root`; the
    caller supplies one Merkle inclusion proof for the selected snapshot height.
    Full `app_hashes_by_height` rows are not required by this consumer.
    """

    if isinstance(required_watcher_count, bool) or not isinstance(required_watcher_count, int):
        raise ValueError("required_watcher_count must be a positive int")
    if required_watcher_count <= 0:
        raise ValueError("required_watcher_count must be a positive int")
    if len(watcher_attestations) != len(verify_reports):
        raise ValueError("watcher_attestations and verify_reports length mismatch")
    if len(watcher_attestations) != len(app_hash_history_proofs):
        raise ValueError("watcher_attestations and app_hash_history_proofs length mismatch")
    if len(watcher_attestations) < required_watcher_count:
        raise ValueError("watcher quorum below required_watcher_count")

    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau watcher history proof finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau watcher history proof finality snapshot_height",
    )
    entries: list[dict[str, Any]] = []
    seen_watchers: set[str] = set()
    for index, (raw_attestation, raw_report, raw_proof) in enumerate(
        zip(watcher_attestations, verify_reports, app_hash_history_proofs, strict=True)
    ):
        attestation = _require_mapping(raw_attestation, name=f"watcher_attestations[{index}]")
        report = _require_mapping(raw_report, name=f"verify_reports[{index}]")
        proof = _require_mapping(raw_proof, name=f"app_hash_history_proofs[{index}]")
        validate_watcher_attestation_v0(
            attestation=attestation,
            verify_report=report,
            profile=profile,
        )
        watcher_id = _require_nonempty_str(
            attestation.get("watcher_id"),
            name=f"watcher_attestations[{index}].watcher_id",
        )
        if watcher_id in seen_watchers:
            raise ValueError("watcher quorum duplicate watcher_id")
        seen_watchers.add(watcher_id)
        checked_heights = _require_nonempty_int_list(
            attestation.get("checked_heights"),
            name=f"watcher_attestations[{index}].checked_heights",
        )
        from_height = _require_nonnegative_int(
            attestation.get("from_height"),
            name=f"watcher_attestations[{index}].from_height",
        )
        to_height = _require_nonnegative_int(
            attestation.get("to_height"),
            name=f"watcher_attestations[{index}].to_height",
        )
        if checked_heights[0] != from_height or checked_heights[-1] != to_height:
            raise ValueError("watcher checked_heights must match attested range")
        last_app_hash = _normalize_tau_state_hash(
            attestation.get("last_app_hash"),
            name=f"watcher_attestations[{index}].last_app_hash",
        )
        app_hash_history_root = _normalize_tau_state_hash(
            report.get("app_hash_history_root"),
            name=f"verify_reports[{index}].app_hash_history_root",
        )
        selected_app_hash = verify_app_hash_history_merkle_proof_v0(
            proof,
            expected_root=app_hash_history_root,
            checked_heights=checked_heights,
            snapshot_height=selected_height,
            last_app_hash=last_app_hash,
        )
        entries.append(
            {
                "watcher_id": watcher_id,
                "from_height": from_height,
                "to_height": to_height,
                "checked_heights": checked_heights,
                "chain_id": _require_nonempty_str(
                    attestation.get("chain_id"),
                    name=f"watcher_attestations[{index}].chain_id",
                ),
                "last_header_hash": _normalize_tau_state_hash(
                    attestation.get("last_header_hash"),
                    name=f"watcher_attestations[{index}].last_header_hash",
                ),
                "last_post_state_root": _normalize_tau_state_hash(
                    attestation.get("last_post_state_root"),
                    name=f"watcher_attestations[{index}].last_post_state_root",
                ),
                "last_app_hash": last_app_hash,
                "selected_app_hash": selected_app_hash,
                "app_hash_history_root": app_hash_history_root,
                "app_hash_history_proof_hash": hash_v0(
                    "tau_watcher_app_hash_history_merkle_proof_v0",
                    proof,
                ),
                "attestation_hash": _normalize_tau_state_hash(
                    attestation.get("attestation_hash"),
                    name=f"watcher_attestations[{index}].attestation_hash",
                ),
                "verify_report_hash": _normalize_tau_state_hash(
                    attestation.get("verify_report_hash"),
                    name=f"watcher_attestations[{index}].verify_report_hash",
                ),
            }
        )

    entries.sort(key=lambda item: item["watcher_id"])
    first = entries[0]
    agreement_key = (
        first["from_height"],
        first["to_height"],
        tuple(first["checked_heights"]),
        first["chain_id"],
        first["last_header_hash"],
        first["last_post_state_root"],
        first["last_app_hash"],
        first["selected_app_hash"],
        first["app_hash_history_root"],
    )
    for entry in entries[1:]:
        current_key = (
            entry["from_height"],
            entry["to_height"],
            tuple(entry["checked_heights"]),
            entry["chain_id"],
            entry["last_header_hash"],
            entry["last_post_state_root"],
            entry["last_app_hash"],
            entry["selected_app_hash"],
            entry["app_hash_history_root"],
        )
        if current_key != agreement_key:
            raise ValueError("Tau watcher history proof attestations must agree on range and app-hash root")

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": first["chain_id"],
        "snapshot_height": selected_height,
        "latest_height": first["to_height"],
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": first["selected_app_hash"],
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_watcher_app_hash_history_merkle_v0",
        "watcher_count": len(entries),
        "required_watcher_count": required_watcher_count,
        "watcher_ids": [entry["watcher_id"] for entry in entries],
        "attestation_hashes": [entry["attestation_hash"] for entry in entries],
        "verify_report_hashes": [entry["verify_report_hash"] for entry in entries],
        "app_hash_history_roots": [entry["app_hash_history_root"] for entry in entries],
        "app_hash_history_proof_hashes": [entry["app_hash_history_proof_hash"] for entry in entries],
        "checked_heights": list(first["checked_heights"]),
        "last_header_hash": first["last_header_hash"],
        "last_post_state_root": first["last_post_state_root"],
        "range_tip_app_hash": first["last_app_hash"],
    }
    checkpoint_hash = hash_v0("tau_watcher_app_hash_history_merkle_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_watcher_app_hash_history_merkle:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0("tau_watcher_app_hash_history_merkle_finality_checkpoint_v0", body)
    return body


def build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
    *,
    watcher_attestations: Sequence[Mapping[str, Any]],
    verify_reports: Sequence[Mapping[str, Any]],
    app_hash_history_proofs: Sequence[Mapping[str, Any]],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any] | None = None,
    required_watcher_count: int = 1,
) -> Mapping[str, Any]:
    """Build a historical finality checkpoint from compact watcher range evidence."""

    if isinstance(required_watcher_count, bool) or not isinstance(required_watcher_count, int):
        raise ValueError("required_watcher_count must be a positive int")
    if required_watcher_count <= 0:
        raise ValueError("required_watcher_count must be a positive int")
    if len(watcher_attestations) != len(verify_reports):
        raise ValueError("watcher_attestations and verify_reports length mismatch")
    if len(watcher_attestations) != len(app_hash_history_proofs):
        raise ValueError("watcher_attestations and app_hash_history_proofs length mismatch")
    if len(watcher_attestations) < required_watcher_count:
        raise ValueError("watcher quorum below required_watcher_count")

    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau compact watcher history proof finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau compact watcher history proof finality snapshot_height",
    )
    entries: list[dict[str, Any]] = []
    seen_watchers: set[str] = set()
    for index, (raw_attestation, raw_report, raw_proof) in enumerate(
        zip(watcher_attestations, verify_reports, app_hash_history_proofs, strict=True)
    ):
        attestation = _require_mapping(raw_attestation, name=f"watcher_attestations[{index}]")
        report = _require_mapping(raw_report, name=f"verify_reports[{index}]")
        proof = _require_mapping(raw_proof, name=f"app_hash_history_proofs[{index}]")
        validate_compact_watcher_attestation_v0(
            attestation=attestation,
            verify_report=report,
            profile=profile,
        )
        watcher_id = _require_nonempty_str(
            attestation.get("watcher_id"),
            name=f"watcher_attestations[{index}].watcher_id",
        )
        if watcher_id in seen_watchers:
            raise ValueError("watcher quorum duplicate watcher_id")
        seen_watchers.add(watcher_id)
        from_height = _require_nonnegative_int(
            attestation.get("from_height"),
            name=f"watcher_attestations[{index}].from_height",
        )
        to_height = _require_nonnegative_int(
            attestation.get("to_height"),
            name=f"watcher_attestations[{index}].to_height",
        )
        height_count = _require_nonnegative_int(
            attestation.get("height_count"),
            name=f"watcher_attestations[{index}].height_count",
        )
        checked_range = {
            "from_height": from_height,
            "to_height": to_height,
            "height_count": height_count,
        }
        last_app_hash = _normalize_tau_state_hash(
            attestation.get("last_app_hash"),
            name=f"watcher_attestations[{index}].last_app_hash",
        )
        app_hash_history_root = _normalize_tau_state_hash(
            report.get("app_hash_history_root"),
            name=f"verify_reports[{index}].app_hash_history_root",
        )
        selected_app_hash = verify_app_hash_history_merkle_proof_for_range_v0(
            proof,
            expected_root=app_hash_history_root,
            checked_range=checked_range,
            snapshot_height=selected_height,
            last_app_hash=last_app_hash,
        )
        entries.append(
            {
                "watcher_id": watcher_id,
                "from_height": from_height,
                "to_height": to_height,
                "height_count": height_count,
                "checked_range": checked_range,
                "checked_range_hash": _normalize_tau_state_hash(
                    attestation.get("checked_range_hash"),
                    name=f"watcher_attestations[{index}].checked_range_hash",
                ),
                "chain_id": _require_nonempty_str(
                    attestation.get("chain_id"),
                    name=f"watcher_attestations[{index}].chain_id",
                ),
                "last_header_hash": _normalize_tau_state_hash(
                    attestation.get("last_header_hash"),
                    name=f"watcher_attestations[{index}].last_header_hash",
                ),
                "last_post_state_root": _normalize_tau_state_hash(
                    attestation.get("last_post_state_root"),
                    name=f"watcher_attestations[{index}].last_post_state_root",
                ),
                "last_app_hash": last_app_hash,
                "selected_app_hash": selected_app_hash,
                "app_hash_history_root": app_hash_history_root,
                "app_hash_history_proof_hash": hash_v0(
                    "tau_compact_watcher_app_hash_history_merkle_proof_v0",
                    proof,
                ),
                "attestation_hash": _normalize_tau_state_hash(
                    attestation.get("attestation_hash"),
                    name=f"watcher_attestations[{index}].attestation_hash",
                ),
                "verify_report_hash": _normalize_tau_state_hash(
                    attestation.get("verify_report_hash"),
                    name=f"watcher_attestations[{index}].verify_report_hash",
                ),
            }
        )

    entries.sort(key=lambda item: item["watcher_id"])
    first = entries[0]
    agreement_key = (
        first["from_height"],
        first["to_height"],
        first["height_count"],
        first["checked_range_hash"],
        first["chain_id"],
        first["last_header_hash"],
        first["last_post_state_root"],
        first["last_app_hash"],
        first["selected_app_hash"],
        first["app_hash_history_root"],
    )
    for entry in entries[1:]:
        current_key = (
            entry["from_height"],
            entry["to_height"],
            entry["height_count"],
            entry["checked_range_hash"],
            entry["chain_id"],
            entry["last_header_hash"],
            entry["last_post_state_root"],
            entry["last_app_hash"],
            entry["selected_app_hash"],
            entry["app_hash_history_root"],
        )
        if current_key != agreement_key:
            raise ValueError("compact Tau watcher history proof attestations must agree on range and app-hash root")

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": first["chain_id"],
        "snapshot_height": selected_height,
        "latest_height": first["to_height"],
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": first["selected_app_hash"],
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_compact_watcher_app_hash_history_merkle_v0",
        "watcher_count": len(entries),
        "required_watcher_count": required_watcher_count,
        "watcher_ids": [entry["watcher_id"] for entry in entries],
        "attestation_hashes": [entry["attestation_hash"] for entry in entries],
        "verify_report_hashes": [entry["verify_report_hash"] for entry in entries],
        "checked_range": dict(first["checked_range"]),
        "checked_range_hashes": [entry["checked_range_hash"] for entry in entries],
        "app_hash_history_roots": [entry["app_hash_history_root"] for entry in entries],
        "app_hash_history_proof_hashes": [entry["app_hash_history_proof_hash"] for entry in entries],
        "last_header_hash": first["last_header_hash"],
        "last_post_state_root": first["last_post_state_root"],
        "range_tip_app_hash": first["last_app_hash"],
    }
    checkpoint_hash = hash_v0("tau_compact_watcher_app_hash_history_merkle_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_compact_watcher_app_hash_history_merkle:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0("tau_compact_watcher_app_hash_history_merkle_finality_checkpoint_v0", body)
    return body


def build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
    *,
    watcher_quorum_certificate: Mapping[str, Any],
    verify_report: Mapping[str, Any],
    app_hash_history_proof: Mapping[str, Any],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any] | None = None,
) -> Mapping[str, Any]:
    """Build a compact historical checkpoint from one proof-carrying quorum certificate."""

    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau compact watcher quorum finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau compact watcher quorum finality snapshot_height",
    )
    certificate = verify_compact_watcher_quorum_certificate_v0(
        watcher_quorum_certificate,
        verify_report=verify_report,
        profile=profile,
    )
    proof = _require_mapping(app_hash_history_proof, name="app_hash_history_proof")
    checked_range = _require_mapping(
        certificate.get("checked_range"),
        name="watcher_quorum_certificate.checked_range",
    )
    last_app_hash = _normalize_tau_state_hash(
        certificate.get("last_app_hash"),
        name="watcher_quorum_certificate.last_app_hash",
    )
    app_hash_history_root = _normalize_tau_state_hash(
        certificate.get("app_hash_history_root"),
        name="watcher_quorum_certificate.app_hash_history_root",
    )
    selected_app_hash = verify_app_hash_history_merkle_proof_for_range_v0(
        proof,
        expected_root=app_hash_history_root,
        checked_range=checked_range,
        snapshot_height=selected_height,
        last_app_hash=last_app_hash,
    )

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": _require_nonempty_str(
            certificate.get("chain_id"),
            name="watcher_quorum_certificate.chain_id",
        ),
        "snapshot_height": selected_height,
        "latest_height": _require_nonnegative_int(
            certificate.get("to_height"),
            name="watcher_quorum_certificate.to_height",
        ),
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": selected_app_hash,
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_compact_watcher_quorum_app_hash_history_merkle_v0",
        "watcher_quorum_certificate_hash": _normalize_tau_state_hash(
            certificate.get("certificate_hash"),
            name="watcher_quorum_certificate.certificate_hash",
        ),
        "compact_verify_report_hash": _normalize_tau_state_hash(
            certificate.get("compact_verify_report_hash"),
            name="watcher_quorum_certificate.compact_verify_report_hash",
        ),
        "registry_root": _normalize_tau_state_hash(
            certificate.get("registry_root"),
            name="watcher_quorum_certificate.registry_root",
        ),
        "accepted_weight": _require_nonnegative_int(
            certificate.get("accepted_weight"),
            name="watcher_quorum_certificate.accepted_weight",
        ),
        "required_weight": _require_nonnegative_int(
            certificate.get("required_weight"),
            name="watcher_quorum_certificate.required_weight",
        ),
        "signer_count": _require_nonnegative_int(
            certificate.get("signer_count"),
            name="watcher_quorum_certificate.signer_count",
        ),
        "signer_ids": list(_require_nonempty_str_list(certificate.get("signer_ids"), name="watcher_quorum_certificate.signer_ids")),
        "checked_range": dict(checked_range),
        "checked_range_hash": _normalize_tau_state_hash(
            certificate.get("checked_range_hash"),
            name="watcher_quorum_certificate.checked_range_hash",
        ),
        "app_hash_history_root": app_hash_history_root,
        "app_hash_history_proof_hash": hash_v0(
            "tau_compact_watcher_quorum_app_hash_history_merkle_proof_v0",
            proof,
        ),
        "last_header_hash": _normalize_tau_state_hash(
            certificate.get("last_header_hash"),
            name="watcher_quorum_certificate.last_header_hash",
        ),
        "last_post_state_root": _normalize_tau_state_hash(
            certificate.get("last_post_state_root"),
            name="watcher_quorum_certificate.last_post_state_root",
        ),
        "range_tip_app_hash": last_app_hash,
    }
    checkpoint_hash = hash_v0("tau_compact_watcher_quorum_app_hash_history_merkle_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_compact_watcher_quorum_app_hash_history_merkle:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0(
        "tau_compact_watcher_quorum_app_hash_history_merkle_finality_checkpoint_v0",
        body,
    )
    return body


def build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0(
    *,
    watcher_quorum_certificate: Mapping[str, Any],
    verify_report: Mapping[str, Any],
    app_hash_history_proof: Mapping[str, Any],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Build a compact checkpoint from an aggregate-signed watcher quorum certificate."""

    profile_obj = _require_mapping(profile, name="profile")
    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau signed compact watcher quorum finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau signed compact watcher quorum finality snapshot_height",
    )
    certificate = verify_signed_compact_watcher_quorum_certificate_v0(
        watcher_quorum_certificate,
        verify_report=verify_report,
    )
    proof = _require_mapping(app_hash_history_proof, name="app_hash_history_proof")
    checked_range = _require_mapping(
        certificate.get("checked_range"),
        name="signed_watcher_quorum_certificate.checked_range",
    )
    last_app_hash = _normalize_tau_state_hash(
        certificate.get("last_app_hash"),
        name="signed_watcher_quorum_certificate.last_app_hash",
    )
    app_hash_history_root = _normalize_tau_state_hash(
        certificate.get("app_hash_history_root"),
        name="signed_watcher_quorum_certificate.app_hash_history_root",
    )
    selected_app_hash = verify_app_hash_history_merkle_proof_for_range_v0(
        proof,
        expected_root=app_hash_history_root,
        checked_range=checked_range,
        snapshot_height=selected_height,
        last_app_hash=last_app_hash,
    )

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": _require_nonempty_str(profile_obj.get("chain_id"), name="profile.chain_id"),
        "snapshot_height": selected_height,
        "latest_height": _require_nonnegative_int(
            certificate.get("to_height"),
            name="signed_watcher_quorum_certificate.to_height",
        ),
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": selected_app_hash,
        "authorizes_settlement": False,
        "source_kind": "zeno_ledger_signed_compact_watcher_quorum_app_hash_history_merkle_v0",
        "watcher_quorum_certificate_hash": _normalize_tau_state_hash(
            certificate.get("certificate_hash"),
            name="signed_watcher_quorum_certificate.certificate_hash",
        ),
        "compact_verify_report_hash": _normalize_tau_state_hash(
            certificate.get("compact_verify_report_hash"),
            name="signed_watcher_quorum_certificate.compact_verify_report_hash",
        ),
        "registry_root": _normalize_tau_state_hash(
            certificate.get("registry_root"),
            name="signed_watcher_quorum_certificate.registry_root",
        ),
        "accepted_weight": _require_nonnegative_int(
            certificate.get("accepted_weight"),
            name="signed_watcher_quorum_certificate.accepted_weight",
        ),
        "required_weight": _require_nonnegative_int(
            certificate.get("required_weight"),
            name="signed_watcher_quorum_certificate.required_weight",
        ),
        "signer_count": _require_nonnegative_int(
            certificate.get("signer_count"),
            name="signed_watcher_quorum_certificate.signer_count",
        ),
        "signer_ids": list(
            _require_nonempty_str_list(
                certificate.get("signer_ids"),
                name="signed_watcher_quorum_certificate.signer_ids",
            )
        ),
        "checked_range": dict(checked_range),
        "checked_range_hash": _normalize_tau_state_hash(
            certificate.get("checked_range_hash"),
            name="signed_watcher_quorum_certificate.checked_range_hash",
        ),
        "app_hash_history_root": app_hash_history_root,
        "app_hash_history_proof_hash": hash_v0(
            "tau_signed_compact_watcher_quorum_app_hash_history_merkle_proof_v0",
            proof,
        ),
        "last_header_hash": _normalize_tau_state_hash(
            certificate.get("last_header_hash"),
            name="signed_watcher_quorum_certificate.last_header_hash",
        ),
        "last_post_state_root": _normalize_tau_state_hash(
            certificate.get("last_post_state_root"),
            name="signed_watcher_quorum_certificate.last_post_state_root",
        ),
        "range_tip_app_hash": last_app_hash,
    }
    checkpoint_hash = hash_v0("tau_signed_compact_watcher_quorum_app_hash_history_merkle_finality_checkpoint_v0", body)
    body["source_ref"] = f"zeno_ledger_signed_compact_watcher_quorum_app_hash_history_merkle:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0(
        "tau_signed_compact_watcher_quorum_app_hash_history_merkle_finality_checkpoint_v0",
        body,
    )
    return body


def build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
    *,
    watcher_quorum_certificate: Mapping[str, Any],
    verify_report: Mapping[str, Any],
    app_hash_history_proof: Mapping[str, Any],
    state_hash: str,
    snapshot_height: int,
    profile: Mapping[str, Any],
    tau_export_packet: Mapping[str, Any],
    tau_export_checkpoint: Mapping[str, Any],
    tau_export_header: Mapping[str, Any],
    tau_export_body: Mapping[str, Any],
    app_root: str,
    membership_proof: Any,
) -> Mapping[str, Any]:
    """Build finality only when the signed quorum is inside an exported state root.

    The sidecar is delayed publication evidence. The watcher quorum finalizes
    the selected app hash from its signed history; the Tau export packet proves
    that the certificate was later committed under `post_state_root`.
    """

    profile_obj = _require_mapping(profile, name="profile")
    normalized_state_hash = _normalize_tau_state_hash(
        state_hash,
        name="Tau state-root-bound signed quorum finality state_hash",
    )
    selected_height = _require_nonnegative_int(
        snapshot_height,
        name="Tau state-root-bound signed quorum finality snapshot_height",
    )
    root = _normalize_tau_state_hash(app_root, name="app_root")
    packet = _require_mapping(tau_export_packet, name="tau_export_packet")
    if packet.get("post_state_root") != root:
        raise ValueError("Tau export packet post_state_root mismatch")
    validate_tau_export_packet_v0(
        packet=packet,
        checkpoint=tau_export_checkpoint,
        header=tau_export_header,
        body=tau_export_body,
        profile=profile_obj,
    )

    certificate = verify_signed_compact_watcher_quorum_certificate_v0(
        watcher_quorum_certificate,
        verify_report=verify_report,
    )
    leaf = build_signed_watcher_quorum_state_leaf_v0(certificate)
    if not verify_app_root_leaf(root, leaf, membership_proof):
        raise ValueError("signed watcher quorum sidecar leaf membership mismatch")

    proof = _require_mapping(app_hash_history_proof, name="app_hash_history_proof")
    checked_range = _require_mapping(
        certificate.get("checked_range"),
        name="signed_watcher_quorum_certificate.checked_range",
    )
    last_app_hash = _normalize_tau_state_hash(
        certificate.get("last_app_hash"),
        name="signed_watcher_quorum_certificate.last_app_hash",
    )
    app_hash_history_root = _normalize_tau_state_hash(
        certificate.get("app_hash_history_root"),
        name="signed_watcher_quorum_certificate.app_hash_history_root",
    )
    selected_app_hash = verify_app_hash_history_merkle_proof_for_range_v0(
        proof,
        expected_root=app_hash_history_root,
        checked_range=checked_range,
        snapshot_height=selected_height,
        last_app_hash=last_app_hash,
    )
    export_height = _require_nonnegative_int(
        packet.get("height"),
        name="tau_export_packet.height",
    )
    if export_height < _require_nonnegative_int(
        certificate.get("to_height"),
        name="signed_watcher_quorum_certificate.to_height",
    ):
        raise ValueError("Tau export packet height below signed watcher range tip")

    body: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": "",
        "chain_id": _require_nonempty_str(profile_obj.get("chain_id"), name="profile.chain_id"),
        "snapshot_height": selected_height,
        "latest_height": _require_nonnegative_int(
            certificate.get("to_height"),
            name="signed_watcher_quorum_certificate.to_height",
        ),
        "finalized_height": selected_height,
        "state_hash": normalized_state_hash,
        "app_hash": selected_app_hash,
        "authorizes_settlement": False,
        "source_kind": STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0,
        "app_root": root,
        "sidecar_leaf_kind": leaf.lane_kind,
        "sidecar_leaf_id": leaf.lane_id,
        "sidecar_leaf_value_hash": "0x" + leaf.value.hex(),
        "tau_export_packet_hash": _normalize_tau_state_hash(
            packet.get("packet_hash"),
            name="tau_export_packet.packet_hash",
        ),
        "tau_export_height": export_height,
        "tau_export_app_hash": _normalize_tau_state_hash(
            packet.get("app_hash"),
            name="tau_export_packet.app_hash",
        ),
        "tau_export_post_state_root": root,
        "watcher_quorum_certificate_hash": _normalize_tau_state_hash(
            certificate.get("certificate_hash"),
            name="signed_watcher_quorum_certificate.certificate_hash",
        ),
        "compact_verify_report_hash": _normalize_tau_state_hash(
            certificate.get("compact_verify_report_hash"),
            name="signed_watcher_quorum_certificate.compact_verify_report_hash",
        ),
        "registry_root": _normalize_tau_state_hash(
            certificate.get("registry_root"),
            name="signed_watcher_quorum_certificate.registry_root",
        ),
        "accepted_weight": _require_nonnegative_int(
            certificate.get("accepted_weight"),
            name="signed_watcher_quorum_certificate.accepted_weight",
        ),
        "required_weight": _require_nonnegative_int(
            certificate.get("required_weight"),
            name="signed_watcher_quorum_certificate.required_weight",
        ),
        "signer_count": _require_nonnegative_int(
            certificate.get("signer_count"),
            name="signed_watcher_quorum_certificate.signer_count",
        ),
        "signer_ids": list(
            _require_nonempty_str_list(
                certificate.get("signer_ids"),
                name="signed_watcher_quorum_certificate.signer_ids",
            )
        ),
        "checked_range": dict(checked_range),
        "checked_range_hash": _normalize_tau_state_hash(
            certificate.get("checked_range_hash"),
            name="signed_watcher_quorum_certificate.checked_range_hash",
        ),
        "app_hash_history_root": app_hash_history_root,
        "app_hash_history_proof_hash": hash_v0(
            "tau_state_root_bound_signed_watcher_quorum_app_hash_history_merkle_proof_v0",
            proof,
        ),
        "last_header_hash": _normalize_tau_state_hash(
            certificate.get("last_header_hash"),
            name="signed_watcher_quorum_certificate.last_header_hash",
        ),
        "last_post_state_root": _normalize_tau_state_hash(
            certificate.get("last_post_state_root"),
            name="signed_watcher_quorum_certificate.last_post_state_root",
        ),
        "range_tip_app_hash": last_app_hash,
    }
    checkpoint_hash = hash_v0(
        "tau_state_root_bound_signed_watcher_quorum_finality_checkpoint_v0",
        body,
    )
    body["source_ref"] = f"zeno_ledger_state_root_bound_signed_watcher_quorum:{checkpoint_hash}"
    body["checkpoint_hash"] = hash_v0(
        "tau_state_root_bound_signed_watcher_quorum_finality_checkpoint_v0",
        body,
    )
    return body


def _validate_tau_finality_checkpoint_v0(
    *,
    verified_snapshot: TauVerifiedStateProofSnapshotReaderV0,
    checkpoint: Mapping[str, Any],
    policy: TauFinalityPolicyV0,
) -> Mapping[str, Any]:
    obj = _require_mapping(checkpoint, name="Tau finality checkpoint")
    if obj.get("schema") != "zenodex.tau.finality_checkpoint.v0":
        raise ValueError("Tau finality checkpoint schema mismatch")
    if obj.get("ok") is not True:
        error = obj.get("error")
        if isinstance(error, str) and error:
            raise ValueError(f"Tau finality checkpoint rejected: {error}")
        raise ValueError("Tau finality checkpoint rejected")
    if obj.get("authorizes_settlement") is not False:
        raise ValueError("Tau finality checkpoint must not authorize settlement")
    source_ref = _require_nonempty_str(obj.get("source_ref"), name="Tau finality checkpoint source_ref")
    chain_id = _require_nonempty_str(obj.get("chain_id"), name="Tau finality checkpoint chain_id")
    if policy.accepted_chain_id is not None and chain_id != policy.accepted_chain_id:
        raise ValueError("Tau finality checkpoint chain_id mismatch")

    proof_height = _require_nonnegative_int(
        verified_snapshot.verification_receipt.get("height"),
        name="Tau state proof verifier receipt height",
    )
    snapshot_height = _require_nonnegative_int(
        obj.get("snapshot_height"),
        name="Tau finality checkpoint snapshot_height",
    )
    latest_height = _require_nonnegative_int(
        obj.get("latest_height"),
        name="Tau finality checkpoint latest_height",
    )
    finalized_height = _require_nonnegative_int(
        obj.get("finalized_height"),
        name="Tau finality checkpoint finalized_height",
    )
    if snapshot_height != proof_height:
        raise ValueError("Tau finality checkpoint snapshot_height mismatch")
    if latest_height < snapshot_height:
        raise ValueError("Tau finality checkpoint latest_height below snapshot_height")
    if finalized_height < snapshot_height:
        raise ValueError("Tau finality checkpoint finalized_height below snapshot_height")

    confirmations = latest_height - snapshot_height
    if confirmations < policy.min_confirmations:
        raise ValueError("Tau finality checkpoint below min_confirmations")
    if confirmations > policy.max_staleness_blocks:
        raise ValueError("Tau finality checkpoint exceeds max_staleness_blocks")

    state_hash = _normalize_tau_state_hash(
        obj.get("state_hash"),
        name="Tau finality checkpoint state_hash",
    )
    if state_hash != verified_snapshot.tau_state_hash:
        raise ValueError("Tau finality checkpoint state_hash mismatch")
    app_hash = _normalize_tau_state_hash(
        obj.get("app_hash"),
        name="Tau finality checkpoint app_hash",
    )
    if app_hash != verified_snapshot.app_hash:
        raise ValueError("Tau finality checkpoint app_hash mismatch")
    result: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": True,
        "source_ref": source_ref,
        "chain_id": chain_id,
        "snapshot_height": snapshot_height,
        "latest_height": latest_height,
        "finalized_height": finalized_height,
        "confirmations": confirmations,
        "state_hash": state_hash,
        "app_hash": app_hash,
        "authorizes_settlement": False,
    }
    source_kind_raw = obj.get("source_kind")
    if source_kind_raw is not None:
        source_kind = _require_nonempty_str(
            source_kind_raw,
            name="Tau finality checkpoint source_kind",
        )
        result["source_kind"] = source_kind
        if source_kind == STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0:
            result.update(
                _validate_state_root_bound_watcher_finality_source_fields_v0(
                    obj,
                    latest_height=latest_height,
                )
            )
    checkpoint_hash_raw = obj.get("checkpoint_hash")
    if checkpoint_hash_raw is not None:
        result["checkpoint_hash"] = _normalize_tau_state_hash(
            checkpoint_hash_raw,
            name="Tau finality checkpoint checkpoint_hash",
        )
    return result


def _validate_state_root_bound_watcher_finality_source_fields_v0(
    checkpoint: Mapping[str, Any],
    *,
    latest_height: int,
) -> Mapping[str, Any]:
    app_root = _normalize_tau_state_hash(
        checkpoint.get("app_root"),
        name="Tau finality checkpoint app_root",
    )
    tau_export_post_state_root = _normalize_tau_state_hash(
        checkpoint.get("tau_export_post_state_root"),
        name="Tau finality checkpoint tau_export_post_state_root",
    )
    if tau_export_post_state_root != app_root:
        raise ValueError("Tau finality checkpoint post_state_root/app_root mismatch")
    sidecar_leaf_kind = _require_nonempty_str(
        checkpoint.get("sidecar_leaf_kind"),
        name="Tau finality checkpoint sidecar_leaf_kind",
    )
    if sidecar_leaf_kind != SIGNED_WATCHER_QUORUM_STATE_LANE_KIND_V0:
        raise ValueError("Tau finality checkpoint sidecar_leaf_kind mismatch")
    tau_export_height = _require_nonnegative_int(
        checkpoint.get("tau_export_height"),
        name="Tau finality checkpoint tau_export_height",
    )
    if tau_export_height < latest_height:
        raise ValueError("Tau finality checkpoint tau_export_height below range tip")
    accepted_weight = _require_nonnegative_int(
        checkpoint.get("accepted_weight"),
        name="Tau finality checkpoint accepted_weight",
    )
    required_weight = _require_nonnegative_int(
        checkpoint.get("required_weight"),
        name="Tau finality checkpoint required_weight",
    )
    if required_weight <= 0:
        raise ValueError("Tau finality checkpoint required_weight must be positive")
    if accepted_weight < required_weight:
        raise ValueError("Tau finality checkpoint accepted_weight below required_weight")
    signer_count = _require_nonnegative_int(
        checkpoint.get("signer_count"),
        name="Tau finality checkpoint signer_count",
    )
    signer_ids = _require_nonempty_str_list(
        checkpoint.get("signer_ids"),
        name="Tau finality checkpoint signer_ids",
    )
    if signer_count != len(signer_ids):
        raise ValueError("Tau finality checkpoint signer_count mismatch")
    return {
        "app_root": app_root,
        "sidecar_leaf_kind": sidecar_leaf_kind,
        "sidecar_leaf_id": _require_nonempty_str(
            checkpoint.get("sidecar_leaf_id"),
            name="Tau finality checkpoint sidecar_leaf_id",
        ),
        "sidecar_leaf_value_hash": _normalize_tau_state_hash(
            checkpoint.get("sidecar_leaf_value_hash"),
            name="Tau finality checkpoint sidecar_leaf_value_hash",
        ),
        "tau_export_packet_hash": _normalize_tau_state_hash(
            checkpoint.get("tau_export_packet_hash"),
            name="Tau finality checkpoint tau_export_packet_hash",
        ),
        "tau_export_height": tau_export_height,
        "tau_export_app_hash": _normalize_tau_state_hash(
            checkpoint.get("tau_export_app_hash"),
            name="Tau finality checkpoint tau_export_app_hash",
        ),
        "tau_export_post_state_root": tau_export_post_state_root,
        "watcher_quorum_certificate_hash": _normalize_tau_state_hash(
            checkpoint.get("watcher_quorum_certificate_hash"),
            name="Tau finality checkpoint watcher_quorum_certificate_hash",
        ),
        "compact_verify_report_hash": _normalize_tau_state_hash(
            checkpoint.get("compact_verify_report_hash"),
            name="Tau finality checkpoint compact_verify_report_hash",
        ),
        "registry_root": _normalize_tau_state_hash(
            checkpoint.get("registry_root"),
            name="Tau finality checkpoint registry_root",
        ),
        "accepted_weight": accepted_weight,
        "required_weight": required_weight,
        "signer_count": signer_count,
        "signer_ids": list(signer_ids),
        "checked_range_hash": _normalize_tau_state_hash(
            checkpoint.get("checked_range_hash"),
            name="Tau finality checkpoint checked_range_hash",
        ),
        "app_hash_history_root": _normalize_tau_state_hash(
            checkpoint.get("app_hash_history_root"),
            name="Tau finality checkpoint app_hash_history_root",
        ),
        "app_hash_history_proof_hash": _normalize_tau_state_hash(
            checkpoint.get("app_hash_history_proof_hash"),
            name="Tau finality checkpoint app_hash_history_proof_hash",
        ),
        "last_header_hash": _normalize_tau_state_hash(
            checkpoint.get("last_header_hash"),
            name="Tau finality checkpoint last_header_hash",
        ),
        "last_post_state_root": _normalize_tau_state_hash(
            checkpoint.get("last_post_state_root"),
            name="Tau finality checkpoint last_post_state_root",
        ),
        "range_tip_app_hash": _normalize_tau_state_hash(
            checkpoint.get("range_tip_app_hash"),
            name="Tau finality checkpoint range_tip_app_hash",
        ),
    }


def build_tau_state_root_bound_watcher_readonly_finality_receipt_v0(
    *,
    finalized_reader: TauFinalizedStateProofSnapshotReaderV0,
) -> Mapping[str, Any]:
    """Build a read-only UX receipt from a state-root-bound watcher finality reader."""

    if not isinstance(finalized_reader, TauFinalizedStateProofSnapshotReaderV0):
        raise TypeError("finalized_reader must be TauFinalizedStateProofSnapshotReaderV0")
    checkpoint = _require_mapping(
        finalized_reader.finality_checkpoint,
        name="Tau finalized state-root-bound watcher checkpoint",
    )
    if checkpoint.get("authorizes_settlement") is not False:
        raise ValueError("Tau finalized watcher receipt must not authorize settlement")
    source_kind = _require_nonempty_str(
        checkpoint.get("source_kind"),
        name="Tau finalized watcher checkpoint source_kind",
    )
    if source_kind != STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0:
        raise ValueError("Tau finalized watcher checkpoint source_kind mismatch")
    state_hash = _normalize_tau_state_hash(
        checkpoint.get("state_hash"),
        name="Tau finalized watcher checkpoint state_hash",
    )
    if state_hash != finalized_reader.tau_state_hash:
        raise ValueError("Tau finalized watcher checkpoint state_hash mismatch")
    app_hash = _normalize_tau_state_hash(
        checkpoint.get("app_hash"),
        name="Tau finalized watcher checkpoint app_hash",
    )
    if app_hash != finalized_reader.app_hash:
        raise ValueError("Tau finalized watcher checkpoint app_hash mismatch")
    app_root = _normalize_tau_state_hash(
        checkpoint.get("app_root"),
        name="Tau finalized watcher checkpoint app_root",
    )
    tau_export_post_state_root = _normalize_tau_state_hash(
        checkpoint.get("tau_export_post_state_root"),
        name="Tau finalized watcher checkpoint tau_export_post_state_root",
    )
    if tau_export_post_state_root != app_root:
        raise ValueError("Tau finalized watcher checkpoint post_state_root/app_root mismatch")
    receipt_body = {
        "schema": TAU_STATE_ROOT_BOUND_WATCHER_READONLY_FINALITY_RECEIPT_SCHEMA_V0,
        "status": TAU_STATE_ROOT_BOUND_WATCHER_READONLY_FINALITY_RECEIPT_STATUS_V0,
        "source_kind": source_kind,
        "source_ref": _require_nonempty_str(
            checkpoint.get("source_ref"),
            name="Tau finalized watcher checkpoint source_ref",
        ),
        "chain_id": _require_nonempty_str(
            checkpoint.get("chain_id"),
            name="Tau finalized watcher checkpoint chain_id",
        ),
        "snapshot_height": _require_nonnegative_int(
            checkpoint.get("snapshot_height"),
            name="Tau finalized watcher checkpoint snapshot_height",
        ),
        "latest_height": _require_nonnegative_int(
            checkpoint.get("latest_height"),
            name="Tau finalized watcher checkpoint latest_height",
        ),
        "finalized_height": _require_nonnegative_int(
            checkpoint.get("finalized_height"),
            name="Tau finalized watcher checkpoint finalized_height",
        ),
        "confirmations": _require_nonnegative_int(
            checkpoint.get("confirmations"),
            name="Tau finalized watcher checkpoint confirmations",
        ),
        "state_hash": state_hash,
        "app_hash": app_hash,
        "app_root": app_root,
        "sidecar_leaf_kind": _require_nonempty_str(
            checkpoint.get("sidecar_leaf_kind"),
            name="Tau finalized watcher checkpoint sidecar_leaf_kind",
        ),
        "sidecar_leaf_id": _require_nonempty_str(
            checkpoint.get("sidecar_leaf_id"),
            name="Tau finalized watcher checkpoint sidecar_leaf_id",
        ),
        "sidecar_leaf_value_hash": _normalize_tau_state_hash(
            checkpoint.get("sidecar_leaf_value_hash"),
            name="Tau finalized watcher checkpoint sidecar_leaf_value_hash",
        ),
        "tau_export_packet_hash": _normalize_tau_state_hash(
            checkpoint.get("tau_export_packet_hash"),
            name="Tau finalized watcher checkpoint tau_export_packet_hash",
        ),
        "tau_export_height": _require_nonnegative_int(
            checkpoint.get("tau_export_height"),
            name="Tau finalized watcher checkpoint tau_export_height",
        ),
        "tau_export_app_hash": _normalize_tau_state_hash(
            checkpoint.get("tau_export_app_hash"),
            name="Tau finalized watcher checkpoint tau_export_app_hash",
        ),
        "tau_export_post_state_root": tau_export_post_state_root,
        "watcher_quorum_certificate_hash": _normalize_tau_state_hash(
            checkpoint.get("watcher_quorum_certificate_hash"),
            name="Tau finalized watcher checkpoint watcher_quorum_certificate_hash",
        ),
        "registry_root": _normalize_tau_state_hash(
            checkpoint.get("registry_root"),
            name="Tau finalized watcher checkpoint registry_root",
        ),
        "accepted_weight": _require_nonnegative_int(
            checkpoint.get("accepted_weight"),
            name="Tau finalized watcher checkpoint accepted_weight",
        ),
        "required_weight": _require_nonnegative_int(
            checkpoint.get("required_weight"),
            name="Tau finalized watcher checkpoint required_weight",
        ),
        "signer_count": _require_nonnegative_int(
            checkpoint.get("signer_count"),
            name="Tau finalized watcher checkpoint signer_count",
        ),
        "signer_ids": list(
            _require_nonempty_str_list(
                checkpoint.get("signer_ids"),
                name="Tau finalized watcher checkpoint signer_ids",
            )
        ),
        "authorizes_settlement": False,
    }
    return {
        **receipt_body,
        "receipt_hash": hash_v0(
            "tau_state_root_bound_watcher_readonly_finality_receipt_v0",
            receipt_body,
        ),
    }


def build_tau_state_proof_verification_request_v0(
    *,
    snapshot: TauRpcStateProofSnapshotReaderV0,
    block: Mapping[str, Any] | None = None,
    context: Mapping[str, Any] | None = None,
) -> Mapping[str, Any]:
    """Build the request consumed by a Tau state-proof verifier."""

    request: dict[str, Any] = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": snapshot.tau_state_hash,
        "proof": dict(snapshot.state_proof),
        "tau_state": dict(snapshot.tau_state),
        "context": {"app_hash": snapshot.app_hash},
    }
    if block is not None:
        request["block"] = dict(_require_mapping(block, name="block"))
    if context is not None:
        context_obj = dict(_require_mapping(context, name="context"))
        context_obj["app_hash"] = snapshot.app_hash
        request["context"] = context_obj
    return request


def _verify_tau_state_proof_request(
    *,
    verifier: TauStateProofVerifierV0,
    request: Mapping[str, Any],
    expected_state_hash: str,
    expected_app_hash: str,
) -> Mapping[str, Any]:
    verify = getattr(verifier, "verify_tau_state_proof", None)
    if verify is None or not callable(verify):
        raise TypeError("verifier must expose verify_tau_state_proof(request)")
    receipt = _require_mapping(verify(request), name="Tau state proof verifier receipt")
    if receipt.get("schema") != "zenodex.tau.state_proof_verification_receipt.v0":
        raise ValueError("Tau state proof verifier receipt schema mismatch")
    if receipt.get("ok") is not True:
        error = receipt.get("error")
        if isinstance(error, str) and error:
            raise ValueError(f"Tau state proof verifier rejected: {error}")
        raise ValueError("Tau state proof verifier rejected")
    if receipt.get("authorizes_settlement") is not False:
        raise ValueError("Tau state proof verifier receipt must not authorize settlement")
    receipt_state_hash = _normalize_tau_state_hash(
        receipt.get("state_hash"),
        name="Tau state proof verifier receipt state_hash",
    )
    if receipt_state_hash != expected_state_hash:
        raise ValueError("Tau state proof verifier receipt state_hash mismatch")
    receipt_app_hash = _normalize_tau_state_hash(
        receipt.get("app_hash"),
        name="Tau state proof verifier receipt app_hash",
    )
    if receipt_app_hash != expected_app_hash:
        raise ValueError("Tau state proof verifier receipt app_hash mismatch")
    return dict(receipt)


def tau_state_record_key_v0(tau_state_hash: str) -> str:
    return f"tau_state:{_normalize_tau_state_hash(tau_state_hash)[2:]}"


def tau_state_proof_record_key_v0(tau_state_hash: str) -> str:
    return f"state_proof:{_normalize_tau_state_hash(tau_state_hash)[2:]}"


def load_tau_retrieved_state_proof_records_v0(
    *,
    reader: TauRecordReaderV0,
    tau_state_hash: str,
    max_record_bytes: int = MAX_TAU_RETRIEVAL_RECORD_BYTES_V0,
) -> TauRetrievedStateProofRecordsV0:
    """Fetch Tau state and proof records by canonical state-hash keys."""

    state_hash = _normalize_tau_state_hash(tau_state_hash)
    tau_state_key = tau_state_record_key_v0(state_hash)
    state_proof_key = tau_state_proof_record_key_v0(state_hash)
    tau_state = _decode_tau_record(
        _read_tau_record(reader, tau_state_key),
        name=tau_state_key,
        max_record_bytes=max_record_bytes,
    )
    state_proof = _decode_tau_record(
        _read_tau_record(reader, state_proof_key),
        name=state_proof_key,
        max_record_bytes=max_record_bytes,
    )
    proof_hash = _normalize_tau_state_hash(
        _extract_state_proof_hash(state_proof),
        name=f"{state_proof_key}.state_hash",
    )
    if proof_hash != state_hash:
        raise ValueError("retrieved state_proof.state_hash does not match retrieval key")
    return TauRetrievedStateProofRecordsV0(
        tau_state_hash=state_hash,
        tau_state_key=tau_state_key,
        state_proof_key=state_proof_key,
        tau_state=tau_state,
        state_proof=state_proof,
    )


def build_tau_export_acceptance_receipt_from_retrieval_v0(
    *,
    reader: TauRecordReaderV0,
    tau_state_hash: str,
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    max_record_bytes: int = MAX_TAU_RETRIEVAL_RECORD_BYTES_V0,
) -> tuple[TauExportAcceptanceReceiptV0, TauRetrievedStateProofRecordsV0]:
    records = load_tau_retrieved_state_proof_records_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        max_record_bytes=max_record_bytes,
    )
    receipt = build_tau_export_acceptance_receipt_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=records.state_proof,
        tau_state=records.tau_state,
    )
    if receipt["state_hash_key"] != records.state_proof_key:
        raise ValueError("receipt state_hash_key does not match retrieved proof key")
    return receipt, records


def validate_tau_export_acceptance_receipt_from_retrieval_v0(
    *,
    reader: TauRecordReaderV0,
    tau_state_hash: str,
    receipt: Mapping[str, Any],
    packet: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    header: Mapping[str, Any],
    body: Mapping[str, Any],
    profile: Mapping[str, Any],
    max_record_bytes: int = MAX_TAU_RETRIEVAL_RECORD_BYTES_V0,
) -> TauRetrievedStateProofRecordsV0:
    records = load_tau_retrieved_state_proof_records_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        max_record_bytes=max_record_bytes,
    )
    validate_tau_export_acceptance_receipt_v0(
        receipt=receipt,
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
        state_proof=records.state_proof,
        tau_state=records.tau_state,
    )
    if receipt.get("state_hash_key") != records.state_proof_key:
        raise ValueError("receipt state_hash_key does not match retrieved proof key")
    return records


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_nonempty_int_list(value: object, *, name: str) -> list[int]:
    if not isinstance(value, list) or not value:
        raise ValueError(f"{name} must be a non-empty int list")
    out: list[int] = []
    for index, item in enumerate(value):
        out.append(_require_nonnegative_int(item, name=f"{name}[{index}]"))
    return out


def _require_nonempty_str_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise ValueError(f"{name} must be a non-empty str list")
    out: list[str] = []
    for index, item in enumerate(value):
        out.append(_require_nonempty_str(item, name=f"{name}[{index}]"))
    return out


def _extract_app_hash_history_rows(
    report: Mapping[str, Any],
    *,
    checked_heights: Sequence[int],
    last_app_hash: str,
    name: str,
) -> Mapping[str, Any]:
    raw_rows = report.get("app_hashes_by_height")
    if not isinstance(raw_rows, list) or not raw_rows:
        raise ValueError(f"{name} must be a non-empty list")
    if len(raw_rows) != len(checked_heights):
        raise ValueError(f"{name} must cover exactly checked_heights")
    rows: list[dict[str, Any]] = []
    by_height: dict[int, str] = {}
    for index, raw in enumerate(raw_rows):
        row = _require_mapping(raw, name=f"{name}[{index}]")
        if set(row.keys()) != {"height", "app_hash"}:
            raise ValueError(f"{name}[{index}] keys mismatch")
        height = _require_nonnegative_int(row.get("height"), name=f"{name}[{index}].height")
        if height != checked_heights[index]:
            raise ValueError(f"{name} heights must match checked_heights order")
        app_hash = _normalize_tau_state_hash(row.get("app_hash"), name=f"{name}[{index}].app_hash")
        rows.append({"height": height, "app_hash": app_hash})
        by_height[height] = app_hash
    if rows[-1]["app_hash"] != last_app_hash:
        raise ValueError(f"{name} final app_hash must match watcher last_app_hash")
    return {
        "rows": rows,
        "by_height": by_height,
        "history_hash": hash_v0("tau_watcher_app_hash_history_v0", {"rows": rows}),
    }


def _read_tau_record(
    reader: TauRecordReaderV0,
    key: str,
) -> Mapping[str, Any] | str | bytes | bytearray:
    read = getattr(reader, "read_tau_record", None)
    if read is None or not callable(read):
        raise TypeError("reader must expose read_tau_record(key)")
    try:
        return read(key)
    except KeyError as exc:
        raise ValueError(f"missing Tau record: {key}") from exc


def _call_tau_rpc_json(method: Any, *, full: bool) -> str:
    if not callable(method):
        raise TypeError("Tau RPC client method must be callable")
    value = method(full=full)
    if not isinstance(value, str):
        raise TypeError("Tau RPC response must be a JSON string")
    return value


def _decode_tau_record(
    raw: Mapping[str, Any] | str | bytes | bytearray,
    *,
    name: str,
    max_record_bytes: int,
) -> Mapping[str, Any]:
    if not isinstance(max_record_bytes, int) or isinstance(max_record_bytes, bool):
        raise ValueError("max_record_bytes must be a positive integer")
    if max_record_bytes <= 0:
        raise ValueError("max_record_bytes must be a positive integer")
    if isinstance(raw, Mapping):
        return dict(raw)
    if isinstance(raw, (bytes, bytearray)):
        if len(raw) > max_record_bytes:
            raise ValueError(f"{name} exceeds max_record_bytes")
        try:
            text = bytes(raw).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValueError(f"{name} must be UTF-8 JSON") from exc
        return _decode_tau_record_text(text, name=name, max_record_bytes=max_record_bytes)
    if isinstance(raw, str):
        return _decode_tau_record_text(raw, name=name, max_record_bytes=max_record_bytes)
    raise TypeError(f"{name} must be a mapping, JSON string, or JSON bytes")


def _decode_tau_record_text(
    text: str,
    *,
    name: str,
    max_record_bytes: int,
) -> Mapping[str, Any]:
    if len(text.encode("utf-8")) > max_record_bytes:
        raise ValueError(f"{name} exceeds max_record_bytes")
    try:
        obj = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValueError(f"{name} must be valid JSON") from exc
    if not isinstance(obj, dict):
        raise ValueError(f"{name} must decode to a JSON object")
    return obj


def _extract_state_proof_hash(state_proof: Mapping[str, Any]) -> object:
    value = state_proof.get("state_hash")
    if value is None and isinstance(state_proof.get("proof"), Mapping):
        value = state_proof["proof"].get("state_hash")
    return value


def _extract_app_hash(tau_state: Mapping[str, Any], *, name: str) -> str:
    return _normalize_tau_state_hash(tau_state.get("app_hash"), name=name)


def _normalize_tau_state_hash(value: object, *, name: str = "tau_state_hash") -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    return canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
