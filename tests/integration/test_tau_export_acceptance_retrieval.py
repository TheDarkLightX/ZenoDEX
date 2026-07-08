from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Mapping

import pytest

from src.integration.proofux_swap_regret_admission import (
    verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance,
)
from src.integration.tau_export_acceptance_retrieval import (
    STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0,
    TauFinalityPolicyV0,
    TauFinalizedStateProofSnapshotReaderV0,
    TauRpcStateProofSnapshotReaderV0,
    TauVerifiedStateProofSnapshotReaderV0,
    build_tau_export_acceptance_receipt_from_retrieval_v0,
    build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0,
    build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0,
    build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0,
    build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0,
    build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0,
    build_tau_finality_checkpoint_from_watcher_app_hash_history_v0,
    build_tau_finality_checkpoint_from_watcher_attestations_v0,
    build_tau_state_root_bound_watcher_readonly_finality_receipt_v0,
    tau_state_proof_record_key_v0,
    tau_state_record_key_v0,
    validate_tau_export_acceptance_receipt_from_retrieval_v0,
)
from src.integration.zeno_ledger_app_hash_history import (
    app_hash_history_merkle_root_v0,
    build_app_hash_history_merkle_proof_v0,
    checked_range_hash_v0,
    checked_range_summary_v0,
)
from src.integration.zeno_ledger_profile import sample_local_sandbox_profile_v0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import (
    build_compact_watcher_attestation_v0,
    build_watcher_attestation_v0,
    compact_verify_report_v0,
)
from src.integration.zeno_ledger_watcher_quorum import (
    aggregate_signed_compact_watcher_report_signature_shares_v0,
    build_compact_watcher_quorum_certificate_v0,
    build_signed_compact_watcher_quorum_certificate_v0,
    build_signed_compact_watcher_report_signature_share_v0,
    build_signed_watcher_quorum_state_leaf_v0,
    signed_watcher_registry_root_v0,
    watcher_registry_root_v0,
)
from src.state.app_root import AppRootLeaf, compute_app_root, prove_app_root_leaf
from tests.integration.test_proofux_swap_regret_admission import _quorum_fixture, _tau_export_bundle

BLS_SK1 = "0x" + ("01" * 32)
BLS_SK2 = "0x" + ("02" * 32)
BLS_SK3 = "0x" + ("03" * 32)


@dataclass(frozen=True)
class FakeTauRecordReader:
    records: Mapping[str, Mapping[str, Any] | str | bytes]

    def read_tau_record(self, key: str) -> Mapping[str, Any] | str | bytes:
        if key not in self.records:
            raise KeyError(key)
        return self.records[key]


class FakeTauRpcClient:
    def __init__(
        self,
        *,
        app_states: list[Mapping[str, Any]],
        state_proof: Mapping[str, Any],
    ) -> None:
        self._app_states = list(app_states)
        self._state_proof = dict(state_proof)

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        if not self._app_states:
            raise RuntimeError("no app state response queued")
        return json.dumps(self._app_states.pop(0), sort_keys=True)

    def getstateproof(self, *, full: bool = False) -> str:
        assert full is True
        return json.dumps(self._state_proof, sort_keys=True)


@dataclass(frozen=True)
class FakeTauStateProofVerifier:
    receipt: Mapping[str, Any]

    def verify_tau_state_proof(self, request: Mapping[str, Any]) -> Mapping[str, Any]:
        assert request["schema"] == "tau_state_proof_verify"
        assert request["schema_version"] == 1
        assert request["proof"]["present"] is True
        return self.receipt


def _state_hash(label: str) -> str:
    byte = {"one": "aa", "two": "bb"}.get(label, "cc")
    return "0x" + (byte * 32)


def _root(label: str) -> str:
    return hash_v0("tau_export_acceptance_retrieval_test", {"label": label})


def _local_profile() -> Mapping[str, Any]:
    return sample_local_sandbox_profile_v0(
        chain_id="tau-local",
        config_digest=_root("config"),
        sequencer_set_hash=_root("sequencer"),
    )


def _verify_report(
    *,
    app_hash: str,
    heights: list[int] | None = None,
    app_hashes_by_height: list[str] | None = None,
) -> dict[str, Any]:
    checked_heights = heights or [8, 9, 10]
    report = {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "accepted",
        "errors": [],
        "checked_heights": checked_heights,
        "checked_range": checked_range_summary_v0(checked_heights),
        "last_header_hash": _root("header"),
        "last_post_state_root": _root("post-state"),
        "last_app_hash": app_hash,
    }
    report["checked_range_hash"] = checked_range_hash_v0(report["checked_range"])
    if app_hashes_by_height is not None:
        report["app_hashes_by_height"] = [
            {"height": height, "app_hash": row_app_hash}
            for height, row_app_hash in zip(checked_heights, app_hashes_by_height, strict=False)
        ]
        report["app_hash_history_root"] = app_hash_history_merkle_root_v0(report["app_hashes_by_height"])
    return report


def _watcher_attestation(
    *,
    watcher_id: str,
    report: Mapping[str, Any],
    profile: Mapping[str, Any],
    observed_time_ms: int = 1000,
) -> Mapping[str, Any]:
    return build_watcher_attestation_v0(
        verify_report=report,
        watcher_id=watcher_id,
        observed_time_ms=observed_time_ms,
        verifier_ref="zeno-ledger-verify",
        profile=profile,
    )


def _reader_for(
    *,
    tau_state_hash: str,
    app_hash: str,
    proof_hash: str | None = None,
    proof_as_json: bool = False,
) -> FakeTauRecordReader:
    proof = {
        "present": True,
        "state_hash": (proof_hash or tau_state_hash)[2:],
        "proof_type": "tau.adapter.acceptance.v1",
    }
    proof_record: Mapping[str, Any] | str = proof
    if proof_as_json:
        proof_record = json.dumps(proof, sort_keys=True)
    return FakeTauRecordReader(
        {
            tau_state_record_key_v0(tau_state_hash): {"app_hash": app_hash},
            tau_state_proof_record_key_v0(tau_state_hash): proof_record,
        }
    )


def _verifier_receipt(
    *,
    state_hash: str,
    app_hash: str,
    height: int | None = None,
    ok: bool = True,
    authorizes_settlement: bool = False,
) -> Mapping[str, Any]:
    receipt: dict[str, Any] = {
        "schema": "zenodex.tau.state_proof_verification_receipt.v0",
        "ok": ok,
        "state_hash": state_hash,
        "app_hash": app_hash,
        "authorizes_settlement": authorizes_settlement,
    }
    if height is not None:
        receipt["height"] = height
    if not ok:
        receipt["error"] = "bad proof"
    return receipt


def _finality_checkpoint(
    *,
    state_hash: str,
    app_hash: str,
    snapshot_height: int = 10,
    latest_height: int = 13,
    finalized_height: int = 10,
    chain_id: str = "tau-local",
    ok: bool = True,
    authorizes_settlement: bool = False,
) -> Mapping[str, Any]:
    checkpoint: dict[str, Any] = {
        "schema": "zenodex.tau.finality_checkpoint.v0",
        "ok": ok,
        "source_ref": "local-finality-source",
        "chain_id": chain_id,
        "snapshot_height": snapshot_height,
        "latest_height": latest_height,
        "finalized_height": finalized_height,
        "state_hash": state_hash,
        "app_hash": app_hash,
        "authorizes_settlement": authorizes_settlement,
    }
    if not ok:
        checkpoint["error"] = "not finalized"
    return checkpoint


def test_tau_rpc_snapshot_reader_builds_keyed_records_from_stable_snapshot() -> None:
    app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    client = FakeTauRpcClient(
        app_states=[
            {"app_hash": app_hash, "app_state": {"height": 7}},
            {"app_hash": app_hash, "app_state": {"height": 7}},
        ],
        state_proof={
            "present": True,
            "state_hash": tau_state_hash[2:],
            "app_hash": app_hash,
            "proof_type": "tau.adapter.acceptance.v1",
        },
    )

    reader = TauRpcStateProofSnapshotReaderV0.from_client(client)

    assert reader.tau_state_hash == tau_state_hash
    assert reader.tau_state_key == tau_state_record_key_v0(tau_state_hash)
    assert reader.state_proof_key == tau_state_proof_record_key_v0(tau_state_hash)
    assert reader.read_tau_record(reader.tau_state_key)["app_hash"] == app_hash
    assert reader.read_tau_record(reader.state_proof_key)["state_hash"] == tau_state_hash[2:]
    with pytest.raises(KeyError):
        reader.read_tau_record(tau_state_record_key_v0(_state_hash("two")))


def test_tau_rpc_snapshot_reader_rejects_unstable_or_incoherent_snapshots() -> None:
    app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")

    with pytest.raises(ValueError, match="app_hash changed"):
        TauRpcStateProofSnapshotReaderV0.from_client(
            FakeTauRpcClient(
                app_states=[
                    {"app_hash": app_hash},
                    {"app_hash": other_app_hash},
                ],
                state_proof={
                    "present": True,
                    "state_hash": tau_state_hash[2:],
                    "proof_type": "tau.adapter.acceptance.v1",
                },
            )
        )

    with pytest.raises(ValueError, match="present must be true"):
        TauRpcStateProofSnapshotReaderV0.from_client(
            FakeTauRpcClient(
                app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
                state_proof={
                    "present": False,
                    "state_hash": tau_state_hash[2:],
                    "proof_type": "tau.adapter.acceptance.v1",
                },
            )
        )

    with pytest.raises(ValueError, match="proof app_hash does not match"):
        TauRpcStateProofSnapshotReaderV0.from_client(
            FakeTauRpcClient(
                app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
                state_proof={
                    "present": True,
                    "state_hash": tau_state_hash[2:],
                    "app_hash": other_app_hash,
                    "proof_type": "tau.adapter.acceptance.v1",
                },
            )
        )


def test_tau_verified_snapshot_reader_requires_bound_verifier_receipt() -> None:
    app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": app_hash, "app_state": {"height": 7}},
                {"app_hash": app_hash, "app_state": {"height": 7}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    )

    verified = reader.verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash)
        ),
        context={"app_hash_pre": "0x" + ("11" * 32)},
    )

    assert isinstance(verified, TauVerifiedStateProofSnapshotReaderV0)
    assert verified.tau_state_hash == tau_state_hash
    assert verified.app_hash == app_hash
    assert verified.verification_request["state_hash"] == tau_state_hash
    assert verified.verification_request["context"]["app_hash"] == app_hash
    assert verified.verification_receipt["authorizes_settlement"] is False
    assert verified.read_tau_record(verified.state_proof_key)["state_hash"] == tau_state_hash[2:]


def test_tau_verified_snapshot_reader_rejects_unbound_or_authoritative_receipts() -> None:
    app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    other_state_hash = _state_hash("two")
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    )

    with pytest.raises(ValueError, match="verifier rejected: bad proof"):
        reader.verified_by(
            FakeTauStateProofVerifier(
                _verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash, ok=False)
            )
        )
    with pytest.raises(ValueError, match="state_hash mismatch"):
        reader.verified_by(
            FakeTauStateProofVerifier(
                _verifier_receipt(state_hash=other_state_hash, app_hash=app_hash)
            )
        )
    with pytest.raises(ValueError, match="app_hash mismatch"):
        reader.verified_by(
            FakeTauStateProofVerifier(
                _verifier_receipt(state_hash=tau_state_hash, app_hash=other_app_hash)
            )
        )
    with pytest.raises(ValueError, match="must not authorize settlement"):
        reader.verified_by(
            FakeTauStateProofVerifier(
                _verifier_receipt(
                    state_hash=tau_state_hash,
                    app_hash=app_hash,
                    authorizes_settlement=True,
                )
            )
        )
    with pytest.raises(ValueError, match="schema mismatch"):
        reader.verified_by(FakeTauStateProofVerifier({"ok": True}))


def test_tau_finalized_snapshot_reader_requires_finality_policy() -> None:
    app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash, height=10)
        )
    )

    finalized = verified.finalized_by(
        checkpoint=_finality_checkpoint(
            state_hash=tau_state_hash,
            app_hash=app_hash,
            snapshot_height=10,
            latest_height=13,
            finalized_height=10,
        ),
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=8,
            accepted_chain_id="tau-local",
        ),
    )

    assert isinstance(finalized, TauFinalizedStateProofSnapshotReaderV0)
    assert finalized.tau_state_hash == tau_state_hash
    assert finalized.finality_checkpoint["confirmations"] == 3
    assert finalized.finality_policy["min_confirmations"] == 2
    assert finalized.read_tau_record(finalized.tau_state_key)["app_hash"] == app_hash


def test_tau_finalized_snapshot_reader_rejects_unfinalized_or_mismatched_checkpoints() -> None:
    app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    other_state_hash = _state_hash("two")
    policy = TauFinalityPolicyV0(
        min_confirmations=2,
        max_staleness_blocks=8,
        accepted_chain_id="tau-local",
    )
    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash, height=10)
        )
    )

    with pytest.raises(ValueError, match="checkpoint rejected: not finalized"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                ok=False,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="chain_id mismatch"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                chain_id="other-chain",
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="snapshot_height mismatch"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                snapshot_height=9,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="latest_height below snapshot_height"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                latest_height=9,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="finalized_height below snapshot_height"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                finalized_height=9,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="below min_confirmations"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                latest_height=11,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="exceeds max_staleness_blocks"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                latest_height=30,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="state_hash mismatch"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=other_state_hash,
                app_hash=app_hash,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="app_hash mismatch"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=other_app_hash,
            ),
            policy=policy,
        )
    with pytest.raises(ValueError, match="must not authorize settlement"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(
                state_hash=tau_state_hash,
                app_hash=app_hash,
                authorizes_settlement=True,
            ),
            policy=policy,
        )


def test_tau_finalized_snapshot_reader_rejects_missing_verifier_height_and_bad_policy() -> None:
    app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    with pytest.raises(ValueError, match="min_confirmations must be <= max_staleness_blocks"):
        TauFinalityPolicyV0(min_confirmations=9, max_staleness_blocks=8)

    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(_verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash))
    )

    with pytest.raises(ValueError, match="verifier receipt height"):
        verified.finalized_by(
            checkpoint=_finality_checkpoint(state_hash=tau_state_hash, app_hash=app_hash),
            policy=TauFinalityPolicyV0(min_confirmations=0, max_staleness_blocks=8),
        )


def test_tau_watcher_finality_checkpoint_builds_from_valid_quorum() -> None:
    profile = _local_profile()
    app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    report = _verify_report(app_hash=app_hash)
    attestations = [
        _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile),
        _watcher_attestation(watcher_id="watcher-b", report=report, profile=profile, observed_time_ms=1001),
    ]

    checkpoint = build_tau_finality_checkpoint_from_watcher_attestations_v0(
        watcher_attestations=attestations,
        verify_reports=[report, report],
        state_hash=tau_state_hash,
        profile=profile,
        required_watcher_count=2,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_watcher_quorum_v0"
    assert checkpoint["watcher_count"] == 2
    assert checkpoint["required_watcher_count"] == 2
    assert checkpoint["chain_id"] == "tau-local"
    assert checkpoint["snapshot_height"] == 10
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 10
    assert checkpoint["state_hash"] == tau_state_hash
    assert checkpoint["app_hash"] == app_hash
    assert checkpoint["authorizes_settlement"] is False
    assert checkpoint["watcher_ids"] == ["watcher-a", "watcher-b"]

    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": app_hash}, {"app_hash": app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=app_hash, height=10)
        )
    )

    finalized = verified.finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=0,
            max_staleness_blocks=0,
            accepted_chain_id="tau-local",
        ),
    )
    assert finalized.finality_checkpoint["confirmations"] == 0


def test_tau_watcher_finality_checkpoint_rejects_bad_quorum_inputs() -> None:
    profile = _local_profile()
    app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    report = _verify_report(app_hash=app_hash)
    attestation_a = _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile)
    attestation_b = _watcher_attestation(
        watcher_id="watcher-b",
        report=report,
        profile=profile,
        observed_time_ms=1001,
    )

    with pytest.raises(ValueError, match="below required_watcher_count"):
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[attestation_a],
            verify_reports=[report],
            state_hash=tau_state_hash,
            profile=profile,
            required_watcher_count=2,
        )

    with pytest.raises(ValueError, match="length mismatch"):
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[attestation_a, attestation_b],
            verify_reports=[report],
            state_hash=tau_state_hash,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="duplicate watcher_id"):
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[attestation_a, attestation_a],
            verify_reports=[report, report],
            state_hash=tau_state_hash,
            profile=profile,
            required_watcher_count=2,
        )

    with pytest.raises(ValueError, match="binding mismatch"):
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[attestation_a],
            verify_reports=[{**report, "last_app_hash": other_app_hash}],
            state_hash=tau_state_hash,
            profile=profile,
            required_watcher_count=1,
        )

    other_report = _verify_report(app_hash=other_app_hash)
    other_attestation = _watcher_attestation(
        watcher_id="watcher-c",
        report=other_report,
        profile=profile,
        observed_time_ms=1002,
    )
    with pytest.raises(ValueError, match="must agree"):
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[attestation_a, other_attestation],
            verify_reports=[report, other_report],
            state_hash=tau_state_hash,
            profile=profile,
            required_watcher_count=2,
        )

    with pytest.raises(ValueError, match="chain_id"):
        no_profile_attestation = build_watcher_attestation_v0(
            verify_report=report,
            watcher_id="watcher-no-profile",
            observed_time_ms=1003,
            verifier_ref="zeno-ledger-verify",
        )
        build_tau_finality_checkpoint_from_watcher_attestations_v0(
            watcher_attestations=[no_profile_attestation],
            verify_reports=[report],
            state_hash=tau_state_hash,
            required_watcher_count=1,
        )


def test_tau_watcher_app_hash_history_checkpoint_supports_nonzero_confirmations() -> None:
    profile = _local_profile()
    snapshot_app_hash = "0x" + ("10" * 32)
    mid_app_hash = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    attestations = [
        _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile),
        _watcher_attestation(watcher_id="watcher-b", report=report, profile=profile, observed_time_ms=1001),
    ]

    checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
        watcher_attestations=attestations,
        verify_reports=[report, report],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
        required_watcher_count=2,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_watcher_app_hash_history_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == snapshot_app_hash
    assert checkpoint["range_tip_app_hash"] == tip_app_hash

    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": snapshot_app_hash}, {"app_hash": snapshot_app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": snapshot_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=snapshot_app_hash, height=8)
        )
    )

    finalized = verified.finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=4,
            accepted_chain_id="tau-local",
        ),
    )
    assert finalized.finality_checkpoint["confirmations"] == 2


def test_tau_watcher_app_hash_history_checkpoint_rejects_invalid_histories() -> None:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    attestation = _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile)

    with pytest.raises(ValueError, match="must be a non-empty list"):
        report_without_history = _verify_report(app_hash=tip_app_hash)
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[
                _watcher_attestation(watcher_id="watcher-a", report=report_without_history, profile=profile)
            ],
            verify_reports=[report_without_history],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="cover exactly checked_heights"):
        short_report = _verify_report(
            app_hash=tip_app_hash,
            app_hashes_by_height=[app8, tip_app_hash],
        )
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[
                _watcher_attestation(watcher_id="watcher-a", report=short_report, profile=profile)
            ],
            verify_reports=[short_report],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="heights must match checked_heights order"):
        reordered_report = {
            **report,
            "app_hashes_by_height": [
                {"height": 9, "app_hash": app9},
                {"height": 8, "app_hash": app8},
                {"height": 10, "app_hash": tip_app_hash},
            ],
        }
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[
                _watcher_attestation(watcher_id="watcher-a", report=reordered_report, profile=profile)
            ],
            verify_reports=[reordered_report],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="final app_hash must match"):
        bad_final_report = _verify_report(
            app_hash=tip_app_hash,
            app_hashes_by_height=[app8, app9, other_app_hash],
        )
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[
                _watcher_attestation(watcher_id="watcher-a", report=bad_final_report, profile=profile)
            ],
            verify_reports=[bad_final_report],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="snapshot_height must be covered"):
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[attestation],
            verify_reports=[report],
            state_hash=tau_state_hash,
            snapshot_height=7,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="must agree"):
        other_report = _verify_report(
            app_hash=tip_app_hash,
            app_hashes_by_height=[other_app_hash, app9, tip_app_hash],
        )
        build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
            watcher_attestations=[
                attestation,
                _watcher_attestation(watcher_id="watcher-b", report=other_report, profile=profile),
            ],
            verify_reports=[report, other_report],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=2,
        )

    checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
        watcher_attestations=[attestation],
        verify_reports=[report],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
        required_watcher_count=1,
    )
    verified_wrong_app = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": other_app_hash}, {"app_hash": other_app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": other_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=other_app_hash, height=8)
        )
    )
    with pytest.raises(ValueError, match="app_hash mismatch"):
        verified_wrong_app.finalized_by(
            checkpoint=checkpoint,
            policy=TauFinalityPolicyV0(
                min_confirmations=2,
                max_staleness_blocks=4,
                accepted_chain_id="tau-local",
            ),
        )


def test_tau_watcher_app_hash_history_merkle_checkpoint_accepts_compact_proof() -> None:
    profile = _local_profile()
    snapshot_app_hash = "0x" + ("10" * 32)
    mid_app_hash = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = {key: value for key, value in full_report.items() if key != "app_hashes_by_height"}
    attestations = [
        _watcher_attestation(watcher_id="watcher-a", report=compact_report, profile=profile),
        _watcher_attestation(
            watcher_id="watcher-b",
            report=compact_report,
            profile=profile,
            observed_time_ms=1001,
        ),
    ]

    checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
        watcher_attestations=attestations,
        verify_reports=[compact_report, compact_report],
        app_hash_history_proofs=[proof, proof],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
        required_watcher_count=2,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_watcher_app_hash_history_merkle_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == snapshot_app_hash
    assert checkpoint["range_tip_app_hash"] == tip_app_hash
    assert checkpoint["app_hash_history_roots"] == [full_report["app_hash_history_root"]] * 2

    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": snapshot_app_hash}, {"app_hash": snapshot_app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": snapshot_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=snapshot_app_hash, height=8)
        )
    )

    finalized = verified.finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=4,
            accepted_chain_id="tau-local",
        ),
    )
    assert finalized.finality_checkpoint["confirmations"] == 2


def test_tau_watcher_app_hash_history_merkle_checkpoint_rejects_invalid_proofs() -> None:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = {key: value for key, value in full_report.items() if key != "app_hashes_by_height"}
    attestation = _watcher_attestation(watcher_id="watcher-a", report=compact_report, profile=profile)

    with pytest.raises((TypeError, ValueError), match="app_hash_history_root"):
        missing_root_report = dict(compact_report)
        missing_root_report.pop("app_hash_history_root")
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[
                _watcher_attestation(watcher_id="watcher-a", report=missing_root_report, profile=profile)
            ],
            verify_reports=[missing_root_report],
            app_hash_history_proofs=[proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="path root mismatch"):
        bad_leaf_proof = json.loads(json.dumps(proof))
        bad_leaf_proof["leaf"]["app_hash"] = other_app_hash
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[bad_leaf_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="index must match snapshot_height"):
        wrong_index_proof = json.loads(json.dumps(proof))
        wrong_index_proof["index"] = 1
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[wrong_index_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="path root mismatch"):
        bad_sibling_proof = json.loads(json.dumps(proof))
        bad_sibling_proof["siblings"][0]["hash"] = other_app_hash
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[bad_sibling_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="total_rows must match"):
        wrong_total_proof = json.loads(json.dumps(proof))
        wrong_total_proof["total_rows"] = 2
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[wrong_total_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="must agree"):
        other_full_report = _verify_report(
            app_hash=tip_app_hash,
            app_hashes_by_height=[other_app_hash, app9, tip_app_hash],
        )
        other_compact_report = {
            key: value for key, value in other_full_report.items() if key != "app_hashes_by_height"
        }
        other_proof = build_app_hash_history_merkle_proof_v0(
            other_full_report["app_hashes_by_height"],
            snapshot_height=8,
        )
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[
                attestation,
                _watcher_attestation(watcher_id="watcher-b", report=other_compact_report, profile=profile),
            ],
            verify_reports=[compact_report, other_compact_report],
            app_hash_history_proofs=[proof, other_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=2,
        )

    with pytest.raises(ValueError, match="binding mismatch"):
        tampered_report = dict(compact_report)
        tampered_report["app_hash_history_root"] = other_app_hash
        build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[tampered_report],
            app_hash_history_proofs=[proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )


def test_tau_compact_watcher_merkle_checkpoint_uses_range_arithmetic() -> None:
    profile = _local_profile()
    snapshot_app_hash = "0x" + ("10" * 32)
    mid_app_hash = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    assert "checked_heights" not in compact_report
    assert "app_hashes_by_height" not in compact_report
    attestations = [
        build_compact_watcher_attestation_v0(
            verify_report=compact_report,
            watcher_id="watcher-a",
            observed_time_ms=1000,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        ),
        build_compact_watcher_attestation_v0(
            verify_report=compact_report,
            watcher_id="watcher-b",
            observed_time_ms=1001,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        ),
    ]
    assert "checked_heights" not in attestations[0]

    checkpoint = build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
        watcher_attestations=attestations,
        verify_reports=[compact_report, compact_report],
        app_hash_history_proofs=[proof, proof],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
        required_watcher_count=2,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_compact_watcher_app_hash_history_merkle_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == snapshot_app_hash
    assert checkpoint["range_tip_app_hash"] == tip_app_hash
    assert checkpoint["checked_range"] == {"from_height": 8, "to_height": 10, "height_count": 3}
    assert "checked_heights" not in checkpoint


def test_tau_compact_watcher_merkle_checkpoint_rejects_range_mutations() -> None:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    attestation = build_compact_watcher_attestation_v0(
        verify_report=compact_report,
        watcher_id="watcher-a",
        observed_time_ms=1000,
        verifier_ref="zeno-ledger-verify",
        profile=profile,
    )

    with pytest.raises(ValueError, match="snapshot_height must be covered by checked_range"):
        build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[proof],
            state_hash=tau_state_hash,
            snapshot_height=7,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="index must match compact checked_range"):
        wrong_index_proof = json.loads(json.dumps(proof))
        wrong_index_proof["index"] = 1
        build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[compact_report],
            app_hash_history_proofs=[wrong_index_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="height_count"):
        bad_range_report = dict(compact_report)
        bad_range_report["checked_range"] = {"from_height": 8, "to_height": 10, "height_count": 2}
        bad_range_report["checked_range_hash"] = checked_range_hash_v0(
            {"from_height": 8, "to_height": 9, "height_count": 2}
        )
        build_compact_watcher_attestation_v0(
            verify_report=bad_range_report,
            watcher_id="bad-range",
            observed_time_ms=1000,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        )

    with pytest.raises(ValueError, match="checked_range_hash mismatch"):
        tampered_report = dict(compact_report)
        tampered_report["checked_range_hash"] = other_app_hash
        build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[tampered_report],
            app_hash_history_proofs=[proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="binding mismatch"):
        binding_tampered_report = dict(compact_report)
        binding_tampered_report["last_app_hash"] = other_app_hash
        build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation],
            verify_reports=[binding_tampered_report],
            app_hash_history_proofs=[proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=1,
        )

    with pytest.raises(ValueError, match="must agree"):
        other_full_report = _verify_report(
            app_hash=tip_app_hash,
            app_hashes_by_height=[other_app_hash, app9, tip_app_hash],
        )
        other_compact_report = compact_verify_report_v0(other_full_report)
        other_attestation = build_compact_watcher_attestation_v0(
            verify_report=other_compact_report,
            watcher_id="watcher-b",
            observed_time_ms=1001,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        )
        other_proof = build_app_hash_history_merkle_proof_v0(
            other_full_report["app_hashes_by_height"],
            snapshot_height=8,
        )
        build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
            watcher_attestations=[attestation, other_attestation],
            verify_reports=[compact_report, other_compact_report],
            app_hash_history_proofs=[proof, other_proof],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
            required_watcher_count=2,
        )


def test_tau_compact_watcher_quorum_certificate_checkpoint_accepts_weighted_registry() -> None:
    profile = _local_profile()
    snapshot_app_hash = "0x" + ("10" * 32)
    mid_app_hash = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    attestations = [
        build_compact_watcher_attestation_v0(
            verify_report=compact_report,
            watcher_id="watcher-a",
            observed_time_ms=1000,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        ),
        build_compact_watcher_attestation_v0(
            verify_report=compact_report,
            watcher_id="watcher-b",
            observed_time_ms=1001,
            verifier_ref="zeno-ledger-verify",
            profile=profile,
        ),
    ]
    registry_rows = [
        {"watcher_id": "watcher-c", "weight": 3},
        {"watcher_id": "watcher-a", "weight": 1},
        {"watcher_id": "watcher-b", "weight": 1},
    ]
    certificate = build_compact_watcher_quorum_certificate_v0(
        verify_report=compact_report,
        compact_attestations=attestations,
        registry_rows=registry_rows,
        required_weight=2,
        profile=profile,
    )

    checkpoint = build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
        watcher_quorum_certificate=certificate,
        verify_report=compact_report,
        app_hash_history_proof=proof,
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_compact_watcher_quorum_app_hash_history_merkle_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == snapshot_app_hash
    assert checkpoint["range_tip_app_hash"] == tip_app_hash
    assert checkpoint["checked_range"] == {"from_height": 8, "to_height": 10, "height_count": 3}
    assert checkpoint["accepted_weight"] == 2
    assert checkpoint["required_weight"] == 2
    assert checkpoint["signer_count"] == 2
    assert checkpoint["signer_ids"] == ["watcher-a", "watcher-b"]
    assert checkpoint["registry_root"] == watcher_registry_root_v0(registry_rows)
    assert checkpoint["watcher_quorum_certificate_hash"] == certificate["certificate_hash"]
    assert "checked_heights" not in checkpoint
    assert "attestation_hashes" not in checkpoint
    assert "verify_report_hashes" not in checkpoint

    verified = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[{"app_hash": snapshot_app_hash}, {"app_hash": snapshot_app_hash}],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": snapshot_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(state_hash=tau_state_hash, app_hash=snapshot_app_hash, height=8)
        )
    )
    finalized = verified.finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=4,
            accepted_chain_id="tau-local",
        ),
    )
    assert finalized.finality_checkpoint["confirmations"] == 2


def test_tau_compact_watcher_quorum_certificate_rejects_registry_and_binding_mutations() -> None:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    attestation_a = build_compact_watcher_attestation_v0(
        verify_report=compact_report,
        watcher_id="watcher-a",
        observed_time_ms=1000,
        verifier_ref="zeno-ledger-verify",
        profile=profile,
    )
    attestation_b = build_compact_watcher_attestation_v0(
        verify_report=compact_report,
        watcher_id="watcher-b",
        observed_time_ms=1001,
        verifier_ref="zeno-ledger-verify",
        profile=profile,
    )
    registry_rows = [
        {"watcher_id": "watcher-a", "weight": 1},
        {"watcher_id": "watcher-b", "weight": 1},
    ]
    certificate = build_compact_watcher_quorum_certificate_v0(
        verify_report=compact_report,
        compact_attestations=[attestation_a, attestation_b],
        registry_rows=registry_rows,
        required_weight=2,
        profile=profile,
    )

    with pytest.raises(ValueError, match="duplicate watcher_id"):
        build_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            compact_attestations=[attestation_a, attestation_a],
            registry_rows=registry_rows,
            required_weight=2,
            profile=profile,
        )

    with pytest.raises(ValueError, match="accepted_weight below required_weight"):
        build_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            compact_attestations=[attestation_a, attestation_b],
            registry_rows=registry_rows,
            required_weight=3,
            profile=profile,
        )

    unregistered_attestation = build_compact_watcher_attestation_v0(
        verify_report=compact_report,
        watcher_id="watcher-z",
        observed_time_ms=1002,
        verifier_ref="zeno-ledger-verify",
        profile=profile,
    )
    with pytest.raises(ValueError, match="must be covered by watcher registry"):
        build_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            compact_attestations=[attestation_a, unregistered_attestation],
            registry_rows=registry_rows,
            required_weight=2,
            profile=profile,
        )

    tampered_membership = json.loads(json.dumps(certificate))
    tampered_membership["signer_rows"][0]["membership_proof"]["leaf"]["weight"] = 2
    with pytest.raises(ValueError, match="path root mismatch"):
        build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=tampered_membership,
            verify_report=compact_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )

    inflated_weight = json.loads(json.dumps(certificate))
    inflated_weight["signer_rows"][0]["weight"] = 2
    with pytest.raises(ValueError, match="signer weight mismatch"):
        build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=inflated_weight,
            verify_report=compact_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )

    bad_attestation_hash = json.loads(json.dumps(certificate))
    bad_attestation_hash["signer_rows"][0]["attestation_hash"] = other_app_hash
    with pytest.raises(ValueError, match="attestation hash mismatch"):
        build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=bad_attestation_hash,
            verify_report=compact_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )

    tampered_report = dict(compact_report)
    tampered_report["last_app_hash"] = other_app_hash
    with pytest.raises(ValueError, match="compact verify report hash mismatch"):
        build_tau_finality_checkpoint_from_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=certificate,
            verify_report=tampered_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )


def _signed_registry_rows_from_shares(
    share_a: Mapping[str, Any],
    share_b: Mapping[str, Any],
) -> list[Mapping[str, Any]]:
    return [
        {
            "watcher_id": "watcher-a",
            "key_id": "key-a",
            "weight": 1,
            "public_key": share_a["body"]["public_key"],
        },
        {
            "watcher_id": "watcher-b",
            "key_id": "key-b",
            "weight": 1,
            "public_key": share_b["body"]["public_key"],
        },
    ]


def _signed_watcher_quorum_fixture() -> Mapping[str, Any]:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    compact_report_hash = hash_v0("compact_verify_report_v0", compact_report)
    share_a = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-a",
        key_id="key-a",
        private_key_hex=BLS_SK1,
    )
    share_b = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-b",
        key_id="key-b",
        private_key_hex=BLS_SK2,
    )
    registry_rows = _signed_registry_rows_from_shares(share_a, share_b)
    certificate = build_signed_compact_watcher_quorum_certificate_v0(
        verify_report=compact_report,
        signer_ids=["watcher-a", "watcher-b"],
        registry_rows=registry_rows,
        required_weight=2,
        aggregate_signature=aggregate_signed_compact_watcher_report_signature_shares_v0([share_a, share_b]),
    )
    sidecar_leaf = build_signed_watcher_quorum_state_leaf_v0(certificate)
    other_leaf = AppRootLeaf.from_json(
        lane_kind="oracle",
        lane_id="global-price-feed",
        payload={"schema": "zenodex.oracle.snapshot.v1", "round": 13},
    )
    leaves = (other_leaf, sidecar_leaf)
    app_root = compute_app_root(leaves)
    membership_proof = prove_app_root_leaf(leaves, sidecar_leaf)
    packet, checkpoint, header, body, tau_profile = _tau_export_bundle(
        post_state_root=app_root,
    )
    return {
        "profile": profile,
        "tau_profile": tau_profile,
        "app8": app8,
        "tip_app_hash": tip_app_hash,
        "proof": proof,
        "compact_report": compact_report,
        "certificate": certificate,
        "registry_rows": registry_rows,
        "sidecar_leaf": sidecar_leaf,
        "other_leaf": other_leaf,
        "app_root": app_root,
        "membership_proof": membership_proof,
        "packet": packet,
        "checkpoint": checkpoint,
        "header": header,
        "body": body,
    }


def test_tau_signed_compact_watcher_quorum_checkpoint_accepts_aggregate_signature() -> None:
    profile = _local_profile()
    snapshot_app_hash = "0x" + ("10" * 32)
    mid_app_hash = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    compact_report_hash = hash_v0("compact_verify_report_v0", compact_report)
    share_a = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-a",
        key_id="key-a",
        private_key_hex=BLS_SK1,
    )
    share_b = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-b",
        key_id="key-b",
        private_key_hex=BLS_SK2,
    )
    registry_rows = _signed_registry_rows_from_shares(share_a, share_b)
    aggregate_signature = aggregate_signed_compact_watcher_report_signature_shares_v0([share_a, share_b])
    certificate = build_signed_compact_watcher_quorum_certificate_v0(
        verify_report=compact_report,
        signer_ids=["watcher-b", "watcher-a"],
        registry_rows=registry_rows,
        required_weight=2,
        aggregate_signature=aggregate_signature,
    )

    checkpoint = build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0(
        watcher_quorum_certificate=certificate,
        verify_report=compact_report,
        app_hash_history_proof=proof,
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
    )

    assert checkpoint["source_kind"] == "zeno_ledger_signed_compact_watcher_quorum_app_hash_history_merkle_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == snapshot_app_hash
    assert checkpoint["range_tip_app_hash"] == tip_app_hash
    assert checkpoint["accepted_weight"] == 2
    assert checkpoint["required_weight"] == 2
    assert checkpoint["signer_ids"] == ["watcher-a", "watcher-b"]
    assert checkpoint["registry_root"] == signed_watcher_registry_root_v0(registry_rows)
    assert "aggregate_signature" not in checkpoint
    assert "checked_heights" not in checkpoint
    assert "attestation_hashes" not in checkpoint


def test_tau_signed_compact_watcher_quorum_rejects_signature_mutations() -> None:
    profile = _local_profile()
    app8 = "0x" + ("10" * 32)
    app9 = "0x" + ("11" * 32)
    tip_app_hash = "0x" + ("12" * 32)
    other_app_hash = "0x" + ("13" * 32)
    tau_state_hash = _state_hash("one")
    full_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[app8, app9, tip_app_hash],
    )
    other_report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[other_app_hash, app9, tip_app_hash],
    )
    proof = build_app_hash_history_merkle_proof_v0(
        full_report["app_hashes_by_height"],
        snapshot_height=8,
    )
    compact_report = compact_verify_report_v0(full_report)
    other_compact_report = compact_verify_report_v0(other_report)
    compact_report_hash = hash_v0("compact_verify_report_v0", compact_report)
    other_compact_report_hash = hash_v0("compact_verify_report_v0", other_compact_report)
    share_a = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-a",
        key_id="key-a",
        private_key_hex=BLS_SK1,
    )
    share_b = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=compact_report_hash,
        watcher_id="watcher-b",
        key_id="key-b",
        private_key_hex=BLS_SK2,
    )
    registry_rows = _signed_registry_rows_from_shares(share_a, share_b)
    aggregate_signature = aggregate_signed_compact_watcher_report_signature_shares_v0([share_a, share_b])
    certificate = build_signed_compact_watcher_quorum_certificate_v0(
        verify_report=compact_report,
        signer_ids=["watcher-a", "watcher-b"],
        registry_rows=registry_rows,
        required_weight=2,
        aggregate_signature=aggregate_signature,
    )

    with pytest.raises(ValueError, match="accepted_weight below required_weight"):
        build_signed_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            signer_ids=["watcher-a"],
            registry_rows=registry_rows,
            required_weight=2,
            aggregate_signature=aggregate_signed_compact_watcher_report_signature_shares_v0([share_a]),
        )

    with pytest.raises(ValueError, match="aggregate signature invalid"):
        build_signed_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            signer_ids=["watcher-a", "watcher-b"],
            registry_rows=registry_rows,
            required_weight=2,
            aggregate_signature=aggregate_signed_compact_watcher_report_signature_shares_v0([share_a]),
        )

    other_share_a = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=other_compact_report_hash,
        watcher_id="watcher-a",
        key_id="key-a",
        private_key_hex=BLS_SK1,
    )
    other_share_b = build_signed_compact_watcher_report_signature_share_v0(
        compact_report_hash=other_compact_report_hash,
        watcher_id="watcher-b",
        key_id="key-b",
        private_key_hex=BLS_SK2,
    )
    with pytest.raises(ValueError, match="aggregate signature invalid"):
        build_signed_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            signer_ids=["watcher-a", "watcher-b"],
            registry_rows=registry_rows,
            required_weight=2,
            aggregate_signature=aggregate_signed_compact_watcher_report_signature_shares_v0([other_share_a, other_share_b]),
        )

    with pytest.raises(ValueError, match="active public_key values must be unique"):
        build_signed_compact_watcher_quorum_certificate_v0(
            verify_report=compact_report,
            signer_ids=["watcher-a", "watcher-b"],
            registry_rows=[
                registry_rows[0],
                {**registry_rows[1], "public_key": registry_rows[0]["public_key"]},
            ],
            required_weight=2,
            aggregate_signature=aggregate_signature,
        )

    tampered_signature = json.loads(json.dumps(certificate))
    tampered_signature["aggregate_signature"] = "0x" + ("00" * 96)
    with pytest.raises(ValueError, match="aggregate signature invalid"):
        build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=tampered_signature,
            verify_report=compact_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )

    tampered_key = json.loads(json.dumps(certificate))
    tampered_key["signer_rows"][0]["key_id"] = "key-x"
    with pytest.raises(ValueError, match="signer key_id mismatch"):
        build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=tampered_key,
            verify_report=compact_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )

    tampered_report = dict(compact_report)
    tampered_report["last_app_hash"] = other_app_hash
    with pytest.raises(ValueError, match="compact verify report hash mismatch"):
        build_tau_finality_checkpoint_from_signed_compact_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=certificate,
            verify_report=tampered_report,
            app_hash_history_proof=proof,
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=profile,
        )


def test_tau_state_root_bound_signed_watcher_quorum_requires_sidecar_membership() -> None:
    fx = _signed_watcher_quorum_fixture()
    tau_state_hash = _state_hash("one")

    checkpoint = build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
        watcher_quorum_certificate=fx["certificate"],
        verify_report=fx["compact_report"],
        app_hash_history_proof=fx["proof"],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=fx["tau_profile"],
        tau_export_packet=fx["packet"],
        tau_export_checkpoint=fx["checkpoint"],
        tau_export_header=fx["header"],
        tau_export_body=fx["body"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
    )

    assert checkpoint["source_kind"] == "zeno_ledger_state_root_bound_signed_watcher_quorum_app_hash_history_merkle_v0"
    assert checkpoint["snapshot_height"] == 8
    assert checkpoint["latest_height"] == 10
    assert checkpoint["finalized_height"] == 8
    assert checkpoint["app_hash"] == fx["app8"]
    assert checkpoint["range_tip_app_hash"] == fx["tip_app_hash"]
    assert checkpoint["app_root"] == fx["app_root"]
    assert checkpoint["tau_export_post_state_root"] == fx["app_root"]
    assert checkpoint["tau_export_packet_hash"] == fx["packet"]["packet_hash"]
    assert checkpoint["tau_export_app_hash"] == fx["packet"]["app_hash"]
    assert checkpoint["tau_export_height"] == 11
    assert checkpoint["sidecar_leaf_kind"] == fx["sidecar_leaf"].lane_kind
    assert checkpoint["sidecar_leaf_id"] == fx["sidecar_leaf"].lane_id
    assert checkpoint["sidecar_leaf_value_hash"] == "0x" + fx["sidecar_leaf"].value.hex()
    assert checkpoint["watcher_quorum_certificate_hash"] == fx["certificate"]["certificate_hash"]
    assert checkpoint["registry_root"] == signed_watcher_registry_root_v0(fx["registry_rows"])
    assert checkpoint["signer_ids"] == ["watcher-a", "watcher-b"]


def test_tau_state_root_bound_signed_watcher_quorum_rejects_detached_or_tampered_export() -> None:
    fx = _signed_watcher_quorum_fixture()
    tau_state_hash = _state_hash("one")
    wrong_leaf = AppRootLeaf.from_json(
        lane_kind="oracle",
        lane_id="global-price-feed",
        payload={"schema": "zenodex.oracle.snapshot.v1", "round": 99},
    )
    wrong_app_root = compute_app_root((wrong_leaf,))
    wrong_packet, wrong_checkpoint, wrong_header, wrong_body, wrong_profile = _tau_export_bundle(
        post_state_root=wrong_app_root,
    )

    with pytest.raises(ValueError, match="post_state_root mismatch"):
        build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=fx["certificate"],
            verify_report=fx["compact_report"],
            app_hash_history_proof=fx["proof"],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=wrong_profile,
            tau_export_packet=wrong_packet,
            tau_export_checkpoint=wrong_checkpoint,
            tau_export_header=wrong_header,
            tau_export_body=wrong_body,
            app_root=fx["app_root"],
            membership_proof=fx["membership_proof"],
        )

    with pytest.raises(ValueError, match="sidecar leaf membership mismatch"):
        build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=fx["certificate"],
            verify_report=fx["compact_report"],
            app_hash_history_proof=fx["proof"],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=wrong_profile,
            tau_export_packet=wrong_packet,
            tau_export_checkpoint=wrong_checkpoint,
            tau_export_header=wrong_header,
            tau_export_body=wrong_body,
            app_root=wrong_app_root,
            membership_proof=fx["membership_proof"],
        )

    tampered_packet = dict(fx["packet"])
    tampered_packet["app_hash"] = _root("tampered-export-app-hash")
    with pytest.raises(ValueError, match="Tau export packet binding mismatch"):
        build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=fx["certificate"],
            verify_report=fx["compact_report"],
            app_hash_history_proof=fx["proof"],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=fx["tau_profile"],
            tau_export_packet=tampered_packet,
            tau_export_checkpoint=fx["checkpoint"],
            tau_export_header=fx["header"],
            tau_export_body=fx["body"],
            app_root=fx["app_root"],
            membership_proof=fx["membership_proof"],
        )

    tampered_certificate = json.loads(json.dumps(fx["certificate"]))
    tampered_certificate["signer_rows"][0]["key_id"] = "key-z"
    with pytest.raises(ValueError, match="signer key_id mismatch"):
        build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
            watcher_quorum_certificate=tampered_certificate,
            verify_report=fx["compact_report"],
            app_hash_history_proof=fx["proof"],
            state_hash=tau_state_hash,
            snapshot_height=8,
            profile=fx["tau_profile"],
            tau_export_packet=fx["packet"],
            tau_export_checkpoint=fx["checkpoint"],
            tau_export_header=fx["header"],
            tau_export_body=fx["body"],
            app_root=fx["app_root"],
            membership_proof=fx["membership_proof"],
        )


def _state_root_bound_watcher_checkpoint(
    fx: Mapping[str, Any],
    *,
    tau_state_hash: str,
) -> Mapping[str, Any]:
    return build_tau_finality_checkpoint_from_state_root_bound_signed_watcher_quorum_certificate_v0(
        watcher_quorum_certificate=fx["certificate"],
        verify_report=fx["compact_report"],
        app_hash_history_proof=fx["proof"],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=fx["tau_profile"],
        tau_export_packet=fx["packet"],
        tau_export_checkpoint=fx["checkpoint"],
        tau_export_header=fx["header"],
        tau_export_body=fx["body"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
    )


def _verified_reader_for_checkpoint(
    checkpoint: Mapping[str, Any],
    *,
    tau_state_hash: str,
    app_hash: str | None = None,
    verifier_app_hash: str | None = None,
    verifier_height: int = 8,
) -> TauVerifiedStateProofSnapshotReaderV0:
    reader_app_hash = app_hash or str(checkpoint["app_hash"])
    receipt_app_hash = verifier_app_hash or reader_app_hash
    return TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": reader_app_hash, "app_state": {"height": verifier_height}},
                {"app_hash": reader_app_hash, "app_state": {"height": verifier_height}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": reader_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(
                state_hash=tau_state_hash,
                app_hash=receipt_app_hash,
                height=verifier_height,
            )
        )
    )


def test_tau_state_root_bound_watcher_readonly_finality_receipt_accepts_finalized_reader() -> None:
    fx = _signed_watcher_quorum_fixture()
    tau_state_hash = _state_hash("one")
    checkpoint = _state_root_bound_watcher_checkpoint(fx, tau_state_hash=tau_state_hash)
    finalized = _verified_reader_for_checkpoint(
        checkpoint,
        tau_state_hash=tau_state_hash,
    ).finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=4,
            accepted_chain_id=fx["tau_profile"]["chain_id"],
        ),
    )

    receipt = build_tau_state_root_bound_watcher_readonly_finality_receipt_v0(
        finalized_reader=finalized,
    )

    assert finalized.finality_checkpoint["source_kind"] == STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0
    assert finalized.finality_checkpoint["app_root"] == fx["app_root"]
    assert finalized.finality_checkpoint["tau_export_post_state_root"] == fx["app_root"]
    assert receipt["status"] == "read_only_finality_confirmed"
    assert receipt["source_kind"] == STATE_ROOT_BOUND_SIGNED_WATCHER_QUORUM_SOURCE_KIND_V0
    assert receipt["authorizes_settlement"] is False
    assert receipt["confirmations"] == 2
    assert receipt["app_hash"] == checkpoint["app_hash"]
    assert receipt["state_hash"] == tau_state_hash
    assert receipt["app_root"] == fx["app_root"]
    assert receipt["sidecar_leaf_value_hash"] == "0x" + fx["sidecar_leaf"].value.hex()
    assert receipt["watcher_quorum_certificate_hash"] == fx["certificate"]["certificate_hash"]
    assert receipt["receipt_hash"].startswith("0x")


def test_tau_state_root_bound_watcher_readonly_finality_receipt_rejects_generic_or_tampered_sources() -> None:
    fx = _signed_watcher_quorum_fixture()
    tau_state_hash = _state_hash("one")
    checkpoint = _state_root_bound_watcher_checkpoint(fx, tau_state_hash=tau_state_hash)
    verified = _verified_reader_for_checkpoint(checkpoint, tau_state_hash=tau_state_hash)
    policy = TauFinalityPolicyV0(
        min_confirmations=2,
        max_staleness_blocks=4,
        accepted_chain_id=fx["tau_profile"]["chain_id"],
    )

    generic_checkpoint = _finality_checkpoint(
        state_hash=tau_state_hash,
        app_hash=checkpoint["app_hash"],
        snapshot_height=8,
        latest_height=10,
        finalized_height=8,
        chain_id=fx["tau_profile"]["chain_id"],
    )
    generic_finalized = verified.finalized_by(
        checkpoint=generic_checkpoint,
        policy=policy,
    )
    with pytest.raises(ValueError, match="source_kind"):
        build_tau_state_root_bound_watcher_readonly_finality_receipt_v0(
            finalized_reader=generic_finalized,
        )

    wrong_source_checkpoint = dict(checkpoint)
    wrong_source_checkpoint["source_kind"] = "zeno_ledger_signed_compact_watcher_quorum_app_hash_history_merkle_v0"
    wrong_source_finalized = verified.finalized_by(
        checkpoint=wrong_source_checkpoint,
        policy=policy,
    )
    with pytest.raises(ValueError, match="source_kind mismatch"):
        build_tau_state_root_bound_watcher_readonly_finality_receipt_v0(
            finalized_reader=wrong_source_finalized,
        )

    wrong_root_checkpoint = dict(checkpoint)
    wrong_root_checkpoint["tau_export_post_state_root"] = _root("wrong-post-state-root")
    with pytest.raises(ValueError, match="post_state_root/app_root mismatch"):
        verified.finalized_by(
            checkpoint=wrong_root_checkpoint,
            policy=policy,
        )

    low_export_height_checkpoint = dict(checkpoint)
    low_export_height_checkpoint["tau_export_height"] = 9
    with pytest.raises(ValueError, match="tau_export_height below range tip"):
        verified.finalized_by(
            checkpoint=low_export_height_checkpoint,
            policy=policy,
        )

    authoritative_checkpoint = dict(checkpoint)
    authoritative_checkpoint["authorizes_settlement"] = True
    with pytest.raises(ValueError, match="must not authorize settlement"):
        verified.finalized_by(
            checkpoint=authoritative_checkpoint,
            policy=policy,
        )

    wrong_app_verified = _verified_reader_for_checkpoint(
        checkpoint,
        tau_state_hash=tau_state_hash,
        app_hash=_root("wrong-state-proof-app-hash"),
    )
    with pytest.raises(ValueError, match="app_hash mismatch"):
        wrong_app_verified.finalized_by(
            checkpoint=checkpoint,
            policy=policy,
        )


def test_tau_rpc_snapshot_reader_feeds_acceptance_receipt_builder() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    client = FakeTauRpcClient(
        app_states=[
            {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
            {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
        ],
        state_proof={
            "present": True,
            "state_hash": tau_state_hash[2:],
            "proof_type": "tau.adapter.acceptance.v1",
        },
    )
    reader = TauRpcStateProofSnapshotReaderV0.from_client(client)

    receipt, records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert records.tau_state_key == reader.tau_state_key
    assert receipt["state_hash_key"] == reader.state_proof_key


def test_tau_verified_snapshot_reader_feeds_proofux_retrieved_acceptance() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(
                state_hash=tau_state_hash,
                app_hash=fx["packet"]["app_hash"],
            )
        )
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=reader,
    )


def test_tau_finalized_snapshot_reader_feeds_proofux_retrieved_acceptance() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 11}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(
                state_hash=tau_state_hash,
                app_hash=fx["packet"]["app_hash"],
                height=10,
            )
        )
    ).finalized_by(
        checkpoint=_finality_checkpoint(
            state_hash=tau_state_hash,
            app_hash=fx["packet"]["app_hash"],
            snapshot_height=10,
            latest_height=13,
            finalized_height=10,
        ),
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=8,
            accepted_chain_id="tau-local",
        ),
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=reader,
    )


def test_tau_watcher_finalized_snapshot_reader_feeds_proofux_retrieved_acceptance() -> None:
    fx = _quorum_fixture()
    profile = _local_profile()
    tau_state_hash = _state_hash("one")
    report = _verify_report(app_hash=fx["packet"]["app_hash"])
    attestations = [
        _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile),
        _watcher_attestation(watcher_id="watcher-b", report=report, profile=profile, observed_time_ms=1001),
    ]
    checkpoint = build_tau_finality_checkpoint_from_watcher_attestations_v0(
        watcher_attestations=attestations,
        verify_reports=[report, report],
        state_hash=tau_state_hash,
        profile=profile,
        required_watcher_count=2,
    )
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 10}},
                {"app_hash": fx["packet"]["app_hash"], "app_state": {"height": 10}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": fx["packet"]["app_hash"],
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(
                state_hash=tau_state_hash,
                app_hash=fx["packet"]["app_hash"],
                height=10,
            )
        )
    ).finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=0,
            max_staleness_blocks=0,
            accepted_chain_id="tau-local",
        ),
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=reader,
    )


def test_tau_watcher_history_finalized_snapshot_reader_feeds_proofux_retrieved_acceptance() -> None:
    fx = _quorum_fixture()
    profile = _local_profile()
    tau_state_hash = _state_hash("one")
    snapshot_app_hash = fx["packet"]["app_hash"]
    mid_app_hash = _root("history-mid-app")
    tip_app_hash = _root("history-tip-app")
    report = _verify_report(
        app_hash=tip_app_hash,
        app_hashes_by_height=[snapshot_app_hash, mid_app_hash, tip_app_hash],
    )
    attestations = [
        _watcher_attestation(watcher_id="watcher-a", report=report, profile=profile),
        _watcher_attestation(watcher_id="watcher-b", report=report, profile=profile, observed_time_ms=1001),
    ]
    checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
        watcher_attestations=attestations,
        verify_reports=[report, report],
        state_hash=tau_state_hash,
        snapshot_height=8,
        profile=profile,
        required_watcher_count=2,
    )
    reader = TauRpcStateProofSnapshotReaderV0.from_client(
        FakeTauRpcClient(
            app_states=[
                {"app_hash": snapshot_app_hash, "app_state": {"height": 8}},
                {"app_hash": snapshot_app_hash, "app_state": {"height": 8}},
            ],
            state_proof={
                "present": True,
                "state_hash": tau_state_hash[2:],
                "app_hash": snapshot_app_hash,
                "proof_type": "tau.adapter.acceptance.v1",
            },
        )
    ).verified_by(
        FakeTauStateProofVerifier(
            _verifier_receipt(
                state_hash=tau_state_hash,
                app_hash=snapshot_app_hash,
                height=8,
            )
        )
    ).finalized_by(
        checkpoint=checkpoint,
        policy=TauFinalityPolicyV0(
            min_confirmations=2,
            max_staleness_blocks=4,
            accepted_chain_id="tau-local",
        ),
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert reader.finality_checkpoint["confirmations"] == 2
    assert verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=reader,
    )


def test_tau_export_acceptance_receipt_builds_from_keyed_retrieval() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    reader = _reader_for(
        tau_state_hash=tau_state_hash,
        app_hash=fx["packet"]["app_hash"],
        proof_as_json=True,
    )

    receipt, records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    assert records.tau_state_key == tau_state_record_key_v0(tau_state_hash)
    assert records.state_proof_key == tau_state_proof_record_key_v0(tau_state_hash)
    assert receipt["tau_state_hash"] == tau_state_hash
    assert receipt["state_hash_key"] == records.state_proof_key
    validate_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        receipt=receipt,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )


def test_tau_export_acceptance_retrieval_rejects_missing_or_bad_records() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    state_key = tau_state_record_key_v0(tau_state_hash)
    proof_key = tau_state_proof_record_key_v0(tau_state_hash)
    valid_reader = _reader_for(
        tau_state_hash=tau_state_hash,
        app_hash=fx["packet"]["app_hash"],
    )

    with pytest.raises(ValueError, match=f"missing Tau record: {state_key}"):
        build_tau_export_acceptance_receipt_from_retrieval_v0(
            reader=FakeTauRecordReader({proof_key: valid_reader.records[proof_key]}),
            tau_state_hash=tau_state_hash,
            packet=fx["packet"],
            checkpoint=fx["checkpoint"],
            header=fx["header"],
            body=fx["body"],
            profile=fx["profile"],
        )

    with pytest.raises(ValueError, match=f"missing Tau record: {proof_key}"):
        build_tau_export_acceptance_receipt_from_retrieval_v0(
            reader=FakeTauRecordReader({state_key: valid_reader.records[state_key]}),
            tau_state_hash=tau_state_hash,
            packet=fx["packet"],
            checkpoint=fx["checkpoint"],
            header=fx["header"],
            body=fx["body"],
            profile=fx["profile"],
        )

    with pytest.raises(ValueError, match="state_hash does not match retrieval key"):
        build_tau_export_acceptance_receipt_from_retrieval_v0(
            reader=_reader_for(
                tau_state_hash=tau_state_hash,
                app_hash=fx["packet"]["app_hash"],
                proof_hash=_state_hash("two"),
            ),
            tau_state_hash=tau_state_hash,
            packet=fx["packet"],
            checkpoint=fx["checkpoint"],
            header=fx["header"],
            body=fx["body"],
            profile=fx["profile"],
        )

    with pytest.raises(ValueError, match="must be valid JSON"):
        build_tau_export_acceptance_receipt_from_retrieval_v0(
            reader=FakeTauRecordReader(
                {
                    state_key: {"app_hash": fx["packet"]["app_hash"]},
                    proof_key: "{bad-json",
                }
            ),
            tau_state_hash=tau_state_hash,
            packet=fx["packet"],
            checkpoint=fx["checkpoint"],
            header=fx["header"],
            body=fx["body"],
            profile=fx["profile"],
        )


def test_tau_export_acceptance_retrieval_rejects_receipt_from_other_key() -> None:
    fx = _quorum_fixture()
    first_hash = _state_hash("one")
    second_hash = _state_hash("two")
    first_reader = _reader_for(
        tau_state_hash=first_hash,
        app_hash=fx["packet"]["app_hash"],
    )
    second_reader = _reader_for(
        tau_state_hash=second_hash,
        app_hash=fx["packet"]["app_hash"],
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=first_reader,
        tau_state_hash=first_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )

    with pytest.raises(ValueError, match="binding mismatch"):
        validate_tau_export_acceptance_receipt_from_retrieval_v0(
            reader=second_reader,
            tau_state_hash=second_hash,
            receipt=receipt,
            packet=fx["packet"],
            checkpoint=fx["checkpoint"],
            header=fx["header"],
            body=fx["body"],
            profile=fx["profile"],
        )


def test_proofux_tau_export_retrieved_acceptance_uses_keyed_reader() -> None:
    fx = _quorum_fixture()
    tau_state_hash = _state_hash("one")
    reader = _reader_for(
        tau_state_hash=tau_state_hash,
        app_hash=fx["packet"]["app_hash"],
    )
    receipt, _records = build_tau_export_acceptance_receipt_from_retrieval_v0(
        reader=reader,
        tau_state_hash=tau_state_hash,
        packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
    )
    assert verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=reader,
    )

    assert not verify_swap_execution_regret_quorum_tau_export_retrieved_acceptance(
        binding_payload=fx["binding_payload"],
        request_snapshot=fx["request"],
        quote_snapshot=fx["quote_snapshot"],
        projection=fx["projection"],
        signature_envelopes=fx["envelopes"],
        signer_registry=fx["registry"],
        app_root=fx["app_root"],
        membership_proof=fx["membership_proof"],
        tau_export_packet=fx["packet"],
        checkpoint=fx["checkpoint"],
        header=fx["header"],
        body=fx["body"],
        profile=fx["profile"],
        tau_acceptance_receipt=receipt,
        tau_state_hash=tau_state_hash,
        tau_record_reader=FakeTauRecordReader({}),
    )
