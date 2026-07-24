"""End-to-end range wiring for the governed strict Spot authority adapter."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    VerifierExecutableFormatV1,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.zeno_ledger_profile import sample_zeno_sovereign_testnet_profile_v0
from src.integration.zeno_ledger_replay import (
    parse_replay_engine_config_v1,
    replay_engine_config_digest_v1,
    replay_engine_config_document_v1,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
)
from src.state.canonical import canonical_json_bytes
from tests.integration.test_zeno_ledger_strict_spot_authority_v1 import (
    _BLOCK_TIMESTAMP,
    _CHAIN_ID,
    _JOURNAL_SHA256,
    _fake_response,
    _make_case,
)
from tests.integration.test_zeno_ledger_verify_cli import _body
from tools.zeno_ledger_verify import REPLAY_BOUND_MODE, verify_zeno_ledger_v0

_ROOT = Path(__file__).resolve().parents[2]
_BRIDGE_FIXTURE = _ROOT / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(value))


@dataclass(frozen=True)
class _RangeCase:
    headers_dir: Path
    bodies_dir: Path
    checkpoints_dir: Path
    proof_metadata_dir: Path
    strict_payloads_dir: Path
    snapshots_dir: Path
    config_path: Path
    profile_path: Path
    verifier: object
    registry: dict[str, Any]
    spot_state_roots: dict[str, str]

    def verify(
        self,
        *,
        proof_verification_report_dir: Path | None = None,
        require_proof_verification_report: bool = False,
    ) -> dict[str, Any]:
        return verify_zeno_ledger_v0(
            headers_dir=self.headers_dir,
            bodies_dir=self.bodies_dir,
            checkpoints_dir=self.checkpoints_dir,
            profile_path=self.profile_path,
            from_height=7,
            to_height=7,
            proof_metadata_dir=self.proof_metadata_dir,
            proof_verification_report_dir=proof_verification_report_dir,
            require_proof_verification_report=require_proof_verification_report,
            strict_spot_request_payloads_dir=self.strict_payloads_dir,
            strict_spot_authority_verifier=self.verifier,
            verifier_registry=self.registry,
            mode=REPLAY_BOUND_MODE,
            pre_snapshots_dir=self.snapshots_dir,
            engine_config_path=self.config_path,
            require_rejection_receipt_replay=True,
        )


def _make_range_case(tmp_path: Path) -> _RangeCase:
    (tmp_path / "protocol").mkdir(parents=True)
    protocol = _make_case(
        tmp_path / "protocol",
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    vector = json.loads(_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    sender = vector["sender_pubkey"]
    ingress_nonce = vector["ingress_nonce"]
    pool = vector["pre_state"]["pools"][0]
    pre_state = state_from_snapshot(vector["pre_state"])
    pre_state.nonces.set_last(sender, ingress_nonce - 1)

    _old_config, policy, _old_document = parse_replay_engine_config_v1(
        protocol.replay_config
    )
    config_document = replay_engine_config_document_v1(
        DexEngineConfig(allow_missing_settlement=True, chain_id=_CHAIN_ID),
        proof_authority_policy=policy,
    )
    config_digest = replay_engine_config_digest_v1(config_document)
    tx = {
        "tx_id": "restricted-spot-state-domain-bridge-v1",
        "block_timestamp": _BLOCK_TIMESTAMP,
        "tx_sender_pubkey": sender,
        "nonce": ingress_nonce,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + "55" * 32,
                    "sender_pubkey": sender,
                    "deadline": 1_999_999_999,
                    "pool_id": pool["pool_id"],
                    "asset_in": pool["asset0"],
                    "asset_out": pool["asset1"],
                    "amount_in": 1_000,
                    "min_amount_out": 1_992,
                    "recipient": sender,
                }
            ]
        },
    }
    body = _body(7, txs=[tx])
    body["chain_id"] = _CHAIN_ID
    body["ingress"]["batch_cutoff"]["chain_id"] = _CHAIN_ID
    for receipt in body["ingress"]["ingress_receipts"]:
        receipt["chain_id"] = _CHAIN_ID
    for request in body["ingress"]["forced_inclusion_requests"]:
        request["chain_id"] = _CHAIN_ID
    for decision in body["ingress"]["forced_inclusion_decisions"]:
        decision["chain_id"] = _CHAIN_ID
    body["evidence"]["rejection_receipts"] = []
    tx_root = compute_tx_root_v0(body["transactions"])
    evidence_root = compute_evidence_root_v0(body["evidence"])
    body_root = canonical_body_root_v0(body)
    proof = dict(protocol.payload["proof"])
    proof_commitment = hash_v0("risc0_tau_state_proof_envelope_v0", proof)
    metadata = build_proof_metadata_v0(
        chain_id=_CHAIN_ID,
        height=7,
        proof_kind="risc0_zkvm_v0",
        program_id=str(protocol.metadata["program_id"]),
        verifier_id=str(protocol.metadata["verifier_id"]),
        proof_commitment=proof_commitment,
        public_input_hash=str(protocol.metadata["public_input_hash"]),
        journal_hash="0x" + _JOURNAL_SHA256,
        pre_state_root=expected["pre_state_root_v5"],
        post_state_root=expected["post_state_root_v5"],
        tx_root=tx_root,
        evidence_root=evidence_root,
        body_root=body_root,
        conflict_schedule_hash=str(protocol.metadata["conflict_schedule_hash"]),
        feature_suite_hash=str(protocol.metadata["feature_suite_hash"]),
        dependency_lock_hash=str(protocol.metadata["dependency_lock_hash"]),
        toolchain_lock_hash=str(protocol.metadata["toolchain_lock_hash"]),
    )
    module_versions_digest = str(protocol.header["module_versions_digest"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": _CHAIN_ID,
            "height": 7,
            "post_state_root": expected["post_state_root_v5"],
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=_CHAIN_ID,
        height=7,
        time_ms=_BLOCK_TIMESTAMP * 1_000,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=str(protocol.header["sequencer_set_hash"]),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=tx_root,
        pre_state_root=expected["pre_state_root_v5"],
        post_state_root=expected["post_state_root_v5"],
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=body_root,
        data_availability_root=str(protocol.header["data_availability_root"]),
        proof_journal_hash=proof_metadata_hash_v0(metadata),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id=_CHAIN_ID,
        config_digest=config_digest,
        sequencer_set_hash=str(header["sequencer_set_hash"]),
        token_symbol="tZENO",
        token_asset_id=hash_v0("strict_range_test_v1", {"asset": "token"}),
        proof_required=True,
    )
    payload = {
        **protocol.payload,
        "block": {
            "header": {"timestamp": _BLOCK_TIMESTAMP},
            "transactions": body["transactions"],
        },
        "proof": proof,
    }

    directories = {
        "headers": tmp_path / "headers",
        "bodies": tmp_path / "bodies",
        "checkpoints": tmp_path / "checkpoints",
        "metadata": tmp_path / "proof_metadata",
        "payloads": tmp_path / "strict_payloads",
        "snapshots": tmp_path / "pre_snapshots",
    }
    _write_json(directories["headers"] / "7.json", header)
    _write_json(directories["bodies"] / "7.json", body)
    _write_json(directories["checkpoints"] / "7.json", build_checkpoint_v0(header))
    _write_json(directories["metadata"] / "7.json", metadata)
    _write_json(directories["payloads"] / "7.json", payload)
    _write_json(directories["snapshots"] / "7.json", snapshot_from_state(pre_state).data)
    config_path = tmp_path / "engine_config.json"
    profile_path = tmp_path / "profile.json"
    _write_json(config_path, config_document)
    _write_json(profile_path, profile)
    return _RangeCase(
        headers_dir=directories["headers"],
        bodies_dir=directories["bodies"],
        checkpoints_dir=directories["checkpoints"],
        proof_metadata_dir=directories["metadata"],
        strict_payloads_dir=directories["payloads"],
        snapshots_dir=directories["snapshots"],
        config_path=config_path,
        profile_path=profile_path,
        verifier=protocol.verifier,
        registry=protocol.registry,
        spot_state_roots={
            "source_pre_app_hash": expected["source_pre_app_hash"],
            "source_post_app_hash": expected["source_post_app_hash"],
            "source_pre_nonce_root": expected["source_pre_nonce_root"],
            "source_post_nonce_root": expected["source_post_nonce_root"],
        },
    )


def test_range_verifier_calls_governed_strict_verifier_once_and_satisfies_authority(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=case.spot_state_roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is True, report["errors"]
    assert report["proof_authority_status"] == "satisfied"
    assert report["proof_authority_satisfied"] is True
    assert report["proof_authority_capable"] is True
    assert report["governed_proof_authority_checked_heights"] == [7]
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert call_count == 1


def test_strict_spot_report_injection_rejects_before_verifier_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    report_dir = tmp_path / "caller-reports"
    report_dir.mkdir()
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("caller-authored reports must reject before verifier execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify(proof_verification_report_dir=report_dir)

    assert report["ok"] is False
    assert report["proof_authority_satisfied"] is False
    assert report["governed_proof_authority_checked_heights"] == []
    assert "replay_bound_rejects_caller_authored_proof_verification_reports" in report[
        "errors"
    ]
    assert call_count == 0


def test_range_verifier_rejects_authenticated_source_substitution_after_one_call(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    roots = dict(case.spot_state_roots)
    roots["source_post_app_hash"] = "0x" + "ff" * 32
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is False
    assert report["proof_authority_satisfied"] is False
    assert report["governed_proof_authority_checked_heights"] == []
    assert any("state_domain_bridge_mismatch" in error for error in report["errors"])
    assert call_count == 1


def test_strict_payload_file_is_bound_to_metadata_proof_commitment(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    payload_path = case.strict_payloads_dir / "7.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["proof"]["proof"] = "dGFtcGVyZWQ="
    _write_json(payload_path, payload)
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("mismatched proof must reject before verifier execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is False
    assert any(
        "strict_spot_authority.metadata_mismatch" in error
        for error in report["errors"]
    )
    assert call_count == 0


def test_strict_v1_range_rejects_multiple_heights_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("a multi-height V1 range must reject before execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = verify_zeno_ledger_v0(
        headers_dir=case.headers_dir,
        bodies_dir=case.bodies_dir,
        checkpoints_dir=case.checkpoints_dir,
        profile_path=case.profile_path,
        from_height=7,
        to_height=8,
        proof_metadata_dir=case.proof_metadata_dir,
        strict_spot_request_payloads_dir=case.strict_payloads_dir,
        strict_spot_authority_verifier=case.verifier,
        verifier_registry=case.registry,
        mode=REPLAY_BOUND_MODE,
        pre_snapshots_dir=case.snapshots_dir,
        engine_config_path=case.config_path,
        require_rejection_receipt_replay=True,
    )

    assert report["ok"] is False
    assert "strict_spot_authority_v1_requires_singleton_range" in report["errors"]
    assert report["proof_authority_satisfied"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert call_count == 0


def test_duplicate_key_payload_rejects_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    payload_path = case.strict_payloads_dir / "7.json"
    canonical = payload_path.read_bytes()
    payload_path.write_bytes(
        canonical[:-1] + b',"state_hash":"0x' + b"00" * 32 + b'"}'
    )
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("duplicate-key payload must reject before execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is False
    assert any("strict_spot_authority.request_invalid" in error for error in report["errors"])
    assert report["proof_authority_satisfied"] is False
    assert call_count == 0


def test_nested_proof_meta_schema_substitution_rejects_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    payload_path = case.strict_payloads_dir / "7.json"
    payload = json.loads(payload_path.read_bytes())
    payload["proof"]["meta"]["uncommitted_authority_hint"] = True
    payload_path.write_bytes(canonical_json_bytes(payload))
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("unknown nested proof metadata must reject before execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is False
    assert any("strict_spot_authority.request_invalid" in error for error in report["errors"])
    assert report["proof_authority_satisfied"] is False
    assert call_count == 0


def test_duplicate_key_governed_config_rejects_before_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_range_case(tmp_path)
    canonical = case.config_path.read_bytes()
    case.config_path.write_bytes(
        canonical[:-1]
        + b',"schema":"zenodex/zeno_ledger/replay_engine_config/v1"}'
    )
    call_count = 0

    def fake_execute(**_kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        raise AssertionError("duplicate-key config must reject before execution")

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    report = case.verify()

    assert report["ok"] is False
    assert any("duplicate JSON key: schema" in error for error in report["errors"])
    assert report["proof_authority_satisfied"] is False
    assert call_count == 0
