from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

from src.core.dex import DexState
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.tau_export_acceptance_retrieval import (
    build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0,
    build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0,
    build_tau_finality_checkpoint_from_watcher_app_hash_history_v0,
)
from src.integration.zeno_ledger_app_hash_history import (
    app_hash_history_merkle_root_v0,
    build_app_hash_history_merkle_proof_v0,
    checked_range_hash_v0,
    checked_range_summary_v0,
)
from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from src.integration.zeno_ledger_profile import (
    sample_local_sandbox_profile_v0,
    sample_tau_exclusive_release_profile_v0,
    sample_zeno_sovereign_testnet_profile_v0,
)
from src.integration.zeno_ledger_signature import validate_signed_artifact_envelope_v0
from src.integration.zeno_ledger_tau_export import validate_tau_export_packet_v0
from src.integration.zeno_ledger_testnet_status import validate_testnet_status_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    FORCED_INCLUSION_DECISION_SCHEMA_V0,
    FORCED_INCLUSION_REQUEST_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
    validate_proof_metadata_header_binding_v0,
)
from src.integration.zeno_ledger_watcher import validate_watcher_attestation_v0
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ROOT = Path(__file__).resolve().parents[2]
VERIFY_SCRIPT = ROOT / "tools" / "zeno_ledger_verify.py"
RUN_SCRIPT = ROOT / "tools" / "zeno_ledger_run_local.py"
MAKE_BUNDLE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_testnet_bundle.py"
MAKE_FEATURE_LANE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_feature_lane.py"
MAKE_CORE_FEATURE_SUITE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_core_feature_suite.py"
MAKE_ASSURANCE_FEATURE_SUITE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_assurance_feature_suite.py"
MAKE_PUBLIC_TESTNET_BUNDLE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_public_testnet_bundle.py"
DUAL_OPERATOR_REHEARSAL_SCRIPT = ROOT / "tools" / "zeno_ledger_dual_operator_rehearsal.py"
MAKE_FEATURE_SUITE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_feature_suite.py"
RUN_FEATURE_SUITE_SCRIPT = ROOT / "tools" / "zeno_ledger_run_feature_suite.py"
MAKE_TESTNET_STATUS_SCRIPT = ROOT / "tools" / "zeno_ledger_make_testnet_status.py"
MAKE_SIGNER_REGISTRY_SCRIPT = ROOT / "tools" / "zeno_ledger_make_signer_registry.py"
VERIFY_SIGNATURE_QUORUM_SCRIPT = ROOT / "tools" / "zeno_ledger_verify_signature_quorum.py"
RUN_MANIFEST_SCRIPT = ROOT / "tools" / "zeno_ledger_run_manifest.py"
EXPORT_TAU_PACKET_SCRIPT = ROOT / "tools" / "zeno_ledger_export_tau_packet.py"
ATTEST_SCRIPT = ROOT / "tools" / "zeno_ledger_attest.py"
VERIFY_MIRROR_INDEX_SCRIPT = ROOT / "tools" / "zeno_ledger_verify_mirror_index.py"
SIGN_ARTIFACT_SCRIPT = ROOT / "tools" / "zeno_ledger_sign_artifact.py"
VERIFY_ARTIFACT_SIGNATURE_SCRIPT = ROOT / "tools" / "zeno_ledger_verify_artifact_signature.py"
PUBLISH_MIRROR_SCRIPT = ROOT / "tools" / "zeno_ledger_publish_mirror.py"
OPERATOR_REHEARSAL_SCRIPT = ROOT / "tools" / "zeno_ledger_operator_rehearsal.py"
ZERO_ROOT = "0x" + "00" * 32
TEST_SIGNING_SECRET = "0x" + "42" * 32
TEST_BLS_PRIVATE_KEY = "0x" + "01" * 32
TEST_BLS_PRIVATE_KEY_2 = "0x" + "02" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _body(height: int, *, nonce: int = 1, txs: list[object] | None = None) -> dict[str, object]:
    tx_hash = hash_v0("tx_fixture", {"height": height, "nonce": nonce})
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": "zeno-ledger-devnet-0",
                "height": height,
                "cutoff_time_ms": 1_778_730_000_000 + height,
                "cutoff_sequence": 12345 + height,
                "sequencer_id": "sequencer-dev-0",
                "policy_id": "public_cutoff_v0",
                "policy_digest": _root("policy"),
            },
            "ingress_receipts": [
                {
                    "schema": INGRESS_RECEIPT_SCHEMA_V0,
                    "chain_id": "zeno-ledger-devnet-0",
                    "tx_hash": tx_hash,
                    "received_time_ms": 1_778_729_999_000 + height,
                    "received_sequence": 12344 + height,
                    "sequencer_id": "sequencer-dev-0",
                    "status": "included",
                    "height": height,
                    "index": 0,
                    "reject_code": None,
                    "receipt_hash": _root(f"receipt-{height}"),
                }
            ],
            "forced_inclusion_requests": [
                {
                    "schema": FORCED_INCLUSION_REQUEST_SCHEMA_V0,
                    "chain_id": "zeno-ledger-devnet-0",
                    "tx_hash": _root(f"forced-tx-{height}"),
                    "tx_body_hash": _root(f"forced-body-{height}"),
                    "submitter_id": "0xsubmitter",
                    "first_seen_time_ms": 1_778_729_999_000 + height,
                    "first_seen_sequence": 12344 + height,
                    "deadline_height": height + 5,
                    "request_hash": _root(f"forced-request-{height}"),
                }
            ],
            "forced_inclusion_decisions": [
                {
                    "schema": FORCED_INCLUSION_DECISION_SCHEMA_V0,
                    "chain_id": "zeno-ledger-devnet-0",
                    "height": height + 5,
                    "request_hash": _root(f"forced-request-{height}"),
                    "decision": "included",
                    "tx_hash": _root(f"forced-tx-{height}"),
                    "index": 2,
                    "reject_code": None,
                }
            ],
        },
        "transactions": [{"sender": "alice", "nonce": nonce}] if txs is None else txs,
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [{"cert_id": f"upba-{height}", "root": _root("upba")}],
            "price_grid_tables": [{"table_root": _root("table")}],
            "uniform_batch_hypergraph_roots": [_root("hypergraph")],
            "oracle_packets": [{"oracle_packet_root": _root("oracle")}],
            "proof_receipts": [{"proof_receipt_root": _root("proof")}],
            "rejection_receipts": [{"receipt_root": _root("reject")}],
        },
    }


def _create_pool_intent_dict(*, intent_id: str, sender: str, asset0: str, asset1: str) -> dict[str, object]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9_999_999_999,
        "nonce": 1,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }


def _header(body: dict[str, object], *, prev_header_hash: str) -> dict[str, object]:
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": _root(f"post-state-{body['height']}"),
            "evidence_root": evidence_root,
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000 + int(body["height"]),
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=_root(f"pre-state-{body['height']}"),
        post_state_root=_root(f"post-state-{body['height']}"),
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _manifest_relative_path(manifest_path: Path, value: object) -> Path:
    path = Path(str(value))
    return path if path.is_absolute() else manifest_path.parent / path


def _load_manifest(report: dict[str, object]) -> tuple[Path, dict[str, object]]:
    manifest_path = Path(str(report["manifest_path"]))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert isinstance(manifest, dict)
    return manifest_path, manifest


def _resolve_command_against_manifest(manifest_path: Path, command: list[str]) -> list[str]:
    path_flags = {
        "--attestation",
        "--autotrader-state",
        "--bodies-dir",
        "--body",
        "--checkpoints-dir",
        "--confidential-state",
        "--headers-dir",
        "--index",
        "--manifest",
        "--mirror-root",
        "--oracle-reporter-state",
        "--oracle-state",
        "--out",
        "--out-dir",
        "--perp-state",
        "--prev-header",
        "--prev-snapshot",
        "--profile",
        "--proof-metadata-dir",
        "--proof-mining-state",
        "--source-root",
        "--tau-app-state",
        "--tau-chain-balances",
        "--upba-state",
        "--zusd-state",
        "--pre-snapshot",
    }
    out: list[str] = []
    previous = ""
    for index, item in enumerate(command):
        if index == 0 and item in {"python", "python3"}:
            out.append(sys.executable)
        elif item.startswith("tools/") and item.endswith(".py"):
            out.append(str(ROOT / item))
        elif previous in path_flags:
            out.append(str(_manifest_relative_path(manifest_path, item)))
        else:
            out.append(item)
        previous = item
    return out


def _run_verify(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VERIFY_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_local(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(RUN_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_bundle(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_BUNDLE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_feature_lane(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_FEATURE_LANE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_feature_suite(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_FEATURE_SUITE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_core_feature_suite(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_CORE_FEATURE_SUITE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_assurance_feature_suite(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_ASSURANCE_FEATURE_SUITE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_public_testnet_bundle(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_PUBLIC_TESTNET_BUNDLE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_dual_operator_rehearsal(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(DUAL_OPERATOR_REHEARSAL_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_feature_suite(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(RUN_FEATURE_SUITE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_testnet_status(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_TESTNET_STATUS_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_operator_rehearsal(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(OPERATOR_REHEARSAL_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_make_signer_registry(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_SIGNER_REGISTRY_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_verify_signature_quorum(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VERIFY_SIGNATURE_QUORUM_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_manifest(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(RUN_MANIFEST_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_export_tau_packet(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(EXPORT_TAU_PACKET_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_attest(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ATTEST_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_verify_mirror_index(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VERIFY_MIRROR_INDEX_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_sign_artifact(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SIGN_ARTIFACT_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_verify_artifact_signature(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VERIFY_ARTIFACT_SIGNATURE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _run_publish_mirror(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(PUBLISH_MIRROR_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _write_chain(tmp_path: Path) -> tuple[Path, Path, list[dict[str, object]], list[dict[str, object]]]:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    headers_dir.mkdir()
    bodies_dir.mkdir()

    body1 = _body(1, nonce=1)
    header1 = _header(body1, prev_header_hash=ZERO_ROOT)
    body2 = _body(2, nonce=2)
    header2 = _header(body2, prev_header_hash=canonical_header_hash_v0(header1))

    _write_json(headers_dir / "1.json", header1)
    _write_json(headers_dir / "2.json", header2)
    _write_json(bodies_dir / "1.json", body1)
    _write_json(bodies_dir / "2.json", body2)
    return headers_dir, bodies_dir, [header1, header2], [body1, body2]


def test_verify_cli_accepts_valid_chain(tmp_path: Path) -> None:
    headers_dir, bodies_dir, headers, _ = _write_chain(tmp_path)

    proc = _run_verify(
        "--headers-dir",
        str(headers_dir),
        "--bodies-dir",
        str(bodies_dir),
        "--from-height",
        "1",
        "--to-height",
        "2",
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["checked_heights"] == [1, 2]
    assert payload["last_header_hash"] == canonical_header_hash_v0(headers[-1])


def test_verify_cli_rejects_tampered_body(tmp_path: Path) -> None:
    headers_dir, bodies_dir, _, bodies = _write_chain(tmp_path)
    tampered = dict(bodies[1])
    tampered["transactions"] = [{"sender": "mallory", "nonce": 99}]
    _write_json(bodies_dir / "2.json", tampered)

    proc = _run_verify(
        "--headers-dir",
        str(headers_dir),
        "--bodies-dir",
        str(bodies_dir),
        "--from-height",
        "1",
        "--to-height",
        "2",
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == [1]
    assert "height_2_invalid" in payload["errors"][0]


def test_verify_cli_rejects_bad_prev_header_hash(tmp_path: Path) -> None:
    headers_dir, bodies_dir, headers, _ = _write_chain(tmp_path)
    bad_header = dict(headers[1])
    bad_header["prev_header_hash"] = _root("wrong-prev")
    _write_json(headers_dir / "2.json", bad_header)

    proc = _run_verify(
        "--headers-dir",
        str(headers_dir),
        "--bodies-dir",
        str(bodies_dir),
        "--from-height",
        "1",
        "--to-height",
        "2",
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == [1]
    assert "prev_header_hash mismatch" in payload["errors"][0]


def test_verify_cli_supports_trusted_mid_chain_start(tmp_path: Path) -> None:
    headers_dir, bodies_dir, headers, _ = _write_chain(tmp_path)

    proc = _run_verify(
        "--headers-dir",
        str(headers_dir),
        "--bodies-dir",
        str(bodies_dir),
        "--from-height",
        "2",
        "--to-height",
        "2",
        "--trusted-prev-header-hash",
        canonical_header_hash_v0(headers[0]),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["checked_heights"] == [2]


def test_run_local_builds_block_that_verify_accepts(tmp_path: Path) -> None:
    body = _body(1)
    body_path = tmp_path / "input_body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert Path(payload["header_path"]).is_file()
    assert Path(payload["body_path"]).is_file()
    assert Path(payload["checkpoint_path"]).is_file()

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr

    verify_payload = json.loads(verify.stdout)
    assert verify_payload["ok"] is True
    assert verify_payload["checked_heights"] == [1]


def test_run_local_builds_structured_proof_metadata(tmp_path: Path) -> None:
    body = _body(1)
    body_path = tmp_path / "input_body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
        "--proof-kind",
        "risc0_zkvm_v0",
        "--proof-program-id",
        "risc0:zenodex-spot-transition-v1",
        "--proof-verifier-id",
        "risc0:receipt-verifier-v1",
        "--proof-commitment",
        _root("proof-commitment"),
        "--proof-public-input-hash",
        _root("public-input"),
        "--proof-raw-journal-hash",
        _root("raw-journal"),
        "--conflict-schedule-hash",
        _root("sequential-schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    metadata_path = Path(str(payload["proof_metadata_path"]))
    assert metadata_path.is_file()

    header = json.loads(Path(str(payload["header_path"])).read_text(encoding="utf-8"))
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    assert header["proof_journal_hash"] == payload["proof_journal_hash"]
    validate_proof_metadata_header_binding_v0(metadata, header)

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr

    verify_with_metadata = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify_with_metadata.returncode == 0, verify_with_metadata.stderr
    verify_with_metadata_payload = json.loads(verify_with_metadata.stdout)
    assert verify_with_metadata_payload["proof_metadata_checked_heights"] == [1]


def test_proof_required_profile_requires_metadata_and_verifier_report_replay(tmp_path: Path) -> None:
    body = _body(1)
    body_path = tmp_path / "input_body.json"
    out_dir = tmp_path / "ledger"
    config = _root("config")
    sequencer = _root("sequencer-set")
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        sequencer,
        "--config-digest",
        config,
        "--module-versions-digest",
        _root("modules"),
        "--proof-kind",
        "risc0_zkvm_v0",
        "--proof-program-id",
        "risc0:zenodex-spot-transition-v1",
        "--proof-verifier-id",
        "risc0:receipt-verifier-v1",
        "--proof-commitment",
        _root("proof-commitment"),
        "--proof-public-input-hash",
        _root("public-input"),
        "--proof-raw-journal-hash",
        _root("raw-journal"),
        "--conflict-schedule-hash",
        _root("sequential-schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
    )
    assert proc.returncode == 0, proc.stderr

    profile = sample_tau_exclusive_release_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="ZENO",
        token_asset_id=_root("zeno-token"),
    )
    profile_path = tmp_path / "profile.json"
    _write_json(profile_path, profile)

    missing_metadata = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert missing_metadata.returncode == 1
    missing_payload = json.loads(missing_metadata.stdout)
    assert "profile_requires_proof_metadata_dir" in missing_payload["errors"]

    metadata_only = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert metadata_only.returncode == 1
    metadata_only_payload = json.loads(metadata_only.stdout)
    assert "profile_requires_proof_verification_report_dir" in metadata_only_payload["errors"]

    report_dir = tmp_path / "proof_verification_reports"
    report_dir.mkdir()
    payload = json.loads(proc.stdout)
    header = json.loads(Path(str(payload["header_path"])).read_text(encoding="utf-8"))
    metadata = json.loads(Path(str(payload["proof_metadata_path"])).read_text(encoding="utf-8"))
    _write_json(
        report_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
            "ok": True,
            "metadata_path": str(payload["proof_metadata_path"]),
            "proof_journal_hash": header["proof_journal_hash"],
            "proof_kind": metadata["proof_kind"],
            "program_id": metadata["program_id"],
            "verifier_id": metadata["verifier_id"],
            "toolchain_lock_hash": metadata["toolchain_lock_hash"],
            "header_bound": True,
            "body_checked": True,
            "body_tx_execution_order_commitment_checked": False,
            "post_app_hash_checked": True,
            "post_state_root_checked": False,
            "pre_state_root_checked": False,
            "risc0_verified": True,
        },
    )

    with_report = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert with_report.returncode == 0, with_report.stderr
    with_payload = json.loads(with_report.stdout)
    assert with_payload["proof_metadata_checked_heights"] == [1]
    assert with_payload["proof_verification_checked_heights"] == [1]


def test_verify_can_require_proof_verification_report_replay(tmp_path: Path) -> None:
    body = _body(1)
    body_path = tmp_path / "input_body.json"
    out_dir = tmp_path / "ledger"
    report_dir = tmp_path / "proof_verification_reports"
    report_dir.mkdir()
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
        "--proof-kind",
        "risc0_zkvm_v0",
        "--proof-program-id",
        "risc0:zenodex-spot-transition-v1",
        "--proof-verifier-id",
        "risc0:receipt-verifier-v1",
        "--proof-commitment",
        _root("proof-commitment"),
        "--proof-public-input-hash",
        _root("public-input"),
        "--proof-raw-journal-hash",
        _root("raw-journal"),
        "--conflict-schedule-hash",
        _root("sequential-schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
    )
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    header = json.loads(Path(str(payload["header_path"])).read_text(encoding="utf-8"))
    metadata = json.loads(Path(str(payload["proof_metadata_path"])).read_text(encoding="utf-8"))
    _write_json(
        report_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
            "ok": True,
            "metadata_path": str(payload["proof_metadata_path"]),
            "proof_journal_hash": header["proof_journal_hash"],
            "proof_kind": metadata["proof_kind"],
            "program_id": metadata["program_id"],
            "verifier_id": metadata["verifier_id"],
            "toolchain_lock_hash": metadata["toolchain_lock_hash"],
            "header_bound": True,
            "body_checked": True,
            "body_tx_execution_order_commitment_checked": False,
            "post_app_hash_checked": True,
            "post_state_root_checked": False,
            "pre_state_root_checked": False,
            "risc0_verified": True,
        },
    )

    missing_report_dir = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert missing_report_dir.returncode == 1
    missing_payload = json.loads(missing_report_dir.stdout)
    assert "require_proof_verification_report_requires_dir" in missing_payload["errors"]

    with_report = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert with_report.returncode == 0, with_report.stderr
    with_report_payload = json.loads(with_report.stdout)
    assert with_report_payload["proof_metadata_checked_heights"] == [1]
    assert with_report_payload["proof_verification_checked_heights"] == [1]

    signed_required_without_inputs = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--require-proof-verification-report",
        "--require-proof-verification-report-signature",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert signed_required_without_inputs.returncode == 1
    signed_required_without_inputs_payload = json.loads(signed_required_without_inputs.stdout)
    assert (
        "require_proof_verification_report_signature_requires_registry_and_envelope_dir"
        in signed_required_without_inputs_payload["errors"]
    )

    envelope_dir = tmp_path / "proof_verification_report_envelopes"
    envelope_dir.mkdir()
    envelope_a_path = tmp_path / "proof_verification_report.a.sig.json"
    envelope_b_path = tmp_path / "proof_verification_report.b.sig.json"
    registry_path = tmp_path / "proof_report_signer_registry.json"
    sign_a = _run_sign_artifact(
        "--artifact",
        str(report_dir / "1.json"),
        "--payload-kind",
        "proof_verification_report",
        "--signer-id",
        "proof-verifier-a",
        "--key-id",
        "release-bls-key-a",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY,
        "--out",
        str(envelope_a_path),
    )
    assert sign_a.returncode == 0, sign_a.stderr
    public_key_a = json.loads(sign_a.stdout)["envelope"]["public_key"]
    sign_b = _run_sign_artifact(
        "--artifact",
        str(report_dir / "1.json"),
        "--payload-kind",
        "proof_verification_report",
        "--signer-id",
        "proof-verifier-b",
        "--key-id",
        "release-bls-key-b",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY_2,
        "--out",
        str(envelope_b_path),
    )
    assert sign_b.returncode == 0, sign_b.stderr
    public_key_b = json.loads(sign_b.stdout)["envelope"]["public_key"]
    make_registry = _run_make_signer_registry(
        "--registry-id",
        "proof-report-verifiers-v0",
        "--payload-kind",
        "proof_verification_report",
        "--threshold",
        "2",
        "--signer",
        f"proof-verifier-a:release-bls-key-a:{public_key_a}:1",
        "--signer",
        f"proof-verifier-b:release-bls-key-b:{public_key_b}:1",
        "--out",
        str(registry_path),
    )
    assert make_registry.returncode == 0, make_registry.stderr
    _write_json(
        envelope_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.proof_verification_report_envelopes.v0",
            "envelopes": [
                json.loads(envelope_a_path.read_text(encoding="utf-8")),
                json.loads(envelope_b_path.read_text(encoding="utf-8")),
            ],
        },
    )
    with_signed_report = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--proof-verification-report-registry",
        str(registry_path),
        "--proof-verification-report-envelope-dir",
        str(envelope_dir),
        "--require-proof-verification-report",
        "--require-proof-verification-report-signature",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert with_signed_report.returncode == 0, with_signed_report.stderr
    signed_payload = json.loads(with_signed_report.stdout)
    assert signed_payload["proof_verification_signature_checked_heights"] == [1]
    signed_quorum_reports = signed_payload["proof_verification_signature_quorum_reports"]
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    assert signed_quorum_reports == [
        {
            "height": 1,
            "registry_hash": registry["registry_hash"],
            "quorum_report_hash": signed_quorum_reports[0]["quorum_report_hash"],
            "accepted_weight": 2,
            "threshold": 2,
        }
    ]
    assert isinstance(signed_quorum_reports[0]["quorum_report_hash"], str)
    assert signed_quorum_reports[0]["quorum_report_hash"].startswith("0x")

    _write_json(
        envelope_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.proof_verification_report_envelopes.v0",
            "envelopes": [json.loads(envelope_a_path.read_text(encoding="utf-8"))],
        },
    )
    insufficient_signed_report = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--proof-verification-report-registry",
        str(registry_path),
        "--proof-verification-report-envelope-dir",
        str(envelope_dir),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert insufficient_signed_report.returncode == 1
    insufficient_signed_payload = json.loads(insufficient_signed_report.stdout)
    assert "signature quorum threshold not met" in insufficient_signed_payload["errors"][0]
    _write_json(
        envelope_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.proof_verification_report_envelopes.v0",
            "envelopes": [
                json.loads(envelope_a_path.read_text(encoding="utf-8")),
                json.loads(envelope_b_path.read_text(encoding="utf-8")),
            ],
        },
    )

    semantically_unbound = json.loads((report_dir / "1.json").read_text(encoding="utf-8"))
    semantically_unbound["post_app_hash_checked"] = False
    semantically_unbound["post_state_root_checked"] = False
    _write_json(report_dir / "1.json", semantically_unbound)
    rejected_semantic = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert rejected_semantic.returncode == 1
    semantic_payload = json.loads(rejected_semantic.stdout)
    assert "risc0 proof verification report must bind post_app_hash to header" in semantic_payload["errors"][0]

    body_unchecked = json.loads((report_dir / "1.json").read_text(encoding="utf-8"))
    body_unchecked["body_checked"] = False
    body_unchecked["post_app_hash_checked"] = True
    _write_json(report_dir / "1.json", body_unchecked)
    rejected_body_unchecked = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert rejected_body_unchecked.returncode == 1
    body_unchecked_payload = json.loads(rejected_body_unchecked.stdout)
    assert "risc0 proof verification report must be body-checked" in body_unchecked_payload["errors"][0]

    bad = json.loads((report_dir / "1.json").read_text(encoding="utf-8"))
    bad["body_checked"] = True
    bad["post_app_hash_checked"] = True
    bad["risc0_verified"] = False
    _write_json(report_dir / "1.json", bad)
    rejected = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--proof-metadata-dir",
        str(out_dir / "proof_metadata"),
        "--proof-verification-report-dir",
        str(report_dir),
        "--require-proof-verification-report",
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert rejected.returncode == 1
    rejected_payload = json.loads(rejected.stdout)
    assert "risc0 proof verification report must be verifier-backed" in rejected_payload["errors"][0]


def test_run_local_chains_to_previous_header(tmp_path: Path) -> None:
    out_dir = tmp_path / "ledger"
    body1 = _body(1)
    body2 = _body(2, nonce=2)
    body1_path = tmp_path / "body1.json"
    body2_path = tmp_path / "body2.json"
    _write_json(body1_path, body1)
    _write_json(body2_path, body2)

    first = _run_local(
        "--body",
        str(body1_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state-1"),
        "--post-state-root",
        _root("post-state-1"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )
    assert first.returncode == 0, first.stderr

    second = _run_local(
        "--body",
        str(body2_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000002",
        "--prev-header",
        str(out_dir / "headers" / "1.json"),
        "--pre-state-root",
        _root("pre-state-2"),
        "--post-state-root",
        _root("post-state-2"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )
    assert second.returncode == 0, second.stderr

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "2",
    )
    assert verify.returncode == 0, verify.stderr
    verify_payload = json.loads(verify.stdout)
    assert verify_payload["ok"] is True
    assert verify_payload["checked_heights"] == [1, 2]


def test_verify_cli_rejects_tampered_checkpoint(tmp_path: Path) -> None:
    out_dir = tmp_path / "ledger"
    body_path = tmp_path / "body.json"
    _write_json(body_path, _body(1))
    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )
    assert proc.returncode == 0, proc.stderr
    checkpoint_path = out_dir / "checkpoints" / "1.json"
    checkpoint = json.loads(checkpoint_path.read_text(encoding="utf-8"))
    checkpoint["app_hash"] = _root("bad-app")
    _write_json(checkpoint_path, checkpoint)

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 1
    payload = json.loads(verify.stdout)
    assert "checkpoint/header binding mismatch" in payload["errors"][0]


def test_verify_cli_accepts_local_profile_admission(tmp_path: Path) -> None:
    out_dir = tmp_path / "ledger"
    body_path = tmp_path / "body.json"
    config = _root("config")
    sequencer = _root("sequencer-set")
    _write_json(body_path, _body(1))
    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        sequencer,
        "--config-digest",
        config,
        "--module-versions-digest",
        _root("modules"),
    )
    assert proc.returncode == 0, proc.stderr
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
    )
    profile_path = tmp_path / "profile.json"
    _write_json(profile_path, profile)

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr
    payload = json.loads(verify.stdout)
    assert payload["ok"] is True


def test_verify_cli_rejects_tau_exclusive_profile_without_proof(tmp_path: Path) -> None:
    out_dir = tmp_path / "ledger"
    body_path = tmp_path / "body.json"
    config = _root("config")
    sequencer = _root("sequencer-set")
    _write_json(body_path, _body(1))
    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-state-root",
        _root("pre-state"),
        "--post-state-root",
        _root("post-state"),
        "--sequencer-set-hash",
        sequencer,
        "--config-digest",
        config,
        "--module-versions-digest",
        _root("modules"),
    )
    assert proc.returncode == 0, proc.stderr
    profile = sample_tau_exclusive_release_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="ZENO",
        token_asset_id=_root("zeno-token"),
    )
    profile_path = tmp_path / "profile.json"
    _write_json(profile_path, profile)

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 1
    payload = json.loads(verify.stdout)
    assert "profile_requires_proof_metadata_dir" in payload["errors"]


def test_run_local_with_snapshot_executes_dex_operations(tmp_path: Path) -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "01" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    genesis = DexState(balances=balances, pools={}, lp_balances=LPTable())
    genesis_path = tmp_path / "genesis.json"
    _write_json(genesis_path, snapshot_from_state(genesis).data)

    tx = {
        "tx_id": "create-pool-1",
        "block_timestamp": 0,
        "tx_sender_pubkey": sender,
        "operations": {
            "2": [
                _create_pool_intent_dict(
                    intent_id=intent_id,
                    sender=sender,
                    asset0=asset0,
                    asset1=asset1,
                )
            ]
        },
    }
    body = _body(1, txs=[tx])
    body_path = tmp_path / "body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-snapshot",
        str(genesis_path),
        "--allow-missing-settlement",
        "--disable-intent-signatures",
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    post_snapshot_path = Path(payload["post_snapshot_path"])
    post_snapshot = json.loads(post_snapshot_path.read_text(encoding="utf-8"))
    assert len(post_snapshot["pools"]) == 1
    assert post_snapshot["balances"] == []
    assert any(row["pubkey"] == sender for row in post_snapshot["lp_balances"])

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr


def test_run_local_with_snapshot_commits_rejected_transactions(tmp_path: Path) -> None:
    genesis = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    genesis_path = tmp_path / "genesis.json"
    _write_json(genesis_path, snapshot_from_state(genesis).data)

    body = _body(1, txs=[{"tx_id": "bad-tx", "block_timestamp": 0}])
    body_path = tmp_path / "body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, body)

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--pre-snapshot",
        str(genesis_path),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    output_body = json.loads(Path(payload["body_path"]).read_text(encoding="utf-8"))
    receipts = json.loads(Path(payload["receipts_path"]).read_text(encoding="utf-8"))
    post_snapshot = json.loads(Path(payload["post_snapshot_path"]).read_text(encoding="utf-8"))

    assert receipts[0]["accepted"] is False
    assert receipts[0]["state_changed"] is False
    assert receipts[0]["error_code"] == "transactions_0_operations_is_required"
    assert output_body["evidence"]["rejection_receipts"][-1] == receipts[0]
    assert post_snapshot == snapshot_from_state(genesis).data

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr


def test_run_local_with_tau_app_state_executes_app_bridge_streams(tmp_path: Path) -> None:
    sender = "00" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    app_state_path = tmp_path / "app_state.json"
    app_state_path.write_text("", encoding="utf-8")

    tx = {
        "tx_id": "tau-app-create-pool",
        "block_timestamp": 123,
        "tx_sender_pubkey": sender,
        "operations": {
            "7": {"mint": [[sender, asset0, 10_000], [sender, asset1, 10_000]]},
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "CREATE_POOL",
                    "intent_id": "0x" + "aa" * 32,
                    "sender_pubkey": sender,
                    "deadline": 9_999_999_999,
                    "nonce": 1,
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": 30,
                    "amount0": 1000,
                    "amount1": 2000,
                }
            ],
        },
    }
    body_path = tmp_path / "body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, _body(1, txs=[tx]))

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--tau-app-state",
        str(app_state_path),
        "--tau-chain-id",
        "zeno-ledger-devnet-0",
        "--tau-enable-faucet",
        "--allow-missing-settlement",
        "--disable-intent-signatures",
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    post_app_state = json.loads(Path(payload["post_app_state_path"]).read_text(encoding="utf-8"))
    assert isinstance(post_app_state.get("pools"), list)
    assert len(post_app_state["pools"]) == 1
    assert Path(payload["receipts_path"]).is_file()

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr


def test_run_local_with_tau_app_state_commits_app_rejection_receipts(tmp_path: Path) -> None:
    sender = "00" * 48
    app_state_path = tmp_path / "app_state.json"
    app_state_path.write_text("", encoding="utf-8")

    tx = {
        "tx_id": "tau-app-bad-token-op",
        "block_timestamp": 123,
        "tx_sender_pubkey": sender,
        "operations": {
            "9": [
                {
                    "module": "TauToken",
                    "action": "transfer",
                    "asset": "0x" + "11" * 32,
                    "to_pubkey": sender,
                    "amount": 1,
                }
            ]
        },
    }
    body_path = tmp_path / "body.json"
    out_dir = tmp_path / "ledger"
    _write_json(body_path, _body(1, txs=[tx]))

    proc = _run_local(
        "--body",
        str(body_path),
        "--out-dir",
        str(out_dir),
        "--time-ms",
        "1778730000001",
        "--tau-app-state",
        str(app_state_path),
        "--tau-chain-id",
        "zeno-ledger-devnet-0",
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--config-digest",
        _root("config"),
        "--module-versions-digest",
        _root("modules"),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    output_body = json.loads(Path(payload["body_path"]).read_text(encoding="utf-8"))
    receipts = json.loads(Path(payload["receipts_path"]).read_text(encoding="utf-8"))
    post_app_state = json.loads(Path(payload["post_app_state_path"]).read_text(encoding="utf-8"))

    assert receipts[0]["accepted"] is False
    assert receipts[0]["state_changed"] is False
    assert receipts[0]["error_code"] == "token_op_0_nonce_must_be_a_positive_int"
    assert output_body["evidence"]["rejection_receipts"][-1] == receipts[0]
    assert post_app_state.get("pools") == []

    verify = _run_verify(
        "--headers-dir",
        str(out_dir / "headers"),
        "--bodies-dir",
        str(out_dir / "bodies"),
        "--checkpoints-dir",
        str(out_dir / "checkpoints"),
        "--from-height",
        "1",
        "--to-height",
        "1",
    )
    assert verify.returncode == 0, verify.stderr


def test_make_testnet_bundle_can_run_and_verify_bootstrap_scenario(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True

    manifest_path, manifest = _load_manifest(report)
    profile = json.loads(_manifest_relative_path(manifest_path, manifest["profile_path"]).read_text(encoding="utf-8"))
    assert profile["deployment_mode"] == "zeno_sovereign_testnet"
    assert profile["tau_net_adapter_required"] is False
    assert profile["bridge_policy"]["requires_tau_checkpoint"] is False

    assert len(manifest["body_paths"]) == 5
    assert len(manifest["run_commands"]) == 5
    assert "attest_command" in manifest
    assert "attestation_path" in manifest
    assert "mirror_index_command" in manifest
    assert "mirror_index_path" in manifest
    run_reports = []
    for command in manifest["run_commands"]:
        run = subprocess.run(
            _resolve_command_against_manifest(manifest_path, command),
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
        assert run.returncode == 0, run.stderr
        run_report = json.loads(run.stdout)
        assert run_report["ok"] is True
        run_reports.append(run_report)
    post_snapshot = json.loads(Path(run_reports[-1]["post_snapshot_path"]).read_text(encoding="utf-8"))
    receipts = json.loads(Path(run_reports[-1]["receipts_path"]).read_text(encoding="utf-8"))
    assert len(post_snapshot["pools"]) == 1
    assert receipts[0]["accepted"] is False
    assert receipts[0]["error_code"] == "transactions_0_operations_is_required"

    verify = subprocess.run(
        _resolve_command_against_manifest(manifest_path, manifest["verify_command"]),
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["checked_heights"] == [1, 2, 3, 4, 5]


def test_make_testnet_bundle_rejects_proof_required_without_verifier_reports(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir), "--proof-required")

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report == {
        "schema": "zenodex.zeno_ledger.make_testnet_bundle_report.v0",
        "ok": False,
        "status": "rejected",
        "errors": ["proof_required_bundle_requires_verifier_report_generation"],
    }


def test_run_manifest_executes_generated_testnet_bundle(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))

    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["checked_heights"] == [1, 2, 3, 4, 5]
    assert len(runner_report["block_reports"]) == 5
    assert runner_report["verify_report"]["stdout_json"]["ok"] is True
    assert runner_report["attest_report"]["stdout_json"]["ok"] is True
    assert Path(runner_report["attest_report"]["stdout_json"]["attestation_path"]).is_file()
    assert runner_report["mirror_index_report"]["stdout_json"]["ok"] is True
    assert Path(runner_report["mirror_index_report"]["stdout_json"]["mirror_index_path"]).is_file()


def test_watcher_attestation_binds_verified_sovereign_range(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr

    manifest_path, manifest = _load_manifest(report)
    ledger_out_dir = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
    attestation_path = tmp_path / "watcher.json"
    attest = _run_attest(
        "--headers-dir",
        str(ledger_out_dir / "headers"),
        "--bodies-dir",
        str(ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        str(ledger_out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "5",
        "--watcher-id",
        "test-watcher",
        "--observed-time-ms",
        "1778730006000",
        "--out",
        str(attestation_path),
    )

    assert attest.returncode == 0, attest.stderr
    attest_report = json.loads(attest.stdout)
    assert attest_report["ok"] is True
    attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    profile = json.loads(profile_path.read_text(encoding="utf-8"))
    assert attestation["status"] == "range_verified"
    assert attestation["deployment_mode"] == "zeno_sovereign_testnet"
    assert attestation["checked_heights"] == [1, 2, 3, 4, 5]
    assert attestation["last_header_hash"] == attest_report["verify_report"]["last_header_hash"]
    history = attest_report["verify_report"]["app_hashes_by_height"]
    assert [row["height"] for row in history] == [1, 2, 3, 4, 5]
    headers_dir = ledger_out_dir / "headers"
    header_1 = json.loads((headers_dir / "1.json").read_text(encoding="utf-8"))
    header_5 = json.loads((headers_dir / "5.json").read_text(encoding="utf-8"))
    assert history[0]["app_hash"] == header_1["app_hash"]
    assert history[-1]["app_hash"] == header_5["app_hash"]
    assert history[-1]["app_hash"] == attest_report["verify_report"]["last_app_hash"]
    assert attest_report["verify_report"]["app_hash_history_root"] == app_hash_history_merkle_root_v0(history)
    assert attest_report["verify_report"]["checked_range"] == {
        "from_height": 1,
        "to_height": 5,
        "height_count": 5,
    }
    assert attest_report["verify_report"]["checked_range_hash"] == checked_range_hash_v0(
        checked_range_summary_v0([1, 2, 3, 4, 5])
    )
    validate_watcher_attestation_v0(
        attestation=attestation,
        verify_report=attest_report["verify_report"],
        profile=profile,
    )
    checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_v0(
        watcher_attestations=[attestation],
        verify_reports=[attest_report["verify_report"]],
        state_hash="0x" + ("ab" * 32),
        snapshot_height=1,
        profile=profile,
        required_watcher_count=1,
    )
    assert checkpoint["source_kind"] == "zeno_ledger_watcher_app_hash_history_v0"
    assert checkpoint["snapshot_height"] == 1
    assert checkpoint["latest_height"] == 5
    assert checkpoint["app_hash"] == header_1["app_hash"]
    assert checkpoint["range_tip_app_hash"] == header_5["app_hash"]
    compact_proof = build_app_hash_history_merkle_proof_v0(history, snapshot_height=1)
    compact_checkpoint = build_tau_finality_checkpoint_from_watcher_app_hash_history_proof_v0(
        watcher_attestations=[attestation],
        verify_reports=[attest_report["verify_report"]],
        app_hash_history_proofs=[compact_proof],
        state_hash="0x" + ("ab" * 32),
        snapshot_height=1,
        profile=profile,
        required_watcher_count=1,
    )
    assert compact_checkpoint["source_kind"] == "zeno_ledger_watcher_app_hash_history_merkle_v0"
    assert compact_checkpoint["snapshot_height"] == 1
    assert compact_checkpoint["latest_height"] == 5
    assert compact_checkpoint["app_hash"] == header_1["app_hash"]
    assert compact_checkpoint["range_tip_app_hash"] == header_5["app_hash"]
    assert compact_checkpoint["app_hash_history_roots"] == [
        attest_report["verify_report"]["app_hash_history_root"]
    ]
    compact_report = attest_report["compact_verify_report"]
    compact_attestation = attest_report["compact_attestation"]
    assert "checked_heights" not in compact_report
    assert "app_hashes_by_height" not in compact_report
    assert "checked_heights" not in compact_attestation
    assert compact_report["checked_range_hash"] == attest_report["verify_report"]["checked_range_hash"]
    compact_range_checkpoint = build_tau_finality_checkpoint_from_compact_watcher_app_hash_history_proof_v0(
        watcher_attestations=[compact_attestation],
        verify_reports=[compact_report],
        app_hash_history_proofs=[compact_proof],
        state_hash="0x" + ("ab" * 32),
        snapshot_height=1,
        profile=profile,
        required_watcher_count=1,
    )
    assert compact_range_checkpoint["source_kind"] == "zeno_ledger_compact_watcher_app_hash_history_merkle_v0"
    assert compact_range_checkpoint["snapshot_height"] == 1
    assert compact_range_checkpoint["latest_height"] == 5
    assert compact_range_checkpoint["app_hash"] == header_1["app_hash"]
    assert compact_range_checkpoint["checked_range"] == {"from_height": 1, "to_height": 5, "height_count": 5}
    assert "checked_heights" not in compact_range_checkpoint

    tampered_report = json.loads(json.dumps(attest_report["verify_report"]))
    tampered_report["app_hashes_by_height"][0]["app_hash"] = header_5["app_hash"]
    try:
        validate_watcher_attestation_v0(
            attestation=attestation,
            verify_report=tampered_report,
            profile=profile,
        )
    except ValueError as exc:
        assert "binding mismatch" in str(exc)
    else:
        raise AssertionError("tampered app_hashes_by_height accepted")


def test_watcher_attestation_rejects_tampered_verified_range(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr

    manifest_path, manifest = _load_manifest(report)
    ledger_out_dir = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
    body_path = ledger_out_dir / "bodies" / "5.json"
    body = json.loads(body_path.read_text(encoding="utf-8"))
    body["transactions"] = []
    _write_json(body_path, body)

    attest = _run_attest(
        "--headers-dir",
        str(ledger_out_dir / "headers"),
        "--bodies-dir",
        str(ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        str(ledger_out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "5",
        "--watcher-id",
        "test-watcher",
        "--observed-time-ms",
        "1778730006000",
    )

    assert attest.returncode == 1
    attest_report = json.loads(attest.stdout)
    assert attest_report["ok"] is False
    assert attest_report["verify_report"]["ok"] is False


def test_mirror_index_binds_public_testnet_artifacts(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["mirror_index_report"]["stdout_json"]["ok"] is True

    manifest_path, manifest = _load_manifest(report)
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    mirror_index = json.loads(mirror_index_path.read_text(encoding="utf-8"))
    assert mirror_index["artifact_count"] >= 1
    assert all(not Path(entry["relative_path"]).is_absolute() for entry in mirror_index["artifacts"])
    assert any(entry["relative_path"] == "manifest.json" for entry in mirror_index["artifacts"])
    assert any(entry["relative_path"] == "profile.json" for entry in mirror_index["artifacts"])
    assert any(entry["relative_path"] == "watcher_attestations/bootstrap_range_1_5.json" for entry in mirror_index["artifacts"])
    validate_mirror_index_v0(index=mirror_index, mirror_root=bundle_dir)

    verify = _run_verify_mirror_index(
        "--index",
        str(mirror_index_path),
        "--mirror-root",
        str(bundle_dir),
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["mirror_index_hash"] == mirror_index["mirror_index_hash"]


def test_mirror_index_rejects_tampered_artifact(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    body_path = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"]) / "bodies" / "5.json"
    body = json.loads(body_path.read_text(encoding="utf-8"))
    body["transactions"] = []
    _write_json(body_path, body)

    verify = _run_verify_mirror_index(
        "--index",
        str(_manifest_relative_path(manifest_path, manifest["mirror_index_path"])),
        "--mirror-root",
        str(bundle_dir),
    )
    assert verify.returncode == 1
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is False
    assert any("binding mismatch" in error for error in verify_report["errors"])


def test_testnet_status_binds_mirror_and_watcher_attestation(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    attestation_path = _manifest_relative_path(manifest_path, manifest["attestation_path"])
    status_path = tmp_path / "testnet_status.json"

    status_proc = _run_make_testnet_status(
        "--network-id",
        "zeno-ledger-devnet-0",
        "--mirror-index",
        str(mirror_index_path),
        "--mirror-root",
        str(bundle_dir),
        "--watcher-attestation",
        str(attestation_path),
        "--out",
        str(status_path),
    )

    assert status_proc.returncode == 0, status_proc.stderr
    status_report = json.loads(status_proc.stdout)
    assert status_report["ok"] is True
    status = json.loads(status_path.read_text(encoding="utf-8"))
    mirror_index = json.loads(mirror_index_path.read_text(encoding="utf-8"))
    attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    assert status["network_id"] == "zeno-ledger-devnet-0"
    assert status["mirror_index_hash"] == mirror_index["mirror_index_hash"]
    assert status["watcher_count"] == 1
    assert status["watchers"][0]["attestation_hash"] == attestation["attestation_hash"]
    validate_testnet_status_v0(
        status=status,
        mirror_index=mirror_index,
        mirror_root=bundle_dir,
        watcher_attestations=[attestation],
    )


def test_testnet_status_rejects_tampered_watcher_attestation(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    attestation_path = _manifest_relative_path(manifest_path, manifest["attestation_path"])
    bad_attestation_path = tmp_path / "bad_attestation.json"
    bad_attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    bad_attestation["last_header_hash"] = _root("bad-status-header")
    _write_json(bad_attestation_path, bad_attestation)

    status_proc = _run_make_testnet_status(
        "--network-id",
        "zeno-ledger-devnet-0",
        "--mirror-index",
        str(_manifest_relative_path(manifest_path, manifest["mirror_index_path"])),
        "--mirror-root",
        str(bundle_dir),
        "--watcher-attestation",
        str(bad_attestation_path),
    )

    assert status_proc.returncode == 1
    status_report = json.loads(status_proc.stdout)
    assert status_report["ok"] is False
    assert "watcher attestation hash mismatch" in status_report["errors"][0]


def test_testnet_status_rejects_disagreeing_watcher_ranges(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    ledger_out_dir = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    attestation_path = _manifest_relative_path(manifest_path, manifest["attestation_path"])
    short_attestation_path = tmp_path / "short_range_attestation.json"
    short_attest = _run_attest(
        "--headers-dir",
        str(ledger_out_dir / "headers"),
        "--bodies-dir",
        str(ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        str(ledger_out_dir / "checkpoints"),
        "--profile",
        str(profile_path),
        "--from-height",
        "1",
        "--to-height",
        "4",
        "--watcher-id",
        "short-range-watcher",
        "--observed-time-ms",
        "1778730006000",
        "--out",
        str(short_attestation_path),
    )
    assert short_attest.returncode == 0, short_attest.stderr

    status_proc = _run_make_testnet_status(
        "--network-id",
        "zeno-ledger-devnet-0",
        "--mirror-index",
        str(mirror_index_path),
        "--mirror-root",
        str(bundle_dir),
        "--watcher-attestation",
        str(attestation_path),
        "--watcher-attestation",
        str(short_attestation_path),
    )

    assert status_proc.returncode == 1
    status_report = json.loads(status_proc.stdout)
    assert status_report["ok"] is False
    assert "watcher attestations must agree on range and final roots" in status_report["errors"][0]


def test_make_feature_lane_manifest_runs_custom_body_sequence(tmp_path: Path) -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    genesis = DexState(balances=balances, pools={}, lp_balances=LPTable())

    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    body1_path = source_dir / "body1.json"
    body2_path = source_dir / "body2.json"
    out_dir = tmp_path / "feature_lane"

    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    tx1 = {
        "tx_id": "feature-create-pool",
        "block_timestamp": 0,
        "tx_sender_pubkey": sender,
        "operations": {
            "2": [
                _create_pool_intent_dict(
                    intent_id="0x" + "91" * 32,
                    sender=sender,
                    asset0=asset0,
                    asset1=asset1,
                )
            ]
        },
    }
    tx2 = {
        "tx_id": "feature-rejected-missing-operations",
        "block_timestamp": 1,
    }
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(genesis).data)
    _write_json(body1_path, _body(1, txs=[tx1]))
    _write_json(body2_path, _body(2, txs=[tx2]))

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--module-versions-digest",
        modules,
        "--allow-missing-settlement",
        "--disable-intent-signatures",
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["bundle_kind"] == "feature_lane"
    assert manifest["body_paths"] == ["bodies/1.json", "bodies/2.json"]

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["checked_heights"] == [1, 2]
    assert runner_report["attest_report"]["stdout_json"]["ok"] is True
    assert runner_report["mirror_index_report"]["stdout_json"]["ok"] is True
    post_snapshot = json.loads((out_dir / "ledger" / "snapshots" / "2.json").read_text(encoding="utf-8"))
    receipts = json.loads((out_dir / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8"))
    assert len(post_snapshot["pools"]) == 1
    assert receipts[0]["accepted"] is False


def test_make_feature_lane_manifest_relativizes_repo_relative_generated_paths() -> None:
    from tools.zeno_ledger_make_feature_lane import _relativize_command

    lane_root = Path("dist/feature-lane-relpath-regression")
    command = [
        sys.executable,
        "tools/zeno_ledger_run_local.py",
        "--body",
        "dist/feature-lane-relpath-regression/bodies/1.json",
        "--out-dir",
        "dist/feature-lane-relpath-regression/ledger",
        "--profile",
        "dist/feature-lane-relpath-regression/profile.json",
    ]

    assert _relativize_command(command, root=lane_root) == [
        "python3",
        "tools/zeno_ledger_run_local.py",
        "--body",
        "bodies/1.json",
        "--out-dir",
        "ledger",
        "--profile",
        "profile.json",
    ]


def test_make_feature_lane_manifest_supports_tau_app_bridge_mode(tmp_path: Path) -> None:
    sender = "00" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    app_state_path = source_dir / "app_state.json"
    body_path = source_dir / "body.json"
    out_dir = tmp_path / "tau_feature_lane"
    app_state_path.write_text("", encoding="utf-8")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    tx = {
        "tx_id": "feature-tau-app-create-pool",
        "block_timestamp": 123,
        "tx_sender_pubkey": sender,
        "operations": {
            "7": {"mint": [[sender, asset0, 10_000], [sender, asset1, 10_000]]},
            "5": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "CREATE_POOL",
                    "intent_id": "0x" + "92" * 32,
                    "sender_pubkey": sender,
                    "deadline": 9_999_999_999,
                    "nonce": 1,
                    "asset0": asset0,
                    "asset1": asset1,
                    "fee_bps": 30,
                    "amount0": 1000,
                    "amount1": 2000,
                }
            ],
        },
    }
    _write_json(profile_path, profile)
    _write_json(body_path, _body(1, txs=[tx]))

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--tau-app-state",
        str(app_state_path),
        "--tau-chain-id",
        "zeno-ledger-devnet-0",
        "--tau-enable-faucet",
        "--body",
        str(body_path),
        "--module-versions-digest",
        modules,
        "--allow-missing-settlement",
        "--disable-intent-signatures",
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "tau_app"
    assert manifest["tau_app_state_path"] == "tau_app_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_app_state = json.loads((out_dir / "ledger" / "app_states" / "1.json").read_text(encoding="utf-8"))
    receipts = json.loads((out_dir / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8"))
    assert len(post_app_state["pools"]) == 1
    assert receipts[0]["accepted"] is True


def test_make_feature_lane_manifest_supports_perp_mode(tmp_path: Path) -> None:
    from src.core.perp_epoch import perp_epoch_isolated_default_initial_state

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    perp_state_path = source_dir / "perp_state.json"
    body1_path = source_dir / "perp_body1.json"
    body2_path = source_dir / "perp_body2.json"
    body3_path = source_dir / "perp_body3.json"
    out_dir = tmp_path / "perp_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    perp_state = perp_epoch_isolated_default_initial_state()
    perp_state["oracle_seen"] = True
    perp_state["oracle_last_update_epoch"] = 0
    perp_state["index_price_e8"] = 100_000_000
    _write_json(profile_path, profile)
    _write_json(perp_state_path, perp_state)
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "perp-open-position",
                    "block_timestamp": 1,
                    "perp_commands": [
                        {"action": "deposit_collateral", "params": {"amount": 20_000, "auth_ok": True}},
                        {"action": "set_position", "params": {"new_position_base": 100_000, "auth_ok": True}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "perp-apply-funding",
                    "block_timestamp": 2,
                    "perp_commands": [
                        {"action": "advance_epoch", "params": {"delta": 1}},
                        {"action": "apply_funding", "params": {"new_rate_bps": 50, "auth_ok": True}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body3_path,
        _body(
            3,
            txs=[
                {
                    "tx_id": "perp-rejected-withdraw",
                    "block_timestamp": 3,
                    "perp_commands": [
                        {"action": "withdraw_collateral", "params": {"amount": 999_999, "auth_ok": True}},
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--perp-state",
        str(perp_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--body",
        str(body3_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "perp"
    assert manifest["perp_state_path"] == "perp_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_perp_state = json.loads((out_dir / "ledger" / "perp_states" / "3.json").read_text(encoding="utf-8"))
    receipts = json.loads((out_dir / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    assert post_perp_state["position_base"] == 100_000
    assert post_perp_state["collateral_quote"] == 19_500
    assert post_perp_state["funding_paid_cumulative"] == 500
    assert receipts[0]["accepted"] is False


def test_make_feature_lane_manifest_supports_oracle_mode(tmp_path: Path) -> None:
    from src.core.oracle import init_oracle_state

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    oracle_state_path = source_dir / "oracle_state.json"
    body1_path = source_dir / "oracle_body1.json"
    body2_path = source_dir / "oracle_body2.json"
    body3_path = source_dir / "oracle_body3.json"
    out_dir = tmp_path / "oracle_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    _write_json(profile_path, profile)
    _write_json(oracle_state_path, dict(init_oracle_state(max_staleness_seconds=300).__dict__))
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "oracle-update",
                    "block_timestamp": 1,
                    "oracle_commands": [
                        {"action": "update_price_timestamp", "args": {"current_timestamp": 100}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "oracle-fresh-check",
                    "block_timestamp": 2,
                    "oracle_commands": [
                        {"action": "require_fresh", "args": {"current_timestamp": 350}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body3_path,
        _body(
            3,
            txs=[
                {
                    "tx_id": "oracle-stale-check",
                    "block_timestamp": 3,
                    "oracle_commands": [
                        {"action": "require_fresh", "args": {"current_timestamp": 401}},
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--oracle-state",
        str(oracle_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--body",
        str(body3_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "oracle"
    assert manifest["oracle_state_path"] == "oracle_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_oracle_state = json.loads((out_dir / "ledger" / "oracle_states" / "3.json").read_text(encoding="utf-8"))
    receipts = json.loads((out_dir / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    assert post_oracle_state["price_timestamp"] == 100
    assert post_oracle_state["max_staleness_seconds"] == 300
    assert receipts[0]["accepted"] is False
    assert "oracle_not_fresh" in receipts[0]["error_code"]


def test_make_feature_lane_manifest_supports_oracle_reporter_mode(tmp_path: Path) -> None:
    from tools.zenodex_oracle_reporter_lifecycle import sample_lifecycle
    from tools.zenodex_oracle_reporter_token_settlement_replay import sample_settlement_replay

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    oracle_reporter_state_path = source_dir / "oracle_reporter_state.json"
    body1_path = source_dir / "oracle_reporter_body1.json"
    body2_path = source_dir / "oracle_reporter_body2.json"
    body3_path = source_dir / "oracle_reporter_body3.json"
    body4_path = source_dir / "oracle_reporter_body4.json"
    out_dir = tmp_path / "oracle_reporter_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    good_trace = sample_lifecycle()
    bad_trace = json.loads(json.dumps(good_trace))
    bad_trace["events"] = [
        {
            "type": "submit_report",
            "epoch": 1,
            "report_id": good_trace["events"][2]["report_id"],
            "query_id": good_trace["events"][2]["query_id"],
            "value_hash": good_trace["events"][2]["value_hash"],
        }
    ]
    good_settlement = sample_settlement_replay()
    bad_settlement = json.loads(json.dumps(good_settlement))
    bad_settlement["policy"]["approved"] = False
    _write_json(profile_path, profile)
    _write_json(
        oracle_reporter_state_path,
        {
            "schema": "zenodex/oracle_reporter_ledger_state/v1",
            "accepted_lifecycle_count": 0,
            "accepted_token_settlement_count": 0,
            "last_result": None,
            "last_token_settlement_result": None,
        },
    )
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "oracle-reporter-lifecycle",
                    "block_timestamp": 1,
                    "oracle_reporter_commands": [
                        {"action": "verify_lifecycle_trace", "args": {"trace": good_trace}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "oracle-reporter-rejected",
                    "block_timestamp": 2,
                    "oracle_reporter_commands": [
                        {"action": "verify_lifecycle_trace", "args": {"trace": bad_trace}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body3_path,
        _body(
            3,
            txs=[
                {
                    "tx_id": "oracle-reporter-token-settlement",
                    "block_timestamp": 3,
                    "oracle_reporter_commands": [
                        {"action": "verify_token_settlement_replay", "args": {"replay": good_settlement}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body4_path,
        _body(
            4,
            txs=[
                {
                    "tx_id": "oracle-reporter-token-settlement-rejected",
                    "block_timestamp": 4,
                    "oracle_reporter_commands": [
                        {"action": "verify_token_settlement_replay", "args": {"replay": bad_settlement}},
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--oracle-reporter-state",
        str(oracle_reporter_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--body",
        str(body3_path),
        "--body",
        str(body4_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "oracle_reporter"
    assert manifest["oracle_reporter_state_path"] == "oracle_reporter_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_state = json.loads((out_dir / "ledger" / "oracle_reporter_states" / "4.json").read_text(encoding="utf-8"))
    first_receipts = json.loads((out_dir / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8"))
    second_receipts = json.loads((out_dir / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8"))
    third_receipts = json.loads((out_dir / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    fourth_receipts = json.loads((out_dir / "ledger" / "receipts" / "4.json").read_text(encoding="utf-8"))
    assert post_state["accepted_lifecycle_count"] == 1
    assert post_state["accepted_token_settlement_count"] == 1
    assert post_state["last_reporter_id"] == "reporter.sample"
    assert post_state["total_slashed"] == 10
    assert post_state["total_withdrawn"] == 90
    assert post_state["token_transfer_count"] == 14
    assert post_state["token_total_debits_e8"] == post_state["token_total_credits_e8"]
    assert first_receipts[0]["accepted"] is True
    assert second_receipts[0]["accepted"] is False
    assert "report_submitted_by_inactive_reporter" in second_receipts[0]["error_code"]
    assert third_receipts[0]["accepted"] is True
    assert fourth_receipts[0]["accepted"] is False
    assert "policy_not_governance_approved" in fourth_receipts[0]["error_code"]


def test_make_feature_lane_manifest_supports_upba_mode(tmp_path: Path) -> None:
    from tools.zeno_ledger_run_local import _load_upba_ref_v0

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    upba_state_path = source_dir / "upba_state.json"
    body_paths = [source_dir / f"upba_body{i}.json" for i in range(1, 7)]
    out_dir = tmp_path / "upba_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    upba_ref = _load_upba_ref_v0()
    _write_json(profile_path, profile)
    _write_json(upba_state_path, dict(upba_ref.init_state().__dict__))
    bodies = [
        _body(
            1,
            txs=[
                {
                    "tx_id": "upba-add-intents",
                    "block_timestamp": 1,
                    "upba_commands": [
                        {
                            "tag": "add_intent",
                            "args": {"amount_in": 100, "min_amount_out": 70, "auth_ok": True},
                        },
                        {
                            "tag": "add_intent",
                            "args": {"amount_in": 50, "min_amount_out": 30, "auth_ok": True},
                        },
                    ],
                }
            ],
        ),
        _body(
            2,
            txs=[
                {
                    "tx_id": "upba-close-collection",
                    "block_timestamp": 2,
                    "upba_commands": [{"tag": "close_collection", "args": {"operator_auth": True}}],
                }
            ],
        ),
        _body(
            3,
            txs=[
                {
                    "tx_id": "upba-submit-solution",
                    "block_timestamp": 3,
                    "upba_commands": [
                        {
                            "tag": "submit_solution",
                            "args": {
                                "solver_id": 1,
                                "proposed_clearing_price_bps": 7333,
                                "surplus_extracted_bps": 2666,
                                "clearing_valid_witness": True,
                            },
                        }
                    ],
                }
            ],
        ),
        _body(
            4,
            txs=[
                {
                    "tx_id": "upba-finalize-winner",
                    "block_timestamp": 4,
                    "upba_commands": [{"tag": "finalize_winner", "args": {"operator_auth": True}}],
                }
            ],
        ),
        _body(
            5,
            txs=[
                {
                    "tx_id": "upba-execute-fills",
                    "block_timestamp": 5,
                    "upba_commands": [
                        {
                            "tag": "execute_fill",
                            "args": {
                                "fill_input_amount": 100,
                                "fill_output_amount": 75,
                                "fill_min_guaranteed": 70,
                                "fill_valid_witness": True,
                            },
                        },
                        {
                            "tag": "execute_fill",
                            "args": {
                                "fill_input_amount": 50,
                                "fill_output_amount": 35,
                                "fill_min_guaranteed": 30,
                                "fill_valid_witness": True,
                            },
                        },
                    ],
                }
            ],
        ),
        _body(
            6,
            txs=[
                {
                    "tx_id": "upba-complete-batch",
                    "block_timestamp": 6,
                    "upba_commands": [
                        {
                            "tag": "complete_batch",
                            "args": {
                                "protocol_fee_amount": 40,
                                "solver_reward_amount": 0,
                                "conservation_witness": True,
                            },
                        }
                    ],
                }
            ],
        ),
    ]
    for path, body in zip(body_paths, bodies, strict=True):
        _write_json(path, body)

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--upba-state",
        str(upba_state_path),
        "--body",
        str(body_paths[0]),
        "--body",
        str(body_paths[1]),
        "--body",
        str(body_paths[2]),
        "--body",
        str(body_paths[3]),
        "--body",
        str(body_paths[4]),
        "--body",
        str(body_paths[5]),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "upba"
    assert manifest["upba_state_path"] == "upba_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_upba_state = json.loads((out_dir / "ledger" / "upba_states" / "6.json").read_text(encoding="utf-8"))
    receipts = json.loads((out_dir / "ledger" / "receipts" / "6.json").read_text(encoding="utf-8"))
    assert post_upba_state["phase"] == "Complete"
    assert post_upba_state["intent_count"] == 2
    assert post_upba_state["settled_count"] == 2
    assert post_upba_state["total_input_collected"] == 150
    assert post_upba_state["total_filled_input"] == 150
    assert post_upba_state["total_actual_output"] == 110
    assert post_upba_state["total_guaranteed_output"] == 100
    assert post_upba_state["fees_captured"] == 40
    assert receipts[0]["accepted"] is True


def test_make_feature_lane_manifest_supports_proof_mining_mode(tmp_path: Path) -> None:
    from src.core.proof_mining_claims import build_proof_mining_claim, explicit_proposal_hash
    from src.core.proof_mining_manager import ProofMiningManagerSnapshot
    from src.integration.proof_mining_context import ProofMiningContext, proof_mining_context_to_obj
    from src.integration.proof_mining_runtime import (
        ProofMiningRuntimeState,
        proof_mining_runtime_state_to_obj,
    )

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    proof_mining_state_path = source_dir / "proof_mining_state.json"
    body1_path = source_dir / "proof_mining_body1.json"
    body2_path = source_dir / "proof_mining_body2.json"
    out_dir = tmp_path / "proof_mining_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    runtime_state = ProofMiningRuntimeState(
        reward_pool_pubkey="proof-mining-pool",
        snapshot=ProofMiningManagerSnapshot(
            epoch=1,
            base_reward=8,
            initial_pool=20,
            reward_pool_balance=20,
            total_paid=0,
            claimed_slots={},
        ),
    )
    witness_hash = "sha256:feature-lane-proof-mining-witness"
    prev_state_hash = "sha256:feature-lane-proof-mining-prev"
    batch_hash = "sha256:feature-lane-proof-mining-batch"
    dex_hash_after = "sha256:feature-lane-proof-mining-after"
    proposal_hash = explicit_proposal_hash(
        chain_id="zeno-ledger-devnet-0",
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
    )
    context = ProofMiningContext(
        chain_id="zeno-ledger-devnet-0",
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        witness_hash=witness_hash,
        dex_hash_after=dex_hash_after,
        proposal_hash=proposal_hash,
        proof_scheme="zeno-ledger-feature-lane-proof-v0",
    )
    claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "feature-lane-proof-mining-job",
            "winner": {
                "miner_id": "proof-miner-0",
                "witness_sha256": witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="feature-lane-proof-mining-round-v0",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id="zeno-ledger-devnet-0",
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )
    duplicate_claim = build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "feature-lane-proof-mining-job",
            "winner": {
                "miner_id": "proof-miner-0",
                "witness_sha256": witness_hash,
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="feature-lane-proof-mining-round-v1",
        reward_pool_before=16,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=2,
        chain_id="zeno-ledger-devnet-0",
        prev_state_hash=prev_state_hash,
        batch_hash=batch_hash,
        dex_hash_after=dex_hash_after,
    )
    _write_json(profile_path, profile)
    _write_json(proof_mining_state_path, proof_mining_runtime_state_to_obj(runtime_state))
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "proof-mining-submit",
                    "block_timestamp": 1,
                    "proof_mining_commands": [
                        {
                            "action": "submit_claim",
                            "args": {
                                "claim_artifact": claim,
                                "proof_mining_context": proof_mining_context_to_obj(context),
                                "actual_reward_pool_balance": 20,
                            },
                        }
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "proof-mining-duplicate-rejected",
                    "block_timestamp": 2,
                    "proof_mining_commands": [
                        {
                            "action": "submit_claim",
                            "args": {
                                "claim_artifact": duplicate_claim,
                                "proof_mining_context": proof_mining_context_to_obj(context),
                                "actual_reward_pool_balance": 16,
                            },
                        }
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--proof-mining-state",
        str(proof_mining_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "proof_mining"
    assert manifest["proof_mining_state_path"] == "proof_mining_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_state = json.loads((out_dir / "ledger" / "proof_mining_states" / "2.json").read_text(encoding="utf-8"))
    first_receipts = json.loads((out_dir / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8"))
    second_receipts = json.loads((out_dir / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8"))
    assert post_state["reward_pool_balance"] == 16
    assert post_state["total_paid"] == 4
    assert len(post_state["claimed_slots"]) == 1
    assert first_receipts[0]["accepted"] is True
    assert second_receipts[0]["accepted"] is False
    assert "already_claimed" in second_receipts[0]["error_code"]


def test_make_feature_lane_manifest_supports_autotrader_mode(tmp_path: Path) -> None:
    from src.agents.policy_compiler import compile_policy_candidate
    from src.core.quote_receipts import make_route_quote_receipt
    from src.core.routing import best_route_exact_in_2hop
    from src.integration.autotrader_controller import AutoTraderControllerState
    from src.state.pools import PoolState, PoolStatus
    from tools.zeno_ledger_run_local import _autotrader_controller_state_to_obj, _pool_state_to_obj

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    autotrader_state_path = source_dir / "autotrader_state.json"
    body1_path = source_dir / "autotrader_body1.json"
    body2_path = source_dir / "autotrader_body2.json"
    body3_path = source_dir / "autotrader_body3.json"
    out_dir = tmp_path / "autotrader_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    strategy = compile_policy_candidate(
        {
            "strategy_id": "feature.autotrader.dca.1",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "local",
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
                "budget_window_epochs": 0,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": 3,
                "max_intents_per_order": 16,
            },
            "template_params": {
                "fixed_order_size": 100,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
            "tau_policy_specs": [],
        }
    ).strategy
    pools = {
        "p_ab": PoolState(
            pool_id="p_ab",
            asset0="A",
            asset1="B",
            reserve0=1_000,
            reserve1=2_000,
            fee_bps=10,
            lp_supply=1,
            status=PoolStatus.ACTIVE,
            created_at=0,
        )
    }
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=quote,
        pools_by_id=pools,
        quote_epoch=5,
    )
    bad_receipt = json.loads(json.dumps(receipt))
    bad_receipt["body"]["amount_in"] = 90
    pools_obj = {pool_id: _pool_state_to_obj(pool) for pool_id, pool in pools.items()}
    _write_json(profile_path, profile)
    _write_json(autotrader_state_path, _autotrader_controller_state_to_obj(AutoTraderControllerState()))
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "autotrader-submit",
                    "block_timestamp": 1,
                    "autotrader_commands": [
                        {
                            "action": "evaluate_quote_receipt",
                            "args": {
                                "strategy": strategy.to_dict(),
                                "receipt": receipt,
                                "pools_by_id": pools_obj,
                                "current_epoch": 5,
                                "intent_deadline": 99,
                            },
                        }
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "autotrader-stale-skip",
                    "block_timestamp": 2,
                    "autotrader_commands": [
                        {
                            "action": "evaluate_quote_receipt",
                            "args": {
                                "strategy": strategy.to_dict(),
                                "receipt": receipt,
                                "pools_by_id": pools_obj,
                                "current_epoch": 9,
                                "intent_deadline": 99,
                            },
                        }
                    ],
                }
            ],
        ),
    )
    _write_json(
        body3_path,
        _body(
            3,
            txs=[
                {
                    "tx_id": "autotrader-rejected-amount",
                    "block_timestamp": 3,
                    "autotrader_commands": [
                        {
                            "action": "evaluate_quote_receipt",
                            "args": {
                                "strategy": strategy.to_dict(),
                                "receipt": bad_receipt,
                                "pools_by_id": pools_obj,
                                "current_epoch": 9,
                                "intent_deadline": 99,
                            },
                        }
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--autotrader-state",
        str(autotrader_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--body",
        str(body3_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "autotrader"
    assert manifest["autotrader_state_path"] == "autotrader_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_state = json.loads((out_dir / "ledger" / "autotrader_states" / "3.json").read_text(encoding="utf-8"))
    first_receipts = json.loads((out_dir / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8"))
    second_receipts = json.loads((out_dir / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8"))
    third_receipts = json.loads((out_dir / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    assert post_state["last_action_epoch"] == 5
    assert post_state["lifetime_spent"] == 100
    assert post_state["live_orders"] == 1
    assert post_state["budget_state"]["window_id"] == 1
    assert post_state["budget_state"]["spent_in_window"] == 100
    assert first_receipts[0]["accepted"] is True
    assert first_receipts[0]["state_changed"] is True
    assert second_receipts[0]["accepted"] is True
    assert second_receipts[0]["state_changed"] is False
    assert third_receipts[0]["accepted"] is False
    assert "receipt_amount_mismatch" in third_receipts[0]["error_code"]


def test_make_feature_lane_manifest_supports_confidential_mode(tmp_path: Path) -> None:
    from src.core.confidential_extension_receipts import make_confidential_extension_receipt
    from src.core.fhe_sealed_bid_alpha import FHECipherBid, compile_fhe_sealed_bid_alpha_plan
    from src.core.sealed_bid_auction import RevealedSealedBid

    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    modules = _root("feature-lane-modules")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    confidential_state_path = source_dir / "confidential_state.json"
    body1_path = source_dir / "confidential_body1.json"
    body2_path = source_dir / "confidential_body2.json"
    body3_path = source_dir / "confidential_body3.json"
    out_dir = tmp_path / "confidential_feature_lane"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    nitro_pcr0 = "a" * 96
    nitro_pcr8 = "b" * 96
    measurement = f"nitro:pcr0:{nitro_pcr0}:pcr8:{nitro_pcr8}"
    policy_digest = "0x" + ("d" * 64)
    confidential_receipt = make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-feature-confidential-1",
        policy_version="tee-policy-v1",
        policy_digest=policy_digest,
        measurement=measurement,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    plain_bids = [
        RevealedSealedBid("alice", "c1", 3, 10),
        RevealedSealedBid("bob", "c2", 4, 9),
        RevealedSealedBid("carol", "c3", 2, 11),
    ]
    fhe_receipt = compile_fhe_sealed_bid_alpha_plan(
        auction_id="feature-fhe-auction-v0",
        units_for_sale=5,
        bids=plain_bids,
        cipher_bids=[
            FHECipherBid("alice", "c1", "ct:q:alice", "ct:p:alice"),
            FHECipherBid("bob", "c2", "ct:q:bob", "ct:p:bob"),
            FHECipherBid("carol", "c3", "ct:q:carol", "ct:p:carol"),
        ],
        key_id="fhe-key-1",
    )
    _write_json(profile_path, profile)
    _write_json(
        confidential_state_path,
        {
            "schema": "zenodex/confidential_ledger_state/v1",
            "approved_measurements": [measurement],
            "approved_fhe_key_ids": ["fhe-key-1"],
            "expected_policy_digest": policy_digest,
            "used_requests": [],
            "accepted_live_admission_count": 0,
            "accepted_fhe_plan_count": 0,
            "last_receipt_hash": None,
            "last_fhe_receipt_hash": None,
            "last_auction_id": None,
        },
    )
    _write_json(
        body1_path,
        _body(
            1,
            txs=[
                {
                    "tx_id": "confidential-live-admission",
                    "block_timestamp": 1,
                    "confidential_commands": [
                        {"action": "validate_live_admission", "args": {"receipt": confidential_receipt}},
                    ],
                }
            ],
        ),
    )
    _write_json(
        body2_path,
        _body(
            2,
            txs=[
                {
                    "tx_id": "confidential-fhe-plan",
                    "block_timestamp": 2,
                    "confidential_commands": [
                        {
                            "action": "verify_fhe_alpha_plan",
                            "args": {
                                "receipt": fhe_receipt,
                                "trusted_plain_bids": [dict(bid.__dict__) for bid in plain_bids],
                            },
                        }
                    ],
                }
            ],
        ),
    )
    _write_json(
        body3_path,
        _body(
            3,
            txs=[
                {
                    "tx_id": "confidential-replay-rejected",
                    "block_timestamp": 3,
                    "confidential_commands": [
                        {"action": "validate_live_admission", "args": {"receipt": confidential_receipt}},
                    ],
                }
            ],
        ),
    )

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--confidential-state",
        str(confidential_state_path),
        "--body",
        str(body1_path),
        "--body",
        str(body2_path),
        "--body",
        str(body3_path),
        "--module-versions-digest",
        modules,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["execution_mode"] == "confidential"
    assert manifest["confidential_state_path"] == "confidential_state.json"

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    post_state = json.loads((out_dir / "ledger" / "confidential_states" / "3.json").read_text(encoding="utf-8"))
    first_receipts = json.loads((out_dir / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8"))
    second_receipts = json.loads((out_dir / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8"))
    third_receipts = json.loads((out_dir / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    assert post_state["accepted_live_admission_count"] == 1
    assert post_state["accepted_fhe_plan_count"] == 1
    assert post_state["last_auction_id"] == "feature-fhe-auction-v0"
    assert len(post_state["used_requests"]) == 1
    assert first_receipts[0]["accepted"] is True
    assert second_receipts[0]["accepted"] is True
    assert third_receipts[0]["accepted"] is False
    assert "request_replay" in third_receipts[0]["error_code"]


def test_make_feature_lane_rejects_noncontiguous_body_heights(tmp_path: Path) -> None:
    config = _root("feature-lane-config")
    sequencer = _root("feature-lane-sequencer")
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    body1_path = source_dir / "body1.json"
    body3_path = source_dir / "body3.json"
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-lane-token"),
    )
    _write_json(profile_path, profile)
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    _write_json(genesis_path, snapshot_from_state(empty_state).data)
    _write_json(body1_path, _body(1, txs=[]))
    _write_json(body3_path, _body(3, txs=[]))

    proc = _run_make_feature_lane(
        "--out-dir",
        str(tmp_path / "feature_lane"),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(body1_path),
        "--body",
        str(body3_path),
    )

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert "body heights must be contiguous" in report["errors"][0]


def test_feature_lane_runs_feature_gate_and_mirrors_report(tmp_path: Path) -> None:
    config = _root("feature-gate-config")
    sequencer = _root("feature-gate-sequencer")
    modules = _root("feature-gate-modules")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-gate-token"),
    )
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    body_path = source_dir / "body.json"
    out_dir = tmp_path / "feature_gate_lane"
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    gate_command = [
        sys.executable,
        "-c",
        "import json; print(json.dumps({'ok': True, 'feature': 'zusd_smoke'}))",
    ]
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(empty_state).data)
    _write_json(body_path, _body(1, txs=[]))

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(body_path),
        "--module-versions-digest",
        modules,
        "--feature-gate-command-json",
        json.dumps(gate_command),
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    manifest = json.loads(Path(report["manifest_path"]).read_text(encoding="utf-8"))
    assert manifest["feature_gate_commands"] == [["python3", *gate_command[1:]]]

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["feature_gate_reports"][0]["stdout_json"]["feature"] == "zusd_smoke"

    gate_report = json.loads((out_dir / "feature_gate_report.json").read_text(encoding="utf-8"))
    assert gate_report["gate_count"] == 1
    mirror_index = json.loads((out_dir / "mirror_index.json").read_text(encoding="utf-8"))
    validate_mirror_index_v0(index=mirror_index, mirror_root=out_dir)
    assert any(
        artifact["relative_path"] == "feature_gate_report.json"
        for artifact in mirror_index["artifacts"]
    )


def test_feature_lane_rejects_failed_feature_gate(tmp_path: Path) -> None:
    config = _root("feature-gate-config")
    sequencer = _root("feature-gate-sequencer")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-gate-token"),
    )
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    body_path = source_dir / "body.json"
    out_dir = tmp_path / "failed_feature_gate_lane"
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    gate_command = [
        sys.executable,
        "-c",
        "import json; print(json.dumps({'ok': False, 'reason': 'synthetic'}))",
    ]
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(empty_state).data)
    _write_json(body_path, _body(1, txs=[]))

    proc = _run_make_feature_lane(
        "--out-dir",
        str(out_dir),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(body_path),
        "--feature-gate-command-json",
        json.dumps(gate_command),
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 1
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is False
    assert "feature gate command returned ok=false" in runner_report["errors"][0]


def test_feature_suite_runs_multiple_feature_lane_manifests(tmp_path: Path) -> None:
    config = _root("feature-suite-config")
    sequencer = _root("feature-suite-sequencer")
    modules = _root("feature-suite-modules")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-suite-token"),
    )
    empty_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    empty_body_path = source_dir / "empty_body.json"
    reject_body_path = source_dir / "reject_body.json"
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(empty_state).data)
    _write_json(empty_body_path, _body(1, txs=[]))
    _write_json(reject_body_path, _body(1, txs=[{"tx_id": "suite-rejected", "block_timestamp": 1}]))

    empty_lane = _run_make_feature_lane(
        "--out-dir",
        str(tmp_path / "empty_lane"),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(empty_body_path),
        "--module-versions-digest",
        modules,
    )
    assert empty_lane.returncode == 0, empty_lane.stderr
    empty_lane_report = json.loads(empty_lane.stdout)

    reject_lane = _run_make_feature_lane(
        "--out-dir",
        str(tmp_path / "reject_lane"),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(reject_body_path),
        "--module-versions-digest",
        modules,
    )
    assert reject_lane.returncode == 0, reject_lane.stderr
    reject_lane_report = json.loads(reject_lane.stdout)

    suite_path = tmp_path / "feature_suite.json"
    make_suite = _run_make_feature_suite(
        "--suite-name",
        "ZenoLedger focused feature suite",
        "--lane",
        f"empty_block={empty_lane_report['manifest_path']}",
        "--lane",
        f"rejection_receipts={reject_lane_report['manifest_path']}",
        "--required-feature",
        "empty_block",
        "--required-feature",
        "rejection_receipts",
        "--out",
        str(suite_path),
    )
    assert make_suite.returncode == 0, make_suite.stderr
    suite_report = json.loads(make_suite.stdout)
    assert suite_report["ok"] is True

    runner = _run_feature_suite("--suite", str(suite_path), "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["covered_features"] == ["empty_block", "rejection_receipts"]
    assert all(lane["ok"] is True for lane in runner_report["lane_reports"])


def test_feature_suite_rejects_missing_required_feature(tmp_path: Path) -> None:
    config = _root("feature-suite-config")
    sequencer = _root("feature-suite-sequencer")
    modules = _root("feature-suite-modules")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("feature-suite-token"),
    )
    source_dir = tmp_path / "source"
    source_dir.mkdir()
    profile_path = source_dir / "profile.json"
    genesis_path = source_dir / "genesis.json"
    body_path = source_dir / "body.json"
    _write_json(profile_path, profile)
    _write_json(genesis_path, snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())).data)
    _write_json(body_path, _body(1, txs=[]))
    lane = _run_make_feature_lane(
        "--out-dir",
        str(tmp_path / "lane"),
        "--profile",
        str(profile_path),
        "--genesis-snapshot",
        str(genesis_path),
        "--body",
        str(body_path),
        "--module-versions-digest",
        modules,
    )
    assert lane.returncode == 0, lane.stderr
    lane_report = json.loads(lane.stdout)

    make_suite = _run_make_feature_suite(
        "--suite-name",
        "bad suite",
        "--lane",
        f"empty_block={lane_report['manifest_path']}",
        "--required-feature",
        "perps_lane",
        "--out",
        str(tmp_path / "suite.json"),
    )
    assert make_suite.returncode == 1
    report = json.loads(make_suite.stdout)
    assert report["ok"] is False
    assert "required feature lanes missing" in report["errors"][0]


def test_make_core_feature_suite_runs_spot_and_tau_adapter_lanes(tmp_path: Path) -> None:
    out_dir = tmp_path / "core_suite"
    proc = _run_make_core_feature_suite("--out-dir", str(out_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert Path(report["spot_bootstrap_manifest_path"]).is_file()
    assert Path(report["tau_app_bridge_manifest_path"]).is_file()
    assert Path(report["zusd_core_manifest_path"]).is_file()
    assert Path(report["perp_core_manifest_path"]).is_file()
    assert Path(report["oracle_core_manifest_path"]).is_file()
    assert Path(report["oracle_reporter_core_manifest_path"]).is_file()
    assert Path(report["upba_core_manifest_path"]).is_file()
    assert Path(report["proof_mining_core_manifest_path"]).is_file()
    assert Path(report["autotrader_core_manifest_path"]).is_file()
    assert Path(report["confidential_core_manifest_path"]).is_file()

    suite = json.loads(Path(report["suite_path"]).read_text(encoding="utf-8"))
    assert suite["feature_count"] == 10
    assert [entry["feature_id"] for entry in suite["features"]] == [
        "spot_bootstrap",
        "tau_app_bridge_spot",
        "zusd_core",
        "perp_core",
        "oracle_core",
        "oracle_reporter_core",
        "upba_core",
        "proof_mining_core",
        "autotrader_core",
        "confidential_core",
    ]

    runner = _run_feature_suite("--suite", report["suite_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["covered_features"] == [
        "spot_bootstrap",
        "tau_app_bridge_spot",
        "zusd_core",
        "perp_core",
        "oracle_core",
        "oracle_reporter_core",
        "upba_core",
        "proof_mining_core",
        "autotrader_core",
        "confidential_core",
    ]
    assert all(lane["ok"] is True for lane in runner_report["lane_reports"])

    suite_run_report_path = out_dir / "core_suite_run_report.json"
    status_path = out_dir / "core_suite_status.json"
    _write_json(suite_run_report_path, runner_report)
    spot_manifest_path = Path(report["spot_bootstrap_manifest_path"])
    spot_manifest = json.loads(spot_manifest_path.read_text(encoding="utf-8"))
    spot_mirror_index_path = _manifest_relative_path(spot_manifest_path, spot_manifest["mirror_index_path"])
    spot_attestation_path = _manifest_relative_path(spot_manifest_path, spot_manifest["attestation_path"])
    status_proc = _run_make_testnet_status(
        "--network-id",
        "zeno-ledger-devnet-0",
        "--mirror-index",
        str(spot_mirror_index_path),
        "--mirror-root",
        str(out_dir / "spot_bootstrap"),
        "--watcher-attestation",
        str(spot_attestation_path),
        "--feature-suite",
        report["suite_path"],
        "--feature-suite-run-report",
        str(suite_run_report_path),
        "--out",
        str(status_path),
    )
    assert status_proc.returncode == 0, status_proc.stderr
    status = json.loads(status_path.read_text(encoding="utf-8"))
    assert status["feature_suite"]["feature_count"] == 10
    assert status["feature_suite_run"]["covered_feature_count"] == 10

    tau_app_state = json.loads((out_dir / "tau_app_bridge_spot" / "ledger" / "app_states" / "1.json").read_text(encoding="utf-8"))
    assert len(tau_app_state["pools"]) == 1
    zusd_state = json.loads((out_dir / "zusd_core" / "ledger" / "zusd_states" / "4.json").read_text(encoding="utf-8"))
    zusd_receipts = json.loads((out_dir / "zusd_core" / "ledger" / "receipts" / "4.json").read_text(encoding="utf-8"))
    assert zusd_state["debt_e8"] == 100 * 100_000_000
    assert zusd_state["collateral_e8"] == 2 * 100_000_000
    assert zusd_receipts[0]["accepted"] is False
    perp_state = json.loads((out_dir / "perp_core" / "ledger" / "perp_states" / "5.json").read_text(encoding="utf-8"))
    perp_receipts = json.loads((out_dir / "perp_core" / "ledger" / "receipts" / "5.json").read_text(encoding="utf-8"))
    assert perp_state["position_base"] == 100_000
    assert perp_state["collateral_quote"] == 19_500
    assert perp_state["funding_paid_cumulative"] == 500
    assert perp_receipts[0]["accepted"] is False
    oracle_state = json.loads((out_dir / "oracle_core" / "ledger" / "oracle_states" / "3.json").read_text(encoding="utf-8"))
    oracle_receipts = json.loads((out_dir / "oracle_core" / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8"))
    assert oracle_state["price_timestamp"] == 100
    assert oracle_receipts[0]["accepted"] is False
    assert "oracle_not_fresh" in oracle_receipts[0]["error_code"]
    oracle_reporter_state = json.loads(
        (out_dir / "oracle_reporter_core" / "ledger" / "oracle_reporter_states" / "4.json").read_text(encoding="utf-8")
    )
    oracle_reporter_receipts_2 = json.loads(
        (out_dir / "oracle_reporter_core" / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8")
    )
    oracle_reporter_receipts_3 = json.loads(
        (out_dir / "oracle_reporter_core" / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8")
    )
    oracle_reporter_receipts_4 = json.loads(
        (out_dir / "oracle_reporter_core" / "ledger" / "receipts" / "4.json").read_text(encoding="utf-8")
    )
    assert oracle_reporter_state["accepted_lifecycle_count"] == 1
    assert oracle_reporter_state["accepted_token_settlement_count"] == 1
    assert oracle_reporter_state["last_reporter_id"] == "reporter.sample"
    assert oracle_reporter_state["total_slashed"] == 10
    assert oracle_reporter_state["total_withdrawn"] == 90
    assert oracle_reporter_state["token_transfer_count"] == 14
    assert oracle_reporter_state["token_total_debits_e8"] == oracle_reporter_state["token_total_credits_e8"]
    assert oracle_reporter_receipts_2[0]["accepted"] is False
    assert "report_submitted_by_inactive_reporter" in oracle_reporter_receipts_2[0]["error_code"]
    assert oracle_reporter_receipts_3[0]["accepted"] is True
    assert oracle_reporter_receipts_4[0]["accepted"] is False
    assert "policy_not_governance_approved" in oracle_reporter_receipts_4[0]["error_code"]
    upba_state = json.loads((out_dir / "upba_core" / "ledger" / "upba_states" / "6.json").read_text(encoding="utf-8"))
    assert upba_state["phase"] == "Complete"
    assert upba_state["intent_count"] == 2
    assert upba_state["settled_count"] == 2
    assert upba_state["total_input_collected"] == 150
    assert upba_state["total_actual_output"] == 110
    assert upba_state["fees_captured"] == 40
    proof_mining_state = json.loads(
        (out_dir / "proof_mining_core" / "ledger" / "proof_mining_states" / "2.json").read_text(encoding="utf-8")
    )
    proof_mining_receipts = json.loads(
        (out_dir / "proof_mining_core" / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8")
    )
    assert proof_mining_state["reward_pool_balance"] == 16
    assert proof_mining_state["total_paid"] == 4
    assert len(proof_mining_state["claimed_slots"]) == 1
    assert proof_mining_receipts[0]["accepted"] is False
    assert "already_claimed" in proof_mining_receipts[0]["error_code"]
    autotrader_state = json.loads(
        (out_dir / "autotrader_core" / "ledger" / "autotrader_states" / "3.json").read_text(encoding="utf-8")
    )
    autotrader_receipts_1 = json.loads(
        (out_dir / "autotrader_core" / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8")
    )
    autotrader_receipts_2 = json.loads(
        (out_dir / "autotrader_core" / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8")
    )
    autotrader_receipts_3 = json.loads(
        (out_dir / "autotrader_core" / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8")
    )
    assert autotrader_state["last_action_epoch"] == 5
    assert autotrader_state["lifetime_spent"] == 100
    assert autotrader_state["live_orders"] == 1
    assert autotrader_state["budget_state"]["spent_in_window"] == 100
    assert autotrader_receipts_1[0]["accepted"] is True
    assert autotrader_receipts_2[0]["accepted"] is True
    assert autotrader_receipts_2[0]["state_changed"] is False
    assert autotrader_receipts_3[0]["accepted"] is False
    assert "receipt_amount_mismatch" in autotrader_receipts_3[0]["error_code"]
    confidential_state = json.loads(
        (out_dir / "confidential_core" / "ledger" / "confidential_states" / "3.json").read_text(encoding="utf-8")
    )
    confidential_receipts_1 = json.loads(
        (out_dir / "confidential_core" / "ledger" / "receipts" / "1.json").read_text(encoding="utf-8")
    )
    confidential_receipts_2 = json.loads(
        (out_dir / "confidential_core" / "ledger" / "receipts" / "2.json").read_text(encoding="utf-8")
    )
    confidential_receipts_3 = json.loads(
        (out_dir / "confidential_core" / "ledger" / "receipts" / "3.json").read_text(encoding="utf-8")
    )
    assert confidential_state["accepted_live_admission_count"] == 1
    assert confidential_state["accepted_fhe_plan_count"] == 1
    assert confidential_state["last_auction_id"] == "core-suite-fhe-auction-v0"
    assert len(confidential_state["used_requests"]) == 1
    assert confidential_receipts_1[0]["accepted"] is True
    assert confidential_receipts_2[0]["accepted"] is True
    assert confidential_receipts_3[0]["accepted"] is False
    assert "request_replay" in confidential_receipts_3[0]["error_code"]


def test_make_public_testnet_bundle_runs_core_features_and_status(tmp_path: Path) -> None:
    out_dir = tmp_path / "public_testnet"
    proc = _run_make_public_testnet_bundle(
        "--out-dir",
        str(out_dir),
        "--network-id",
        "zeno-ledger-devnet-0",
        "--chain-id",
        "zeno-ledger-devnet-0",
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["covered_feature_count"] == 10
    assert report["covered_features"] == [
        "spot_bootstrap",
        "tau_app_bridge_spot",
        "zusd_core",
        "perp_core",
        "oracle_core",
        "oracle_reporter_core",
        "upba_core",
        "proof_mining_core",
        "autotrader_core",
        "confidential_core",
    ]

    launch_manifest = json.loads(Path(report["launch_manifest_path"]).read_text(encoding="utf-8"))
    assert launch_manifest["schema"] == "zenodex.zeno_ledger.public_testnet_bundle.v0"
    assert launch_manifest["tau_posture"]["preferred_release_adapter"] == "tau_net"
    assert launch_manifest["tau_posture"]["testnet_liveness_dependency"] == "zeno_ledger"
    assert launch_manifest["token_posture"]["testnet_scope"] == "zeno_ledger_testnet"
    assert launch_manifest["token_posture"]["release_scope"] == "tau_net_exclusive"
    assert [item["symbol"] for item in launch_manifest["test_token_catalog"]] == ["tAGRS", "tZDEX", "zUSD"]
    assert launch_manifest["token_posture"]["release_aligned_test_assets"] == ["tAGRS", "tZDEX", "zUSD"]
    assert launch_manifest["token_posture"]["default_faucet_token"] == "tAGRS"
    assert launch_manifest["token_posture"]["default_zusd_collateral"] == "tAGRS"
    assert launch_manifest["token_posture"]["default_spot_pool_symbols"] == ["tAGRS", "tZDEX"]
    assert launch_manifest["test_token_catalog"][2]["created_through_collateralized_zusd_flow"] is True
    assert launch_manifest["test_token_catalog"][2]["faucet_mint_allowed"] is False
    assert launch_manifest["testnet_faucet_posture"]["supports_fixture_mint"] is True

    status = json.loads(Path(report["testnet_status_path"]).read_text(encoding="utf-8"))
    assert status["network_id"] == "zeno-ledger-devnet-0"
    assert status["feature_suite"]["feature_count"] == 10
    assert status["feature_suite_run"]["covered_feature_count"] == 10

    feature_suite_manifest = json.loads(Path(report["core_suite_path"]).read_text(encoding="utf-8"))
    for feature in feature_suite_manifest["features"]:
        assert not Path(feature["manifest_path"]).is_absolute()

    bootstrap_manifest_path = Path(report["bootstrap_manifest_path"])
    bootstrap_manifest = json.loads(bootstrap_manifest_path.read_text(encoding="utf-8"))
    bootstrap_root = bootstrap_manifest_path.parent
    bootstrap_mirror_index_path = Path(bootstrap_manifest["mirror_index_path"])
    if not bootstrap_mirror_index_path.is_absolute():
        bootstrap_mirror_index_path = bootstrap_root / bootstrap_mirror_index_path
    bootstrap_attestation_path = Path(bootstrap_manifest["attestation_path"])
    if not bootstrap_attestation_path.is_absolute():
        bootstrap_attestation_path = bootstrap_root / bootstrap_attestation_path
    mirror_index = json.loads(bootstrap_mirror_index_path.read_text(encoding="utf-8"))
    attestation = json.loads(bootstrap_attestation_path.read_text(encoding="utf-8"))
    feature_suite = json.loads(Path(report["core_suite_path"]).read_text(encoding="utf-8"))
    feature_suite_run = json.loads(Path(report["core_suite_run_report_path"]).read_text(encoding="utf-8"))
    validate_testnet_status_v0(
        status=status,
        mirror_index=mirror_index,
        mirror_root=out_dir / "bootstrap",
        watcher_attestations=[attestation],
        feature_suite=feature_suite,
        feature_suite_run_report=feature_suite_run,
    )

    incomplete_run_path = tmp_path / "incomplete_core_suite_run_report.json"
    incomplete_run = dict(feature_suite_run)
    incomplete_run["covered_features"] = feature_suite_run["covered_features"][:-1]
    _write_json(incomplete_run_path, incomplete_run)
    incomplete_status = _run_make_testnet_status(
        "--network-id",
        "zeno-ledger-devnet-0",
        "--mirror-index",
        str(bootstrap_mirror_index_path),
        "--mirror-root",
        str(out_dir / "bootstrap"),
        "--watcher-attestation",
        str(bootstrap_attestation_path),
        "--feature-suite",
        report["core_suite_path"],
        "--feature-suite-run-report",
        str(incomplete_run_path),
    )
    assert incomplete_status.returncode == 1
    incomplete_status_report = json.loads(incomplete_status.stdout)
    assert incomplete_status_report["ok"] is False
    assert "feature suite coverage mismatch" in incomplete_status_report["errors"][0]


def test_operator_rehearsal_replays_copied_public_testnet_bundle(tmp_path: Path) -> None:
    out_dir = tmp_path / "public_testnet"
    proc = _run_make_public_testnet_bundle(
        "--out-dir",
        str(out_dir),
        "--network-id",
        "zeno-ledger-devnet-0",
        "--chain-id",
        "zeno-ledger-devnet-0",
    )
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True

    copied_bundle_dir = tmp_path / "operator_b_bundle_copy"
    shutil.copytree(out_dir, copied_bundle_dir)
    peer_attestation_path = copied_bundle_dir / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    operator_out_dir = tmp_path / "operator_b"
    rehearsal = _run_operator_rehearsal(
        "--bundle-root",
        str(copied_bundle_dir),
        "--operator-id",
        "operator-b",
        "--out-dir",
        str(operator_out_dir),
        "--observed-time-ms",
        "1778730015000",
        "--peer-watcher-attestation",
        str(peer_attestation_path),
    )

    assert rehearsal.returncode == 0, rehearsal.stderr
    rehearsal_report = json.loads(rehearsal.stdout)
    assert rehearsal_report["ok"] is True
    assert rehearsal_report["combined_watcher_count"] == 2
    assert rehearsal_report["peer_watcher_count"] == 1
    assert rehearsal_report["mirror_index_hash"]
    assert rehearsal_report["feature_suite_hash"]
    assert rehearsal_report["last_header_hash"]
    assert rehearsal_report["last_app_hash"]

    operator_attestation_path = Path(rehearsal_report["operator_attestation_path"])
    combined_status_path = Path(rehearsal_report["combined_testnet_status_path"])
    assert operator_attestation_path.is_file()
    assert combined_status_path.is_file()
    operator_attestation = json.loads(operator_attestation_path.read_text(encoding="utf-8"))
    combined_status = json.loads(combined_status_path.read_text(encoding="utf-8"))
    assert operator_attestation["watcher_id"] == "operator-b"
    assert combined_status["watcher_count"] == 2
    assert [watcher["watcher_id"] for watcher in combined_status["watchers"]] == [
        "bootstrap-watcher-0",
        "operator-b",
    ]
    assert combined_status["feature_suite_run"]["covered_feature_count"] == 10


def test_dual_operator_rehearsal_builds_matching_bundles_and_replays_copy(tmp_path: Path) -> None:
    proc = _run_dual_operator_rehearsal(
        "--out-dir",
        str(tmp_path / "dual_operator"),
        "--network-id",
        "zeno-ledger-devnet-0",
        "--chain-id",
        "zeno-ledger-devnet-0",
        "--observed-time-ms",
        "1778730015000",
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["independent_build_match"] is True
    assert report["operator_b_rehearsal_ok"] is True
    assert report["combined_watcher_count"] == 2
    assert report["covered_feature_count"] == 10
    assert report["testnet_status_hash"] == report["operator_a2_testnet_status_hash"]
    assert report["mirror_index_hash"] == report["operator_a2_mirror_index_hash"]
    assert report["feature_suite_hash"] == report["operator_a2_feature_suite_hash"]
    assert Path(report["report_path"]).is_file()
    assert Path(report["operator_b_bundle_root"]).is_dir()
    assert Path(report["operator_b_out_dir"]).is_dir()


def test_make_assurance_feature_suite_smoke_runs_feature_gates(tmp_path: Path) -> None:
    out_dir = tmp_path / "assurance_suite"
    proc = _run_make_assurance_feature_suite("--out-dir", str(out_dir), "--mode", "smoke")
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert set(report["features"]) == {
        "autotrader_evidence",
        "confidential_extension_evidence",
        "oracle_evidence",
        "perps_evidence",
        "proof_mining_evidence",
        "spot_evidence",
        "upba_batch_auction",
        "zusd_evidence",
    }

    runner = _run_feature_suite("--suite", report["suite_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    runner_report = json.loads(runner.stdout)
    assert runner_report["ok"] is True
    assert runner_report["covered_features"] == sorted(report["features"])
    assert all(lane["ok"] is True for lane in runner_report["lane_reports"])

    for feature_id in report["features"]:
        gate_report = json.loads((out_dir / feature_id / "feature_gate_report.json").read_text(encoding="utf-8"))
        assert gate_report["gate_count"] == 1
        assert gate_report["gate_reports"][0]["stdout_json"]["feature_id"] == feature_id
        mirror_index = json.loads((out_dir / feature_id / "mirror_index.json").read_text(encoding="utf-8"))
        validate_mirror_index_v0(index=mirror_index, mirror_root=out_dir / feature_id)
        assert any(
            artifact["relative_path"] == "feature_gate_report.json"
            for artifact in mirror_index["artifacts"]
        )


def test_export_tau_packet_binds_sovereign_checkpoint_without_tau_acceptance_claim(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr

    manifest_path, manifest = _load_manifest(report)
    ledger_out_dir = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    checkpoint_path = ledger_out_dir / "checkpoints" / "5.json"
    header_path = ledger_out_dir / "headers" / "5.json"
    body_path = ledger_out_dir / "bodies" / "5.json"
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
    packet_path = tmp_path / "tau_packet.json"

    export = _run_export_tau_packet(
        "--checkpoint",
        str(checkpoint_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--profile",
        str(profile_path),
        "--tau-network-id",
        "tau-local",
        "--tau-adapter-ref",
        "idni/tau-testnet@c16992cd",
        "--out",
        str(packet_path),
    )

    assert export.returncode == 0, export.stderr
    export_report = json.loads(export.stdout)
    assert export_report["ok"] is True
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    checkpoint = json.loads(checkpoint_path.read_text(encoding="utf-8"))
    header = json.loads(header_path.read_text(encoding="utf-8"))
    body = json.loads(body_path.read_text(encoding="utf-8"))
    profile = json.loads(profile_path.read_text(encoding="utf-8"))

    assert packet["deployment_mode"] == "zeno_sovereign_testnet"
    assert packet["app_hash"] == checkpoint["app_hash"]
    assert packet["header_hash"] == checkpoint["header_hash"]
    assert packet["body_root"] == checkpoint["body_root"]
    assert packet["tau_admission"] == {
        "status": "handoff_only",
        "requires_tau_adapter_verification": True,
        "requires_tau_plugin_acceptance": True,
        "requires_tau_state_hash_assignment": True,
    }
    assert packet["tau_state_proof_hint"]["tau_state_hash_status"] == "unassigned"
    assert "state_hash_key" not in packet["tau_state_proof_hint"]
    validate_tau_export_packet_v0(
        packet=packet,
        checkpoint=checkpoint,
        header=header,
        body=body,
        profile=profile,
    )


def test_export_tau_packet_rejects_tampered_body(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr

    manifest_path, manifest = _load_manifest(report)
    ledger_out_dir = _manifest_relative_path(manifest_path, manifest["ledger_out_dir"])
    profile_path = _manifest_relative_path(manifest_path, manifest["profile_path"])
    body_path = ledger_out_dir / "bodies" / "5.json"
    bad_body_path = tmp_path / "bad_body.json"
    body = json.loads(body_path.read_text(encoding="utf-8"))
    body["transactions"] = []
    _write_json(bad_body_path, body)

    export = _run_export_tau_packet(
        "--checkpoint",
        str(ledger_out_dir / "checkpoints" / "5.json"),
        "--header",
        str(ledger_out_dir / "headers" / "5.json"),
        "--body",
        str(bad_body_path),
        "--profile",
        str(profile_path),
        "--tau-network-id",
        "tau-local",
        "--tau-adapter-ref",
        "idni/tau-testnet@c16992cd",
    )

    assert export.returncode == 1
    export_report = json.loads(export.stdout)
    assert export_report["ok"] is False
    assert any("mismatch" in error for error in export_report["errors"])


def test_signed_artifact_envelope_binds_watcher_attestation_and_mirror_index(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    attestation_path = _manifest_relative_path(manifest_path, manifest["attestation_path"])
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    attestation_envelope_path = tmp_path / "watcher_signature.json"
    mirror_envelope_path = tmp_path / "mirror_signature.json"

    watcher_sign = _run_sign_artifact(
        "--artifact",
        str(attestation_path),
        "--payload-kind",
        "watcher_attestation",
        "--signer-id",
        "bootstrap-watcher-0",
        "--key-id",
        "testnet-key-0",
        "--secret-hex",
        TEST_SIGNING_SECRET,
        "--out",
        str(attestation_envelope_path),
    )
    assert watcher_sign.returncode == 0, watcher_sign.stderr
    watcher_sign_report = json.loads(watcher_sign.stdout)
    assert watcher_sign_report["ok"] is True

    mirror_sign = _run_sign_artifact(
        "--artifact",
        str(mirror_index_path),
        "--payload-kind",
        "mirror_index",
        "--signer-id",
        "bootstrap-watcher-0",
        "--key-id",
        "testnet-key-0",
        "--secret-hex",
        TEST_SIGNING_SECRET,
        "--out",
        str(mirror_envelope_path),
    )
    assert mirror_sign.returncode == 0, mirror_sign.stderr
    mirror_sign_report = json.loads(mirror_sign.stdout)
    assert mirror_sign_report["ok"] is True

    watcher_verify = _run_verify_artifact_signature(
        "--artifact",
        str(attestation_path),
        "--envelope",
        str(attestation_envelope_path),
        "--payload-kind",
        "watcher_attestation",
        "--secret-hex",
        TEST_SIGNING_SECRET,
    )
    assert watcher_verify.returncode == 0, watcher_verify.stderr
    watcher_verify_report = json.loads(watcher_verify.stdout)
    assert watcher_verify_report["ok"] is True

    mirror_verify = _run_verify_artifact_signature(
        "--artifact",
        str(mirror_index_path),
        "--envelope",
        str(mirror_envelope_path),
        "--payload-kind",
        "mirror_index",
        "--secret-hex",
        TEST_SIGNING_SECRET,
    )
    assert mirror_verify.returncode == 0, mirror_verify.stderr
    mirror_verify_report = json.loads(mirror_verify.stdout)
    assert mirror_verify_report["ok"] is True

    attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    envelope = json.loads(attestation_envelope_path.read_text(encoding="utf-8"))
    validate_signed_artifact_envelope_v0(
        envelope=envelope,
        expected_payload_kind="watcher_attestation",
        expected_payload_hash=attestation["attestation_hash"],
        secret_hex=TEST_SIGNING_SECRET,
    )


def test_signed_artifact_envelope_binds_proof_verification_report(tmp_path: Path) -> None:
    report_path = tmp_path / "proof_verification_report.json"
    envelope_path = tmp_path / "proof_verification_report.sig.json"
    report = {
        "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
        "ok": True,
        "metadata_path": str(tmp_path / "proof_metadata" / "1.json"),
        "proof_journal_hash": _root("proof-journal"),
        "proof_kind": "risc0_zkvm_v0",
        "program_id": "risc0:zenodex-spot-transition-v1",
        "verifier_id": "risc0:receipt-verifier-v1",
        "toolchain_lock_hash": _root("toolchain"),
        "header_bound": True,
        "body_checked": True,
        "body_tx_execution_order_commitment_checked": False,
        "post_app_hash_checked": True,
        "post_state_root_checked": False,
        "pre_state_root_checked": False,
        "risc0_verified": True,
    }
    _write_json(report_path, report)

    sign = _run_sign_artifact(
        "--artifact",
        str(report_path),
        "--payload-kind",
        "proof_verification_report",
        "--signer-id",
        "proof-verifier-0",
        "--key-id",
        "testnet-key-0",
        "--secret-hex",
        TEST_SIGNING_SECRET,
        "--out",
        str(envelope_path),
    )
    assert sign.returncode == 0, sign.stderr

    verify = _run_verify_artifact_signature(
        "--artifact",
        str(report_path),
        "--envelope",
        str(envelope_path),
        "--payload-kind",
        "proof_verification_report",
        "--secret-hex",
        TEST_SIGNING_SECRET,
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["payload_kind"] == "proof_verification_report"

    tampered_path = tmp_path / "tampered_proof_verification_report.json"
    tampered = {**report, "post_app_hash_checked": False}
    _write_json(tampered_path, tampered)

    rejected = _run_verify_artifact_signature(
        "--artifact",
        str(tampered_path),
        "--envelope",
        str(envelope_path),
        "--payload-kind",
        "proof_verification_report",
        "--secret-hex",
        TEST_SIGNING_SECRET,
    )
    assert rejected.returncode == 1
    rejected_report = json.loads(rejected.stdout)
    assert any("binding mismatch" in error for error in rejected_report["errors"])


def test_signed_artifact_envelope_rejects_tampered_artifact_hash(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    attestation_path = _manifest_relative_path(manifest_path, manifest["attestation_path"])
    attestation_envelope_path = tmp_path / "watcher_signature.json"

    sign = _run_sign_artifact(
        "--artifact",
        str(attestation_path),
        "--payload-kind",
        "watcher_attestation",
        "--signer-id",
        "bootstrap-watcher-0",
        "--key-id",
        "testnet-key-0",
        "--secret-hex",
        TEST_SIGNING_SECRET,
        "--out",
        str(attestation_envelope_path),
    )
    assert sign.returncode == 0, sign.stderr

    bad_attestation_path = tmp_path / "bad_attestation.json"
    bad_attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
    bad_attestation["attestation_hash"] = _root("tampered-attestation-hash")
    _write_json(bad_attestation_path, bad_attestation)

    verify = _run_verify_artifact_signature(
        "--artifact",
        str(bad_attestation_path),
        "--envelope",
        str(attestation_envelope_path),
        "--payload-kind",
        "watcher_attestation",
        "--secret-hex",
        TEST_SIGNING_SECRET,
    )
    assert verify.returncode == 1
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is False
    assert any("binding mismatch" in error for error in verify_report["errors"])


def test_bls_release_artifact_envelope_uses_public_key_verification(tmp_path: Path) -> None:
    artifact_path = tmp_path / "mirror_index.json"
    envelope_path = tmp_path / "mirror_index.release.sig.json"
    artifact = {"mirror_index_hash": _root("release-mirror-index")}
    _write_json(artifact_path, artifact)

    sign = _run_sign_artifact(
        "--artifact",
        str(artifact_path),
        "--payload-kind",
        "mirror_index",
        "--signer-id",
        "release-watcher-0",
        "--key-id",
        "release-bls-key-0",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY,
        "--out",
        str(envelope_path),
    )
    assert sign.returncode == 0, sign.stderr
    sign_report = json.loads(sign.stdout)
    assert sign_report["ok"] is True
    assert sign_report["algorithm"] == "bls12-381-g2-basic-release-v0"
    public_key = sign_report["envelope"]["public_key"]

    verify = _run_verify_artifact_signature(
        "--artifact",
        str(artifact_path),
        "--envelope",
        str(envelope_path),
        "--payload-kind",
        "mirror_index",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--public-key-hex",
        public_key,
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["algorithm"] == "bls12-381-g2-basic-release-v0"

    wrong_public_key = "0x" + "11" * 48
    rejected = _run_verify_artifact_signature(
        "--artifact",
        str(artifact_path),
        "--envelope",
        str(envelope_path),
        "--payload-kind",
        "mirror_index",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--public-key-hex",
        wrong_public_key,
    )
    assert rejected.returncode == 1
    rejected_report = json.loads(rejected.stdout)
    assert rejected_report["ok"] is False
    assert any("public_key mismatch" in error for error in rejected_report["errors"])


def test_bls_signer_registry_enforces_signature_quorum(tmp_path: Path) -> None:
    artifact_path = tmp_path / "mirror_index.json"
    envelope_a_path = tmp_path / "mirror_index.a.sig.json"
    envelope_b_path = tmp_path / "mirror_index.b.sig.json"
    registry_path = tmp_path / "signer_registry.json"
    quorum_report_path = tmp_path / "quorum_report.json"
    artifact = {"mirror_index_hash": _root("quorum-mirror-index")}
    _write_json(artifact_path, artifact)

    sign_a = _run_sign_artifact(
        "--artifact",
        str(artifact_path),
        "--payload-kind",
        "mirror_index",
        "--signer-id",
        "release-watcher-a",
        "--key-id",
        "release-bls-key-a",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY,
        "--out",
        str(envelope_a_path),
    )
    assert sign_a.returncode == 0, sign_a.stderr
    public_key_a = json.loads(sign_a.stdout)["envelope"]["public_key"]

    sign_b = _run_sign_artifact(
        "--artifact",
        str(artifact_path),
        "--payload-kind",
        "mirror_index",
        "--signer-id",
        "release-watcher-b",
        "--key-id",
        "release-bls-key-b",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY_2,
        "--out",
        str(envelope_b_path),
    )
    assert sign_b.returncode == 0, sign_b.stderr
    public_key_b = json.loads(sign_b.stdout)["envelope"]["public_key"]

    make_registry = _run_make_signer_registry(
        "--registry-id",
        "release-watchers-v0",
        "--payload-kind",
        "mirror_index",
        "--threshold",
        "2",
        "--signer",
        f"release-watcher-a:release-bls-key-a:{public_key_a}:1",
        "--signer",
        f"release-watcher-b:release-bls-key-b:{public_key_b}:1",
        "--out",
        str(registry_path),
    )
    assert make_registry.returncode == 0, make_registry.stderr
    registry_report = json.loads(make_registry.stdout)
    assert registry_report["ok"] is True

    verify = _run_verify_signature_quorum(
        "--artifact",
        str(artifact_path),
        "--registry",
        str(registry_path),
        "--payload-kind",
        "mirror_index",
        "--envelope",
        str(envelope_a_path),
        "--envelope",
        str(envelope_b_path),
        "--out",
        str(quorum_report_path),
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["quorum_report"]["accepted_weight"] == 2
    assert Path(verify_report["quorum_report_path"]).is_file()

    insufficient = _run_verify_signature_quorum(
        "--artifact",
        str(artifact_path),
        "--registry",
        str(registry_path),
        "--payload-kind",
        "mirror_index",
        "--envelope",
        str(envelope_a_path),
    )
    assert insufficient.returncode == 1
    insufficient_report = json.loads(insufficient.stdout)
    assert insufficient_report["ok"] is False
    assert any("threshold not met" in error for error in insufficient_report["errors"])


def test_bls_signer_registry_accepts_proof_verification_report_quorum(tmp_path: Path) -> None:
    report_path = tmp_path / "proof_verification_report.json"
    envelope_a_path = tmp_path / "proof_verification_report.a.sig.json"
    envelope_b_path = tmp_path / "proof_verification_report.b.sig.json"
    registry_path = tmp_path / "proof_report_signer_registry.json"
    quorum_report_path = tmp_path / "proof_report_quorum_report.json"
    report = {
        "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
        "ok": True,
        "metadata_path": str(tmp_path / "proof_metadata" / "1.json"),
        "proof_journal_hash": _root("proof-journal-quorum"),
        "proof_kind": "risc0_zkvm_v0",
        "program_id": "risc0:zenodex-spot-transition-v1",
        "verifier_id": "risc0:receipt-verifier-v1",
        "toolchain_lock_hash": _root("toolchain-quorum"),
        "header_bound": True,
        "body_checked": True,
        "body_tx_execution_order_commitment_checked": False,
        "post_app_hash_checked": True,
        "post_state_root_checked": False,
        "pre_state_root_checked": False,
        "risc0_verified": True,
    }
    _write_json(report_path, report)

    sign_a = _run_sign_artifact(
        "--artifact",
        str(report_path),
        "--payload-kind",
        "proof_verification_report",
        "--signer-id",
        "proof-verifier-a",
        "--key-id",
        "release-bls-key-a",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY,
        "--out",
        str(envelope_a_path),
    )
    assert sign_a.returncode == 0, sign_a.stderr
    public_key_a = json.loads(sign_a.stdout)["envelope"]["public_key"]

    sign_b = _run_sign_artifact(
        "--artifact",
        str(report_path),
        "--payload-kind",
        "proof_verification_report",
        "--signer-id",
        "proof-verifier-b",
        "--key-id",
        "release-bls-key-b",
        "--algorithm",
        "bls12-381-g2-basic-release-v0",
        "--bls-private-key-hex",
        TEST_BLS_PRIVATE_KEY_2,
        "--out",
        str(envelope_b_path),
    )
    assert sign_b.returncode == 0, sign_b.stderr
    public_key_b = json.loads(sign_b.stdout)["envelope"]["public_key"]

    make_registry = _run_make_signer_registry(
        "--registry-id",
        "proof-report-verifiers-v0",
        "--payload-kind",
        "proof_verification_report",
        "--threshold",
        "2",
        "--signer",
        f"proof-verifier-a:release-bls-key-a:{public_key_a}:1",
        "--signer",
        f"proof-verifier-b:release-bls-key-b:{public_key_b}:1",
        "--out",
        str(registry_path),
    )
    assert make_registry.returncode == 0, make_registry.stderr

    verify = _run_verify_signature_quorum(
        "--artifact",
        str(report_path),
        "--registry",
        str(registry_path),
        "--payload-kind",
        "proof_verification_report",
        "--envelope",
        str(envelope_a_path),
        "--envelope",
        str(envelope_b_path),
        "--out",
        str(quorum_report_path),
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["quorum_report"]["accepted_weight"] == 2
    assert Path(verify_report["quorum_report_path"]).is_file()

    tampered_path = tmp_path / "tampered_proof_verification_report.json"
    _write_json(tampered_path, {**report, "body_checked": False})
    rejected = _run_verify_signature_quorum(
        "--artifact",
        str(tampered_path),
        "--registry",
        str(registry_path),
        "--payload-kind",
        "proof_verification_report",
        "--envelope",
        str(envelope_a_path),
        "--envelope",
        str(envelope_b_path),
    )
    assert rejected.returncode == 1
    rejected_report = json.loads(rejected.stdout)
    assert rejected_report["ok"] is False
    assert any("BLS signature invalid" in error or "binding mismatch" in error for error in rejected_report["errors"])


def test_publish_mirror_copies_indexed_artifacts_and_extra_signature(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    publish_dir = tmp_path / "published"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    signature_path = bundle_dir / "mirror_index.sig.json"
    sign = _run_sign_artifact(
        "--artifact",
        str(mirror_index_path),
        "--payload-kind",
        "mirror_index",
        "--signer-id",
        "bootstrap-watcher-0",
        "--key-id",
        "testnet-key-0",
        "--secret-hex",
        TEST_SIGNING_SECRET,
        "--out",
        str(signature_path),
    )
    assert sign.returncode == 0, sign.stderr

    publish = _run_publish_mirror(
        "--index",
        str(mirror_index_path),
        "--source-root",
        str(bundle_dir),
        "--publish-root",
        str(publish_dir),
        "--include-extra",
        str(signature_path),
    )

    assert publish.returncode == 0, publish.stderr
    publish_report = json.loads(publish.stdout)
    assert publish_report["ok"] is True
    receipt = publish_report["receipt"]
    assert receipt["mirror_index_hash"] == json.loads(mirror_index_path.read_text(encoding="utf-8"))["mirror_index_hash"]
    assert "mirror_index.sig.json" in receipt["copied_extra_paths"]
    assert (publish_dir / "manifest.json").is_file()
    assert (publish_dir / "mirror_index.json").is_file()
    assert (publish_dir / "mirror_index.sig.json").is_file()

    verify = _run_verify_mirror_index(
        "--index",
        str(publish_dir / "mirror_index.json"),
        "--mirror-root",
        str(publish_dir),
    )
    assert verify.returncode == 0, verify.stderr
    verify_report = json.loads(verify.stdout)
    assert verify_report["ok"] is True
    assert verify_report["mirror_index_hash"] == receipt["mirror_index_hash"]


def test_publish_mirror_rejects_publish_dir_inside_source_tree(tmp_path: Path) -> None:
    bundle_dir = tmp_path / "bundle"
    proc = _run_make_bundle("--out-dir", str(bundle_dir))
    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)

    runner = _run_manifest("--manifest", report["manifest_path"], "--cwd", str(ROOT))
    assert runner.returncode == 0, runner.stderr
    manifest_path, manifest = _load_manifest(report)
    mirror_index_path = _manifest_relative_path(manifest_path, manifest["mirror_index_path"])
    publish = _run_publish_mirror(
        "--index",
        str(mirror_index_path),
        "--source-root",
        str(bundle_dir),
        "--publish-root",
        str(bundle_dir / "published"),
    )

    assert publish.returncode == 1
    publish_report = json.loads(publish.stdout)
    assert publish_report["ok"] is False
    assert "publish_root must not be inside source_root" in publish_report["errors"][0]
