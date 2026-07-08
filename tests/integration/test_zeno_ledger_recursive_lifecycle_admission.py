from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    FORCED_INCLUSION_DECISION_SCHEMA_V0,
    FORCED_INCLUSION_REQUEST_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
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

ROOT = Path(__file__).resolve().parents[2]
VERIFY_SCRIPT = ROOT / "tools" / "zeno_ledger_verify.py"
ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _body(height: int) -> dict[str, object]:
    tx_hash = hash_v0("tx_fixture", {"height": height, "nonce": 1})
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
        "transactions": [{"sender": "alice", "nonce": 1}],
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


def _header(body: dict[str, object]) -> dict[str, object]:
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
        prev_header_hash=ZERO_ROOT,
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


def _hex32_no_prefix(value: object) -> str:
    raw = str(value)
    return raw[2:] if raw.startswith("0x") else raw


def _recursive_asset_delta_root(rows: list[dict[str, object]]) -> str:
    digest = hashlib.sha256()
    digest.update(b"zenodex.risc0.recursive.asset_delta_root.v1")
    digest.update(len(rows).to_bytes(4, "big"))
    for row in rows:
        asset_id = str(row["asset_id"])
        encoded_asset = asset_id.encode("utf-8")
        digest.update(len(encoded_asset).to_bytes(4, "big"))
        digest.update(encoded_asset)
        for field in (
            "debit_atoms",
            "credit_atoms",
            "authorized_mint_atoms",
            "authorized_burn_atoms",
        ):
            digest.update(int(row[field]).to_bytes(16, "big"))
        digest.update(bytes.fromhex(str(row["authority_root"])))
    return digest.hexdigest()


def _recursive_lifecycle_packet(
    *,
    header: dict[str, object],
    metadata: dict[str, object],
    rows: list[dict[str, object]],
    authority_root: str,
) -> dict[str, object]:
    aggregate_asset_delta_root = _recursive_asset_delta_root(rows)
    bound_roots = {
        "post_state_root": _hex32_no_prefix(header["post_state_root"]),
        "tx_root": _hex32_no_prefix(header["tx_root"]),
        "evidence_root": _hex32_no_prefix(header["evidence_root"]),
        "receipt_root": _hex32_no_prefix(_root("recursive-receipt-root")),
        "aggregate_asset_delta_root": aggregate_asset_delta_root,
        "data_availability_root": _hex32_no_prefix(header["data_availability_root"]),
        "public_policy_hash": _hex32_no_prefix(_root("recursive-public-policy")),
        "feature_suite_hash": _hex32_no_prefix(metadata["feature_suite_hash"]),
    }
    transcript_binding_hash = _hex32_no_prefix(_root("recursive-transcript-binding"))
    return {
        "schema": "zenodex.recursive_lifecycle_admission_packet.v1",
        "proof_requested": True,
        "proof_verified": True,
        "proof_type": "risc0.zenodex_recursive_epoch.v1",
        "proof_profile": "recursive_epoch_v1",
        "unsupported_lifecycle_absent": True,
        "transcript_binding_hash": transcript_binding_hash,
        "expected_transcript_binding_hash": transcript_binding_hash,
        "allowed_authority_roots": [authority_root],
        "asset_delta_rows": rows,
        "proof_meta": {"child_count": 2, **bound_roots},
        "header": bound_roots,
    }


def _recursive_proof_report(
    *,
    header: dict[str, object],
    metadata: dict[str, object],
    packet: dict[str, object],
) -> dict[str, object]:
    proof_meta = packet["proof_meta"]
    assert isinstance(proof_meta, dict)
    return {
        "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
        "ok": True,
        "metadata_path": "proof_metadata/1.json",
        "proof_journal_hash": header["proof_journal_hash"],
        "proof_kind": metadata["proof_kind"],
        "program_id": metadata["program_id"],
        "verifier_id": metadata["verifier_id"],
        "toolchain_lock_hash": metadata["toolchain_lock_hash"],
        "header_bound": True,
        "body_checked": True,
        "body_tx_execution_order_commitment_checked": False,
        "post_app_hash_checked": False,
        "post_state_root_checked": True,
        "pre_state_root_checked": True,
        "risc0_verified": True,
        "proof_type": "risc0.zenodex_recursive_epoch.v1",
        "proof_profile": "recursive_epoch_v1",
        "chain_id": metadata["chain_id"],
        "epoch_id": 1,
        "child_count": proof_meta["child_count"],
        "pre_state_root": _hex32_no_prefix(metadata["pre_state_root"]),
        "post_state_root": proof_meta["post_state_root"],
        "tx_root": proof_meta["tx_root"],
        "evidence_root": proof_meta["evidence_root"],
        "receipt_root": proof_meta["receipt_root"],
        "statement_hash": _hex32_no_prefix(_root("recursive-statement")),
        "verifier_set_root": _hex32_no_prefix(_root("recursive-verifier-set")),
        "allowed_authority_roots_root": _hex32_no_prefix(_root("recursive-authority-set")),
        "child_verification_claims_root": _hex32_no_prefix(_root("recursive-child-claims")),
        "child_journals_root": _hex32_no_prefix(_root("recursive-child-journals")),
        "child_effect_summaries_root": _hex32_no_prefix(_root("recursive-child-summaries")),
        "accepted_receipts_root": _hex32_no_prefix(_root("recursive-accepted-receipts")),
        "rejected_receipts_root": _hex32_no_prefix(_root("recursive-rejected-receipts")),
        "aggregate_asset_delta_root": proof_meta["aggregate_asset_delta_root"],
        "cross_shard_outbox_root": _hex32_no_prefix(_root("recursive-outbox")),
        "cross_shard_inbox_root": _hex32_no_prefix(_root("recursive-inbox")),
        "carry_queue_pre_root": _hex32_no_prefix(_root("recursive-carry")),
        "carry_queue_post_root": _hex32_no_prefix(_root("recursive-carry")),
        "conflict_schedule_hash": _hex32_no_prefix(metadata["conflict_schedule_hash"]),
        "data_availability_root": proof_meta["data_availability_root"],
        "public_policy_hash": proof_meta["public_policy_hash"],
        "feature_suite_hash": proof_meta["feature_suite_hash"],
        "dependency_lock_hash": _hex32_no_prefix(metadata["dependency_lock_hash"]),
    }


def _write_recursive_lifecycle_fixture(
    tmp_path: Path,
) -> tuple[Path, Path, Path, Path, Path, dict[str, object], dict[str, object], dict[str, object]]:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    proof_metadata_dir = tmp_path / "proof_metadata"
    proof_report_dir = tmp_path / "proof_verification_reports"
    recursive_admission_dir = tmp_path / "recursive_lifecycle_admission"
    headers_dir.mkdir()
    bodies_dir.mkdir()
    proof_metadata_dir.mkdir()
    proof_report_dir.mkdir()
    recursive_admission_dir.mkdir()

    body = _body(1)
    header = _header(body)
    metadata = build_proof_metadata_v0(
        chain_id=str(header["chain_id"]),
        height=int(header["height"]),
        proof_kind="recursive_epoch_v0",
        program_id="risc0:zenodex-recursive-epoch-v1",
        verifier_id="risc0:recursive-receipt-verifier-v1",
        proof_commitment=_root("recursive-proof-commitment"),
        public_input_hash=_root("recursive-public-input"),
        journal_hash=_root("recursive-journal"),
        pre_state_root=str(header["pre_state_root"]),
        post_state_root=str(header["post_state_root"]),
        tx_root=str(header["tx_root"]),
        evidence_root=str(header["evidence_root"]),
        body_root=str(header["body_root"]),
        conflict_schedule_hash=_root("recursive-conflict-schedule"),
        feature_suite_hash=_root("recursive-feature-suite"),
        dependency_lock_hash=_root("recursive-dependency-lock"),
        toolchain_lock_hash=_root("recursive-toolchain-lock"),
        child_receipts_root=_root("recursive-child-receipts"),
    )
    header["proof_journal_hash"] = proof_metadata_hash_v0(metadata)
    authority_root = _hex32_no_prefix(_root("zusd-authority-root"))
    rows = [
        {
            "asset_id": "USDC",
            "debit_atoms": 100,
            "credit_atoms": 100,
            "authorized_mint_atoms": 0,
            "authorized_burn_atoms": 0,
            "authority_root": "0" * 64,
        },
        {
            "asset_id": "zUSD",
            "debit_atoms": 0,
            "credit_atoms": 25,
            "authorized_mint_atoms": 25,
            "authorized_burn_atoms": 0,
            "authority_root": authority_root,
        },
    ]
    packet = _recursive_lifecycle_packet(
        header=header,
        metadata=metadata,
        rows=rows,
        authority_root=authority_root,
    )

    _write_json(headers_dir / "1.json", header)
    _write_json(bodies_dir / "1.json", body)
    _write_json(proof_metadata_dir / "1.json", metadata)
    _write_json(recursive_admission_dir / "1.json", packet)
    _write_json(
        proof_report_dir / "1.json",
        _recursive_proof_report(header=header, metadata=metadata, packet=packet),
    )
    return headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, header, metadata, packet


def _run_verify(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(VERIFY_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _base_verify_args(
    headers_dir: Path,
    bodies_dir: Path,
    proof_metadata_dir: Path,
    proof_report_dir: Path | None = None,
) -> list[str]:
    args = [
        "--headers-dir",
        str(headers_dir),
        "--bodies-dir",
        str(bodies_dir),
        "--proof-metadata-dir",
        str(proof_metadata_dir),
        "--from-height",
        "1",
        "--to-height",
        "1",
    ]
    if proof_report_dir is not None:
        args.extend(["--proof-verification-report-dir", str(proof_report_dir)])
    return [
        *args,
    ]


def test_recursive_lifecycle_admission_accepts_valid_packet(tmp_path: Path) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, _, _, _ = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["checked_heights"] == [1]
    assert payload["proof_metadata_checked_heights"] == [1]
    assert payload["proof_verification_checked_heights"] == [1]
    assert payload["recursive_lifecycle_admission_checked_heights"] == [1]


def test_recursive_lifecycle_admission_rejects_packet_without_proof_report(tmp_path: Path) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, _, recursive_admission_dir, _, _, _ = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert payload["recursive_lifecycle_admission_checked_heights"] == []
    assert "recursive proof verification report required" in payload["errors"][0]


def test_recursive_lifecycle_admission_packet_required_for_recursive_metadata(tmp_path: Path) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, _, _, _, _ = _write_recursive_lifecycle_fixture(
        tmp_path
    )

    proc = _run_verify(*_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir))

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert payload.get("app_hashes_by_height", []) == []
    assert payload["last_header_hash"] is None
    assert payload["last_app_hash"] is None
    assert payload["recursive_lifecycle_admission_checked_heights"] == []
    assert "recursive lifecycle admission packet dir required" in payload["errors"][0]


def test_recursive_lifecycle_admission_rejects_malformed_packet_without_accepting_height(
    tmp_path: Path,
) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, _, _, packet = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )
    rows_obj = packet["asset_delta_rows"]
    assert isinstance(rows_obj, list)
    rows = [dict(row) for row in rows_obj]
    rows[1]["authorized_mint_atoms"] = 24
    malformed = {**packet, "asset_delta_rows": rows}
    _write_json(recursive_admission_dir / "1.json", malformed)

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert payload.get("app_hashes_by_height", []) == []
    assert payload["last_header_hash"] is None
    assert payload["last_app_hash"] is None
    assert payload["recursive_lifecycle_admission_checked_heights"] == []
    assert "recursive lifecycle admission rejected" in payload["errors"][0]
    assert "aggregate row unbalanced: zUSD" in payload["errors"][0]


def test_recursive_lifecycle_admission_rejects_stale_packet_without_accepting_height(
    tmp_path: Path,
) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, _, _, packet = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )
    header_obj = packet["header"]
    proof_meta_obj = packet["proof_meta"]
    assert isinstance(header_obj, dict)
    assert isinstance(proof_meta_obj, dict)
    stale_root = _hex32_no_prefix(_root("stale-recursive-post-state"))
    stale = {
        **packet,
        "header": {**header_obj, "post_state_root": stale_root},
        "proof_meta": {**proof_meta_obj, "post_state_root": stale_root},
    }
    _write_json(recursive_admission_dir / "1.json", stale)

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert payload.get("app_hashes_by_height", []) == []
    assert payload["last_header_hash"] is None
    assert payload["last_app_hash"] is None
    assert payload["recursive_lifecycle_admission_checked_heights"] == []
    assert "recursive lifecycle admission/header post_state_root mismatch" in payload["errors"][0]


def test_recursive_lifecycle_admission_rejects_unverified_recursive_report(tmp_path: Path) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, _, _, _ = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )
    report = json.loads((proof_report_dir / "1.json").read_text(encoding="utf-8"))
    report["risc0_verified"] = False
    _write_json(proof_report_dir / "1.json", report)

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert "recursive proof verification report must be verifier-backed" in payload["errors"][0]


def test_recursive_lifecycle_admission_rejects_wrong_recursive_report_profile(tmp_path: Path) -> None:
    headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir, recursive_admission_dir, _, _, _ = (
        _write_recursive_lifecycle_fixture(tmp_path)
    )
    report = json.loads((proof_report_dir / "1.json").read_text(encoding="utf-8"))
    report["proof_profile"] = "recursive_block_v1"
    _write_json(proof_report_dir / "1.json", report)

    proc = _run_verify(
        *_base_verify_args(headers_dir, bodies_dir, proof_metadata_dir, proof_report_dir),
        "--recursive-lifecycle-admission-dir",
        str(recursive_admission_dir),
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stdout)
    assert payload["ok"] is False
    assert payload["checked_heights"] == []
    assert "recursive proof verification report proof_profile mismatch" in payload["errors"][0]
