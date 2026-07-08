from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.frontier_signature_root import FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1
from src.core.risc0_tx_execution_order import (
    build_tx_execution_order_certificate_v1,
    tx_execution_order_commitment_hex_v1,
)
from src.integration.proof_toolchain_lock import proof_toolchain_lock_hash_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    FORCED_INCLUSION_DECISION_SCHEMA_V0,
    FORCED_INCLUSION_REQUEST_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    ZERO_ROOT_V0,
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
    validate_proof_metadata_header_binding_v0,
)

ROOT = Path(__file__).resolve().parents[2]
ADAPTER_SCRIPT = ROOT / "tools" / "zeno_ledger_risc0_proof_metadata.py"
TX_ORDER_ABI_CORPUS_PATH = ROOT / "tests" / "fixtures" / "risc0_tx_execution_order_abi_v1.json"
ORDER_COMMITMENT_RECEIPT_SCHEMA = "zenodex/zeno_ledger/risc0_tx_execution_order_commitment/v0"


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _hex(label: str) -> str:
    return _root(label)[2:]


def _tx_order_abi_positive_cases() -> list[dict[str, object]]:
    corpus = json.loads(TX_ORDER_ABI_CORPUS_PATH.read_text(encoding="utf-8"))
    positive_cases = corpus["positive_cases"]
    assert isinstance(positive_cases, list)
    return positive_cases


def _body(height: int) -> dict[str, object]:
    tx_hash = hash_v0("tx_fixture", {"height": height})
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
        "transactions": [{"sender": "alice", "nonce": height}],
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


def _body_with_order_commitment(
    height: int,
    *,
    tx_execution_order_commitment: str,
    proof_type: str = "risc0.zenodex_spot_transition.v1",
) -> dict[str, object]:
    body = _body(height)
    evidence = dict(body["evidence"])  # type: ignore[arg-type]
    proof_receipts = list(evidence["proof_receipts"])  # type: ignore[index]
    proof_receipts.append(
        {
            "schema": ORDER_COMMITMENT_RECEIPT_SCHEMA,
            "proof_type": proof_type,
            "tx_execution_order_commitment": tx_execution_order_commitment,
        }
    )
    evidence["proof_receipts"] = proof_receipts
    body["evidence"] = evidence
    return body


def _header(
    body: dict[str, object],
    *,
    proof_journal_hash: str = ZERO_ROOT_V0,
    pre_state_root: str | None = None,
    post_state_root: str | None = None,
) -> dict[str, object]:
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    resolved_pre_state_root = _root("pre-state") if pre_state_root is None else pre_state_root
    resolved_post_state_root = _root("post-state") if post_state_root is None else post_state_root
    config_digest = _root("config")
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": resolved_post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000 + int(body["height"]),
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=resolved_pre_state_root,
        post_state_root=resolved_post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _proof(
    *,
    post_app_hash: str,
    proof_type: str = "risc0.zenodex_spot_transition.v1",
    tx_execution_order_commitment: str | None = None,
    frontier_count: int | None = None,
    frontier_root: str | None = None,
) -> dict[str, object]:
    meta: dict[str, object] = {
        "risc0_image_id": _hex("risc0-image-id"),
        "txs_commitment": _hex("txs-commitment"),
        "tx_execution_order_commitment": tx_execution_order_commitment
        or tx_execution_order_commitment_hex_v1([0]),
        "ingress_commitment": _hex("ingress-commitment"),
        "pre_nonce_root": _hex("pre-nonce-root"),
        "post_nonce_root": _hex("post-nonce-root"),
        "accepted_receipts_root": _hex("accepted-receipts-root"),
        "pre_app_hash": "",
        "post_app_hash": post_app_hash,
        "protocol_fee_share_bps": 0,
        "protocol_fee_recipient_pubkey": None,
    }
    if frontier_count is not None:
        meta["shared_pool_frontier_signature_certificate_count"] = frontier_count
    if frontier_root is not None:
        meta["shared_pool_frontier_signature_certificates_root"] = frontier_root
    return {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": _hex("tau-state-hash"),
        "proof_type": proof_type,
        "proof": "cmlzYzAtcmVjZWlwdA==",
        "meta": meta,
    }


def _proof_with_pre_app_hash(
    *,
    post_app_hash: str,
    pre_app_hash: str,
) -> dict[str, object]:
    proof = _proof(post_app_hash=post_app_hash)
    meta = dict(proof["meta"])  # type: ignore[arg-type]
    meta["pre_app_hash"] = pre_app_hash
    proof["meta"] = meta
    return proof


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _run_adapter(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ADAPTER_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _verifier_script(path: Path, *, ok: bool) -> Path:
    body = f"""#!/usr/bin/env python3
import json
import sys

req = json.load(sys.stdin)
if req.get("schema") != "tau_state_proof_verify":
    print(json.dumps({{"ok": False, "error": "bad schema"}}))
    raise SystemExit(0)
if req.get("schema_version") != 1:
    print(json.dumps({{"ok": False, "error": "bad schema_version"}}))
    raise SystemExit(0)
if req.get("state_hash") != req.get("proof", {{}}).get("state_hash"):
    print(json.dumps({{"ok": False, "error": "state hash mismatch"}}))
    raise SystemExit(0)
if "tau_state" not in req or "context" not in req:
    print(json.dumps({{"ok": False, "error": "missing context"}}))
    raise SystemExit(0)
print(json.dumps({{"ok": {str(ok)}}}))
"""
    path.write_text(body, encoding="utf-8")
    path.chmod(0o755)
    return path


def test_risc0_adapter_builds_metadata_and_validates_bound_header(tmp_path: Path) -> None:
    body = _body(1)
    header_unbound = _header(body)
    proof = _proof(post_app_hash=str(header_unbound["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_unbound_path = tmp_path / "header_unbound.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "proof_metadata.json"
    _write_json(body_path, body)
    _write_json(header_unbound_path, header_unbound)
    _write_json(proof_path, proof)

    first = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_unbound_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
    )
    assert first.returncode == 0, first.stderr or first.stdout
    first_report = json.loads(first.stdout)
    assert first_report["ok"] is True
    assert first_report["header_bound"] is False
    assert first_report["body_checked"] is True
    assert first_report["toolchain_lock_hash"] == _root("toolchain-lock")
    assert metadata_path.is_file()

    bound_header = _header(body, proof_journal_hash=str(first_report["proof_journal_hash"]))
    bound_header_path = tmp_path / "header_bound.json"
    bound_metadata_path = tmp_path / "proof_metadata_bound.json"
    _write_json(bound_header_path, bound_header)

    second = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(bound_header_path),
        "--body",
        str(body_path),
        "--out",
        str(bound_metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-bound-header",
        "--require-post-app-hash-header-app-hash",
    )
    assert second.returncode == 0, second.stderr or second.stdout
    second_report = json.loads(second.stdout)
    assert second_report["header_bound"] is True

    metadata = json.loads(bound_metadata_path.read_text(encoding="utf-8"))
    assert metadata["toolchain_lock_hash"] == _root("toolchain-lock")
    validate_proof_metadata_header_binding_v0(metadata, bound_header)


def test_risc0_adapter_rejects_wrong_proof_type_and_app_hash_mismatch(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    wrong_type_path = tmp_path / "wrong_type_proof.json"
    wrong_app_hash_path = tmp_path / "wrong_app_hash_proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(
        wrong_type_path,
        _proof(post_app_hash=str(header["app_hash"])[2:], proof_type="risc0.other_transition.v1"),
    )
    _write_json(wrong_app_hash_path, _proof(post_app_hash=_hex("wrong-post-app-hash")))

    wrong_type = _run_adapter("--proof", str(wrong_type_path), "--header", str(header_path), "--body", str(body_path))
    assert wrong_type.returncode == 1
    assert "unsupported risc0 proof_type" in wrong_type.stdout

    wrong_app_hash = _run_adapter(
        "--proof",
        str(wrong_app_hash_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--require-post-app-hash-header-app-hash",
    )
    assert wrong_app_hash.returncode == 1
    assert "post_app_hash/header app_hash mismatch" in wrong_app_hash.stdout


def test_risc0_adapter_rejects_default_placeholder_metadata_roots(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
    )
    assert proc.returncode == 1
    assert "proof_metadata.conflict_schedule_hash must be non-zero" in proc.stdout


def test_risc0_adapter_defaults_to_repo_toolchain_lock_hash(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "metadata.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--require-post-app-hash-header-app-hash",
    )

    assert proc.returncode == 0, proc.stderr or proc.stdout
    report = json.loads(proc.stdout)
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    expected = proof_toolchain_lock_hash_v0(ROOT)
    assert report["toolchain_lock_hash"] == expected
    assert metadata["toolchain_lock_hash"] == expected


def test_risc0_adapter_binds_pre_app_hash_presence_bit(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    no_pre_path = tmp_path / "proof_no_pre.json"
    with_pre_path = tmp_path / "proof_with_pre.json"
    no_pre_metadata_path = tmp_path / "metadata_no_pre.json"
    with_pre_metadata_path = tmp_path / "metadata_with_pre.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(no_pre_path, _proof(post_app_hash=str(header["app_hash"])[2:]))
    _write_json(
        with_pre_path,
        _proof_with_pre_app_hash(
            post_app_hash=str(header["app_hash"])[2:],
            pre_app_hash=_hex("pre-app-hash"),
        ),
    )

    common_args = (
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
    )
    no_pre = _run_adapter("--proof", str(no_pre_path), "--out", str(no_pre_metadata_path), *common_args)
    with_pre = _run_adapter("--proof", str(with_pre_path), "--out", str(with_pre_metadata_path), *common_args)
    assert no_pre.returncode == 0, no_pre.stderr or no_pre.stdout
    assert with_pre.returncode == 0, with_pre.stderr or with_pre.stdout

    metadata_no_pre = json.loads(no_pre_metadata_path.read_text(encoding="utf-8"))
    metadata_with_pre = json.loads(with_pre_metadata_path.read_text(encoding="utf-8"))
    assert metadata_no_pre["public_input_hash"] != metadata_with_pre["public_input_hash"]
    assert metadata_no_pre["journal_hash"] != metadata_with_pre["journal_hash"]


def test_risc0_adapter_binds_order_and_protocol_fee_meta(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    base_proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    order_proof = json.loads(json.dumps(base_proof))
    order_proof["meta"]["tx_execution_order_commitment"] = _hex("different-tx-order")
    fee_proof = json.loads(json.dumps(base_proof))
    fee_proof["meta"]["protocol_fee_share_bps"] = 2500
    fee_proof["meta"]["protocol_fee_recipient_pubkey"] = "0xfee-recipient"

    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    base_path = tmp_path / "proof_base.json"
    order_path = tmp_path / "proof_order.json"
    fee_path = tmp_path / "proof_fee.json"
    base_metadata_path = tmp_path / "metadata_base.json"
    order_metadata_path = tmp_path / "metadata_order.json"
    fee_metadata_path = tmp_path / "metadata_fee.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(base_path, base_proof)
    _write_json(order_path, order_proof)
    _write_json(fee_path, fee_proof)

    common_args = (
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
    )
    base = _run_adapter("--proof", str(base_path), "--out", str(base_metadata_path), *common_args)
    order = _run_adapter("--proof", str(order_path), "--out", str(order_metadata_path), *common_args)
    fee = _run_adapter("--proof", str(fee_path), "--out", str(fee_metadata_path), *common_args)
    assert base.returncode == 0, base.stderr or base.stdout
    assert order.returncode == 0, order.stderr or order.stdout
    assert fee.returncode == 0, fee.stderr or fee.stdout

    base_metadata = json.loads(base_metadata_path.read_text(encoding="utf-8"))
    order_metadata = json.loads(order_metadata_path.read_text(encoding="utf-8"))
    fee_metadata = json.loads(fee_metadata_path.read_text(encoding="utf-8"))
    assert base_metadata["public_input_hash"] != order_metadata["public_input_hash"]
    assert base_metadata["journal_hash"] != order_metadata["journal_hash"]
    assert base_metadata["public_input_hash"] != fee_metadata["public_input_hash"]
    assert base_metadata["journal_hash"] != fee_metadata["journal_hash"]


def test_risc0_adapter_binds_frontier_signature_meta(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    base_proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    frontier_a = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        frontier_count=1,
        frontier_root="0x" + "aa" * 32,
    )
    frontier_b = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        frontier_count=1,
        frontier_root="0x" + "bb" * 32,
    )

    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    base_path = tmp_path / "proof_base.json"
    frontier_a_path = tmp_path / "proof_frontier_a.json"
    frontier_b_path = tmp_path / "proof_frontier_b.json"
    base_metadata_path = tmp_path / "metadata_base.json"
    frontier_a_metadata_path = tmp_path / "metadata_frontier_a.json"
    frontier_b_metadata_path = tmp_path / "metadata_frontier_b.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(base_path, base_proof)
    _write_json(frontier_a_path, frontier_a)
    _write_json(frontier_b_path, frontier_b)

    common_args = (
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
    )
    base = _run_adapter("--proof", str(base_path), "--out", str(base_metadata_path), *common_args)
    a = _run_adapter("--proof", str(frontier_a_path), "--out", str(frontier_a_metadata_path), *common_args)
    b = _run_adapter("--proof", str(frontier_b_path), "--out", str(frontier_b_metadata_path), *common_args)
    assert base.returncode == 0, base.stderr or base.stdout
    assert a.returncode == 0, a.stderr or a.stdout
    assert b.returncode == 0, b.stderr or b.stdout

    base_metadata = json.loads(base_metadata_path.read_text(encoding="utf-8"))
    a_metadata = json.loads(frontier_a_metadata_path.read_text(encoding="utf-8"))
    b_metadata = json.loads(frontier_b_metadata_path.read_text(encoding="utf-8"))

    assert base_metadata["public_input_hash"] != a_metadata["public_input_hash"]
    assert a_metadata["public_input_hash"] != b_metadata["public_input_hash"]
    assert base_metadata["journal_hash"] != a_metadata["journal_hash"]
    assert a_metadata["journal_hash"] != b_metadata["journal_hash"]
    assert proof_metadata_hash_v0(a_metadata) != proof_metadata_hash_v0(b_metadata)
    a_bound_header = _header(body, proof_journal_hash=proof_metadata_hash_v0(a_metadata))
    with pytest.raises(ValueError, match="proof_journal_hash mismatch"):
        validate_proof_metadata_header_binding_v0(b_metadata, a_bound_header)

    proof_meta = frontier_a["meta"]
    assert isinstance(proof_meta, dict)
    expected_public_input = {
        "proof_type": frontier_a["proof_type"],
        "state_hash": frontier_a["state_hash"],
        "txs_commitment": proof_meta["txs_commitment"],
        "tx_execution_order_commitment": proof_meta["tx_execution_order_commitment"],
        "ingress_commitment": proof_meta["ingress_commitment"],
        "pre_nonce_root": proof_meta["pre_nonce_root"],
        "post_nonce_root": proof_meta["post_nonce_root"],
        "accepted_receipts_root": proof_meta["accepted_receipts_root"],
        "pre_app_hash_present": False,
        "pre_app_hash": "",
        "post_app_hash": proof_meta["post_app_hash"],
        "protocol_fee_share_bps": 0,
        "protocol_fee_recipient_pubkey": None,
        "shared_pool_frontier_signature_certificate_count": 1,
        "shared_pool_frontier_signature_certificates_root": "aa" * 32,
    }
    assert a_metadata["public_input_hash"] == hash_v0(
        "risc0_tau_state_proof_public_input_v0",
        expected_public_input,
    )


def test_risc0_adapter_consumes_python_order_certificate(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    certificate = build_tx_execution_order_certificate_v1([1, 0], tx_count=2)
    proof = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        tx_execution_order_commitment=certificate.tx_execution_order_commitment,
    )
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "metadata.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
    )

    assert proc.returncode == 0, proc.stderr or proc.stdout
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    proof_meta = proof["meta"]
    assert isinstance(proof_meta, dict)
    expected_public_input = {
        "proof_type": proof["proof_type"],
        "state_hash": proof["state_hash"],
        "txs_commitment": proof_meta["txs_commitment"],
        "tx_execution_order_commitment": certificate.tx_execution_order_commitment,
        "ingress_commitment": proof_meta["ingress_commitment"],
        "pre_nonce_root": proof_meta["pre_nonce_root"],
        "post_nonce_root": proof_meta["post_nonce_root"],
        "accepted_receipts_root": proof_meta["accepted_receipts_root"],
        "pre_app_hash_present": False,
        "pre_app_hash": "",
        "post_app_hash": proof_meta["post_app_hash"],
        "protocol_fee_share_bps": 0,
        "protocol_fee_recipient_pubkey": None,
        "shared_pool_frontier_signature_certificate_count": 0,
        "shared_pool_frontier_signature_certificates_root": (
            FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1[2:]
        ),
    }
    assert metadata["public_input_hash"] == hash_v0(
        "risc0_tau_state_proof_public_input_v0",
        expected_public_input,
    )


def test_risc0_adapter_binds_body_order_commitment_receipt(tmp_path: Path) -> None:
    certificate = build_tx_execution_order_certificate_v1([1, 0], tx_count=2)
    body = _body_with_order_commitment(
        1,
        tx_execution_order_commitment=certificate.tx_execution_order_commitment,
    )
    header = _header(body)
    proof = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        tx_execution_order_commitment=certificate.tx_execution_order_commitment,
    )
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "metadata.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-body-tx-execution-order-commitment",
        "--require-post-app-hash-header-app-hash",
    )

    assert proc.returncode == 0, proc.stderr or proc.stdout
    report = json.loads(proc.stdout)
    assert report["body_checked"] is True
    assert report["body_tx_execution_order_commitment_checked"] is True


def test_risc0_adapter_accepts_body_order_commitment_abi_corpus(tmp_path: Path) -> None:
    for index, case in enumerate(_tx_order_abi_positive_cases()):
        commitment = case["commitment"]
        assert isinstance(commitment, str)
        body = _body_with_order_commitment(
            20 + index,
            tx_execution_order_commitment=commitment,
        )
        header = _header(body)
        proof = _proof(
            post_app_hash=str(header["app_hash"])[2:],
            tx_execution_order_commitment=commitment,
        )
        body_path = tmp_path / f"body_{index}.json"
        header_path = tmp_path / f"header_{index}.json"
        proof_path = tmp_path / f"proof_{index}.json"
        metadata_path = tmp_path / f"metadata_{index}.json"
        _write_json(body_path, body)
        _write_json(header_path, header)
        _write_json(proof_path, proof)

        proc = _run_adapter(
            "--proof",
            str(proof_path),
            "--header",
            str(header_path),
            "--body",
            str(body_path),
            "--out",
            str(metadata_path),
            "--conflict-schedule-hash",
            _root("schedule"),
            "--feature-suite-hash",
            _root("feature-suite"),
            "--dependency-lock-hash",
            _root("dependency-lock"),
            "--toolchain-lock-hash",
            _root("toolchain-lock"),
            "--require-body-tx-execution-order-commitment",
            "--require-post-app-hash-header-app-hash",
        )

        assert proc.returncode == 0, proc.stderr or proc.stdout
        report = json.loads(proc.stdout)
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        proof_meta = proof["meta"]
        assert isinstance(proof_meta, dict)
        expected_public_input = {
            "proof_type": proof["proof_type"],
            "state_hash": proof["state_hash"],
            "txs_commitment": proof_meta["txs_commitment"],
            "tx_execution_order_commitment": commitment,
            "ingress_commitment": proof_meta["ingress_commitment"],
            "pre_nonce_root": proof_meta["pre_nonce_root"],
            "post_nonce_root": proof_meta["post_nonce_root"],
            "accepted_receipts_root": proof_meta["accepted_receipts_root"],
            "pre_app_hash_present": False,
            "pre_app_hash": "",
            "post_app_hash": proof_meta["post_app_hash"],
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": None,
            "shared_pool_frontier_signature_certificate_count": 0,
            "shared_pool_frontier_signature_certificates_root": (
                FRONTIER_SIGNATURE_CERTIFICATES_EMPTY_ROOT_V1[2:]
            ),
        }
        assert report["body_tx_execution_order_commitment_checked"] is True
        assert metadata["public_input_hash"] == hash_v0(
            "risc0_tau_state_proof_public_input_v0",
            expected_public_input,
        )


def test_risc0_adapter_rejects_body_order_commitment_mismatch(tmp_path: Path) -> None:
    body_certificate = build_tx_execution_order_certificate_v1([1, 0], tx_count=2)
    proof_certificate = build_tx_execution_order_certificate_v1([0, 1], tx_count=2)
    body = _body_with_order_commitment(
        1,
        tx_execution_order_commitment=body_certificate.tx_execution_order_commitment,
    )
    header = _header(body)
    proof = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        tx_execution_order_commitment=proof_certificate.tx_execution_order_commitment,
    )
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter("--proof", str(proof_path), "--header", str(header_path), "--body", str(body_path))

    assert proc.returncode == 1
    assert "body tx_execution_order_commitment/proof meta mismatch" in proc.stdout


def test_risc0_adapter_rejects_required_body_order_commitment_when_missing(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--require-body-tx-execution-order-commitment",
    )

    assert proc.returncode == 1
    assert "body tx_execution_order_commitment receipt missing" in proc.stdout


def test_risc0_adapter_rejects_malformed_current_meta_fields(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    _write_json(body_path, body)
    _write_json(header_path, header)

    missing_order = _proof(post_app_hash=str(header["app_hash"])[2:])
    del missing_order["meta"]["tx_execution_order_commitment"]
    missing_order_path = tmp_path / "missing_order.json"
    _write_json(missing_order_path, missing_order)

    oversized_fee = _proof(post_app_hash=str(header["app_hash"])[2:])
    oversized_fee["meta"]["protocol_fee_share_bps"] = 10001
    oversized_fee_path = tmp_path / "oversized_fee.json"
    _write_json(oversized_fee_path, oversized_fee)

    missing_recipient = _proof(post_app_hash=str(header["app_hash"])[2:])
    missing_recipient["meta"]["protocol_fee_share_bps"] = 1
    missing_recipient_path = tmp_path / "missing_recipient.json"
    _write_json(missing_recipient_path, missing_recipient)
    partial_frontier = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        frontier_count=1,
    )
    partial_frontier_path = tmp_path / "partial_frontier.json"
    _write_json(partial_frontier_path, partial_frontier)
    zero_count_nonempty_root = _proof(
        post_app_hash=str(header["app_hash"])[2:],
        frontier_count=0,
        frontier_root="0x" + "aa" * 32,
    )
    zero_count_nonempty_root_path = tmp_path / "zero_count_nonempty_root.json"
    _write_json(zero_count_nonempty_root_path, zero_count_nonempty_root)

    common_args = ("--header", str(header_path), "--body", str(body_path))
    missing_order_proc = _run_adapter("--proof", str(missing_order_path), *common_args)
    oversized_fee_proc = _run_adapter("--proof", str(oversized_fee_path), *common_args)
    missing_recipient_proc = _run_adapter("--proof", str(missing_recipient_path), *common_args)
    partial_frontier_proc = _run_adapter("--proof", str(partial_frontier_path), *common_args)
    zero_count_nonempty_root_proc = _run_adapter(
        "--proof",
        str(zero_count_nonempty_root_path),
        *common_args,
    )

    assert missing_order_proc.returncode == 1
    assert "risc0 meta keys mismatch" in missing_order_proc.stdout
    assert oversized_fee_proc.returncode == 1
    assert "meta.protocol_fee_share_bps must be <= 10000" in oversized_fee_proc.stdout
    assert missing_recipient_proc.returncode == 1
    assert "meta.protocol_fee_recipient_pubkey required when share_bps > 0" in missing_recipient_proc.stdout
    assert partial_frontier_proc.returncode == 1
    assert "risc0 frontier signature meta partial" in partial_frontier_proc.stdout
    assert zero_count_nonempty_root_proc.returncode == 1
    assert (
        "meta.shared_pool_frontier_signature_certificates_root must be empty root when count is zero"
        in zero_count_nonempty_root_proc.stdout
    )


def test_risc0_adapter_can_require_state_root_hash_binding(tmp_path: Path) -> None:
    body = _body(1)
    pre_state_root = _root("risc0-pre-state")
    post_state_root = _root("risc0-post-state")
    header = _header(body, pre_state_root=pre_state_root, post_state_root=post_state_root)
    proof = _proof_with_pre_app_hash(
        post_app_hash=post_state_root[2:],
        pre_app_hash=pre_state_root[2:],
    )
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "metadata.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-post-state-root",
        "--require-pre-app-hash-header-pre-state-root",
    )

    assert proc.returncode == 0, proc.stderr or proc.stdout
    report = json.loads(proc.stdout)
    assert report["post_state_root_checked"] is True
    assert report["pre_state_root_checked"] is True
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    assert metadata["post_state_root"] == post_state_root
    assert metadata["pre_state_root"] == pre_state_root


def test_risc0_adapter_accepts_empty_pre_app_hash_without_pre_state_equality(tmp_path: Path) -> None:
    body = _body(1)
    post_state_root = _root("risc0-post-state")
    header = _header(body, pre_state_root=_root("ledger-pre-state"), post_state_root=post_state_root)
    proof = _proof(post_app_hash=post_state_root[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-post-state-root",
        "--require-pre-app-hash-header-pre-state-root",
    )

    assert proc.returncode == 0, proc.stderr or proc.stdout
    assert json.loads(proc.stdout)["pre_state_root_checked"] is True


def test_risc0_adapter_rejects_state_root_hash_mismatch(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(
        body,
        pre_state_root=_root("risc0-pre-state"),
        post_state_root=_root("risc0-post-state"),
    )
    proof = _proof(post_app_hash=_hex("wrong-risc0-post-state"))
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    post_mismatch = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-post-state-root",
    )
    assert post_mismatch.returncode == 1
    assert "post_app_hash/header post_state_root mismatch" in post_mismatch.stdout

    wrong_pre_path = tmp_path / "wrong_pre_proof.json"
    _write_json(
        wrong_pre_path,
        _proof_with_pre_app_hash(
            post_app_hash=str(header["post_state_root"])[2:],
            pre_app_hash=_hex("wrong-risc0-pre-state"),
        ),
    )
    pre_mismatch = _run_adapter(
        "--proof",
        str(wrong_pre_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-pre-app-hash-header-pre-state-root",
    )
    assert pre_mismatch.returncode == 1
    assert "pre_app_hash/header pre_state_root mismatch" in pre_mismatch.stdout


def test_risc0_adapter_can_require_external_verifier(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    metadata_path = tmp_path / "metadata.json"
    verifier_path = _verifier_script(tmp_path / "accept_verifier.py", ok=True)
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--out",
        str(metadata_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--toolchain-lock-hash",
        _root("toolchain-lock"),
        "--require-post-app-hash-header-app-hash",
        "--require-risc0-verifier",
        "--risc0-verify-cmd",
        str(verifier_path),
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
    report = json.loads(proc.stdout)
    assert report["risc0_verified"] is True
    assert metadata_path.is_file()


def test_risc0_adapter_rejects_when_required_verifier_rejects(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    verifier_path = _verifier_script(tmp_path / "reject_verifier.py", ok=False)
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--require-risc0-verifier",
        "--risc0-verify-cmd",
        str(verifier_path),
    )
    assert proc.returncode == 1
    assert "risc0 verifier rejected proof" in proc.stdout


def test_risc0_adapter_rejects_required_verifier_without_command(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    proof = _proof(post_app_hash=str(header["app_hash"])[2:])
    body_path = tmp_path / "body.json"
    header_path = tmp_path / "header.json"
    proof_path = tmp_path / "proof.json"
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(proof_path, proof)

    proc = _run_adapter(
        "--proof",
        str(proof_path),
        "--header",
        str(header_path),
        "--body",
        str(body_path),
        "--require-risc0-verifier",
    )
    assert proc.returncode == 1
    assert "--require-risc0-verifier requires --risc0-verify-cmd" in proc.stdout
