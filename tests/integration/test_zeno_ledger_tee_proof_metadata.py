from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.core.confidential_extension_receipts import make_confidential_extension_receipt
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
    validate_proof_metadata_header_binding_v0,
)

ROOT = Path(__file__).resolve().parents[2]
ADAPTER_SCRIPT = ROOT / "tools" / "zeno_ledger_tee_proof_metadata.py"
NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
MEASUREMENT = f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"
POLICY_DIGEST = "0x" + ("d" * 64)


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


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


def _header(body: dict[str, object], *, proof_journal_hash: str = ZERO_ROOT_V0) -> dict[str, object]:
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    post_state_root = _root("post-state")
    config_digest = _root("config")
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": post_state_root,
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
        pre_state_root=_root("pre-state"),
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _receipt() -> dict[str, object]:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-tee-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=MEASUREMENT,
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


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _run_adapter(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ADAPTER_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _verifier_script(path: Path, *, ok: bool, bad_result: str | None = None) -> Path:
    body = f"""#!/usr/bin/env python3
import json
import sys

req = json.load(sys.stdin)
if req.get("provider") != "nitro":
    print(json.dumps({{"ok": False, "error": "bad provider"}}))
    raise SystemExit(0)
result = {{
    "measurement": {MEASUREMENT!r},
    "policy_digest": {POLICY_DIGEST!r},
    "attestation_epoch": 8,
}}
if {bad_result!r} == "measurement":
    result["measurement"] = "nitro:pcr0:{{}}:pcr8:{{}}".format("c" * 96, "d" * 96)
print(json.dumps({{"ok": {str(ok)}, "result": result}}))
"""
    path.write_text(body, encoding="utf-8")
    path.chmod(0o755)
    return path


def test_tee_adapter_builds_metadata_and_validates_bound_header(tmp_path: Path) -> None:
    body = _body(1)
    header_unbound = _header(body)
    receipt = _receipt()
    body_path = tmp_path / "body.json"
    header_unbound_path = tmp_path / "header_unbound.json"
    receipt_path = tmp_path / "receipt.json"
    metadata_path = tmp_path / "proof_metadata.json"
    _write_json(body_path, body)
    _write_json(header_unbound_path, header_unbound)
    _write_json(receipt_path, receipt)

    first = _run_adapter(
        "--receipt",
        str(receipt_path),
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
        "--approved-measurement",
        MEASUREMENT,
    )
    assert first.returncode == 0, first.stderr or first.stdout
    first_report = json.loads(first.stdout)
    assert first_report["proof_kind"] == "tee_attestation_v0"
    assert first_report["header_bound"] is False
    assert first_report["body_checked"] is True

    bound_header = _header(body, proof_journal_hash=str(first_report["proof_journal_hash"]))
    bound_header_path = tmp_path / "header_bound.json"
    bound_metadata_path = tmp_path / "proof_metadata_bound.json"
    _write_json(bound_header_path, bound_header)

    second = _run_adapter(
        "--receipt",
        str(receipt_path),
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
        "--approved-measurement",
        MEASUREMENT,
        "--require-bound-header",
    )
    assert second.returncode == 0, second.stderr or second.stdout
    metadata = json.loads(bound_metadata_path.read_text(encoding="utf-8"))
    validate_proof_metadata_header_binding_v0(metadata, bound_header)


def test_tee_adapter_rejects_unapproved_measurement(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    receipt = _receipt()
    receipt_path = tmp_path / "receipt.json"
    header_path = tmp_path / "header.json"
    _write_json(receipt_path, receipt)
    _write_json(header_path, header)

    proc = _run_adapter(
        "--receipt",
        str(receipt_path),
        "--header",
        str(header_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--approved-measurement",
        f"nitro:pcr0:{'c' * 96}:pcr8:{'d' * 96}",
    )
    assert proc.returncode == 1
    assert "receipt measurement is not in --approved-measurement" in proc.stdout


def test_tee_adapter_can_require_external_attestation_verifier(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    receipt = _receipt()
    receipt_path = tmp_path / "receipt.json"
    header_path = tmp_path / "header.json"
    attestation_path = tmp_path / "attestation.json"
    verifier_path = _verifier_script(tmp_path / "accept_tee_verifier.py", ok=True)
    _write_json(receipt_path, receipt)
    _write_json(header_path, header)
    _write_json(attestation_path, {"provider": "nitro", "raw_quote": "fixture"})

    proc = _run_adapter(
        "--receipt",
        str(receipt_path),
        "--header",
        str(header_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--approved-measurement",
        MEASUREMENT,
        "--require-tee-attestation-verifier",
        "--tee-attestation-verify-cmd",
        str(verifier_path),
        "--attestation-payload",
        str(attestation_path),
    )
    assert proc.returncode == 0, proc.stderr or proc.stdout
    assert json.loads(proc.stdout)["tee_verified"] is True


def test_tee_adapter_rejects_external_attestation_mismatch(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    receipt = _receipt()
    receipt_path = tmp_path / "receipt.json"
    header_path = tmp_path / "header.json"
    attestation_path = tmp_path / "attestation.json"
    verifier_path = _verifier_script(tmp_path / "bad_tee_verifier.py", ok=True, bad_result="measurement")
    _write_json(receipt_path, receipt)
    _write_json(header_path, header)
    _write_json(attestation_path, {"provider": "nitro", "raw_quote": "fixture"})

    proc = _run_adapter(
        "--receipt",
        str(receipt_path),
        "--header",
        str(header_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--approved-measurement",
        MEASUREMENT,
        "--require-tee-attestation-verifier",
        "--tee-attestation-verify-cmd",
        str(verifier_path),
        "--attestation-payload",
        str(attestation_path),
    )
    assert proc.returncode == 1
    assert "TEE attestation verifier measurement mismatch" in proc.stdout


def test_tee_adapter_rejects_required_verifier_without_payload(tmp_path: Path) -> None:
    body = _body(1)
    header = _header(body)
    receipt = _receipt()
    receipt_path = tmp_path / "receipt.json"
    header_path = tmp_path / "header.json"
    verifier_path = _verifier_script(tmp_path / "accept_tee_verifier.py", ok=True)
    _write_json(receipt_path, receipt)
    _write_json(header_path, header)

    proc = _run_adapter(
        "--receipt",
        str(receipt_path),
        "--header",
        str(header_path),
        "--conflict-schedule-hash",
        _root("schedule"),
        "--feature-suite-hash",
        _root("feature-suite"),
        "--dependency-lock-hash",
        _root("dependency-lock"),
        "--approved-measurement",
        MEASUREMENT,
        "--require-tee-attestation-verifier",
        "--tee-attestation-verify-cmd",
        str(verifier_path),
    )
    assert proc.returncode == 1
    assert "--require-tee-attestation-verifier requires --attestation-payload" in proc.stdout
