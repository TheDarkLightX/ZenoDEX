from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

from tools.check_zeno_oracle_cross_domain_finality_gate import (
    check_finality_gate,
    read_content_hash,
    receipt_content_hash,
    sample_policy,
    sample_read,
    sample_receipt_bundle,
)

ROOT = Path(__file__).resolve().parents[1]


def _sample_inputs() -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    policy = sample_policy()
    read = sample_read(policy)
    receipts = sample_receipt_bundle(policy, read)
    return policy, read, receipts


def _refresh_receipt_id(receipts: dict[str, object], kind: str) -> None:
    raw = receipts["receipts"]
    assert isinstance(raw, list)
    for receipt in raw:
        assert isinstance(receipt, dict)
        if receipt["kind"] == kind:
            receipt["receipt_id"] = receipt_content_hash(receipt)
            return
    raise AssertionError(f"receipt kind missing: {kind}")


def test_cross_domain_finality_gate_accepts_sample_bundle() -> None:
    policy, read, receipts = _sample_inputs()

    result = check_finality_gate(policy, read, receipts)

    assert result["schema"] == "zenodex.oracle.cross_domain_finality_gate_check.v1"
    assert result["status"] == "accepted"
    assert result["receipt_bundle_status"] == "accepted"
    assert result["receipt_kind_count"] == 2
    assert result["error_count"] == 0
    assert "does_not_claim_cross_domain_finality" in result["not_claimed"]


def test_cross_domain_finality_gate_rejects_missing_receipt_bundle() -> None:
    policy, read, _receipts = _sample_inputs()

    result = check_finality_gate(policy, read, None)

    assert result["status"] == "rejected"
    assert result["receipt_bundle_status"] == "missing"
    assert "receipt_bundle_required" in result["errors"]


def test_cross_domain_finality_gate_rejects_insufficient_confirmations() -> None:
    policy, read, receipts = _sample_inputs()
    mutated = copy.deepcopy(receipts)
    raw = mutated["receipts"]
    assert isinstance(raw, list)
    source = next(receipt for receipt in raw if isinstance(receipt, dict) and receipt["kind"] == "source_finality_checkpoint")
    payload = source["payload"]
    assert isinstance(payload, dict)
    payload["confirmation_count"] = int(policy["min_confirmations"]) - 1
    _refresh_receipt_id(mutated, "source_finality_checkpoint")

    result = check_finality_gate(policy, read, mutated)

    assert result["status"] == "rejected"
    assert "source_payload_confirmation_count_below_policy" in result["errors"]


def test_cross_domain_finality_gate_rejects_source_receipt_before_finalized_block() -> None:
    policy, read, receipts = _sample_inputs()
    mutated = copy.deepcopy(receipts)
    raw = mutated["receipts"]
    assert isinstance(raw, list)
    source = next(receipt for receipt in raw if isinstance(receipt, dict) and receipt["kind"] == "source_finality_checkpoint")
    payload = source["payload"]
    assert isinstance(payload, dict)
    source["block_number"] = int(payload["finalized_block_number"]) - 1
    _refresh_receipt_id(mutated, "source_finality_checkpoint")

    result = check_finality_gate(policy, read, mutated)

    assert result["status"] == "rejected"
    assert "source_receipt_block_before_finalized_block" in result["errors"]


def test_cross_domain_finality_gate_rejects_target_finality_receipt_mismatch() -> None:
    policy, read, receipts = _sample_inputs()
    mutated = copy.deepcopy(receipts)
    raw = mutated["receipts"]
    assert isinstance(raw, list)
    target = next(receipt for receipt in raw if isinstance(receipt, dict) and receipt["kind"] == "target_adapter_acceptance")
    payload = target["payload"]
    assert isinstance(payload, dict)
    payload["finality_receipt_id"] = "sha256:" + "0" * 64
    _refresh_receipt_id(mutated, "target_adapter_acceptance")

    result = check_finality_gate(policy, read, mutated)

    assert result["status"] == "rejected"
    assert "target_payload_finality_receipt_id_mismatch" in result["errors"]


def test_cross_domain_finality_gate_rejects_read_hash_drift() -> None:
    policy, read, receipts = _sample_inputs()
    mutated_read = dict(read)
    mutated_read["query_id"] = "oracle:eth-usdc:wrong-query"

    result = check_finality_gate(policy, mutated_read, receipts)

    assert result["status"] == "rejected"
    assert "read_id_mismatch" in result["errors"]


def test_cross_domain_finality_gate_rejects_receipt_bundle_read_drift() -> None:
    policy, read, receipts = _sample_inputs()
    mutated_read = dict(read)
    mutated_read["query_id"] = "oracle:eth-usdc:alternate-query"
    mutated_read["read_id"] = read_content_hash(mutated_read)

    result = check_finality_gate(policy, mutated_read, receipts)

    assert result["status"] == "rejected"
    assert "receipt_bundle_read_id_mismatch" in result["errors"]
    assert "source_payload_read_id_mismatch" in result["errors"]


def test_cross_domain_finality_gate_cli_sample_and_require_live(tmp_path: Path) -> None:
    accepted = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_cross_domain_finality_gate.py",
            "--format",
            "text",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert accepted.returncode == 0, accepted.stdout + accepted.stderr
    assert "status = accepted" in accepted.stdout
    assert "receipt_bundle_status = accepted" in accepted.stdout

    sample_policy_proc = subprocess.run(
        [sys.executable, "tools/check_zeno_oracle_cross_domain_finality_gate.py", "--sample-policy"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    policy_path = tmp_path / "policy.json"
    policy_path.write_text(sample_policy_proc.stdout, encoding="utf-8")

    sample_read_proc = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_cross_domain_finality_gate.py",
            "--policy",
            str(policy_path),
            "--sample-read",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    read_path = tmp_path / "read.json"
    read_path.write_text(sample_read_proc.stdout, encoding="utf-8")

    missing_receipts = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_cross_domain_finality_gate.py",
            "--policy",
            str(policy_path),
            "--read",
            str(read_path),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert missing_receipts.returncode == 1
    missing_receipt = json.loads(missing_receipts.stdout)
    assert "receipt_bundle_required" in missing_receipt["errors"]

    require_live = subprocess.run(
        [
            sys.executable,
            "tools/check_zeno_oracle_cross_domain_finality_gate.py",
            "--require-live",
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert require_live.returncode == 1
    receipt = json.loads(require_live.stdout)
    assert receipt["receipt_bundle_status"] == "rejected"
    assert "live_finality_adapter_receipts_not_verified_onchain" in receipt["errors"]
