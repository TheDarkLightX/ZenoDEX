from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from tools.permissionless_round_ledger import (
    append_round_record,
    build_round_ledger_record,
    verify_ledger_rows,
)
from tools.permissionless_solver_proof_mining_claim import build_proof_mining_claim


def _round_obj(*, round_id: str, miner_id: str, witness_sha256: str, improvement_u64: int, job_digest: str) -> dict:
    return {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": job_digest,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": witness_sha256,
            "improvement_u64": improvement_u64,
        },
        "candidates": [],
        "argmax_certificate": None,
        "round_id_hint": round_id,
    }


def _payout_plan(*, round_id: str, miner_id: str, witness_sha256: str, improvement_u64: int, payout_amount: int, job_digest: str, reward_pool_before: int) -> dict:
    body = {
        "schema": "zenodex/permissionless_solver_payout_plan/v1",
        "round_id": round_id,
        "job_digest": job_digest,
        "winner": {
            "miner_id": miner_id,
            "witness_sha256": witness_sha256,
            "improvement_u64": improvement_u64,
            "payout_amount": payout_amount,
        },
        "budget": {
            "reward_pool_before": reward_pool_before,
            "reward_pool_after": reward_pool_before - payout_amount,
            "base_reward": 5,
            "improvement_reward_bps": 1000,
            "max_reward": 25,
        },
        "conditions": {"round_ok": True, "positive_improvement": True, "winner_only": True},
    }
    plan_hash = sha256_hex(domain_sep_bytes("permissionless_solver_payout_plan", version=1) + canonical_json_bytes(body))
    return {"body": body, "plan_hash": plan_hash}


def _proof_mining_claim(*, round_id: str, miner_id: str, witness_sha256: str, improvement_u64: int, job_digest: str, reward_pool_before: int) -> dict:
    return build_proof_mining_claim(
        round_obj=_round_obj(
            round_id=round_id,
            miner_id=miner_id,
            witness_sha256=witness_sha256,
            improvement_u64=improvement_u64,
            job_digest=job_digest,
        ),
        round_id=round_id,
        reward_pool_before=reward_pool_before,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
    )


def test_round_ledger_appends_hash_chain(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    r1 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
        reward_artifact=_payout_plan(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, payout_amount=5, job_digest="job1", reward_pool_before=10),
        prev_record_hash="",
    )
    append_round_record(ledger_path=ledger_path, record=r1)

    r2 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r2", miner_id="bob", witness_sha256="sha:b", improvement_u64=9, job_digest="job2"),
        reward_artifact=_payout_plan(round_id="r2", miner_id="bob", witness_sha256="sha:b", improvement_u64=9, payout_amount=3, job_digest="job2", reward_pool_before=5),
        prev_record_hash=r1["record_hash"],
    )
    append_round_record(ledger_path=ledger_path, record=r2)

    rows = [json.loads(line) for line in ledger_path.read_text(encoding="utf-8").splitlines()]
    ok, msg = verify_ledger_rows(rows)
    assert ok is True
    assert msg == "ok"
    assert rows[1]["body"]["prev_record_hash"] == r1["record_hash"]


def test_round_ledger_rejects_winner_mismatch() -> None:
    with pytest.raises(ValueError, match="winner miner mismatch"):
        build_round_ledger_record(
            round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
            reward_artifact=_payout_plan(round_id="r1", miner_id="bob", witness_sha256="sha:a", improvement_u64=7, payout_amount=5, job_digest="job1", reward_pool_before=10),
            prev_record_hash="",
        )


def test_round_ledger_detects_hash_chain_tamper(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    record = build_round_ledger_record(
        round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
        reward_artifact=_payout_plan(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, payout_amount=5, job_digest="job1", reward_pool_before=10),
        prev_record_hash="",
    )
    append_round_record(ledger_path=ledger_path, record=record)
    rows = [json.loads(line) for line in ledger_path.read_text(encoding="utf-8").splitlines()]
    rows[0]["body"]["winner"]["payout_amount"] = 6
    ok, msg = verify_ledger_rows(rows)
    assert ok is False
    assert "record_hash mismatch" in msg


def test_round_ledger_accepts_proof_mining_claim_artifact(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    record = build_round_ledger_record(
        round_obj=_round_obj(round_id="r-proof", miner_id="alice", witness_sha256="sha:a", improvement_u64=11, job_digest="job-proof"),
        reward_artifact=_proof_mining_claim(
            round_id="r-proof",
            miner_id="alice",
            witness_sha256="sha:a",
            improvement_u64=11,
            job_digest="job-proof",
            reward_pool_before=20,
        ),
        prev_record_hash="",
    )
    append_round_record(ledger_path=ledger_path, record=record)
    rows = [json.loads(line) for line in ledger_path.read_text(encoding="utf-8").splitlines()]
    ok, msg = verify_ledger_rows(rows)
    assert ok is True
    assert msg == "ok"
    assert rows[0]["body"]["reward_artifact_schema"] == "zenodex/permissionless_solver_proof_mining_claim/v1"


def test_round_ledger_rejects_inadmissible_proof_mining_claim() -> None:
    claim = build_proof_mining_claim(
        round_obj=_round_obj(round_id="r-bad", miner_id="alice", witness_sha256="sha:a", improvement_u64=11, job_digest="job-bad"),
        round_id="r-bad",
        reward_pool_before=3,
        base_reward=8,
        epoch=0,
        proposal_slot=0,
        prover_id=0,
        allow_rejected=True,
    )
    with pytest.raises(ValueError, match="inadmissible"):
        build_round_ledger_record(
            round_obj=_round_obj(round_id="r-bad", miner_id="alice", witness_sha256="sha:a", improvement_u64=11, job_digest="job-bad"),
            reward_artifact=claim,
            prev_record_hash="",
        )


def test_round_ledger_rejects_forged_claim_hash() -> None:
    claim = _proof_mining_claim(
        round_id="r-hash",
        miner_id="alice",
        witness_sha256="sha:a",
        improvement_u64=11,
        job_digest="job-hash",
        reward_pool_before=20,
    )
    claim["claim_hash"] = "sha256:deadbeef"
    with pytest.raises(ValueError, match="claim_hash mismatch"):
        build_round_ledger_record(
            round_obj=_round_obj(round_id="r-hash", miner_id="alice", witness_sha256="sha:a", improvement_u64=11, job_digest="job-hash"),
            reward_artifact=claim,
            prev_record_hash="",
        )


def test_round_ledger_cli_appends_proof_mining_claim(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    round_path = tmp_path / "round.json"
    claim_path = tmp_path / "claim.json"

    round_obj = _round_obj(round_id="r-cli", miner_id="alice", witness_sha256="sha:a", improvement_u64=12, job_digest="job-cli")
    round_path.write_text(json.dumps(round_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    claim = _proof_mining_claim(
        round_id="r-cli",
        miner_id="alice",
        witness_sha256="sha:a",
        improvement_u64=12,
        job_digest="job-cli",
        reward_pool_before=20,
    )
    claim_path.write_text(json.dumps(claim, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    subprocess.check_call(
        [
            "python3",
            "tools/permissionless_round_ledger.py",
            "--ledger",
            str(ledger_path),
            "--round",
            str(round_path),
            "--proof-mining-claim",
            str(claim_path),
        ]
    )

    verify = subprocess.check_output(
        [
            "python3",
            "tools/permissionless_round_ledger.py",
            "--ledger",
            str(ledger_path),
            "--verify-only",
            "--json",
        ],
        text=True,
    )
    payload = json.loads(verify)
    assert payload["ok"] is True
    assert payload["rows"] == 1


def test_round_ledger_verify_detects_pool_continuity_gap(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    r1 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
        reward_artifact=_payout_plan(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, payout_amount=5, job_digest="job1", reward_pool_before=10),
        prev_record_hash="",
    )
    append_round_record(ledger_path=ledger_path, record=r1)
    r2 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r2", miner_id="bob", witness_sha256="sha:b", improvement_u64=9, job_digest="job2"),
        reward_artifact=_payout_plan(round_id="r2", miner_id="bob", witness_sha256="sha:b", improvement_u64=9, payout_amount=2, job_digest="job2", reward_pool_before=4),
        prev_record_hash=r1["record_hash"],
    )
    append_round_record(ledger_path=ledger_path, record=r2)
    rows = [json.loads(line) for line in ledger_path.read_text(encoding="utf-8").splitlines()]
    ok, msg = verify_ledger_rows(rows)
    assert ok is False
    assert "reward pool continuity mismatch" in msg


def test_round_ledger_verify_detects_duplicate_proposal_hash(tmp_path: Path) -> None:
    ledger_path = tmp_path / "ledger.jsonl"
    claim_1 = build_proof_mining_claim(
        round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
        round_id="r1",
        reward_pool_before=20,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=0,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        dex_hash_after="sha256:after",
    )
    claim_2 = build_proof_mining_claim(
        round_obj=_round_obj(round_id="r2", miner_id="bob", witness_sha256="sha:a", improvement_u64=9, job_digest="job2"),
        round_id="r2",
        reward_pool_before=16,
        base_reward=8,
        epoch=2,
        proposal_slot=1,
        prover_id=1,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        dex_hash_after="sha256:after",
    )
    r1 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r1", miner_id="alice", witness_sha256="sha:a", improvement_u64=7, job_digest="job1"),
        reward_artifact=claim_1,
        prev_record_hash="",
    )
    append_round_record(ledger_path=ledger_path, record=r1)
    r2 = build_round_ledger_record(
        round_obj=_round_obj(round_id="r2", miner_id="bob", witness_sha256="sha:a", improvement_u64=9, job_digest="job2"),
        reward_artifact=claim_2,
        prev_record_hash=r1["record_hash"],
    )
    append_round_record(ledger_path=ledger_path, record=r2)
    rows = [json.loads(line) for line in ledger_path.read_text(encoding="utf-8").splitlines()]
    ok, msg = verify_ledger_rows(rows)
    assert ok is False
    assert "duplicate proposal_hash" in msg
