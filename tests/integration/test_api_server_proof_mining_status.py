from __future__ import annotations

import json
import threading
from http.client import HTTPConnection

from src.integration.proof_mining_context import ProofMiningContext, proof_mining_context_to_obj
from src.integration.proof_mining_runtime import (
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_to_obj,
)


def _start_test_server():
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = True  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _claim(*, miner_id: str, reward_pool_before: int) -> dict:
    from src.core.proof_mining_claims import build_proof_mining_claim

    return build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-api",
            "winner": {
                "miner_id": miner_id,
                "witness_sha256": "witness-api",
                "improvement_u64": 5,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-api",
        reward_pool_before=reward_pool_before,
        base_reward=8,
        epoch=1,
        proposal_slot=0,
        prover_id=1,
        chain_id="tau-testnet-alpha",
        prev_state_hash="sha256:prev",
        batch_hash="sha256:batch",
        dex_hash_after="sha256:after",
    )


def _context_from_claim(claim: dict) -> dict:
    binding = claim["body"]["proposal_binding"]
    return proof_mining_context_to_obj(
        ProofMiningContext(
            chain_id=str(binding["chain_id"]),
            prev_state_hash=str(binding["prev_state_hash"]),
            batch_hash=str(binding["batch_hash"]),
            witness_hash=str(binding["witness_hash"]),
            dex_hash_after=str(binding["dex_hash_after"]),
            proposal_hash=str(claim["body"]["proposal_hash"]),
            proof_scheme="dummy",
        )
    )


def _app_state_from_runtime_state(runtime_state) -> str:
    return json.dumps(
        {
            "schema": "zenodex/tau_app_state/v1",
            "proof_mining": proof_mining_runtime_state_to_obj(runtime_state),
        },
        separators=(",", ":"),
        sort_keys=True,
    )


def test_api_server_proof_mining_status_claimable(monkeypatch) -> None:
    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    httpd, thread, host, port = _start_test_server()
    try:
        req = {
            "app_state_json": "",
            "chain_balances": {reward_pool: 20, sender: 0},
            "claim": claim,
            "proof_mining_context": context,
            "tx_sender_pubkey": sender,
            "expected_proposal_hash": claim["body"]["proposal_hash"],
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/proof_mining_status",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        status = body["status"]
        assert status["claimable"] is True
        assert status["reward_amount"] == 4
        assert status["reward_pool_after"] == 16
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_proof_mining_status_rejects_runtime_snapshot_balance_drift(monkeypatch) -> None:
    sender = "0x" + "33" * 48
    reward_pool = "0x" + "77" * 48
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    runtime_state = initialize_proof_mining_runtime_state(
        reward_pool_pubkey=reward_pool,
        reward_pool_balance=20,
        claim_artifact=claim,
    )
    httpd, thread, host, port = _start_test_server()
    try:
        req = {
            "app_state_json": _app_state_from_runtime_state(runtime_state),
            "chain_balances": {reward_pool: 15, sender: 0},
            "claim": claim,
            "proof_mining_context": context,
            "tx_sender_pubkey": sender,
            "expected_proposal_hash": claim["body"]["proposal_hash"],
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/proof_mining_status",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 200
        assert body["ok"] is True
        status = body["status"]
        assert status["claimable"] is False
        assert status["error"] == "proof mining reward pool balance drift"
        assert status["checks"]["runtime_state_present"] is True
        assert status["checks"]["reward_pool_pubkey_matches_state"] is True
        assert status["checks"]["reward_pool_balance_matches_state"] is False
        assert status["checks"]["runtime_apply_ok"] is False
    finally:
        _stop_test_server(httpd, thread)


def test_api_server_proof_mining_status_requires_expected_hash(monkeypatch) -> None:
    sender = "0x" + "22" * 48
    reward_pool = "0x" + "88" * 48
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    claim = _claim(miner_id=sender, reward_pool_before=20)
    context = _context_from_claim(claim)
    httpd, thread, host, port = _start_test_server()
    try:
        req = {
            "app_state_json": "",
            "chain_balances": {reward_pool: 20, sender: 0},
            "claim": claim,
            "proof_mining_context": context,
            "tx_sender_pubkey": sender,
        }
        conn = HTTPConnection(host, port, timeout=2.0)
        conn.request(
            "POST",
            "/api/dex/proof_mining_status",
            body=json.dumps(req).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        resp = conn.getresponse()
        body = json.loads(resp.read().decode("utf-8"))
        assert resp.status == 400
        assert body["ok"] is False
        assert body["error"] == "missing_expected_proposal_hash"
    finally:
        _stop_test_server(httpd, thread)
