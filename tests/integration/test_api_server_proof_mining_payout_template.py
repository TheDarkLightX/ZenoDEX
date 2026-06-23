"""
End-to-end test for the proof-mining payout TEMPLATE endpoint.

The template endpoint (POST /api/dex/proof_mining_payout_template) builds a
real, well-formed proof-mining claim plus the submit transaction. The decisive
checks: (1) feed the template's status_request into the live
/api/dex/proof_mining_status PREFLIGHT and assert every consistency check
passes (the preflight reports claimable=false only because it defers DEX-proof
verification, passing context=None by design); (2) supply the template's proof
context directly to evaluate_proof_mining_claimability and assert claimable
becomes True — proving the template produces a genuinely payable claim, closing
the previously-404 wiring gap the UI's ProofMiningWorkbench consumes.
"""

from __future__ import annotations

import json
import threading
from http.client import HTTPConnection


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


def _post(host: str, port: int, path: str, payload: dict) -> tuple[int, dict]:
    conn = HTTPConnection(host, port, timeout=4.0)
    conn.request(
        "POST",
        path,
        body=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    resp = conn.getresponse()
    body = json.loads(resp.read().decode("utf-8"))
    return resp.status, body


_SENDER = "0x" + "ab" * 48
_REWARD_POOL = "0x" + "cd" * 48


def _template_request(**overrides) -> dict:
    req = {
        "chain_id": "zeno-ledger-localtest-v0",
        "tx_sender_pubkey": _SENDER,
        "reward_pool_pubkey": _REWARD_POOL,
        "reward_pool_before": 64,
        "base_reward": 8,
        "epoch": 1,
        "proposal_slot": 0,
        "prover_id": 1,
        "faucet_mint": [{"pubkey": _SENDER, "asset": "0x" + "01" * 32, "amount": 10_000}],
    }
    req.update(overrides)
    return req


def test_payout_template_produces_claimable_status_request(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        status, tpl = _post(host, port, "/api/dex/proof_mining_payout_template", _template_request())
        assert status == 200, tpl
        assert tpl["ok"] is True
        assert tpl["template_mode"] == "preview_v1"
        assert tpl["reward_pool_pubkey"] == _REWARD_POOL
        assert tpl["reward_pool_before"] == 64
        assert tpl["reward_amount"] == 4  # 8 >> 1

        # The submit tx is the ZenoProofMining submit_proof carrying the claim.
        tx = tpl["tx"]
        op = tx["operations"]["10"]
        assert op["module"] == "ZenoProofMining"
        assert op["action"] == "submit_proof"
        assert op["recipient_pubkey"] == _SENDER
        assert op["claim"] == tpl["status_request"]["claim"]
        assert tx["tx_sender_pubkey"] == _SENDER

        # The status_request carries exactly the fields the status endpoint
        # consumes; context is returned separately (status rejects it inline).
        sr = tpl["status_request"]
        assert set(sr.keys()) == {
            "claim",
            "chain_balances",
            "app_state_json",
            "tx_sender_pubkey",
            "expected_proposal_hash",
        }
        assert sr["expected_proposal_hash"] == sr["claim"]["body"]["proposal_hash"]

        # THE decisive wiring check: the produced status_request flows into
        # the live claimability preflight (/api/dex/proof_mining_status) and
        # EVERY consistency check passes. The preflight intentionally does not
        # verify the DEX proof (it passes proof_mining_context_obj=None and
        # rejects a caller-supplied context), so `claimable` is structurally
        # False with the "requires verified DEX proof context" reason — that
        # is the honest preflight outcome, deferred to actual submission.
        s2, status_resp = _post(host, port, "/api/dex/proof_mining_status", sr)
        assert s2 == 200, status_resp
        assert status_resp["ok"] is True
        st = status_resp["status"]
        checks = st["checks"]
        assert checks["claim_valid"] is True, st
        assert checks["winner_matches_sender"] is True, st
        assert checks["proposal_hash_matches_context"] is True, st
        assert checks["reward_pool_balance_non_negative"] is True, st
        assert checks["runtime_state_present"] is True, st
        assert checks["reward_pool_pubkey_matches_state"] is True, st
        assert checks["reward_pool_balance_matches_state"] is True, st
        assert st["claimable"] is False
        assert st["error"] == "proof mining claim requires verified DEX proof context"

        # Stronger, direct check: with the DEX proof context SUPPLIED (the step
        # the preflight defers to submission), the SAME template claim is
        # genuinely claimable — proving the template produces a real,
        # payable claim, not just a preflight-consistent shell.
        from src.integration.proof_mining_claimability import (
            evaluate_proof_mining_claimability,
        )

        with_context = evaluate_proof_mining_claimability(
            reward_pool_pubkey=_REWARD_POOL,
            app_state_json=sr["app_state_json"],
            chain_balances=sr["chain_balances"],
            claim_artifact=sr["claim"],
            tx_sender_pubkey=sr["tx_sender_pubkey"],
            expected_proposal_hash=sr["expected_proposal_hash"],
            proof_mining_context_obj=tpl["proof_mining_context"],
        ).to_public_dict()
        assert with_context["claimable"] is True, with_context
        assert with_context["reward_pool_after"] == 64 - 4
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_is_deterministic(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        _, a = _post(host, port, "/api/dex/proof_mining_payout_template", _template_request())
        _, b = _post(host, port, "/api/dex/proof_mining_payout_template", _template_request())
        # Same inputs -> byte-identical claim + proposal hash (template is a
        # deterministic, request-bound projection).
        assert a["status_request"]["claim"] == b["status_request"]["claim"]
        assert a["status_request"]["expected_proposal_hash"] == b["status_request"]["expected_proposal_hash"]
        assert a["tx"] == b["tx"]
        # Different sender -> different proposal hash (binding is input-bound).
        _, c = _post(
            host,
            port,
            "/api/dex/proof_mining_payout_template",
            _template_request(tx_sender_pubkey="0x" + "ef" * 48),
        )
        assert c["status_request"]["expected_proposal_hash"] != a["status_request"]["expected_proposal_hash"]
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_rejects_missing_required_fields(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        for field, code in [
            ("chain_id", "missing_chain_id"),
            ("tx_sender_pubkey", "missing_tx_sender_pubkey"),
            ("reward_pool_pubkey", "missing_reward_pool_pubkey"),
        ]:
            req = _template_request()
            req[field] = ""
            status, body = _post(host, port, "/api/dex/proof_mining_payout_template", req)
            assert status == 400
            assert body == {"ok": False, "error": code}
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_rejects_underfunded_reward_pool(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        # reward_amount for base_reward=8, epoch=1 is 4; a pool of 3 cannot fund it.
        req = _template_request(reward_pool_before=3)
        status, body = _post(host, port, "/api/dex/proof_mining_payout_template", req)
        assert status == 400
        assert body["error"] == "reward_pool_before_below_reward_amount"
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_rejects_malformed_pubkeys(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        # Non-canonical sender pubkey (too short) must be rejected BEFORE a
        # template is returned, matching what the claimability gate requires.
        status, body = _post(
            host, port, "/api/dex/proof_mining_payout_template",
            _template_request(tx_sender_pubkey="0xdeadbeef"),
        )
        assert status == 400
        assert body["error"] == "bad_tx_sender_pubkey"

        status, body = _post(
            host, port, "/api/dex/proof_mining_payout_template",
            _template_request(reward_pool_pubkey="not-a-pubkey"),
        )
        assert status == 400
        assert body["error"] == "bad_reward_pool_pubkey"
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_rejects_pool_equal_sender(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        # Pool == sender would collapse the two chain_balances entries.
        status, body = _post(
            host, port, "/api/dex/proof_mining_payout_template",
            _template_request(reward_pool_pubkey=_SENDER),
        )
        assert status == 400
        assert body["error"] == "reward_pool_pubkey_must_differ_from_sender"
    finally:
        _stop_test_server(httpd, thread)


def test_payout_template_rejects_bad_amounts(monkeypatch) -> None:
    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", _REWARD_POOL)
    httpd, thread, host, port = _start_test_server()
    try:
        status, body = _post(
            host, port, "/api/dex/proof_mining_payout_template", _template_request(base_reward=-1)
        )
        assert status == 400
        assert body["error"].startswith("bad_")
        status, body = _post(
            host, port, "/api/dex/proof_mining_payout_template", _template_request(base_reward=0)
        )
        assert status == 400
        assert body["error"] == "bad_base_reward"
    finally:
        _stop_test_server(httpd, thread)
