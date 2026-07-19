from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
from pathlib import Path

from src.integration.proof_mining_context import ProofMiningContext, proof_mining_context_to_obj
from tools.permissionless_proof_mining_status import _api_result_claimable

REPO = Path(__file__).resolve().parents[2]



def _start_static_status_server(payload: dict):
    import http.server as _http_server

    class _StaticStatusHandler(_http_server.BaseHTTPRequestHandler):
        def do_POST(self) -> None:  # noqa: N802
            body = json.dumps(payload).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, format: str, *args: object) -> None:  # noqa: A003
            _ = format, args

    httpd = _http_server.ThreadingHTTPServer(("127.0.0.1", 0), _StaticStatusHandler)
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    return httpd, thread


def _claim(*, miner_id: str, reward_pool_before: int) -> dict:
    from src.core.proof_mining_claims import build_proof_mining_claim

    return build_proof_mining_claim(
        round_obj={
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": True,
            "job_digest": "job-cli",
            "winner": {
                "miner_id": miner_id,
                "witness_sha256": "witness-cli",
                "improvement_u64": 7,
            },
            "candidates": [],
            "argmax_certificate": None,
        },
        round_id="round-cli",
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


def _write_json(path: Path, obj: object) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _start_test_server():
    from src.integration import api_server

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.dex_api_enabled = True  # type: ignore[attr-defined]
    httpd.api_bearer_token = ""  # type: ignore[attr-defined]
    httpd.external_auth_enforced = True  # type: ignore[attr-defined]

    thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    thread.start()
    host, port = httpd.server_address[:2]
    return httpd, thread, str(host), int(port)


def test_api_result_claimable_rejects_truthy_string_ok() -> None:
    assert _api_result_claimable({"ok": "true", "status": {"claimable": True}}) is False


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def test_permissionless_proof_mining_status_cli_local_success(tmp_path: Path) -> None:
    sender = "0x" + "11" * 48
    reward_pool = "0x" + "99" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    claim_path = tmp_path / "claim.json"
    balances_path = tmp_path / "balances.json"
    context_path = tmp_path / "context.json"
    output_path = tmp_path / "status.json"
    _write_json(claim_path, claim)
    _write_json(balances_path, {reward_pool: 20, sender: 0})
    _write_json(context_path, _context_from_claim(claim))

    env = dict(os.environ)
    env["TAU_DEX_PROOF_MINING_POOL_PUBKEY"] = reward_pool
    proc = subprocess.run(
        [
            sys.executable,
            "tools/permissionless_proof_mining_status.py",
            "--claim",
            str(claim_path),
            "--chain-balances",
            str(balances_path),
            "--tx-sender-pubkey",
            sender,
            "--expected-proposal-hash",
            str(claim["body"]["proposal_hash"]),
            "--proof-mining-context",
            str(context_path),
            "--output",
            str(output_path),
        ],
        cwd=REPO,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    body = json.loads(output_path.read_text(encoding="utf-8"))
    assert body["ok"] is True
    assert body["status"]["claimable"] is True
    assert body["status"]["reward_amount"] == 4


def test_permissionless_proof_mining_status_cli_local_rejected_claim_returns_nonzero(tmp_path: Path) -> None:
    sender = "0x" + "22" * 48
    reward_pool = "0x" + "88" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    claim_path = tmp_path / "claim.json"
    balances_path = tmp_path / "balances.json"
    context_path = tmp_path / "context.json"
    _write_json(claim_path, claim)
    _write_json(balances_path, {reward_pool: 20, sender: 0})
    _write_json(context_path, _context_from_claim(claim))

    env = dict(os.environ)
    env["TAU_DEX_PROOF_MINING_POOL_PUBKEY"] = reward_pool
    proc = subprocess.run(
        [
            sys.executable,
            "tools/permissionless_proof_mining_status.py",
            "--claim",
            str(claim_path),
            "--chain-balances",
            str(balances_path),
            "--tx-sender-pubkey",
            sender,
            "--expected-proposal-hash",
            "sha256:wrong",
            "--proof-mining-context",
            str(context_path),
        ],
        cwd=REPO,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    body = json.loads(proc.stdout)
    assert body["ok"] is True
    assert body["status"]["claimable"] is False
    assert body["status"]["error"] == "proof mining claim proposal_hash mismatch"


def test_permissionless_proof_mining_status_cli_api_mode(tmp_path: Path, monkeypatch) -> None:
    sender = "0x" + "33" * 48
    reward_pool = "0x" + "77" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    claim_path = tmp_path / "claim.json"
    balances_path = tmp_path / "balances.json"
    context_path = tmp_path / "context.json"
    _write_json(claim_path, claim)
    _write_json(balances_path, {reward_pool: 20, sender: 0})
    _write_json(context_path, _context_from_claim(claim))

    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", reward_pool)
    httpd, thread, host, port = _start_test_server()
    try:
        proc = subprocess.run(
            [
                sys.executable,
                "tools/permissionless_proof_mining_status.py",
                "--api-url",
                f"http://{host}:{port}",
                "--claim",
                str(claim_path),
                "--chain-balances",
                str(balances_path),
                "--tx-sender-pubkey",
                sender,
                "--expected-proposal-hash",
                str(claim["body"]["proposal_hash"]),
                "--proof-mining-context",
                str(context_path),
            ],
            cwd=REPO,
            env=dict(os.environ),
            check=False,
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0, proc.stderr
        body = json.loads(proc.stdout)
        assert body["ok"] is True
        assert body["status"]["claimable"] is True
    finally:
        _stop_test_server(httpd, thread)

def test_permissionless_proof_mining_status_cli_api_mode_rejected_status_returns_nonzero(tmp_path: Path) -> None:
    sender = "0x" + "34" * 48
    reward_pool = "0x" + "76" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    claim_path = tmp_path / "claim.json"
    balances_path = tmp_path / "balances.json"
    context_path = tmp_path / "context.json"
    _write_json(claim_path, claim)
    _write_json(balances_path, {reward_pool: 20, sender: 0})
    _write_json(context_path, _context_from_claim(claim))

    httpd, thread = _start_static_status_server(
        {"ok": True, "status": {"claimable": False, "error": "proof mining manager rejected"}}
    )
    try:
        proc = subprocess.run(
            [
                sys.executable,
                "tools/permissionless_proof_mining_status.py",
                "--api-url",
                f"http://127.0.0.1:{httpd.server_port}",
                "--claim",
                str(claim_path),
                "--chain-balances",
                str(balances_path),
                "--tx-sender-pubkey",
                sender,
                "--expected-proposal-hash",
                str(claim["body"]["proposal_hash"]),
                "--proof-mining-context",
                str(context_path),
            ],
            cwd=REPO,
            env=dict(os.environ),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        httpd.shutdown()
        httpd.server_close()
        thread.join(timeout=2.0)

    assert proc.returncode == 1
    body = json.loads(proc.stdout)
    assert body["ok"] is True
    assert body["status"]["claimable"] is False


def test_permissionless_proof_mining_status_cli_api_mode_requires_status_object(tmp_path: Path) -> None:
    sender = "0x" + "35" * 48
    reward_pool = "0x" + "75" * 48
    claim = _claim(miner_id=sender, reward_pool_before=20)
    claim_path = tmp_path / "claim.json"
    balances_path = tmp_path / "balances.json"
    context_path = tmp_path / "context.json"
    _write_json(claim_path, claim)
    _write_json(balances_path, {reward_pool: 20, sender: 0})
    _write_json(context_path, _context_from_claim(claim))

    httpd, thread = _start_static_status_server({"ok": True})
    try:
        proc = subprocess.run(
            [
                sys.executable,
                "tools/permissionless_proof_mining_status.py",
                "--api-url",
                f"http://127.0.0.1:{httpd.server_port}",
                "--claim",
                str(claim_path),
                "--chain-balances",
                str(balances_path),
                "--tx-sender-pubkey",
                sender,
                "--expected-proposal-hash",
                str(claim["body"]["proposal_hash"]),
                "--proof-mining-context",
                str(context_path),
            ],
            cwd=REPO,
            env=dict(os.environ),
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        httpd.shutdown()
        httpd.server_close()
        thread.join(timeout=2.0)

    assert proc.returncode == 1
    body = json.loads(proc.stdout)
    assert body == {"ok": True}
