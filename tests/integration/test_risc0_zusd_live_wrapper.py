from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / "tools" / "proof_verifiers" / "risc0_zusd_live_wrapper_v1.py"
PROOF_TYPE = "risc0.zenodex_zusd_transition.v1"
SURFACE = "zusd_stream11"
OWNER = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
RECEIPT_HASH_DOMAIN = "zenodex.zusd_monetary_wallet.proof_intent_receipt/v1"
EXECUTION_CONTEXT_HASH = "ec" * 32


def _receipt_hash(body: dict[str, object]) -> str:
    return sha256_hex(domain_sep_bytes(RECEIPT_HASH_DOMAIN) + canonical_json_bytes(dict(body)))


def _refresh_receipt_hash(req: dict[str, object]) -> None:
    receipt = req["proof_intent_receipt"]
    assert isinstance(receipt, dict)
    body = receipt["body"]
    assert isinstance(body, dict)
    receipt_hash = _receipt_hash(body)
    receipt["receipt_hash"] = receipt_hash
    req["proof_intent_receipt_hash"] = receipt_hash


def _request(*, surface: str = SURFACE, action: str = "mint_zusd", proof_type: str = PROOF_TYPE) -> dict[str, object]:
    body = {
        "schema": "zenodex/zusd_monetary_wallet/proof_intent_receipt/v1",
        "profile_id": "zusd_stream11_live_monetary_v0",
        "chain_id": "tau-test-zusd",
        "stream_key": "11",
        "action": action,
        "asset_id": "zUSD",
        "app_hash_before": "11" * 32,
        "app_hash_after": "22" * 32,
        "operation_hash": "33" * 32,
        "actor_pubkey": OWNER,
        "nonce_before": 0,
        "nonce_after": 1,
    }
    receipt_hash = _receipt_hash(body)
    return {
        "schema": "zenodex/live-proof-wrapper-request/v1",
        "surface": surface,
        "proof_intent_receipt_hash": receipt_hash,
        "proof_intent_receipt": {
            "schema": "zenodex/zusd_monetary_wallet/proof_intent_receipt/v1",
            "profile_id": "zusd_stream11_live_monetary_v0",
            "body": body,
            "receipt_hash": receipt_hash,
        },
        "proof": {
            "proof_type": proof_type,
            "state_hash": "aa" * 32,
            "proof": "not-a-real-receipt",
            "operation": {
                "kind": "deposit_mint",
                "pubkey": OWNER,
                "collateral_asset": "tAGRS",
                "deposit_amount_e8": 200000000000,
                "mint_amount_e8": 100000000000,
                "oracle": {
                    "oracle_bridge_id": "test-oracle",
                    "oracle_bridge_hash": "44" * 32,
                    "price_e8": 100000000,
                    "price_timestamp": 10,
                    "max_staleness_seconds": 5,
                    "observed_at": 12,
                    "pre_price_batch_commitment": "55" * 32,
                },
                "mcr_bps": 11000,
                "nonce": 1,
            },
            "meta": {
                "execution_context_hash": EXECUTION_CONTEXT_HASH,
                "proof_type": proof_type,
                "chain_id": "tau-test-zusd",
                "vault_id": f"zusd:vault:{OWNER}",
                "owner_pubkey": OWNER,
                "operation_hash": "33" * 32,
                "pre_app_hash": "11" * 32,
                "post_app_hash": "22" * 32,
                "state_delta_hash": "66" * 32,
                "oracle_binding_hash": "77" * 32,
                "participant_set_hash": "88" * 32,
                "zusd_balance_root_hash": "99" * 32,
                "zusd_vault_root_hash": "aa" * 32,
            },
        },
        "expected_execution_context_hash": EXECUTION_CONTEXT_HASH,
        "verifier_request_hash": "wrapper-request-hash",
    }


def _run(req: dict[str, object], *, fake_cli: str | None = None) -> dict[str, object]:
    env = os.environ.copy()
    if fake_cli is not None:
        env["RISC0_ZUSD_CLI_CMD_JSON"] = json.dumps([sys.executable, "-c", fake_cli])
    proc = subprocess.run(
        [sys.executable, str(WRAPPER)],
        input=json.dumps(req),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=ROOT,
        env=env,
        timeout=10,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    assert isinstance(out, dict)
    return out


def test_risc0_zusd_wrapper_binds_runtime_receipt_to_cli_expected() -> None:
    fake_cli = """
import json, sys
obj = json.load(sys.stdin)
assert sys.argv[1:] == ["--expected-execution-context-hash", "ec" * 32]
assert obj["schema"] == "tau_state_proof_verify"
assert obj["state_hash"] == "aa" * 32
assert obj["proof"]["proof_type"] == "risc0.zenodex_zusd_transition.v1"
assert obj["chain_id"] == "tau-test-zusd"
assert obj["tau_state"]["app_hash"] == "22" * 32
context = obj["context"]
assert context["execution_context_hash"] == "ec" * 32
assert context["chain_id"] == "tau-test-zusd"
assert context["operation_hash"] == "33" * 32
assert context["app_hash_pre"] == "11" * 32
assert context["state_delta_hash"] == "66" * 32
assert context["oracle_binding_hash"] == "77" * 32
assert context["participant_set_hash"] == "88" * 32
assert context["zusd_balance_root_hash"] == "99" * 32
assert context["zusd_vault_root_hash"] == "aa" * 32
assert obj["operation"]["kind"] == "deposit_mint"
print('{"ok": true}')
"""
    out = _run(_request(), fake_cli=fake_cli)
    assert out["ok"] is True
    assert out["surface"] == SURFACE
    assert out["proof_type"] == PROOF_TYPE
    assert out["production_security_claim"] is False


def test_risc0_zusd_wrapper_requires_independent_execution_context() -> None:
    req = _request()
    req.pop("expected_execution_context_hash")
    out = _run(req, fake_cli="raise AssertionError('CLI must not run')")
    assert out["ok"] is False
    assert out["error"] == "expected_execution_context_hash must be a non-empty string"


def test_risc0_zusd_wrapper_rejects_proof_context_substitution() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    meta = proof["meta"]
    assert isinstance(meta, dict)
    meta["execution_context_hash"] = "ed" * 32
    out = _run(req, fake_cli="raise AssertionError('CLI must not run')")
    assert out["ok"] is False
    assert out["error"] == "proof execution_context_hash mismatch"


def test_risc0_zusd_wrapper_rejects_wrong_surface() -> None:
    out = _run(_request(surface=PROOF_TYPE))
    assert out["ok"] is False
    assert out["error"] == "unsupported live proof-wrapper surface"


def test_risc0_zusd_wrapper_rejects_wrong_proof_type() -> None:
    out = _run(_request(proof_type="risc0.zenodex_perps_np_transition.v1"))
    assert out["ok"] is False
    assert out["error"] == "unsupported proof_type"


def test_risc0_zusd_wrapper_rejects_non_mint_action_before_cli_verify() -> None:
    out = _run(_request(action="repay_zusd"))
    assert out["ok"] is False
    assert out["error"] == "RISC0 zUSD proof only covers mint_zusd"


def test_risc0_zusd_wrapper_rejects_missing_receipt_app_hash_bindings() -> None:
    for field in ("app_hash_before", "app_hash_after"):
        req = _request()
        receipt = req["proof_intent_receipt"]
        assert isinstance(receipt, dict)
        body = receipt["body"]
        assert isinstance(body, dict)
        body[field] = None
        _refresh_receipt_hash(req)

        out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

        assert out["ok"] is False
        assert out["error"] == f"proof_intent_receipt.body.{field} must be a non-empty string"


def test_risc0_zusd_wrapper_rejects_receipt_nonce_gap_before_cli_verify() -> None:
    req = _request()
    receipt = req["proof_intent_receipt"]
    assert isinstance(receipt, dict)
    body = receipt["body"]
    assert isinstance(body, dict)
    body["nonce_after"] = 2
    _refresh_receipt_hash(req)

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "proof_intent_receipt nonce transition must be strict-sequential"


def test_risc0_zusd_wrapper_rejects_operation_nonce_mismatch_before_cli_verify() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    operation = proof["operation"]
    assert isinstance(operation, dict)
    operation["nonce"] = 2

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "proof.operation.nonce mismatch"


def test_risc0_zusd_wrapper_rejects_operation_pubkey_mismatch_before_cli_verify() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    operation = proof["operation"]
    assert isinstance(operation, dict)
    operation["pubkey"] = "0x" + "bb" * 48

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "proof.operation.pubkey mismatch"


def test_risc0_zusd_wrapper_recomputes_runtime_receipt_hash() -> None:
    req = _request()
    receipt = req["proof_intent_receipt"]
    assert isinstance(receipt, dict)
    body = receipt["body"]
    assert isinstance(body, dict)
    body["operation_hash"] = "44" * 32
    receipt["receipt_hash"] = "same-bogus-hash"
    req["proof_intent_receipt_hash"] = "same-bogus-hash"

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "proof_intent_receipt.receipt_hash mismatch"


def test_risc0_zusd_wrapper_rejects_production_claim() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    proof["production_security_claim"] = True
    out = _run(req)
    assert out["ok"] is False
    assert out["error"] == "RISC0 zUSD verifier cannot make production security claim"
