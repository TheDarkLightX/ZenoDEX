from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / "tools" / "proof_verifiers" / "risc0_perps_np_live_wrapper_v1.py"
SURFACE = "risc0.zenodex_perps_np_transition.v1"
LIVE_WALLET_SURFACE = "perps_stream8"
RECEIPT_HASH_DOMAIN = "zenodex.perps_wallet.proof_intent_receipt/v1"
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


def _request(*, surface: str = SURFACE, action: str = "run_epoch", proof_type: str = SURFACE) -> dict[str, object]:
    body = {
        "schema": "zenodex/perps_wallet/proof_intent_receipt/v1",
        "profile_id": "perps-stream8-risc0-or-equivalent-v1",
        "chain_id": "zenodex-local-1",
        "action": action,
        "market_id": "perp:chnp:ETH-PERP",
        "app_hash_before": "11" * 32,
        "app_hash_after": "22" * 32,
        "operation_hash": "33" * 32,
        "state_delta_witness_hash": None,
    }
    receipt_hash = _receipt_hash(body)
    return {
        "schema": "zenodex/live-proof-wrapper-request/v1",
        "surface": surface,
        "proof_intent_receipt_hash": receipt_hash,
        "proof_intent_receipt": {
            "schema": "zenodex/perps_wallet/proof_intent_receipt/v1",
            "profile_id": "perps-stream8-risc0-or-equivalent-v1",
            "body": body,
            "receipt_hash": receipt_hash,
        },
        "proof": {
            "proof_type": proof_type,
            "state_hash": "aa" * 32,
            "proof": "not-a-real-receipt",
            "actions": [
                {
                    "kind": "run_epoch",
                    "oracle": {
                        "oracle_bridge_id": "test-oracle",
                        "oracle_bridge_hash": "44" * 32,
                        "price_e8": 100,
                        "price_timestamp": 10,
                        "max_staleness_seconds": 5,
                        "observed_at": 12,
                        "pre_price_batch_commitment": "55" * 32,
                    },
                    "clearing_price_e8": 100,
                    "funding_rate_bps": 0,
                    "intents": [],
                }
            ],
            "meta": {
                "execution_context_hash": EXECUTION_CONTEXT_HASH,
                "proof_type": proof_type,
                "chain_id": "zenodex-local-1",
                "market_id": "perp:chnp:ETH-PERP",
                "operation_hash": "33" * 32,
                "pre_app_hash": "11" * 32,
                "post_app_hash": "22" * 32,
                "state_delta_hash": "66" * 32,
                "oracle_binding_hash": "77" * 32,
                "collateral_binding_hash": "88" * 32,
                "participant_set_hash": "99" * 32,
                "receipt_root": "aa" * 32,
            },
        },
        "expected_execution_context_hash": EXECUTION_CONTEXT_HASH,
        "verifier_request_hash": "wrapper-request-hash",
    }


def _run(
    req: dict[str, object],
    *,
    fake_cli: str | None = None,
    extra_env: dict[str, str] | None = None,
) -> dict[str, object]:
    env = os.environ.copy()
    if fake_cli is not None:
        env["RISC0_PERPS_NP_CLI_CMD_JSON"] = json.dumps([sys.executable, "-c", fake_cli])
    if extra_env:
        env.update(extra_env)
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


def test_risc0_perps_np_wrapper_binds_runtime_receipt_to_cli_request() -> None:
    fake_cli = """
import json, sys
obj = json.load(sys.stdin)
assert sys.argv[1:] == ["--expected-execution-context-hash", "ec" * 32]
assert obj["schema"] == "tau_state_proof_verify"
assert obj["state_hash"] == "aa" * 32
assert obj["chain_id"] == "zenodex-local-1"
assert obj["proof"]["proof_type"] == "risc0.zenodex_perps_np_transition.v1"
assert obj["tau_state"]["app_hash"] == "22" * 32
context = obj["context"]
assert context["execution_context_hash"] == "ec" * 32
assert context["chain_id"] == "zenodex-local-1"
assert context["app_hash_pre"] == "11" * 32
assert context["operation_hash"] == "33" * 32
assert context["state_delta_hash"] == "66" * 32
assert context["oracle_binding_hash"] == "77" * 32
assert context["collateral_binding_hash"] == "88" * 32
assert context["participant_set_hash"] == "99" * 32
assert context["receipt_root"] == "aa" * 32
assert obj["actions"][0]["kind"] == "run_epoch"
print('{"ok": true}')
"""
    out = _run(_request(), fake_cli=fake_cli)
    assert out["ok"] is True
    assert out["surface"] == SURFACE
    assert out["verified_surface"] == SURFACE
    assert out["proof_type"] == SURFACE
    assert out["production_security_claim"] is False


def test_risc0_perps_np_wrapper_requires_independent_execution_context() -> None:
    req = _request()
    req.pop("expected_execution_context_hash")
    out = _run(req, fake_cli="raise AssertionError('CLI must not run')")
    assert out["ok"] is False
    assert out["error"] == "expected_execution_context_hash must be a non-empty string"


def test_risc0_perps_np_wrapper_rejects_proof_context_substitution() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    meta = proof["meta"]
    assert isinstance(meta, dict)
    meta["execution_context_hash"] = "ed" * 32
    out = _run(req, fake_cli="raise AssertionError('CLI must not run')")
    assert out["ok"] is False
    assert out["error"] == "proof execution_context_hash mismatch"


def test_risc0_perps_np_wrapper_accepts_live_wallet_surface_alias() -> None:
    fake_cli = "import json, sys\njson.load(sys.stdin)\nprint('{\"ok\": true}')\n"
    out = _run(_request(surface=LIVE_WALLET_SURFACE), fake_cli=fake_cli)
    assert out["ok"] is True
    assert out["surface"] == LIVE_WALLET_SURFACE
    assert out["verified_surface"] == SURFACE


def test_risc0_perps_np_wrapper_rejects_wrong_surface() -> None:
    out = _run(_request(surface="perps_stream9"))
    assert out["ok"] is False
    assert out["error"] == "unsupported live proof-wrapper surface"


def test_risc0_perps_np_wrapper_rejects_wrong_proof_type() -> None:
    out = _run(_request(proof_type="risc0.zenodex_spot_transition.v1"))
    assert out["ok"] is False
    assert out["error"] == "unsupported proof_type"


def test_risc0_perps_np_wrapper_rejects_non_epoch_action_before_cli_verify() -> None:
    out = _run(_request(action="deposit_collateral"))
    assert out["ok"] is False
    assert out["error"] == "RISC0 perps NP proof only covers run_epoch/settle_epoch transitions"


def test_risc0_perps_np_wrapper_rejects_non_epoch_action_even_with_legacy_env_bypass() -> None:
    out = _run(
        _request(action="deposit_collateral"),
        extra_env={"RISC0_PERPS_NP_ALLOW_NON_EPOCH_ACTIONS": "1"},
    )
    assert out["ok"] is False
    assert out["error"] == "RISC0 perps NP proof only covers run_epoch/settle_epoch transitions"


def test_risc0_perps_np_wrapper_rejects_missing_receipt_app_hash_bindings() -> None:
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


def test_risc0_perps_np_wrapper_rejects_bad_state_delta_witness_hash_shape() -> None:
    req = _request()
    receipt = req["proof_intent_receipt"]
    assert isinstance(receipt, dict)
    body = receipt["body"]
    assert isinstance(body, dict)
    body["state_delta_witness_hash"] = "not-hex"
    proof = req["proof"]
    assert isinstance(proof, dict)
    meta = proof["meta"]
    assert isinstance(meta, dict)
    meta["state_delta_witness_hash"] = "not-hex"
    _refresh_receipt_hash(req)

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "hex binding must be 64 chars"


def test_risc0_perps_np_wrapper_rejects_state_delta_witness_hash_mismatch() -> None:
    req = _request()
    receipt = req["proof_intent_receipt"]
    assert isinstance(receipt, dict)
    body = receipt["body"]
    assert isinstance(body, dict)
    body["state_delta_witness_hash"] = "44" * 32
    proof = req["proof"]
    assert isinstance(proof, dict)
    meta = proof["meta"]
    assert isinstance(meta, dict)
    meta["state_delta_witness_hash"] = "55" * 32
    _refresh_receipt_hash(req)

    out = _run(req, fake_cli="import sys\nraise SystemExit('cli should not run')\n")

    assert out["ok"] is False
    assert out["error"] == "state_delta_witness_hash mismatch"


def test_risc0_perps_np_wrapper_recomputes_runtime_receipt_hash() -> None:
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


def test_risc0_perps_np_wrapper_rejects_production_claim() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    proof["production_security_claim"] = True
    out = _run(req)
    assert out["ok"] is False
    assert out["error"] == "RISC0 perps NP verifier cannot make production security claim"
