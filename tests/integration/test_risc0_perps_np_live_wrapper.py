from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / "tools" / "proof_verifiers" / "risc0_perps_np_live_wrapper_v1.py"
SURFACE = "risc0.zenodex_perps_np_transition.v1"


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
    return {
        "schema": "zenodex/live-proof-wrapper-request/v1",
        "surface": surface,
        "proof_intent_receipt_hash": "receipt-hash",
        "proof_intent_receipt": {
            "schema": "zenodex/perps_wallet/proof_intent_receipt/v1",
            "profile_id": "perps-stream8-risc0-or-equivalent-v1",
            "body": body,
            "receipt_hash": "receipt-hash",
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
        "verifier_request_hash": "wrapper-request-hash",
    }


def _run(req: dict[str, object], *, fake_cli: str | None = None) -> dict[str, object]:
    env = os.environ.copy()
    if fake_cli is not None:
        env["RISC0_PERPS_NP_CLI_CMD_JSON"] = json.dumps([sys.executable, "-c", fake_cli])
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
assert obj["schema"] == "tau_state_proof_verify"
assert obj["state_hash"] == "aa" * 32
assert obj["chain_id"] == "zenodex-local-1"
assert obj["proof"]["proof_type"] == "risc0.zenodex_perps_np_transition.v1"
assert obj["tau_state"]["app_hash"] == "22" * 32
context = obj["context"]
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
    assert out["proof_type"] == SURFACE
    assert out["production_security_claim"] is False


def test_risc0_perps_np_wrapper_rejects_wrong_surface() -> None:
    out = _run(_request(surface="perps_stream8"))
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


def test_risc0_perps_np_wrapper_rejects_production_claim() -> None:
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    proof["production_security_claim"] = True
    out = _run(req)
    assert out["ok"] is False
    assert out["error"] == "RISC0 perps NP verifier cannot make production security claim"


def test_risc0_perps_np_wrapper_rejects_echo_local_fixture_proof() -> None:
    """An echo / local-testnet fixture proof (accepted by
    local_live_wrapper_echo_v1) must NEVER be accepted by the strict production
    wrapper. The echo fixture carries no real ``proof_type`` and only a
    ``system: local-testnet-live-wrapper-fixture-v1`` tag, so the strict wrapper
    must reject it as an unsupported proof type before ever touching the CLI.
    Locks the "echo wrappers never count as production" invariant.
    """
    req = _request()
    proof = req["proof"]
    assert isinstance(proof, dict)
    # Replace the strict RISC0 proof with the echo fixture shape.
    proof.pop("proof_type", None)
    proof.pop("meta", None)
    proof.pop("actions", None)
    proof["system"] = "local-testnet-live-wrapper-fixture-v1"
    proof["production_security_claim"] = False
    out = _run(req)
    assert out["ok"] is False
    assert out["error"] == "unsupported proof_type"
