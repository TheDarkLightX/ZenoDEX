from __future__ import annotations

import json
import sys
from dataclasses import replace

import src.integration.zusd_monetary_wallet_api as monetary_api
from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, step
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.integration.zusd_monetary_bridge import (
    init_monetary_state,
    zusd_monetary_sender_nonce_key,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable

ALICE_PRIVKEY = 82
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(81)
ASSET_A = "0x" + "a1" * 32
ASSET_B = "0x" + "b2" * 32


def _ok(core, tag: str, **kwargs):
    res = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _wrapped_app_state() -> dict[str, object]:
    monetary = init_monetary_state(
        monetary_api._runtime_monetary_config(  # noqa: SLF001
            chain_id=monetary_api._tau_chain_id(),  # noqa: SLF001
        )
    )
    core = monetary.core
    core = _ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _ok(core, "deposit_collateral", amount_e8=20 * E8)
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            replace(
                monetary,
                core=core,
                vault_owner_pubkey=ALICE,
            )
        ),
    }


class _FakeClient:
    def __init__(self, _cfg=None) -> None:
        self.sent: list[dict[str, object]] = []

    def rpc(self, cmd: str) -> str:
        if cmd == "hello version=1":
            return "HELLO: ok"
        raise AssertionError(f"unexpected rpc call: {cmd}")

    def getappstate(self, *, full: bool = False) -> str:
        assert full is True
        payload = {
            "app_hash": "sha256:" + "ab" * 32,
            "app_state": _wrapped_app_state(),
        }
        return json.dumps(payload, sort_keys=True)

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        if sender_pubkey_hex == ALICE[2:]:
            return 7
        return 0

    def get_balance(self, address_hex: str) -> int:
        if address_hex == ALICE[2:]:
            return 0
        return 0

    def sendtx(self, payload):
        self.sent.append(dict(payload))
        return "SUCCESS tx accepted"

    def createblock(self) -> str:
        return "BLOCK created"


def test_status_reports_zusd_monetary_state_from_wrapped_app_state(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8", str(E8 // 20))
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS", "25")
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "GET",
        "/api/zusd/monetary/status",
        None,
    )

    assert status_code == 200
    assert payload["ok"] is True
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["monetary_state_present"] is True
    assert status["core"]["collateral_e8"] == 20 * E8
    assert status["vault_owner_pubkey"] == ALICE
    assert status["liquidation_fee_comp_fixed_collateral_e8"] == E8 // 20
    assert status["liquidation_fee_comp_bps"] == 25
    assert status["liquidation_gas_comp_fixed_collateral_e8"] == E8 // 20
    assert status["liquidation_gas_comp_bps"] == 25


def test_status_reports_committed_policy_when_environment_drifts(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", ASSET_A)
    committed_app_state = _wrapped_app_state()

    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", ASSET_B)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)
    monkeypatch.setattr(
        monetary_api,
        "_load_app_state",
        lambda _client: (committed_app_state, "sha256:" + "ab" * 32),
    )

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "GET",
        "/api/zusd/monetary/status",
        None,
    )

    assert status_code == 200
    status = payload["status"]
    assert status["node_reachable"] is True
    assert status["asset_id"] == ASSET_A
    assert status["configured_asset_id"] == ASSET_B
    assert status["policy_binding_ok"] is False
    assert status["policy_binding_error"] == (
        "zUSD monetary policy binding mismatch: canonical_zusd_asset"
    )
    assert status["committed_policy_binding"]["canonical_zusd_asset"] == ASSET_A


def test_prepare_rejects_environment_policy_drift_before_building_intent(
    monkeypatch,
) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", ASSET_A)
    committed_app_state = _wrapped_app_state()
    monkeypatch.setenv("TAU_DEX_ZUSD_ASSET_ID", ASSET_B)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)
    monkeypatch.setattr(
        monetary_api,
        "_load_app_state",
        lambda _client: (committed_app_state, "sha256:" + "ab" * 32),
    )

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(
            {
                "action": "mint_zusd",
                "owner_pubkey": ALICE,
                "amount": 1000,
                "deadline": 123456789,
                "block_timestamp": 10,
                "tx_fee_limit": "2",
            }
        ).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("preflight_failed:")
    assert "canonical_zusd_asset" in str(payload["error"])


def test_prepare_mint_uses_monetary_nonce_and_preflights_stream_11(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["actor_pubkey"] == ALICE
    assert payload["transport"]["tx_sequence_number"] == 7
    report = payload["report"]
    assert report["nonce_key"] == zusd_monetary_sender_nonce_key(ALICE)
    assert report["nonce_before"] == 0
    assert report["nonce_after"] == 1
    assert report["operation"]["action"] == "mint_zusd"
    assert report["operation"]["amount_e8"] == 1000 * E8
    assert "11" in report["operations"]
    assert report["preflight"]["ok"] is True
    assert report["fee_limit"]["tx_fee_limit"] == "2"
    assert report["fee_limit"]["native_balance_covers_fee_limit"] is False
    assert report["fee_limit"]["warning"] == "native balance is below requested Tau fee limit"
    assert report["preflight"]["effects"][0]["effects"]["principal_e8"] == 1000 * E8
    assert payload["transport"]["tx_fee_limit"] == "2"
    assert payload["transport"]["fee_limit_native_balance_ok"] is False
    assert payload["transport"]["asset_id"] == derive_zusd_tau_asset_id(chain_id=chain_id)
    assert payload["proof"]["profile"]["profile_id"] == "zusd_stream11_live_monetary_v0"
    assert payload["proof"]["intent_receipt"]["body"]["stream_key"] == "11"
    assert payload["proof"]["intent_receipt"]["body"]["action"] == "mint_zusd"
    assert payload["proof"]["zk_wrapper"]["required"] is False
    assert payload["proof"]["zk_wrapper"]["zk_proof_verified"] is False


def test_prepare_rejects_boolean_block_timestamp(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": True,
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_block_timestamp"}


def test_prepare_mint_requires_zk_proof_when_enabled(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [sys.executable, "-c", "import json,sys; json.load(sys.stdin); print('{\"ok\": true}')"]
        ),
    )
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "zk_proof_required: zk_proof missing"}


def test_prepare_mint_accepts_verified_zk_wrapper(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                "import json,sys; obj=json.load(sys.stdin); assert obj['surface']=='zusd_stream11'; print('{\"ok\": true}')",
            ]
        ),
    )
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["surface"] == "zusd_stream11"
    assert wrapper["required"] is True
    assert wrapper["proof_provided"] is True
    assert wrapper["verifier_configured"] is True
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["artifact_binding_configured"] is False
    assert wrapper["artifact_binding_complete"] is False
    assert (
        wrapper["proof_intent_receipt_hash"] == payload["proof"]["intent_receipt"]["receipt_hash"]
    )
    assert payload["proof"]["profile"]["zk_proof_verified"] is True
    assert payload["proof"]["profile"]["artifact_binding_complete"] is False
    assert payload["proof"]["profile"]["promotion_ready"] is False


def test_prepare_mint_accepts_artifact_bound_zk_wrapper(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                "import json,sys; obj=json.load(sys.stdin); assert obj['surface']=='zusd_stream11'; print('{\"ok\": true}')",
            ]
        ),
    )
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "zusd-proof-verifier-v1",
                "artifact_hash": "sha256:" + "33" * 32,
                "build_ref": "tools/proof_verifiers/zusd_stream11_v1.py",
            }
        ),
    )
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps(
            {
                "artifact_id": "zusd-stream11-circuit-v1",
                "artifact_hash": "sha256:" + "44" * 32,
                "proof_system": "test-zk",
            }
        ),
    )
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "zk_proof": {"system": "test-zk", "proof_bytes": "fixture"},
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    wrapper = payload["proof"]["zk_wrapper"]
    assert wrapper["zk_proof_verified"] is True
    assert wrapper["artifact_binding_configured"] is True
    assert wrapper["artifact_binding_complete"] is True
    assert wrapper["artifact_binding"]["binding_hash"].startswith("0x")
    assert wrapper["artifact_binding"]["verifier_artifact_ready"] is True
    assert wrapper["artifact_binding"]["circuit_artifact_ready"] is True
    assert wrapper["artifact_binding"]["verifier_cmd_hash"].startswith("0x")
    assert payload["proof"]["profile"]["artifact_binding_complete"] is True
    assert payload["proof"]["profile"]["promotion_ready"] is True


def test_submit_mint_rejected_zk_proof_blocks_sendtx(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps(
            [
                sys.executable,
                "-c",
                'import json,sys; json.load(sys.stdin); print(\'{"ok": false, "error": "fixture proof rejected"}\')',
            ]
        ),
    )
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    def fail_sendtx(self, payload):  # pragma: no cover - this is a disaster-state sentinel.
        raise AssertionError("zk_reject_broadcasts_tx")

    monkeypatch.setattr(_FakeClient, "sendtx", fail_sendtx)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "signer_privkey": str(ALICE_PRIVKEY),
        "zk_proof": {"system": "test-zk", "proof_bytes": "bad-fixture"},
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "zk_proof_required: fixture proof rejected"}


def test_submit_mint_requires_local_signing_and_returns_sendtx(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "signer_privkey": str(ALICE_PRIVKEY),
        "tx_fee_limit": "2",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    assert payload["report"]["tau_tx_payload"]["sender_pubkey"] == ALICE[2:]
    assert payload["report"]["tau_tx_payload"]["fee_limit"] == "2"


def test_submit_accepts_external_signed_tau_payload_without_local_signing(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    assert prepared["ok"] is True
    assert prepared["report"]["tau_tx_payload"] is None

    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**body, "signed_tau_tx_payload": external_payload}).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["transport"]["allow_local_signing"] is False
    assert payload["transport"]["signing_mode"] == "external_signed_payload"
    assert payload["report"]["preflight"]["ok"] is True
    assert payload["report"]["tau_tx_payload"] == external_payload
    assert payload["submission"]["sendtx_response"] == "SUCCESS tx accepted"
    assert (
        json.loads(payload["report"]["tau_tx_payload"]["operations"]["11"])[0]["action"]
        == "mint_zusd"
    )


def test_submit_rejects_external_signed_tau_payload_operation_mismatch(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    wrong_operations = json.loads(json.dumps(prepared["report"]["operations"]))
    wrong_operations["11"][0]["amount_e8"] = 999 * E8
    external_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=wrong_operations,
        fee_limit=2,
    )

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**body, "signed_tau_tx_payload": external_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload operations mismatch"}


def test_submit_rejects_external_signed_tau_payload_sender_mismatch(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    wrong_sender_payload = build_signed_tau_transaction(
        privkey=81,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**body, "signed_tau_tx_payload": wrong_sender_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload sender mismatch"}


def test_submit_rejects_external_signed_tau_payload_sequence_mismatch(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    wrong_sequence_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"] + 1,
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**body, "signed_tau_tx_payload": wrong_sequence_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload sequence mismatch"}


def test_submit_rejects_external_signed_tau_payload_bad_signature(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, prepared = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    bad_signature_payload = build_signed_tau_transaction(
        privkey=ALICE_PRIVKEY,
        sequence_number=prepared["transport"]["tx_sequence_number"],
        expiration_time=123456789,
        operations=prepared["report"]["operations"],
        fee_limit=2,
    )
    bad_signature_payload["signature"] = "00" * 96

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps({**body, "signed_tau_tx_payload": bad_signature_payload}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "signed_tau_tx_payload signature invalid"}


def test_submit_rejects_preflight_failure_before_broadcast(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.delenv("ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 1,
        "block_timestamp": 10,
        "tx_fee_limit": "2",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/submit",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("preflight_failed:")


def test_prepare_rejects_bad_tx_fee_limit(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
        "tx_fee_limit": "1.5",
    }
    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 400
    assert payload == {"ok": False, "error": "bad_tx_fee_limit"}
