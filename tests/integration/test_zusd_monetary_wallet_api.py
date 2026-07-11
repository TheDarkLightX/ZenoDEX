from __future__ import annotations

import json
import sys

from src.core.dex import DexState
from src.core.zusd import E8, ZUSDCommand, init_state, step
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    _oracle_runtime_facts,
    apply_zusd_monetary_ops,
    zusd_monetary_sender_nonce_key,
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)
from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from src.state import BalanceTable, LPTable
from tests.integration.oracle_authorization_test_helpers import authorization_bundle
import src.integration.zusd_monetary_wallet_api as monetary_api


ALICE_PRIVKEY = 82
ALICE = "0x" + bls_pubkey_hex_from_privkey(ALICE_PRIVKEY)
ORACLE = "0x" + bls_pubkey_hex_from_privkey(81)


def _ok(core, tag: str, **kwargs):
    res = step(core, ZUSDCommand(tag=tag, args=kwargs))
    assert res.ok, res.error
    assert res.state is not None
    return res.state


def _wrapped_app_state() -> dict[str, object]:
    core = init_state()
    core = _ok(core, "bootstrap_oracle", price_e8=100 * E8, auth_ok=True)
    core = _ok(core, "deposit_collateral", amount_e8=20 * E8)
    dex_state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(dex_state).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(
            ZUSDMonetaryState(
                core=core,
                vault_owner_pubkey=ALICE,
                sp_deposits_e8={},
                sp_collateral_claims_e8={},
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


def _authorization_for_runtime(
    runtime: dict[str, object],
    *,
    value_e8: int | None = None,
    evidence_class: str = "O3",
    expires_at_epoch: int | None = None,
) -> dict[str, object]:
    query_id = str(runtime["query_id"])
    now_epoch = int(runtime["now_epoch"])
    observed_epoch = max(0, now_epoch - 1)
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    auth = {
        "consumer_module": str(runtime["consumer_module"]),
        "action_kind": str(runtime["action_kind"]),
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": str(runtime["profile_id"]),
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 1,
        "deviation_bps": 1,
        "observed_epoch": observed_epoch,
        "expires_at_epoch": int(now_epoch if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:zusd-collateral-price:v1",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "zusd-monetary"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "zusd-monetary"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "zusd-monetary"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "zusd-monetary"}),
        "evidence_class": evidence_class,
        "economic_envelope_id": semantic_hash("test.economic-envelope", {"surface": "zusd-monetary"}),
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "zusd-monetary"}),
    }
    return authorization_bundle(auth)


def _direct_bridge_fixture() -> tuple[DexState, ZUSDMonetaryState, dict[str, object]]:
    app_state = _wrapped_app_state()
    dex_state = state_from_snapshot(app_state["dex_state"])
    zusd_state = zusd_monetary_state_from_obj(app_state["zusd_monetary"])
    operation: dict[str, object] = {
        "module": "ZUSDFinance",
        "version": "0.1",
        "action": "mint_zusd",
        "nonce": 1,
        "deadline": 123456789,
        "owner_pubkey": ALICE,
        "amount_e8": 200 * E8,
    }
    return dex_state, zusd_state, operation


def test_direct_bridge_requires_oracle_authorization_when_configured() -> None:
    dex_state, zusd_state, operation = _direct_bridge_fixture()

    res = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(require_oracle_authorization=True),
        state=dex_state,
        zusd_state=zusd_state,
        operations=[operation],
        tx_sender_pubkey=ALICE,
        block_timestamp=10,
    )

    assert res.ok is False
    assert res.error == "zusd op[0] oracle_authorization_required"


def test_direct_bridge_rejects_self_attested_oracle_authorization() -> None:
    dex_state, zusd_state, operation = _direct_bridge_fixture()
    operation["oracle_authorization"] = {
        "oracle_authorization_ok": True,
        "query_id": "self-attested",
        "action_kind": "mint",
        "runtime_value_e8": 100 * E8,
    }

    res = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(require_oracle_authorization=True),
        state=dex_state,
        zusd_state=zusd_state,
        operations=[operation],
        tx_sender_pubkey=ALICE,
        block_timestamp=10,
    )

    assert res.ok is False
    assert str(res.error).startswith("zusd op[0] oracle_authorization_rejected:")


def test_direct_bridge_accepts_bound_oracle_authorization_when_configured() -> None:
    dex_state, zusd_state, operation = _direct_bridge_fixture()
    runtime = _oracle_runtime_facts(zusd_state=zusd_state, action="mint_zusd", operation=operation)
    assert runtime is not None
    operation["oracle_authorization"] = _authorization_for_runtime(runtime.__dict__)

    res = apply_zusd_monetary_ops(
        config=ZUSDMonetaryConfig(require_oracle_authorization=True),
        state=dex_state,
        zusd_state=zusd_state,
        operations=[operation],
        tx_sender_pubkey=ALICE,
        block_timestamp=10,
    )

    assert res.ok is True, res.error
    assert res.zusd_state is not None
    assert res.zusd_state.core.debt_e8 == 200 * E8


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


def test_zusd_monetary_state_rejects_unknown_top_level_fields() -> None:
    obj = dict(_wrapped_app_state()["zusd_monetary"])
    obj["future_extension"] = {"drop": "me"}

    try:
        zusd_monetary_state_from_obj(obj)
    except ValueError as exc:
        assert "zusd_monetary unknown fields" in str(exc)
    else:
        raise AssertionError("unknown zUSD monetary fields must fail closed")


def test_zusd_monetary_state_rejects_unknown_stability_pool_entry_fields() -> None:
    obj = dict(_wrapped_app_state()["zusd_monetary"])
    obj["core"] = {**obj["core"], "sp_debt_e8": E8}
    obj["sp_deposits"] = [{"pubkey": ALICE, "amount_e8": E8, "note": "ignored before hardening"}]

    try:
        zusd_monetary_state_from_obj(obj)
    except ValueError as exc:
        assert "zusd_monetary.sp_deposits[0] unknown fields" in str(exc)
    else:
        raise AssertionError("unknown stability-pool entry fields must fail closed")


def test_status_rejects_malformed_monetary_tau_port(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_TAU_PORT", "70000")

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "GET",
        "/api/zusd/monetary/status",
        None,
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert "ZUSD_MONETARY_WALLET_TAU_PORT" in str(payload["error"])


def test_status_monetary_tau_port_overrides_bad_legacy_fallback(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_TAU_PORT", "65433")
    monkeypatch.setenv("ZUSD_TAU_WALLET_TAU_PORT", "70000")
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "GET",
        "/api/zusd/monetary/status",
        None,
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["status"]["tau_port"] == 65433


def test_prepare_rejects_nonfinite_monetary_tau_timeout(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S", "nan")

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
    assert payload["ok"] is False
    assert "ZUSD_MONETARY_WALLET_TAU_TIMEOUT_S" in str(payload["error"])


def test_prepare_rejects_malformed_local_signing_fallback(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING", "maybe")
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
    assert payload["ok"] is False
    assert "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING" in str(payload["error"])


def test_prepare_rejects_malformed_liquidation_fee_config(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv("TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS", "10001")

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
    assert payload["ok"] is False
    assert "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS" in str(payload["error"])


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
    oracle_runtime = payload["oracle_runtime"]
    assert oracle_runtime["required"] is False
    assert oracle_runtime["consumer_module"] == "zenodex.zusd"
    assert oracle_runtime["action_kind"] == "mint"
    assert oracle_runtime["runtime_value_e8"] == 100 * E8
    assert oracle_runtime["runtime_action"]["query_id"].startswith("sha256:")


def test_oracle_runtime_endpoint_returns_mint_binding_without_zk(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
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
        "/api/zusd/monetary/oracle-runtime",
        json.dumps(body).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert "zk_wrapper" not in payload["proof"]
    runtime = payload["oracle_runtime"]["runtime_action"]
    assert runtime["consumer_module"] == "zenodex.zusd"
    assert runtime["action_kind"] == "mint"
    assert runtime["profile_id"].startswith("sha256:")
    assert runtime["query_id"].startswith("sha256:")
    assert runtime["runtime_value_e8"] == 100 * E8


def test_prepare_mint_requires_oracle_authorization_when_enabled(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
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
    assert payload == {"ok": False, "error": "oracle_authorization_required"}


def test_prepare_mint_accepts_bound_oracle_authorization_when_enabled(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
    }
    status_code, runtime_payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/oracle-runtime",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    auth = _authorization_for_runtime(runtime_payload["oracle_runtime"]["runtime_action"])

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps({**body, "oracle_authorization": auth}).encode("utf-8"),
    )

    assert status_code == 200
    assert payload["ok"] is True
    assert payload["oracle_runtime"]["required"] is True
    assert payload["oracle_runtime"]["authorization_check"]["typed_ok"] is True


def test_prepare_mint_rejects_wrong_oracle_authorization_value(monkeypatch) -> None:
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", "tau-test-zusd-monetary")
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setattr(monetary_api, "TauNetTcpClient", _FakeClient)

    body = {
        "action": "mint_zusd",
        "owner_pubkey": ALICE,
        "amount": 1000,
        "deadline": 123456789,
        "block_timestamp": 10,
    }
    status_code, runtime_payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/oracle-runtime",
        json.dumps(body).encode("utf-8"),
    )
    assert status_code == 200
    runtime = runtime_payload["oracle_runtime"]["runtime_action"]
    auth = _authorization_for_runtime(runtime, value_e8=int(runtime["runtime_value_e8"]) + 1)

    status_code, payload = monetary_api.handle_zusd_monetary_wallet_request(
        "POST",
        "/api/zusd/monetary/prepare",
        json.dumps({**body, "oracle_authorization": auth}).encode("utf-8"),
    )

    assert status_code == 400
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("oracle_authorization_rejected:")
    assert "runtime_value_e8 mismatch" in str(payload["error"])


def test_prepare_mint_requires_zk_proof_when_enabled(monkeypatch) -> None:
    chain_id = "tau-test-zusd-monetary"
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_CHAIN_ID", chain_id)
    monkeypatch.setenv("ZUSD_MONETARY_WALLET_REQUIRE_ZK_PROOF", "1")
    monkeypatch.setenv("TAU_DEX_ZUSD_ORACLE_PUBKEY", ORACLE)
    monkeypatch.setenv(
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON",
        json.dumps([sys.executable, "-c", "import json,sys; json.load(sys.stdin); print('{\"ok\": true}')"]),
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
        json.dumps([sys.executable, "-c", "import json,sys; obj=json.load(sys.stdin); assert obj['surface']=='zusd_stream11'; print('{\"ok\": true}')"]),
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
    assert wrapper["proof_intent_receipt_hash"] == payload["proof"]["intent_receipt"]["receipt_hash"]
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
        json.dumps([sys.executable, "-c", "import json,sys; obj=json.load(sys.stdin); assert obj['surface']=='zusd_stream11'; print('{\"ok\": true}')"]),
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
                "import json,sys; json.load(sys.stdin); print('{\"ok\": false, \"error\": \"fixture proof rejected\"}')",
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
    assert json.loads(payload["report"]["tau_tx_payload"]["operations"]["11"])[0]["action"] == "mint_zusd"


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
