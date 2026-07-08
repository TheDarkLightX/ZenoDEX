from __future__ import annotations

import json

import pytest

import src.integration.autotrader_live_api as autotrader_live_api
from src.integration.autotrader_live_api import handle_autotrader_live_request
from src.integration.autotrader_supervisor_profile import build_autotrader_supervisor_profile_v1
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction


def _balance(payload: str, *, pubkey: str, asset: str) -> int:
    state = json.loads(payload)
    balances = state.get("balances")
    assert isinstance(balances, list)
    for row in balances:
        if not isinstance(row, dict):
            continue
        if row.get("pubkey") == pubkey and row.get("asset") == asset:
            return int(row.get("amount", 0))
    return 0


def _supervisor_profile() -> dict[str, object]:
    return build_autotrader_supervisor_profile_v1(
        supervisor_id="autotrader.supervisor.local.1",
        chain_id="tau-local",
        stage="local-testnet",
        enabled=True,
        external_signed_payload_required=True,
        execution_id_required=True,
        release_certificate_required=True,
        stage_certificate_required=True,
        require_testnet_submission=True,
        require_local_preparation=True,
        max_actions_per_tick=1,
        max_runs_per_process=16,
        allowed_templates=["dca"],
        allowed_actions=["PLACE_SWAP_EXACT_IN"],
    )


def _mock_supervisor_prepare_payload(
    *,
    template: str = "dca",
    allowed_actions: list[str] | None = None,
) -> dict[str, object]:
    return {
        "ok": True,
        "status": "prepared",
        "surface": "autotrader_live_prepare",
        "report": {
            "signing": {"chain_id": "tau-local"},
            "decision": {"tag": "submit"},
            "user_rule_summary": {
                "intent": {
                    "template": template,
                    "allowed_actions": list(allowed_actions or ["PLACE_SWAP_EXACT_IN"]),
                }
            },
            "operations": {"2": [{"kind": "PLACE_SWAP_EXACT_IN"}]},
            "stage_certificate": {"stage_hash": "0xstage"},
            "live_release_certificate": {"release_hash": "0xrelease", "release_ok": True},
        },
        "not_claimed": ["unattended_production_strategy_execution"],
    }


def test_autotrader_live_status_reports_receipt_backed_prepare_surface(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", raising=False)
    monkeypatch.delenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", raising=False)
    monkeypatch.delenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", raising=False)

    status, payload = handle_autotrader_live_request(
        "GET",
        "/api/strategy/autotrader/status",
        None,
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"]["surface"] == "autotrader_live_prepare"
    assert payload["status"]["mode"] == "receipt_backed_prepare"
    assert "POST /api/strategy/autotrader/prepare" in payload["status"]["endpoints"]
    assert "POST /api/strategy/autotrader/submit" in payload["status"]["endpoints"]
    assert "POST /api/strategy/autotrader/execute-once" in payload["status"]["endpoints"]
    assert payload["status"]["testnet_submission_enabled"] is False
    assert payload["status"]["execute_once_enabled"] is False
    assert payload["status"]["supervisor_enabled"] is False
    assert "production_chain_submission" in payload["status"]["not_claimed"]


def test_autotrader_live_status_rejects_malformed_tau_port(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_TAU_PORT", "70000")

    status, payload = handle_autotrader_live_request(
        "GET",
        "/api/strategy/autotrader/status",
        None,
    )

    assert status == 400
    assert payload["ok"] is False
    assert "AUTOTRADER_LIVE_TAU_PORT" in str(payload["error"])


def test_autotrader_live_status_rejects_malformed_execute_flag(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "maybe")

    status, payload = handle_autotrader_live_request(
        "GET",
        "/api/strategy/autotrader/status",
        None,
    )

    assert status == 400
    assert payload["ok"] is False
    assert "AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED" in str(payload["error"])


def test_autotrader_live_prepare_requires_risk_acknowledgement() -> None:
    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps({"signer_privkey": 7}).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "autotrader_live_requires_risk_acknowledgement"
    assert payload["risk_disclosure"]["requires_explicit_acknowledgement"] is True
    assert payload["risk_disclosure"]["user_acknowledged"] is False


def test_autotrader_live_prepare_requires_local_signing_enablement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", raising=False)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "local_signing_disabled"
    assert payload["risk_disclosure"]["user_acknowledged"] is True


def test_autotrader_live_prepare_rejects_malformed_local_signing_flag(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "maybe")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING" in str(payload["error"])


def test_autotrader_live_prepare_fixture_builds_signed_receipt_backed_ops(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"] == "prepared"
    assert payload["surface"] == "autotrader_live_prepare"
    assert "production_chain_submission" in payload["not_claimed"]

    report = payload["report"]
    assert report["mode"] == "live_prepare"
    assert report["risk_disclosure"]["user_acknowledged"] is True
    assert report["signing"]["chain_id"] == "tau-local"
    assert report["decision"]["tag"] == "submit"
    assert report["live_admission"]["ok"] is True
    assert report["system_compose"]["ok"] is True
    assert report["submit_bundle"]["ok"] is True
    assert report["decision"]["intents"]
    assert report["operations"]["2"]
    assert report["tau_tx_payload"] is not None
    assert report["tau_tx_payload"]["sequence_number"] == 9
    assert report["tau_tx_payload"]["expiration_time"] == 999
    assert report["stage_certificate"] is not None
    assert report["live_release_certificate"] is not None


def test_autotrader_live_submit_requires_testnet_submission_enablement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", raising=False)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "testnet_submission_disabled"
    assert payload["risk_disclosure"]["user_acknowledged"] is True
    assert "production_chain_submission" in payload["not_claimed"]


def test_autotrader_live_submit_rejects_nonfinite_tau_timeout(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_TAU_TIMEOUT_S", "nan")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert "AUTOTRADER_LIVE_TAU_TIMEOUT_S" in str(payload["error"])


def test_autotrader_live_submit_sends_prepared_payload_and_mines(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        mined = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            return "SUCCESS: Transaction queued."

        def createblock(self) -> str:
            type(self).mined += 1
            return "SUCCESS: Block created."

    _FakeTauClient.sent = []
    _FakeTauClient.mined = 0
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_AUTO_MINE", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"] == "submitted"
    assert payload["surface"] == "autotrader_live_local_testnet_submit"
    assert payload["report"]["tau_tx_payload"]["sequence_number"] == 9
    assert payload["report"]["tau_tx_payload"]["expiration_time"] == 999
    assert payload["submission"]["sendtx_response"] == "SUCCESS: Transaction queued."
    assert payload["submission"]["signing_mode"] == "local_test_signing"
    assert payload["submission"]["createblock_response"] == "SUCCESS: Block created."
    assert len(_FakeTauClient.sent) == 1
    assert _FakeTauClient.sent[0] == payload["report"]["tau_tx_payload"]
    assert _FakeTauClient.mined == 1


def test_autotrader_live_submit_accepts_external_signed_tau_payload(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            return "SUCCESS: Transaction queued."

    _FakeTauClient.sent = []
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    prepare_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }
    status, prepared = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(prepare_body).encode("utf-8"),
    )
    assert status == 200
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                **{
                    k: v
                    for k, v in prepare_body.items()
                    if k not in {"tx_sequence_number", "tx_expiration_time"}
                },
                "signed_tau_tx_payload": external_payload,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["submission"]["signing_mode"] == "external_signed_payload"
    assert payload["report"]["tau_tx_signing_mode"] == "external_signed_payload"
    assert payload["report"]["tau_tx_payload"] == external_payload
    assert _FakeTauClient.sent == [external_payload]


def test_autotrader_live_submit_rejects_external_signed_tau_replay_before_sendtx(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        sequence = 9

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return type(self).sequence

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            type(self).sequence += 1
            return "SUCCESS: Transaction queued."

    _FakeTauClient.sent = []
    _FakeTauClient.sequence = 9
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    prepare_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }
    status, prepared = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(prepare_body).encode("utf-8"),
    )
    assert status == 200
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )
    submit_body = {
        **{k: v for k, v in prepare_body.items() if k != "tx_sequence_number"},
        "signed_tau_tx_payload": external_payload,
    }

    status, accepted = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(submit_body).encode("utf-8"),
    )
    assert status == 200
    assert accepted["ok"] is True
    assert len(_FakeTauClient.sent) == 1

    status, replay_rejected = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(submit_body).encode("utf-8"),
    )

    assert status == 400
    assert replay_rejected["ok"] is False
    assert replay_rejected["error"] == "signed_tau_tx_payload sequence mismatch"
    assert len(_FakeTauClient.sent) == 1


def test_autotrader_live_execute_once_requires_enablement(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", raising=False)
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "exec-disabled",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "execute_once_disabled"


def test_autotrader_live_execute_once_consumes_execution_key_and_rejects_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        sequence = 9

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return type(self).sequence

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            type(self).sequence += 1
            return "SUCCESS: Transaction queued."

    _FakeTauClient.sent = []
    _FakeTauClient.sequence = 9
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)
    execution_keys: set[str] = set()

    body = {
        "execution_id": "strategy-exec-1",
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }
    status, accepted = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=execution_keys,
    )
    assert status == 200
    assert accepted["ok"] is True
    assert accepted["status"] == "executed_once"
    assert accepted["surface"] == "autotrader_live_local_testnet_execute_once"
    assert accepted["execution"] == {"execution_id": "strategy-exec-1", "replay_guard": "consumed"}
    assert execution_keys == {"strategy-exec-1"}
    assert len(_FakeTauClient.sent) == 1

    replay_body = {**body, "tx_sequence_number": 10}
    status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(replay_body).encode("utf-8"),
        execution_keys=execution_keys,
    )
    assert status == 400
    assert replay["ok"] is False
    assert replay["error"] == "execution_replay"
    assert replay["execution"]["replay_guard"] == "already_consumed"
    assert len(_FakeTauClient.sent) == 1


def test_autotrader_live_supervisor_preflight_requires_ready_profile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.delenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", raising=False)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-1",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_profile_not_ready"
    assert payload["supervisor"]["supervisor_ready"] is False
    assert "autotrader supervisor profile is missing" in payload["supervisor"]["readiness_gaps"]


def test_autotrader_live_supervisor_preflight_emits_receipt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-1",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["status"] == "supervisor_preflight_ready"
    assert payload["supervisor"]["supervisor_ready"] is True
    assert payload["supervisor"]["runtime"]["consumed_runs_in_process"] == 0
    assert payload["supervisor"]["runtime"]["remaining_runs_in_process"] == 16
    assert payload["preflight"]["execution_id"] == "supervisor-preflight-1"
    assert payload["preflight"]["required_signing_mode"] == "external_signed_payload"
    assert payload["preflight"]["operation_count"] == 1
    assert payload["preflight"]["consumed_runs_in_process"] == 0
    assert payload["preflight"]["remaining_runs_in_process"] == 16
    assert payload["preflight"]["template"] == "dca"
    assert payload["preflight"]["allowed_actions"] == ["PLACE_SWAP_EXACT_IN"]
    assert payload["preflight"]["stage_hash"]
    assert payload["preflight"]["release_hash"]
    assert payload["preflight"]["preflight_hash"]


def test_autotrader_live_supervisor_preflight_rejects_disallowed_template(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    monkeypatch.setattr(
        autotrader_live_api,
        "_build_prepare_response",
        lambda _body: _mock_supervisor_prepare_payload(template="stop_loss", allowed_actions=["PLACE_SWAP_EXACT_IN"]),
    )

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-disallowed-template",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_template_not_allowed:stop_loss"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_disallowed_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    monkeypatch.setattr(
        autotrader_live_api,
        "_build_prepare_response",
        lambda _body: _mock_supervisor_prepare_payload(template="dca", allowed_actions=["PLACE_ORDER_INTENT"]),
    )

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-disallowed-action",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_action_not_allowed:PLACE_ORDER_INTENT"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_execute_consumes_execution_key_and_rejects_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        sequence = 9

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return type(self).sequence

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            type(self).sequence += 1
            return "SUCCESS: Transaction queued."

    _FakeTauClient.sent = []
    _FakeTauClient.sequence = 9
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    prepare_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }
    status, prepared = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(prepare_body).encode("utf-8"),
    )
    assert status == 200
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )
    execution_keys: set[str] = set()
    execute_body = {
        **{k: v for k, v in prepare_body.items() if k not in {"tx_sequence_number", "tx_expiration_time"}},
        "execution_id": "supervisor-exec-1",
        "signed_tau_tx_payload": external_payload,
    }

    status, accepted = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(execute_body).encode("utf-8"),
        execution_keys=execution_keys,
    )
    assert status == 200
    assert accepted["ok"] is True
    assert accepted["status"] == "supervisor_executed"
    assert accepted["execution"] == {
        "execution_id": "supervisor-exec-1",
        "replay_guard": "consumed",
        "mode": "supervised_manual_tick",
        "run_scope_id": "tau-local:autotrader.supervisor.local.1",
        "consumed_runs_in_process": 1,
        "remaining_runs_in_process": 15,
    }
    assert accepted["supervisor"]["supervisor_ready"] is True
    assert accepted["preflight"]["preflight_hash"]
    assert execution_keys == {"supervisor-exec-1"}
    assert len(_FakeTauClient.sent) == 1

    status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(execute_body).encode("utf-8"),
        execution_keys=execution_keys,
    )
    assert status == 400
    assert replay["ok"] is False
    assert replay["error"] == "execution_replay"
    assert replay["execution"]["replay_guard"] == "already_consumed"
    assert len(_FakeTauClient.sent) == 1


def test_autotrader_live_supervisor_execute_enforces_max_runs_per_process(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        sequence = 9

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return type(self).sequence

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            type(self).sequence += 1
            return "SUCCESS: Transaction queued."

    _FakeTauClient.sent = []
    _FakeTauClient.sequence = 9
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    profile = build_autotrader_supervisor_profile_v1(
        supervisor_id="autotrader.supervisor.local.1",
        chain_id="tau-local",
        stage="local-testnet",
        enabled=True,
        external_signed_payload_required=True,
        execution_id_required=True,
        release_certificate_required=True,
        stage_certificate_required=True,
        require_testnet_submission=True,
        require_local_preparation=True,
        max_actions_per_tick=1,
        max_runs_per_process=1,
        allowed_templates=["dca"],
        allowed_actions=["PLACE_SWAP_EXACT_IN"],
    )
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(profile, sort_keys=True))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    execution_keys: set[str] = set()
    supervisor_runs: dict[str, int] = {}
    prepare_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }
    status, prepared = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(prepare_body).encode("utf-8"),
    )
    assert status == 200
    payload_one = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )
    first_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "execution_id": "supervisor-exec-1",
        "signed_tau_tx_payload": payload_one,
    }
    status, accepted = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(first_body).encode("utf-8"),
        execution_keys=execution_keys,
        supervisor_runs=supervisor_runs,
    )
    assert status == 200
    assert accepted["ok"] is True
    assert supervisor_runs == {"tau-local:autotrader.supervisor.local.1": 1}

    second_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=10,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )
    second_body = {
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "execution_id": "supervisor-exec-2",
        "signed_tau_tx_payload": second_payload,
    }
    status, blocked = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(second_body).encode("utf-8"),
        execution_keys=execution_keys,
        supervisor_runs=supervisor_runs,
    )
    assert status == 400
    assert blocked["ok"] is False
    assert blocked["error"] == "supervisor_max_runs_per_process_exceeded:1>=1"
    assert blocked["supervisor"]["runtime"]["consumed_runs_in_process"] == 1
    assert blocked["supervisor"]["runtime"]["remaining_runs_in_process"] == 0
    assert len(_FakeTauClient.sent) == 1


def test_autotrader_live_prepared_default_payload_applies_to_tau_app_bridge(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    signer_privkey = 7
    signer_pubkey = "0x" + bls_pubkey_hex_from_privkey(signer_privkey)
    signer_raw = signer_pubkey[2:]
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("TAU_DEX_FAUCET", "1")
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", "tau-local")

    create_pool_intent = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "aa" * 32,
        "sender_pubkey": signer_pubkey,
        "deadline": 9999999999,
        "nonce": 1,
        "asset0": "A",
        "asset1": "B",
        "fee_bps": 10,
        "amount0": 1000,
        "amount1": 2000,
    }
    ok, app_state_json, _app_hash, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={signer_raw: 1},
        operations={
            "21": {"mint": [[signer_pubkey, "A", 10_000], [signer_pubkey, "B", 10_000]]},
            "19": [create_pool_intent],
        },
        tx_sender_pubkey=signer_raw,
        block_timestamp=1,
    )
    assert ok is True
    assert err is None
    assert _balance(app_state_json, pubkey=signer_pubkey, asset="A") == 9000

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": signer_privkey,
                "chain_id": "tau-local",
                "tx_sequence_number": 1,
                "tx_expiration_time": 999,
                "last_used_nonce": 1,
            }
        ).encode("utf-8"),
    )
    assert status == 200
    assert payload["ok"] is True

    ok, next_app_state_json, _app_hash, _balances_patch, err = plugin.apply_app_tx(
        app_state_json=app_state_json,
        chain_balances={signer_raw: 1},
        operations=payload["report"]["operations"],
        tx_sender_pubkey=signer_raw,
        block_timestamp=10,
    )
    assert ok is True
    assert err is None
    assert _balance(next_app_state_json, pubkey=signer_pubkey, asset="A") == 8900
